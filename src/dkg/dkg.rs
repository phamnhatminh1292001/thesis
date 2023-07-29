// This module imports steps of the DKG protocol run by a participant
// The DKG protocol consists of the following steps:
// 1) Participant i chooses a polynomial P_i(X)=p_0+p_1*X+p_2*X^2+...+p_t*X^t
// Then they broadcast the commitment C_i=G*p_i for i=0,1,2,...,t
// 2) Participant i then calculate s_ij=p_i(j) then sends s_ij to Participant j
// 3) Participant i then checks thhe validity of

use crate::helper::{ecmult, ecmult_gen, randomize};
use libsecp256k1::{
    curve::{Affine, Scalar},
    ECMULT_GEN_CONTEXT,
};
use std::collections::{BTreeSet, HashMap};
use std::time::Duration;
pub mod message;
pub mod secret_sharing;
use crate::message::{InMsg, SecretShare};
pub mod secp256k1 {
    pub use libsecp256k1::*;
    pub use util::*;
}
pub mod random {
    pub use rand::thread_rng;
}
pub mod helper;
pub mod protocol;
use crate::protocol::PartyIndex;
use thiserror::Error;

#[derive(Debug, Error)]
#[allow(clippy::large_enum_variant)]
// Returns a list of possible errors of the DKG phase.
pub enum KeygenError {
    #[error("Key generation cannot be started: {0}")]
    IncorrectParameters(String),
    #[error("keygen: timeout in {phase}")]
    Timeout { phase: String },
}

// This struct consists of the threshold t and the number of participants for the DKG phase
// The function new(t,n) check the validity of t and n then assigns threshold to be t and num_share
// to be n
#[derive(Clone, Copy, Debug)]
pub struct Parameters {
    threshold: u32,
    pub num_share: u32,
}

impl Parameters {
    // Initialize the threshold and number of participants. Remember to check the
    // validity of threshold and the number of participants.
    pub fn new(threshold: u32, num_share: u32) -> Result<Self, KeygenError> {
        // threshold cannot be bigger than the number of participants
        if threshold > num_share {
            return Err(KeygenError::IncorrectParameters(format!(
                "Threshold {} cannot be greater than number of shares {}",
                threshold, num_share
            )));
        }
        // there must be at least 2 participants
        if num_share < 2 {
            return Err(KeygenError::IncorrectParameters(format!(
                "Number of shares must be at least 2, got {}",
                num_share
            )));
        }
        // threshold must be at least 2
        if threshold < 2 {
            return Err(KeygenError::IncorrectParameters(format!(
                "Threshold must be at least 2, got: {}",
                threshold
            )));
        }
        Ok(Parameters {
            threshold,
            num_share,
        })
    }

    // Returns the threshold value
    pub fn threshold(&self) -> u32 {
        self.threshold
    }

    // Returns the number of participants
    pub fn share_count(&self) -> u32 {
        self.num_share
    }
}

// Map of `PartyIndex` of each party into the x-coordinate of the shares received by this party
//
// Maps [`PartyIndex`] to a number. Used in the calculation of Lagrange's coefficients in the Beacon
// Phase as there are only several valid parties after the Setup Phase

pub struct Party2PointMap {
    pub points: HashMap<PartyIndex, u32>,
}

impl Party2PointMap {
    // Map each valid PartyIndex to a number (valid here means that it passed the
    // verification test)
    pub fn map_valid_parties_to_points(&self, valid: &[PartyIndex]) -> Vec<u32> {
        let mut qualified = Vec::new();
        let mut absent = Vec::new();
        for idx in valid {
            match self.points.get(idx) {
                Some(point) => qualified.push(*point),
                None => absent.push(*idx),
            }
        }
        assert_eq!(qualified.len(), 0);
        qualified
    }

    // Returns the corresponding Lagrange coefficient of the party
    pub fn calculate_lagrange_multiplier(&self, valid: &[PartyIndex], own_x: Scalar) -> Scalar {
        let subset = self
            .map_valid_parties_to_points(valid)
            .into_iter()
            .map(|x| {
                let index_bn = x;
                Scalar::from_int(index_bn)
            })
            .collect::<Vec<Scalar>>();
        let mut nume = Scalar::from_int(1);
        let mut demo = Scalar::from_int(1);
        for i in 1..valid.len() {
            nume = nume * subset[i];
            let mut own_xc = own_x.clone();
            own_xc.cond_neg_assign(1.into());
            demo = demo * (subset[i] + own_xc);
        }
        demo.inv() * nume
    }
}

// The final result result of the DKG protocol and input for computing the ECVRF.
// key_params consists of the threshold and the number of participants
// own_party_index consists of the index of the participant
// secret share and public key consisis of the secret share and public key of the participant
// party_to_point_map consists of the index of all participants
pub struct MultiPartyInfo {
    key_params: Parameters,
    own_party_index: PartyIndex,
    secret_key: SecretShare,
    public_key: Affine,
    party_to_point_map: Party2PointMap,
}

// Get info of the secret share
impl MultiPartyInfo {
    // Returns the index of the participant
    pub fn own_point(&self) -> u32 {
        self.secret_key.0
    }
    // Returns the share of the participant
    pub fn own_share(&self) -> Scalar {
        self.secret_key.1
    }
}

// Start the DKG
// Do the following:
// Sample a polynomial P(X)=a_0+a_1*X+a_2*X^2+...+a_t*X^t
// Receive share s_j from participant P_j
// Check if share s_j is valid for each j

pub struct PedersenDKG {
    param: Parameters,
    own_party_index: PartyIndex,
    other_parties: BTreeSet<PartyIndex>,
    own_share: SecretShare,
    other_share: HashMap<PartyIndex, SecretShare>,
    timeout: Option<Duration>,
}
impl PedersenDKG {
    fn start(
        self,
        param: &Parameters,
        parties: &[PartyIndex],
        own_party_index: PartyIndex,
        timeout: Option<Duration>,
    ) {
        log::info!("Phase1 starts");
        // Remove all duplicates in the set of parties (Multiple participants have the same id)
        // If there is any duplicate. report Error
        let acting_parties = BTreeSet::from_iter(parties.iter().cloned());
        assert!(acting_parties.len() != parties.len());

        // Check if you are in the list of acting parties
        assert!(acting_parties.get(&own_party_index).is_none());

        // Get the list of active parties other than yourself
        let mut other_parties = acting_parties;
        other_parties.remove(&own_party_index);
        // Generate your own secret share
        let secret_share = randomize();
        let own_share: SecretShare = (self.own_share.0, secret_share);
    }

    fn consume(&self, current_msg_set: Vec<InMsg>) -> FinalState {
        let share = current_msg_set;
        let mut verified = false;
        // Init the secret key variable for yourself
        let mut private_share = Scalar::from_int(0);
        // Verify the validity of share s_j for all other j
        for i in 1..share.len() {
            verified = share[i].fvss.verify();
            if verified {
                private_share = private_share + share[i].fvss.share.1;
            }
        }
        let points = self
            .other_share
            .iter()
            .map(|(p, share_xy)| (*p, share_xy.0))
            .collect();
        let public_share = ecmult_gen(&ECMULT_GEN_CONTEXT, &private_share);

        let state = FinalState {
            multiparty_shared_info: MultiPartyInfo {
                key_params: self.param,
                own_party_index: self.own_party_index,
                secret_key: (self.own_share.0, private_share),
                public_key: public_share,
                party_to_point_map: Party2PointMap { points },
            },
        };
        state
    }

    fn timeout(&self) -> Option<Duration> {
        self.timeout
    }
}

// Result of key generation protocol
pub struct FinalState {
    pub multiparty_shared_info: MultiPartyInfo,
}

// Container of `KeygenError` type
pub struct ErrorState {
    errors: Vec<KeygenError>,
}

impl ErrorState {
    pub fn new(errors: Vec<KeygenError>) -> Self {
        ErrorState { errors }
    }
}
