use libsecp256k1::curve::Scalar;

use crate::protocol::PartyIndex;
use crate::secret_sharing::VerifiableSS;
pub struct InMsg {
    pub sender: PartyIndex,
    pub fvss: GeneratingPhase,
}

pub type SecretShare = (u32, Scalar);

#[derive(Debug, Clone)]
pub struct GeneratingPhase {
    pub vss: VerifiableSS,
    pub share: SecretShare,
}

impl GeneratingPhase {
    pub fn verify(&self) -> bool {
        let valid = self.vss.validate_share(&self.share.1, self.share.0);
        if valid {
            log::debug!("validated FVSS {:?}\n", &self);
        } else {
            log::error!("failed FVSS {:?}\n", &self);
        }
        valid
    }
}
