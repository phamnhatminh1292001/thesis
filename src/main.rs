use crate::{
    ecproof::{ECVRFContractProof, ECVRFProof, Proof},
    helper::{
        address_to_scalar, calculate_witness_address, ecmult, ecmult_gen, is_on_curve,
        jacobian_to_affine, keccak256_affine_scalar, new_candidate_point, projective_ec_add,
        randomize, scalar_is_gte, GROUP_ORDER,
    },
};
use ethers::prelude::*;
use libsecp256k1::{
    curve::{Affine, ECMultContext, ECMultGenContext, Field, Jacobian, Scalar, AFFINE_G},
    PublicKey, SecretKey, ECMULT_CONTEXT, ECMULT_GEN_CONTEXT,
};
use std::time::{Duration, Instant};
use std::{str::FromStr, sync::Arc};
use tiny_keccak::{Hasher, Keccak};
pub mod ecproof;
pub mod helper;
pub mod secp256k1 {
    pub use libsecp256k1::*;
    pub use util::*;
}
pub mod random {
    pub use rand::thread_rng;
}
use ethers::{
    contract::abigen,
    core::{
        types::{Address, U256},
        utils::Anvil,
    },
    middleware::SignerMiddleware,
    providers::{Http, Provider},
    signers::LocalWallet,
};

pub struct ECVRF<'a> {
    secret_key: SecretKey,
    public_key: PublicKey,
    ctx_mul: &'a ECMultContext,
    ctx_gen: &'a ECMultGenContext,
}

impl ECVRF<'_> {
    // Create new instance of ECVRF from a secret key
    pub fn new(secret_key: SecretKey) -> Self {
        ECVRF {
            secret_key: secret_key,
            public_key: PublicKey::from_secret_key(&secret_key),
            ctx_gen: &ECMULT_GEN_CONTEXT,
            ctx_mul: &ECMULT_CONTEXT,
        }
    }

    // Hash to curve with prefix
    // HASH_TO_CURVE_HASH_PREFIX = 1
    pub fn hash_to_curve_prefix(&self, alpha: &Scalar, pk: &Affine) -> Affine {
        let mut tpk = pk.clone();
        tpk.x.normalize();
        tpk.y.normalize();
        let packed = [
            Field::from_int(1).b32().to_vec(),
            // pk
            tpk.x.b32().to_vec(),
            tpk.y.b32().to_vec(),
            // seed
            alpha.b32().to_vec(),
        ]
        .concat();
        let mut rv = new_candidate_point(&packed);
        while !is_on_curve(&rv) {
            rv = new_candidate_point(&rv.x.b32().to_vec());
        }
        rv
    }

    // Hash to curve
    pub fn hash_to_curve(&self, alpha: &Scalar, y: Option<&Affine>) -> Affine {
        let mut r = Jacobian::default();
        self.ctx_gen.ecmult_gen(&mut r, alpha);
        let mut p = Affine::default();
        match y {
            Some(v) => {
                r = r.add_ge(v);
                r
            }
            None => r,
        };
        p.set_gej(&r);
        p.x.normalize();
        p.y.normalize();
        p
    }

    // Hash point to Scalar
    pub fn hash_points(
        &self,
        g: &Affine,
        h: &Affine,
        pk: &Affine,
        gamma: &Affine,
        kg: &Affine,
        kh: &Affine,
    ) -> Scalar {
        let mut output = [0u8; 32];
        let mut hasher = Keccak::v256();
        let all_points = [g, h, pk, gamma, kg, kh];
        for point in all_points {
            hasher.update(point.x.b32().as_ref());
            hasher.update(point.y.b32().as_ref());
        }

        hasher.finalize(&mut output);
        let mut r = Scalar::default();
        r.set_b32(&output).unwrap_u8();
        r
    }

    // Hash points with prefix
    // SCALAR_FROM_CURVE_POINTS_HASH_PREFIX = 2
    pub fn hash_points_prefix(
        &self,
        hash: &Affine,
        pk: &Affine,
        gamma: &Affine,
        u_witness: &[u8; 20],
        v: &Affine,
    ) -> Scalar {
        let mut output = [0u8; 32];
        let mut hasher = Keccak::v256();
        let all_points = [hash, pk, gamma, v];
        hasher.update(Scalar::from_int(2).b32().as_ref());
        for point in all_points {
            hasher.update(point.x.b32().as_ref());
            hasher.update(point.y.b32().as_ref());
        }
        hasher.update(u_witness);
        hasher.finalize(&mut output);
        let mut r = Scalar::default();
        r.set_b32(&output).unwrap_u8();
        r
    }

    // We use this method to prove a randomness for L1 smart contract
    // This prover was optimized for on-chain verification
    // u_witness is a represent of u, used ecrecover to minimize gas cost
    // we're also add projective EC add to make the proof compatible with
    // on-chain verifier.
    pub fn prove_contract(self, alpha: &Scalar) -> ECVRFContractProof {
        let mut pub_affine: Affine = self.public_key.into();
        let mut secret_key: Scalar = self.secret_key.into();
        pub_affine.x.normalize();
        pub_affine.y.normalize();

        // On-chain compatible HASH_TO_CURVE_PREFIX
        let h = self.hash_to_curve_prefix(alpha, &pub_affine);

        // gamma = H * sk
        let gamma = ecmult(self.ctx_mul, &h, &secret_key);

        // k = random()
        // We need to make sure that k < GROUP_ORDER
        let mut k = randomize();
        while scalar_is_gte(&k, &GROUP_ORDER) || k.is_zero() {
            k = randomize();
        }

        // Calculate k * G = u
        let kg = ecmult_gen(self.ctx_gen, &k);
        // U = c * pk + s * G
        // u_witness = ecrecover(c * pk + s * G)
        // this value equal to address(keccak256(U))
        // It's a gas optimization for EVM
        // https://ethresear.ch/t/you-can-kinda-abuse-ecrecover-to-do-ecmul-in-secp256k1-today/2384
        let u_witness = calculate_witness_address(&kg);

        // Calculate k * H = v
        let kh = ecmult(self.ctx_mul, &h, &k);

        // c = ECVRF_hash_points_prefix(H, pk, gamma, u_witness, k * H)
        let c = self.hash_points_prefix(&h, &pub_affine, &gamma, &u_witness, &kh);

        // s = (k - c * sk)
        // Based on Schnorr signature
        let mut neg_c = c.clone();
        neg_c.cond_neg_assign(1.into());
        let s = k + neg_c * secret_key;
        secret_key.clear();

        // Gamma witness
        // witness_gamma = gamma * c
        let witness_gamma = ecmult(self.ctx_mul, &gamma, &c);

        // Hash witness
        // witness_hash = h * s
        let witness_hash = ecmult(self.ctx_mul, &h, &s);

        // V = witness_gamma + witness_hash
        //   = c * gamma + s * H
        //   = c * (sk * H) + (k - c * sk) * H
        //   = k * H
        let v = projective_ec_add(&witness_gamma, &witness_hash);

        // Inverse do not guarantee that z is normalized
        // We need to normalize it after we done the inverse
        let mut inverse_z = v.z.inv();
        inverse_z.normalize();

        ECVRFContractProof {
            pk: self.public_key,
            gamma,
            c,
            s,
            y: keccak256_affine_scalar(&gamma),
            alpha: *alpha,
            witness_address: address_to_scalar(&u_witness),
            witness_gamma,
            witness_hash,
            inverse_z,
        }
    }

    pub fn display(&self, smart_contract_proof: ECVRFProof) -> Proof {
        let gamma1 = hex::encode(smart_contract_proof.gamma.x.b32());

        let gamma2 = hex::encode(smart_contract_proof.gamma.y.b32());

        let c = hex::encode(smart_contract_proof.c.b32());

        let s = hex::encode(smart_contract_proof.s.b32());

        let gamma = (gamma1, gamma2);
        let c = c;
        let s = s;

        Proof { gamma, c, s }
    }
    // Ordinary prover
    pub fn prove(&self, alpha: &Scalar) -> ECVRFProof {
        let mut pub_affine: Affine = self.public_key.into();
        let mut secret_key: Scalar = self.secret_key.into();
        pub_affine.x.normalize();
        pub_affine.y.normalize();

        // Hash to a point on curve
        let h = self.hash_to_curve(alpha, Some(&pub_affine));

        // gamma = H * secret_key
        let gamma = ecmult(self.ctx_mul, &h, &secret_key);

        // k = random()
        // We need to make sure that k < GROUP_ORDER
        let mut k = randomize();
        while scalar_is_gte(&k, &GROUP_ORDER) || k.is_zero() {
            k = randomize();
        }

        // Calculate k * G <=> u
        let kg = ecmult_gen(self.ctx_gen, &k);

        // Calculate k * H <=> v
        let kh = ecmult(self.ctx_mul, &h, &k);

        // c = ECVRF_hash_points(G, H, public_key, gamma, k * G, k * H)
        let c = self.hash_points(&AFFINE_G, &h, &pub_affine, &gamma, &kg, &kh);

        // s = (k - c * secret_key) mod p
        let mut neg_c = c.clone();
        neg_c.cond_neg_assign(1.into());
        let s = k + neg_c * secret_key;
        secret_key.clear();

        // y = keccak256(gama.encode())
        let y = keccak256_affine_scalar(&gamma);

        ECVRFProof::new(gamma, c, s, y, self.public_key)
    }

    // Ordinary verifier
    pub fn verify(self, alpha: &Scalar, vrf_proof: &ECVRFProof) -> bool {
        let mut pub_affine: Affine = self.public_key.into();
        pub_affine.x.normalize();
        pub_affine.y.normalize();

        assert!(pub_affine.is_valid_var());
        assert!(vrf_proof.gamma.is_valid_var());

        // H = ECVRF_hash_to_curve(alpha, pk)
        let h = self.hash_to_curve(alpha, Some(&pub_affine));
        let mut jh = Jacobian::default();
        jh.set_ge(&h);

        // U = c * pk + s * G
        //   = c * sk * G + (k - c * sk) * G
        //   = k * G
        let mut u = Jacobian::default();
        let pub_jacobian = Jacobian::from_ge(&pub_affine);
        self.ctx_mul
            .ecmult(&mut u, &pub_jacobian, &vrf_proof.c, &vrf_proof.s);

        // Gamma witness
        let witness_gamma = ecmult(self.ctx_mul, &vrf_proof.gamma, &vrf_proof.c);
        // Hash witness
        let witness_hash = ecmult(self.ctx_mul, &h, &vrf_proof.s);

        // V = c * gamma + s * H = witness_gamma + witness_hash
        //   = c * sk * H + (k - c * sk) * H
        //   = k *. H
        let v = Jacobian::from_ge(&witness_gamma).add_ge(&witness_hash);

        // c_prime = ECVRF_hash_points(G, H, pk, gamma, U, V)
        let computed_c = self.hash_points(
            &AFFINE_G,
            &h,
            &pub_affine,
            &vrf_proof.gamma,
            &jacobian_to_affine(&u),
            &jacobian_to_affine(&v),
        );

        // y = keccak256(gama.encode())
        let computed_y = keccak256_affine_scalar(&vrf_proof.gamma);

        // computed values should equal to the real one
        computed_c.eq(&vrf_proof.c) && computed_y.eq(&vrf_proof.y)
    }
}

use rand::thread_rng;
abigen!(VerifierContract, "src/verifier_abi.json");

// The results below have been tested on chainlink.
#[tokio::main]

async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Testing the system for 4 participants
    let mut r = thread_rng();
    let start = Instant::now();
    let mut sum = Jacobian::default();
    //The current input
    let alpha = Scalar([
        0xD0364141, 0xBFD25E8C, 0xAF48A03B, 0xBAAEDCE6, 0xFFFFFFFE, 0xFFFFFFFF, 0xFFFFFFFF,
        0xFFFFFFFF,
    ]);

    let alpha2 = hex::encode(alpha.b32());
    let mut sum = Jacobian::default();
    // The list of Lagrange coefficients for 4 participants
    let mut lag1 = Scalar([
        0x00000004, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
        0x00000000,
    ]);
    let mut lag2 = Scalar([
        0xd036413b, 0xbfd25e8c, 0xaf48a03b, 0xbaaedce6, 0xfffffffe, 0xffffffff, 0xffffffff,
        0xffffffff,
    ]);

    let mut lag3 = Scalar([
        0xd0364140, 0xbfd25e8c, 0xaf48a03b, 0xbaaedce6, 0xfffffffe, 0xffffffff, 0xffffffff,
        0xffffffff,
    ]);
    let mut lag4 = Scalar([
        0x00000004, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
        0x00000000,
    ]);
    let mut vec = Vec::new();
    vec.push(lag1);
    vec.push(lag2);
    vec.push(lag3);
    vec.push(lag4);
    println! {"{:?}",alpha2};
    for i in 1..5 {
        let secret_key = SecretKey::random(&mut thread_rng());
        let secret_key2: Scalar = secret_key.into();
        println! {"Output of participant {i}:"};
        let ecvrf = ECVRF::new(secret_key);
        let context = ecvrf.ctx_mul;
        let r1 = ecvrf.prove(&alpha);
        let pr = ecvrf.display(r1);
        println! {"{:?}",pr.gamma};
        println! {"Proof of participant {i}:"};
        println! {"{:?}",pr};
        let r2 = ecvrf.verify(&alpha, &r1);
        println! {"Verifying the output of participant {i}:"};
        println! {"Result: {r2}"};
        println!("\n");
        // multiply by lagrange coefficients
        let temp = ecmult(&context, &r1.gamma, &vec[i - 1]);
        sum = sum.add_ge(&r1.gamma);
    }
    println!("There are 3 participants that have produced valid outputs: 1,2,3");
    println!("Combining final output...");

    let mut sum_affine = Affine::default();
    sum_affine = Affine::from_gej(&sum);
    sum_affine.x.normalize();
    sum_affine.y.normalize();
    let r1 = keccak256_affine_scalar(&sum_affine);
    let y = hex::encode(r1.b32());
    println!("Final output: {y}");

    let secret_key = SecretKey::random(&mut thread_rng());
    let ecvrf = ECVRF::new(secret_key);
    Ok(())
}
