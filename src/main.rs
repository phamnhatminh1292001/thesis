//! The implementation has two main components: DKG and ECVRF.
//! I implemented the DKG module by myself in dkg_module.
//! The EVCRF component is implemented in the main file here.
//! Most of the structs and functions of ECVRF module is referenced from here 
//! https://github.com/orochi-network/orochimaru/blob/main/libecvrf/src/ecvrf.rs.
//! The main() function is to test the whole distributed VRF, not the single ECVRF run
//! like the above link.
use crate::gadget::{ecmult, ecmult_gen, jacobian_to_affine, keccak256_affine_scalar, randomize};
use ethers::prelude::*;
use libsecp256k1::{
    curve::{Affine, ECMultContext, ECMultGenContext, Jacobian, Scalar, AFFINE_G},
    PublicKey, SecretKey, ECMULT_CONTEXT, ECMULT_GEN_CONTEXT,
};
use std::{ops::Neg, time::Instant};
// use std::{str::FromStr, sync::Arc};
use tiny_keccak::{Hasher, Keccak};
pub mod gadget;
pub mod dkg_module;
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

#[derive(Clone, Copy, Debug)]
pub struct ECVRFProof {
    pub gamma: Affine,
    pub c: Scalar,
    pub s: Scalar,
    pub y: Scalar,
    pub pk: PublicKey,
}

#[derive(Clone, Debug)]
pub struct Proof {
    pub gamma: (String, String),
    pub c: String,
    pub s: String,
}

impl ECVRFProof {
    pub fn new(gamma: Affine, c: Scalar, s: Scalar, y: Scalar, pk: PublicKey) -> Self {
        Self { gamma, c, s, y, pk }
    }
}

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

    pub fn encode(&self, alpha: &Scalar, y: Affine) -> Affine {
        let mut r = Jacobian::default();
        self.ctx_gen.ecmult_gen(&mut r, alpha);
        r=r.add_ge(&y);
        let mut p = Affine::default();
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
        let points = [g, h, pk, gamma, kg, kh];
        for i in 0..points.len() {
            hasher.update(points[i].x.b32().as_ref());
            hasher.update(points[i].y.b32().as_ref());
        }

        hasher.finalize(&mut output);
        let mut r = Scalar::default();
        r.set_b32(&output).unwrap_u8();
        r
    }

    pub fn prove(&self, alpha: &Scalar) -> ECVRFProof {
        let mut pub_affine: Affine = self.public_key.into();
        let secret_key: Scalar = self.secret_key.into();
        pub_affine.x.normalize();
        pub_affine.y.normalize();

        // Hash to a point on curve
        let h = self.encode(alpha, pub_affine);

        // gamma = H * secret_key
        let gamma = ecmult(self.ctx_mul, &h, &secret_key);

        let k = randomize();

        // Calculate k * G <=> u
        let kg = ecmult_gen(self.ctx_gen, &k);

        // Calculate k * H <=> v
        let kh = ecmult(self.ctx_mul, &h, &k);

        // c = ECVRF_hash_points(G, H, public_key, gamma, k * G, k * H)
        let c = self.hash_points(&AFFINE_G, &h, &pub_affine, &gamma, &kg, &kh);

        // s = (k - c * secret_key) mod p
        let neg_c = c.clone().neg();
        let s = k + neg_c * secret_key;

        // y = keccak256(gama.encode())
        let y = keccak256_affine_scalar(&gamma);

        ECVRFProof::new(gamma, c, s, y, self.public_key)
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

    // Ordinary verifier
    pub fn verify(self, alpha: &Scalar, vrf_proof: &ECVRFProof) -> bool {
        let mut pub_affine: Affine = self.public_key.into();
        pub_affine.x.normalize();
        pub_affine.y.normalize();


        // H = ECVRF_encode(alpha, pk)
        let h = self.encode(alpha, pub_affine);
        let mut jh = Jacobian::default();
        jh.set_ge(&h);

        let mut u = Jacobian::default();
        let pub_jacobian = Jacobian::from_ge(&pub_affine);
        self.ctx_mul
            .ecmult(&mut u, &pub_jacobian, &vrf_proof.c, &vrf_proof.s);

        // Gamma witness
        let witness_gamma = ecmult(self.ctx_mul, &vrf_proof.gamma, &vrf_proof.c);
        // Hash witness
        let witness_hash = ecmult(self.ctx_mul, &h, &vrf_proof.s);

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
// abigen!(VerifierContract, "src/verifier_abi.json");

// The results below have been tested on chainlink.
// #[tokio::main]

fn main() {
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
    // The list of Lagrange coefficients for 4 participants. For simplicity, I preprocessed this.
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
        sum = sum.add_ge(&temp);
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
}
