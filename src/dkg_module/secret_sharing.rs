// This module implements the Feldman's VSS Scheme
// In the DKG Phase, each party choose a random polynomial p(X)=a_0+a_1*X+a_2*X^2+...+a_t*X^t
// and commits G*a_0, G*a_1,..., G*a_t
// Then he compute s_j=a(j) and shares to participant j

use crate::helper::{ecmult, ecmult_gen, randomize, GROUP_ORDER};
use libsecp256k1::{
    curve::{Affine, ECMultContext, ECMultGenContext, Field, Jacobian, Scalar, AFFINE_G},
    PublicKey, SecretKey, ECMULT_CONTEXT, ECMULT_GEN_CONTEXT,
};

pub mod secp256k1 {
    pub use libsecp256k1::*;
    pub use util::*;
}
pub mod random {
    pub use rand::thread_rng;
}

// This is the Feldman VSS Class. It has a threshold t, a number of shares n and
// a list of commitment of the polynomial a(x)
#[derive(Debug, Clone)]
pub struct VerifiableSS {
    pub threshold: u32,
    pub num_share: u32,
    pub commitment: Vec<Affine>,
}

impl VerifiableSS {
    // This function takes input s and samples a_0,a_1,...,a_t
    //  for the polynomial a(X)=a_0+a_1*X+a_2*X^2+...+a_t*X^t such that a_0=s
    // and returns [a_0,a_1,...,a_t]
    pub fn sample_polynomial(t: u32, secret: &Scalar) -> Vec<Scalar> {
        let mut coefficients = vec![*secret];
        for i in 1..t {
            let random_coefficients = randomize();
            let mut v = vec![random_coefficients];
            coefficients.append(&mut v);
        }
        coefficients
    }
    // Perform the share process by calculating s_j=a(j) for j=1,2,...,n. Then returns
    // the following information:
    // threshold: t
    // number of participants: n
    // commitment: [G*a_0, G*a_1,...,G*a_t]
    // the list [s_1,s_2,...,s_n]
    pub fn share(t: u32, n: u32, secret: &Scalar) -> (VerifiableSS, Vec<Scalar>) {
        assert!(t < n);
        let poly = VerifiableSS::sample_polynomial(t, secret);
        let index_vec: Vec<u32> = (1..=n).collect();
        let secret_shares = VerifiableSS::evaluate_polynomial(&poly, &index_vec);
        let commitments = (0..poly.len())
            .map(|i| {
                let i2 = i as u32;
                ecmult_gen(&ECMULT_GEN_CONTEXT, &Scalar::from_int(i2))
            })
            .collect::<Vec<Affine>>();
        (
            VerifiableSS {
                threshold: t,
                num_share: n,
                commitment: commitments,
            },
            secret_shares,
        )
    }
    // Calculate s_j=a(j) for j=1,2,...,n.
    pub fn evaluate_polynomial(poly: &Vec<Scalar>, index_vec: &Vec<u32>) -> Vec<Scalar> {
        (0..index_vec.len())
            .map(|point| {
                let point_bn = index_vec[point];

                VerifiableSS::mod_evaluate_polynomial(poly, Scalar::from_int(point_bn))
            })
            .collect::<Vec<Scalar>>()
    }
    // Take the input point and calculate the value a(X) at X=point
    pub fn mod_evaluate_polynomial(poly: &Vec<Scalar>, point: Scalar) -> Scalar {
        let mut eval = poly[0];
        let mut iter = Scalar::from_int(1);
        for i in 1..poly.len() {
            iter = iter * point;
            eval = eval + poly[i] * iter;
        }
        eval
    }
    //
    pub fn validate_share(&self, secret_share: &Scalar, index: u32) -> bool {
        let ss_point = ecmult_gen(&ECMULT_GEN_CONTEXT, secret_share);
        let comm_to_point = self.comm_to_point(index);
        ss_point == comm_to_point
    }

    pub fn comm_to_point(&self, index: u32) -> Affine {
        let mut point = Jacobian::from_ge(&self.commitment[0]);
        let mut iter = Scalar::from_int(1);
        let index = Scalar::from_int(index);
        for i in 1..self.threshold {
            let i2 = i as usize;
            iter = iter * index;
            point = point.add_ge(&ecmult(&ECMULT_CONTEXT, &self.commitment[i2], &iter));
        }
        let mut point_prime = Affine::default();
        point_prime.set_gej(&point);
        point_prime
    }
}
