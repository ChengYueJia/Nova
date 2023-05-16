//! This module defines CCS related types and functions.
/// See https://eprint.iacr.org/2023/552
#![allow(clippy::type_complexity)]
use crate::{
  constants::{BN_LIMB_WIDTH, BN_N_LIMBS, NUM_HASH_BITS},
  errors::NovaError,
  gadgets::{
    nonnative::{bignat::nat_to_limbs, util::f_to_nat},
    utils::scalar_as_base,
  },
  traits::{
    commitment::CommitmentEngineTrait, AbsorbInROTrait, Group, ROTrait, TranscriptReprTrait,
  },
  Commitment, CommitmentKey, CE,
};
use core::{cmp::max, marker::PhantomData};
use ff::Field;
use flate2::{write::ZlibEncoder, Compression};
use itertools::concat;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use sha3::{Digest, Sha3_256};

// TODO, based on r1cs.rs:
// - CCS struct
// - CCS impl
// - CCS is_sat
// - R1CS to CCS

/// Public parameters for a given CCS
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct CCS<G: Group> {
  _p: PhantomData<G>,
}

pub struct CCSShape<G: Group> {
    pub(crate) num_cons: usize,
    pub(crate) num_vars: usize,
    pub(crate) num_io: usize,
    pub(crate) M: Vec<Vec<(usize, usize, G::Scalar)>>,
    pub(crate) t: usize,
    pub(crate) q: usize,
    pub(crate) d: usize,
    digest: G::Scalar, // digest of the rest of CCSShape
}

// TODO Function to convert R1CS to CCS
// Put here or in r1cs module
// R1CS-to-CCS parameters:
// n=n, m=m, N=N, l=l, t=3, q=2, d=2
// M={A,B,C}, S={{0, 1}, {2}}, c={1,−1}

// TODO: CCSShape implementation
impl<G: Group> R1CSShape<G> {
    /// Create an object of type `R1CSShape` from the explicitly specified R1CS matrices
    pub fn new(
      num_cons: usize,
      num_vars: usize,
      num_io: usize,
      A: &[(usize, usize, G::Scalar)],
      B: &[(usize, usize, G::Scalar)],
      C: &[(usize, usize, G::Scalar)],
    ) -> Result<R1CSShape<G>, NovaError> {
      let is_valid = |num_cons: usize,
                      num_vars: usize,
                      num_io: usize,
                      M: &[(usize, usize, G::Scalar)]|
       -> Result<(), NovaError> {
        let res = (0..M.len())
          .map(|i| {
            let (row, col, _val) = M[i];
            if row >= num_cons || col > num_io + num_vars {
              Err(NovaError::InvalidIndex)
            } else {
              Ok(())
            }
          })
          .collect::<Result<Vec<()>, NovaError>>();
  
        if res.is_err() {
          Err(NovaError::InvalidIndex)
        } else {
          Ok(())
        }
      };
  
      let res_A = is_valid(num_cons, num_vars, num_io, A);
      let res_B = is_valid(num_cons, num_vars, num_io, B);
      let res_C = is_valid(num_cons, num_vars, num_io, C);
  
      if res_A.is_err() || res_B.is_err() || res_C.is_err() {
        return Err(NovaError::InvalidIndex);
      }
  
      // We require the number of public inputs/outputs to be even
      if num_io % 2 != 0 {
        return Err(NovaError::OddInputLength);
      }
  
      let digest = Self::compute_digest(num_cons, num_vars, num_io, A, B, C);

      // TODO: We assume the following constants for now
      // # fixed parameters (and n, m, l are direct from R1CS)
      // t=3
      // q=2
      // d=2
      // S1=[0,1]
      // S2=[2]
      // S = [S1, S2]
      // c0=1
      // c1=-1
      // c = [c0, c1]
        
      let shape = R1CSShape {
        num_cons,
        num_vars,
        num_io,
        A: A.to_owned(),
        B: B.to_owned(),
        C: C.to_owned(),
        digest,
      };
  
      Ok(shape)
    }
  
    pub fn multiply_vec(
      &self,
      z: &[G::Scalar],
    ) -> Result<(Vec<G::Scalar>, Vec<G::Scalar>, Vec<G::Scalar>), NovaError> {
      if z.len() != self.num_io + self.num_vars + 1 {
        return Err(NovaError::InvalidWitnessLength);
      }
  
      // computes a product between a sparse matrix `M` and a vector `z`
      // This does not perform any validation of entries in M (e.g., if entries in `M` reference indexes outside the range of `z`)
      // This is safe since we know that `M` is valid
      let sparse_matrix_vec_product =
        |M: &Vec<(usize, usize, G::Scalar)>, num_rows: usize, z: &[G::Scalar]| -> Vec<G::Scalar> {
          (0..M.len())
            .map(|i| {
              let (row, col, val) = M[i];
              (row, val * z[col])
            })
            .fold(vec![G::Scalar::ZERO; num_rows], |mut Mz, (r, v)| {
              Mz[r] += v;
              Mz
            })
        };
  
      let (Az, (Bz, Cz)) = rayon::join(
        || sparse_matrix_vec_product(&self.A, self.num_cons, z),
        || {
          rayon::join(
            || sparse_matrix_vec_product(&self.B, self.num_cons, z),
            || sparse_matrix_vec_product(&self.C, self.num_cons, z),
          )
        },
      );
  
      Ok((Az, Bz, Cz))
    }
  
    /// Checks if the Relaxed R1CS instance is satisfiable given a witness and its shape
    pub fn is_sat_relaxed(
      &self,
      ck: &CommitmentKey<G>,
      U: &RelaxedR1CSInstance<G>,
      W: &RelaxedR1CSWitness<G>,
    ) -> Result<(), NovaError> {
      assert_eq!(W.W.len(), self.num_vars);
      assert_eq!(W.E.len(), self.num_cons);
      assert_eq!(U.X.len(), self.num_io);
  
      // verify if Az * Bz = u*Cz + E
      let res_eq: bool = {
        let z = concat(vec![W.W.clone(), vec![U.u], U.X.clone()]);
        let (Az, Bz, Cz) = self.multiply_vec(&z)?;
        assert_eq!(Az.len(), self.num_cons);
        assert_eq!(Bz.len(), self.num_cons);
        assert_eq!(Cz.len(), self.num_cons);
  
        let res: usize = (0..self.num_cons)
          .map(|i| usize::from(Az[i] * Bz[i] != U.u * Cz[i] + W.E[i]))
          .sum();
  
        res == 0
      };
  
      // verify if comm_E and comm_W are commitments to E and W
      let res_comm: bool = {
        let (comm_W, comm_E) =
          rayon::join(|| CE::<G>::commit(ck, &W.W), || CE::<G>::commit(ck, &W.E));
        U.comm_W == comm_W && U.comm_E == comm_E
      };
  
      if res_eq && res_comm {
        Ok(())
      } else {
        Err(NovaError::UnSat)
      }
    }
  
    /// Checks if the CCS instance is satisfiable given a witness and its shape
    pub fn is_sat(
      &self,
      ck: &CommitmentKey<G>,
      U: &R1CSInstance<G>,
      W: &R1CSWitness<G>,
    ) -> Result<(), NovaError> {
      assert_eq!(W.W.len(), self.num_vars);
      assert_eq!(U.X.len(), self.num_io);

        // TODO CCS check
        // Sage code to check CCS relation:
        // r = [F(0)] * m
        // for i in range(0, q):
        //     hadamard_output = [F(1)]*m
        //     for j in S[i]:
        //         hadamard_output = hadamard_product(hadamard_output,
        //                 matrix_vector_product(M[j], z))
        //
        //     r = vec_add(r, vec_elem_mul(hadamard_output, c[i]))
        // print("\nCCS relation check (∑ cᵢ ⋅ ◯ Mⱼ z == 0):", r == [0]*m)
  
      // verify if Az * Bz = u*Cz
      let res_eq: bool = {
        let z = concat(vec![W.W.clone(), vec![G::Scalar::ONE], U.X.clone()]);
        let (Az, Bz, Cz) = self.multiply_vec(&z)?;
        assert_eq!(Az.len(), self.num_cons);
        assert_eq!(Bz.len(), self.num_cons);
        assert_eq!(Cz.len(), self.num_cons);
  
        let res: usize = (0..self.num_cons)
          .map(|i| usize::from(Az[i] * Bz[i] != Cz[i]))
          .sum();
  
        res == 0
      };
  
      // verify if comm_W is a commitment to W
      let res_comm: bool = U.comm_W == CE::<G>::commit(ck, &W.W);
  
      if res_eq && res_comm {
        Ok(())
      } else {
        Err(NovaError::UnSat)
      }
    }