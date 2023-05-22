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

// A type that holds the shape of a CCS instance
// Unlike R1CS we have a list of matrices M instead of only A, B, C
// We also have t, q, d constants and c (vector), S (set)
// TODO Add c and S

// Make CCShape default to these values:
// n=n, m=m, N=N, l=l, t=3, q=2, d=2
// M={A,B,C}, S={{0, 1}, {2}}, c={1,−1}
pub struct CCSShape<G: Group> {
    pub(crate) num_cons: usize,
    pub(crate) num_vars: usize,
    pub(crate) num_io: usize,
    pub(crate) M: Vec<Vec<(usize, usize, G::Scalar)>>,
    pub(crate) t: usize,
    pub(crate) q: usize,
    pub(crate) d: usize,
    pub(crate) S: Vec<Vec<usize>>,
    pub(crate) c: Vec<usize>,
    digest: G::Scalar, // digest of the rest of CCSShape
}

// TODO Function to convert R1CS to CCS
// Put here or in r1cs module

// TODO: CCSShape implementation

impl<G: Group> CCSShape<G> {
    /// Create an object of type `CCSSShape` from the explicitly specified CCS matrices
    pub fn new(
      num_cons: usize,
      num_vars: usize,
      num_io: usize,
      M: &[Vec<(usize, usize, G::Scalar)>],
    ) -> Result<CCSShape<G>, NovaError> {
      let is_valid = |num_cons: usize,
                      num_vars: usize,
                      num_io: usize,
                      matrix: &[(usize, usize, G::Scalar)]|
       -> Result<(), NovaError> {
        let res = (0..matrix.len())
          .map(|i| {
            let (row, col, _val) = matrix[i];
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

      // Check that the row and column indexes are within the range of the number of constraints and variables
      let res_M = M
        .iter()
        .map(|m| is_valid(num_cons, num_vars, num_io, m))
        .collect::<Result<Vec<()>, NovaError>>();

      // If any of the matricies are invalid, return an error
      if res_M.is_err() {
        return Err(NovaError::InvalidIndex);
      }
  
      // We require the number of public inputs/outputs to be even
      if num_io % 2 != 0 {
        return Err(NovaError::OddInputLength);
      }
  
      let digest = Self::compute_digest(num_cons, num_vars, num_io, M);

      // NOTE: We assume the following constants for R1CS-to-CCS
      const T: usize = 3;
      const Q: usize = 2;
      const D: usize = 2;
      const S: [[usize; 2]; 1] = [[0, 1]];
      const S2: [usize; 1] = [2];
      const C0: i32 = 1;
      const C1: i32 = -1;

      let shape = CCSShape {
        num_cons,
        num_vars,
        num_io,
        M: M.to_vec(),
        t: T,
        q: Q,
        d: D,
        S: vec![S[0].to_vec(), S2.to_vec()],
        c: vec![C0 as usize, C1 as usize],
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

      /// A method to compute a commitment to the cross-term `T` given a
  /// Relaxed R1CS instance-witness pair and an R1CS instance-witness pair
  pub fn commit_T(
    &self,
    ck: &CommitmentKey<G>,
    U1: &RelaxedR1CSInstance<G>,
    W1: &RelaxedR1CSWitness<G>,
    U2: &R1CSInstance<G>,
    W2: &R1CSWitness<G>,
  ) -> Result<(Vec<G::Scalar>, Commitment<G>), NovaError> {
    let (AZ_1, BZ_1, CZ_1) = {
      let Z1 = concat(vec![W1.W.clone(), vec![U1.u], U1.X.clone()]);
      self.multiply_vec(&Z1)?
    };

    let (AZ_2, BZ_2, CZ_2) = {
      let Z2 = concat(vec![W2.W.clone(), vec![G::Scalar::ONE], U2.X.clone()]);
      self.multiply_vec(&Z2)?
    };

    let AZ_1_circ_BZ_2 = (0..AZ_1.len())
      .into_par_iter()
      .map(|i| AZ_1[i] * BZ_2[i])
      .collect::<Vec<G::Scalar>>();
    let AZ_2_circ_BZ_1 = (0..AZ_2.len())
      .into_par_iter()
      .map(|i| AZ_2[i] * BZ_1[i])
      .collect::<Vec<G::Scalar>>();
    let u_1_cdot_CZ_2 = (0..CZ_2.len())
      .into_par_iter()
      .map(|i| U1.u * CZ_2[i])
      .collect::<Vec<G::Scalar>>();
    let u_2_cdot_CZ_1 = (0..CZ_1.len())
      .into_par_iter()
      .map(|i| CZ_1[i])
      .collect::<Vec<G::Scalar>>();

    let T = AZ_1_circ_BZ_2
      .par_iter()
      .zip(&AZ_2_circ_BZ_1)
      .zip(&u_1_cdot_CZ_2)
      .zip(&u_2_cdot_CZ_1)
      .map(|(((a, b), c), d)| *a + *b - *c - *d)
      .collect::<Vec<G::Scalar>>();

    let comm_T = CE::<G>::commit(ck, &T);

    Ok((T, comm_T))
  }

  /// returns the digest of R1CSShape
  pub fn get_digest(&self) -> G::Scalar {
    self.digest
  }

  fn compute_digest(
    num_cons: usize,
    num_vars: usize,
    num_io: usize,
    M: &[Vec<(usize, usize, G::Scalar)>],
  ) -> G::Scalar {
    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    struct CCSShapeWithoutDigest<G: Group> {
      num_cons: usize,
      num_vars: usize,
      num_io: usize,
      M: Vec<Vec<(usize, usize, G::Scalar)>>,
    }

    let shape = CCSShapeWithoutDigest::<G> {
      num_cons,
      num_vars,
      num_io,
      M: M.to_vec(),
    };

    // obtain a vector of bytes representing the CCS shape
    let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
    bincode::serialize_into(&mut encoder, &shape).unwrap();
    let shape_bytes = encoder.finish().unwrap();

    // convert shape_bytes into a short digest
    let mut hasher = Sha3_256::new();
    hasher.input(&shape_bytes);
    let digest = hasher.result();

    // truncate the digest to 250 bits
    let bv = (0..NUM_HASH_BITS).map(|i| {
      let (byte_pos, bit_pos) = (i / 8, i % 8);
      let bit = (digest[byte_pos] >> bit_pos) & 1;
      bit == 1
    });

    // turn the bit vector into a scalar
    let mut res = G::Scalar::ZERO;
    let mut coeff = G::Scalar::ONE;
    for bit in bv {
      if bit {
        res += coeff;
      }
      coeff += coeff;
    }
    res
  }

  /// Pads the R1CSShape so that the number of variables is a power of two
  /// Renumbers variables to accomodate padded variables
  pub fn pad(&self) -> Self {
    // equalize the number of variables and constraints
    let m = max(self.num_vars, self.num_cons).next_power_of_two();

    // check if the provided R1CSShape is already as required
    if self.num_vars == m && self.num_cons == m {
      return self.clone();
    }

    // check if the number of variables are as expected, then
    // we simply set the number of constraints to the next power of two
    if self.num_vars == m {
      let digest = Self::compute_digest(m, self.num_vars, self.num_io, &self.M);

      return CCSShape {
        num_cons: m,
        num_vars: m,
        num_io: self.num_io,
        M: self.M.clone(),
        digest,
      };
    }

    // otherwise, we need to pad the number of variables and renumber variable accesses
    let num_vars_padded = m;
    let num_cons_padded = m;
    let apply_pad = |M: &[(usize, usize, G::Scalar)]| -> Vec<(usize, usize, G::Scalar)> {
      M.par_iter()
        .map(|(r, c, v)| {
          (
            *r,
            if c >= &self.num_vars {
              c + num_vars_padded - self.num_vars
            } else {
              *c
            },
            *v,
          )
        })
        .collect::<Vec<_>>()
    };

  
    // Apply pad for each matrix in M
    let M_padded = self.M.iter().map(|m| apply_pad(m)).collect::<Vec<_>>();

    let digest = Self::compute_digest(
      num_cons_padded,
      num_vars_padded,
      self.num_io,
      &M_padded,
    );

    CCSShape {
      num_cons: num_cons_padded,
      num_vars: num_vars_padded,
      num_io: self.num_io,
      M: M_padded,
      digest,
    }
  }
}