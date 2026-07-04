//! SHA-256 Fiat-Shamir transcript, byte-exact between host and SBF.
//!
//! The hash backend is injected as a plain function pointer so this crate
//! stays no_std and dependency-free: the host passes a sha2-backed function,
//! the SBF program passes `solana_program::hash::hashv`.
//!
//! v0 Fiat-Shamir ordering (audited in Stage 1, per design section 8.1):
//! absorb profile header, statement digest, all roots (sampling one fold
//! challenge after each root), final polynomial, grinding witness; only then
//! derive query positions.

use crate::field::{M31, QM31};

/// hashv-shaped backend: hash the concatenation of the input slices.
pub type HashFn = fn(&[&[u8]]) -> [u8; 32];

pub mod label {
    pub const PROFILE: u8 = 1;
    pub const STATEMENT: u8 = 2;
    pub const ROOT: u8 = 3;
    pub const FINAL_POLY: u8 = 4;
    pub const GRIND_NONCE: u8 = 5;
}

const DOM_ABSORB: u8 = 0x00;
const DOM_SQUEEZE: u8 = 0x01;
const DOM_ADVANCE: u8 = 0x02;
const DOM_GRIND: u8 = 0x03;

#[derive(Clone)]
pub struct Transcript {
    state: [u8; 32],
    hash: HashFn,
}

impl Transcript {
    pub fn new(hash: HashFn) -> Transcript {
        Transcript {
            state: [0u8; 32],
            hash,
        }
    }

    pub fn absorb(&mut self, label: u8, data: &[u8]) {
        self.state = (self.hash)(&[&self.state, &[DOM_ABSORB, label], data]);
    }

    /// Squeeze one 32-byte block and advance the state.
    pub fn squeeze_block(&mut self) -> [u8; 32] {
        let out = (self.hash)(&[&self.state, &[DOM_SQUEEZE]]);
        self.state = (self.hash)(&[&self.state, &[DOM_ADVANCE]]);
        out
    }

    /// Sample a QM31 challenge from one squeezed block.
    ///
    /// Each limb takes 31 bits of a LE u32 and folds the single value P to 0;
    /// the resulting bias is 1 part in 2^31 per limb — acceptable for v0 and
    /// recorded for the Stage 1 Fiat-Shamir audit.
    pub fn challenge_qm31(&mut self) -> QM31 {
        let block = self.squeeze_block();
        let mut limbs = [M31::ZERO; 4];
        for (i, limb) in limbs.iter_mut().enumerate() {
            let word = u32::from_le_bytes(block[i * 4..i * 4 + 4].try_into().unwrap());
            *limb = M31::from_u32_reduced(word);
        }
        QM31 {
            c0: crate::field::CM31 {
                a: limbs[0],
                b: limbs[1],
            },
            c1: crate::field::CM31 {
                a: limbs[2],
                b: limbs[3],
            },
        }
    }

    /// Derive `count` query positions in [0, bound) where bound is a power of
    /// two (exact-uniform masking, no modulo bias).
    pub fn challenge_queries(&mut self, count: usize, bound: u32) -> alloc::vec::Vec<u32> {
        debug_assert!(bound.is_power_of_two());
        let mask = bound - 1;
        let mut out = alloc::vec::Vec::with_capacity(count);
        'outer: loop {
            let block = self.squeeze_block();
            for word in block.chunks_exact(4) {
                if out.len() == count {
                    break 'outer;
                }
                let word = u32::from_le_bytes(word.try_into().unwrap());
                out.push(word & mask);
            }
            if out.len() == count {
                break;
            }
        }
        out
    }

    /// Grinding check: hash(state, DOM_GRIND, nonce) must have
    /// `bits` leading zero bits. Verifier-side cost: one hash call.
    pub fn grinding_ok(&self, nonce: u64, bits: u8) -> bool {
        if bits == 0 {
            return true;
        }
        let digest = (self.hash)(&[&self.state, &[DOM_GRIND], &nonce.to_le_bytes()]);
        let head = u64::from_be_bytes(digest[0..8].try_into().unwrap());
        head < (1u64 << (64 - bits as u32))
    }
}
