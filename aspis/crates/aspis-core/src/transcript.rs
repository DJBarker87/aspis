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

/// Pinned expected digest of `transcript_kat` — computed once on the host
/// (sha2 backend) and asserted bit-identical on host (`transcript_kat_pinned`
/// test) and on SBF (`TranscriptKat` program instruction, syscall backend).
/// Never edit this constant except as part of a deliberate, named transcript
/// protocol change.
pub const TRANSCRIPT_KAT_EXPECTED: [u8; 32] = [
    0x16, 0xeb, 0x0c, 0xab, 0xdd, 0x02, 0xfa, 0xbe,
    0xc9, 0x1c, 0xac, 0xe9, 0x5d, 0x2d, 0xb1, 0xa6,
    0x9f, 0xd9, 0xd8, 0xe6, 0x65, 0x10, 0x91, 0x52,
    0xf1, 0xac, 0x01, 0xf4, 0x6a, 0x9c, 0xe9, 0xa9,
];

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

/// Maximum candidate draws per QM31 limb before the transcript is declared
/// exhausted. Per-limb exhaustion probability (2^-31)^8 = 2^-248.
pub const CHALLENGE_RETRY_LIMIT: u32 = 8;

/// The bounded rejection-sampling loop ran out of retries (a 2^-248-per-limb
/// completeness event). The verifier maps this to proof rejection.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ChallengeSampleExhausted;

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

    /// Sample a QM31 challenge by per-limb rejection sampling (exactly
    /// uniform; soundness-note §3 T9).
    ///
    /// Each limb draw takes 31 bits of a LE u32 and REJECTS the single
    /// non-canonical value P, redrawing from fresh transcript bytes: retries
    /// consume the next word of the block stream, and a spent block is
    /// replaced via `squeeze_block`, which advances the duplex state — no
    /// input is ever re-hashed, so retries cannot repeat a rejected value
    /// deterministically. The retry loop is bounded (`CHALLENGE_RETRY_LIMIT`)
    /// and exhaustion is an error the verifier surfaces as proof rejection:
    /// per-limb exhaustion probability is (2^-31)^8 = 2^-248, a completeness
    /// event (soundness-note §6), the correct trade on a CU-metered chain
    /// versus an unmetered loop.
    ///
    /// In the non-rejecting case (all real transcripts, whp) this consumes
    /// exactly one block and produces the same limbs as the pre-fix sampler
    /// except on a P-hit, where the old code folded P to 0 (the ~2^-31
    /// per-limb bias this fix removes).
    pub fn challenge_qm31(&mut self) -> Result<QM31, ChallengeSampleExhausted> {
        let mut limbs = [M31::ZERO; 4];
        let mut block = self.squeeze_block();
        let mut word_index = 0usize;
        for limb in limbs.iter_mut() {
            let mut accepted = false;
            for _ in 0..CHALLENGE_RETRY_LIMIT {
                if word_index == 8 {
                    block = self.squeeze_block();
                    word_index = 0;
                }
                let word = u32::from_le_bytes(
                    block[word_index * 4..word_index * 4 + 4].try_into().unwrap(),
                );
                word_index += 1;
                let masked = word & crate::field::P;
                if masked != crate::field::P {
                    *limb = M31(masked);
                    accepted = true;
                    break;
                }
            }
            if !accepted {
                return Err(ChallengeSampleExhausted);
            }
        }
        Ok(QM31 {
            c0: crate::field::CM31 {
                a: limbs[0],
                b: limbs[1],
            },
            c1: crate::field::CM31 {
                a: limbs[2],
                b: limbs[3],
            },
        })
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

/// Known-answer transcript vector (soundness-note appendix): absorb a fixed
/// pattern, sample the full challenge menu (QM31 rejection sampler, grinding
/// check, query derivation), and fold every output into one digest. The
/// pinned expected value lives in the host test `transcript_kat_pinned` and
/// is asserted bit-identical on SBF via the program's `TranscriptKat`
/// instruction — a silent host/chain sampler divergence costs a test
/// failure here instead of a week.
pub fn transcript_kat(hash: HashFn) -> [u8; 32] {
    let mut t = Transcript::new(hash);
    t.absorb(label::PROFILE, b"aspis-transcript-kat-v1");
    t.absorb(label::STATEMENT, &[0xA5; 32]);
    let mut acc = [0u8; 32];
    for i in 0..8u8 {
        t.absorb(label::ROOT, &[i; 32]);
        let alpha = t
            .challenge_qm31()
            .expect("kat: sampler exhausted (2^-248 per limb)");
        let mut bytes = [0u8; 16];
        alpha.write_le_bytes(&mut bytes);
        acc = hash(&[&acc, &bytes]);
    }
    t.absorb(label::FINAL_POLY, &[0x77; 64]);
    let grind = t.grinding_ok(0xDEAD_BEEF, 8);
    acc = hash(&[&acc, &[grind as u8]]);
    t.absorb(label::GRIND_NONCE, &0xDEAD_BEEFu64.to_le_bytes());
    for q in t.challenge_queries(16, 1 << 10) {
        acc = hash(&[&acc, &q.to_le_bytes()]);
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{CM31, P};

    fn test_hash(inputs: &[&[u8]]) -> [u8; 32] {
        use sha2::{Digest, Sha256};
        let mut h = Sha256::new();
        for i in inputs {
            h.update(i);
        }
        h.finalize().into()
    }

    #[test]
    fn transcript_kat_pinned() {
        let digest = transcript_kat(test_hash);
        let mut hex = alloc::string::String::new();
        for b in digest {
            use core::fmt::Write;
            let _ = write!(hex, "{b:02x}");
        }
        assert_eq!(
            digest, TRANSCRIPT_KAT_EXPECTED,
            "transcript KAT drifted; computed {hex} — a deliberate protocol \
             change must re-pin TRANSCRIPT_KAT_EXPECTED and say so in the log"
        );
    }

    /// Adversarial backend: every squeezed word masks to P, so every draw is
    /// rejected and the bounded loop must exhaust with an error, not spin.
    fn all_p_hash(_inputs: &[&[u8]]) -> [u8; 32] {
        [0xFF; 32]
    }

    #[test]
    fn sampler_exhaustion_is_bounded_error() {
        let mut t = Transcript::new(all_p_hash);
        assert_eq!(t.challenge_qm31(), Err(ChallengeSampleExhausted));
    }

    /// Backend that rejects exactly the first draw: word 0 masks to P, the
    /// retry must consume the NEXT word (fresh bytes), not re-hash.
    fn first_word_p_hash(inputs: &[&[u8]]) -> [u8; 32] {
        if inputs.len() == 2 && inputs[1] == [0x01u8] {
            // DOM_SQUEEZE block: word0 = P (rejected), then 1, 2, 3, 4, ...
            let mut block = [0u8; 32];
            block[0..4].copy_from_slice(&0x7FFF_FFFFu32.to_le_bytes());
            for (w, chunk) in block[4..].chunks_exact_mut(4).enumerate() {
                chunk.copy_from_slice(&(w as u32 + 1).to_le_bytes());
            }
            block
        } else {
            test_hash(inputs)
        }
    }

    #[test]
    fn sampler_rejects_p_and_uses_fresh_word() {
        let mut t = Transcript::new(first_word_p_hash);
        let alpha = t.challenge_qm31().expect("must accept on retry");
        assert_eq!(
            alpha,
            QM31 {
                c0: CM31 {
                    a: M31(1),
                    b: M31(2)
                },
                c1: CM31 {
                    a: M31(3),
                    b: M31(4)
                },
            }
        );
        // and no limb can ever be the folded-P artifact of the old sampler
        assert!(alpha.c0.a.0 < P);
    }
}
