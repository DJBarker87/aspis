use crate::field::LiftPolicy;
use crate::merkle::{hash_leaf, verify_path_bytes};
use crate::profile::{profile_manifest, ProfileId, WhirProfileManifest};
use crate::proof::{evaluate_block_for_verifier, ParseError, WhirEnvelopeView};
use crate::statement::SpendV0Binding;
use crate::transcript::Transcript;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VerifyError {
    Parse(ParseError),
    StatementDigestMismatch,
    CurrentMerkleMismatch { round: usize, repetition: usize },
    NextMerkleMismatch { round: usize, repetition: usize },
    FoldMismatch { round: usize, repetition: usize },
    FinalValueMismatch { round: usize, repetition: usize },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct VerificationReport {
    pub proof_bytes: usize,
    pub round_count: usize,
    pub query_repetitions_per_round: usize,
}

impl From<ParseError> for VerifyError {
    fn from(value: ParseError) -> Self {
        Self::Parse(value)
    }
}

pub fn verify_proof_bytes(
    profile_id: ProfileId,
    binding: &SpendV0Binding,
    proof_bytes: &[u8],
) -> Result<VerificationReport, VerifyError> {
    let profile = profile_manifest(profile_id);
    verify_proof_with_manifest(profile, binding, proof_bytes)
}

pub fn verify_proof_with_manifest(
    profile: &'static WhirProfileManifest,
    binding: &SpendV0Binding,
    proof_bytes: &[u8],
) -> Result<VerificationReport, VerifyError> {
    let view = WhirEnvelopeView::parse(profile, proof_bytes)?;
    if view.statement_digest() != binding.digest() {
        return Err(VerifyError::StatementDigestMismatch);
    }

    let mut transcript = Transcript::new(profile.id, &view.statement_digest());
    let mut round_challenges = [(crate::field::Qm31::ZERO, crate::field::Qm31::ZERO); 8];
    let mut round = 0;
    while round < profile.round_count() {
        let root = view.round_root(round);
        transcript.absorb_root(round, &root.0);
        round_challenges[round] = transcript.sample_round_challenge_pair(round);
        round += 1;
    }
    let final_value = view.final_value()?;
    let final_bytes = final_value.to_m31_array().map(|v| v.as_u32().to_le_bytes());
    let mut packed_final = [0_u8; 16];
    let mut offset = 0;
    while offset < 4 {
        packed_final[offset * 4..offset * 4 + 4].copy_from_slice(&final_bytes[offset]);
        offset += 1;
    }
    transcript.absorb_final_value(&packed_final);

    round = 0;
    while round < profile.round_count() {
        let (x, y) = round_challenges[round];
        let mut repetition = 0;
        while repetition < profile.query_repetitions_per_round as usize {
            let domain = profile.block_count_at_round(round);
            let query_index = transcript.sample_query_index(round, repetition, domain);
            let opening = view.query_opening(round, repetition)?;
            let current_hash = hash_leaf(opening.current_block_bytes());
            if !verify_path_bytes(
                current_hash,
                query_index,
                opening.current_siblings_bytes(),
                &view.round_root(round).0,
            ) {
                return Err(VerifyError::CurrentMerkleMismatch { round, repetition });
            }

            let current_block = opening.current_block()?;

            let next_block = if round + 1 < profile.round_count() {
                let hash = hash_leaf(opening.next_block_bytes());
                if !verify_path_bytes(
                    hash,
                    query_index >> profile.fold_vars_per_round,
                    opening.next_siblings_bytes(),
                    &view.round_root(round + 1).0,
                ) {
                    return Err(VerifyError::NextMerkleMismatch { round, repetition });
                }
                Some(opening.next_block()?)
            } else {
                None
            };

            let (expected, actual) = evaluate_block_for_verifier(
                current_block,
                next_block,
                query_index,
                x,
                y,
                LiftPolicy::LateQm31,
            );
            if round + 1 < profile.round_count() {
                if actual.expect("missing actual") != expected {
                    return Err(VerifyError::FoldMismatch { round, repetition });
                }
            } else if expected != final_value {
                return Err(VerifyError::FinalValueMismatch { round, repetition });
            }
            repetition += 1;
        }
        round += 1;
    }

    Ok(VerificationReport {
        proof_bytes: proof_bytes.len(),
        round_count: profile.round_count(),
        query_repetitions_per_round: profile.query_repetitions_per_round as usize,
    })
}
