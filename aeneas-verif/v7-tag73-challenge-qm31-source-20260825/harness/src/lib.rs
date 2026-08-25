#![allow(dead_code)]

use aspis_core::field::QM31;
use aspis_core::transcript::{ChallengeSampleExhausted, Transcript};

/// Extraction root only.  This delegates to the unchanged deployed method
/// and returns the updated transcript so Aeneas exposes the full state
/// transition as part of the result.
pub fn extract_challenge_qm31(
    mut transcript: Transcript,
) -> (Result<QM31, ChallengeSampleExhausted>, Transcript) {
    let result = transcript.challenge_qm31();
    (result, transcript)
}
