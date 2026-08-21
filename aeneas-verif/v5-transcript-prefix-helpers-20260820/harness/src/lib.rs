#![allow(dead_code)]

use aspis_core::field::QM31;
use aspis_core::state_only_hiding::{
    begin_state_only_masked_sumcheck, StateOnlyHidingScheduleError,
};
use aspis_core::state_only_sumcheck::{
    begin_state_only_zerocheck, verify_state_only_sumcheck_streaming,
    StateOnlySumcheckVerification, StateOnlySumcheckVerifyError,
};
use aspis_core::statement_sumcheck::PaymentConstraintChallenges;
use aspis_core::transcript::{ChallengeSampleExhausted, Transcript};

/// Extraction root only: delegate to the unchanged production helper and
/// return the updated transcript explicitly.
pub fn extract_begin_state_only_zerocheck(
    mut transcript: Transcript,
) -> (
    Result<PaymentConstraintChallenges, ChallengeSampleExhausted>,
    Transcript,
) {
    let result = begin_state_only_zerocheck(&mut transcript);
    (result, transcript)
}

/// Extraction root only: delegate to the unchanged production helper and
/// return the updated transcript explicitly.
pub fn extract_begin_state_only_masked_sumcheck(
    mut transcript: Transcript,
    initial_claim: QM31,
) -> (Result<QM31, StateOnlyHidingScheduleError>, Transcript) {
    let result = begin_state_only_masked_sumcheck(&mut transcript, initial_claim);
    (result, transcript)
}

/// Extraction root only: delegate to the unchanged production helper and
/// return the updated transcript explicitly.
pub fn extract_verify_state_only_sumcheck_streaming(
    mut transcript: Transcript,
    proof: &[u8],
    initial_claim: QM31,
) -> (
    Result<StateOnlySumcheckVerification, StateOnlySumcheckVerifyError>,
    Transcript,
) {
    let result = verify_state_only_sumcheck_streaming(&mut transcript, proof, initial_claim);
    (result, transcript)
}
