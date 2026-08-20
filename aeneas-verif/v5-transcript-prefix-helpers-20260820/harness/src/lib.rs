#![allow(dead_code)]

use aspis_core::field::QM31;
use aspis_core::state_only_hiding::{
    begin_state_only_masked_sumcheck, StateOnlyHidingScheduleError,
};
use aspis_core::state_only_sumcheck::begin_state_only_zerocheck;
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
