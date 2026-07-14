//! Host-only, verifier-neutral profile-22 unpublished-retry gate.
//!
//! This module defines a deterministic *strong* `Good22` predicate over an
//! already-derived public verifier schedule.  It does not change the proof
//! wire or the verifier acceptance predicate. The host production attempt
//! manager invokes it after building each complete candidate; the raw fixture
//! builder and verifier do not.
//!
//! The strong predicate conservatively rejects schedules on which one of the
//! canonical raw/sumcheck quotient blocks loses rank, even when the minimal
//! target-containment predicate might still accept (Boolean `z` is the
//! motivating example).  Every accepted schedule nevertheless satisfies the
//! exact protocol-coupled physical semantic, conditional zero-initial and
//! zero-terminal sumcheck, and active-helper containment checks performed by
//! the canonical rank replay.  The independent-terminal direct sum remains a
//! negative diagnostic and is not an accepting transcript view.

use aspis_core::state_only_prefix::StateOnlyTranscriptScheduleResult;
use aspis_core::HashFn;

use crate::state_only_hiding_rank::{
    probe_atomic_state_only_profile21_witness_difference_containment, StateOnlyHidingRankGateError,
    StateOnlyHidingRankGateReport,
};

pub const PROFILE22_GOOD_SCHEDULE_MAX_ATTEMPTS: usize = 16;
pub const PROFILE22_GOOD_SCHEDULE_QUERY_COUNT: usize = 16;
pub const PROFILE22_GOOD_SCHEDULE_PHYSICAL_GENERATORS_M31: usize = 16_352;
pub const PROFILE22_GOOD_SCHEDULE_LEGAL_SUMCHECK_GENERATORS_M31: usize = 1_076;
pub const PROFILE22_GOOD_SCHEDULE_INDEPENDENT_SUMCHECK_STRESS_GENERATORS_M31: usize = 1_080;

const PROFILE22_GOOD_SCHEDULE_FINGERPRINT_DOMAIN: &[u8] = b"aspis:profile22:good-schedule-gate:v1";
const PROFILE22_GOOD_SCHEDULE_DESCRIPTOR: &[u8] = b"profile=22;version=v4_s2;atomic_layout=v3;rows=1024;rate=1/512;q=16;c1=26;c2=2;gamma=exact_nonzero_qm31_retry3;factor=full_shared_linear;pcs=arity4x4;physical=active_e_r,inactive_e_r_minus_e_dc,row0_fixed,H_coupled;targets=semantic,legal_zero_initial_zero_terminal_sumcheck,active_zero_sum_helper;terminal=compressed_exact_c1_boundary;rank_field=m31;predicate=protocol_coupled_containment_v2";

/// SHA-256 under `HOST_HASH` in the frozen host artifact.  Keeping the hash
/// function explicit makes this helper usable by independent host tooling.
pub fn profile22_good_schedule_definition_fingerprint(hash: HashFn) -> [u8; 32] {
    hash(&[
        PROFILE22_GOOD_SCHEDULE_FINGERPRINT_DOMAIN,
        PROFILE22_GOOD_SCHEDULE_DESCRIPTOR,
    ])
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Profile22GoodScheduleRejection {
    /// A stronger operational rank condition failed before the minimal
    /// containment report could be constructed.  Retrying is privacy-safe,
    /// but no liveness probability is claimed for this event yet.
    ConservativeRankDeficiency(StateOnlyHidingRankGateError),
    ActiveHelperNotContained,
    PhysicalSemanticNotContained,
    LegalSumcheckNotContained,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Profile22GoodScheduleGateError {
    /// Shape/layout/encoding failures are implementation faults, not bad
    /// random schedules.  A retry manager must fail closed rather than grind
    /// through them.
    CanonicalBuilder(StateOnlyHidingRankGateError),
    DefinitionDrift(&'static str),
}

/// The only public failure of the bounded production attempt manager.  It
/// deliberately carries no attempt count, rank reason, entropy error, build
/// error, nonce-store error, timing class, or partial candidate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Profile22AttemptsExhausted;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Profile22GoodScheduleDecision {
    pub accepted: bool,
    pub rejection: Option<Profile22GoodScheduleRejection>,
    pub mask_rank_m31: usize,
    pub physical_augmented_rank_m31: usize,
    pub legal_sumcheck_augmented_rank_m31: usize,
}

impl Profile22GoodScheduleDecision {
    fn conservative_rejection(error: StateOnlyHidingRankGateError) -> Self {
        Self {
            accepted: false,
            rejection: Some(Profile22GoodScheduleRejection::ConservativeRankDeficiency(
                error,
            )),
            mask_rank_m31: 0,
            physical_augmented_rank_m31: 0,
            legal_sumcheck_augmented_rank_m31: 0,
        }
    }
}

fn classify_report(
    report: &StateOnlyHidingRankGateReport,
) -> Result<Profile22GoodScheduleDecision, Profile22GoodScheduleGateError> {
    if report.pcs_schedule != "arity4x4"
        || report.query_count != PROFILE22_GOOD_SCHEDULE_QUERY_COUNT
        || report.tail_qm31_probe
        || report.coordinate_factored_mask_columns != 0
        || report.late_switch_probe
        || !report.witness_difference_probe
    {
        return Err(Profile22GoodScheduleGateError::DefinitionDrift(
            "profile22 Good22 schedule shape",
        ));
    }
    if report.witness_semantic_superset_generators_m31
        != PROFILE22_GOOD_SCHEDULE_PHYSICAL_GENERATORS_M31
        || report.witness_legal_sumcheck_generators_m31
            != PROFILE22_GOOD_SCHEDULE_INDEPENDENT_SUMCHECK_STRESS_GENERATORS_M31
        || report.witness_coupled_legal_sumcheck_generators_m31
            != PROFILE22_GOOD_SCHEDULE_LEGAL_SUMCHECK_GENERATORS_M31
    {
        return Err(Profile22GoodScheduleGateError::DefinitionDrift(
            "profile22 Good22 source basis",
        ));
    }
    if !report.witness_semantic_sparse_dense_guard {
        return Err(Profile22GoodScheduleGateError::DefinitionDrift(
            "profile22 Good22 sparse/dense source map",
        ));
    }
    if !report.witness_coupled_terminal_identity_guard
        || !report.witness_mask_raw_kernel_terminal_zero_guard
        || !report.witness_h_zero_sumcheck_terminal_guard
        || !report.witness_mask_sumcheck_equals_terminal_kernel
        || report.witness_compatibility_rank_m31 != 4
        || report.witness_compatibility_terminal_map_rank_m31 != 4
    {
        return Err(Profile22GoodScheduleGateError::DefinitionDrift(
            "profile22 Good22 terminal-kernel proof",
        ));
    }

    let mask_rank_m31 = report.witness_direct_sum_mask_view_rank_m31.ok_or(
        Profile22GoodScheduleGateError::DefinitionDrift("profile22 Good22 literal mask View rank"),
    )?;
    let physical_augmented_rank_m31 = report
        .witness_coupled_physical_augmented_view_rank_m31
        .ok_or(Profile22GoodScheduleGateError::DefinitionDrift(
            "profile22 Good22 coupled physical View rank",
        ))?;
    let legal_sumcheck_augmented_rank_m31 = report
        .witness_coupled_legal_augmented_view_rank_m31
        .ok_or(Profile22GoodScheduleGateError::DefinitionDrift(
            "profile22 Good22 conditional legal-sumcheck View rank",
        ))?;
    let physical_contained = report.witness_coupled_physical_contained.ok_or(
        Profile22GoodScheduleGateError::DefinitionDrift(
            "profile22 Good22 coupled physical containment",
        ),
    )?;
    let legal_contained = report.witness_coupled_legal_contained.ok_or(
        Profile22GoodScheduleGateError::DefinitionDrift(
            "profile22 Good22 conditional legal-sumcheck containment",
        ),
    )?;
    let helper_contained = report.witness_coupled_helper_contained.ok_or(
        Profile22GoodScheduleGateError::DefinitionDrift(
            "profile22 Good22 coupled helper containment",
        ),
    )?;

    let rejection = if !physical_contained {
        Some(Profile22GoodScheduleRejection::PhysicalSemanticNotContained)
    } else if !legal_contained {
        Some(Profile22GoodScheduleRejection::LegalSumcheckNotContained)
    } else if !helper_contained || !report.baseline_valid_witness_containment {
        Some(Profile22GoodScheduleRejection::ActiveHelperNotContained)
    } else {
        None
    };

    Ok(Profile22GoodScheduleDecision {
        accepted: rejection.is_none(),
        rejection,
        mask_rank_m31,
        physical_augmented_rank_m31,
        legal_sumcheck_augmented_rank_m31,
    })
}

/// Evaluate the frozen, schedule-only strong `Good22` predicate.
///
/// The argument contains public verifier coins, OOD samples, fold challenges
/// and query indices.  There is no witness, realized mask, Merkle salt, root,
/// opening, retry counter, or prover-selected minor input.  The underlying
/// replay uses the atomic-v3 physical source `B_c`, expanded over M31.
///
/// This function is intentionally expensive and host-only.  The production
/// first-good worker calls it after each complete mined candidate; the
/// verifier and fixture-only raw builder do not.
pub fn evaluate_profile22_strong_good_schedule(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<Profile22GoodScheduleDecision, Profile22GoodScheduleGateError> {
    match probe_atomic_state_only_profile21_witness_difference_containment(schedule) {
        Ok(report) => classify_report(&report),
        Err(
            error @ (StateOnlyHidingRankGateError::RawC1Rank { .. }
            | StateOnlyHidingRankGateError::RawGRank { .. }
            | StateOnlyHidingRankGateError::MaskedSumcheckRank { .. }
            | StateOnlyHidingRankGateError::JointPcsRank { .. }
            | StateOnlyHidingRankGateError::HelperContainment { .. }
            | StateOnlyHidingRankGateError::WitnessRawQuotient { .. }
            | StateOnlyHidingRankGateError::WitnessSumcheckQuotient { .. }),
        ) => Ok(Profile22GoodScheduleDecision::conservative_rejection(error)),
        Err(error) => Err(Profile22GoodScheduleGateError::CanonicalBuilder(error)),
    }
}

/// Fixed-cap first-good state machine shared by the production wrapper and
/// fast synthetic tests.  All internal failures collapse to the same public
/// error.  `discard` must scrub candidate-owned buffers before drop.
pub(crate) fn run_profile22_first_good<S, C, Generate, Build, Decide, Discard>(
    mut generate: Generate,
    mut build: Build,
    mut decide: Decide,
    mut discard: Discard,
) -> Result<C, Profile22AttemptsExhausted>
where
    Generate: FnMut() -> Result<S, ()>,
    Build: FnMut(S) -> Result<C, ()>,
    Decide: FnMut(&C) -> Result<bool, ()>,
    Discard: FnMut(&mut C),
{
    for _ in 0..PROFILE22_GOOD_SCHEDULE_MAX_ATTEMPTS {
        let secret = generate().map_err(|_| Profile22AttemptsExhausted)?;
        let mut candidate = build(secret).map_err(|_| Profile22AttemptsExhausted)?;
        match decide(&candidate) {
            Ok(true) => return Ok(candidate),
            Ok(false) => discard(&mut candidate),
            Err(()) => {
                discard(&mut candidate);
                return Err(Profile22AttemptsExhausted);
            }
        }
    }
    Err(Profile22AttemptsExhausted)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn definition_fingerprint_is_frozen() {
        assert_eq!(
            profile22_good_schedule_definition_fingerprint(crate::HOST_HASH),
            [
                0x59, 0xea, 0x6e, 0x29, 0xe7, 0x23, 0x1a, 0x43, 0x46, 0xd9, 0x40, 0x35, 0xaf, 0xc6,
                0x21, 0x3b, 0x2b, 0x4e, 0x8f, 0x57, 0xfb, 0x50, 0x56, 0x15, 0xb6, 0xf5, 0x41, 0x19,
                0xe1, 0xef, 0x83, 0x9b,
            ]
        );
        assert_eq!(PROFILE22_GOOD_SCHEDULE_MAX_ATTEMPTS, 16);
        assert_eq!(PROFILE22_GOOD_SCHEDULE_LEGAL_SUMCHECK_GENERATORS_M31, 1_076);
    }

    #[test]
    fn conservative_rank_failure_is_never_reclassified_as_fatal_or_good() {
        let error = StateOnlyHidingRankGateError::MaskedSumcheckRank {
            got: 1_076,
            want: 1_080,
        };
        let decision = Profile22GoodScheduleDecision::conservative_rejection(error);
        assert!(!decision.accepted);
        assert_eq!(
            decision.rejection,
            Some(Profile22GoodScheduleRejection::ConservativeRankDeficiency(
                error
            ))
        );
    }

    #[test]
    fn bounded_manager_discards_bad_attempts_and_returns_first_good() {
        let mut generated = 0usize;
        let mut discarded = Vec::new();
        let result = run_profile22_first_good(
            || {
                generated += 1;
                Ok(generated)
            },
            |attempt| Ok(attempt),
            |candidate| Ok(*candidate == 3),
            |candidate| {
                discarded.push(*candidate);
                *candidate = 0;
            },
        )
        .unwrap();
        assert_eq!(result, 3);
        assert_eq!(generated, 3);
        assert_eq!(discarded, [1, 2]);
    }

    #[test]
    fn bounded_manager_all_bad_has_one_generic_failure_at_exact_cap() {
        let mut generated = 0usize;
        let mut discarded = 0usize;
        let result = run_profile22_first_good(
            || {
                generated += 1;
                Ok(generated)
            },
            |attempt| Ok(attempt),
            |_| Ok(false),
            |candidate| {
                *candidate = 0;
                discarded += 1;
            },
        );
        assert_eq!(result, Err(Profile22AttemptsExhausted));
        assert_eq!(generated, PROFILE22_GOOD_SCHEDULE_MAX_ATTEMPTS);
        assert_eq!(discarded, PROFILE22_GOOD_SCHEDULE_MAX_ATTEMPTS);
    }

    #[test]
    fn bounded_manager_collapses_controlled_internal_failures() {
        let generation: Result<u8, _> =
            run_profile22_first_good(|| Err(()), Ok, |_| Ok(true), |_| {});
        assert_eq!(generation, Err(Profile22AttemptsExhausted));

        let build: Result<u8, _> =
            run_profile22_first_good(|| Ok(7u8), |_| Err(()), |_| Ok(true), |_| {});
        assert_eq!(build, Err(Profile22AttemptsExhausted));

        let mut discarded = false;
        let decision = run_profile22_first_good(
            || Ok(7u8),
            Ok,
            |_| Err(()),
            |candidate| {
                *candidate = 0;
                discarded = true;
            },
        );
        assert_eq!(decision, Err(Profile22AttemptsExhausted));
        assert!(discarded);
    }
}
