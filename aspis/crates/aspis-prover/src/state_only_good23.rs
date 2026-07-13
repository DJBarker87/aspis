//! Host-only Profile-23 complete-Good predicate and q3 selector.
//!
//! This module does not build proofs, mutate a prefix, publish a selector or
//! authorize release.  It replays three independent copies of the same
//! pre-query transcript, absorbs exactly one selector byte (`0`, `1`, or
//! `2`) into each copy, evaluates every resulting schedule, and reports the
//! least good selector. The production builder in `state_only_profile23`
//! retains one common attempt, calls this gate, serializes only the selected
//! branch, and scrubs or retries behind an opaque cap-16 boundary.

use aspis_core::state_only_hiding::{
    PINNED_ATOMIC_STATE_ONLY_PROFILE23_LAYOUT_FACTOR_FINGERPRINT_V3,
    STATE_ONLY_PROFILE23_C2_COLUMNS, STATE_ONLY_PROFILE23_D_FACTOR_IDENTIFIER,
    STATE_ONLY_PROFILE23_D_GENERATOR_INDEX, STATE_ONLY_PROFILE23_G_GENERATOR_INDEX,
    STATE_ONLY_PROFILE23_H_GENERATOR_INDEX, STATE_ONLY_PROFILE23_QUERY_CANDIDATES,
    STATE_ONLY_PROFILE23_TOTAL_GENERATOR_WIDTH,
};
use aspis_core::state_only_prefix::{
    run_atomic_state_only_profile23_transcript_schedule_host_unmined_for_diagnostics_v3,
    run_atomic_state_only_profile23_transcript_schedule_host_v3, StateOnlyProfile23Prefix,
    StateOnlyTranscriptError, StateOnlyTranscriptScheduleResult, STATE_ONLY_LOG_ROWS,
    STATE_ONLY_PROFILE23_QUERY_CANDIDATE_COUNT, STATE_ONLY_PROFILE23_ZERO_FACTOR_SHAPE,
};
use aspis_core::HashFn;

use crate::state_only_hiding_rank::{
    bind_profile23_complete_good_product_provenance,
    probe_atomic_state_only_profile22_zero_factor_qm31_tail_root_neutral,
    probe_profile22_root_neutral_polynomial_kernel_rank, StateOnlyHidingRankGateError,
};

pub const PROFILE23_GOOD_SCHEDULE_MAX_ATTEMPTS: usize = 16;
pub const PROFILE23_GOOD_SCHEDULE_QUERY_CANDIDATES: usize = 3;
pub const PROFILE23_GOOD_SCHEDULE_QUERY_COUNT: usize = 16;
pub const PROFILE23_GOOD_SCHEDULE_INVERSE_RATE: usize = 512;
pub const PROFILE23_GOOD_SCHEDULE_DOMAIN_LOG: u32 = 19;
pub const PROFILE23_GOOD_SCHEDULE_QUERY_FIBERS: usize = 131_072;
pub const PROFILE23_GOOD_SCHEDULE_ROOT_NEUTRAL_RANK_M31: usize = 1_404;
pub const PROFILE23_GOOD_SCHEDULE_RAW_QUERY_RANK_M31: usize = 256;
pub const PROFILE23_GOOD_SCHEDULE_RAW_TERMINAL_RANK_M31: usize = 12;
pub const PROFILE23_GOOD_SCHEDULE_Q_DEGREE: usize = 28_544;
pub const PROFILE23_GOOD_SCHEDULE_ROOT_Z_DEGREE: usize = 41_040;
pub const PROFILE23_GOOD_SCHEDULE_COMPLETE_Z_DEGREE: usize = 41_280;
pub const PROFILE23_GOOD_SCHEDULE_GAMMA_DEGREE: usize = 92_436;
pub const PROFILE23_GOOD_SCHEDULE_CONTINUOUS_DEGREE: usize = 133_716;

/// Frozen witnesses used to prove the bad-schedule probability bound.  The
/// runtime echelon replay may select different full-rank minors, so these are
/// provenance anchors and are deliberately not runtime equality predicates.
pub const PROFILE23_GOOD_SCHEDULE_ROOT_ANCHOR_FINGERPRINT: u64 = 0xb747_2b1f_2b1d_03e7;
pub const PROFILE23_GOOD_SCHEDULE_GD_ANCHOR_FINGERPRINT: u64 = 0x0a2d_bf8f_1a90_59c0;
pub const PROFILE23_GOOD_SCHEDULE_H1_ANCHOR_FINGERPRINT: u64 = 0x5c61_aee3_83df_f271;
pub const PROFILE23_GOOD_SCHEDULE_PRODUCT_ANCHOR_FINGERPRINT: u64 = 0x1d66_9744_7b7a_1448;

const PROFILE23_GOOD_SCHEDULE_FINGERPRINT_DOMAIN: &[u8] = b"aspis:profile23:good-schedule-gate:v1";
const PROFILE23_GOOD_SCHEDULE_DESCRIPTOR: &[u8] = b"profile=23;version=v4_s2;atomic_layout=v3;rows=1024;rate=1/512;domain_log=19;q=16;query_fibers=131072;query_candidates=3;attempt_cap=16;generator_order=semantic0..15,mask16..25,H26,G27,D28;layout_fp=0x233ba2ca68f94148;predicate=root_neutral1404+remaining_gd_schur12+h1_inactive_schur12;q_degree=28544;z_degree=41280;gamma_degree=92436;continuous_degree=133716;selector=three_independent_post_final_label44_clones_choose_least;runtime_minor_fingerprint=dynamic;anchor_product=0x1d6697447b7a1448";

pub fn profile23_good_schedule_definition_fingerprint(hash: HashFn) -> [u8; 32] {
    hash(&[
        PROFILE23_GOOD_SCHEDULE_FINGERPRINT_DOMAIN,
        PROFILE23_GOOD_SCHEDULE_DESCRIPTOR,
    ])
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Profile23GoodScheduleRejection {
    RootNeutralIncomplete,
    RemainingGdOrH1RawIncomplete,
    ConservativeRawRankDeficiency(StateOnlyHidingRankGateError),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Profile23GoodScheduleGateError {
    CanonicalBuilder(StateOnlyHidingRankGateError),
    Transcript(StateOnlyTranscriptError),
    DefinitionDrift(&'static str),
}

/// The only public failure of the bounded production attempt manager. It
/// intentionally carries no retry count, selector, rank reason, entropy
/// error, build error, timing class, or partial candidate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Profile23AttemptsExhausted;

/// Private control result of one durably reserved attempt. `Retry` is used
/// only when the exact Good23 predicate successfully evaluated all three
/// schedules and found none good. Builder/gate/schema failures are `Err(())`
/// and stop the worker immediately (with the same opaque public outcome).
pub(crate) enum Profile23AttemptBuild<C> {
    Candidate(C),
    Retry,
}

impl From<StateOnlyTranscriptError> for Profile23GoodScheduleGateError {
    fn from(error: StateOnlyTranscriptError) -> Self {
        Self::Transcript(error)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Profile23GoodScheduleDecision {
    pub accepted: bool,
    pub rejection: Option<Profile23GoodScheduleRejection>,
    pub root_neutral_rank_m31: usize,
    pub remaining_gd_query_rank_m31: usize,
    pub remaining_gd_terminal_rank_m31: usize,
    pub h1_query_rank_m31: usize,
    pub h1_terminal_rank_m31: usize,
    pub dynamic_root_minor_fingerprint: u64,
    pub dynamic_remaining_gd_minor_fingerprint: u64,
    pub dynamic_h1_minor_fingerprint: u64,
    pub dynamic_product_fingerprint: u64,
}

impl Profile23GoodScheduleDecision {
    fn rejected(rejection: Profile23GoodScheduleRejection, root_neutral_rank_m31: usize) -> Self {
        Self {
            accepted: false,
            rejection: Some(rejection),
            root_neutral_rank_m31,
            remaining_gd_query_rank_m31: 0,
            remaining_gd_terminal_rank_m31: 0,
            h1_query_rank_m31: 0,
            h1_terminal_rank_m31: 0,
            dynamic_root_minor_fingerprint: 0,
            dynamic_remaining_gd_minor_fingerprint: 0,
            dynamic_h1_minor_fingerprint: 0,
            dynamic_product_fingerprint: 0,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Profile23QueryCandidateEvaluation {
    pub decisions: [Profile23GoodScheduleDecision; PROFILE23_GOOD_SCHEDULE_QUERY_CANDIDATES],
    pub selected_selector: Option<u8>,
}

fn strict_static_definition() -> Result<(), Profile23GoodScheduleGateError> {
    let shape = STATE_ONLY_PROFILE23_ZERO_FACTOR_SHAPE;
    if PROFILE23_GOOD_SCHEDULE_QUERY_CANDIDATES != STATE_ONLY_PROFILE23_QUERY_CANDIDATES
        || PROFILE23_GOOD_SCHEDULE_QUERY_CANDIDATES
            != usize::from(STATE_ONLY_PROFILE23_QUERY_CANDIDATE_COUNT)
        || PROFILE23_GOOD_SCHEDULE_QUERY_COUNT != usize::from(shape.query_count)
        || PROFILE23_GOOD_SCHEDULE_INVERSE_RATE != 1usize << shape.log_blowup
        || PROFILE23_GOOD_SCHEDULE_DOMAIN_LOG != STATE_ONLY_LOG_ROWS + shape.log_blowup
        || PROFILE23_GOOD_SCHEDULE_QUERY_FIBERS
            != 1usize << (PROFILE23_GOOD_SCHEDULE_DOMAIN_LOG - 2)
        || STATE_ONLY_PROFILE23_TOTAL_GENERATOR_WIDTH != 29
        || STATE_ONLY_PROFILE23_H_GENERATOR_INDEX != 26
        || STATE_ONLY_PROFILE23_G_GENERATOR_INDEX != 27
        || STATE_ONLY_PROFILE23_D_GENERATOR_INDEX != 28
        || STATE_ONLY_PROFILE23_D_FACTOR_IDENTIFIER != 0
        || STATE_ONLY_PROFILE23_C2_COLUMNS != 3
        || PINNED_ATOMIC_STATE_ONLY_PROFILE23_LAYOUT_FACTOR_FINGERPRINT_V3 != 0x233b_a2ca_68f9_4148
    {
        return Err(Profile23GoodScheduleGateError::DefinitionDrift(
            "profile23 static shape, layout or cap",
        ));
    }
    Ok(())
}

fn validate_schedule_queries(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<(), Profile23GoodScheduleGateError> {
    if schedule.query_count != PROFILE23_GOOD_SCHEDULE_QUERY_COUNT {
        return Err(Profile23GoodScheduleGateError::DefinitionDrift(
            "profile23 candidate q16 count",
        ));
    }
    if schedule.queries[..schedule.query_count]
        .iter()
        .any(|&query| query >= PROFILE23_GOOD_SCHEDULE_QUERY_FIBERS as u32)
    {
        return Err(Profile23GoodScheduleGateError::DefinitionDrift(
            "profile23 candidate query outside q-fiber domain",
        ));
    }
    for left in 0..schedule.query_count {
        for right in 0..left {
            if schedule.queries[left] == schedule.queries[right] {
                return Err(Profile23GoodScheduleGateError::DefinitionDrift(
                    "profile23 candidate contains duplicate query",
                ));
            }
        }
    }
    Ok(())
}

/// Evaluate all three blocks of the exact prospective Profile-23 Good
/// predicate on one already-derived public schedule.
pub fn evaluate_profile23_strong_good_schedule(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<Profile23GoodScheduleDecision, Profile23GoodScheduleGateError> {
    strict_static_definition()?;
    validate_schedule_queries(schedule)?;

    let root = match probe_profile22_root_neutral_polynomial_kernel_rank(schedule) {
        Ok(report) => report,
        Err(error @ StateOnlyHidingRankGateError::Relation) => {
            return Ok(Profile23GoodScheduleDecision::rejected(
                Profile23GoodScheduleRejection::ConservativeRawRankDeficiency(error),
                0,
            ));
        }
        Err(error) => return Err(Profile23GoodScheduleGateError::CanonicalBuilder(error)),
    };
    if root.generator_order != "semantic0..15,mask-only16..25,H26,G27,D28"
        || root.query_count != PROFILE23_GOOD_SCHEDULE_QUERY_COUNT
        || root.joint_target_rank_m31 != PROFILE23_GOOD_SCHEDULE_ROOT_NEUTRAL_RANK_M31
        || root.root_neutral_target_rank_m31 != 1_076
        || root.semantic_lanes != 16
        || root.mask_only_lanes != 10
        || root.d_tower_coordinates != 4
        || root.z_total_degree_bound != PROFILE23_GOOD_SCHEDULE_ROOT_Z_DEGREE
    {
        return Err(Profile23GoodScheduleGateError::DefinitionDrift(
            "profile23 root-neutral report schema",
        ));
    }
    if !root.complete {
        return Ok(Profile23GoodScheduleDecision::rejected(
            Profile23GoodScheduleRejection::RootNeutralIncomplete,
            root.joint_rank_m31,
        ));
    }

    let raw = match probe_atomic_state_only_profile22_zero_factor_qm31_tail_root_neutral(schedule) {
        Ok(report) => report,
        Err(
            error @ (StateOnlyHidingRankGateError::RawC1Rank { .. }
            | StateOnlyHidingRankGateError::RawGRank { .. }
            | StateOnlyHidingRankGateError::Relation),
        ) => {
            return Ok(Profile23GoodScheduleDecision::rejected(
                Profile23GoodScheduleRejection::ConservativeRawRankDeficiency(error),
                root.joint_rank_m31,
            ));
        }
        Err(error) => return Err(Profile23GoodScheduleGateError::CanonicalBuilder(error)),
    };
    if raw.production_h_generator_index != 26
        || raw.production_g_generator_index != 27
        || raw.tail_generator_index != 28
        || raw.generator_width_before != 28
        || raw.generator_width_after != 29
        || raw.qm31_raw_target_m31 != 268
        || raw.conditional_target_m31 != 1_076
        || raw.remaining_gd_terminal_schur_z_degree != 120
        || raw.h1_inactive_padding_terminal_schur_z_degree != 120
    {
        return Err(Profile23GoodScheduleGateError::DefinitionDrift(
            "profile23 raw Schur report schema",
        ));
    }
    if !raw.complete
        || raw.remaining_gd_query_rank_m31 != PROFILE23_GOOD_SCHEDULE_RAW_QUERY_RANK_M31
        || raw.remaining_gd_terminal_schur_rank_m31 != PROFILE23_GOOD_SCHEDULE_RAW_TERMINAL_RANK_M31
        || raw.h1_inactive_padding_query_rank_m31 != PROFILE23_GOOD_SCHEDULE_RAW_QUERY_RANK_M31
        || raw.h1_inactive_padding_terminal_schur_rank_m31
            != PROFILE23_GOOD_SCHEDULE_RAW_TERMINAL_RANK_M31
    {
        return Ok(Profile23GoodScheduleDecision {
            accepted: false,
            rejection: Some(Profile23GoodScheduleRejection::RemainingGdOrH1RawIncomplete),
            root_neutral_rank_m31: root.joint_rank_m31,
            remaining_gd_query_rank_m31: raw.remaining_gd_query_rank_m31,
            remaining_gd_terminal_rank_m31: raw.remaining_gd_terminal_schur_rank_m31,
            h1_query_rank_m31: raw.h1_inactive_padding_query_rank_m31,
            h1_terminal_rank_m31: raw.h1_inactive_padding_terminal_schur_rank_m31,
            dynamic_root_minor_fingerprint: root.minor.fingerprint,
            dynamic_remaining_gd_minor_fingerprint: raw
                .remaining_gd_terminal_schur_minor
                .fingerprint,
            dynamic_h1_minor_fingerprint: raw.h1_inactive_padding_terminal_schur_minor.fingerprint,
            dynamic_product_fingerprint: 0,
        });
    }

    let product = bind_profile23_complete_good_product_provenance(&root, &raw)
        .map_err(Profile23GoodScheduleGateError::CanonicalBuilder)?;
    if product.root_neutral_minor_rank_m31 != PROFILE23_GOOD_SCHEDULE_ROOT_NEUTRAL_RANK_M31
        || product.remaining_gd_terminal_schur_rank_m31
            != PROFILE23_GOOD_SCHEDULE_RAW_TERMINAL_RANK_M31
        || product.h1_inactive_padding_terminal_schur_rank_m31
            != PROFILE23_GOOD_SCHEDULE_RAW_TERMINAL_RANK_M31
        || product.q_total_degree_bound != PROFILE23_GOOD_SCHEDULE_Q_DEGREE
        || product.root_neutral_z_degree_bound != PROFILE23_GOOD_SCHEDULE_ROOT_Z_DEGREE
        || product.complete_good_z_degree_bound != PROFILE23_GOOD_SCHEDULE_COMPLETE_Z_DEGREE
        || product.gamma_coordinate_total_degree_bound != PROFILE23_GOOD_SCHEDULE_GAMMA_DEGREE
        || product.continuous_total_degree_bound != PROFILE23_GOOD_SCHEDULE_CONTINUOUS_DEGREE
        || !product.complete
    {
        return Err(Profile23GoodScheduleGateError::DefinitionDrift(
            "profile23 complete product degree or rank",
        ));
    }
    Ok(Profile23GoodScheduleDecision {
        accepted: true,
        rejection: None,
        root_neutral_rank_m31: root.joint_rank_m31,
        remaining_gd_query_rank_m31: raw.remaining_gd_query_rank_m31,
        remaining_gd_terminal_rank_m31: raw.remaining_gd_terminal_schur_rank_m31,
        h1_query_rank_m31: raw.h1_inactive_padding_query_rank_m31,
        h1_terminal_rank_m31: raw.h1_inactive_padding_terminal_schur_rank_m31,
        dynamic_root_minor_fingerprint: root.minor.fingerprint,
        dynamic_remaining_gd_minor_fingerprint: raw.remaining_gd_terminal_schur_minor.fingerprint,
        dynamic_h1_minor_fingerprint: raw.h1_inactive_padding_terminal_schur_minor.fingerprint,
        dynamic_product_fingerprint: product.product_fingerprint,
    })
}

fn validate_candidate_schedules(
    schedules: &[StateOnlyTranscriptScheduleResult; PROFILE23_GOOD_SCHEDULE_QUERY_CANDIDATES],
) -> Result<(), Profile23GoodScheduleGateError> {
    let common = &schedules[0];
    for schedule in schedules {
        if schedule.prefix != common.prefix
            || schedule.circle_ood_points != common.circle_ood_points
            || schedule.line_ood_points != common.line_ood_points
            || schedule.mu != common.mu
            || schedule.alpha != common.alpha
            || schedule.state_before_grinding != common.state_before_grinding
        {
            return Err(Profile23GoodScheduleGateError::DefinitionDrift(
                "profile23 candidate pre-query schedule mismatch",
            ));
        }
        validate_schedule_queries(schedule)?;
    }
    Ok(())
}

fn derive_profile23_query_candidate_schedules(
    hash: HashFn,
    prefix: &StateOnlyProfile23Prefix<'_>,
    statement_digest: &[u8; 32],
    check_pow: bool,
) -> Result<
    [StateOnlyTranscriptScheduleResult; PROFILE23_GOOD_SCHEDULE_QUERY_CANDIDATES],
    Profile23GoodScheduleGateError,
> {
    strict_static_definition()?;
    let replay = |selector: u8| {
        let candidate = StateOnlyProfile23Prefix {
            base: prefix.base,
            d_claims_bytes: prefix.d_claims_bytes,
            query_selector: selector,
        };
        if check_pow {
            run_atomic_state_only_profile23_transcript_schedule_host_v3(
                hash,
                &candidate,
                statement_digest,
            )
        } else {
            run_atomic_state_only_profile23_transcript_schedule_host_unmined_for_diagnostics_v3(
                hash,
                &candidate,
                statement_digest,
            )
        }
        .map_err(Profile23GoodScheduleGateError::Transcript)
    };
    // These are three independent replays from the same prefix. Each replay
    // absorbs exactly one label-44 selector; selectors are never chained.
    let schedules = [replay(0)?, replay(1)?, replay(2)?];
    validate_candidate_schedules(&schedules)?;
    Ok(schedules)
}

pub fn derive_profile23_query_candidate_schedules_host(
    hash: HashFn,
    prefix: &StateOnlyProfile23Prefix<'_>,
    statement_digest: &[u8; 32],
) -> Result<
    [StateOnlyTranscriptScheduleResult; PROFILE23_GOOD_SCHEDULE_QUERY_CANDIDATES],
    Profile23GoodScheduleGateError,
> {
    derive_profile23_query_candidate_schedules(hash, prefix, statement_digest, true)
}

pub fn derive_profile23_query_candidate_schedules_host_unmined_for_diagnostics(
    hash: HashFn,
    prefix: &StateOnlyProfile23Prefix<'_>,
    statement_digest: &[u8; 32],
) -> Result<
    [StateOnlyTranscriptScheduleResult; PROFILE23_GOOD_SCHEDULE_QUERY_CANDIDATES],
    Profile23GoodScheduleGateError,
> {
    derive_profile23_query_candidate_schedules(hash, prefix, statement_digest, false)
}

fn evaluate_all_and_choose_least<Evaluate>(
    schedules: &[StateOnlyTranscriptScheduleResult; PROFILE23_GOOD_SCHEDULE_QUERY_CANDIDATES],
    mut evaluate: Evaluate,
) -> Result<Profile23QueryCandidateEvaluation, Profile23GoodScheduleGateError>
where
    Evaluate: FnMut(
        &StateOnlyTranscriptScheduleResult,
    ) -> Result<Profile23GoodScheduleDecision, Profile23GoodScheduleGateError>,
{
    validate_candidate_schedules(schedules)?;
    // Deliberately evaluate every branch before inspecting acceptance. This
    // is part of the fixed-view q3 manager contract.
    let decisions = [
        evaluate(&schedules[0])?,
        evaluate(&schedules[1])?,
        evaluate(&schedules[2])?,
    ];
    let selected_selector = decisions
        .iter()
        .position(|decision| decision.accepted)
        .map(|selector| selector as u8);
    Ok(Profile23QueryCandidateEvaluation {
        decisions,
        selected_selector,
    })
}

/// Evaluate a caller-derived q3 schedule set.  This is the integration seam
/// for a two-phase builder which already retained one common attempt and
/// cloned its post-final transcript into selector branches 0/1/2.
pub fn evaluate_profile23_candidate_schedules_host(
    schedules: &[StateOnlyTranscriptScheduleResult; PROFILE23_GOOD_SCHEDULE_QUERY_CANDIDATES],
) -> Result<Profile23QueryCandidateEvaluation, Profile23GoodScheduleGateError> {
    evaluate_all_and_choose_least(schedules, evaluate_profile23_strong_good_schedule)
}

/// Fixed-cap first-good state machine for the production Profile23 worker.
/// Every controlled internal failure collapses to one opaque error. `discard`
/// must scrub all candidate-owned private buffers before return.
pub(crate) fn run_profile23_first_good<S, C, Generate, Build, Decide, Discard>(
    mut generate: Generate,
    mut build: Build,
    mut decide: Decide,
    mut discard: Discard,
) -> Result<C, Profile23AttemptsExhausted>
where
    Generate: FnMut() -> Result<S, ()>,
    Build: FnMut(S) -> Result<Profile23AttemptBuild<C>, ()>,
    Decide: FnMut(&C) -> Result<bool, ()>,
    Discard: FnMut(&mut C),
{
    for _ in 0..PROFILE23_GOOD_SCHEDULE_MAX_ATTEMPTS {
        let secret = generate().map_err(|_| Profile23AttemptsExhausted)?;
        let mut candidate = match build(secret).map_err(|_| Profile23AttemptsExhausted)? {
            Profile23AttemptBuild::Candidate(candidate) => candidate,
            Profile23AttemptBuild::Retry => continue,
        };
        match decide(&candidate) {
            Ok(true) => return Ok(candidate),
            Ok(false) => discard(&mut candidate),
            Err(()) => {
                discard(&mut candidate);
                return Err(Profile23AttemptsExhausted);
            }
        }
    }
    Err(Profile23AttemptsExhausted)
}

pub fn evaluate_profile23_query_candidates_host(
    hash: HashFn,
    prefix: &StateOnlyProfile23Prefix<'_>,
    statement_digest: &[u8; 32],
) -> Result<Profile23QueryCandidateEvaluation, Profile23GoodScheduleGateError> {
    let schedules =
        derive_profile23_query_candidate_schedules_host(hash, prefix, statement_digest)?;
    evaluate_profile23_candidate_schedules_host(&schedules)
}

pub fn evaluate_profile23_query_candidates_host_unmined_for_diagnostics(
    hash: HashFn,
    prefix: &StateOnlyProfile23Prefix<'_>,
    statement_digest: &[u8; 32],
) -> Result<Profile23QueryCandidateEvaluation, Profile23GoodScheduleGateError> {
    let schedules = derive_profile23_query_candidate_schedules_host_unmined_for_diagnostics(
        hash,
        prefix,
        statement_digest,
    )?;
    evaluate_profile23_candidate_schedules_host(&schedules)
}

#[cfg(test)]
mod tests {
    use super::*;

    const PROFILE23_FIXTURE: &[u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../results/stage2/proofs/atomic_state_only_profile23_v3_unmined.bin"
    ));
    const STATEMENT_DIGEST: [u8; 32] = [
        0x52, 0xe9, 0x6f, 0x99, 0x75, 0x6f, 0xe8, 0xfd, 0x2d, 0x8b, 0x7a, 0x70, 0x00, 0x19, 0xb1,
        0x43, 0xd7, 0xeb, 0x54, 0x9a, 0xf1, 0xbf, 0x1a, 0xe9, 0x87, 0xe9, 0x9a, 0x75, 0xca, 0xdc,
        0xd4, 0xc9,
    ];

    fn decision(accepted: bool) -> Profile23GoodScheduleDecision {
        Profile23GoodScheduleDecision {
            accepted,
            rejection: (!accepted).then_some(Profile23GoodScheduleRejection::RootNeutralIncomplete),
            root_neutral_rank_m31: usize::from(accepted) * 1_404,
            remaining_gd_query_rank_m31: 0,
            remaining_gd_terminal_rank_m31: 0,
            h1_query_rank_m31: 0,
            h1_terminal_rank_m31: 0,
            dynamic_root_minor_fingerprint: 0,
            dynamic_remaining_gd_minor_fingerprint: 0,
            dynamic_h1_minor_fingerprint: 0,
            dynamic_product_fingerprint: 0,
        }
    }

    fn schedules() -> [StateOnlyTranscriptScheduleResult; 3] {
        let (prefix, _) = StateOnlyProfile23Prefix::parse_from_proof(PROFILE23_FIXTURE).unwrap();
        derive_profile23_query_candidate_schedules_host_unmined_for_diagnostics(
            crate::HOST_HASH,
            &prefix,
            &STATEMENT_DIGEST,
        )
        .unwrap()
    }

    #[test]
    fn definition_fingerprint_and_caps_are_frozen() {
        assert_eq!(PROFILE23_GOOD_SCHEDULE_MAX_ATTEMPTS, 16);
        assert_eq!(PROFILE23_GOOD_SCHEDULE_QUERY_CANDIDATES, 3);
        assert_eq!(PROFILE23_GOOD_SCHEDULE_QUERY_COUNT, 16);
        assert_eq!(PROFILE23_GOOD_SCHEDULE_INVERSE_RATE, 512);
        assert_eq!(PROFILE23_GOOD_SCHEDULE_DOMAIN_LOG, 19);
        assert_eq!(PROFILE23_GOOD_SCHEDULE_QUERY_FIBERS, 131_072);
        assert_eq!(PROFILE23_GOOD_SCHEDULE_CONTINUOUS_DEGREE, 133_716);
        assert_eq!(
            profile23_good_schedule_definition_fingerprint(crate::HOST_HASH),
            [
                0x9c, 0xdd, 0x6a, 0x6c, 0x14, 0xb7, 0x96, 0x76, 0x0c, 0x8d, 0xd7, 0x33, 0x29, 0xef,
                0xfb, 0xfc, 0x73, 0x4a, 0x04, 0x8c, 0xce, 0xcc, 0x4c, 0xe1, 0x0f, 0x21, 0x4b, 0xda,
                0xe3, 0xa6, 0xaf, 0x2a,
            ]
        );
        strict_static_definition().unwrap();
    }

    #[test]
    fn real_replay_derives_three_independent_post_final_query_schedules() {
        let schedules = schedules();
        validate_candidate_schedules(&schedules).unwrap();
        for schedule in &schedules {
            assert_eq!(schedule.query_count, 16);
        }
        assert_ne!(schedules[0].queries[..16], schedules[1].queries[..16]);
        assert_ne!(schedules[0].queries[..16], schedules[2].queries[..16]);
        assert_ne!(schedules[1].queries[..16], schedules[2].queries[..16]);
        assert_ne!(
            schedules[0].state_after_queries,
            schedules[1].state_after_queries
        );
        assert_ne!(
            schedules[0].state_after_queries,
            schedules[2].state_after_queries
        );
    }

    #[test]
    fn invalid_selector_and_query_shapes_are_rejected_before_rank_work() {
        let mut prefix_bytes = PROFILE23_FIXTURE
            [..aspis_core::state_only_prefix::STATE_ONLY_PROFILE23_PREFIX_LEN]
            .to_vec();
        let selector_offset = aspis_core::state_only_prefix::STATE_ONLY_PREFIX_LEN
            + aspis_core::state_only_prefix::STATE_ONLY_PROFILE23_D_CLAIMS_LEN;
        prefix_bytes[selector_offset] = PROFILE23_GOOD_SCHEDULE_QUERY_CANDIDATES as u8;
        assert!(StateOnlyProfile23Prefix::parse_exact(&prefix_bytes).is_err());

        let mut out_of_domain = schedules()[0];
        out_of_domain.queries[0] = PROFILE23_GOOD_SCHEDULE_QUERY_FIBERS as u32;
        assert!(matches!(
            evaluate_profile23_strong_good_schedule(&out_of_domain),
            Err(Profile23GoodScheduleGateError::DefinitionDrift(
                "profile23 candidate query outside q-fiber domain"
            ))
        ));

        let mut duplicate = schedules()[0];
        duplicate.queries[1] = duplicate.queries[0];
        assert!(matches!(
            evaluate_profile23_strong_good_schedule(&duplicate),
            Err(Profile23GoodScheduleGateError::DefinitionDrift(
                "profile23 candidate contains duplicate query"
            ))
        ));
    }

    #[test]
    fn manager_evaluates_all_three_and_selects_least_good() {
        let schedules = schedules();
        for (pattern, expected) in [
            ([true, true, true], Some(0)),
            ([false, true, true], Some(1)),
            ([false, false, true], Some(2)),
            ([false, false, false], None),
        ] {
            let mut calls = 0usize;
            let result = evaluate_all_and_choose_least(&schedules, |_| {
                let value = pattern[calls];
                calls += 1;
                Ok(decision(value))
            })
            .unwrap();
            assert_eq!(calls, 3);
            assert_eq!(result.selected_selector, expected);
        }
    }

    #[test]
    fn bounded_attempt_manager_caps_at_sixteen_and_collapses_failures() {
        let mut generated = 0usize;
        let mut discarded = 0usize;
        let exhausted = run_profile23_first_good(
            || {
                generated += 1;
                Ok(generated)
            },
            |candidate| Ok(Profile23AttemptBuild::Candidate(candidate)),
            |_| Ok(false),
            |_| discarded += 1,
        );
        assert_eq!(exhausted, Err(Profile23AttemptsExhausted));
        assert_eq!(generated, PROFILE23_GOOD_SCHEDULE_MAX_ATTEMPTS);
        assert_eq!(discarded, PROFILE23_GOOD_SCHEDULE_MAX_ATTEMPTS);

        let generation: Result<u8, _> = run_profile23_first_good(
            || Err(()),
            |candidate| Ok(Profile23AttemptBuild::Candidate(candidate)),
            |_| Ok(true),
            |_| {},
        );
        assert_eq!(generation, Err(Profile23AttemptsExhausted));
        let build: Result<u8, _> =
            run_profile23_first_good(|| Ok(7u8), |_| Err(()), |_| Ok(true), |_| {});
        assert_eq!(build, Err(Profile23AttemptsExhausted));

        let mut decision_discarded = false;
        let decision = run_profile23_first_good(
            || Ok(7u8),
            |candidate| Ok(Profile23AttemptBuild::Candidate(candidate)),
            |_| Err(()),
            |_| decision_discarded = true,
        );
        assert_eq!(decision, Err(Profile23AttemptsExhausted));
        assert!(decision_discarded);

        let mut retry_generated = 0usize;
        let retries: Result<u8, _> = run_profile23_first_good(
            || {
                retry_generated += 1;
                Ok(7u8)
            },
            |_| Ok(Profile23AttemptBuild::Retry),
            |_| unreachable!(),
            |_| unreachable!(),
        );
        assert_eq!(retries, Err(Profile23AttemptsExhausted));
        assert_eq!(retry_generated, PROFILE23_GOOD_SCHEDULE_MAX_ATTEMPTS);
    }

    #[test]
    #[ignore = "slow exact q3 complete-product replay"]
    fn frozen_profile23_fixture_runs_exact_good23_on_all_selectors() {
        let (prefix, _) = StateOnlyProfile23Prefix::parse_from_proof(PROFILE23_FIXTURE).unwrap();
        let evaluated = evaluate_profile23_query_candidates_host_unmined_for_diagnostics(
            crate::HOST_HASH,
            &prefix,
            &STATEMENT_DIGEST,
        )
        .unwrap();
        println!("{evaluated:#?}");
        assert_eq!(evaluated.selected_selector, Some(0));
        assert!(evaluated.decisions.iter().all(|decision| decision.accepted));
        assert_eq!(
            evaluated
                .decisions
                .map(|decision| decision.dynamic_product_fingerprint),
            [
                0xc73e_789d_aa54_c8dd,
                0xd5e2_1e46_1ef4_e5d2,
                0x9d1b_cf6c_7437_71ff,
            ]
        );
    }
}
