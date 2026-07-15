//! Host-only Spend complete-Good predicate and q3 selector.
//!
//! This module does not build proofs, mutate a prefix, publish a selector or
//! authorize release.  It replays three independent copies of the same
//! pre-query transcript, absorbs exactly one selector byte (`0`, `1`, or
//! `2`) into each copy, evaluates every resulting schedule, and reports the
//! least good selector. The production builder in `state_only_spend`
//! retains one common attempt, calls this gate, serializes only the selected
//! branch, and scrubs or retries behind an opaque cap-17 boundary.

use aspis_core::state_only_hiding::{
    PINNED_ATOMIC_STATE_ONLY_SPEND_LAYOUT_FACTOR_FINGERPRINT_V3, STATE_ONLY_SPEND_C2_COLUMNS,
    STATE_ONLY_SPEND_D_FACTOR_IDENTIFIER, STATE_ONLY_SPEND_D_GENERATOR_INDEX,
    STATE_ONLY_SPEND_G_GENERATOR_INDEX, STATE_ONLY_SPEND_H_GENERATOR_INDEX,
    STATE_ONLY_SPEND_QUERY_CANDIDATES, STATE_ONLY_SPEND_TOTAL_GENERATOR_WIDTH,
};
use aspis_core::state_only_prefix::{
    run_atomic_state_only_spend_transcript_schedule_host_unmined_for_diagnostics_v3,
    run_atomic_state_only_spend_transcript_schedule_host_v3, StateOnlySpendPrefix,
    StateOnlyTranscriptError, StateOnlyTranscriptScheduleResult, STATE_ONLY_LOG_ROWS,
    STATE_ONLY_SPEND_BATCH_GRINDING_BITS, STATE_ONLY_SPEND_FOLD_GRINDING_BITS,
    STATE_ONLY_SPEND_GRINDING_BITS, STATE_ONLY_SPEND_QUERY_CANDIDATE_COUNT,
    STATE_ONLY_SPEND_QUERY_COUNT, STATE_ONLY_SPEND_ZERO_FACTOR_SHAPE,
};
use aspis_core::HashFn;

use crate::state_only_hiding_rank::{
    bind_spend_complete_good_product_provenance,
    probe_atomic_state_only_profile22_zero_factor_qm31_tail_root_neutral,
    probe_profile22_root_neutral_polynomial_kernel_rank, StateOnlyHidingRankGateError,
};

pub const SPEND_GOOD_SCHEDULE_MAX_ATTEMPTS: usize = 17;
pub const SPEND_GOOD_SCHEDULE_QUERY_CANDIDATES: usize = 3;
pub const SPEND_GOOD_SCHEDULE_QUERY_COUNT: usize = STATE_ONLY_SPEND_QUERY_COUNT as usize;
pub const SPEND_GOOD_SCHEDULE_INVERSE_RATE: usize = 512;
pub const SPEND_GOOD_SCHEDULE_DOMAIN_LOG: u32 = 19;
pub const SPEND_GOOD_SCHEDULE_QUERY_FIBERS: usize = 131_072;
pub const SPEND_GOOD_SCHEDULE_ROOT_NEUTRAL_RANK_M31: usize = 1_404;
pub const SPEND_GOOD_SCHEDULE_RAW_QUERY_RANK_M31: usize = 288;
pub const SPEND_GOOD_SCHEDULE_RAW_TERMINAL_RANK_M31: usize = 12;
pub const SPEND_GOOD_SCHEDULE_Q_DEGREE: usize = 31_320;
pub const SPEND_GOOD_SCHEDULE_ROOT_Z_DEGREE: usize = 41_040;
pub const SPEND_GOOD_SCHEDULE_COMPLETE_Z_DEGREE: usize = 41_280;
pub const SPEND_GOOD_SCHEDULE_GAMMA_DEGREE: usize = 80_688;
pub const SPEND_GOOD_SCHEDULE_CONTINUOUS_DEGREE: usize = 121_968;
/// Number of exhaustive Boolean/selector cases in the arbitrary-selector
/// containment proof: 2^4 assignments for B,M0,M1,M2 times three selectors.
pub const SPEND_SELECTOR_SCOPE_PROPOSITIONAL_CASES: usize = 48;
// The fingerprint domain separators and descriptors below keep the
// release's original working-name spelling: they are hashed into the frozen
// predicate-definition fingerprints that the release certificates,
// evaluator, and known-answer tests pin. Rewriting them would silently
// change those anchors.
const SPEND_SELECTOR_SCOPE_FINGERPRINT_DOMAIN: &[u8] = b"aspis:profile23:selector-scope-proof:v1";
const SPEND_SELECTOR_SCOPE_DESCRIPTOR: &[u8] = b"profile=23;q=18;batch=37;folds=34,33,30,25;final=32;selectors=3;selector_label=44;order=final_poly,final_nonce,label44,query_sample;scope=15_common_preselector+1_final_query_miss;lemma=B_or_M_selected_subset_B_or_M0_or_M1_or_M2;cases=48";

pub fn spend_selector_scope_definition_fingerprint(hash: HashFn) -> [u8; 32] {
    assert_eq!(STATE_ONLY_SPEND_QUERY_COUNT, 18);
    assert_eq!(STATE_ONLY_SPEND_BATCH_GRINDING_BITS, 37);
    assert_eq!(STATE_ONLY_SPEND_FOLD_GRINDING_BITS, [34, 33, 30, 25]);
    assert_eq!(STATE_ONLY_SPEND_GRINDING_BITS, 32);
    hash(&[
        SPEND_SELECTOR_SCOPE_FINGERPRINT_DOMAIN,
        SPEND_SELECTOR_SCOPE_DESCRIPTOR,
    ])
}

/// Machine-check the finite core of the Spend selector-scope lemma.
///
/// `common_bad || misses[selected]` is pointwise contained in
/// `common_bad || misses[0] || misses[1] || misses[2]`, even when `selected`
/// is adversarially correlated with all three schedules.  Consequently the
/// factor three applies only to the selector-dependent final query miss once
/// the common-prefix schedule contract has been checked separately.
pub fn verify_spend_selector_scope_lemma() -> usize {
    let mut cases = 0usize;
    for common_bad in [false, true] {
        for miss0 in [false, true] {
            for miss1 in [false, true] {
                for miss2 in [false, true] {
                    let misses = [miss0, miss1, miss2];
                    for selected in 0..SPEND_GOOD_SCHEDULE_QUERY_CANDIDATES {
                        let selected_bad = common_bad || misses[selected];
                        let union_bad = common_bad || misses.into_iter().any(|miss| miss);
                        assert!(
                            !selected_bad || union_bad,
                            "Spend selector-scope containment counterexample"
                        );
                        cases += 1;
                    }
                }
            }
        }
    }
    assert_eq!(cases, SPEND_SELECTOR_SCOPE_PROPOSITIONAL_CASES);
    cases
}

/// Frozen witnesses used to prove the bad-schedule probability bound.  The
/// runtime echelon replay may select different full-rank minors, so these are
/// provenance anchors and are deliberately not runtime equality predicates.
pub const SPEND_GOOD_SCHEDULE_ROOT_ANCHOR_FINGERPRINT: u64 = 0x6b38_3866_2fbf_34db;
pub const SPEND_GOOD_SCHEDULE_GD_ANCHOR_FINGERPRINT: u64 = 0x1f34_525d_b611_d292;
pub const SPEND_GOOD_SCHEDULE_H1_ANCHOR_FINGERPRINT: u64 = 0xe702_15f0_b479_5f52;
pub const SPEND_GOOD_SCHEDULE_PRODUCT_ANCHOR_FINGERPRINT: u64 = 0xfc07_06f3_a304_ae26;

const SPEND_GOOD_SCHEDULE_FINGERPRINT_DOMAIN: &[u8] = b"aspis:profile23:good-schedule-gate:v1";
const SPEND_GOOD_SCHEDULE_DESCRIPTOR: &[u8] = b"profile=23;version=v4_s2;atomic_layout=v3;rows=1024;rate=1/512;domain_log=19;q=18;query_fibers=131072;query_candidates=3;attempt_cap=17;generator_order=semantic0..15,mask16..25,H26,G27,D28;basis_selection=minimum_q_degree_semantic_then_D_then_mask;layout_fp=0x233ba2ca68f94148;predicate=root_neutral1404+remaining_gd_schur12+h1_inactive_schur12;q_degree=31320;z_degree=41280;gamma_degree=80688;continuous_degree=121968;selector=three_independent_post_final_label44_clones_choose_least;runtime_minor_fingerprint=dynamic;anchor_product=0xfc0706f3a304ae26";

pub fn spend_good_schedule_definition_fingerprint(hash: HashFn) -> [u8; 32] {
    hash(&[
        SPEND_GOOD_SCHEDULE_FINGERPRINT_DOMAIN,
        SPEND_GOOD_SCHEDULE_DESCRIPTOR,
    ])
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpendGoodScheduleRejection {
    RootNeutralIncomplete,
    RemainingGdOrH1RawIncomplete,
    ConservativeRawRankDeficiency(StateOnlyHidingRankGateError),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpendGoodScheduleGateError {
    CanonicalBuilder(StateOnlyHidingRankGateError),
    Transcript(StateOnlyTranscriptError),
    DefinitionDrift(&'static str),
}

/// The only public failure of the bounded production attempt manager. It
/// intentionally carries no retry count, selector, rank reason, entropy
/// error, build error, timing class, or partial candidate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SpendAttemptsExhausted;

/// Private control result of one durably reserved attempt. `Retry` is used
/// only when the exact GoodSpend predicate successfully evaluated all three
/// schedules and found none good. Builder/gate/schema failures are `Err(())`
/// and stop the worker immediately (with the same opaque public outcome).
pub(crate) enum SpendAttemptBuild<C> {
    Candidate(C),
    Retry,
}

impl From<StateOnlyTranscriptError> for SpendGoodScheduleGateError {
    fn from(error: StateOnlyTranscriptError) -> Self {
        Self::Transcript(error)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SpendGoodScheduleDecision {
    pub accepted: bool,
    pub rejection: Option<SpendGoodScheduleRejection>,
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

impl SpendGoodScheduleDecision {
    fn rejected(rejection: SpendGoodScheduleRejection, root_neutral_rank_m31: usize) -> Self {
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
pub struct SpendQueryCandidateEvaluation {
    pub decisions: [SpendGoodScheduleDecision; SPEND_GOOD_SCHEDULE_QUERY_CANDIDATES],
    pub selected_selector: Option<u8>,
}

fn strict_static_definition() -> Result<(), SpendGoodScheduleGateError> {
    let shape = STATE_ONLY_SPEND_ZERO_FACTOR_SHAPE;
    if SPEND_GOOD_SCHEDULE_MAX_ATTEMPTS != 17
        || SPEND_GOOD_SCHEDULE_QUERY_CANDIDATES != STATE_ONLY_SPEND_QUERY_CANDIDATES
        || SPEND_GOOD_SCHEDULE_QUERY_CANDIDATES
            != usize::from(STATE_ONLY_SPEND_QUERY_CANDIDATE_COUNT)
        || SPEND_GOOD_SCHEDULE_QUERY_COUNT != usize::from(shape.query_count)
        || STATE_ONLY_SPEND_BATCH_GRINDING_BITS != 37
        || STATE_ONLY_SPEND_FOLD_GRINDING_BITS != [34, 33, 30, 25]
        || STATE_ONLY_SPEND_GRINDING_BITS != 32
        || SPEND_GOOD_SCHEDULE_INVERSE_RATE != 1usize << shape.log_blowup
        || SPEND_GOOD_SCHEDULE_DOMAIN_LOG != STATE_ONLY_LOG_ROWS + shape.log_blowup
        || SPEND_GOOD_SCHEDULE_QUERY_FIBERS != 1usize << (SPEND_GOOD_SCHEDULE_DOMAIN_LOG - 2)
        || STATE_ONLY_SPEND_TOTAL_GENERATOR_WIDTH != 29
        || STATE_ONLY_SPEND_H_GENERATOR_INDEX != 26
        || STATE_ONLY_SPEND_G_GENERATOR_INDEX != 27
        || STATE_ONLY_SPEND_D_GENERATOR_INDEX != 28
        || STATE_ONLY_SPEND_D_FACTOR_IDENTIFIER != 0
        || STATE_ONLY_SPEND_C2_COLUMNS != 3
        || PINNED_ATOMIC_STATE_ONLY_SPEND_LAYOUT_FACTOR_FINGERPRINT_V3 != 0x233b_a2ca_68f9_4148
    {
        return Err(SpendGoodScheduleGateError::DefinitionDrift(
            "spend static shape, layout or cap",
        ));
    }
    Ok(())
}

fn validate_schedule_queries(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<(), SpendGoodScheduleGateError> {
    if schedule.query_count != SPEND_GOOD_SCHEDULE_QUERY_COUNT {
        return Err(SpendGoodScheduleGateError::DefinitionDrift(
            "spend candidate q18 count",
        ));
    }
    if schedule.queries[..schedule.query_count]
        .iter()
        .any(|&query| query >= SPEND_GOOD_SCHEDULE_QUERY_FIBERS as u32)
    {
        return Err(SpendGoodScheduleGateError::DefinitionDrift(
            "spend candidate query outside q-fiber domain",
        ));
    }
    for left in 0..schedule.query_count {
        for right in 0..left {
            if schedule.queries[left] == schedule.queries[right] {
                return Err(SpendGoodScheduleGateError::DefinitionDrift(
                    "spend candidate contains duplicate query",
                ));
            }
        }
    }
    Ok(())
}

/// Evaluate all three blocks of the exact prospective Spend Good
/// predicate on one already-derived public schedule.
pub fn evaluate_spend_strong_good_schedule(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<SpendGoodScheduleDecision, SpendGoodScheduleGateError> {
    strict_static_definition()?;
    validate_schedule_queries(schedule)?;

    let root = match probe_profile22_root_neutral_polynomial_kernel_rank(schedule) {
        Ok(report) => report,
        Err(error @ StateOnlyHidingRankGateError::Relation) => {
            return Ok(SpendGoodScheduleDecision::rejected(
                SpendGoodScheduleRejection::ConservativeRawRankDeficiency(error),
                0,
            ));
        }
        Err(error) => return Err(SpendGoodScheduleGateError::CanonicalBuilder(error)),
    };
    if root.generator_order != "semantic0..15,mask-only16..25,H26,G27,D28"
        || root.query_count != SPEND_GOOD_SCHEDULE_QUERY_COUNT
        || root.joint_target_rank_m31 != SPEND_GOOD_SCHEDULE_ROOT_NEUTRAL_RANK_M31
        || root.root_neutral_target_rank_m31 != 1_076
        || root.semantic_lanes != 16
        || root.mask_only_lanes != 10
        || root.d_tower_coordinates != 4
        || root.z_total_degree_bound != SPEND_GOOD_SCHEDULE_ROOT_Z_DEGREE
    {
        return Err(SpendGoodScheduleGateError::DefinitionDrift(
            "spend root-neutral report schema",
        ));
    }
    if !root.complete {
        return Ok(SpendGoodScheduleDecision::rejected(
            SpendGoodScheduleRejection::RootNeutralIncomplete,
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
            return Ok(SpendGoodScheduleDecision::rejected(
                SpendGoodScheduleRejection::ConservativeRawRankDeficiency(error),
                root.joint_rank_m31,
            ));
        }
        Err(error) => return Err(SpendGoodScheduleGateError::CanonicalBuilder(error)),
    };
    if raw.production_h_generator_index != 26
        || raw.production_g_generator_index != 27
        || raw.tail_generator_index != 28
        || raw.generator_width_before != 28
        || raw.generator_width_after != 29
        || raw.qm31_raw_target_m31 != 300
        || raw.conditional_target_m31 != 1_076
        || raw.remaining_gd_terminal_schur_z_degree != 120
        || raw.h1_inactive_padding_terminal_schur_z_degree != 120
    {
        return Err(SpendGoodScheduleGateError::DefinitionDrift(
            "spend raw Schur report schema",
        ));
    }
    if !raw.complete
        || raw.remaining_gd_query_rank_m31 != SPEND_GOOD_SCHEDULE_RAW_QUERY_RANK_M31
        || raw.remaining_gd_terminal_schur_rank_m31 != SPEND_GOOD_SCHEDULE_RAW_TERMINAL_RANK_M31
        || raw.h1_inactive_padding_query_rank_m31 != SPEND_GOOD_SCHEDULE_RAW_QUERY_RANK_M31
        || raw.h1_inactive_padding_terminal_schur_rank_m31
            != SPEND_GOOD_SCHEDULE_RAW_TERMINAL_RANK_M31
    {
        return Ok(SpendGoodScheduleDecision {
            accepted: false,
            rejection: Some(SpendGoodScheduleRejection::RemainingGdOrH1RawIncomplete),
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

    let product = bind_spend_complete_good_product_provenance(&root, &raw)
        .map_err(SpendGoodScheduleGateError::CanonicalBuilder)?;
    if product.root_neutral_minor_rank_m31 != SPEND_GOOD_SCHEDULE_ROOT_NEUTRAL_RANK_M31
        || product.remaining_gd_terminal_schur_rank_m31 != SPEND_GOOD_SCHEDULE_RAW_TERMINAL_RANK_M31
        || product.h1_inactive_padding_terminal_schur_rank_m31
            != SPEND_GOOD_SCHEDULE_RAW_TERMINAL_RANK_M31
        || product.q_total_degree_bound != SPEND_GOOD_SCHEDULE_Q_DEGREE
        || product.root_neutral_z_degree_bound != SPEND_GOOD_SCHEDULE_ROOT_Z_DEGREE
        || product.complete_good_z_degree_bound != SPEND_GOOD_SCHEDULE_COMPLETE_Z_DEGREE
        || product.gamma_coordinate_total_degree_bound != SPEND_GOOD_SCHEDULE_GAMMA_DEGREE
        || product.continuous_total_degree_bound != SPEND_GOOD_SCHEDULE_CONTINUOUS_DEGREE
        || !product.complete
    {
        return Err(SpendGoodScheduleGateError::DefinitionDrift(
            "spend complete product degree or rank",
        ));
    }
    Ok(SpendGoodScheduleDecision {
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
    schedules: &[StateOnlyTranscriptScheduleResult; SPEND_GOOD_SCHEDULE_QUERY_CANDIDATES],
) -> Result<(), SpendGoodScheduleGateError> {
    let common = &schedules[0];
    for schedule in schedules {
        if schedule.prefix != common.prefix
            || schedule.circle_ood_points != common.circle_ood_points
            || schedule.line_ood_points != common.line_ood_points
            || schedule.mu != common.mu
            || schedule.alpha != common.alpha
            || schedule.state_before_grinding != common.state_before_grinding
        {
            return Err(SpendGoodScheduleGateError::DefinitionDrift(
                "spend candidate pre-query schedule mismatch",
            ));
        }
        validate_schedule_queries(schedule)?;
    }
    Ok(())
}

fn derive_spend_query_candidate_schedules(
    hash: HashFn,
    prefix: &StateOnlySpendPrefix<'_>,
    statement_digest: &[u8; 32],
    check_pow: bool,
) -> Result<
    [StateOnlyTranscriptScheduleResult; SPEND_GOOD_SCHEDULE_QUERY_CANDIDATES],
    SpendGoodScheduleGateError,
> {
    strict_static_definition()?;
    let replay = |selector: u8| {
        let candidate = StateOnlySpendPrefix {
            base: prefix.base,
            d_claims_bytes: prefix.d_claims_bytes,
            query_selector: selector,
        };
        if check_pow {
            run_atomic_state_only_spend_transcript_schedule_host_v3(
                hash,
                &candidate,
                statement_digest,
            )
        } else {
            run_atomic_state_only_spend_transcript_schedule_host_unmined_for_diagnostics_v3(
                hash,
                &candidate,
                statement_digest,
            )
        }
        .map_err(SpendGoodScheduleGateError::Transcript)
    };
    // These are three independent replays from the same prefix. Each replay
    // absorbs exactly one label-44 selector; selectors are never chained.
    let schedules = [replay(0)?, replay(1)?, replay(2)?];
    validate_candidate_schedules(&schedules)?;
    Ok(schedules)
}

pub fn derive_spend_query_candidate_schedules_host(
    hash: HashFn,
    prefix: &StateOnlySpendPrefix<'_>,
    statement_digest: &[u8; 32],
) -> Result<
    [StateOnlyTranscriptScheduleResult; SPEND_GOOD_SCHEDULE_QUERY_CANDIDATES],
    SpendGoodScheduleGateError,
> {
    derive_spend_query_candidate_schedules(hash, prefix, statement_digest, true)
}

pub fn derive_spend_query_candidate_schedules_host_unmined_for_diagnostics(
    hash: HashFn,
    prefix: &StateOnlySpendPrefix<'_>,
    statement_digest: &[u8; 32],
) -> Result<
    [StateOnlyTranscriptScheduleResult; SPEND_GOOD_SCHEDULE_QUERY_CANDIDATES],
    SpendGoodScheduleGateError,
> {
    derive_spend_query_candidate_schedules(hash, prefix, statement_digest, false)
}

#[cfg(test)]
fn evaluate_all_and_choose_least<Evaluate>(
    schedules: &[StateOnlyTranscriptScheduleResult; SPEND_GOOD_SCHEDULE_QUERY_CANDIDATES],
    mut evaluate: Evaluate,
) -> Result<SpendQueryCandidateEvaluation, SpendGoodScheduleGateError>
where
    Evaluate: FnMut(
        &StateOnlyTranscriptScheduleResult,
    ) -> Result<SpendGoodScheduleDecision, SpendGoodScheduleGateError>,
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
    Ok(SpendQueryCandidateEvaluation {
        decisions,
        selected_selector,
    })
}

fn evaluate_all_and_choose_least_parallel<Evaluate>(
    schedules: &[StateOnlyTranscriptScheduleResult; SPEND_GOOD_SCHEDULE_QUERY_CANDIDATES],
    evaluate: Evaluate,
) -> Result<SpendQueryCandidateEvaluation, SpendGoodScheduleGateError>
where
    Evaluate: Fn(
            &StateOnlyTranscriptScheduleResult,
        ) -> Result<SpendGoodScheduleDecision, SpendGoodScheduleGateError>
        + Sync,
{
    validate_candidate_schedules(schedules)?;

    // The three selector branches share no mutable state after schedule
    // derivation.  Evaluate all of them concurrently, retain their fixed
    // selector indices, then apply the same least-Good rule only after every
    // branch has joined.  Scheduling therefore cannot affect the result.
    let [decision0, decision1, decision2] = std::thread::scope(|scope| {
        let branch0 = scope.spawn(|| evaluate(&schedules[0]));
        let branch1 = scope.spawn(|| evaluate(&schedules[1]));
        let branch2 = scope.spawn(|| evaluate(&schedules[2]));
        let joined0 = branch0.join();
        let joined1 = branch1.join();
        let joined2 = branch2.join();
        Ok::<_, SpendGoodScheduleGateError>([
            joined0.map_err(|_| {
                SpendGoodScheduleGateError::DefinitionDrift(
                    "spend parallel GoodSpend branch panicked",
                )
            })?,
            joined1.map_err(|_| {
                SpendGoodScheduleGateError::DefinitionDrift(
                    "spend parallel GoodSpend branch panicked",
                )
            })?,
            joined2.map_err(|_| {
                SpendGoodScheduleGateError::DefinitionDrift(
                    "spend parallel GoodSpend branch panicked",
                )
            })?,
        ])
    })?;
    let decisions = [decision0?, decision1?, decision2?];
    let selected_selector = decisions
        .iter()
        .position(|decision| decision.accepted)
        .map(|selector| selector as u8);
    Ok(SpendQueryCandidateEvaluation {
        decisions,
        selected_selector,
    })
}

/// Evaluate a caller-derived q3 schedule set.  This is the integration seam
/// for a two-phase builder which already retained one common attempt and
/// cloned its post-final transcript into selector branches 0/1/2.
pub fn evaluate_spend_candidate_schedules_host(
    schedules: &[StateOnlyTranscriptScheduleResult; SPEND_GOOD_SCHEDULE_QUERY_CANDIDATES],
) -> Result<SpendQueryCandidateEvaluation, SpendGoodScheduleGateError> {
    evaluate_all_and_choose_least_parallel(schedules, evaluate_spend_strong_good_schedule)
}

/// Fixed-cap first-good state machine for the production Spend worker.
/// Every controlled internal failure collapses to one opaque error. `discard`
/// must scrub all candidate-owned private buffers before return.
pub(crate) fn run_spend_first_good<S, C, Generate, Build, Decide, Discard>(
    mut generate: Generate,
    mut build: Build,
    mut decide: Decide,
    mut discard: Discard,
) -> Result<C, SpendAttemptsExhausted>
where
    Generate: FnMut() -> Result<S, ()>,
    Build: FnMut(S) -> Result<SpendAttemptBuild<C>, ()>,
    Decide: FnMut(&C) -> Result<bool, ()>,
    Discard: FnMut(&mut C),
{
    for _ in 0..SPEND_GOOD_SCHEDULE_MAX_ATTEMPTS {
        let secret = generate().map_err(|_| SpendAttemptsExhausted)?;
        let mut candidate = match build(secret).map_err(|_| SpendAttemptsExhausted)? {
            SpendAttemptBuild::Candidate(candidate) => candidate,
            SpendAttemptBuild::Retry => continue,
        };
        match decide(&candidate) {
            Ok(true) => return Ok(candidate),
            Ok(false) => discard(&mut candidate),
            Err(()) => {
                discard(&mut candidate);
                return Err(SpendAttemptsExhausted);
            }
        }
    }
    Err(SpendAttemptsExhausted)
}

pub fn evaluate_spend_query_candidates_host(
    hash: HashFn,
    prefix: &StateOnlySpendPrefix<'_>,
    statement_digest: &[u8; 32],
) -> Result<SpendQueryCandidateEvaluation, SpendGoodScheduleGateError> {
    let schedules = derive_spend_query_candidate_schedules_host(hash, prefix, statement_digest)?;
    evaluate_spend_candidate_schedules_host(&schedules)
}

pub fn evaluate_spend_query_candidates_host_unmined_for_diagnostics(
    hash: HashFn,
    prefix: &StateOnlySpendPrefix<'_>,
    statement_digest: &[u8; 32],
) -> Result<SpendQueryCandidateEvaluation, SpendGoodScheduleGateError> {
    let schedules = derive_spend_query_candidate_schedules_host_unmined_for_diagnostics(
        hash,
        prefix,
        statement_digest,
    )?;
    evaluate_spend_candidate_schedules_host(&schedules)
}

#[cfg(test)]
mod tests {
    use super::*;

    const SPEND_FIXTURE: &[u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/fixtures/atomic_state_only_spend_v3_unmined.bin"
    ));
    const STATEMENT_DIGEST: [u8; 32] = [
        0x52, 0xe9, 0x6f, 0x99, 0x75, 0x6f, 0xe8, 0xfd, 0x2d, 0x8b, 0x7a, 0x70, 0x00, 0x19, 0xb1,
        0x43, 0xd7, 0xeb, 0x54, 0x9a, 0xf1, 0xbf, 0x1a, 0xe9, 0x87, 0xe9, 0x9a, 0x75, 0xca, 0xdc,
        0xd4, 0xc9,
    ];

    fn decision(accepted: bool) -> SpendGoodScheduleDecision {
        SpendGoodScheduleDecision {
            accepted,
            rejection: (!accepted).then_some(SpendGoodScheduleRejection::RootNeutralIncomplete),
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
        let (prefix, _) = StateOnlySpendPrefix::parse_from_proof(SPEND_FIXTURE).unwrap();
        derive_spend_query_candidate_schedules_host_unmined_for_diagnostics(
            crate::HOST_HASH,
            &prefix,
            &STATEMENT_DIGEST,
        )
        .unwrap()
    }

    #[test]
    fn definition_fingerprint_and_caps_are_frozen() {
        assert_eq!(SPEND_GOOD_SCHEDULE_MAX_ATTEMPTS, 17);
        assert_eq!(SPEND_GOOD_SCHEDULE_QUERY_CANDIDATES, 3);
        assert_eq!(SPEND_GOOD_SCHEDULE_QUERY_COUNT, 18);
        assert_eq!(SPEND_GOOD_SCHEDULE_INVERSE_RATE, 512);
        assert_eq!(SPEND_GOOD_SCHEDULE_DOMAIN_LOG, 19);
        assert_eq!(SPEND_GOOD_SCHEDULE_QUERY_FIBERS, 131_072);
        assert_eq!(SPEND_GOOD_SCHEDULE_CONTINUOUS_DEGREE, 121_968);
        assert_eq!(
            spend_good_schedule_definition_fingerprint(crate::HOST_HASH),
            [
                0x92, 0x79, 0x20, 0xb1, 0x0b, 0xa3, 0x13, 0x73, 0xc1, 0x90, 0x9e, 0xf9, 0xbf, 0xb7,
                0xae, 0x7c, 0xb9, 0x57, 0x0c, 0x7e, 0x25, 0x36, 0xd2, 0x94, 0x34, 0x78, 0x34, 0xb3,
                0xc8, 0x3d, 0xcb, 0x26,
            ]
        );
        assert_eq!(
            verify_spend_selector_scope_lemma(),
            SPEND_SELECTOR_SCOPE_PROPOSITIONAL_CASES
        );
        assert_eq!(
            spend_selector_scope_definition_fingerprint(crate::HOST_HASH),
            [
                0xb9, 0x1e, 0x10, 0x08, 0xf4, 0x92, 0x0c, 0x51, 0x2a, 0x63, 0x9e, 0x29, 0x1b, 0x31,
                0xcc, 0x07, 0x33, 0x8d, 0xf1, 0xbf, 0x16, 0x77, 0x5a, 0x1e, 0xe1, 0x26, 0xcb, 0xda,
                0x7b, 0x34, 0xa1, 0x93,
            ]
        );
        strict_static_definition().unwrap();
    }

    #[test]
    fn real_replay_derives_three_independent_post_final_query_schedules() {
        let schedules = schedules();
        validate_candidate_schedules(&schedules).unwrap();
        for schedule in &schedules {
            assert_eq!(schedule.query_count, 18);
        }
        assert_ne!(schedules[0].queries[..18], schedules[1].queries[..18]);
        assert_ne!(schedules[0].queries[..18], schedules[2].queries[..18]);
        assert_ne!(schedules[1].queries[..18], schedules[2].queries[..18]);
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
        let mut prefix_bytes =
            SPEND_FIXTURE[..aspis_core::state_only_prefix::STATE_ONLY_SPEND_PREFIX_LEN].to_vec();
        let selector_offset = aspis_core::state_only_prefix::STATE_ONLY_PREFIX_LEN
            + aspis_core::state_only_prefix::STATE_ONLY_SPEND_D_CLAIMS_LEN;
        prefix_bytes[selector_offset] = SPEND_GOOD_SCHEDULE_QUERY_CANDIDATES as u8;
        assert!(StateOnlySpendPrefix::parse_exact(&prefix_bytes).is_err());

        let mut out_of_domain = schedules()[0];
        out_of_domain.queries[0] = SPEND_GOOD_SCHEDULE_QUERY_FIBERS as u32;
        assert!(matches!(
            evaluate_spend_strong_good_schedule(&out_of_domain),
            Err(SpendGoodScheduleGateError::DefinitionDrift(
                "spend candidate query outside q-fiber domain"
            ))
        ));

        let mut duplicate = schedules()[0];
        duplicate.queries[1] = duplicate.queries[0];
        assert!(matches!(
            evaluate_spend_strong_good_schedule(&duplicate),
            Err(SpendGoodScheduleGateError::DefinitionDrift(
                "spend candidate contains duplicate query"
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
    fn parallel_manager_joins_all_branches_and_preserves_selector_order() {
        let schedules = schedules();
        let barrier = std::sync::Barrier::new(SPEND_GOOD_SCHEDULE_QUERY_CANDIDATES);
        let calls = std::sync::atomic::AtomicUsize::new(0);
        let result = evaluate_all_and_choose_least_parallel(&schedules, |schedule| {
            barrier.wait();
            calls.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            Ok(decision(
                schedule.queries[..schedule.query_count]
                    == schedules[1].queries[..schedules[1].query_count],
            ))
        })
        .unwrap();
        assert_eq!(
            calls.load(std::sync::atomic::Ordering::Relaxed),
            SPEND_GOOD_SCHEDULE_QUERY_CANDIDATES
        );
        assert_eq!(result.selected_selector, Some(1));
    }

    #[test]
    fn parallel_manager_collapses_a_branch_panic_to_a_gate_error() {
        let schedules = schedules();
        let result = evaluate_all_and_choose_least_parallel(&schedules, |schedule| {
            if schedule.queries[..schedule.query_count]
                == schedules[1].queries[..schedules[1].query_count]
            {
                panic!("synthetic private GoodSpend branch failure");
            }
            Ok(decision(true))
        });
        assert_eq!(
            result,
            Err(SpendGoodScheduleGateError::DefinitionDrift(
                "spend parallel GoodSpend branch panicked"
            ))
        );
    }

    #[test]
    fn bounded_attempt_manager_caps_at_seventeen_and_collapses_failures() {
        let mut generated = 0usize;
        let mut discarded = 0usize;
        let exhausted = run_spend_first_good(
            || {
                generated += 1;
                Ok(generated)
            },
            |candidate| Ok(SpendAttemptBuild::Candidate(candidate)),
            |_| Ok(false),
            |_| discarded += 1,
        );
        assert_eq!(exhausted, Err(SpendAttemptsExhausted));
        assert_eq!(generated, SPEND_GOOD_SCHEDULE_MAX_ATTEMPTS);
        assert_eq!(discarded, SPEND_GOOD_SCHEDULE_MAX_ATTEMPTS);

        let generation: Result<u8, _> = run_spend_first_good(
            || Err(()),
            |candidate| Ok(SpendAttemptBuild::Candidate(candidate)),
            |_| Ok(true),
            |_| {},
        );
        assert_eq!(generation, Err(SpendAttemptsExhausted));
        let build: Result<u8, _> =
            run_spend_first_good(|| Ok(7u8), |_| Err(()), |_| Ok(true), |_| {});
        assert_eq!(build, Err(SpendAttemptsExhausted));

        let mut decision_discarded = false;
        let decision = run_spend_first_good(
            || Ok(7u8),
            |candidate| Ok(SpendAttemptBuild::Candidate(candidate)),
            |_| Err(()),
            |_| decision_discarded = true,
        );
        assert_eq!(decision, Err(SpendAttemptsExhausted));
        assert!(decision_discarded);

        let mut retry_generated = 0usize;
        let retries: Result<u8, _> = run_spend_first_good(
            || {
                retry_generated += 1;
                Ok(7u8)
            },
            |_| Ok(SpendAttemptBuild::Retry),
            |_| unreachable!(),
            |_| unreachable!(),
        );
        assert_eq!(retries, Err(SpendAttemptsExhausted));
        assert_eq!(retry_generated, SPEND_GOOD_SCHEDULE_MAX_ATTEMPTS);
    }

    #[test]
    #[ignore = "slow exact q3 complete-product replay"]
    fn frozen_spend_fixture_runs_exact_good_spend_on_all_selectors() {
        let (prefix, _) = StateOnlySpendPrefix::parse_from_proof(SPEND_FIXTURE).unwrap();
        let evaluated = evaluate_spend_query_candidates_host_unmined_for_diagnostics(
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
                0xfc07_06f3_a304_ae26,
                0x1eb7_a0d4_a2b3_f79f,
                0xa8e5_683c_ed1e_2d1c,
            ]
        );
    }
}
