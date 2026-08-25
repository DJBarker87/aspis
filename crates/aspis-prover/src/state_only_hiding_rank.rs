//! Exact host-side rank gate for the affine state-only hiding view.
//!
//! This module intentionally lives in the prover crate: it uses the actual
//! circle encoder and the complete post-transcript query schedule.  The gate
//! is not part of verifier soundness.  It prevents an honest prover from
//! emitting a proof whose fixed public schedule makes the selected mask map
//! rank-deficient.

use std::collections::BTreeMap;
use std::time::Instant;

use aspis_core::circle_fri::{
    line_domain_x_for_circle, normalized_line_arity4_at_fiber_for_domain_log,
};
use aspis_core::circle_line_merkle::derive_circle_line_query_indices_for_count;
use aspis_core::circle_prefix::{CANDIDATE_OOD_SAMPLES, CANDIDATE_ROUND_COUNT};
use aspis_core::field::{CM31, M31, QM31};
use aspis_core::state_only_hiding::{
    state_only_c1_mask_factor, state_only_explicit_g_mask_factor, state_only_mask_only_c1_factor,
    state_only_mask_tower_basis, STATE_ONLY_HIDING_C1_COLUMNS,
    STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS, STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS,
    STATE_ONLY_HIDING_SUMCHECK_ROUNDS,
};
use aspis_core::state_only_masked_switch_basis::{
    MASKED_SWITCH_UNIVERSAL_CODE_BASIS, MASKED_SWITCH_UNIVERSAL_CODE_BASIS_FINGERPRINT,
    MASKED_SWITCH_UNIVERSAL_DIMENSION,
};
use aspis_core::state_only_prefix::{
    StateOnlyProfile21TranscriptScheduleResult, StateOnlyTranscriptScheduleResult,
    STATE_ONLY_LOG_ROWS, STATE_ONLY_SPEND_QUERY_COUNT,
};
use aspis_core::sumcheck::{
    boundary_sum, evaluate as evaluate_relation, polynomial_for_extension, WeightAccumulator,
};
use aspis_statement::atomic_state_only_registry::atomic_state_only_relation_free_mask_cells_v3;
use aspis_statement::atomic_state_only_terminal::{
    atomic_state_only_copy_active_rows_v3, atomic_state_only_copy_inactive_row_masks_v3,
};
use aspis_statement::{
    binary_successor_point, state_only_copy_active_rows_v4, state_only_copy_inactive_row_masks_v4,
    state_only_relation_free_mask_cells_v4, xor12_point,
};

use crate::circle_candidate::CandidatePrefixBuildError;
use crate::circle_candidate::{
    fold_adjacent_natural_arity4, fold_candidate_codeword_round_for_domain_log,
    CircleCandidateError, CircleEncoder, FIBER_SLOTS,
};
use crate::state_only_circle_relation::StateOnlyIncrementalRelation;

mod spend_polynomial_kernel_rank;
mod spend_zero_factor_root_neutral;
mod state_only_affine_slice_rank;
mod state_only_claim_aggregation_rank;
mod state_only_complete_shared_mask_rank;
mod state_only_extra_mask_rank;
mod state_only_joint_aux_claim_rank;
mod state_only_native_full_x_affine_rank;
mod state_only_reduced_high_switch_rank;
mod state_only_two_variable_slice_rank;
mod state_only_variable_permutation_rank;
pub use spend_polynomial_kernel_rank::{
    probe_spend_common_tail_polynomial_kernel_rank, probe_spend_mixed_polynomial_kernel_rank,
    probe_spend_root_neutral_polynomial_kernel_rank, SpendMixedPolynomialKernelRankReport,
    SpendPolynomialKernelRankReport, SpendRootNeutralPolynomialKernelRankReport,
};
pub use spend_zero_factor_root_neutral::{
    bind_spend_complete_good_product_provenance,
    probe_atomic_state_only_spend_zero_factor_qm31_tail_root_neutral,
    probe_atomic_state_only_spend_zero_factor_root_neutral_prefixes,
    SpendCompleteGoodProductProvenance, SpendZeroFactorQm31TailRootNeutralReport,
    SpendZeroFactorRootNeutralPrefix, SpendZeroFactorRootNeutralReport,
    SPEND_ZERO_FACTOR_MAX_LANES,
};
pub use state_only_affine_slice_rank::{
    probe_atomic_state_only_profile21_affine_extension_slice_lift_rank_variant,
    probe_atomic_state_only_profile21_affine_g_claim_elision_rank_variant,
    probe_atomic_state_only_profile21_affine_g_z_aggregate_claim_rank_variant,
    probe_atomic_state_only_profile21_affine_slice_lift_rank,
    probe_atomic_state_only_profile21_affine_slice_lift_rank_variant,
    AtomicProfile21AffineSliceLiftRankReport, AtomicProfile21AffineSliceVariantReport,
};
pub use state_only_claim_aggregation_rank::{
    probe_atomic_state_only_compact_claim_bound_root0_multiplier_lean_rank,
    probe_atomic_state_only_compact_claim_bound_root0_multiplier_rank,
    probe_atomic_state_only_compact_claim_bound_root0_switch_rank,
    probe_atomic_state_only_compact_claim_rank,
    probe_atomic_state_only_compact_claim_rank_with_constant_pad,
    probe_atomic_state_only_profile21_compact_claim_rank, AtomicProfile21CompactClaimRankReport,
    CompactBoundRoot0SwitchShape, CompactRoot0Multiplier,
};
pub use state_only_complete_shared_mask_rank::{
    complete_shared_mask_missing_lanes, probe_atomic_state_only_complete_shared_mask_basis_rank,
    CompleteSharedMaskBasisRankReport, CompleteSharedMaskLane,
};
pub use state_only_extra_mask_rank::{
    probe_atomic_state_only_extra_mask_rank, probe_atomic_state_only_profile21_extra_mask_rank,
    ExtraMaskFactorFamily, ExtraMaskFactorSpec, ExtraMaskRankReport,
};
pub use state_only_joint_aux_claim_rank::{
    probe_atomic_state_only_joint_aux_claim_rank, AtomicJointAuxClaimRankReport,
};
pub use state_only_two_variable_slice_rank::{
    probe_atomic_state_only_profile21_two_variable_slice_lift_rank,
    AtomicProfile21TwoVariableSliceLiftRankReport,
};
pub use state_only_variable_permutation_rank::{
    AtomicProfile21VariablePermutationP0Probe, AtomicProfile21VariablePermutationP0RankReport,
};

const TRACE_ROWS: usize = 1 << STATE_ONLY_HIDING_SUMCHECK_ROUNDS;
const MASK_SUMCHECK_DEGREE: usize = 27;
const MASK_SUMCHECK_COEFFICIENTS: usize = MASK_SUMCHECK_DEGREE + 1;
const HYBRID_ARITY8_RELATION_COEFFICIENTS: usize = 15;
/// One QM31 terminal relation removes four serialized M31 dimensions.
const MASK_SUMCHECK_QUOTIENT_M31: usize = 4 * (STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS - 1);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateOnlyHidingRankGateError {
    Shape,
    Layout,
    Encoding,
    Relation,
    RawC1Rank {
        column: usize,
        got: usize,
        want: usize,
    },
    RawGRank {
        got: usize,
        want: usize,
    },
    MaskedSumcheckRank {
        got: usize,
        want: usize,
    },
    JointPcsRank {
        got: usize,
        want: usize,
        pre_helper: usize,
        declared_combined: usize,
        declared_inactive_helper: usize,
        declared_active_helper: usize,
    },
    HelperContainment {
        before: usize,
        after: usize,
    },
    WitnessRawQuotient {
        source: usize,
    },
    WitnessSumcheckQuotient {
        class: u8,
        source: usize,
    },
}

impl From<CircleCandidateError> for StateOnlyHidingRankGateError {
    fn from(_: CircleCandidateError) -> Self {
        Self::Encoding
    }
}

impl From<CandidatePrefixBuildError> for StateOnlyHidingRankGateError {
    fn from(_: CandidatePrefixBuildError) -> Self {
        Self::Relation
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateOnlyHidingRankGateReport {
    pub pcs_schedule: &'static str,
    pub tail_qm31_probe: bool,
    pub tail_qm31_mask_factor: &'static str,
    pub first_later_x_multiplier: &'static str,
    pub first_later_x_multiplier_degree: usize,
    pub shared_linear_factor_probe: bool,
    pub coordinate_factored_mask_columns: usize,
    pub late_switch_probe: bool,
    pub complete_ambient_rank: bool,
    pub query_count: usize,
    pub c1_raw_m31: usize,
    pub g_raw_m31: usize,
    pub masked_sumcheck_m31: usize,
    pub masked_sumcheck_rank: usize,
    pub joint_pcs_m31: usize,
    pub joint_pcs_declared_rank: usize,
    pub joint_pcs_rank: usize,
    pub helper_augmented_rank: usize,
    pub pre_helper_pcs_rank: usize,
    pub declared_combined_rank: usize,
    pub declared_inactive_helper_rank: usize,
    pub semantic_mask_basis_m31: usize,
    pub semantic_raw_kernel_m31: usize,
    pub mask_only_basis_m31: usize,
    pub mask_only_raw_kernel_m31: usize,
    pub g_mask_basis_m31: usize,
    pub g_raw_kernel_m31: usize,
    pub tail_qm31_basis_m31: usize,
    pub tail_qm31_raw_kernel_m31: usize,
    pub post_sumcheck_kernel_m31: usize,
    pub h_inactive_mask_basis_m31: usize,
    pub ambient_combined_domain_qm31: usize,
    pub ambient_inactive_helper_domain_qm31: usize,
    pub ambient_active_helper_domain_qm31: usize,
    pub baseline_valid_witness_containment: bool,
    pub baseline_ambient_deficit_m31: usize,
    /// Stronger-than-witness diagnostic: after quotienting the exact raw
    /// openings, every M31 cell direction in all sixteen semantic columns
    /// except the fixed atomic block-0 pre-absorb row is inserted with its
    /// real gamma-scaled PCS image. Nonlinear zerocheck variation is handled
    /// independently by the complete legal sumcheck quotient below.
    pub witness_difference_probe: bool,
    pub witness_semantic_superset_generators_m31: usize,
    pub witness_semantic_superset_rank: usize,
    pub witness_legal_sumcheck_generators_m31: usize,
    pub witness_legal_sumcheck_rank: usize,
    pub witness_compatibility_rank_m31: usize,
    /// Exact block-elimination ranks for an intentionally overstrong
    /// independent-terminal stress target: physical semantic sources with a
    /// zero SC image, independently allowed zero-initial-only sumcheck units,
    /// and active helper differences.  This is not an accepting protocol
    /// view; it is retained as a negative modelling tooth.
    ///
    /// These fields differ from the historical PCS-only augmented ranks
    /// above when the mask sumcheck image is deficient.  A target pivot that
    /// remains outside the mask sumcheck image is a public-view direction and
    /// must be counted; it cannot be discarded merely because no PCS carry
    /// is produced.  `None` means this report did not request the physical
    /// witness-difference source audit.
    pub witness_direct_sum_mask_view_rank_m31: Option<usize>,
    pub witness_direct_sum_physical_augmented_view_rank_m31: Option<usize>,
    pub witness_direct_sum_legal_augmented_view_rank_m31: Option<usize>,
    pub witness_direct_sum_helper_augmented_view_rank_m31: Option<usize>,
    pub witness_direct_sum_physical_contained: Option<bool>,
    pub witness_direct_sum_legal_contained: Option<bool>,
    pub witness_direct_sum_helper_contained: Option<bool>,
    /// Stronger control which replaces each balanced inactive semantic
    /// direction by the literal unbalanced e_r source.  Under the semantic
    /// aggregate probe, inactive sources also carry their public A_S claim
    /// coordinate through the same block elimination.
    pub witness_direct_sum_unbalanced_physical_augmented_view_rank_m31: Option<usize>,
    pub witness_direct_sum_unbalanced_physical_contained: Option<bool>,
    /// Valid-view companion: each physical semantic source carries the exact
    /// linear H=sum factor_c*C_c sumcheck observation induced by that same
    /// committed-column difference.  The remaining independently variable
    /// sumcheck source has zero initial claim.  This is the protocol-coupled
    /// target; it must not be confused with the stronger independent direct
    /// sum above.
    pub witness_coupled_physical_augmented_view_rank_m31: Option<usize>,
    pub witness_coupled_legal_augmented_view_rank_m31: Option<usize>,
    pub witness_coupled_helper_augmented_view_rank_m31: Option<usize>,
    pub witness_coupled_physical_contained: Option<bool>,
    pub witness_coupled_legal_contained: Option<bool>,
    pub witness_coupled_helper_contained: Option<bool>,
    /// The conditional sumcheck fiber fixes both the initial claim and the
    /// verifier-computed terminal.  Its free wire therefore has 269 QM31
    /// (1,076 M31) directions, not the 270 QM31 zero-initial-only ambient
    /// used by the deliberately stronger independent direct-sum control.
    pub witness_coupled_legal_sumcheck_generators_m31: usize,
    pub witness_coupled_terminal_dependent_observation: Option<usize>,
    pub witness_coupled_terminal_functional_fingerprint: u64,
    pub witness_coupled_terminal_identity_guard: bool,
    pub witness_mask_raw_kernel_terminal_zero_sources_m31: usize,
    pub witness_mask_raw_kernel_terminal_zero_guard: bool,
    pub witness_h_zero_sumcheck_terminal_guard: bool,
    pub witness_mask_sumcheck_equals_terminal_kernel: bool,
    pub witness_compatibility_terminal_map_rank_m31: usize,
    pub witness_compatibility_terminal_map_fingerprint: u64,
    pub witness_compatibility_pivot_sources: Vec<usize>,
    pub witness_compatibility_pivot_rows_m31: Vec<usize>,
    /// Four coefficients per uncovered semantic source, expressed against
    /// `witness_compatibility_pivot_sources`; the uncovered source itself has
    /// implicit coefficient one.
    pub witness_semantic_kernel_coefficients_m31: Vec<u32>,
    /// True iff the exact physical per-column B_c semantic PCS map passed one
    /// full 16-column randomized projection against an independent dense
    /// C2/`StateOnlyIncrementalRelation` execution.
    pub witness_semantic_sparse_dense_guard: bool,
    pub witness_semantic_sparse_dense_fingerprint: u64,
    /// Stronger, nonphysical upper-oracle control using internally consistent
    /// unbalanced e_r raw/PCS sources.  It is reported separately and never
    /// decides same-statement physical containment.
    pub witness_unbalanced_semantic_superset_generators_m31: usize,
    pub witness_unbalanced_semantic_superset_rank: usize,
    pub witness_unbalanced_compatibility_rank_m31: usize,
    pub witness_unbalanced_compatibility_pivot_sources: Vec<usize>,
    pub witness_unbalanced_sparse_dense_guard: bool,
    pub witness_unbalanced_sparse_dense_fingerprint: u64,
    pub witness_unbalanced_semantic_superset_minor: RankMinorProvenance,
    /// Present only for the caller-supplied, production-neutral actual-trace
    /// projection diagnostic.
    pub witness_difference_projection: Option<WitnessDifferenceProjectionReport>,
    pub witness_semantic_superset_minor: RankMinorProvenance,
    pub witness_legal_sumcheck_minor: RankMinorProvenance,
    pub late_switch_source_rows: Vec<usize>,
    pub late_switch_variables_qm31: usize,
    pub late_switch_conditioned_kernel_qm31: usize,
    pub late_switch_conditioned_rank: usize,
    pub late_switch_semantic_augmented_rank: usize,
    pub late_switch_semantic_new_pivots_m31: Vec<usize>,
    pub late_switch_contains_conservative_semantic_superset: bool,
    pub late_switch_ambient_deficit_m31: usize,
    pub late_switch_complement_pivots_later_m31: usize,
    pub late_switch_complement_pivots_ood_m31: usize,
    pub late_switch_complement_pivots_relation_m31: usize,
    pub late_switch_complement_pivots_final_m31: usize,
    /// True only for the full carried/fresh single-switch observation
    /// quotient. The older late-switch probes model only a carried tail.
    pub masked_switch_joint_probe: bool,
    /// True when the encoding-randomness subspace is
    /// `(x^2+1) * M31[x]_{<q}` and the message coordinates are its explicit
    /// ordinary-polynomial complement.
    pub masked_switch_universal_mds_basis: bool,
    /// Exact M31 rank of the generated logical-to-natural basis.
    pub masked_switch_code_basis_rank_m31: usize,
    /// The production q schedule maps to q distinct root-one M31 abscissae.
    pub masked_switch_query_abscissae_distinct: bool,
    /// False for the universal basis: no sampled minor or rank retry is part
    /// of the honest prover algorithm.
    pub masked_switch_rank_retry_required: bool,
    /// Frozen q16 basis fingerprint. Zero only for the retained q29 research
    /// comparison, whose generalized basis is generated inside this gate.
    pub masked_switch_code_basis_fingerprint: u64,
    /// Total carried-X plus fresh-F scalar variables before conditioning.
    pub masked_switch_variables_qm31: usize,
    /// Rank of `(U,t_X,mu_F,A X,A F)` over QM31.
    pub masked_switch_observation_rank_qm31: usize,
    /// Rank after removing the disclosed U coefficient block while retaining
    /// the actual tau=L(U+pX) row and raw X/F query fibers.
    pub masked_switch_without_u_observation_rank_qm31: usize,
    pub masked_switch_without_u_kernel_qm31: usize,
    pub masked_switch_u_observation_rank_redundant: bool,
    /// Dimension left after fixing the complete single-switch public view.
    pub masked_switch_kernel_qm31: usize,
    /// Rank of the q-by-29 carried-randomness evaluation block.
    pub masked_switch_q_randomness_rank_qm31: usize,
    /// Rank of all q carried/fresh co-openings once public U is fixed.
    pub masked_switch_q_coopening_rank_qm31: usize,
    /// Rank of the `(2q+3)`-coordinate affine one-time-pad reveal map.
    pub masked_switch_otp_rank_qm31: usize,
    /// Legacy diagnostic rank after appending the two line-OOD Horner
    /// evaluations used by the standalone switch probe. Profile 21's
    /// selected direct-q logical-U extension is beta-free, so this is not a
    /// production-View or EPRO-schedule coordinate.
    pub masked_switch_u_rank_qm31: usize,
    pub masked_switch_u_plus_legacy_ood_diagnostic_rank_qm31: usize,
    /// Complete-view rank if X/F are opened as their four raw circle-C2
    /// symbols inside the existing root-zero leaf instead of as one folded
    /// root-one symbol.  This is a hiding gate for the tempting shared-root
    /// Merkle optimization: the raw slots are public transcript data, even
    /// when their frontier is shared with an existing commitment.
    pub masked_switch_shared_c2_observation_rank_qm31: usize,
    pub masked_switch_shared_c2_kernel_qm31: usize,
    /// Rank of one q-by-four raw C2 opening block on the code-randomness
    /// coordinates.  A value above q records the extra leakage introduced by
    /// opening pre-fold slots rather than the folded line symbol.
    pub masked_switch_shared_c2_randomness_rank_qm31: usize,
    pub masked_switch_standalone_frontier_nodes: usize,
    pub masked_switch_shared_root_increment_bytes: usize,
    pub masked_switch_standalone_increment_bytes: usize,
    pub coordinate_prefix_sumcheck_ranks: Vec<usize>,
    pub coordinate_prefix_pcs_ranks: Vec<usize>,
    /// Block-diagonal raw-opening minor: 26 M31-oracle blocks of width 76
    /// followed by the QM31 G block of width 268 at q16.
    pub raw_opening_minor: RankMinorProvenance,
    /// Canonical numeric minor selected by the exact masked-sumcheck
    /// elimination. Source ids are the stable mask-basis enumeration used by
    /// this gate, before any raw-view quotienting.
    pub masked_sumcheck_minor: RankMinorProvenance,
    /// Fixed square minor of the original joint raw-plus-compressed-sumcheck
    /// matrix.  This is the block-triangular union of `raw_opening_minor` and
    /// `masked_sumcheck_minor`; sumcheck rows are offset by the complete raw
    /// row count.  Unlike a rank number, these source/row lists identify the
    /// concrete determinant polynomial whose degree and nonzeroness must be
    /// proved for a Good22 liveness ledger.
    pub joint_raw_sumcheck_minor: RankMinorProvenance,
    /// Canonical numeric minor for the post-sumcheck PCS image, including the
    /// inactive-helper columns which increase the image rank.
    pub post_sumcheck_pcs_minor: RankMinorProvenance,
    /// Canonical quotient-complement minor contributed by the selected
    /// masked switch. Source id `4*variable+tower_coordinate` identifies the
    /// exact switch direction inserted into the quotient.
    pub late_switch_complement_minor: RankMinorProvenance,
    /// Canonical 208-M31 public-observation minor quotiented before the
    /// 68-dimensional switch complement is inserted into the PCS image.
    pub late_switch_observation_minor: RankMinorProvenance,
    pub mask_basis_columns_examined: usize,
    pub elapsed_millis: u128,
}

/// Exact source-level probe for the profile-22 root-neutral masked-sumcheck
/// reduction.  This is deliberately separate from the complete PCS rank
/// gate: nonzero `gamma` eliminates the full-QM31 G table pointwise, so the
/// only remaining question is whether the ten mask-only C1 raw kernels span
/// every legal (zero-initial-claim) sumcheck wire direction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateOnlyRootNeutralSumcheckReport {
    pub factor_schedule: &'static str,
    pub query_count: usize,
    pub gamma_nonzero: bool,
    pub c1_raw_m31: usize,
    pub legal_sumcheck_m31: usize,
    pub mask_only_columns: usize,
    pub raw_kernel_m31: usize,
    pub raw_plus_initial_kernel_m31: usize,
    pub unconditioned_sumcheck_rank_m31: usize,
    pub mask_only_root_neutral_legal_sumcheck_rank_m31: usize,
    pub semantic_raw_kernel_m31: usize,
    /// Diagnostic upper bound obtained by pairing H1 padding with G while
    /// assigning H1 zero direct sumcheck image.  Production H1 does have a
    /// direct unmasked-oracle image, so this field is not by itself a proof.
    pub idealized_h1_root_neutral_kernel_m31: usize,
    pub idealized_h1_root_neutral_legal_sumcheck_rank_m31: usize,
    pub root_neutral_legal_sumcheck_rank_m31: usize,
    pub prefix_root_neutral_legal_ranks_m31: Vec<usize>,
    pub complete: bool,
    pub elapsed_millis: u128,
}

/// Bounded host-only scan of additional full-domain QM31 mask lanes.
///
/// This report describes a rank diagnostic, not a proof-wire candidate.  The
/// factors are inserted in the reported order at consecutive generator
/// exponents beginning immediately after production G.  Prefix ranks make
/// the first successful lane count explicit without rerunning an unbounded
/// subset search.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateOnlyMultiQm31LaneProbeReport {
    pub factor_descriptions: Vec<String>,
    pub factor_degrees: Vec<usize>,
    pub gamma_exponents: Vec<usize>,
    /// Entry zero is the production-width control; entry `i` includes the
    /// first `i` additional lanes.
    pub prefix_masked_sumcheck_ranks_m31: Vec<usize>,
    pub masked_sumcheck_target_m31: usize,
    /// Minimum successful prefix in this explicitly ordered bounded family.
    /// This is not a global minimum over all degree-at-most-26 factors.
    pub minimum_complete_prefix_lanes: Option<usize>,
    pub complete_full_view_replayed: bool,
    pub joint_pcs_rank_m31: Option<usize>,
    pub joint_pcs_declared_rank_m31: Option<usize>,
    pub physical_augmented_rank_m31: Option<usize>,
    pub legal_augmented_rank_m31: Option<usize>,
    pub physical_contained: Option<bool>,
    pub legal_contained: Option<bool>,
    pub elapsed_millis: u128,
}

/// Exact host-only replay of the zero-width weighted inactive-sum repair.
///
/// Eight existing mask-only M31 columns gain one unbalanced inactive-sum
/// source each.  Their one public QM31 aggregate is fixed before a fresh
/// nonzero `delta`; the ordinary PCS word is then grouped as
/// `S_gamma + delta * U_gamma`, where `S` contains semantic C1 plus H and
/// `U` contains every mask-only C1 column plus G.  Raw/three-point openings
/// and the masked-zerocheck map are unchanged.  This report is research
/// evidence only and does not alter a production proof wire.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateOnlyWeightedInactiveSumRankReport {
    pub source_group: &'static str,
    pub selected_columns: Vec<usize>,
    pub auxiliary_delta_nonzero: bool,
    pub additional_private_sources_m31: usize,
    pub aggregate_claim_rank_m31: usize,
    pub aggregate_claim_minor: RankMinorProvenance,
    pub conditioned_kernel_m31: usize,
    /// Rank after conditioning on the fixed aggregate claim and omitting its
    /// four public coordinates.  `complete_view.witness_direct_sum_*` retains
    /// those coordinates and is the literal full-View accounting.
    pub conditioned_mask_view_rank_m31: Option<usize>,
    pub conditioned_physical_augmented_view_rank_m31: Option<usize>,
    pub conditioned_legal_augmented_view_rank_m31: Option<usize>,
    pub conditioned_helper_augmented_view_rank_m31: Option<usize>,
    pub conditioned_unbalanced_physical_augmented_view_rank_m31: Option<usize>,
    pub pcs_schedule: &'static str,
    pub complete_view: StateOnlyHidingRankGateReport,
}

/// Exact quotient image of one caller-supplied semantic-trace / unmasked
/// sumcheck difference under the frozen atomic profile-21 mask schedule.
///
/// The compatibility remainder must vanish for a legal zero-initial-claim
/// zerocheck transcript. `pcs_quotient_*` is the remainder after quotienting
/// the 712-dimensional baseline mask image. The four semantic quotient
/// coordinates use the canonical pivot rows selected by the conservative
/// semantic audit; `outside_conservative_superset_*` must be empty.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WitnessDifferenceProjectionReport {
    pub compatibility_remainder_rows_m31: Vec<usize>,
    pub compatibility_remainder_values_m31: Vec<u32>,
    pub compatibility_kernel: bool,
    pub pcs_quotient_rows_m31: Vec<usize>,
    pub pcs_quotient_values_m31: Vec<u32>,
    pub semantic_quotient_pivot_rows_m31: Vec<usize>,
    pub semantic_quotient_coordinates_m31: Vec<u32>,
    pub outside_conservative_superset_rows_m31: Vec<usize>,
    pub outside_conservative_superset_values_m31: Vec<u32>,
    pub inside_conservative_superset: bool,
    pub fingerprint: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtomicProfile21UpperOracleVariantReport {
    pub support: &'static str,
    pub pcs_rank: usize,
    pub upper_new_pivots_m31: Vec<usize>,
    pub upper_minor: RankMinorProvenance,
    pub semantic_augmented_rank: usize,
    pub semantic_new_pivots_m31: Vec<usize>,
    pub legal_sumcheck_augmented_rank: usize,
    pub legal_sumcheck_new_pivots_m31: Vec<usize>,
    pub contains_conservative_semantic_and_legal_sumcheck: bool,
}

/// One exact host-only scan of upper-half entropy in the existing G/H oracle
/// leaves on the literal atomic profile-21 q16 schedule.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtomicProfile21UpperOracleRankReport {
    pub query_count: usize,
    pub message_log: u32,
    pub codeword_domain_log: u32,
    pub codeword_len: usize,
    pub rate_denominator: usize,
    pub codeword_len_at_rate_1_512: usize,
    pub final_coefficients_qm31: usize,
    pub layer0_opened_symbols_per_oracle: usize,
    pub later_opened_symbols_per_oracle: usize,
    pub ood_values_per_oracle: usize,
    pub relation_coefficients_per_oracle: usize,
    pub pcs_tail_qm31: usize,
    pub joint_pcs_m31: usize,
    pub masked_sumcheck_rank_m31: usize,
    pub baseline_pcs_rank_m31: usize,
    pub baseline_semantic_augmented_rank_m31: usize,
    pub baseline_legal_sumcheck_augmented_rank_m31: usize,
    pub semantic_minor: RankMinorProvenance,
    pub legal_sumcheck_minor: RankMinorProvenance,
    pub variants: Vec<AtomicProfile21UpperOracleVariantReport>,
    pub elapsed_millis: u128,
}

/// One coordinate of the exact zero-slice embedding scan. The original
/// ten-variable trace is committed on inserted bit zero; one existing full
/// QM31 G helper lane carries independent entropy on inserted bit one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtomicProfile21ZeroSliceEmbeddingVariantReport {
    /// MSB-first insertion position in `0..=10`.
    pub insertion_coordinate: usize,
    pub baseline_pcs_rank_m31: usize,
    pub mask_augmented_pcs_rank_m31: usize,
    pub mask_new_pivots_m31: Vec<usize>,
    pub semantic_augmented_rank_m31: usize,
    pub semantic_new_pivots_m31: Vec<usize>,
    pub legal_sumcheck_augmented_rank_m31: usize,
    pub legal_sumcheck_new_pivots_m31: Vec<usize>,
    pub contains_conservative_semantic_and_legal_sumcheck: bool,
    pub elapsed_millis: u128,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtomicProfile21ZeroSliceEmbeddingFailureReport {
    pub insertion_coordinate: usize,
    pub stage: &'static str,
    pub column: Option<usize>,
    pub got_rank_m31: usize,
    pub want_rank_m31: usize,
    pub elapsed_millis: u128,
}

/// Exact production-neutral scan over every insertion coordinate of the
/// claim-preserving log-11 zero-slice construction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtomicProfile21ZeroSliceEmbeddingScanReport {
    pub query_count: usize,
    pub codeword_domain_log: u32,
    pub rate_denominator: usize,
    pub variants: Vec<AtomicProfile21ZeroSliceEmbeddingVariantReport>,
    pub failures: Vec<AtomicProfile21ZeroSliceEmbeddingFailureReport>,
    pub elapsed_millis: u128,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtomicProfile21AffineSliceEmbeddingVariantReport {
    pub insertion_coordinate: usize,
    pub slice_value_m31: u32,
    pub baseline_pcs_rank_m31: usize,
    pub mask_augmented_pcs_rank_m31: usize,
    pub mask_new_pivots_m31: Vec<usize>,
    pub semantic_augmented_rank_m31: usize,
    pub semantic_new_pivots_m31: Vec<usize>,
    pub legal_sumcheck_augmented_rank_m31: usize,
    pub legal_sumcheck_new_pivots_m31: Vec<usize>,
    pub contains_conservative_semantic_and_legal_sumcheck: bool,
    pub elapsed_millis: u128,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtomicProfile21AffineSliceEmbeddingScanReport {
    pub query_count: usize,
    pub codeword_domain_log: u32,
    pub rate_denominator: usize,
    pub stopped_on_first_containment: bool,
    pub variants: Vec<AtomicProfile21AffineSliceEmbeddingVariantReport>,
    pub elapsed_millis: u128,
}

#[derive(Clone)]
struct WitnessDifferenceProjectionInput {
    semantic_columns: Vec<Vec<M31>>,
    sumcheck_observations: Vec<QM31>,
}

/// Machine-derived provenance for one deterministic streaming-elimination
/// minor.  The ordered source columns and ordered pivot rows select a square
/// nonzero minor. `pivot_values_m31` are the nonzero residual values before
/// normalization; the fingerprint binds all three lists and the block name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RankMinorProvenance {
    pub block: &'static str,
    pub source_columns: Vec<usize>,
    pub pivot_rows: Vec<usize>,
    pub pivot_values_m31: Vec<u32>,
    pub fingerprint: u64,
}

/// Conservative total-degree ledger for the one block-triangular mixed-M31
/// minor selected by the profile-21 rank replay.
///
/// This is an availability bound, not a privacy or soundness error.  More
/// importantly, `every_q_nonzero_polynomial_proved` remains false: the frozen
/// numeric minor proves nonzeroness for one q tuple, while applying the M31
/// Schwartz--Zippel ratio to every accepted q tuple still needs an all-q
/// nonzero-polynomial theorem for the residual PCS/complement block.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Profile21GoodScheduleDegreeBudget {
    pub combined_minor_rows: usize,
    pub circle_tensor_denominator_exponent: usize,
    pub circle_parameter_norm_denominator_degree_per_sample: usize,
    pub cleared_two_circle_denominator_degree: usize,
    pub target_entry_numerator_degree: usize,
    pub pcs_entry_numerator_degree: usize,
    pub raw_block_determinant_degree: usize,
    pub masked_sumcheck_determinant_degree: usize,
    pub baseline_pcs_determinant_degree: usize,
    pub switch_observation_determinant_degree: usize,
    pub switch_complement_determinant_degree: usize,
    pub combined_determinant_degree: usize,
    pub m31_schwartz_zippel_denominator: u64,
    pub retry_cap_for_100_bit_completeness: usize,
    pub retry_cap_for_128_bit_completeness: usize,
    pub every_q_nonzero_polynomial_proved: bool,
}

/// Return the mechanically pinned degree ledger for the selected q16/rate
/// 1/512 profile.  Degrees are in the M31 coordinates of all QM31 schedule
/// coins.  In particular, one inverse of `1+t^2` is cleared with the degree-8
/// norm denominator of the degree-four extension; it is not incorrectly
/// counted as a degree-2 scalar denominator.
pub const fn profile21_good_schedule_degree_budget() -> Profile21GoodScheduleDegreeBudget {
    const QM31_OVER_M31_DEGREE: usize = 4;
    // Circle tensor factors are y,x,T2(x),...,T256(x).  Selecting all of
    // them uses denominator exponent 1+(1+2+...+256)=512.
    const CIRCLE_TENSOR_DENOMINATOR_EXPONENT: usize = 1usize << (STATE_ONLY_LOG_ROWS - 1);
    // Norm(1+t^2) has M31-coordinate degree 2*[QM31:M31] = 8.
    const PARAMETER_NORM_DEGREE: usize = 2 * QM31_OVER_M31_DEGREE;
    const PER_CIRCLE_SAMPLE_DEGREE: usize =
        CIRCLE_TENSOR_DENOMINATOR_EXPONENT * PARAMETER_NORM_DEGREE;
    const CLEARED_TWO_CIRCLE_DEGREE: usize = CANDIDATE_OOD_SAMPLES * PER_CIRCLE_SAMPLE_DEGREE;

    // Initial weights have eq(z) degree 10 and kappa^2 degree 2.  One
    // arity-four dual fold adds at most alpha^3.
    const TARGET_ENTRY_DEGREE: usize =
        CLEARED_TWO_CIRCLE_DEGREE + STATE_ONLY_HIDING_SUMCHECK_ROUNDS + 2 + 3;
    // The first line layer has degree 255.  Its weight is carried through two
    // later folds (+6), then multiplied by round-three coefficients (+9).
    const FIRST_LINE_TENSOR_DEGREE: usize = (1usize << (STATE_ONLY_LOG_ROWS - 2)) - 1;
    const PCS_TAIL_ENTRY_DEGREE: usize =
        CLEARED_TWO_CIRCLE_DEGREE + 1 + FIRST_LINE_TENSOR_DEGREE + 2 * 3 + 3 * 3;
    const MAX_GAMMA_EXPONENT: usize =
        STATE_ONLY_HIDING_C1_COLUMNS + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS + 1;
    const PCS_ENTRY_DEGREE: usize = PCS_TAIL_ENTRY_DEGREE + MAX_GAMMA_EXPONENT;

    const RAW_BLOCKS: usize =
        STATE_ONLY_HIDING_C1_COLUMNS + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS + 1;
    const RAW_TERMINAL_M31_ROWS_PER_BLOCK: usize = 3 * 4;
    const RAW_DEGREE: usize =
        RAW_BLOCKS * RAW_TERMINAL_M31_ROWS_PER_BLOCK * STATE_ONLY_HIDING_SUMCHECK_ROUNDS;
    // At round nine, eq(prefix,row) has schedule degree nine and the largest
    // public mask factor has degree 26.
    const SUMCHECK_ENTRY_DEGREE: usize =
        (STATE_ONLY_HIDING_SUMCHECK_ROUNDS - 1) + MASK_SUMCHECK_DEGREE - 1;
    const SUMCHECK_DEGREE: usize = MASK_SUMCHECK_QUOTIENT_M31 * SUMCHECK_ENTRY_DEGREE;
    const BASELINE_PCS_ROWS: usize = 712;
    const BASELINE_PCS_DEGREE: usize = BASELINE_PCS_ROWS * PCS_ENTRY_DEGREE;
    // The canonical 208-row observation minor contains all 140 U rows, four
    // t_X rows, and the 64 A(X) rows.  Only U (delta-linear) and t_X carry
    // schedule degree.
    const SWITCH_OBSERVATION_DEGREE: usize = 35 * 4 + 4 * TARGET_ENTRY_DEGREE;
    const SWITCH_COMPLEMENT_ROWS: usize = 68;
    const SWITCH_COMPLEMENT_DEGREE: usize = SWITCH_COMPLEMENT_ROWS * PCS_ENTRY_DEGREE;
    const COMBINED_DEGREE: usize = RAW_DEGREE
        + SUMCHECK_DEGREE
        + BASELINE_PCS_DEGREE
        + SWITCH_OBSERVATION_DEGREE
        + SWITCH_COMPLEMENT_DEGREE;

    Profile21GoodScheduleDegreeBudget {
        combined_minor_rows: 2244 + 1080 + 712 + 208 + 68,
        circle_tensor_denominator_exponent: CIRCLE_TENSOR_DENOMINATOR_EXPONENT,
        circle_parameter_norm_denominator_degree_per_sample: PER_CIRCLE_SAMPLE_DEGREE,
        cleared_two_circle_denominator_degree: CLEARED_TWO_CIRCLE_DEGREE,
        target_entry_numerator_degree: TARGET_ENTRY_DEGREE,
        pcs_entry_numerator_degree: PCS_ENTRY_DEGREE,
        raw_block_determinant_degree: RAW_DEGREE,
        masked_sumcheck_determinant_degree: SUMCHECK_DEGREE,
        baseline_pcs_determinant_degree: BASELINE_PCS_DEGREE,
        switch_observation_determinant_degree: SWITCH_OBSERVATION_DEGREE,
        switch_complement_determinant_degree: SWITCH_COMPLEMENT_DEGREE,
        combined_determinant_degree: COMBINED_DEGREE,
        m31_schwartz_zippel_denominator: 2_147_483_647,
        retry_cap_for_100_bit_completeness: 13,
        retry_cap_for_128_bit_completeness: 16,
        every_q_nonzero_polynomial_proved: false,
    }
}

impl RankMinorProvenance {
    fn empty(block: &'static str) -> Self {
        Self {
            block,
            source_columns: Vec::new(),
            pivot_rows: Vec::new(),
            pivot_values_m31: Vec::new(),
            fingerprint: rank_minor_fingerprint(block, &[], &[], &[]),
        }
    }

    fn from_parts(
        block: &'static str,
        source_columns: Vec<usize>,
        pivot_rows: Vec<usize>,
        pivot_values: Vec<M31>,
    ) -> Self {
        debug_assert_eq!(source_columns.len(), pivot_rows.len());
        debug_assert_eq!(source_columns.len(), pivot_values.len());
        let pivot_values_m31 = pivot_values
            .into_iter()
            .map(|value| value.0)
            .collect::<Vec<_>>();
        let fingerprint =
            rank_minor_fingerprint(block, &source_columns, &pivot_rows, &pivot_values_m31);
        Self {
            block,
            source_columns,
            pivot_rows,
            pivot_values_m31,
            fingerprint,
        }
    }
}

fn rank_minor_fingerprint(
    block: &str,
    source_columns: &[usize],
    pivot_rows: &[usize],
    pivot_values_m31: &[u32],
) -> u64 {
    debug_assert_eq!(source_columns.len(), pivot_rows.len());
    debug_assert_eq!(source_columns.len(), pivot_values_m31.len());
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    let mut absorb = |bytes: &[u8]| {
        for &byte in bytes {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
        }
    };
    absorb(b"aspis/profile21/rank-minor-provenance/v1");
    absorb(&(block.len() as u64).to_le_bytes());
    absorb(block.as_bytes());
    absorb(&(source_columns.len() as u64).to_le_bytes());
    for ((&source, &row), &value) in source_columns.iter().zip(pivot_rows).zip(pivot_values_m31) {
        absorb(&(source as u64).to_le_bytes());
        absorb(&(row as u64).to_le_bytes());
        absorb(&value.to_le_bytes());
    }
    hash
}

fn m31_matrix_fingerprint(block: &str, columns: &[Vec<M31>]) -> u64 {
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    let mut absorb = |bytes: &[u8]| {
        for &byte in bytes {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
        }
    };
    absorb(b"aspis/profile21/m31-matrix/v1");
    absorb(&(block.len() as u64).to_le_bytes());
    absorb(block.as_bytes());
    absorb(&(columns.len() as u64).to_le_bytes());
    for column in columns {
        absorb(&(column.len() as u64).to_le_bytes());
        for value in column {
            absorb(&value.0.to_le_bytes());
        }
    }
    hash
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PcsSchedule {
    Arity4x4,
    Arity4ThenArity8,
    /// Diagnostic exact-sequence target: retain the canonical balanced
    /// gamma-combined root message itself instead of applying any PCS
    /// continuation.  If the raw+sumcheck kernel spans this complete module,
    /// every later linear PCS/fold/OOD view is contained automatically.
    RootMessage,
    /// V6 exact-sequence target.  The root-message map is identical to
    /// `RootMessage`, but the q16 raw openings are evaluated on V6's log-20
    /// circle domain rather than the legacy log-19 q16 diagnostic domain.
    RootMessageV6Log20,
}

impl PcsSchedule {
    fn is_root_message(self) -> bool {
        matches!(self, Self::RootMessage | Self::RootMessageV6Log20)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FactorSchedule {
    Production,
    SharedLinear,
    FullSharedLinear,
    /// Production-neutral repair probe.  This is the full shared-linear
    /// schedule, except that the explicit QM31 G lane supplies the unique
    /// missing shared power `L_0^23` instead of `1 + L_16^26`.
    CompleteSharedPowers,
    /// Host-only zero-width degree-cover probe.  Relative to the full shared
    /// schedule, semantic lane 13 uses `L_0^23` instead of `L_0^26`.
    /// Consequently the 26 M31 lanes cover restricted-line degrees 0..=25
    /// exactly, while production-shaped QM31 G remains `1 + L_16^26` and
    /// supplies the sole degree-26 leading term.
    SharedDegreesZeroToTwentyFive,
    /// Host-only zero-width G enrichment.  All 26 M31 lanes retain the full
    /// shared-L0 schedule, while the one existing QM31 G factor becomes
    /// `1 + L_16^26 + coefficient * L_0^exponent` on that same source lane.
    ExplicitGAddSharedPower {
        exponent: u8,
        coefficient: M31,
    },
    /// Host-only, zero-width diagnostic.  The existing sixteen semantic M31
    /// lanes, ten mask-only M31 lanes, and one QM31 G lane keep their frozen
    /// exponents, tower rotations, gamma positions, and raw-opening maps;
    /// only the public dense affine family used by each factor changes.
    DistinctLinear {
        assignment: DistinctLinearAssignment,
        g_factor: DistinctLinearGFactor,
        /// Ordered, bounded CU screen: the first `prefix_m31_lanes` M31 lanes
        /// use their assigned family and the remainder retain shared family
        /// zero.  G always uses its assigned nonzero-slope family.  Full
        /// distinct-linear is the exact value 26.
        prefix_m31_lanes: u8,
    },
}

const DISTINCT_LINEAR_M31_LANES: usize =
    STATE_ONLY_HIDING_C1_COLUMNS + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS;

const SEMANTIC_FACTOR_EXPONENTS: [usize; STATE_ONLY_HIDING_C1_COLUMNS] =
    [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 13, 25];

const MASK_ONLY_FACTOR_EXPONENTS: [usize; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS] =
    [1, 3, 5, 7, 9, 11, 15, 17, 19, 21];

/// Predeclared deterministic dense-family assignments for the host-only
/// distinct-linear probe.  Every variant is a bijection from the 27 existing
/// source lanes to families 1..=27; no subset or combinatorial search occurs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DistinctLinearAssignment {
    /// Lane `j` uses family `j+1`.
    LanePlusOne,
    /// Lane `j` uses family `1 + ((7*j + 3) mod 27)`.
    AffineSevenPlusThree,
    /// Lane `j` uses family `27-j`.
    Reverse,
}

impl DistinctLinearAssignment {
    pub fn family_for_lane(self, lane: usize) -> u8 {
        debug_assert!(lane < DISTINCT_LINEAR_M31_LANES + 1);
        match self {
            Self::LanePlusOne => (lane + 1) as u8,
            Self::AffineSevenPlusThree => (1 + (7 * lane + 3) % 27) as u8,
            Self::Reverse => (27 - lane) as u8,
        }
    }

    pub fn label(self) -> &'static str {
        match self {
            Self::LanePlusOne => "lane_plus_one",
            Self::AffineSevenPlusThree => "affine_7j_plus_3_mod_27",
            Self::Reverse => "reverse_27_minus_j",
        }
    }
}

/// Alternative factor retained on the one existing QM31 G source lane.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DistinctLinearGFactor {
    /// `L_family^23`.  Together with the frozen M31 exponents this gives one
    /// restricted-line degree in every degree 0..=26, with nonzero slope in
    /// all ten rounds for the bounded family set.
    MissingDegree23,
    /// Control matching the old G shape: `1 + L_family^26`.  Degree 26 is
    /// already present on one semantic lane, though its family differs.
    Degree26AddOne,
}

impl DistinctLinearGFactor {
    pub fn label(self) -> &'static str {
        match self {
            Self::MissingDegree23 => "l_pow23",
            Self::Degree26AddOne => "one_plus_l_pow26",
        }
    }
}

/// Production-neutral factor choices for one extra full-domain QM31 G2 mask
/// lane at gamma exponent 28.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TailQm31MaskFactor {
    /// Historical control: the lane perturbs PCS only and contributes zero to
    /// the masked zerocheck transcript.
    Zero,
    /// Literal constant-one factor. The lane participates in the masked
    /// zerocheck while retaining the existing degree-27 wire envelope.
    ConstantOne,
    /// Independent dense family 17, `1 + L^26` (masked degree 27).
    Dense17Pow26AddOne,
    /// Independent dense family 17, `L^23` (masked degree 24).
    Dense17Pow23,
    /// The shared family-0 form `L_0^23` (masked degree 24).  This is the
    /// sole exponent absent from the twenty-six existing shared factors and
    /// is intended for an *additional* G2 lane, never as a replacement for
    /// production G.
    Shared0Pow23,
    /// Host-only parameterized dense factor
    /// `add_one + L_family^exponent`.  The public probe rejects exponents
    /// above 26.  Production factor tables and fingerprints do not use this
    /// variant.
    DensePower {
        family: u8,
        exponent: u8,
        add_one: bool,
    },
}

/// Fixed low-degree multiplier for the authenticated X codeword in the first
/// later word, `W1 = Fold(W0) + Enc(U) + p(t) Enc(X)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FirstLaterXMultiplier {
    One,
    /// `(t^2 + 1)^power`; M31 is 3 mod 4, so this has no M31 roots.
    X2PlusOnePower(u8),
}

impl FirstLaterXMultiplier {
    fn ordinary_coefficients(self) -> Option<Vec<M31>> {
        match self {
            Self::One => Some(vec![M31::ONE]),
            Self::X2PlusOnePower(power) if (1..=8).contains(&power) => {
                let mut polynomial = vec![M31::ONE];
                for _ in 0..power {
                    let mut next = vec![M31::ZERO; polynomial.len() + 2];
                    for (degree, &coefficient) in polynomial.iter().enumerate() {
                        next[degree] = next[degree].add(coefficient);
                        next[degree + 2] = next[degree + 2].add(coefficient);
                    }
                    polynomial = next;
                }
                Some(polynomial)
            }
            Self::X2PlusOnePower(_) => None,
        }
    }

    fn label(self) -> &'static str {
        match self {
            Self::One => "one",
            Self::X2PlusOnePower(1) => "x2_plus_one",
            Self::X2PlusOnePower(2) => "x2_plus_one_squared",
            Self::X2PlusOnePower(3) => "x2_plus_one_cubed",
            Self::X2PlusOnePower(4) => "x2_plus_one_pow4",
            Self::X2PlusOnePower(5) => "x2_plus_one_pow5",
            Self::X2PlusOnePower(6) => "x2_plus_one_pow6",
            Self::X2PlusOnePower(7) => "x2_plus_one_pow7",
            Self::X2PlusOnePower(8) => "x2_plus_one_pow8",
            Self::X2PlusOnePower(_) => "invalid",
        }
    }
}

impl TailQm31MaskFactor {
    fn label(self) -> &'static str {
        match self {
            Self::Zero => "zero",
            Self::ConstantOne => "constant_one",
            Self::Dense17Pow26AddOne => "dense17_1_plus_l26",
            Self::Dense17Pow23 => "dense17_l23",
            Self::Shared0Pow23 => "shared0_l23",
            Self::DensePower { .. } => "parameterized_dense_power_host_only",
        }
    }

    fn degree(self) -> usize {
        match self {
            Self::Zero | Self::ConstantOne => 0,
            Self::Dense17Pow26AddOne => 26,
            Self::Dense17Pow23 | Self::Shared0Pow23 => 23,
            Self::DensePower { exponent, .. } => usize::from(exponent),
        }
    }

    fn description(self) -> String {
        match self {
            Self::DensePower {
                family,
                exponent,
                add_one,
            } => format!(
                "{}L_{}^{}",
                if add_one { "1+" } else { "" },
                family,
                exponent
            ),
            _ => self.label().to_owned(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RankLayout {
    StateOnlyV4,
    AtomicV3,
}

fn rank_active_rows(layout: RankLayout) -> &'static [u16] {
    match layout {
        RankLayout::StateOnlyV4 => state_only_copy_active_rows_v4(),
        RankLayout::AtomicV3 => atomic_state_only_copy_active_rows_v3(),
    }
}

fn rank_inactive_masks(layout: RankLayout) -> [u16; 64] {
    match layout {
        RankLayout::StateOnlyV4 => state_only_copy_inactive_row_masks_v4(),
        RankLayout::AtomicV3 => atomic_state_only_copy_inactive_row_masks_v3(),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LateSwitchSupport {
    None,
    /// Diagnostic only. Test a conservative superset of every atomic-v3
    /// same-statement witness difference against the baseline mask image.
    WitnessDifferenceSuperset,
    StructuredSource31,
    DistinctFolded31,
    MaskedSlotZeroSingleCodeword,
    /// Diagnostic all-q complement candidate: carry natural line
    /// coefficient 18 through the pre-alpha p0 wire, then use coefficients
    /// 0..17 at root one.  The leading-coefficient functional is outside
    /// every 16-point evaluation row space on `P_<19`.
    MaskedHighCoefficientSingleCodeword,
    /// Minimal semantic-only diagnostic: the one physical message coordinate
    /// remains natural coefficient 18 / row 72 in the old PCS view, while its
    /// switched code is `span{x} + (x^2+1) P_<16` (dimension 17).  The
    /// randomness block evaluates invertibly at every distinct q16 tuple, so
    /// the unique conditioned kernel necessarily carries the row-72 source.
    MaskedSemanticHighSingleCodeword,
    /// Production-shaped semantic-only candidate.  Add logical `1` / the
    /// existing root-one natural coefficient zero to the preceding shape, and
    /// quotient the four raw C2 symbols of X/F at every query.  The basis is
    /// `span{x,1} + (x^2+1) P_<16` (dimension 18); the expected raw-view
    /// conditioned kernel is one QM31 direction.
    MaskedSemanticHighSharedC2SingleCodeword,
    /// Bound reduced switch: V = span{B_18} (+) (x^2+1)P_<16. X/F use
    /// literal four-symbol shared-C2 q fibers and U=F+delta X is disclosed in
    /// the same 17-coordinate basis. The one conditioned QM31 kernel carries
    /// the physical natural-B18 p0 class.
    MaskedSemanticNatural18SharedC2SingleCodeword,
    /// Implementable-carry candidate: the already-authenticated X source
    /// lane is also the 29th main gamma lane at root zero.  One exact initial
    /// relation target for X is fixed before gamma; F remains source-only.
    MaskedFullXGammaLane,
    /// Claim-preserving physical-X candidate.  This is the same literal full
    /// authenticated X lane as `MaskedFullXGammaLane`, but X is sampled in
    /// the kernel of the exact initial relation covector.  The rank model
    /// therefore retains `L(X)=0` as a conditioning row while the wire sends
    /// no `t_X` scalar.  It also enables the conservative semantic-source
    /// containment audit instead of checking ambient rank alone.
    MaskedFullXGammaKernelLane,
    /// Physical post-alpha candidate: keep W0 unchanged and translate W1 by
    /// the full authenticated line polynomial `U+X`.  Tau is the exact
    /// first-later relation target of `U+X`, hence contributes one X
    /// observation after U is fixed.
    MaskedFullXFirstLaterLane,
    /// Lean native full root-zero C2 word. X has all 1024 independent QM31
    /// message coordinates; the public view is exactly raw q fibers plus the
    /// complete initial-relation target tX. The outer main-PCS coefficient is
    /// a fresh caller-supplied epsilon, with no X/F/U source machinery.
    LeanNativeFullRootX,
    /// Negative-control companion to `LeanNativeFullRootX`: condition the X
    /// translation on authenticated q symbols but deliberately omit the
    /// independently serialized `tX`.  This is not a sound protocol shape;
    /// it localizes whether the one public target functional is the remaining
    /// four-M31 affine obstruction.
    LeanNativeFullRootXRawOnlyControl,
}

#[derive(Clone, Copy)]
enum MaskFactor {
    Semantic(usize),
    MaskOnly(usize),
    ExplicitG,
}

fn qm31_coordinates(value: QM31) -> [M31; 4] {
    [value.c0.a, value.c0.b, value.c1.a, value.c1.b]
}

fn qm31_from_m31_coordinates(coordinates: &[M31]) -> Option<QM31> {
    (coordinates.len() == 4).then(|| QM31 {
        c0: CM31::new(coordinates[0], coordinates[1]),
        c1: CM31::new(coordinates[2], coordinates[3]),
    })
}

fn compressed_mask_sumcheck_terminal_from_m31(
    coordinates: &[M31],
    challenges: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
) -> Option<QM31> {
    if coordinates.len() != 4 * STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS {
        return None;
    }
    let observations = coordinates
        .chunks_exact(4)
        .map(qm31_from_m31_coordinates)
        .collect::<Option<Vec<_>>>()?;
    compressed_mask_sumcheck_terminal(&observations, challenges)
}

fn append_qm31_coordinates(target: &mut Vec<M31>, values: impl IntoIterator<Item = QM31>) {
    for value in values {
        target.extend_from_slice(&qm31_coordinates(value));
    }
}

fn add_scaled_m31(target: &mut [M31], source: &[M31], scale: M31) {
    debug_assert_eq!(target.len(), source.len());
    if scale == M31::ZERO {
        return;
    }
    for (target, source) in target.iter_mut().zip(source) {
        *target = target.add(scale.mul(*source));
    }
}

fn eq_weight(point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS], row: usize) -> QM31 {
    point
        .iter()
        .enumerate()
        .fold(QM31::ONE, |weight, (coordinate, value)| {
            let bit = (row >> (point.len() - 1 - coordinate)) & 1;
            weight.mul(if bit == 0 {
                QM31::ONE.sub(*value)
            } else {
                *value
            })
        })
}

fn factor_at(factor: MaskFactor, point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS]) -> QM31 {
    match factor {
        MaskFactor::Semantic(column) => state_only_c1_mask_factor(column, point),
        MaskFactor::MaskOnly(column) => state_only_mask_only_c1_factor(column, point),
        MaskFactor::ExplicitG => state_only_explicit_g_mask_factor(point),
    }
}

fn shared_mask_linear(point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS]) -> QM31 {
    dense_mask_linear(0, point)
}

/// Exact host mirror of the frozen dense affine family formula in
/// `aspis_core::state_only_hiding`.  This helper is deliberately local to the
/// rank diagnostic; it does not enter the production factor table or its
/// fingerprint.
fn dense_mask_linear(family: u8, point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS]) -> QM31 {
    point
        .iter()
        .enumerate()
        .fold(QM31::ZERO, |sum, (variable, value)| {
            let family = usize::from(family);
            let coefficient = 3 + 22 * variable + family * (17 + 8 * variable);
            sum.add(value.mul_m31(M31(coefficient as u32)))
        })
}

fn factor_at_schedule(
    schedule: FactorSchedule,
    factor: MaskFactor,
    point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
    coordinate_factored_mask_columns: Option<usize>,
) -> QM31 {
    if let FactorSchedule::DistinctLinear {
        assignment,
        g_factor,
        prefix_m31_lanes,
    } = schedule
    {
        let (lane, exponent, tower_coordinate, add_one) = match factor {
            MaskFactor::Semantic(column) => (
                column,
                SEMANTIC_FACTOR_EXPONENTS[column],
                Some(column & 3),
                false,
            ),
            MaskFactor::MaskOnly(column) => (
                STATE_ONLY_HIDING_C1_COLUMNS + column,
                MASK_ONLY_FACTOR_EXPONENTS[column],
                Some(column & 3),
                false,
            ),
            MaskFactor::ExplicitG => (
                DISTINCT_LINEAR_M31_LANES,
                match g_factor {
                    DistinctLinearGFactor::MissingDegree23 => 23,
                    DistinctLinearGFactor::Degree26AddOne => 26,
                },
                None,
                g_factor == DistinctLinearGFactor::Degree26AddOne,
            ),
        };
        let family = if lane < DISTINCT_LINEAR_M31_LANES && lane >= usize::from(prefix_m31_lanes) {
            0
        } else {
            assignment.family_for_lane(lane)
        };
        let mut value = dense_mask_linear(family, point).pow(exponent as u64);
        if let Some(coordinate) = tower_coordinate {
            value = state_only_mask_tower_basis(coordinate).mul(value);
        }
        if add_one {
            value = QM31::ONE.add(value);
        }
        return value;
    }
    if let MaskFactor::MaskOnly(index) = factor {
        if matches!(
            schedule,
            FactorSchedule::FullSharedLinear
                | FactorSchedule::CompleteSharedPowers
                | FactorSchedule::SharedDegreesZeroToTwentyFive
                | FactorSchedule::ExplicitGAddSharedPower { .. }
        ) {
            let exponent = if coordinate_factored_mask_columns.is_none() {
                MASK_ONLY_FACTOR_EXPONENTS[index]
            } else {
                MASK_ONLY_FACTOR_EXPONENTS[index]
            };
            return state_only_mask_tower_basis(index & 3)
                .mul(shared_mask_linear(point).pow(exponent as u64));
        }
        if coordinate_factored_mask_columns.is_some() {
            let linear = point
                .iter()
                .enumerate()
                .fold(QM31::ZERO, |sum, (variable, value)| {
                    sum.add(
                        value.mul_m31(M31((37 + 31 * index + (29 + 2 * index) * variable) as u32)),
                    )
                });
            return linear.pow((16 + index % 11) as u64);
        }
        return factor_at(factor, point);
    }
    if schedule == FactorSchedule::Production {
        return factor_at(factor, point);
    }
    if matches!(factor, MaskFactor::ExplicitG) {
        if let FactorSchedule::ExplicitGAddSharedPower {
            exponent,
            coefficient,
        } = schedule
        {
            return factor_at(factor, point).add(
                shared_mask_linear(point)
                    .pow(u64::from(exponent))
                    .mul_m31(coefficient),
            );
        }
        if schedule == FactorSchedule::CompleteSharedPowers {
            // The semantic and mask-only exponent schedules contain every
            // exponent in 0..=26 except 23.  G is QM31-valued, so this one
            // source supplies all four M31 coordinates of that missing
            // polynomial direction.  In every sumcheck round the restricted
            // shared form is C + (3 + 22*r)t with nonzero slope, hence this
            // remains the missing degree-23 direction for every prefix C.
            return shared_mask_linear(point).pow(23);
        }
        // One independent dense degree-26 factor restores the final four
        // M31 quotient directions lost when every oracle uses the same L.
        return factor_at(factor, point);
    }
    let linear = shared_mask_linear(point);
    match factor {
        MaskFactor::Semantic(column) => {
            state_only_mask_tower_basis(column & 3).mul(linear.pow(if schedule
                == FactorSchedule::SharedDegreesZeroToTwentyFive
                && column == 13
            {
                23
            } else {
                SEMANTIC_FACTOR_EXPONENTS[column]
            } as u64))
        }
        MaskFactor::ExplicitG => unreachable!(),
        MaskFactor::MaskOnly(_) => unreachable!(),
    }
}

fn lagrange_basis() -> [[M31; MASK_SUMCHECK_COEFFICIENTS]; MASK_SUMCHECK_COEFFICIENTS] {
    core::array::from_fn(|i| {
        let mut basis = [M31::ZERO; MASK_SUMCHECK_COEFFICIENTS];
        basis[0] = M31::ONE;
        let mut degree = 0usize;
        let mut denominator = M31::ONE;
        for j in 0..MASK_SUMCHECK_COEFFICIENTS {
            if i == j {
                continue;
            }
            let root = M31(j as u32);
            let previous = basis;
            for coefficient in 0..=degree + 1 {
                let shifted = if coefficient == 0 {
                    M31::ZERO
                } else {
                    previous[coefficient - 1]
                };
                let constant = if coefficient <= degree {
                    previous[coefficient].mul(root)
                } else {
                    M31::ZERO
                };
                basis[coefficient] = shifted.sub(constant);
            }
            degree += 1;
            denominator = denominator.mul(M31(i as u32).sub(root));
        }
        let inverse = denominator.inv();
        for value in &mut basis {
            *value = value.mul(inverse);
        }
        basis
    })
}

fn interpolate(
    values: &[QM31; MASK_SUMCHECK_COEFFICIENTS],
    basis: &[[M31; MASK_SUMCHECK_COEFFICIENTS]; MASK_SUMCHECK_COEFFICIENTS],
) -> [QM31; MASK_SUMCHECK_COEFFICIENTS] {
    core::array::from_fn(|coefficient| {
        (0..MASK_SUMCHECK_COEFFICIENTS).fold(QM31::ZERO, |sum, sample| {
            sum.add(values[sample].mul_m31(basis[sample][coefficient]))
        })
    })
}

fn evaluate(polynomial: &[QM31; MASK_SUMCHECK_COEFFICIENTS], point: QM31) -> QM31 {
    polynomial[..MASK_SUMCHECK_DEGREE]
        .iter()
        .rev()
        .copied()
        .fold(polynomial[MASK_SUMCHECK_DEGREE], |value, coefficient| {
            value.mul(point).add(coefficient)
        })
}

/// Evaluate the terminal claim represented by the compressed state-only
/// sumcheck wire: initial claim, then `c0,c2,...,c27` for each round.  The
/// omitted `c1` is recovered from the exact verifier boundary
/// `p(0)+p(1)=running_claim`.
fn compressed_mask_sumcheck_terminal(
    observations: &[QM31],
    challenges: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
) -> Option<QM31> {
    if observations.len() != STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS {
        return None;
    }
    let mut running_claim = observations[0];
    let mut cursor = 1usize;
    for &challenge in challenges {
        let c0 = observations[cursor];
        cursor += 1;
        let mut polynomial = [QM31::ZERO; MASK_SUMCHECK_COEFFICIENTS];
        polynomial[0] = c0;
        let mut high_sum = QM31::ZERO;
        for coefficient in 2..MASK_SUMCHECK_COEFFICIENTS {
            let value = observations[cursor];
            cursor += 1;
            polynomial[coefficient] = value;
            high_sum = high_sum.add(value);
        }
        // running = p(0)+p(1) = 2*c0 + c1 + sum_{k=2}^{27} c_k.
        polynomial[1] = running_claim.sub(c0.add(c0)).sub(high_sum);
        running_claim = evaluate(&polynomial, challenge);
    }
    (cursor == observations.len()).then_some(running_claim)
}

fn compressed_mask_sumcheck_terminal_coefficients(
    challenges: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
) -> Vec<QM31> {
    (0..STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS)
        .map(|observation| {
            let mut basis = vec![QM31::ZERO; STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS];
            basis[observation] = QM31::ONE;
            compressed_mask_sumcheck_terminal(&basis, challenges)
                .expect("fixed compressed sumcheck shape")
        })
        .collect()
}

fn mask_sumcheck_observations(
    row: usize,
    challenges: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
    lagrange: &[[M31; MASK_SUMCHECK_COEFFICIENTS]; MASK_SUMCHECK_COEFFICIENTS],
    factor: MaskFactor,
    factor_schedule: FactorSchedule,
    coordinate_factored_mask_columns: Option<usize>,
) -> Vec<QM31> {
    let boolean_point = core::array::from_fn(|coordinate| {
        let bit = (row >> (STATE_ONLY_HIDING_SUMCHECK_ROUNDS - 1 - coordinate)) & 1;
        if bit == 0 {
            QM31::ZERO
        } else {
            QM31::ONE
        }
    });
    let mut prefix = [QM31::ZERO; STATE_ONLY_HIDING_SUMCHECK_ROUNDS];
    let mut running_claim = factor_at_schedule(
        factor_schedule,
        factor,
        &boolean_point,
        coordinate_factored_mask_columns,
    );
    let mut observations = Vec::with_capacity(STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS);
    observations.push(running_claim);
    for round in 0..STATE_ONLY_HIDING_SUMCHECK_ROUNDS {
        let samples = core::array::from_fn(|sample| {
            prefix[round] = QM31::from_cm31(CM31::from_m31(M31(sample as u32)));
            for coordinate in round + 1..STATE_ONLY_HIDING_SUMCHECK_ROUNDS {
                let bit = (row >> (STATE_ONLY_HIDING_SUMCHECK_ROUNDS - 1 - coordinate)) & 1;
                prefix[coordinate] = if bit == 0 { QM31::ZERO } else { QM31::ONE };
            }
            eq_weight(&prefix, row).mul(factor_at_schedule(
                factor_schedule,
                factor,
                &prefix,
                coordinate_factored_mask_columns,
            ))
        });
        let polynomial = interpolate(&samples, lagrange);
        observations.push(polynomial[0]);
        observations.extend(polynomial[2..].iter().copied());
        running_claim = evaluate(&polynomial, challenges[round]);
        prefix[round] = challenges[round];
    }
    debug_assert_eq!(
        observations.len(),
        STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS
    );
    let _ = running_claim;
    observations
}

fn tail_qm31_factor_at(
    factor: TailQm31MaskFactor,
    point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
) -> QM31 {
    if factor == TailQm31MaskFactor::Zero {
        return QM31::ZERO;
    }
    if factor == TailQm31MaskFactor::ConstantOne {
        return QM31::ONE;
    }
    if factor == TailQm31MaskFactor::Shared0Pow23 {
        return shared_mask_linear(point).pow(23);
    }
    let family = match factor {
        TailQm31MaskFactor::DensePower { family, .. } => usize::from(family),
        _ => 17,
    };
    let linear = point
        .iter()
        .enumerate()
        .fold(QM31::ZERO, |sum, (variable, value)| {
            let scalar = 3 + 22 * variable + family * (17 + 8 * variable);
            sum.add(value.mul_m31(M31(scalar as u32)))
        });
    match factor {
        TailQm31MaskFactor::Zero => QM31::ZERO,
        TailQm31MaskFactor::ConstantOne => QM31::ONE,
        TailQm31MaskFactor::Dense17Pow26AddOne => QM31::ONE.add(linear.pow(26)),
        TailQm31MaskFactor::Dense17Pow23 => linear.pow(23),
        TailQm31MaskFactor::Shared0Pow23 => unreachable!(),
        TailQm31MaskFactor::DensePower {
            exponent, add_one, ..
        } => {
            let power = linear.pow(u64::from(exponent));
            if add_one {
                QM31::ONE.add(power)
            } else {
                power
            }
        }
    }
}

fn tail_qm31_sumcheck_observations(
    row: usize,
    challenges: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
    lagrange: &[[M31; MASK_SUMCHECK_COEFFICIENTS]; MASK_SUMCHECK_COEFFICIENTS],
    factor: TailQm31MaskFactor,
) -> Vec<QM31> {
    let boolean_point = core::array::from_fn(|coordinate| {
        let bit = (row >> (STATE_ONLY_HIDING_SUMCHECK_ROUNDS - 1 - coordinate)) & 1;
        if bit == 0 {
            QM31::ZERO
        } else {
            QM31::ONE
        }
    });
    let mut prefix = [QM31::ZERO; STATE_ONLY_HIDING_SUMCHECK_ROUNDS];
    let mut running_claim = tail_qm31_factor_at(factor, &boolean_point);
    let mut observations = Vec::with_capacity(STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS);
    observations.push(running_claim);
    for round in 0..STATE_ONLY_HIDING_SUMCHECK_ROUNDS {
        let samples = core::array::from_fn(|sample| {
            prefix[round] = QM31::from_cm31(CM31::from_m31(M31(sample as u32)));
            for coordinate in round + 1..STATE_ONLY_HIDING_SUMCHECK_ROUNDS {
                let bit = (row >> (STATE_ONLY_HIDING_SUMCHECK_ROUNDS - 1 - coordinate)) & 1;
                prefix[coordinate] = if bit == 0 { QM31::ZERO } else { QM31::ONE };
            }
            eq_weight(&prefix, row).mul(tail_qm31_factor_at(factor, &prefix))
        });
        let polynomial = interpolate(&samples, lagrange);
        observations.push(polynomial[0]);
        observations.extend(polynomial[2..].iter().copied());
        running_claim = evaluate(&polynomial, challenges[round]);
        prefix[round] = challenges[round];
    }
    debug_assert_eq!(
        observations.len(),
        STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS
    );
    let _ = running_claim;
    observations
}

/// Streaming column echelon form.  `insert` returns true exactly when the
/// column increases rank.
#[derive(Clone)]
struct ColumnEchelon {
    pivots: Vec<Option<Vec<M31>>>,
    rank: usize,
}

impl ColumnEchelon {
    fn new(rows: usize) -> Self {
        Self {
            pivots: vec![None; rows],
            rank: 0,
        }
    }

    fn insert_with_pivot_value(&mut self, mut column: Vec<M31>) -> Option<(usize, M31)> {
        debug_assert_eq!(column.len(), self.pivots.len());
        for pivot in 0..self.pivots.len() {
            if column[pivot] == M31::ZERO {
                continue;
            }
            if let Some(basis) = &self.pivots[pivot] {
                let scale = column[pivot];
                for index in pivot..column.len() {
                    column[index] = column[index].sub(scale.mul(basis[index]));
                }
                continue;
            }
            let pivot_value = column[pivot];
            let inverse = column[pivot].inv();
            for value in &mut column[pivot..] {
                *value = value.mul(inverse);
            }
            self.pivots[pivot] = Some(column);
            self.rank += 1;
            return Some((pivot, pivot_value));
        }
        None
    }

    fn insert_with_pivot(&mut self, column: Vec<M31>) -> Option<usize> {
        self.insert_with_pivot_value(column).map(|(pivot, _)| pivot)
    }

    fn insert(&mut self, column: Vec<M31>) -> bool {
        self.insert_with_pivot(column).is_some()
    }

    /// Reduce against this frozen echelon without changing its basis.
    fn remainder_existing(&self, mut column: Vec<M31>) -> Vec<M31> {
        debug_assert_eq!(column.len(), self.pivots.len());
        for pivot in 0..column.len() {
            if column[pivot] == M31::ZERO {
                continue;
            }
            let Some(basis) = self.pivots[pivot].as_ref() else {
                continue;
            };
            let scale = column[pivot];
            for index in pivot..column.len() {
                column[index] = column[index].sub(scale.mul(basis[index]));
            }
        }
        column
    }
}

enum CarryReduction {
    Pivot { row: usize, value: M31 },
    Kernel(Vec<M31>),
}

/// Raw-block elimination which carries the joint auxiliary image through
/// every pivot operation and returns it precisely when the raw column lies in
/// the conditioned kernel.
#[derive(Clone)]
struct CarryEchelon {
    pivots: Vec<Option<(Vec<M31>, Vec<M31>)>>,
    rank: usize,
}

impl CarryEchelon {
    fn new(raw_rows: usize) -> Self {
        Self {
            pivots: vec![None; raw_rows],
            rank: 0,
        }
    }

    fn reduce_with_pivot(&mut self, mut raw: Vec<M31>, mut carry: Vec<M31>) -> CarryReduction {
        debug_assert_eq!(raw.len(), self.pivots.len());
        for pivot in 0..raw.len() {
            if raw[pivot] == M31::ZERO {
                continue;
            }
            if let Some((basis_raw, basis_carry)) = &self.pivots[pivot] {
                let scale = raw[pivot];
                for index in pivot..raw.len() {
                    raw[index] = raw[index].sub(scale.mul(basis_raw[index]));
                }
                for (value, basis) in carry.iter_mut().zip(basis_carry) {
                    *value = value.sub(scale.mul(*basis));
                }
                continue;
            }
            let pivot_value = raw[pivot];
            let inverse = raw[pivot].inv();
            for value in &mut raw[pivot..] {
                *value = value.mul(inverse);
            }
            for value in &mut carry {
                *value = value.mul(inverse);
            }
            self.pivots[pivot] = Some((raw, carry));
            self.rank += 1;
            return CarryReduction::Pivot {
                row: pivot,
                value: pivot_value,
            };
        }
        CarryReduction::Kernel(carry)
    }

    fn reduce(&mut self, raw: Vec<M31>, carry: Vec<M31>) -> Option<Vec<M31>> {
        match self.reduce_with_pivot(raw, carry) {
            CarryReduction::Pivot { .. } => None,
            CarryReduction::Kernel(carry) => Some(carry),
        }
    }

    /// Reduce against an already frozen echelon without adding a new pivot.
    /// Returns `None` exactly when `raw` is outside the conditioned span.
    fn quotient_existing(&self, raw: Vec<M31>, carry: Vec<M31>) -> Option<Vec<M31>> {
        let (raw, carry) = self.remainder_existing(raw, carry);
        raw.into_iter()
            .all(|value| value == M31::ZERO)
            .then_some(carry)
    }

    /// Frozen-echelon reduction retaining the exact quotient remainder.
    fn remainder_existing(&self, mut raw: Vec<M31>, mut carry: Vec<M31>) -> (Vec<M31>, Vec<M31>) {
        debug_assert_eq!(raw.len(), self.pivots.len());
        for pivot in 0..raw.len() {
            if raw[pivot] == M31::ZERO {
                continue;
            }
            let Some((basis_raw, basis_carry)) = self.pivots[pivot].as_ref() else {
                continue;
            };
            let scale = raw[pivot];
            for index in pivot..raw.len() {
                raw[index] = raw[index].sub(scale.mul(basis_raw[index]));
            }
            for (value, basis) in carry.iter_mut().zip(basis_carry) {
                *value = value.sub(scale.mul(*basis));
            }
        }
        (raw, carry)
    }
}

#[derive(Clone)]
struct RowPublicMaps {
    layer0_m31: Vec<M31>,
    terminal: [QM31; 3],
    pcs_tail: Vec<QM31>,
}

fn row_public_maps_linear_combination(
    left: &RowPublicMaps,
    left_scale: M31,
    right: &RowPublicMaps,
    right_scale: M31,
) -> RowPublicMaps {
    RowPublicMaps {
        layer0_m31: left
            .layer0_m31
            .iter()
            .zip(&right.layer0_m31)
            .map(|(&left, &right)| left.mul(left_scale).add(right.mul(right_scale)))
            .collect(),
        terminal: core::array::from_fn(|point| {
            left.terminal[point]
                .mul_m31(left_scale)
                .add(right.terminal[point].mul_m31(right_scale))
        }),
        pcs_tail: left
            .pcs_tail
            .iter()
            .zip(&right.pcs_tail)
            .map(|(&left, &right)| left.mul_m31(left_scale).add(right.mul_m31(right_scale)))
            .collect(),
    }
}

/// Presents any physical insertion coordinate in a stable logical ordering:
/// original rows first, followed by one full-QM31 helper-mask row per
/// original row. For a zero slice these are the two physical bit slices. For
/// an affine slice at `c`, the original polynomial is duplicated and the
/// helper row is `(s-c)R = (-c R, (1-c) R)`.
fn canonicalize_extended_row_public_maps(
    physical: &[RowPublicMaps],
    insertion_coordinate: usize,
    affine_slice: Option<M31>,
) -> Vec<RowPublicMaps> {
    debug_assert_eq!(physical.len(), EXTENDED_TRACE_ROWS);
    let mut rows = Vec::with_capacity(EXTENDED_TRACE_ROWS);
    for row in 0..TRACE_ROWS {
        let lower = &physical[embed_extended_trace_row(row, insertion_coordinate, 0)];
        let upper = &physical[embed_extended_trace_row(row, insertion_coordinate, 1)];
        if affine_slice.is_some() {
            rows.push(row_public_maps_linear_combination(
                lower,
                M31::ONE,
                upper,
                M31::ONE,
            ));
        } else {
            rows.push(lower.clone());
        }
    }
    for row in 0..TRACE_ROWS {
        let lower = &physical[embed_extended_trace_row(row, insertion_coordinate, 0)];
        let upper = &physical[embed_extended_trace_row(row, insertion_coordinate, 1)];
        if let Some(c) = affine_slice {
            rows.push(row_public_maps_linear_combination(
                lower,
                M31::ZERO.sub(c),
                upper,
                M31::ONE.sub(c),
            ));
        } else {
            rows.push(upper.clone());
        }
    }
    rows
}

fn sparse_folded_row_value(
    encoder: &CircleEncoder,
    domain_log: u32,
    row: usize,
    dependent: Option<usize>,
    schedule: &StateOnlyTranscriptScheduleResult,
    layer: usize,
    index: usize,
    memo: &mut BTreeMap<(usize, usize), QM31>,
) -> Result<QM31, StateOnlyHidingRankGateError> {
    if let Some(value) = memo.get(&(layer, index)) {
        return Ok(*value);
    }
    let value = if layer == 0 {
        let value = encoder.encode_c1_basis_value(row, index)?;
        let subtract = dependent
            .map(|dependent| encoder.encode_c1_basis_value(dependent, index))
            .transpose()?
            .unwrap_or(M31::ZERO);
        QM31::from_cm31(CM31::from_m31(value.sub(subtract)))
    } else {
        let mut values = [QM31::ZERO; FIBER_SLOTS];
        for (slot, value) in values.iter_mut().enumerate() {
            *value = sparse_folded_row_value(
                encoder,
                domain_log,
                row,
                dependent,
                schedule,
                layer - 1,
                FIBER_SLOTS * index + slot,
                memo,
            )?;
        }
        if layer == 1 {
            aspis_core::circle_fri::normalized_circle_to_line_arity4_at_fiber_for_domain_log(
                values,
                schedule.alpha[0],
                domain_log,
                index,
            )
            .map_err(|_| StateOnlyHidingRankGateError::Encoding)?
        } else {
            normalized_line_arity4_at_fiber_for_domain_log(
                values,
                schedule.alpha[layer - 1],
                domain_log,
                (layer - 1) as u8,
                index,
            )
            .map_err(|_| StateOnlyHidingRankGateError::Encoding)?
        }
    };
    memo.insert((layer, index), value);
    Ok(value)
}

fn row_pcs_tail_sparse(
    encoder: &CircleEncoder,
    domain_log: u32,
    row: usize,
    active: &[bool; TRACE_ROWS],
    inactive_dependent: usize,
    schedule: &StateOnlyTranscriptScheduleResult,
    later_indices: &[Vec<u32>; CANDIDATE_ROUND_COUNT - 1],
    layout: RankLayout,
) -> Result<Vec<QM31>, StateOnlyHidingRankGateError> {
    if row == inactive_dependent {
        let later = later_indices
            .iter()
            .map(|queries| queries.len() * FIBER_SLOTS)
            .sum::<usize>();
        return Ok(vec![
            QM31::ZERO;
            later
                + CANDIDATE_ROUND_COUNT * CANDIDATE_OOD_SAMPLES
                + CANDIDATE_ROUND_COUNT * 7
                + 4
        ]);
    }
    let dependent = (!active[row]).then_some(inactive_dependent);
    let mut message = vec![QM31::ZERO; TRACE_ROWS];
    message[row] = QM31::ONE;
    if let Some(dependent) = dependent {
        message[dependent] = QM31::ZERO.sub(QM31::ONE);
    }
    let points = [
        schedule.prefix.z,
        binary_successor_point(&schedule.prefix.z),
        xor12_point(&schedule.prefix.z),
    ];
    let kappa = schedule.prefix.point_scale;
    let mut relation = StateOnlyIncrementalRelation::new_with_inactive_masks(
        message,
        &points,
        [QM31::ONE, kappa, kappa.square()],
        rank_inactive_masks(layout),
    )?;
    let mut later = Vec::new();
    let mut polynomials = Vec::with_capacity(CANDIDATE_ROUND_COUNT);
    let mut memo = BTreeMap::new();
    for round in 0..CANDIDATE_ROUND_COUNT {
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            if round == 0 {
                let point = schedule.circle_ood_points[sample];
                let value = relation.evaluate_circle_ood(point)?;
                relation.add_circle_ood(point, value, schedule.mu[round][sample])?;
            } else {
                let point = schedule.line_ood_points[round - 1][sample];
                let value = relation.evaluate_line_ood(point)?;
                relation.add_line_ood(point, value, schedule.mu[round][sample])?;
            }
        }
        polynomials.push(relation.polynomial()?);
        relation.fold(schedule.alpha[round])?;
        if round + 1 < CANDIDATE_ROUND_COUNT {
            for &leaf in &later_indices[round] {
                for slot in 0..FIBER_SLOTS {
                    later.push(sparse_folded_row_value(
                        encoder,
                        domain_log,
                        row,
                        dependent,
                        schedule,
                        round + 1,
                        FIBER_SLOTS * leaf as usize + slot,
                        &mut memo,
                    )?);
                }
            }
        }
    }
    let relation = relation.finish()?;
    let mut tail = later;
    for values in relation.ood_values {
        tail.extend_from_slice(&values);
    }
    for polynomial in polynomials {
        tail.extend_from_slice(&polynomial);
    }
    tail.extend_from_slice(&relation.final_coefficients);
    Ok(tail)
}

fn row_pcs_tail(
    encoder: &CircleEncoder,
    domain_log: u32,
    row: usize,
    active: &[bool; TRACE_ROWS],
    inactive_dependent: usize,
    schedule: &StateOnlyTranscriptScheduleResult,
    later_indices: &[Vec<u32>; CANDIDATE_ROUND_COUNT - 1],
    layout: RankLayout,
) -> Result<Vec<QM31>, StateOnlyHidingRankGateError> {
    if domain_log >= 19 {
        return row_pcs_tail_sparse(
            encoder,
            domain_log,
            row,
            active,
            inactive_dependent,
            schedule,
            later_indices,
            layout,
        );
    }
    if row == inactive_dependent {
        // This coordinate is eliminated by the exact inactive-zero sampler.
        // Keeping an explicit zero image makes later per-column dependent
        // changes a simple row-image subtraction.
        let layer0 = later_indices
            .iter()
            .map(|queries| queries.len() * FIBER_SLOTS)
            .sum::<usize>();
        return Ok(vec![
            QM31::ZERO;
            layer0
                + CANDIDATE_ROUND_COUNT * CANDIDATE_OOD_SAMPLES
                + CANDIDATE_ROUND_COUNT * 7
                + 4
        ]);
    }
    let mut message = vec![QM31::ZERO; TRACE_ROWS];
    message[row] = QM31::ONE;
    if !active[row] {
        message[inactive_dependent] = QM31::ZERO.sub(QM31::ONE);
    }
    let mut base = vec![M31::ZERO; TRACE_ROWS];
    base[row] = M31::ONE;
    if !active[row] {
        base[inactive_dependent] = M31::ZERO.sub(M31::ONE);
    }
    let encoded = encoder.encode_c1_message(&base)?;
    let mut codeword = encoded
        .into_iter()
        .map(|value| QM31::from_cm31(CM31::from_m31(value)))
        .collect::<Vec<_>>();
    let points = [
        schedule.prefix.z,
        binary_successor_point(&schedule.prefix.z),
        xor12_point(&schedule.prefix.z),
    ];
    let kappa = schedule.prefix.point_scale;
    let mut relation = StateOnlyIncrementalRelation::new_with_inactive_masks(
        message,
        &points,
        [QM31::ONE, kappa, kappa.square()],
        rank_inactive_masks(layout),
    )?;
    let mut later = Vec::new();
    let mut polynomials = Vec::with_capacity(CANDIDATE_ROUND_COUNT);
    for round in 0..CANDIDATE_ROUND_COUNT {
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            if round == 0 {
                let point = schedule.circle_ood_points[sample];
                let value = relation.evaluate_circle_ood(point)?;
                relation.add_circle_ood(point, value, schedule.mu[round][sample])?;
            } else {
                let point = schedule.line_ood_points[round - 1][sample];
                let value = relation.evaluate_line_ood(point)?;
                relation.add_line_ood(point, value, schedule.mu[round][sample])?;
            }
        }
        polynomials.push(relation.polynomial()?);
        relation.fold(schedule.alpha[round])?;
        codeword = fold_candidate_codeword_round_for_domain_log(
            &codeword,
            schedule.alpha[round],
            round,
            domain_log,
        )?;
        if round + 1 < CANDIDATE_ROUND_COUNT {
            for &query in &later_indices[round] {
                let start = FIBER_SLOTS * query as usize;
                later.extend_from_slice(&codeword[start..start + FIBER_SLOTS]);
            }
        }
    }
    let relation = relation.finish()?;
    let mut tail = later;
    for values in relation.ood_values {
        tail.extend_from_slice(&values);
    }
    for polynomial in polynomials {
        tail.extend_from_slice(&polynomial);
    }
    tail.extend_from_slice(&relation.final_coefficients);
    Ok(tail)
}

/// Complete PCS tail of one *unbalanced* root-zero combined-message row.
///
/// Ordinary mask rows are sampled in the copy-inactive-zero subspace, so the
/// baseline helper above may eliminate an inactive dependent row.  The full-X
/// gamma lane is different: its exact initial relation target is serialized
/// before gamma, hence the initial running claim is the complete relation
/// covector dot this raw row.  No dependent subtraction is valid here.
fn raw_root0_row_pcs_tail_sparse(
    encoder: &CircleEncoder,
    domain_log: u32,
    row: usize,
    schedule: &StateOnlyTranscriptScheduleResult,
    later_indices: &[Vec<u32>; CANDIDATE_ROUND_COUNT - 1],
    layout: RankLayout,
) -> Result<Vec<QM31>, StateOnlyHidingRankGateError> {
    if row >= TRACE_ROWS {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let mut coefficients = vec![QM31::ZERO; TRACE_ROWS];
    coefficients[row] = QM31::ONE;
    let mut weights = initial_relation_weights(schedule, layout)?;
    let mut later = Vec::new();
    let mut ood_values = [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT];
    let mut polynomials = [[QM31::ZERO; 7]; CANDIDATE_ROUND_COUNT];
    let mut memo = BTreeMap::new();

    for round in 0..CANDIDATE_ROUND_COUNT {
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            let mut evaluation =
                WeightAccumulator::empty(STATE_ONLY_LOG_ROWS.saturating_sub(2 * round as u32));
            if round == 0 {
                evaluation
                    .add_circle_tensor(QM31::ONE, schedule.circle_ood_points[sample])
                    .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
                weights
                    .add_circle_tensor(
                        schedule.mu[round][sample],
                        schedule.circle_ood_points[sample],
                    )
                    .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
            } else {
                evaluation
                    .add_line_tensor(QM31::ONE, schedule.line_ood_points[round - 1][sample])
                    .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
                weights
                    .add_line_tensor(
                        schedule.mu[round][sample],
                        schedule.line_ood_points[round - 1][sample],
                    )
                    .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
            }
            ood_values[round][sample] = evaluation.dot(&coefficients);
        }
        let polynomial = polynomial_for_extension(&coefficients, &weights);
        if boundary_sum(&polynomial) != weights.dot(&coefficients) {
            return Err(StateOnlyHidingRankGateError::Relation);
        }
        polynomials[round] = polynomial;
        weights.fold(schedule.alpha[round]);
        coefficients = fold_adjacent_natural_arity4(&coefficients, schedule.alpha[round]);
        if round + 1 < CANDIDATE_ROUND_COUNT {
            for &leaf in &later_indices[round] {
                for slot in 0..FIBER_SLOTS {
                    later.push(sparse_folded_row_value(
                        encoder,
                        domain_log,
                        row,
                        None,
                        schedule,
                        round + 1,
                        FIBER_SLOTS * leaf as usize + slot,
                        &mut memo,
                    )?);
                }
            }
        }
    }

    let mut tail = later;
    for values in ood_values {
        tail.extend_from_slice(&values);
    }
    for polynomial in polynomials {
        tail.extend_from_slice(&polynomial);
    }
    tail.extend_from_slice(&coefficients);
    Ok(tail)
}

/// Independent dense reference for the complete PCS tail of an arbitrary
/// unbalanced root-zero QM31 message.  Unlike the sparse unit-row helper,
/// this path executes the production-shaped C2 encoder and
/// `StateOnlyIncrementalRelation` directly.
fn raw_root0_message_pcs_tail_dense(
    encoder: &CircleEncoder,
    domain_log: u32,
    message: &[QM31],
    schedule: &StateOnlyTranscriptScheduleResult,
    later_indices: &[Vec<u32>; CANDIDATE_ROUND_COUNT - 1],
    layout: RankLayout,
) -> Result<Vec<QM31>, StateOnlyHidingRankGateError> {
    if message.len() != TRACE_ROWS {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let mut codeword = encoder.encode_c2_message(message)?;
    let points = [
        schedule.prefix.z,
        binary_successor_point(&schedule.prefix.z),
        xor12_point(&schedule.prefix.z),
    ];
    let kappa = schedule.prefix.point_scale;
    let inactive_masks = rank_inactive_masks(layout);
    let inactive_claim =
        message
            .iter()
            .copied()
            .enumerate()
            .fold(QM31::ZERO, |sum, (row, value)| {
                if inactive_masks[row >> 4] & (1 << (row & 15)) == 0 {
                    sum
                } else {
                    sum.add(value)
                }
            });
    let mut relation = StateOnlyIncrementalRelation::new_with_inactive_masks_and_claim(
        message.to_vec(),
        &points,
        [QM31::ONE, kappa, kappa.square()],
        inactive_masks,
        inactive_claim,
    )?;
    let mut later = Vec::new();
    let mut polynomials = Vec::with_capacity(CANDIDATE_ROUND_COUNT);
    for round in 0..CANDIDATE_ROUND_COUNT {
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            if round == 0 {
                let point = schedule.circle_ood_points[sample];
                let value = relation.evaluate_circle_ood(point)?;
                relation.add_circle_ood(point, value, schedule.mu[round][sample])?;
            } else {
                let point = schedule.line_ood_points[round - 1][sample];
                let value = relation.evaluate_line_ood(point)?;
                relation.add_line_ood(point, value, schedule.mu[round][sample])?;
            }
        }
        polynomials.push(relation.polynomial()?);
        relation.fold(schedule.alpha[round])?;
        codeword = fold_candidate_codeword_round_for_domain_log(
            &codeword,
            schedule.alpha[round],
            round,
            domain_log,
        )?;
        if round + 1 < CANDIDATE_ROUND_COUNT {
            for &query in &later_indices[round] {
                let start = FIBER_SLOTS * query as usize;
                later.extend_from_slice(&codeword[start..start + FIBER_SLOTS]);
            }
        }
    }
    let relation = relation.finish()?;
    let mut tail = later;
    for values in relation.ood_values {
        tail.extend_from_slice(&values);
    }
    for polynomial in polynomials {
        tail.extend_from_slice(&polynomial);
    }
    tail.extend_from_slice(&relation.final_coefficients);
    Ok(tail)
}

fn fold_adjacent_natural_arity8(values: &[QM31], alpha: QM31) -> Vec<QM31> {
    let powers: [QM31; 8] = core::array::from_fn(|exponent| alpha.pow(exponent as u64));
    values
        .chunks_exact(8)
        .map(|chunk| {
            chunk
                .iter()
                .zip(powers)
                .fold(QM31::ZERO, |sum, (value, power)| sum.add(value.mul(power)))
        })
        .collect()
}

fn polynomial_for_extension_arity8(
    coefficients: &[QM31],
    weights: &WeightAccumulator,
) -> [QM31; HYBRID_ARITY8_RELATION_COEFFICIENTS] {
    let mut output = [QM31::ZERO; HYBRID_ARITY8_RELATION_COEFFICIENTS];
    let inverse_eight = M31(8).inv();
    for (chunk_index, chunk) in coefficients.chunks_exact(8).enumerate() {
        let base = 8 * chunk_index;
        let chunk_weights: [QM31; 8] =
            core::array::from_fn(|slot| weights.weight_at((base + slot) as u32));
        for (a_degree, value) in chunk.iter().enumerate() {
            for b_degree in 0..8 {
                let dual = if b_degree == 0 {
                    chunk_weights[0]
                } else {
                    chunk_weights[8 - b_degree]
                };
                output[a_degree + b_degree] =
                    output[a_degree + b_degree].add(value.mul(dual).mul_m31(inverse_eight));
            }
        }
    }
    output
}

fn boundary_sum_arity8(polynomial: &[QM31; HYBRID_ARITY8_RELATION_COEFFICIENTS]) -> QM31 {
    polynomial[0].add(polynomial[8]).mul_m31(M31(8))
}

fn evaluate_arity8(polynomial: &[QM31; HYBRID_ARITY8_RELATION_COEFFICIENTS], point: QM31) -> QM31 {
    polynomial
        .iter()
        .rev()
        .fold(QM31::ZERO, |accumulator, coefficient| {
            accumulator.mul(point).add(*coefficient)
        })
}

fn fold_line_codeword_arity8_for_probe(
    evaluations: &[QM31],
    alpha: QM31,
    domain_log: u32,
) -> Result<Vec<QM31>, StateOnlyHidingRankGateError> {
    let alpha4 = alpha.pow(4);
    evaluations
        .chunks_exact(8)
        .enumerate()
        .map(|(fiber, chunk)| {
            let left = normalized_line_arity4_at_fiber_for_domain_log(
                chunk[..4].try_into().unwrap(),
                alpha,
                domain_log,
                1,
                2 * fiber,
            )?;
            let right = normalized_line_arity4_at_fiber_for_domain_log(
                chunk[4..].try_into().unwrap(),
                alpha,
                domain_log,
                1,
                2 * fiber + 1,
            )?;
            let x = line_domain_x_for_circle(domain_log, 2, 2 * fiber)?;
            if x == M31::ZERO {
                return Err(aspis_core::circle_fri::CircleFriError::ZeroDenominator(
                    aspis_core::circle_fri::FoldDenominator::LineFirstPairX,
                ));
            }
            Ok(left
                .add(right)
                .half()
                .add(alpha4.mul(left.sub(right).mul_m31(x.double().inv()))))
        })
        .collect::<Result<Vec<_>, _>>()
        .map_err(|_| StateOnlyHidingRankGateError::Encoding)
}

fn initial_relation_weights(
    schedule: &StateOnlyTranscriptScheduleResult,
    layout: RankLayout,
) -> Result<WeightAccumulator, StateOnlyHidingRankGateError> {
    let points = [
        schedule.prefix.z,
        binary_successor_point(&schedule.prefix.z),
        xor12_point(&schedule.prefix.z),
    ];
    let kappa = schedule.prefix.point_scale;
    let mut weights = WeightAccumulator::empty(STATE_ONLY_LOG_ROWS);
    for (point, scale) in points.into_iter().zip([QM31::ONE, kappa, kappa.square()]) {
        weights
            .add_multilinear(scale, point.to_vec())
            .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
    }
    weights
        .add_grouped_64x16_binary_masks(rank_inactive_masks(layout))
        .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
    Ok(weights)
}

/// Complete linear PCS tail for the hybrid schedule: the existing arity-4
/// circle fold, followed by one arity-8 line fold, ending at 32 explicit
/// coefficients. The schedule reuses a fixed transcript's challenges only as
/// a structural A/B; a production transcript tag/order is intentionally not
/// defined here.
fn row_pcs_tail_hybrid_arity8(
    encoder: &CircleEncoder,
    domain_log: u32,
    row: usize,
    active: &[bool; TRACE_ROWS],
    inactive_dependent: usize,
    schedule: &StateOnlyTranscriptScheduleResult,
    later_indices: &[u32],
    layout: RankLayout,
) -> Result<Vec<QM31>, StateOnlyHidingRankGateError> {
    if row == inactive_dependent {
        return Ok(vec![
            QM31::ZERO;
            later_indices.len() * 8
                + 2 * CANDIDATE_OOD_SAMPLES
                + 7
                + HYBRID_ARITY8_RELATION_COEFFICIENTS
                + 32
        ]);
    }
    let mut coefficients = vec![QM31::ZERO; TRACE_ROWS];
    coefficients[row] = QM31::ONE;
    if !active[row] {
        coefficients[inactive_dependent] = QM31::ZERO.sub(QM31::ONE);
    }
    let mut base = vec![M31::ZERO; TRACE_ROWS];
    base[row] = M31::ONE;
    if !active[row] {
        base[inactive_dependent] = M31::ZERO.sub(M31::ONE);
    }
    let encoded = encoder.encode_c1_message(&base)?;
    let mut codeword = encoded
        .into_iter()
        .map(|value| QM31::from_cm31(CM31::from_m31(value)))
        .collect::<Vec<_>>();
    let mut weights = initial_relation_weights(schedule, layout)?;
    let mut running_claim = weights.dot(&coefficients);
    let mut ood_values = [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; 2];

    for sample in 0..CANDIDATE_OOD_SAMPLES {
        let point = schedule.circle_ood_points[sample];
        let mut evaluation = WeightAccumulator::empty(STATE_ONLY_LOG_ROWS);
        evaluation
            .add_circle_tensor(QM31::ONE, point)
            .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
        let value = evaluation.dot(&coefficients);
        ood_values[0][sample] = value;
        weights
            .add_circle_tensor(schedule.mu[0][sample], point)
            .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
        running_claim = running_claim.add(schedule.mu[0][sample].mul(value));
    }
    let polynomial0 = polynomial_for_extension(&coefficients, &weights);
    if boundary_sum(&polynomial0) != running_claim {
        return Err(StateOnlyHidingRankGateError::Relation);
    }
    running_claim = evaluate_relation(&polynomial0, schedule.alpha[0]);
    weights.fold(schedule.alpha[0]);
    coefficients = fold_adjacent_natural_arity4(&coefficients, schedule.alpha[0]);
    if weights.dot(&coefficients) != running_claim {
        return Err(StateOnlyHidingRankGateError::Relation);
    }
    codeword =
        fold_candidate_codeword_round_for_domain_log(&codeword, schedule.alpha[0], 0, domain_log)?;

    let mut later = Vec::with_capacity(later_indices.len() * 8);
    for &query in later_indices {
        let start = 8 * query as usize;
        later.extend_from_slice(&codeword[start..start + 8]);
    }

    for sample in 0..CANDIDATE_OOD_SAMPLES {
        let point = schedule.line_ood_points[0][sample];
        let mut evaluation = WeightAccumulator::empty(STATE_ONLY_LOG_ROWS - 2);
        evaluation
            .add_line_tensor(QM31::ONE, point)
            .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
        let value = evaluation.dot(&coefficients);
        ood_values[1][sample] = value;
        weights
            .add_line_tensor(schedule.mu[1][sample], point)
            .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
        running_claim = running_claim.add(schedule.mu[1][sample].mul(value));
    }
    let polynomial1 = polynomial_for_extension_arity8(&coefficients, &weights);
    if boundary_sum_arity8(&polynomial1) != running_claim {
        return Err(StateOnlyHidingRankGateError::Relation);
    }
    running_claim = evaluate_arity8(&polynomial1, schedule.alpha[1]);
    weights.fold_arity8_materialized_for_probe(schedule.alpha[1]);
    coefficients = fold_adjacent_natural_arity8(&coefficients, schedule.alpha[1]);
    if coefficients.len() != 32 || weights.dot(&coefficients) != running_claim {
        return Err(StateOnlyHidingRankGateError::Relation);
    }
    let final_codeword =
        fold_line_codeword_arity8_for_probe(&codeword, schedule.alpha[1], domain_log)?;
    if final_codeword.len() != (1usize << domain_log) / 32 {
        return Err(StateOnlyHidingRankGateError::Shape);
    }

    let mut tail = later;
    for values in ood_values {
        tail.extend_from_slice(&values);
    }
    tail.extend_from_slice(&polynomial0);
    tail.extend_from_slice(&polynomial1);
    tail.extend_from_slice(&coefficients);
    Ok(tail)
}

fn row_public_maps(
    encoder: &CircleEncoder,
    domain_log: u32,
    schedule: &StateOnlyTranscriptScheduleResult,
    pcs_schedule: PcsSchedule,
    layout: RankLayout,
) -> Result<Vec<RowPublicMaps>, StateOnlyHidingRankGateError> {
    let queries = schedule.queries[..schedule.query_count].to_vec();
    let indices =
        derive_circle_line_query_indices_for_count(&queries, encoder.codeword_len() / FIBER_SLOTS)
            .map_err(|_| StateOnlyHidingRankGateError::Shape)?;
    let later_indices = indices.later;
    let mut hybrid_later_indices = indices
        .layer0
        .iter()
        .map(|query| query >> 3)
        .collect::<Vec<_>>();
    hybrid_later_indices.dedup();
    let terminal_points = [
        schedule.prefix.z,
        binary_successor_point(&schedule.prefix.z),
        xor12_point(&schedule.prefix.z),
    ];
    let mut active = [false; TRACE_ROWS];
    for &row in rank_active_rows(layout) {
        active[usize::from(row)] = true;
    }
    let inactive_dependent = (0..TRACE_ROWS)
        .find(|row| !active[*row])
        .ok_or(StateOnlyHidingRankGateError::Layout)?;
    let mut rows = Vec::with_capacity(TRACE_ROWS);
    for row in 0..TRACE_ROWS {
        let mut layer0_m31 = Vec::with_capacity(indices.layer0.len() * FIBER_SLOTS);
        if domain_log >= 19 {
            for &query in &indices.layer0 {
                for slot in 0..FIBER_SLOTS {
                    layer0_m31.push(
                        encoder.encode_c1_basis_value(row, FIBER_SLOTS * query as usize + slot)?,
                    );
                }
            }
        } else {
            let mut message = vec![M31::ZERO; TRACE_ROWS];
            message[row] = M31::ONE;
            let codeword = encoder.encode_c1_message(&message)?;
            for &query in &indices.layer0 {
                let start = FIBER_SLOTS * query as usize;
                layer0_m31.extend_from_slice(&codeword[start..start + FIBER_SLOTS]);
            }
        }
        rows.push(RowPublicMaps {
            layer0_m31,
            terminal: core::array::from_fn(|point| eq_weight(&terminal_points[point], row)),
            pcs_tail: match pcs_schedule {
                PcsSchedule::Arity4x4 => row_pcs_tail(
                    encoder,
                    domain_log,
                    row,
                    &active,
                    inactive_dependent,
                    schedule,
                    &later_indices,
                    layout,
                )?,
                PcsSchedule::Arity4ThenArity8 => row_pcs_tail_hybrid_arity8(
                    encoder,
                    domain_log,
                    row,
                    &active,
                    inactive_dependent,
                    schedule,
                    &hybrid_later_indices,
                    layout,
                )?,
                PcsSchedule::RootMessage | PcsSchedule::RootMessageV6Log20 => {
                    let mut message = vec![QM31::ZERO; TRACE_ROWS];
                    if row != inactive_dependent {
                        message[row] = QM31::ONE;
                        if !active[row] {
                            message[inactive_dependent] = QM31::ZERO.sub(QM31::ONE);
                        }
                    }
                    message
                }
            },
        });
    }
    Ok(rows)
}

fn first_later_weights(
    schedule: &StateOnlyTranscriptScheduleResult,
    layout: RankLayout,
) -> Result<WeightAccumulator, StateOnlyHidingRankGateError> {
    let points = [
        schedule.prefix.z,
        binary_successor_point(&schedule.prefix.z),
        xor12_point(&schedule.prefix.z),
    ];
    let kappa = schedule.prefix.point_scale;
    let mut weights = WeightAccumulator::empty(STATE_ONLY_LOG_ROWS);
    for (point, scale) in points.into_iter().zip([QM31::ONE, kappa, kappa.square()]) {
        weights
            .add_multilinear(scale, point.to_vec())
            .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
    }
    weights
        .add_grouped_64x16_binary_masks(rank_inactive_masks(layout))
        .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
    for sample in 0..CANDIDATE_OOD_SAMPLES {
        weights
            .add_circle_tensor(schedule.mu[0][sample], schedule.circle_ood_points[sample])
            .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
    }
    weights.fold(schedule.alpha[0]);
    Ok(weights)
}

/// Complete public tail generated by adding one coefficient to the freshly
/// committed first later word. Round-zero OOD and polynomial coordinates are
/// explicitly zero: they were serialized before this root exists.
fn first_later_coefficient_tail(
    encoder: &CircleEncoder,
    domain_log: u32,
    coefficient: usize,
    schedule: &StateOnlyTranscriptScheduleResult,
    later_indices: &[Vec<u32>; CANDIDATE_ROUND_COUNT - 1],
    layout: RankLayout,
) -> Result<Vec<QM31>, StateOnlyHidingRankGateError> {
    if coefficient >= TRACE_ROWS / FIBER_SLOTS {
        return Err(StateOnlyHidingRankGateError::Shape);
    }

    if domain_log >= 19 {
        let mut weights = first_later_weights(schedule, layout)?;
        let mut coefficients = vec![QM31::ZERO; TRACE_ROWS / FIBER_SLOTS];
        coefficients[coefficient] = QM31::ONE;
        let mut running_claim = weights.dot(&coefficients);
        let mut later = Vec::new();
        let mut ood_values = [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT];
        let mut polynomials = [[QM31::ZERO; 7]; CANDIDATE_ROUND_COUNT];
        let mut memo = BTreeMap::new();
        for round in 1..CANDIDATE_ROUND_COUNT {
            for &leaf in &later_indices[round - 1] {
                for slot in 0..FIBER_SLOTS {
                    later.push(sparse_folded_row_value(
                        encoder,
                        domain_log,
                        FIBER_SLOTS * coefficient,
                        None,
                        schedule,
                        round,
                        FIBER_SLOTS * leaf as usize + slot,
                        &mut memo,
                    )?);
                }
            }
            for sample in 0..CANDIDATE_OOD_SAMPLES {
                let mut evaluation =
                    WeightAccumulator::empty(STATE_ONLY_LOG_ROWS - 2 * round as u32);
                evaluation
                    .add_line_tensor(QM31::ONE, schedule.line_ood_points[round - 1][sample])
                    .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
                let value = evaluation.dot(&coefficients);
                ood_values[round][sample] = value;
                weights
                    .add_line_tensor(
                        schedule.mu[round][sample],
                        schedule.line_ood_points[round - 1][sample],
                    )
                    .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
                running_claim = running_claim.add(schedule.mu[round][sample].mul(value));
            }
            let polynomial = polynomial_for_extension(&coefficients, &weights);
            if boundary_sum(&polynomial) != running_claim {
                return Err(StateOnlyHidingRankGateError::Relation);
            }
            polynomials[round] = polynomial;
            running_claim = evaluate_relation(&polynomial, schedule.alpha[round]);
            weights.fold(schedule.alpha[round]);
            coefficients = fold_adjacent_natural_arity4(&coefficients, schedule.alpha[round]);
            if weights.dot(&coefficients) != running_claim {
                return Err(StateOnlyHidingRankGateError::Relation);
            }
        }
        let mut tail = later;
        for values in ood_values {
            tail.extend_from_slice(&values);
        }
        for polynomial in polynomials {
            tail.extend_from_slice(&polynomial);
        }
        tail.extend_from_slice(&coefficients);
        return Ok(tail);
    }

    // A slot-zero preimage folds to exactly the requested first-line natural
    // coefficient, while using the real circle encoder and normalization.
    let mut preimage = vec![QM31::ZERO; TRACE_ROWS];
    preimage[FIBER_SLOTS * coefficient] = QM31::ONE;
    let encoded = encoder.encode_c2_message(&preimage)?;
    let mut codeword =
        fold_candidate_codeword_round_for_domain_log(&encoded, schedule.alpha[0], 0, domain_log)?;

    let mut later = Vec::new();
    for round in 1..CANDIDATE_ROUND_COUNT {
        for &query in &later_indices[round - 1] {
            let start = FIBER_SLOTS * query as usize;
            later.extend_from_slice(&codeword[start..start + FIBER_SLOTS]);
        }
        codeword = fold_candidate_codeword_round_for_domain_log(
            &codeword,
            schedule.alpha[round],
            round,
            domain_log,
        )?;
    }

    let mut weights = first_later_weights(schedule, layout)?;
    let mut coefficients = vec![QM31::ZERO; TRACE_ROWS / FIBER_SLOTS];
    coefficients[coefficient] = QM31::ONE;
    let mut running_claim = weights.dot(&coefficients);
    let mut ood_values = [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT];
    let mut polynomials = [[QM31::ZERO; 7]; CANDIDATE_ROUND_COUNT];
    for round in 1..CANDIDATE_ROUND_COUNT {
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            let mut evaluation = WeightAccumulator::empty(STATE_ONLY_LOG_ROWS - 2 * round as u32);
            evaluation
                .add_line_tensor(QM31::ONE, schedule.line_ood_points[round - 1][sample])
                .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
            let value = evaluation.dot(&coefficients);
            ood_values[round][sample] = value;
            weights
                .add_line_tensor(
                    schedule.mu[round][sample],
                    schedule.line_ood_points[round - 1][sample],
                )
                .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
            running_claim = running_claim.add(schedule.mu[round][sample].mul(value));
        }
        let polynomial = polynomial_for_extension(&coefficients, &weights);
        if boundary_sum(&polynomial) != running_claim {
            return Err(StateOnlyHidingRankGateError::Relation);
        }
        polynomials[round] = polynomial;
        running_claim = evaluate_relation(&polynomial, schedule.alpha[round]);
        weights.fold(schedule.alpha[round]);
        coefficients = fold_adjacent_natural_arity4(&coefficients, schedule.alpha[round]);
        if weights.dot(&coefficients) != running_claim {
            return Err(StateOnlyHidingRankGateError::Relation);
        }
    }

    let mut tail = later;
    for values in ood_values {
        tail.extend_from_slice(&values);
    }
    for polynomial in polynomials {
        tail.extend_from_slice(&polynomial);
    }
    tail.extend_from_slice(&coefficients);
    Ok(tail)
}

fn first_later_pcs_image(tail: &[QM31], scale: QM31, h_raw_qm31: usize) -> Vec<M31> {
    let mut image = vec![M31::ZERO; 4 * h_raw_qm31];
    image.extend_from_slice(&scaled_qm31_difference(tail, None, scale));
    image
}

/// Evaluate one natural first-line coefficient at the exact root-one scalar
/// positions selected by the production q-query schedule.  This deliberately
/// goes through the real circle C2 encoder and the normalized circle-to-line
/// arity-four fold; a synthetic Vandermonde is not accepted by the gate.
fn first_later_coefficient_query_values(
    encoder: &CircleEncoder,
    domain_log: u32,
    coefficient: usize,
    schedule: &StateOnlyTranscriptScheduleResult,
    queries: &[u32],
) -> Result<Vec<QM31>, StateOnlyHidingRankGateError> {
    if coefficient >= TRACE_ROWS / FIBER_SLOTS {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    if domain_log >= 19 {
        let mut memo = BTreeMap::new();
        return queries
            .iter()
            .map(|&query| {
                sparse_folded_row_value(
                    encoder,
                    domain_log,
                    FIBER_SLOTS * coefficient,
                    None,
                    schedule,
                    1,
                    query as usize,
                    &mut memo,
                )
            })
            .collect();
    }
    let mut preimage = vec![QM31::ZERO; TRACE_ROWS];
    preimage[FIBER_SLOTS * coefficient] = QM31::ONE;
    let encoded = encoder.encode_c2_message(&preimage)?;
    let codeword =
        fold_candidate_codeword_round_for_domain_log(&encoded, schedule.alpha[0], 0, domain_log)?;
    queries
        .iter()
        .map(|&query| {
            codeword
                .get(query as usize)
                .copied()
                .ok_or(StateOnlyHidingRankGateError::Shape)
        })
        .collect()
}

/// Four exact root-zero circle-C2 symbols for one slot-zero natural-line
/// coefficient at every root-one query fiber.  A unit QM31 message entry has
/// the same M31 encoding matrix as `encode_c1_basis_value`; tower-coordinate
/// expansion is performed later by `qm31_column_rank`.
fn first_layer0_coefficient_query_fibers(
    encoder: &CircleEncoder,
    coefficient: usize,
    queries: &[u32],
) -> Result<Vec<QM31>, StateOnlyHidingRankGateError> {
    if coefficient >= TRACE_ROWS / FIBER_SLOTS {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let row = FIBER_SLOTS * coefficient;
    let mut values = Vec::with_capacity(FIBER_SLOTS * queries.len());
    for &query in queries {
        for slot in 0..FIBER_SLOTS {
            let encoded =
                encoder.encode_c1_basis_value(row, FIBER_SLOTS * query as usize + slot)?;
            values.push(QM31::from_cm31(CM31::from_m31(encoded)));
        }
    }
    Ok(values)
}

/// Ordinary-polynomial expansions of the natural line tensor basis
/// `B_i(x)=prod_{b in bits(i)} T_{2^b}(x)`.  The matrix is triangular with a
/// nonzero diagonal, so it gives an exact generated change of basis between
/// ordinary monomials and the verifier's natural tensor coefficients.
fn natural_line_basis_polynomials(size: usize) -> Vec<Vec<M31>> {
    let log_size = usize::BITS as usize - (size - 1).leading_zeros() as usize;
    let mut factors = Vec::with_capacity(log_size);
    factors.push(vec![M31::ZERO, M31::ONE]);
    for bit in 1..log_size {
        let previous = &factors[bit - 1];
        let mut squared = vec![M31::ZERO; 2 * previous.len() - 1];
        for (left, &a) in previous.iter().enumerate() {
            for (right, &b) in previous.iter().enumerate() {
                squared[left + right] = squared[left + right].add(a.mul(b));
            }
        }
        for value in &mut squared {
            *value = value.double();
        }
        squared[0] = squared[0].sub(M31::ONE);
        factors.push(squared);
    }

    let mut basis = Vec::with_capacity(size);
    basis.push(vec![M31::ONE]);
    for index in 1..size {
        let bit = index.trailing_zeros() as usize;
        let prefix = &basis[index ^ (1usize << bit)];
        let factor = &factors[bit];
        let mut polynomial = vec![M31::ZERO; prefix.len() + factor.len() - 1];
        for (left, &a) in prefix.iter().enumerate() {
            for (right, &b) in factor.iter().enumerate() {
                polynomial[left + right] = polynomial[left + right].add(a.mul(b));
            }
        }
        basis.push(polynomial);
    }
    basis
}

fn ordinary_monomials_in_natural_line_basis(size: usize) -> Vec<Vec<M31>> {
    let basis = natural_line_basis_polynomials(size);
    (0..size)
        .map(|degree| {
            let mut residual = vec![M31::ZERO; size];
            residual[degree] = M31::ONE;
            let mut coefficients = vec![M31::ZERO; size];
            for pivot in (0..=degree).rev() {
                let diagonal = basis[pivot][pivot];
                let scale = residual[pivot].mul(diagonal.inv());
                coefficients[pivot] = scale;
                for (monomial, &value) in basis[pivot].iter().enumerate() {
                    residual[monomial] = residual[monomial].sub(scale.mul(value));
                }
            }
            debug_assert!(residual.iter().all(|value| *value == M31::ZERO));
            coefficients
        })
        .collect()
}

/// Exact algebraic certificate for the target-free profile-21 switch carry.
///
/// The carried old-view message is the full natural line space `P_<19`.
/// Sixteen distinct root-one evaluations have rank 16.  Appending natural
/// coefficient 18 has rank 17 for every accepted q tuple: if
/// `g(X)=prod_i (X-x_i)`, then `X^2 g(X)` vanishes at all queries and has a
/// nonzero natural coefficient 18 because the natural-to-monomial matrix is
/// triangular with nonzero diagonal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Profile21HighSwitchCarryCertificate {
    pub query_count: usize,
    pub distinct_abscissae: bool,
    pub evaluation_plus_leading_rank_qm31: usize,
    pub vanishing_witness_natural_coefficient_18: u32,
}

pub fn profile21_high_switch_carry_certificate(
    queries: &[u32],
) -> Result<Profile21HighSwitchCarryCertificate, StateOnlyHidingRankGateError> {
    const QUERY_COUNT: usize = 16;
    const MESSAGE: usize = QUERY_COUNT + 3;
    const HIGH: usize = MESSAGE - 1;
    if queries.len() != QUERY_COUNT {
        return Err(StateOnlyHidingRankGateError::Shape);
    }

    let abscissae = queries
        .iter()
        .map(|&query| {
            line_domain_x_for_circle(STATE_ONLY_LOG_ROWS + 9, 1, query as usize)
                .map_err(|_| StateOnlyHidingRankGateError::Encoding)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut distinct = abscissae.iter().map(|value| value.0).collect::<Vec<_>>();
    distinct.sort_unstable();
    distinct.dedup();
    let distinct_abscissae = distinct.len() == QUERY_COUNT;
    if !distinct_abscissae {
        return Err(StateOnlyHidingRankGateError::Shape);
    }

    let natural = natural_line_basis_polynomials(MESSAGE);
    let evaluate = |polynomial: &[M31], point: M31| {
        polynomial
            .iter()
            .rev()
            .fold(M31::ZERO, |value, coefficient| {
                value.mul(point).add(*coefficient)
            })
    };
    let mut evaluation_plus_leading = ColumnEchelon::new(QUERY_COUNT + 1);
    for (coefficient, polynomial) in natural.iter().enumerate() {
        let mut column = abscissae
            .iter()
            .map(|&point| evaluate(polynomial, point))
            .collect::<Vec<_>>();
        column.push(if coefficient == HIGH {
            M31::ONE
        } else {
            M31::ZERO
        });
        evaluation_plus_leading.insert(column);
    }

    let mut vanishing = vec![M31::ONE];
    for &point in &abscissae {
        let mut next = vec![M31::ZERO; vanishing.len() + 1];
        for (degree, &coefficient) in vanishing.iter().enumerate() {
            next[degree] = next[degree].sub(coefficient.mul(point));
            next[degree + 1] = next[degree + 1].add(coefficient);
        }
        vanishing = next;
    }
    let mut x2_vanishing = vec![M31::ZERO; MESSAGE];
    x2_vanishing[2..].copy_from_slice(&vanishing);
    debug_assert!(abscissae
        .iter()
        .all(|&point| evaluate(&x2_vanishing, point) == M31::ZERO));
    let monomial_to_natural = ordinary_monomials_in_natural_line_basis(MESSAGE);
    let witness_high = x2_vanishing
        .iter()
        .enumerate()
        .fold(M31::ZERO, |sum, (degree, coefficient)| {
            sum.add(coefficient.mul(monomial_to_natural[degree][HIGH]))
        });
    if evaluation_plus_leading.rank != QUERY_COUNT + 1 || witness_high == M31::ZERO {
        return Err(StateOnlyHidingRankGateError::Layout);
    }

    Ok(Profile21HighSwitchCarryCertificate {
        query_count: QUERY_COUNT,
        distinct_abscissae,
        evaluation_plus_leading_rank_qm31: evaluation_plus_leading.rank,
        vanishing_witness_natural_coefficient_18: witness_high.0,
    })
}

fn combine_natural_qm31_columns(
    natural_columns: &[Vec<QM31>],
    coefficients: &[M31],
) -> Result<Vec<QM31>, StateOnlyHidingRankGateError> {
    let rows = natural_columns
        .first()
        .map(Vec::len)
        .ok_or(StateOnlyHidingRankGateError::Shape)?;
    if coefficients.len() != natural_columns.len()
        || natural_columns.iter().any(|column| column.len() != rows)
    {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let mut combined = vec![QM31::ZERO; rows];
    for (column, &scale) in natural_columns.iter().zip(coefficients) {
        if scale == M31::ZERO {
            continue;
        }
        for (output, &value) in combined.iter_mut().zip(column) {
            *output = output.add(value.mul_m31(scale));
        }
    }
    Ok(combined)
}

fn natural_line_linear_form(weights: &WeightAccumulator, coefficients: &[M31]) -> QM31 {
    coefficients
        .iter()
        .enumerate()
        .filter(|(_, coefficient)| **coefficient != M31::ZERO)
        .fold(QM31::ZERO, |sum, (index, coefficient)| {
            sum.add(weights.weight_at(index as u32).mul_m31(*coefficient))
        })
}

/// Rank of a K-linear column map, computed through its exact four-coordinate
/// M31 representation.  Every K dimension must expand to four M31 pivots.
fn qm31_column_rank(columns: &[Vec<QM31>], rows: usize) -> usize {
    let mut rank = ColumnEchelon::new(4 * rows);
    for column in columns {
        debug_assert_eq!(column.len(), rows);
        for coordinate in 0..4 {
            let basis = state_only_mask_tower_basis(coordinate);
            let mut expanded = Vec::with_capacity(4 * rows);
            append_qm31_coordinates(
                &mut expanded,
                column.iter().copied().map(|value| value.mul(basis)),
            );
            rank.insert(expanded);
        }
    }
    debug_assert_eq!(rank.rank % 4, 0);
    rank.rank / 4
}

fn radix4_frontier_node_count(mut current: Vec<u32>, mut leaf_count: usize) -> usize {
    current.sort_unstable();
    current.dedup();
    let mut frontier = 0usize;
    while leaf_count > 1 {
        if leaf_count == 2 {
            frontier += usize::from(current.len() == 1);
            break;
        }
        let mut next = Vec::new();
        let mut position = 0usize;
        while position < current.len() {
            let parent = current[position] >> 2;
            let mut present = 0u8;
            while position < current.len() && current[position] >> 2 == parent {
                present |= 1 << (current[position] & 3);
                position += 1;
            }
            frontier += 4 - present.count_ones() as usize;
            next.push(parent);
        }
        current = next;
        leaf_count >>= 2;
    }
    frontier
}

const EXTENDED_LOG_ROWS: u32 = STATE_ONLY_LOG_ROWS + 1;
const EXTENDED_TRACE_ROWS: usize = 1 << EXTENDED_LOG_ROWS;

fn extended_point(
    point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
) -> [QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS + 1] {
    extended_point_at(point, 0, QM31::ZERO)
}

/// Inserts one coordinate into the natural MSB-first multilinear ordering.
/// `insertion_coordinate == 0` is the most-significant coordinate and
/// `insertion_coordinate == STATE_ONLY_HIDING_SUMCHECK_ROUNDS` is the least.
fn extended_point_at(
    point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
    insertion_coordinate: usize,
    inserted_value: QM31,
) -> [QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS + 1] {
    debug_assert!(insertion_coordinate <= STATE_ONLY_HIDING_SUMCHECK_ROUNDS);
    core::array::from_fn(|coordinate| {
        if coordinate < insertion_coordinate {
            point[coordinate]
        } else if coordinate == insertion_coordinate {
            inserted_value
        } else {
            point[coordinate - 1]
        }
    })
}

/// Embeds a ten-bit natural-order trace row into an eleven-bit row by
/// inserting `inserted_bit` at `insertion_coordinate` (MSB-first).
fn embed_extended_trace_row(row: usize, insertion_coordinate: usize, inserted_bit: usize) -> usize {
    debug_assert!(row < TRACE_ROWS);
    debug_assert!(insertion_coordinate <= STATE_ONLY_HIDING_SUMCHECK_ROUNDS);
    debug_assert!(inserted_bit <= 1);
    let low_bits = STATE_ONLY_HIDING_SUMCHECK_ROUNDS - insertion_coordinate;
    let low_mask = (1usize << low_bits).wrapping_sub(1);
    ((row >> low_bits) << (low_bits + 1)) | (inserted_bit << low_bits) | (row & low_mask)
}

fn eq_weight_slice(point: &[QM31], row: usize) -> QM31 {
    point
        .iter()
        .enumerate()
        .fold(QM31::ONE, |weight, (coordinate, value)| {
            let bit = (row >> (point.len() - 1 - coordinate)) & 1;
            weight.mul(if bit == 0 {
                QM31::ONE.sub(*value)
            } else {
                *value
            })
        })
}

fn extended_initial_weights(
    schedule: &StateOnlyTranscriptScheduleResult,
    layout: RankLayout,
) -> Result<WeightAccumulator, StateOnlyHidingRankGateError> {
    extended_initial_weights_at(schedule, layout, 0, QM31::ZERO)
}

fn extended_initial_weights_at(
    schedule: &StateOnlyTranscriptScheduleResult,
    layout: RankLayout,
    insertion_coordinate: usize,
    inserted_value: QM31,
) -> Result<WeightAccumulator, StateOnlyHidingRankGateError> {
    if insertion_coordinate > STATE_ONLY_HIDING_SUMCHECK_ROUNDS {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let points = [
        extended_point_at(&schedule.prefix.z, insertion_coordinate, inserted_value),
        extended_point_at(
            &binary_successor_point(&schedule.prefix.z),
            insertion_coordinate,
            inserted_value,
        ),
        extended_point_at(
            &xor12_point(&schedule.prefix.z),
            insertion_coordinate,
            inserted_value,
        ),
    ];
    let kappa = schedule.prefix.point_scale;
    let mut weights = WeightAccumulator::empty(EXTENDED_LOG_ROWS);
    for (point, scale) in points.into_iter().zip([QM31::ONE, kappa, kappa.square()]) {
        weights
            .add_multilinear(scale, point.to_vec())
            .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
    }
    let lower = rank_inactive_masks(layout);
    if inserted_value == QM31::ZERO {
        let mut inactive_masks = [0u16; 128];
        for row in 0..TRACE_ROWS {
            if ((lower[row >> 4] >> (row & 15)) & 1) == 0 {
                continue;
            }
            let embedded = embed_extended_trace_row(row, insertion_coordinate, 0);
            inactive_masks[embedded >> 4] |= 1 << (embedded & 15);
        }
        weights
            .add_grouped_128x16_binary_masks(inactive_masks)
            .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
    } else {
        let mut inactive_weights = vec![QM31::ZERO; EXTENDED_TRACE_ROWS];
        for row in 0..TRACE_ROWS {
            if ((lower[row >> 4] >> (row & 15)) & 1) == 0 {
                continue;
            }
            inactive_weights[embed_extended_trace_row(row, insertion_coordinate, 0)] =
                QM31::ONE.sub(inserted_value);
            inactive_weights[embed_extended_trace_row(row, insertion_coordinate, 1)] =
                inserted_value;
        }
        weights
            .add_dense(inactive_weights)
            .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
    }
    Ok(weights)
}

fn extended_row_pcs_tail(
    domain_log: u32,
    row: usize,
    mut codeword: Vec<QM31>,
    schedule: &StateOnlyTranscriptScheduleResult,
    later_indices: &[Vec<u32>; CANDIDATE_ROUND_COUNT - 1],
    layout: RankLayout,
) -> Result<Vec<QM31>, StateOnlyHidingRankGateError> {
    let mut coefficients = vec![QM31::ZERO; EXTENDED_TRACE_ROWS];
    coefficients[row] = QM31::ONE;
    let mut weights = extended_initial_weights(schedule, layout)?;
    let mut running_claim = weights.dot(&coefficients);
    let mut later = Vec::new();
    let mut ood_values = [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT];
    let mut polynomials = [[QM31::ZERO; 7]; CANDIDATE_ROUND_COUNT];

    for round in 0..CANDIDATE_ROUND_COUNT {
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            let mut evaluation = WeightAccumulator::empty(EXTENDED_LOG_ROWS - 2 * round as u32);
            if round == 0 {
                evaluation
                    .add_circle_tensor(QM31::ONE, schedule.circle_ood_points[sample])
                    .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
                weights
                    .add_circle_tensor(
                        schedule.mu[round][sample],
                        schedule.circle_ood_points[sample],
                    )
                    .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
            } else {
                evaluation
                    .add_line_tensor(QM31::ONE, schedule.line_ood_points[round - 1][sample])
                    .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
                weights
                    .add_line_tensor(
                        schedule.mu[round][sample],
                        schedule.line_ood_points[round - 1][sample],
                    )
                    .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
            }
            let value = evaluation.dot(&coefficients);
            ood_values[round][sample] = value;
            running_claim = running_claim.add(schedule.mu[round][sample].mul(value));
        }
        let polynomial = polynomial_for_extension(&coefficients, &weights);
        if boundary_sum(&polynomial) != running_claim {
            return Err(StateOnlyHidingRankGateError::Relation);
        }
        polynomials[round] = polynomial;
        running_claim = evaluate_relation(&polynomial, schedule.alpha[round]);
        weights.fold(schedule.alpha[round]);
        coefficients = fold_adjacent_natural_arity4(&coefficients, schedule.alpha[round]);
        if weights.dot(&coefficients) != running_claim {
            return Err(StateOnlyHidingRankGateError::Relation);
        }
        codeword = fold_candidate_codeword_round_for_domain_log(
            &codeword,
            schedule.alpha[round],
            round,
            domain_log,
        )?;
        if round + 1 < CANDIDATE_ROUND_COUNT {
            for &query in &later_indices[round] {
                let start = FIBER_SLOTS * query as usize;
                later.extend_from_slice(&codeword[start..start + FIBER_SLOTS]);
            }
        }
    }

    let mut tail = later;
    for values in ood_values {
        tail.extend_from_slice(&values);
    }
    for polynomial in polynomials {
        tail.extend_from_slice(&polynomial);
    }
    debug_assert_eq!(coefficients.len(), 8);
    tail.extend_from_slice(&coefficients);
    Ok(tail)
}

fn extended_row_public_maps(
    encoder: &CircleEncoder,
    domain_log: u32,
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<Vec<RowPublicMaps>, StateOnlyHidingRankGateError> {
    let indices = derive_circle_line_query_indices_for_count(
        &schedule.queries[..schedule.query_count],
        encoder.codeword_len() / FIBER_SLOTS,
    )
    .map_err(|_| StateOnlyHidingRankGateError::Shape)?;
    let terminal_points = [
        extended_point(&schedule.prefix.z),
        extended_point(&binary_successor_point(&schedule.prefix.z)),
        extended_point(&xor12_point(&schedule.prefix.z)),
    ];
    let mut rows = Vec::with_capacity(EXTENDED_TRACE_ROWS);
    for row in 0..EXTENDED_TRACE_ROWS {
        let mut message = vec![QM31::ZERO; EXTENDED_TRACE_ROWS];
        message[row] = QM31::ONE;
        let codeword = encoder.encode_c2_message_prefix(&message)?;
        let mut layer0_m31 = Vec::with_capacity(indices.layer0.len() * FIBER_SLOTS);
        for &query in &indices.layer0 {
            let start = FIBER_SLOTS * query as usize;
            for value in &codeword[start..start + FIBER_SLOTS] {
                if value.c0.b != M31::ZERO || value.c1 != CM31::ZERO {
                    return Err(StateOnlyHidingRankGateError::Encoding);
                }
                layer0_m31.push(value.c0.a);
            }
        }
        rows.push(RowPublicMaps {
            layer0_m31,
            terminal: core::array::from_fn(|point| eq_weight_slice(&terminal_points[point], row)),
            pcs_tail: extended_row_pcs_tail(
                domain_log,
                row,
                codeword,
                schedule,
                &indices.later,
                RankLayout::StateOnlyV4,
            )?,
        });
    }
    Ok(rows)
}

fn sparse_extended_folded_row_value(
    encoder: &CircleEncoder,
    domain_log: u32,
    row: usize,
    schedule: &StateOnlyTranscriptScheduleResult,
    layer: usize,
    index: usize,
    memo: &mut BTreeMap<(usize, usize), QM31>,
) -> Result<QM31, StateOnlyHidingRankGateError> {
    if let Some(value) = memo.get(&(layer, index)) {
        return Ok(*value);
    }
    let value = if layer == 0 {
        QM31::from_cm31(CM31::from_m31(encoder.encode_prefix_basis_value(
            EXTENDED_LOG_ROWS,
            row,
            index,
        )?))
    } else {
        let mut values = [QM31::ZERO; FIBER_SLOTS];
        for (slot, value) in values.iter_mut().enumerate() {
            *value = sparse_extended_folded_row_value(
                encoder,
                domain_log,
                row,
                schedule,
                layer - 1,
                FIBER_SLOTS * index + slot,
                memo,
            )?;
        }
        if layer == 1 {
            aspis_core::circle_fri::normalized_circle_to_line_arity4_at_fiber_for_domain_log(
                values,
                schedule.alpha[0],
                domain_log,
                index,
            )
            .map_err(|_| StateOnlyHidingRankGateError::Encoding)?
        } else {
            normalized_line_arity4_at_fiber_for_domain_log(
                values,
                schedule.alpha[layer - 1],
                domain_log,
                (layer - 1) as u8,
                index,
            )
            .map_err(|_| StateOnlyHidingRankGateError::Encoding)?
        }
    };
    memo.insert((layer, index), value);
    Ok(value)
}

fn extended_row_pcs_tail_sparse(
    encoder: &CircleEncoder,
    domain_log: u32,
    row: usize,
    schedule: &StateOnlyTranscriptScheduleResult,
    later_indices: &[Vec<u32>; CANDIDATE_ROUND_COUNT - 1],
    layout: RankLayout,
) -> Result<Vec<QM31>, StateOnlyHidingRankGateError> {
    extended_row_pcs_tail_sparse_at(
        encoder,
        domain_log,
        row,
        schedule,
        later_indices,
        layout,
        0,
        QM31::ZERO,
    )
}

fn extended_row_pcs_tail_sparse_at(
    encoder: &CircleEncoder,
    domain_log: u32,
    row: usize,
    schedule: &StateOnlyTranscriptScheduleResult,
    later_indices: &[Vec<u32>; CANDIDATE_ROUND_COUNT - 1],
    layout: RankLayout,
    insertion_coordinate: usize,
    inserted_value: QM31,
) -> Result<Vec<QM31>, StateOnlyHidingRankGateError> {
    let mut coefficients = vec![QM31::ZERO; EXTENDED_TRACE_ROWS];
    coefficients[row] = QM31::ONE;
    let mut weights =
        extended_initial_weights_at(schedule, layout, insertion_coordinate, inserted_value)?;
    let mut running_claim = weights.dot(&coefficients);
    let mut later = Vec::new();
    let mut ood_values = [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT];
    let mut polynomials = [[QM31::ZERO; 7]; CANDIDATE_ROUND_COUNT];
    let mut memo = BTreeMap::new();

    for round in 0..CANDIDATE_ROUND_COUNT {
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            let mut evaluation = WeightAccumulator::empty(EXTENDED_LOG_ROWS - 2 * round as u32);
            if round == 0 {
                evaluation
                    .add_circle_tensor(QM31::ONE, schedule.circle_ood_points[sample])
                    .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
                weights
                    .add_circle_tensor(
                        schedule.mu[round][sample],
                        schedule.circle_ood_points[sample],
                    )
                    .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
            } else {
                evaluation
                    .add_line_tensor(QM31::ONE, schedule.line_ood_points[round - 1][sample])
                    .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
                weights
                    .add_line_tensor(
                        schedule.mu[round][sample],
                        schedule.line_ood_points[round - 1][sample],
                    )
                    .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
            }
            let value = evaluation.dot(&coefficients);
            ood_values[round][sample] = value;
            running_claim = running_claim.add(schedule.mu[round][sample].mul(value));
        }
        let polynomial = polynomial_for_extension(&coefficients, &weights);
        if boundary_sum(&polynomial) != running_claim {
            return Err(StateOnlyHidingRankGateError::Relation);
        }
        polynomials[round] = polynomial;
        running_claim = evaluate_relation(&polynomial, schedule.alpha[round]);
        weights.fold(schedule.alpha[round]);
        coefficients = fold_adjacent_natural_arity4(&coefficients, schedule.alpha[round]);
        if weights.dot(&coefficients) != running_claim {
            return Err(StateOnlyHidingRankGateError::Relation);
        }
        if round + 1 < CANDIDATE_ROUND_COUNT {
            for &leaf in &later_indices[round] {
                for slot in 0..FIBER_SLOTS {
                    later.push(sparse_extended_folded_row_value(
                        encoder,
                        domain_log,
                        row,
                        schedule,
                        round + 1,
                        FIBER_SLOTS * leaf as usize + slot,
                        &mut memo,
                    )?);
                }
            }
        }
    }

    let mut tail = later;
    for values in ood_values {
        tail.extend_from_slice(&values);
    }
    for polynomial in polynomials {
        tail.extend_from_slice(&polynomial);
    }
    if coefficients.len() != 8 {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    tail.extend_from_slice(&coefficients);
    Ok(tail)
}

fn extended_row_public_maps_sparse_atomic_profile21(
    encoder: &CircleEncoder,
    domain_log: u32,
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<(Vec<RowPublicMaps>, [Vec<u32>; CANDIDATE_ROUND_COUNT - 1]), StateOnlyHidingRankGateError>
{
    extended_row_public_maps_sparse_atomic_profile21_at(
        encoder,
        domain_log,
        schedule,
        0,
        QM31::ZERO,
    )
}

fn extended_row_public_maps_sparse_atomic_profile21_at(
    encoder: &CircleEncoder,
    domain_log: u32,
    schedule: &StateOnlyTranscriptScheduleResult,
    insertion_coordinate: usize,
    inserted_value: QM31,
) -> Result<(Vec<RowPublicMaps>, [Vec<u32>; CANDIDATE_ROUND_COUNT - 1]), StateOnlyHidingRankGateError>
{
    if insertion_coordinate > STATE_ONLY_HIDING_SUMCHECK_ROUNDS {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let indices = derive_circle_line_query_indices_for_count(
        &schedule.queries[..schedule.query_count],
        encoder.codeword_len() / FIBER_SLOTS,
    )
    .map_err(|_| StateOnlyHidingRankGateError::Shape)?;
    let terminal_points = [
        extended_point_at(&schedule.prefix.z, insertion_coordinate, inserted_value),
        extended_point_at(
            &binary_successor_point(&schedule.prefix.z),
            insertion_coordinate,
            inserted_value,
        ),
        extended_point_at(
            &xor12_point(&schedule.prefix.z),
            insertion_coordinate,
            inserted_value,
        ),
    ];
    let mut rows = Vec::with_capacity(EXTENDED_TRACE_ROWS);
    for row in 0..EXTENDED_TRACE_ROWS {
        let mut layer0_m31 = Vec::with_capacity(indices.layer0.len() * FIBER_SLOTS);
        for &query in &indices.layer0 {
            for slot in 0..FIBER_SLOTS {
                layer0_m31.push(encoder.encode_prefix_basis_value(
                    EXTENDED_LOG_ROWS,
                    row,
                    FIBER_SLOTS * query as usize + slot,
                )?);
            }
        }
        rows.push(RowPublicMaps {
            layer0_m31,
            terminal: core::array::from_fn(|point| eq_weight_slice(&terminal_points[point], row)),
            pcs_tail: extended_row_pcs_tail_sparse_at(
                encoder,
                domain_log,
                row,
                schedule,
                &indices.later,
                RankLayout::AtomicV3,
                insertion_coordinate,
                inserted_value,
            )?,
        });
    }
    Ok((rows, indices.later))
}

fn scaled_qm31_difference(left: &[QM31], right: Option<&[QM31]>, scale: QM31) -> Vec<M31> {
    let mut output = Vec::with_capacity(4 * left.len());
    for (index, value) in left.iter().copied().enumerate() {
        let difference = right.map_or(value, |right| value.sub(right[index]));
        output.extend_from_slice(&qm31_coordinates(scale.mul(difference)));
    }
    output
}

fn c1_raw_difference(rows: &[RowPublicMaps], row: usize, dependent: Option<usize>) -> Vec<M31> {
    let mut raw = rows[row].layer0_m31.clone();
    if let Some(dependent) = dependent {
        for (value, subtract) in raw.iter_mut().zip(&rows[dependent].layer0_m31) {
            *value = value.sub(*subtract);
        }
    }
    for point in 0..3 {
        let value = dependent.map_or(rows[row].terminal[point], |dependent| {
            rows[row].terminal[point].sub(rows[dependent].terminal[point])
        });
        raw.extend_from_slice(&qm31_coordinates(value));
    }
    raw
}

fn qm31_raw_difference(
    rows: &[RowPublicMaps],
    row: usize,
    dependent: Option<usize>,
    basis: QM31,
) -> Vec<M31> {
    let mut raw = Vec::with_capacity(4 * (rows[row].layer0_m31.len() + 3));
    for (index, value) in rows[row].layer0_m31.iter().copied().enumerate() {
        let value = dependent.map_or(value, |dependent| {
            value.sub(rows[dependent].layer0_m31[index])
        });
        raw.extend_from_slice(&qm31_coordinates(basis.mul_m31(value)));
    }
    for point in 0..3 {
        let value = dependent.map_or(rows[row].terminal[point], |dependent| {
            rows[row].terminal[point].sub(rows[dependent].terminal[point])
        });
        raw.extend_from_slice(&qm31_coordinates(basis.mul(value)));
    }
    raw
}

fn scaled_aux_difference(
    rows: &[RowPublicMaps],
    row: usize,
    dependent: Option<usize>,
    sumcheck: &[Vec<QM31>],
    sumcheck_scale: QM31,
    pcs_scale: QM31,
    h_raw_m31: usize,
    pcs_rows: usize,
) -> Vec<M31> {
    let mut aux = scaled_qm31_difference(
        &sumcheck[row],
        dependent.map(|dependent| sumcheck[dependent].as_slice()),
        sumcheck_scale,
    );
    aux.resize(
        4 * STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS + pcs_rows,
        M31::ZERO,
    );
    let pcs = scaled_qm31_difference(
        &rows[row].pcs_tail,
        dependent.map(|dependent| rows[dependent].pcs_tail.as_slice()),
        pcs_scale,
    );
    let pcs_start = 4 * STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS + h_raw_m31;
    aux[pcs_start..pcs_start + pcs.len()].copy_from_slice(&pcs);
    aux
}

fn h_pcs_image(
    rows: &[RowPublicMaps],
    row: usize,
    dependent: usize,
    basis: QM31,
    h_scale: QM31,
    h_raw_qm31: usize,
    pcs_tail_qm31: usize,
) -> Vec<M31> {
    let mut image = Vec::with_capacity(4 * (h_raw_qm31 + pcs_tail_qm31));
    for (index, value) in rows[row].layer0_m31.iter().copied().enumerate() {
        let difference = value.sub(rows[dependent].layer0_m31[index]);
        image.extend_from_slice(&qm31_coordinates(basis.mul_m31(difference)));
    }
    for point in 0..3 {
        let difference = rows[row].terminal[point].sub(rows[dependent].terminal[point]);
        image.extend_from_slice(&qm31_coordinates(basis.mul(difference)));
    }
    let scale = basis.mul(h_scale);
    image.extend_from_slice(&scaled_qm31_difference(
        &rows[row].pcs_tail,
        Some(&rows[dependent].pcs_tail),
        scale,
    ));
    image
}

fn h_pcs_single_image(
    rows: &[RowPublicMaps],
    row: usize,
    basis: QM31,
    h_scale: QM31,
    h_raw_qm31: usize,
    pcs_tail_qm31: usize,
) -> Vec<M31> {
    let mut image = Vec::with_capacity(4 * (h_raw_qm31 + pcs_tail_qm31));
    for value in rows[row].layer0_m31.iter().copied() {
        image.extend_from_slice(&qm31_coordinates(basis.mul_m31(value)));
    }
    for point in 0..3 {
        image.extend_from_slice(&qm31_coordinates(basis.mul(rows[row].terminal[point])));
    }
    image.extend_from_slice(&scaled_qm31_difference(
        &rows[row].pcs_tail,
        None,
        basis.mul(h_scale),
    ));
    image
}

fn combined_pcs_image(
    rows: &[RowPublicMaps],
    row: usize,
    basis: QM31,
    h_raw_qm31: usize,
    pcs_tail_qm31: usize,
) -> Vec<M31> {
    let mut image = vec![M31::ZERO; 4 * h_raw_qm31];
    image.reserve(4 * pcs_tail_qm31);
    image.extend_from_slice(&scaled_qm31_difference(&rows[row].pcs_tail, None, basis));
    image
}

fn gamma_power(gamma: QM31, exponent: usize) -> QM31 {
    (0..exponent).fold(QM31::ONE, |power, _| power.mul(gamma))
}

/// Build only the root opening map needed by the root-neutral sumcheck
/// theorem.  In particular this does not construct a PCS continuation and
/// therefore cannot accidentally turn a nonzero root message into a false
/// positive through a schedule-specific PCS kernel.
fn root_neutral_raw_rows(
    encoder: &CircleEncoder,
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<Vec<RowPublicMaps>, StateOnlyHidingRankGateError> {
    let indices = derive_circle_line_query_indices_for_count(
        &schedule.queries[..schedule.query_count],
        encoder.codeword_len() / FIBER_SLOTS,
    )
    .map_err(|_| StateOnlyHidingRankGateError::Shape)?;
    if indices.layer0.len() != schedule.query_count {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let terminal_points = [
        schedule.prefix.z,
        binary_successor_point(&schedule.prefix.z),
        xor12_point(&schedule.prefix.z),
    ];
    let mut rows = Vec::with_capacity(TRACE_ROWS);
    for row in 0..TRACE_ROWS {
        let mut layer0_m31 = Vec::with_capacity(indices.layer0.len() * FIBER_SLOTS);
        for &query in &indices.layer0 {
            for slot in 0..FIBER_SLOTS {
                layer0_m31
                    .push(encoder.encode_c1_basis_value(row, FIBER_SLOTS * query as usize + slot)?);
            }
        }
        rows.push(RowPublicMaps {
            layer0_m31,
            terminal: core::array::from_fn(|point| eq_weight(&terminal_points[point], row)),
            pcs_tail: Vec::new(),
        });
    }
    Ok(rows)
}

/// Probe the exact algebraic reduction
///
/// ```text
/// U_j  -> (U_j, G = -gamma^(16+j-27) U_j).
/// ```
///
/// The paired source has identically zero gamma-combined root message.  The
/// C1 and G opening maps are restrictions of the same K-linear map, hence a
/// raw-kernel `U_j` also gives a raw-kernel G value.  We additionally put the
/// initial mask claim in the conditioned block, and ask whether the remaining
/// 270 QM31 serialized sumcheck coordinates have full M31 rank.  A deficit is
/// therefore a genuine root-neutral source-map counterexample for the ten
/// selected mask-only columns, not a sampled-minor or PCS artifact.
pub fn probe_atomic_state_only_profile22_root_neutral_sumcheck(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<StateOnlyRootNeutralSumcheckReport, StateOnlyHidingRankGateError> {
    probe_atomic_state_only_profile22_root_neutral_sumcheck_inner(
        schedule,
        FactorSchedule::Production,
    )
}

/// Same exact root-neutral reduction as
/// [`probe_atomic_state_only_profile22_root_neutral_sumcheck`], with the
/// production-neutral complete-shared-power repair (`G=L_0^23`).
pub fn probe_atomic_state_only_profile22_complete_shared_power_root_neutral_sumcheck(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<StateOnlyRootNeutralSumcheckReport, StateOnlyHidingRankGateError> {
    probe_atomic_state_only_profile22_root_neutral_sumcheck_inner(
        schedule,
        FactorSchedule::CompleteSharedPowers,
    )
}

/// Exact D=0/root-neutral diagnostic for the zero-width shared degree-cover
/// schedule: M31 factors cover degrees 0..=25 and production-shaped G keeps
/// the independent-family degree-26 factor.
pub fn probe_atomic_state_only_profile22_shared_degree_cover_root_neutral_sumcheck(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<StateOnlyRootNeutralSumcheckReport, StateOnlyHidingRankGateError> {
    probe_atomic_state_only_profile22_root_neutral_sumcheck_inner(
        schedule,
        FactorSchedule::SharedDegreesZeroToTwentyFive,
    )
}

/// Exact D=0/root-neutral diagnostic for enriching the same existing QM31 G
/// lane by `coefficient * L_0^exponent`.  This adds no source, opening, or
/// generator coordinate.
pub fn probe_atomic_state_only_profile22_g_add_shared_power_root_neutral_sumcheck(
    schedule: &StateOnlyTranscriptScheduleResult,
    exponent: usize,
    coefficient: M31,
) -> Result<StateOnlyRootNeutralSumcheckReport, StateOnlyHidingRankGateError> {
    if exponent > 26 || coefficient == M31::ZERO {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    probe_atomic_state_only_profile22_root_neutral_sumcheck_inner(
        schedule,
        FactorSchedule::ExplicitGAddSharedPower {
            exponent: exponent as u8,
            coefficient,
        },
    )
}

/// Exact D=0/root-neutral sumcheck diagnostic for one host-only
/// distinct-linear factor assignment.  `prefix_m31_lanes=26` selects the
/// full bijective assignment; smaller values are the predeclared ordered
/// shared-to-distinct prefix screen.  No proof or verifier state changes.
pub fn probe_atomic_state_only_profile22_distinct_linear_root_neutral_sumcheck(
    schedule: &StateOnlyTranscriptScheduleResult,
    assignment: DistinctLinearAssignment,
    g_factor: DistinctLinearGFactor,
    prefix_m31_lanes: usize,
) -> Result<StateOnlyRootNeutralSumcheckReport, StateOnlyHidingRankGateError> {
    if prefix_m31_lanes > DISTINCT_LINEAR_M31_LANES {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    probe_atomic_state_only_profile22_root_neutral_sumcheck_inner(
        schedule,
        FactorSchedule::DistinctLinear {
            assignment,
            g_factor,
            prefix_m31_lanes: prefix_m31_lanes as u8,
        },
    )
}

fn probe_atomic_state_only_profile22_root_neutral_sumcheck_inner(
    schedule: &StateOnlyTranscriptScheduleResult,
    factor_schedule: FactorSchedule,
) -> Result<StateOnlyRootNeutralSumcheckReport, StateOnlyHidingRankGateError> {
    let started = Instant::now();
    if schedule.query_count != 16
        || schedule.query_count > schedule.queries.len()
        || schedule.prefix.gamma == QM31::ZERO
    {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let domain_log = STATE_ONLY_LOG_ROWS + 9;
    let encoder = CircleEncoder::new_for_domain_log(domain_log);
    let rows = root_neutral_raw_rows(&encoder, schedule)?;
    let c1_raw_m31 = rows[0].layer0_m31.len() + 12;
    let legal_sumcheck_m31 = 4 * (STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS - 1);
    let lagrange = lagrange_basis();
    let active_rows = rank_active_rows(RankLayout::AtomicV3);
    let mut active = [false; TRACE_ROWS];
    for &row in active_rows {
        active[usize::from(row)] = true;
    }
    let global_dependent = (0..TRACE_ROWS)
        .find(|row| !active[*row])
        .ok_or(StateOnlyHidingRankGateError::Layout)?;
    let g_observations = (0..TRACE_ROWS)
        .map(|row| {
            mask_sumcheck_observations(
                row,
                &schedule.prefix.z,
                &lagrange,
                MaskFactor::ExplicitG,
                factor_schedule,
                None,
            )
        })
        .collect::<Vec<_>>();
    let gamma_g_inverse = gamma_power(schedule.prefix.gamma, 27).inv();
    let mut legal_rank = ColumnEchelon::new(legal_sumcheck_m31);
    let mut initial_claim = CarryEchelon::new(4);
    let mut full_rank = ColumnEchelon::new(4 * STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS);
    let mut raw_kernel_m31 = 0usize;
    let mut raw_plus_initial_kernel_m31 = 0usize;
    let mut prefix_root_neutral_legal_ranks_m31 =
        Vec::with_capacity(STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS);

    for mask_column in 0..STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS {
        let observations = (0..TRACE_ROWS)
            .map(|row| {
                mask_sumcheck_observations(
                    row,
                    &schedule.prefix.z,
                    &lagrange,
                    MaskFactor::MaskOnly(mask_column),
                    factor_schedule,
                    None,
                )
            })
            .collect::<Vec<_>>();
        let generator = STATE_ONLY_HIDING_C1_COLUMNS + mask_column;
        let g_ratio = gamma_power(schedule.prefix.gamma, generator).mul(gamma_g_inverse);
        let effective = observations
            .iter()
            .zip(&g_observations)
            .map(|(mask, g)| {
                mask.iter()
                    .copied()
                    .zip(g)
                    .map(|(mask, &g)| mask.sub(g_ratio.mul(g)))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        // First quotient only the separate C1 raw block.  This reports the
        // ordinary effective-wire rank and provides a useful negative-tooth
        // distinction from the stronger zero-initial-claim quotient below.
        let mut raw = CarryEchelon::new(c1_raw_m31);
        let mut column_sources = 0usize;
        for row in 0..TRACE_ROWS {
            if row == global_dependent {
                continue;
            }
            let subtract = (!active[row]).then_some(global_dependent);
            let raw_image = c1_raw_difference(&rows, row, subtract);
            let effective_image = scaled_qm31_difference(
                &effective[row],
                subtract.map(|dependent| effective[dependent].as_slice()),
                QM31::ONE,
            );
            column_sources += 1;
            if let Some(kernel) = raw.reduce(raw_image.clone(), effective_image.clone()) {
                raw_kernel_m31 += 1;
                full_rank.insert(kernel.clone());
                if let Some(legal) =
                    initial_claim.reduce(kernel[..4].to_vec(), kernel[4..].to_vec())
                {
                    raw_plus_initial_kernel_m31 += 1;
                    legal_rank.insert(legal);
                }
            }
        }
        debug_assert_eq!(column_sources, TRACE_ROWS - 1);
        prefix_root_neutral_legal_ranks_m31.push(legal_rank.rank);
    }

    let mask_only_root_neutral_legal_sumcheck_rank_m31 = legal_rank.rank;
    let mut semantic_raw_kernel_m31 = 0usize;
    let cells = atomic_state_only_relation_free_mask_cells_v3()
        .map_err(|_| StateOnlyHidingRankGateError::Layout)?;
    let mut cells_by_column = vec![Vec::new(); STATE_ONLY_HIDING_C1_COLUMNS];
    for cell in cells {
        cells_by_column[usize::from(cell.column)].push(usize::from(cell.row));
    }
    for (column, cells) in cells_by_column.iter().enumerate() {
        let dependent = cells
            .iter()
            .copied()
            .filter(|row| !active[*row])
            .last()
            .ok_or(StateOnlyHidingRankGateError::Layout)?;
        let observations = (0..TRACE_ROWS)
            .map(|row| {
                mask_sumcheck_observations(
                    row,
                    &schedule.prefix.z,
                    &lagrange,
                    MaskFactor::Semantic(column),
                    factor_schedule,
                    None,
                )
            })
            .collect::<Vec<_>>();
        let g_ratio = gamma_power(schedule.prefix.gamma, column).mul(gamma_g_inverse);
        let effective = observations
            .iter()
            .zip(&g_observations)
            .map(|(mask, g)| {
                mask.iter()
                    .copied()
                    .zip(g)
                    .map(|(mask, &g)| mask.sub(g_ratio.mul(g)))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let mut raw = CarryEchelon::new(c1_raw_m31);
        for &row in cells {
            if row == dependent {
                continue;
            }
            let subtract = (!active[row]).then_some(dependent);
            let raw_image = c1_raw_difference(&rows, row, subtract);
            let effective_image = scaled_qm31_difference(
                &effective[row],
                subtract.map(|dependent| effective[dependent].as_slice()),
                QM31::ONE,
            );
            if let Some(kernel) = raw.reduce(raw_image, effective_image) {
                semantic_raw_kernel_m31 += 1;
                if let Some(legal) =
                    initial_claim.reduce(kernel[..4].to_vec(), kernel[4..].to_vec())
                {
                    legal_rank.insert(legal);
                }
            }
        }
    }
    let root_neutral_legal_sumcheck_rank_m31 = legal_rank.rank;

    // Diagnostic only: H1 padding is supported on inactive rows and paired
    // pointwise with G at ratio gamma^(26-27).  Its actual production
    // sumcheck image also contains eta times the unmasked H1 oracle, which is
    // witness-dependent; omitting that term here tells us whether H1 is the
    // sole location of any remaining rank, but is not an all-witness proof.
    let h_g_ratio = gamma_power(schedule.prefix.gamma, 26).mul(gamma_g_inverse);
    let mut idealized_h1_root_neutral_kernel_m31 = 0usize;
    let mut h_raw = CarryEchelon::new(4 * c1_raw_m31);
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for row in 0..TRACE_ROWS {
            if active[row] || row == global_dependent {
                continue;
            }
            let raw_image = qm31_raw_difference(&rows, row, Some(global_dependent), basis);
            let effective_image = scaled_qm31_difference(
                &g_observations[row],
                Some(g_observations[global_dependent].as_slice()),
                QM31::ZERO.sub(h_g_ratio.mul(basis)),
            );
            if let Some(kernel) = h_raw.reduce(raw_image, effective_image) {
                idealized_h1_root_neutral_kernel_m31 += 1;
                if let Some(legal) =
                    initial_claim.reduce(kernel[..4].to_vec(), kernel[4..].to_vec())
                {
                    legal_rank.insert(legal);
                }
            }
        }
    }

    Ok(StateOnlyRootNeutralSumcheckReport {
        factor_schedule: match factor_schedule {
            FactorSchedule::Production => "production",
            FactorSchedule::CompleteSharedPowers => "complete_shared_powers_g_l0_pow23",
            FactorSchedule::SharedLinear => "shared_linear",
            FactorSchedule::FullSharedLinear => "full_shared_linear",
            FactorSchedule::SharedDegreesZeroToTwentyFive => {
                "shared_m31_degrees_0_to_25_g_family16_degree26"
            }
            FactorSchedule::ExplicitGAddSharedPower { .. } => {
                "shared_m31_g_one_plus_l16_pow26_plus_c_l0_pow_d"
            }
            FactorSchedule::DistinctLinear {
                g_factor: DistinctLinearGFactor::MissingDegree23,
                ..
            } => "distinct_linear_g_l_pow23",
            FactorSchedule::DistinctLinear {
                g_factor: DistinctLinearGFactor::Degree26AddOne,
                ..
            } => "distinct_linear_g_one_plus_l_pow26",
        },
        query_count: schedule.query_count,
        gamma_nonzero: schedule.prefix.gamma != QM31::ZERO,
        c1_raw_m31,
        legal_sumcheck_m31,
        mask_only_columns: STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS,
        raw_kernel_m31,
        raw_plus_initial_kernel_m31,
        unconditioned_sumcheck_rank_m31: full_rank.rank,
        mask_only_root_neutral_legal_sumcheck_rank_m31,
        semantic_raw_kernel_m31,
        idealized_h1_root_neutral_kernel_m31,
        idealized_h1_root_neutral_legal_sumcheck_rank_m31: legal_rank.rank,
        root_neutral_legal_sumcheck_rank_m31,
        prefix_root_neutral_legal_ranks_m31,
        complete: root_neutral_legal_sumcheck_rank_m31 == legal_sumcheck_m31,
        elapsed_millis: started.elapsed().as_millis(),
    })
}

/// Run the canonical joint affine-View rank gate for the exact schedule that
/// will be serialized.  The function is deliberately deterministic and does
/// not inspect witness values or realized masks.
pub fn check_state_only_complete_hiding_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner(
        schedule,
        false,
        FactorSchedule::Production,
        None,
        LateSwitchSupport::None,
        PcsSchedule::Arity4x4,
        false,
    )
}

/// Diagnostic A/B for one extra full-domain QM31 C2 tail mask.  The probe has
/// its own raw and three-point opening block, generator index 28, zero
/// zerocheck coefficient, and the exact inactive-zero sampler constraint.
/// It is not integrated into the proof format by this function.
pub fn check_state_only_complete_hiding_rank_with_tail_qm31_probe(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner(
        schedule,
        true,
        FactorSchedule::Production,
        None,
        LateSwitchSupport::None,
        PcsSchedule::Arity4x4,
        false,
    )
}

/// Host-only structural probe for a fresh late code-switch mask.  The probe
/// selects a 31-QM31 low-degree source subspace, conditions it on one dense
/// QM31 switch identity, and tests the resulting 30-QM31 kernel against the
/// exact complete PCS-view quotient.  It does not implement the commitment,
/// simulator, or proximity proof and therefore is not an HVZK claim.
pub fn probe_state_only_late_switch_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
    shared_linear_factors: bool,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner(
        schedule,
        false,
        if shared_linear_factors {
            FactorSchedule::SharedLinear
        } else {
            FactorSchedule::Production
        },
        None,
        LateSwitchSupport::StructuredSource31,
        PcsSchedule::Arity4x4,
        false,
    )
}

pub fn probe_state_only_full_shared_late_switch_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner(
        schedule,
        false,
        FactorSchedule::FullSharedLinear,
        None,
        LateSwitchSupport::StructuredSource31,
        PcsSchedule::Arity4x4,
        false,
    )
}

/// Host-only complete-view gate for the shared-power factor schedule without
/// any late switch.  It returns a red rank report instead of converting an
/// ambient deficit into `JointPcsRank`, which makes lower-q structural A/Bs
/// directly measurable.
pub fn probe_state_only_full_shared_hiding_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner(
        schedule,
        false,
        FactorSchedule::FullSharedLinear,
        None,
        LateSwitchSupport::None,
        PcsSchedule::Arity4x4,
        true,
    )
}

/// Exact complete-view quotient for the conservative single masked switch.
/// This is production-neutral: it fixes the complete field wire and FS order
/// for rank testing but does not enable any verifier acceptance path.
pub fn probe_state_only_masked_single_switch_joint_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner(
        schedule,
        false,
        FactorSchedule::FullSharedLinear,
        None,
        LateSwitchSupport::MaskedSlotZeroSingleCodeword,
        PcsSchedule::Arity4x4,
        false,
    )
}

/// Exact complete-view baseline under the atomic-v3 mask inventory and copy
/// inactive-row factor, using the actual atomic transcript schedule.
pub fn probe_atomic_state_only_full_shared_hiding_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner_for_layout(
        schedule,
        false,
        FactorSchedule::FullSharedLinear,
        None,
        LateSwitchSupport::None,
        PcsSchedule::Arity4x4,
        true,
        RankLayout::AtomicV3,
    )
}

/// Exact quotient diagnostic for the physical atomic-v3 witness-difference
/// basis emitted by `apply_mask_material_for_layout`: active `e_r` and
/// inactive `e_r-e_d(c)`, excluding row zero and each column dependent.  It
/// also covers all legal zero-initial-claim degree-27 sumcheck wire directions
/// and the complete active zero-sum H subspace.  A separately labelled
/// unbalanced `e_r` upper-oracle control is reported but never decides
/// same-statement containment. X, F, mask-only columns and G are prover
/// randomness, not witness sources.
pub fn probe_atomic_state_only_profile21_witness_difference_containment(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner_for_layout(
        schedule,
        false,
        FactorSchedule::FullSharedLinear,
        None,
        LateSwitchSupport::WitnessDifferenceSuperset,
        PcsSchedule::Arity4x4,
        true,
        RankLayout::AtomicV3,
    )
}

/// Minimal Good22 diagnostic. Unlike the stronger ambient-surjectivity
/// probe, this continues after a deficient 1080-row sumcheck image. The
/// `witness_direct_sum_*` report fields then perform literal block Gaussian
/// elimination of the documented target: physical semantic differences,
/// independently allowed legal zero-initial sumcheck directions, and active
/// helper differences. The older `witness_*_rank` fields are PCS-quotient
/// diagnostics and must not classify containment when a target leaves a
/// sumcheck pivot. This is host-only research code and changes no proof wire
/// or verifier predicate.
pub fn probe_atomic_state_only_profile22_minimal_containment(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner_for_layout_and_delta_and_projection(
        schedule,
        false,
        FactorSchedule::FullSharedLinear,
        None,
        LateSwitchSupport::WitnessDifferenceSuperset,
        PcsSchedule::Arity4x4,
        true,
        RankLayout::AtomicV3,
        None,
        None,
        None,
        None,
        None,
        true,
        None,
    )
}

const PROFILE22_WEIGHTED_INACTIVE_SUM_COLUMNS: usize = 8;

#[derive(Clone, Copy)]
enum WeightedInactiveSumGroup {
    MaskOnly,
    Semantic,
    SemanticPlusMaskOnly,
}

#[derive(Clone, Copy)]
struct WeightedInactiveSumConfig {
    delta: QM31,
    selected_columns: u32,
    group: WeightedInactiveSumGroup,
}

fn probe_atomic_state_only_profile22_weighted_inactive_sum_rank_for_pcs(
    schedule: &StateOnlyTranscriptScheduleResult,
    delta: QM31,
    selected_columns: &[usize],
    group: WeightedInactiveSumGroup,
    pcs_schedule: PcsSchedule,
) -> Result<StateOnlyWeightedInactiveSumRankReport, StateOnlyHidingRankGateError> {
    let maximum_columns = match group {
        WeightedInactiveSumGroup::MaskOnly => STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS,
        WeightedInactiveSumGroup::Semantic => STATE_ONLY_HIDING_C1_COLUMNS,
        WeightedInactiveSumGroup::SemanticPlusMaskOnly => {
            STATE_ONLY_HIDING_C1_COLUMNS + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS
        }
    };
    let mut selected_mask = 0u32;
    for &column in selected_columns {
        if column >= maximum_columns || selected_mask & (1u32 << column) != 0 {
            return Err(StateOnlyHidingRankGateError::Shape);
        }
        selected_mask |= 1u32 << column;
    }
    if delta == QM31::ZERO || selected_mask.count_ones() < 4 {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let mut aggregate_claim = CarryEchelon::new(4);
    let mut aggregate_claim_sources = Vec::new();
    let mut aggregate_claim_rows = Vec::new();
    let mut aggregate_claim_values = Vec::new();
    for &column in selected_columns {
        let generator = match group {
            WeightedInactiveSumGroup::MaskOnly => STATE_ONLY_HIDING_C1_COLUMNS + column,
            WeightedInactiveSumGroup::Semantic => column,
            WeightedInactiveSumGroup::SemanticPlusMaskOnly => column,
        };
        if let CarryReduction::Pivot { row, value } = aggregate_claim.reduce_with_pivot(
            qm31_coordinates(gamma_power(schedule.prefix.gamma, generator)).to_vec(),
            Vec::new(),
        ) {
            aggregate_claim_sources.push(column);
            aggregate_claim_rows.push(row);
            aggregate_claim_values.push(value);
        }
    }
    if aggregate_claim.rank != 4 {
        return Err(StateOnlyHidingRankGateError::Layout);
    }
    let aggregate_claim_minor = RankMinorProvenance::from_parts(
        "weighted_inactive_sum_claim_4",
        aggregate_claim_sources,
        aggregate_claim_rows,
        aggregate_claim_values,
    );
    let complete_view =
        check_state_only_complete_hiding_rank_inner_for_layout_and_delta_and_projection(
            schedule,
            false,
            FactorSchedule::FullSharedLinear,
            None,
            LateSwitchSupport::WitnessDifferenceSuperset,
            pcs_schedule,
            true,
            RankLayout::AtomicV3,
            None,
            None,
            None,
            None,
            None,
            true,
            Some(WeightedInactiveSumConfig {
                delta,
                selected_columns: selected_mask,
                group,
            }),
        )?;
    let conditioned = |rank: Option<usize>| rank.map(|rank| rank - aggregate_claim.rank);
    Ok(StateOnlyWeightedInactiveSumRankReport {
        source_group: match group {
            WeightedInactiveSumGroup::MaskOnly => "mask_only",
            WeightedInactiveSumGroup::Semantic => "semantic",
            WeightedInactiveSumGroup::SemanticPlusMaskOnly => "semantic_plus_mask_only",
        },
        selected_columns: selected_columns.to_vec(),
        auxiliary_delta_nonzero: true,
        additional_private_sources_m31: selected_columns.len(),
        aggregate_claim_rank_m31: aggregate_claim.rank,
        aggregate_claim_minor,
        conditioned_kernel_m31: selected_columns.len() - aggregate_claim.rank,
        conditioned_mask_view_rank_m31: conditioned(
            complete_view.witness_direct_sum_mask_view_rank_m31,
        ),
        conditioned_physical_augmented_view_rank_m31: conditioned(
            complete_view.witness_direct_sum_physical_augmented_view_rank_m31,
        ),
        conditioned_legal_augmented_view_rank_m31: conditioned(
            complete_view.witness_direct_sum_legal_augmented_view_rank_m31,
        ),
        conditioned_helper_augmented_view_rank_m31: conditioned(
            complete_view.witness_direct_sum_helper_augmented_view_rank_m31,
        ),
        conditioned_unbalanced_physical_augmented_view_rank_m31: conditioned(
            complete_view.witness_direct_sum_unbalanced_physical_augmented_view_rank_m31,
        ),
        pcs_schedule: complete_view.pcs_schedule,
        complete_view,
    })
}

/// Exact production-PCS replay for the profile-22 first-eight weighted
/// inactive-sum repair.  The claim rank and conditioned-kernel dimension are
/// checked inside the elimination before this report is returned.
pub fn probe_atomic_state_only_profile22_weighted_inactive_sum_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
    delta: QM31,
) -> Result<StateOnlyWeightedInactiveSumRankReport, StateOnlyHidingRankGateError> {
    probe_atomic_state_only_profile22_weighted_inactive_sum_rank_for_pcs(
        schedule,
        delta,
        &(0..PROFILE22_WEIGHTED_INACTIVE_SUM_COLUMNS).collect::<Vec<_>>(),
        WeightedInactiveSumGroup::MaskOnly,
        PcsSchedule::Arity4x4,
    )
}

/// General host-only subset diagnostic used to find the minimum deterministic
/// selection after the all-ten control.  Column order is also the aggregate
/// claim elimination order and therefore appears in the returned minor.
pub fn probe_atomic_state_only_profile22_weighted_inactive_sum_rank_for_columns(
    schedule: &StateOnlyTranscriptScheduleResult,
    delta: QM31,
    selected_mask_columns: &[usize],
) -> Result<StateOnlyWeightedInactiveSumRankReport, StateOnlyHidingRankGateError> {
    probe_atomic_state_only_profile22_weighted_inactive_sum_rank_for_pcs(
        schedule,
        delta,
        selected_mask_columns,
        WeightedInactiveSumGroup::MaskOnly,
        PcsSchedule::Arity4x4,
    )
}

/// Semantic-column companion.  It relaxes the omitted relation-free
/// dependent source in each selected semantic column, conditions the single
/// gamma-weighted inactive aggregate, and group-batches semantic C1 plus H
/// by the fresh nonzero delta.  Same-statement disclosure invariance and the
/// new batching argument remain proof obligations; this is rank evidence.
pub fn probe_atomic_state_only_profile22_weighted_semantic_inactive_sum_rank_for_columns(
    schedule: &StateOnlyTranscriptScheduleResult,
    delta: QM31,
    selected_columns: &[usize],
) -> Result<StateOnlyWeightedInactiveSumRankReport, StateOnlyHidingRankGateError> {
    probe_atomic_state_only_profile22_weighted_inactive_sum_rank_for_pcs(
        schedule,
        delta,
        selected_columns,
        WeightedInactiveSumGroup::Semantic,
        PcsSchedule::Arity4x4,
    )
}

/// Last zero-width span control: one aggregate conditions the union of all
/// sixteen semantic-dependent and ten mask-only unbalanced sources.  The
/// fresh group scalar separates mask-only/G PCS contributions from
/// semantic/H contributions; zerocheck and raw openings remain unchanged.
pub fn probe_atomic_state_only_profile22_weighted_all_inactive_sum_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
    delta: QM31,
) -> Result<StateOnlyWeightedInactiveSumRankReport, StateOnlyHidingRankGateError> {
    probe_atomic_state_only_profile22_weighted_inactive_sum_rank_for_pcs(
        schedule,
        delta,
        &(0..STATE_ONLY_HIDING_C1_COLUMNS + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS)
            .collect::<Vec<_>>(),
        WeightedInactiveSumGroup::SemanticPlusMaskOnly,
        PcsSchedule::Arity4x4,
    )
}

/// Root-message companion to
/// `probe_atomic_state_only_profile22_weighted_inactive_sum_rank`.
pub fn probe_atomic_state_only_profile22_weighted_inactive_sum_root_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
    delta: QM31,
) -> Result<StateOnlyWeightedInactiveSumRankReport, StateOnlyHidingRankGateError> {
    probe_atomic_state_only_profile22_weighted_inactive_sum_rank_for_pcs(
        schedule,
        delta,
        &(0..PROFILE22_WEIGHTED_INACTIVE_SUM_COLUMNS).collect::<Vec<_>>(),
        WeightedInactiveSumGroup::MaskOnly,
        PcsSchedule::RootMessage,
    )
}

/// Production-neutral A/B for the complete shared-power repair.  Relative to
/// `probe_atomic_state_only_profile21_witness_difference_containment`, only
/// the public factor assigned to explicit G changes: it is `L_0^23`, the
/// sole power absent from the other twenty-six factors.  The production mask
/// schedule, transcript tag, and verifier are not changed by this probe.
pub fn probe_atomic_state_only_profile22_complete_shared_power_containment(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner_for_layout(
        schedule,
        false,
        FactorSchedule::CompleteSharedPowers,
        None,
        LateSwitchSupport::WitnessDifferenceSuperset,
        PcsSchedule::Arity4x4,
        true,
        RankLayout::AtomicV3,
    )
}

/// Exact frozen raw/sumcheck/PCS and literal physical/legal direct-sum replay
/// for the zero-width shared degree-cover schedule.  The replay continues
/// after an ordinary sumcheck deficit so a red result remains fully labelled.
pub fn probe_atomic_state_only_profile22_shared_degree_cover_containment(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner_for_layout_and_delta_and_projection(
        schedule,
        false,
        FactorSchedule::SharedDegreesZeroToTwentyFive,
        None,
        LateSwitchSupport::WitnessDifferenceSuperset,
        PcsSchedule::Arity4x4,
        true,
        RankLayout::AtomicV3,
        None,
        None,
        None,
        None,
        None,
        true,
        None,
    )
}

/// Literal physical/legal direct-sum replay for the same-lane G enrichment.
/// Callers should run the cheaper root-neutral gate first.
pub fn probe_atomic_state_only_profile22_g_add_shared_power_containment(
    schedule: &StateOnlyTranscriptScheduleResult,
    exponent: usize,
    coefficient: M31,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    if exponent > 26 || coefficient == M31::ZERO {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    check_state_only_complete_hiding_rank_inner_for_layout_and_delta_and_projection(
        schedule,
        false,
        FactorSchedule::ExplicitGAddSharedPower {
            exponent: exponent as u8,
            coefficient,
        },
        None,
        LateSwitchSupport::WitnessDifferenceSuperset,
        PcsSchedule::Arity4x4,
        true,
        RankLayout::AtomicV3,
        None,
        None,
        None,
        None,
        None,
        true,
        None,
    )
}

/// Zero-width host diagnostic for deterministic distinct dense-linear factor
/// families on the existing 26 M31 lanes and one QM31 G lane.  The exact raw
/// openings are quotiented before masked-sumcheck rank is measured.  The
/// replay deliberately continues after a deficient sumcheck image so the
/// same result also reports exact physical and legal direct-sum containment.
/// Production factors, proof bytes, transcript, gamma positions, and layout
/// fingerprint are untouched.
pub fn probe_atomic_state_only_profile22_distinct_linear_containment(
    schedule: &StateOnlyTranscriptScheduleResult,
    assignment: DistinctLinearAssignment,
    g_factor: DistinctLinearGFactor,
    prefix_m31_lanes: usize,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    if prefix_m31_lanes > DISTINCT_LINEAR_M31_LANES {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    check_state_only_complete_hiding_rank_inner_for_layout_and_delta_and_projection(
        schedule,
        false,
        FactorSchedule::DistinctLinear {
            assignment,
            g_factor,
            prefix_m31_lanes: prefix_m31_lanes as u8,
        },
        None,
        LateSwitchSupport::WitnessDifferenceSuperset,
        PcsSchedule::Arity4x4,
        true,
        RankLayout::AtomicV3,
        None,
        None,
        None,
        None,
        None,
        true,
        None,
    )
}

/// Exact source-level diagnostic for the profile-22 no-source translation.
/// It replaces the PCS continuation by the canonical copy-inactive-balanced
/// gamma-combined root message.  A full root-message image after quotienting
/// separate raw openings and the legal masked-sumcheck wire is a sufficient,
/// schedule-independent bridge to every later linear PCS/fold/OOD value.
///
/// This is a host research gate only.  It does not alter the proof wire or
/// verifier acceptance predicate.
pub fn probe_atomic_state_only_profile22_root_neutral_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner_for_layout(
        schedule,
        false,
        FactorSchedule::FullSharedLinear,
        None,
        LateSwitchSupport::WitnessDifferenceSuperset,
        PcsSchedule::RootMessage,
        true,
        RankLayout::AtomicV3,
    )
}

/// Exact conservative hiding-rank replay for the production V6 one-fold
/// shape: atomic-v3 mask layout, the frozen production factor schedule,
/// sixteen four-symbol layer-zero openings on the log-20 circle domain, and
/// the complete gamma-combined 1024-element root message.  Spanning this
/// target is sufficient for every later linear fold/final projection.
///
/// The report deliberately retains both ambient and same-statement witness
/// containment fields.  Callers must use the protocol-coupled containment
/// booleans for the HVZK gate; an ambient deficit is not silently promoted to
/// a proof failure or success.
pub fn probe_v6_onefold_atomic_root_message_hiding_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    if schedule.query_count != 16 {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    check_state_only_complete_hiding_rank_inner_for_layout(
        schedule,
        false,
        FactorSchedule::Production,
        None,
        LateSwitchSupport::WitnessDifferenceSuperset,
        PcsSchedule::RootMessageV6Log20,
        true,
        RankLayout::AtomicV3,
    )
}

/// Project one concrete atomic-v3 semantic-trace difference and its exact
/// unmasked degree-27 sumcheck-observation difference through the same frozen
/// q16 mask quotient used by the conservative witness audit.
///
/// `semantic_columns` is column-major and must contain sixteen 1024-element
/// M31 columns. `sumcheck_observations` uses the production serialization:
/// the initial QM31 claim followed by each round's constant coefficient and
/// coefficients 2 through 27, for 271 QM31 values total. The caller supplies
/// the unmasked `F` difference; this hook applies the frozen transcript's
/// `eta` internally, matching the production `H + eta*F` oracle.
pub fn project_atomic_state_only_profile21_witness_difference(
    schedule: &StateOnlyTranscriptScheduleResult,
    semantic_columns: &[Vec<M31>],
    sumcheck_observations: &[QM31],
) -> Result<WitnessDifferenceProjectionReport, StateOnlyHidingRankGateError> {
    let report = check_state_only_complete_hiding_rank_inner_for_layout_and_delta_and_projection(
        schedule,
        false,
        FactorSchedule::FullSharedLinear,
        None,
        LateSwitchSupport::WitnessDifferenceSuperset,
        PcsSchedule::Arity4x4,
        true,
        RankLayout::AtomicV3,
        None,
        Some(WitnessDifferenceProjectionInput {
            semantic_columns: semantic_columns.to_vec(),
            sumcheck_observations: sumcheck_observations.to_vec(),
        }),
        None,
        None,
        None,
        false,
        None,
    )?;
    report
        .witness_difference_projection
        .ok_or(StateOnlyHidingRankGateError::Layout)
}

/// Atomic-v3 A/B for one extra full-domain QM31 C2 mask lane under the
/// selected shared-factor schedule. The lane has its own raw/three-point
/// openings, contributes zero to zerocheck, and enters the combined PCS word
/// at the next gamma power. This is a rank diagnostic only; it does not alter
/// the production wire.
pub fn probe_atomic_state_only_full_shared_tail_qm31_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner_for_layout(
        schedule,
        true,
        FactorSchedule::FullSharedLinear,
        None,
        LateSwitchSupport::None,
        PcsSchedule::Arity4x4,
        true,
        RankLayout::AtomicV3,
    )
}

/// Exact joint raw/sumcheck/PCS and conservative semantic-containment probe
/// for one additional full-domain QM31 G2 lane at gamma exponent 28. Unlike
/// the historical zero-factor tail, this lane participates in zerocheck with
/// a nonzero degree-at-most-26 factor.
pub fn probe_atomic_state_only_profile21_g2_mask_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
    factor: TailQm31MaskFactor,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner_for_layout_and_delta_and_projection(
        schedule,
        false,
        FactorSchedule::FullSharedLinear,
        None,
        LateSwitchSupport::WitnessDifferenceSuperset,
        PcsSchedule::Arity4x4,
        true,
        RankLayout::AtomicV3,
        None,
        None,
        Some(core::slice::from_ref(&factor)),
        None,
        None,
        false,
        None,
    )
}

/// Bounded multi-lane generalization of the preceding G2 diagnostic.
///
/// Every caller-supplied lane is a separate full-domain QM31 table with its
/// own raw opening block.  The lanes enter the combined root word at
/// consecutive powers `gamma^28, gamma^29, ...`; their explicit zerocheck
/// factors must have degree at most 26.  Nothing in this function changes a
/// serializer, transcript tag, verifier, or production factor fingerprint.
pub fn probe_atomic_state_only_profile22_multi_g_mask_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
    factors: &[TailQm31MaskFactor],
) -> Result<StateOnlyMultiQm31LaneProbeReport, StateOnlyHidingRankGateError> {
    const MAX_BOUNDED_LANES: usize = 27;
    if factors.is_empty()
        || factors.len() > MAX_BOUNDED_LANES
        || factors.iter().any(|factor| factor.degree() > 26)
    {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let started = Instant::now();
    let mut prefix_ranks = Vec::new();
    let replay = check_state_only_complete_hiding_rank_inner_for_layout_and_delta_and_projection(
        schedule,
        false,
        FactorSchedule::FullSharedLinear,
        None,
        LateSwitchSupport::WitnessDifferenceSuperset,
        PcsSchedule::Arity4x4,
        true,
        RankLayout::AtomicV3,
        None,
        None,
        Some(factors),
        None,
        Some(&mut prefix_ranks),
        false,
        None,
    );
    let full = match replay {
        Ok(report) => Some(report),
        Err(StateOnlyHidingRankGateError::MaskedSumcheckRank { got, want }) => {
            if want != MASK_SUMCHECK_QUOTIENT_M31 || prefix_ranks.last().copied() != Some(got) {
                return Err(StateOnlyHidingRankGateError::Layout);
            }
            None
        }
        Err(error) => return Err(error),
    };
    if prefix_ranks.len() != factors.len() + 1 {
        return Err(StateOnlyHidingRankGateError::Layout);
    }
    let minimum_complete_prefix_lanes = prefix_ranks
        .iter()
        .position(|&rank| rank == MASK_SUMCHECK_QUOTIENT_M31);
    let (
        joint_pcs_rank_m31,
        joint_pcs_declared_rank_m31,
        physical_augmented_rank_m31,
        legal_augmented_rank_m31,
        physical_contained,
        legal_contained,
    ) = if let Some(report) = &full {
        (
            Some(report.joint_pcs_rank),
            Some(report.joint_pcs_declared_rank),
            Some(report.witness_semantic_superset_rank),
            Some(report.witness_legal_sumcheck_rank),
            Some(report.joint_pcs_rank == report.witness_semantic_superset_rank),
            Some(report.joint_pcs_rank == report.witness_legal_sumcheck_rank),
        )
    } else {
        (None, None, None, None, None, None)
    };
    let first_tail_exponent =
        STATE_ONLY_HIDING_C1_COLUMNS + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS + 2;
    Ok(StateOnlyMultiQm31LaneProbeReport {
        factor_descriptions: factors.iter().map(|factor| factor.description()).collect(),
        factor_degrees: factors.iter().map(|factor| factor.degree()).collect(),
        gamma_exponents: (first_tail_exponent..first_tail_exponent + factors.len()).collect(),
        prefix_masked_sumcheck_ranks_m31: prefix_ranks,
        masked_sumcheck_target_m31: MASK_SUMCHECK_QUOTIENT_M31,
        minimum_complete_prefix_lanes,
        complete_full_view_replayed: full.is_some(),
        joint_pcs_rank_m31,
        joint_pcs_declared_rank_m31,
        physical_augmented_rank_m31,
        legal_augmented_rank_m31,
        physical_contained,
        legal_contained,
        elapsed_millis: started.elapsed().as_millis(),
    })
}

/// Atomic-v3 complete-view quotient with the selected external slot-zero
/// masked switch. This remains a rank gate, not a production hiding claim.
pub fn probe_atomic_state_only_masked_single_switch_joint_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner_for_layout(
        schedule,
        false,
        FactorSchedule::FullSharedLinear,
        None,
        LateSwitchSupport::MaskedSlotZeroSingleCodeword,
        PcsSchedule::Arity4x4,
        false,
        RankLayout::AtomicV3,
    )
}

/// Atomic-v3 complete-view quotient on the literal profile-21 transcript.
///
/// Unlike the legacy diagnostic above, this path uses profile 21's sampled
/// nonzero `delta`; it must not substitute the base prefix's unrelated `eta`.
pub fn probe_atomic_state_only_profile21_masked_single_switch_joint_rank(
    schedule: &StateOnlyProfile21TranscriptScheduleResult,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner_for_layout_and_delta(
        &schedule.base,
        false,
        FactorSchedule::FullSharedLinear,
        None,
        LateSwitchSupport::MaskedSlotZeroSingleCodeword,
        PcsSchedule::Arity4x4,
        false,
        RankLayout::AtomicV3,
        Some(schedule.delta),
    )
}

/// Diagnostic profile-21 rank replay for the high-coefficient p0 bridge.
///
/// This changes the switch basis but not the mask/source dimension.  It is a
/// candidate for removing the current complement's discrete-query gap; it is
/// not part of the production transcript until the source/relation splice is
/// separately frozen and differential-tested.
pub fn probe_atomic_state_only_profile21_masked_high_switch_joint_rank(
    schedule: &StateOnlyProfile21TranscriptScheduleResult,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner_for_layout_and_delta(
        &schedule.base,
        false,
        FactorSchedule::FullSharedLinear,
        None,
        LateSwitchSupport::MaskedHighCoefficientSingleCodeword,
        PcsSchedule::Arity4x4,
        false,
        RankLayout::AtomicV3,
        Some(schedule.delta),
    )
}

/// Production-neutral exact rank replay for the minimal semantic-only
/// high-switch candidate.
///
/// The old-view source remains the known p0 repair coordinate at natural
/// coefficient 18 / row 72.  Only that one message coordinate is switched;
/// sixteen `(x^2+1)x^j` directions provide a universally q-MDS randomness
/// block.  This probe asks only whether its one-QM31 conditioned PCS image
/// closes the conservative 712 -> 716 semantic/legal-sumcheck gap.
pub fn probe_atomic_state_only_profile21_semantic_high_switch_joint_rank(
    schedule: &StateOnlyProfile21TranscriptScheduleResult,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner_for_layout_and_delta(
        &schedule.base,
        false,
        FactorSchedule::FullSharedLinear,
        None,
        LateSwitchSupport::MaskedSemanticHighSingleCodeword,
        PcsSchedule::Arity4x4,
        true,
        RankLayout::AtomicV3,
        Some(schedule.delta),
    )
}

/// Production-shaped shared-C2 companion to the folded semantic-high
/// control.  The conditioned quotient uses all four authenticated root-zero
/// X/F symbols per query and carries the physical row-72 and root-one
/// coefficient-zero sources.
pub fn probe_atomic_state_only_profile21_semantic_high_shared_c2_switch_joint_rank(
    schedule: &StateOnlyProfile21TranscriptScheduleResult,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner_for_layout_and_delta(
        &schedule.base,
        false,
        FactorSchedule::FullSharedLinear,
        None,
        LateSwitchSupport::MaskedSemanticHighSharedC2SingleCodeword,
        PcsSchedule::Arity4x4,
        true,
        RankLayout::AtomicV3,
        Some(schedule.delta),
    )
}

/// Production-neutral strict full-View replay for the reduced bound B18
/// switch.  Unlike the older d17 diagnostic, the authenticated source basis
/// and the carried old-view basis are the same natural-B18 code.
pub fn probe_atomic_state_only_profile21_semantic_natural18_shared_c2_switch_joint_rank(
    schedule: &StateOnlyProfile21TranscriptScheduleResult,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner_for_layout_and_delta(
        &schedule.base,
        false,
        FactorSchedule::FullSharedLinear,
        None,
        LateSwitchSupport::MaskedSemanticNatural18SharedC2SingleCodeword,
        PcsSchedule::Arity4x4,
        true,
        RankLayout::AtomicV3,
        Some(schedule.delta),
    )
}

/// Exact rank A/B for the physical-X gamma-lane candidate.
///
/// X is the already-committed widened-C2 source lane and is appended to the
/// main generator at exponent 28.  Its complete initial relation target is a
/// single pre-gamma public coordinate.  The target includes the copy-inactive
/// functional used by the real relation, in addition to the three scaled
/// statement-point evaluations; omitting that term would not model the
/// production relation polynomial.  This function changes no transcript or
/// verifier wire by itself.
pub fn probe_atomic_state_only_profile21_full_x_gamma_lane_joint_rank(
    schedule: &StateOnlyProfile21TranscriptScheduleResult,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner_for_layout_and_delta(
        &schedule.base,
        false,
        FactorSchedule::FullSharedLinear,
        None,
        LateSwitchSupport::MaskedFullXGammaLane,
        PcsSchedule::Arity4x4,
        false,
        RankLayout::AtomicV3,
        Some(schedule.delta),
    )
}

/// Exact uncompressed-profile gate for one lean native full root-zero C2
/// masking word. X is committed before its exact old-relation target `tX`;
/// after `tX` is bound, a fresh nonzero `epsilon` separates X as an outer PCS
/// group. The affine View exposes `tX` and all four authenticated X symbols at
/// each q16 query—the three point evaluations enter `tX` but are not separately
/// serialized, and no F/U/source-CA disclosure is present. The literal
/// direct-sum fields include the conditioned X PCS kernel before
/// physical/legal/helper target augmentation.
pub fn probe_atomic_state_only_native_full_root_x_joint_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
    epsilon: QM31,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    if epsilon == QM31::ZERO {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    check_state_only_complete_hiding_rank_inner_for_layout_and_delta(
        schedule,
        false,
        FactorSchedule::FullSharedLinear,
        None,
        LateSwitchSupport::LeanNativeFullRootX,
        PcsSchedule::Arity4x4,
        true,
        RankLayout::AtomicV3,
        Some(epsilon),
    )
}

/// Host-only negative control for the native full-X affine replay.  The
/// public `tX` row is deliberately omitted and therefore this result can
/// never authorize a proof wire or hiding claim.
pub fn probe_atomic_state_only_native_full_root_x_raw_only_control_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
    epsilon: QM31,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    if epsilon == QM31::ZERO {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    check_state_only_complete_hiding_rank_inner_for_layout_and_delta(
        schedule,
        false,
        FactorSchedule::FullSharedLinear,
        None,
        LateSwitchSupport::LeanNativeFullRootXRawOnlyControl,
        PcsSchedule::Arity4x4,
        true,
        RankLayout::AtomicV3,
        Some(epsilon),
    )
}

/// Exact semantic-containment A/B for a claim-preserving physical-X gamma
/// lane.  The complete authenticated X word, including all sixteen encoding-
/// randomness coordinates, enters W0.  The source sampler restricts X to the
/// kernel of the exact initial relation covector, so the verifier enforces
/// `L(X)=0` as part of the relation and serializes no separate target.
///
/// Conditioning on the zero equation and conditioning on a transmitted
/// value of the same linear form have the same affine rank; the distinction
/// here is causal/physical and removes the scalar from the byte model.
pub fn probe_atomic_state_only_profile21_full_x_gamma_kernel_lane_joint_rank(
    schedule: &StateOnlyProfile21TranscriptScheduleResult,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner_for_layout_and_delta(
        &schedule.base,
        false,
        FactorSchedule::FullSharedLinear,
        None,
        LateSwitchSupport::MaskedFullXGammaKernelLane,
        PcsSchedule::Arity4x4,
        true,
        RankLayout::AtomicV3,
        Some(schedule.delta),
    )
}

/// Pointwise-multiplied companion to the claim-preserving physical-X gamma
/// lane.  The authenticated source remains the complete degree-`<35` word X;
/// the main W0 lane carries `p(t)X(t)` and the enforced zero relation is the
/// exact `L(pX)=0`.  Query authentication still observes the unmultiplied X,
/// so the verifier-side local identity is `W0_X(q)=p(q)X(q)`.
pub fn probe_atomic_state_only_profile21_full_x_gamma_kernel_polynomial_joint_rank(
    schedule: &StateOnlyProfile21TranscriptScheduleResult,
    multiplier: FirstLaterXMultiplier,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner_for_layout_and_delta_and_projection(
        &schedule.base,
        false,
        FactorSchedule::FullSharedLinear,
        None,
        LateSwitchSupport::MaskedFullXGammaKernelLane,
        PcsSchedule::Arity4x4,
        true,
        RankLayout::AtomicV3,
        Some(schedule.delta),
        None,
        None,
        Some(multiplier),
        None,
        false,
        None,
    )
}

/// Exact rank A/B for translating the first-later word by `Enc(U+X)`.
///
/// The base W0 generator is unchanged.  The already-authenticated raw X/F
/// fibers are public, U is disclosed, and the serialized tau is the complete
/// post-alpha relation target of U+X.  This diagnostic therefore quotients
/// the one remaining X functional before inserting X's real W1/later PCS
/// image.
pub fn probe_atomic_state_only_profile21_full_x_first_later_joint_rank(
    schedule: &StateOnlyProfile21TranscriptScheduleResult,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner_for_layout_and_delta(
        &schedule.base,
        false,
        FactorSchedule::FullSharedLinear,
        None,
        LateSwitchSupport::MaskedFullXFirstLaterLane,
        PcsSchedule::Arity4x4,
        false,
        RankLayout::AtomicV3,
        Some(schedule.delta),
    )
}

/// Exact W1 multiplier scan for
/// `W1 = Fold(W0) + Enc(U) + p(t) Enc(X)`. The source X/F commitments, raw
/// query fibers and derived `U=F+delta X` are unchanged; tau binds
/// `L(U+pX)`. This is a production-neutral rank diagnostic.
pub fn probe_atomic_state_only_profile21_full_x_first_later_polynomial_joint_rank(
    schedule: &StateOnlyProfile21TranscriptScheduleResult,
    multiplier: FirstLaterXMultiplier,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner_for_layout_and_delta_and_projection(
        &schedule.base,
        false,
        FactorSchedule::FullSharedLinear,
        None,
        LateSwitchSupport::MaskedFullXFirstLaterLane,
        PcsSchedule::Arity4x4,
        true,
        RankLayout::AtomicV3,
        Some(schedule.delta),
        None,
        None,
        Some(multiplier),
        None,
        false,
        None,
    )
}

/// Differential tooth for the selected-query encoder used by the log-19
/// gate. It compares sparse basis entries and recursively folded q leaves to
/// the original full-word implementation on the exact supplied transcript.
pub fn check_state_only_sparse_row_map_reference(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<(), StateOnlyHidingRankGateError> {
    if schedule.query_count != 29 {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let domain_log = STATE_ONLY_LOG_ROWS + 5;
    let encoder = CircleEncoder::new_for_domain_log(domain_log);
    let indices = derive_circle_line_query_indices_for_count(
        &schedule.queries[..schedule.query_count],
        encoder.codeword_len() / FIBER_SLOTS,
    )
    .map_err(|_| StateOnlyHidingRankGateError::Shape)?;
    let mut active = [false; TRACE_ROWS];
    for &row in state_only_copy_active_rows_v4() {
        active[usize::from(row)] = true;
    }
    let inactive_dependent = (0..TRACE_ROWS)
        .find(|row| !active[*row])
        .ok_or(StateOnlyHidingRankGateError::Layout)?;
    for row in [0usize, 1, 3, 4, 8, 72, 112, 136, 1023] {
        let full = row_pcs_tail(
            &encoder,
            domain_log,
            row,
            &active,
            inactive_dependent,
            schedule,
            &indices.later,
            RankLayout::StateOnlyV4,
        )?;
        let sparse = row_pcs_tail_sparse(
            &encoder,
            domain_log,
            row,
            &active,
            inactive_dependent,
            schedule,
            &indices.later,
            RankLayout::StateOnlyV4,
        )?;
        if full != sparse {
            return Err(StateOnlyHidingRankGateError::Encoding);
        }
        let mut message = vec![M31::ZERO; TRACE_ROWS];
        message[row] = M31::ONE;
        let codeword = encoder.encode_c1_message(&message)?;
        for &query in &indices.layer0 {
            for slot in 0..FIBER_SLOTS {
                let index = FIBER_SLOTS * query as usize + slot;
                if encoder.encode_c1_basis_value(row, index)? != codeword[index] {
                    return Err(StateOnlyHidingRankGateError::Encoding);
                }
            }
        }
    }
    Ok(())
}

pub fn probe_state_only_root1_distinct_folded_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner(
        schedule,
        false,
        FactorSchedule::Production,
        None,
        LateSwitchSupport::DistinctFolded31,
        PcsSchedule::Arity4x4,
        false,
    )
}

/// Host-only A/B which materializes the coordinate-factored diagnostic as
/// ordinary M31 C1 columns, so every terminal MLE is verifier-computable.
/// `columns` is probed directly; no QM31 column is treated as four unrelated
/// terminal values.
pub fn probe_state_only_coordinate_factored_late_switch_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
    shared_linear_factors: bool,
    columns: usize,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    if columns > 8 {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    check_state_only_complete_hiding_rank_inner(
        schedule,
        false,
        if shared_linear_factors {
            FactorSchedule::FullSharedLinear
        } else {
            FactorSchedule::Production
        },
        Some(columns),
        LateSwitchSupport::StructuredSource31,
        PcsSchedule::Arity4x4,
        false,
    )
}

/// Host-only complete-view rank A/B for an unchanged arity-4 first fold and
/// one arity-8 line fold. This reinterprets an existing fixed transcript's
/// nonzero challenges; it does not define a production wire tag or BCS order.
pub fn probe_state_only_hybrid_arity8_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner(
        schedule,
        false,
        FactorSchedule::FullSharedLinear,
        None,
        LateSwitchSupport::None,
        PcsSchedule::Arity4ThenArity8,
        true,
    )
}

fn check_state_only_complete_hiding_rank_inner(
    schedule: &StateOnlyTranscriptScheduleResult,
    tail_qm31_probe: bool,
    factor_schedule: FactorSchedule,
    coordinate_factored_mask_columns: Option<usize>,
    late_switch_support: LateSwitchSupport,
    pcs_schedule: PcsSchedule,
    allow_ambient_deficit: bool,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner_for_layout(
        schedule,
        tail_qm31_probe,
        factor_schedule,
        coordinate_factored_mask_columns,
        late_switch_support,
        pcs_schedule,
        allow_ambient_deficit,
        RankLayout::StateOnlyV4,
    )
}

fn check_state_only_complete_hiding_rank_inner_for_layout(
    schedule: &StateOnlyTranscriptScheduleResult,
    tail_qm31_probe: bool,
    factor_schedule: FactorSchedule,
    coordinate_factored_mask_columns: Option<usize>,
    late_switch_support: LateSwitchSupport,
    pcs_schedule: PcsSchedule,
    allow_ambient_deficit: bool,
    layout: RankLayout,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner_for_layout_and_delta(
        schedule,
        tail_qm31_probe,
        factor_schedule,
        coordinate_factored_mask_columns,
        late_switch_support,
        pcs_schedule,
        allow_ambient_deficit,
        layout,
        None,
    )
}

#[allow(clippy::too_many_arguments)]
fn check_state_only_complete_hiding_rank_inner_for_layout_and_delta(
    schedule: &StateOnlyTranscriptScheduleResult,
    tail_qm31_probe: bool,
    factor_schedule: FactorSchedule,
    coordinate_factored_mask_columns: Option<usize>,
    late_switch_support: LateSwitchSupport,
    pcs_schedule: PcsSchedule,
    allow_ambient_deficit: bool,
    layout: RankLayout,
    selected_late_switch_delta: Option<QM31>,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    check_state_only_complete_hiding_rank_inner_for_layout_and_delta_and_projection(
        schedule,
        tail_qm31_probe,
        factor_schedule,
        coordinate_factored_mask_columns,
        late_switch_support,
        pcs_schedule,
        allow_ambient_deficit,
        layout,
        selected_late_switch_delta,
        None,
        None,
        None,
        None,
        false,
        None,
    )
}

#[allow(clippy::too_many_arguments)]
fn check_state_only_complete_hiding_rank_inner_for_layout_and_delta_and_projection(
    schedule: &StateOnlyTranscriptScheduleResult,
    tail_qm31_probe: bool,
    factor_schedule: FactorSchedule,
    coordinate_factored_mask_columns: Option<usize>,
    late_switch_support: LateSwitchSupport,
    pcs_schedule: PcsSchedule,
    allow_ambient_deficit: bool,
    layout: RankLayout,
    selected_late_switch_delta: Option<QM31>,
    witness_projection_input: Option<WitnessDifferenceProjectionInput>,
    tail_qm31_mask_factors_override: Option<&[TailQm31MaskFactor]>,
    first_later_x_multiplier_override: Option<FirstLaterXMultiplier>,
    mut tail_prefix_sumcheck_ranks_out: Option<&mut Vec<usize>>,
    continue_after_sumcheck_deficit: bool,
    weighted_inactive_sum: Option<WeightedInactiveSumConfig>,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    let started = Instant::now();
    if weighted_inactive_sum.is_some_and(|config| config.delta == QM31::ZERO)
        || weighted_inactive_sum.is_some()
            && (tail_qm31_probe
                || tail_qm31_mask_factors_override.is_some()
                || coordinate_factored_mask_columns.is_some()
                || late_switch_support != LateSwitchSupport::WitnessDifferenceSuperset)
    {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    if tail_qm31_probe && tail_qm31_mask_factors_override.is_some() {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let single_tail_factor = [TailQm31MaskFactor::Zero];
    let tail_qm31_mask_factors: &[TailQm31MaskFactor] =
        if let Some(factors) = tail_qm31_mask_factors_override {
            factors
        } else if tail_qm31_probe {
            &single_tail_factor[..]
        } else {
            &[]
        };
    if tail_qm31_mask_factors
        .iter()
        .any(|factor| factor.degree() > 26)
    {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    if first_later_x_multiplier_override.is_some()
        && late_switch_support != LateSwitchSupport::MaskedFullXFirstLaterLane
        && late_switch_support != LateSwitchSupport::MaskedFullXGammaKernelLane
    {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let first_later_x_multiplier =
        first_later_x_multiplier_override.unwrap_or(FirstLaterXMultiplier::One);
    let first_later_x_multiplier_coefficients = first_later_x_multiplier
        .ordinary_coefficients()
        .ok_or(StateOnlyHidingRankGateError::Shape)?;
    let first_later_x_multiplier_degree = first_later_x_multiplier_coefficients.len() - 1;
    let witness_difference_probe = late_switch_support
        == LateSwitchSupport::WitnessDifferenceSuperset
        || late_switch_support == LateSwitchSupport::MaskedSemanticHighSingleCodeword
        || late_switch_support == LateSwitchSupport::MaskedSemanticHighSharedC2SingleCodeword
        || late_switch_support == LateSwitchSupport::MaskedSemanticNatural18SharedC2SingleCodeword
        || late_switch_support == LateSwitchSupport::MaskedFullXGammaKernelLane
        || late_switch_support == LateSwitchSupport::LeanNativeFullRootX
        || late_switch_support == LateSwitchSupport::LeanNativeFullRootXRawOnlyControl
        || first_later_x_multiplier_override.is_some();
    let late_switch_probe = late_switch_support != LateSwitchSupport::None
        && late_switch_support != LateSwitchSupport::WitnessDifferenceSuperset;
    if schedule.query_count == 0
        || schedule.query_count > schedule.queries.len()
        || schedule.prefix.z.len() != STATE_ONLY_HIDING_SUMCHECK_ROUNDS
    {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let domain_log = if pcs_schedule == PcsSchedule::RootMessageV6Log20 {
        if schedule.query_count != 16 {
            return Err(StateOnlyHidingRankGateError::Shape);
        }
        STATE_ONLY_LOG_ROWS + 10
    } else {
        STATE_ONLY_LOG_ROWS
            + if schedule.query_count == 36 {
                4
            } else if schedule.query_count == 29 {
                5
            } else if schedule.query_count == 16 {
                9
            } else {
                return Err(StateOnlyHidingRankGateError::Shape);
            }
    };
    let encoder = CircleEncoder::new_for_domain_log(domain_log);
    let rows = row_public_maps(&encoder, domain_log, schedule, pcs_schedule, layout)?;
    let layer0_m31 = rows[0].layer0_m31.len();
    let c1_raw_m31 = layer0_m31 + 12;
    let g_raw_m31 = 4 * (layer0_m31 + 3);
    let pcs_tail_qm31 = rows[0].pcs_tail.len();
    let h_raw_qm31 = layer0_m31 + 3;
    let joint_pcs_m31 = 4 * (h_raw_qm31 + pcs_tail_qm31);
    let sc_m31 = 4 * STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS;
    let aux_m31 = sc_m31 + joint_pcs_m31;
    let lagrange = lagrange_basis();
    let active_rows = rank_active_rows(layout);
    let mut active = [false; TRACE_ROWS];
    for &row in active_rows {
        active[usize::from(row)] = true;
    }
    let inactive = (0..TRACE_ROWS)
        .filter(|row| !active[*row])
        .collect::<Vec<_>>();
    let global_dependent = inactive[0];
    let mask_only_columns =
        coordinate_factored_mask_columns.unwrap_or(STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS);
    let h_generator_index = STATE_ONLY_HIDING_C1_COLUMNS + mask_only_columns;
    let g_generator_index = h_generator_index + 1;
    let powers = (0..=g_generator_index + tail_qm31_mask_factors.len())
        .map(|column| gamma_power(schedule.prefix.gamma, column))
        .collect::<Vec<_>>();
    // In the zero-width weighted inactive-sum probe, the ordinary combined
    // PCS word is S_gamma + delta*U_gamma.  S is semantic C1 plus H; U is
    // every mask-only C1 column plus G.  This scalar never touches separate
    // raw openings or masked-sumcheck observations.
    let semantic_pcs_delta = weighted_inactive_sum.map_or(QM31::ONE, |config| match config.group {
        WeightedInactiveSumGroup::MaskOnly | WeightedInactiveSumGroup::SemanticPlusMaskOnly => {
            QM31::ONE
        }
        WeightedInactiveSumGroup::Semantic => config.delta,
    });
    let u_pcs_delta = weighted_inactive_sum.map_or(QM31::ONE, |config| match config.group {
        WeightedInactiveSumGroup::MaskOnly | WeightedInactiveSumGroup::SemanticPlusMaskOnly => {
            config.delta
        }
        WeightedInactiveSumGroup::Semantic => QM31::ONE,
    });
    let mut sumcheck_kernel_images = Vec::new();
    let mut sumcheck_kernel_source_ids = Vec::new();
    let mut basis_columns = 0usize;
    let mut semantic_mask_basis_m31 = 0usize;
    let mut semantic_raw_kernel_m31 = 0usize;
    let mut mask_only_basis_m31 = 0usize;
    let mut mask_only_raw_kernel_m31 = 0usize;
    let mut weighted_inactive_sum_sources = Vec::new();
    let mut weighted_aggregate_claim_rank_m31 = 0usize;
    let mut weighted_aggregate_claim_echelon = None;
    let mut raw_minor_sources = Vec::new();
    let mut raw_minor_rows = Vec::new();
    let mut raw_minor_values = Vec::new();
    let mut raw_block_offset = 0usize;
    let mut semantic_raw_echelons = Vec::with_capacity(STATE_ONLY_HIDING_C1_COLUMNS);
    let mut semantic_inactive_dependents = Vec::with_capacity(STATE_ONLY_HIDING_C1_COLUMNS);
    let mut semantic_sumcheck_observations = Vec::with_capacity(STATE_ONLY_HIDING_C1_COLUMNS);

    let cells = match layout {
        RankLayout::StateOnlyV4 => state_only_relation_free_mask_cells_v4()
            .map_err(|_| StateOnlyHidingRankGateError::Layout)?,
        RankLayout::AtomicV3 => atomic_state_only_relation_free_mask_cells_v3()
            .map_err(|_| StateOnlyHidingRankGateError::Layout)?,
    };
    let mut cells_by_column = vec![Vec::new(); STATE_ONLY_HIDING_C1_COLUMNS];
    for cell in cells {
        cells_by_column[usize::from(cell.column)].push(usize::from(cell.row));
    }
    for (column, cells) in cells_by_column.iter().enumerate() {
        let dependent = cells
            .iter()
            .copied()
            .filter(|row| !active[*row])
            .last()
            .ok_or(StateOnlyHidingRankGateError::Layout)?;
        let observations = (0..TRACE_ROWS)
            .map(|row| {
                mask_sumcheck_observations(
                    row,
                    &schedule.prefix.z,
                    &lagrange,
                    MaskFactor::Semantic(column),
                    factor_schedule,
                    coordinate_factored_mask_columns,
                )
            })
            .collect::<Vec<_>>();
        let mut raw = CarryEchelon::new(c1_raw_m31);
        let mut column_basis = 0usize;
        for &row in cells {
            if row == dependent {
                continue;
            }
            let subtract = (!active[row]).then_some(dependent);
            let raw_image = c1_raw_difference(&rows, row, subtract);
            let aux = scaled_aux_difference(
                &rows,
                row,
                subtract,
                &observations,
                QM31::ONE,
                semantic_pcs_delta.mul(powers[column]),
                4 * h_raw_qm31,
                joint_pcs_m31,
            );
            debug_assert_eq!(aux.len(), aux_m31);
            let source_id = basis_columns;
            basis_columns += 1;
            column_basis += 1;
            match raw.reduce_with_pivot(raw_image, aux) {
                CarryReduction::Pivot { row, value } => {
                    raw_minor_sources.push(source_id);
                    raw_minor_rows.push(raw_block_offset + row);
                    raw_minor_values.push(value);
                }
                CarryReduction::Kernel(kernel) => {
                    sumcheck_kernel_images.push(kernel);
                    sumcheck_kernel_source_ids.push(source_id);
                }
            }
        }
        semantic_mask_basis_m31 += column_basis;
        semantic_raw_kernel_m31 += column_basis - raw.rank;
        if raw.rank != c1_raw_m31 {
            return Err(StateOnlyHidingRankGateError::RawC1Rank {
                column,
                got: raw.rank,
                want: c1_raw_m31,
            });
        }
        if weighted_inactive_sum.is_some_and(|config| {
            matches!(
                config.group,
                WeightedInactiveSumGroup::Semantic | WeightedInactiveSumGroup::SemanticPlusMaskOnly
            ) && config.selected_columns & (1u32 << column) != 0
        }) {
            // Add the omitted relation-free inactive dependent as one new
            // semantic source.  All semantic C1 and H PCS images share the
            // fresh group scalar; raw and zerocheck observations do not.
            let source_id = basis_columns;
            basis_columns += 1;
            semantic_mask_basis_m31 += 1;
            semantic_raw_kernel_m31 += 1;
            let raw_image = c1_raw_difference(&rows, dependent, None);
            let aux = scaled_aux_difference(
                &rows,
                dependent,
                None,
                &observations,
                QM31::ONE,
                semantic_pcs_delta.mul(powers[column]),
                4 * h_raw_qm31,
                joint_pcs_m31,
            );
            let post_raw = raw
                .quotient_existing(raw_image, aux)
                .ok_or(StateOnlyHidingRankGateError::Layout)?;
            weighted_inactive_sum_sources.push((
                source_id,
                qm31_coordinates(powers[column]).to_vec(),
                post_raw,
            ));
        }
        semantic_raw_echelons.push(raw);
        semantic_inactive_dependents.push(dependent);
        semantic_sumcheck_observations.push(observations);
        raw_block_offset += c1_raw_m31;
    }
    let semantic_kernel_end = sumcheck_kernel_images.len();

    let mut mask_kernel_ends = Vec::with_capacity(mask_only_columns);
    for mask_column in 0..mask_only_columns {
        let observations = (0..TRACE_ROWS)
            .map(|row| {
                mask_sumcheck_observations(
                    row,
                    &schedule.prefix.z,
                    &lagrange,
                    MaskFactor::MaskOnly(mask_column),
                    factor_schedule,
                    coordinate_factored_mask_columns,
                )
            })
            .collect::<Vec<_>>();
        let generator = STATE_ONLY_HIDING_C1_COLUMNS + mask_column;
        let mut raw = CarryEchelon::new(c1_raw_m31);
        let mut column_basis = 0usize;
        for row in 0..TRACE_ROWS {
            if row == global_dependent {
                continue;
            }
            let subtract = (!active[row]).then_some(global_dependent);
            let raw_image = c1_raw_difference(&rows, row, subtract);
            let aux = scaled_aux_difference(
                &rows,
                row,
                subtract,
                &observations,
                QM31::ONE,
                u_pcs_delta.mul(powers[generator]),
                4 * h_raw_qm31,
                joint_pcs_m31,
            );
            let source_id = basis_columns;
            basis_columns += 1;
            column_basis += 1;
            match raw.reduce_with_pivot(raw_image, aux) {
                CarryReduction::Pivot { row, value } => {
                    raw_minor_sources.push(source_id);
                    raw_minor_rows.push(raw_block_offset + row);
                    raw_minor_values.push(value);
                }
                CarryReduction::Kernel(kernel) => {
                    sumcheck_kernel_images.push(kernel);
                    sumcheck_kernel_source_ids.push(source_id);
                }
            }
        }
        mask_only_basis_m31 += column_basis;
        mask_only_raw_kernel_m31 += column_basis - raw.rank;
        if raw.rank != c1_raw_m31 {
            return Err(StateOnlyHidingRankGateError::RawC1Rank {
                column: generator,
                got: raw.rank,
                want: c1_raw_m31,
            });
        }
        if weighted_inactive_sum.is_some_and(|config| {
            let selected_bit =
                if matches!(config.group, WeightedInactiveSumGroup::SemanticPlusMaskOnly) {
                    STATE_ONLY_HIDING_C1_COLUMNS + mask_column
                } else {
                    mask_column
                };
            matches!(
                config.group,
                WeightedInactiveSumGroup::MaskOnly | WeightedInactiveSumGroup::SemanticPlusMaskOnly
            ) && config.selected_columns & (1u32 << selected_bit) != 0
        }) {
            // Relax the column's inactive-sum-zero constraint by adding the
            // omitted dependent-row basis direction.  Its existing raw and
            // three-point image is quotiented against the frozen balanced
            // source echelon.  A_U is sampled before delta, so its claim row
            // uses gamma^generator while its PCS carry uses delta*gamma^generator.
            let source_id = basis_columns;
            basis_columns += 1;
            mask_only_basis_m31 += 1;
            mask_only_raw_kernel_m31 += 1;
            let raw_image = c1_raw_difference(&rows, global_dependent, None);
            let aux = scaled_aux_difference(
                &rows,
                global_dependent,
                None,
                &observations,
                QM31::ONE,
                u_pcs_delta.mul(powers[generator]),
                4 * h_raw_qm31,
                joint_pcs_m31,
            );
            let post_raw = raw
                .quotient_existing(raw_image, aux)
                .ok_or(StateOnlyHidingRankGateError::Layout)?;
            weighted_inactive_sum_sources.push((
                source_id,
                qm31_coordinates(powers[generator]).to_vec(),
                post_raw,
            ));
        }
        raw_block_offset += c1_raw_m31;
        mask_kernel_ends.push(sumcheck_kernel_images.len());
    }

    if let Some(config) = weighted_inactive_sum {
        let selected_columns = config.selected_columns.count_ones() as usize;
        if (matches!(
            config.group,
            WeightedInactiveSumGroup::MaskOnly | WeightedInactiveSumGroup::SemanticPlusMaskOnly
        ) && mask_only_columns < STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS)
            || weighted_inactive_sum_sources.len() != selected_columns
        {
            return Err(StateOnlyHidingRankGateError::Shape);
        }
        // Condition the eight added sources on their sole public claim
        // A_U=sum gamma^(16+j)*inactive_sum(U_j).  Exactly four claim pivots
        // and four remaining source directions are required.
        let kernel_start = sumcheck_kernel_images.len();
        let mut aggregate_claim = CarryEchelon::new(4);
        for (source_id, claim, carry) in weighted_inactive_sum_sources {
            if let CarryReduction::Kernel(kernel) = aggregate_claim.reduce_with_pivot(claim, carry)
            {
                sumcheck_kernel_images.push(kernel);
                sumcheck_kernel_source_ids.push(source_id);
            }
        }
        if aggregate_claim.rank != 4
            || sumcheck_kernel_images.len() - kernel_start != selected_columns - 4
        {
            return Err(StateOnlyHidingRankGateError::Layout);
        }
        weighted_aggregate_claim_rank_m31 = aggregate_claim.rank;
        weighted_aggregate_claim_echelon = Some(aggregate_claim);
    }

    let g_kernel_start = sumcheck_kernel_images.len();
    let g_observations = (0..TRACE_ROWS)
        .map(|row| {
            mask_sumcheck_observations(
                row,
                &schedule.prefix.z,
                &lagrange,
                MaskFactor::ExplicitG,
                factor_schedule,
                coordinate_factored_mask_columns,
            )
        })
        .collect::<Vec<_>>();
    let mut g_raw = CarryEchelon::new(g_raw_m31);
    let mut g_mask_basis_m31 = 0usize;
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for row in 0..TRACE_ROWS {
            if row == global_dependent {
                continue;
            }
            let subtract = (!active[row]).then_some(global_dependent);
            let raw_image = qm31_raw_difference(&rows, row, subtract, basis);
            let aux = scaled_aux_difference(
                &rows,
                row,
                subtract,
                &g_observations,
                basis,
                basis.mul(u_pcs_delta.mul(powers[g_generator_index])),
                4 * h_raw_qm31,
                joint_pcs_m31,
            );
            let source_id = basis_columns;
            basis_columns += 1;
            g_mask_basis_m31 += 1;
            match g_raw.reduce_with_pivot(raw_image, aux) {
                CarryReduction::Pivot { row, value } => {
                    raw_minor_sources.push(source_id);
                    raw_minor_rows.push(raw_block_offset + row);
                    raw_minor_values.push(value);
                }
                CarryReduction::Kernel(kernel) => {
                    sumcheck_kernel_images.push(kernel);
                    sumcheck_kernel_source_ids.push(source_id);
                }
            }
        }
    }
    if g_raw.rank != g_raw_m31 {
        return Err(StateOnlyHidingRankGateError::RawGRank {
            got: g_raw.rank,
            want: g_raw_m31,
        });
    }
    let g_raw_kernel_m31 = g_mask_basis_m31 - g_raw.rank;
    let g_kernel_end = sumcheck_kernel_images.len();
    raw_block_offset += g_raw_m31;

    let mut tail_qm31_basis_m31 = 0usize;
    let mut tail_qm31_raw_kernel_m31 = 0usize;
    let mut tail_kernel_ends = Vec::with_capacity(tail_qm31_mask_factors.len());
    for (tail_lane, &tail_qm31_mask_factor) in tail_qm31_mask_factors.iter().enumerate() {
        let lane_basis_start = tail_qm31_basis_m31;
        let tail_observations = (0..TRACE_ROWS)
            .map(|row| {
                tail_qm31_sumcheck_observations(
                    row,
                    &schedule.prefix.z,
                    &lagrange,
                    tail_qm31_mask_factor,
                )
            })
            .collect::<Vec<_>>();
        let mut tail_raw = CarryEchelon::new(g_raw_m31);
        for coordinate in 0..4 {
            let basis = state_only_mask_tower_basis(coordinate);
            for row in 0..TRACE_ROWS {
                if row == global_dependent {
                    continue;
                }
                let subtract = (!active[row]).then_some(global_dependent);
                let raw_image = qm31_raw_difference(&rows, row, subtract, basis);
                let aux = scaled_aux_difference(
                    &rows,
                    row,
                    subtract,
                    &tail_observations,
                    basis,
                    basis.mul(powers[g_generator_index + 1 + tail_lane]),
                    4 * h_raw_qm31,
                    joint_pcs_m31,
                );
                let source_id = basis_columns;
                basis_columns += 1;
                tail_qm31_basis_m31 += 1;
                match tail_raw.reduce_with_pivot(raw_image, aux) {
                    CarryReduction::Pivot { row, value } => {
                        raw_minor_sources.push(source_id);
                        raw_minor_rows.push(raw_block_offset + row);
                        raw_minor_values.push(value);
                    }
                    CarryReduction::Kernel(kernel) => {
                        sumcheck_kernel_images.push(kernel);
                        sumcheck_kernel_source_ids.push(source_id);
                    }
                }
            }
        }
        if tail_raw.rank != g_raw_m31 {
            return Err(StateOnlyHidingRankGateError::RawGRank {
                got: tail_raw.rank,
                want: g_raw_m31,
            });
        }
        tail_qm31_raw_kernel_m31 += (tail_qm31_basis_m31 - lane_basis_start) - tail_raw.rank;
        tail_kernel_ends.push(sumcheck_kernel_images.len());
        raw_block_offset += g_raw_m31;
    }

    let terminal_coefficients = compressed_mask_sumcheck_terminal_coefficients(&schedule.prefix.z);
    let terminal_dependent = (1..terminal_coefficients.len())
        .rev()
        .find(|&observation| terminal_coefficients[observation] != QM31::ZERO)
        .ok_or(StateOnlyHidingRankGateError::Relation)?;
    let terminal_dependent_inverse = terminal_coefficients[terminal_dependent].inv();
    let mut terminal_coefficients_m31 = Vec::with_capacity(4 * terminal_coefficients.len());
    append_qm31_coordinates(
        &mut terminal_coefficients_m31,
        terminal_coefficients.iter().copied(),
    );
    let witness_coupled_terminal_functional_fingerprint = m31_matrix_fingerprint(
        "compressed_mask_sumcheck_terminal_functional",
        &[terminal_coefficients_m31],
    );

    // Every source reaching this list is already in the exact separate-raw
    // kernel.  The verifier terminal is therefore fixed, so its compressed
    // sumcheck component must lie in ker(T).  This covers semantic, all ten
    // mask-only columns, G, and any parameterized tail source.  H padding and
    // active-helper paths carry an identically zero sumcheck component.
    let witness_mask_raw_kernel_terminal_zero_sources_m31 = sumcheck_kernel_images.len();
    let witness_mask_raw_kernel_terminal_zero_guard = sumcheck_kernel_images.iter().all(|image| {
        compressed_mask_sumcheck_terminal_from_m31(&image[..sc_m31], &schedule.prefix.z)
            == Some(QM31::ZERO)
    });
    let zero_sumcheck = vec![M31::ZERO; sc_m31];
    let witness_h_zero_sumcheck_terminal_guard =
        compressed_mask_sumcheck_terminal_from_m31(&zero_sumcheck, &schedule.prefix.z)
            == Some(QM31::ZERO);
    if !witness_mask_raw_kernel_terminal_zero_guard || !witness_h_zero_sumcheck_terminal_guard {
        return Err(StateOnlyHidingRankGateError::Relation);
    }

    let raw_opening_minor = RankMinorProvenance::from_parts(
        "raw_openings_2244",
        raw_minor_sources,
        raw_minor_rows,
        raw_minor_values,
    );

    // Quotient the exact masked-sumcheck wire while carrying every shared
    // PCS/helper coordinate.  This catches cross-block dependencies that
    // independent rank checks cannot see.
    let mut tail_prefix_sumcheck_ranks = Vec::with_capacity(tail_kernel_ends.len() + 1);
    let mut prefix_sumcheck = ColumnEchelon::new(sc_m31);
    for image in &sumcheck_kernel_images[..g_kernel_end] {
        prefix_sumcheck.insert(image[..sc_m31].to_vec());
    }
    tail_prefix_sumcheck_ranks.push(prefix_sumcheck.rank);
    let mut prefix_start = g_kernel_end;
    for &prefix_end in &tail_kernel_ends {
        for image in &sumcheck_kernel_images[prefix_start..prefix_end] {
            prefix_sumcheck.insert(image[..sc_m31].to_vec());
        }
        tail_prefix_sumcheck_ranks.push(prefix_sumcheck.rank);
        prefix_start = prefix_end;
    }
    if let Some(output) = tail_prefix_sumcheck_ranks_out.as_deref_mut() {
        output.clear();
        output.extend_from_slice(&tail_prefix_sumcheck_ranks);
    }

    let mut sumcheck = CarryEchelon::new(sc_m31);
    let mut pcs_kernel_images = Vec::new();
    let mut pcs_kernel_source_ids = Vec::new();
    let mut sumcheck_minor_sources = Vec::new();
    let mut sumcheck_minor_rows = Vec::new();
    let mut sumcheck_minor_values = Vec::new();
    debug_assert_eq!(
        sumcheck_kernel_images.len(),
        sumcheck_kernel_source_ids.len()
    );
    for (&source_id, image) in sumcheck_kernel_source_ids
        .iter()
        .zip(&sumcheck_kernel_images)
    {
        let (sc, pcs) = image.split_at(sc_m31);
        match sumcheck.reduce_with_pivot(sc.to_vec(), pcs.to_vec()) {
            CarryReduction::Pivot { row, value } => {
                sumcheck_minor_sources.push(source_id);
                sumcheck_minor_rows.push(row);
                sumcheck_minor_values.push(value);
            }
            CarryReduction::Kernel(kernel) => {
                pcs_kernel_images.push(kernel);
                pcs_kernel_source_ids.push(source_id);
            }
        }
    }
    if sumcheck.rank != MASK_SUMCHECK_QUOTIENT_M31
        && coordinate_factored_mask_columns.is_none()
        && !continue_after_sumcheck_deficit
    {
        return Err(StateOnlyHidingRankGateError::MaskedSumcheckRank {
            got: sumcheck.rank,
            want: MASK_SUMCHECK_QUOTIENT_M31,
        });
    }
    let witness_mask_sumcheck_equals_terminal_kernel = witness_mask_raw_kernel_terminal_zero_guard
        && witness_h_zero_sumcheck_terminal_guard
        && sumcheck.rank == MASK_SUMCHECK_QUOTIENT_M31;
    let post_sumcheck_kernel_m31 = pcs_kernel_images.len();
    let masked_sumcheck_minor = RankMinorProvenance::from_parts(
        "masked_sumcheck_1080",
        sumcheck_minor_sources,
        sumcheck_minor_rows,
        sumcheck_minor_values,
    );
    let joint_raw_sumcheck_minor = RankMinorProvenance::from_parts(
        "joint_raw_sumcheck_3324",
        raw_opening_minor
            .source_columns
            .iter()
            .chain(&masked_sumcheck_minor.source_columns)
            .copied()
            .collect(),
        raw_opening_minor
            .pivot_rows
            .iter()
            .copied()
            .chain(
                masked_sumcheck_minor
                    .pivot_rows
                    .iter()
                    .map(|row| raw_block_offset + *row),
            )
            .collect(),
        raw_opening_minor
            .pivot_values_m31
            .iter()
            .chain(&masked_sumcheck_minor.pivot_values_m31)
            .copied()
            .map(M31)
            .collect(),
    );

    let mut pcs_rank = ColumnEchelon::new(joint_pcs_m31);
    let mut pcs_minor_sources = Vec::new();
    let mut pcs_minor_rows = Vec::new();
    let mut pcs_minor_values = Vec::new();
    debug_assert_eq!(pcs_kernel_images.len(), pcs_kernel_source_ids.len());
    for (source_id, image) in pcs_kernel_source_ids.into_iter().zip(pcs_kernel_images) {
        if let Some((row, value)) = pcs_rank.insert_with_pivot_value(image) {
            pcs_minor_sources.push(source_id);
            pcs_minor_rows.push(row);
            pcs_minor_values.push(value);
        }
    }
    let pre_helper_pcs_rank = pcs_rank.rank;
    let h_scale = semantic_pcs_delta.mul(powers[h_generator_index]);
    let mut h_inactive_mask_basis_m31 = 0usize;
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for &row in &inactive {
            if row == global_dependent {
                continue;
            }
            let source_id = basis_columns;
            if let Some((pivot, value)) = pcs_rank.insert_with_pivot_value(h_pcs_image(
                &rows,
                row,
                global_dependent,
                basis,
                h_scale,
                h_raw_qm31,
                pcs_tail_qm31,
            )) {
                pcs_minor_sources.push(source_id);
                pcs_minor_rows.push(pivot);
                pcs_minor_values.push(value);
            }
            basis_columns += 1;
            h_inactive_mask_basis_m31 += 1;
        }
    }
    let before = pcs_rank.rank;
    let post_sumcheck_pcs_minor = RankMinorProvenance::from_parts(
        "post_sumcheck_pcs_712",
        pcs_minor_sources,
        pcs_minor_rows,
        pcs_minor_values,
    );

    let mut coordinate_prefix_sumcheck_ranks = Vec::new();
    let mut coordinate_prefix_pcs_ranks = Vec::new();
    if coordinate_factored_mask_columns.is_some() {
        debug_assert!(tail_qm31_mask_factors.is_empty());
        for prefix in 0..=mask_only_columns {
            let mask_end = if prefix == 0 {
                semantic_kernel_end
            } else {
                mask_kernel_ends[prefix - 1]
            };
            let mut prefix_sumcheck = CarryEchelon::new(sc_m31);
            let mut prefix_pcs_images = Vec::new();
            for image in sumcheck_kernel_images[..mask_end]
                .iter()
                .chain(&sumcheck_kernel_images[g_kernel_start..g_kernel_end])
            {
                let (sc, pcs) = image.split_at(sc_m31);
                if let Some(kernel) = prefix_sumcheck.reduce(sc.to_vec(), pcs.to_vec()) {
                    prefix_pcs_images.push(kernel);
                }
            }
            coordinate_prefix_sumcheck_ranks.push(prefix_sumcheck.rank);
            let mut prefix_pcs = ColumnEchelon::new(joint_pcs_m31);
            for image in prefix_pcs_images {
                prefix_pcs.insert(image);
            }
            let prefix_h_scale = powers[STATE_ONLY_HIDING_C1_COLUMNS + prefix];
            for coordinate in 0..4 {
                let basis = state_only_mask_tower_basis(coordinate);
                for &row in &inactive {
                    if row != global_dependent {
                        prefix_pcs.insert(h_pcs_image(
                            &rows,
                            row,
                            global_dependent,
                            basis,
                            prefix_h_scale,
                            h_raw_qm31,
                            pcs_tail_qm31,
                        ));
                    }
                }
            }
            coordinate_prefix_pcs_ranks.push(prefix_pcs.rank);
        }
    }

    // Independently derive the complete ambient joint image.  Counting the
    // serialized rows is too strong because later folds, OOD values and the
    // final coefficients obey public linear relations.  The ambient source
    // is the exact zero-inactive combined-message space, plus the inactive
    // helper mask space and every valid active zero-sum helper difference.
    let mut declared = ColumnEchelon::new(joint_pcs_m31);
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for row in 0..TRACE_ROWS {
            if row != global_dependent {
                declared.insert(combined_pcs_image(
                    &rows,
                    row,
                    basis,
                    h_raw_qm31,
                    pcs_tail_qm31,
                ));
            }
        }
    }
    let declared_combined_rank = declared.rank;
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for &row in &inactive {
            if row != global_dependent {
                declared.insert(h_pcs_image(
                    &rows,
                    row,
                    global_dependent,
                    basis,
                    h_scale,
                    h_raw_qm31,
                    pcs_tail_qm31,
                ));
            }
        }
    }
    let declared_inactive_helper_rank = declared.rank;

    // Independent universal containment tooth: every active zero-sum helper
    // difference must remain in the accepted joint image.
    let active_rows = (0..TRACE_ROWS)
        .filter(|row| active[*row])
        .collect::<Vec<_>>();
    let active_dependent = *active_rows
        .last()
        .ok_or(StateOnlyHidingRankGateError::Layout)?;
    let mut augmented = pcs_rank.clone();
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for &row in &active_rows[..active_rows.len() - 1] {
            let image = h_pcs_image(
                &rows,
                row,
                active_dependent,
                basis,
                h_scale,
                h_raw_qm31,
                pcs_tail_qm31,
            );
            declared.insert(image.clone());
            augmented.insert(image);
        }
    }
    if augmented.rank != before {
        return Err(StateOnlyHidingRankGateError::HelperContainment {
            before,
            after: augmented.rank,
        });
    }
    let baseline_valid_witness_containment = augmented.rank == before;
    let baseline_ambient_deficit_m31 = declared.rank.saturating_sub(before);

    // The historical `baseline_valid_witness_containment` tooth above covers
    // only active zero-sum H/helper differences.  This optional diagnostic
    // keeps both (a) the old overstrong independent-terminal stress target
    // and (b) the protocol-valid coupled target.  The latter carries each
    // physical source's exact H image and conditions the remaining sumcheck
    // fiber on both its initial claim and verifier-computed terminal.
    let mut witness_semantic_superset_generators_m31 = 0usize;
    let mut witness_semantic_superset_rank = before;
    let mut witness_legal_sumcheck_generators_m31 = 0usize;
    let mut witness_legal_sumcheck_rank = before;
    let mut witness_compatibility_rank_m31 = 0usize;
    let mut witness_semantic_sources = Vec::new();
    let mut witness_semantic_rows = Vec::new();
    let mut witness_semantic_values = Vec::new();
    let mut witness_sumcheck_sources = Vec::new();
    let mut witness_sumcheck_rows = Vec::new();
    let mut witness_sumcheck_values = Vec::new();
    let mut witness_compatibility_pivot_sources = Vec::new();
    let mut witness_compatibility_pivot_rows_m31 = Vec::new();
    let mut witness_compatibility_terminal_columns_m31 = Vec::new();
    let mut witness_compatibility_terminal_map_rank_m31 = 0usize;
    let mut witness_compatibility_terminal_map_fingerprint = 0u64;
    let mut witness_semantic_kernel_coefficients_m31 = Vec::new();
    let mut witness_semantic_complement_images = Vec::new();
    let mut witness_unbalanced_semantic_superset_generators_m31 = 0usize;
    let mut witness_unbalanced_semantic_superset_rank = before;
    let mut witness_unbalanced_compatibility_rank_m31 = 0usize;
    let mut witness_unbalanced_compatibility_pivot_sources = Vec::new();
    let mut witness_unbalanced_sources = Vec::new();
    let mut witness_unbalanced_rows = Vec::new();
    let mut witness_unbalanced_values = Vec::new();
    let mut witness_difference_projection = None;
    let mut witness_semantic_sparse_dense_guard = false;
    let mut witness_semantic_sparse_dense_fingerprint = 0u64;
    let mut witness_unbalanced_sparse_dense_guard = false;
    let mut witness_unbalanced_sparse_dense_fingerprint = 0u64;
    let mut witness_unbalanced_pcs_tails = None;
    // The weighted inactive-sum claim is an actual four-coordinate public
    // View block.  Keep it in literal direct-sum ranks; the wrapper also
    // reports the conditioned quotient with these fixed coordinates omitted.
    let raw_mask_rank_m31 =
        raw_opening_minor.source_columns.len() + weighted_aggregate_claim_rank_m31;
    let mut witness_direct_sum_extra_public_rank_m31 = 0usize;
    let mut witness_direct_sum_mask_view_rank_m31 =
        raw_mask_rank_m31 + sumcheck.rank + pcs_rank.rank;
    let mut witness_direct_sum_sumcheck = sumcheck.clone();
    let mut witness_direct_sum_pcs = pcs_rank.clone();
    let mut witness_direct_sum_physical_augmented_view_rank_m31 =
        witness_direct_sum_mask_view_rank_m31;
    let mut witness_direct_sum_legal_augmented_view_rank_m31 =
        witness_direct_sum_mask_view_rank_m31;
    let mut witness_direct_sum_helper_augmented_view_rank_m31 =
        witness_direct_sum_mask_view_rank_m31;
    let mut witness_direct_sum_unbalanced_physical_augmented_view_rank_m31 =
        witness_direct_sum_mask_view_rank_m31;
    let mut witness_coupled_physical_augmented_view_rank_m31 =
        witness_direct_sum_mask_view_rank_m31;
    let mut witness_coupled_legal_augmented_view_rank_m31 = witness_direct_sum_mask_view_rank_m31;
    let mut witness_coupled_helper_augmented_view_rank_m31 = witness_direct_sum_mask_view_rank_m31;
    let mut witness_coupled_legal_sumcheck_generators_m31 = 0usize;
    let witness_coupled_terminal_dependent_observation =
        witness_difference_probe.then_some(terminal_dependent);
    let mut witness_coupled_terminal_identity_guard = false;
    if witness_difference_probe {
        if layout != RankLayout::AtomicV3
            || semantic_raw_echelons.len() != STATE_ONLY_HIDING_C1_COLUMNS
        {
            return Err(StateOnlyHidingRankGateError::Layout);
        }

        let indices = derive_circle_line_query_indices_for_count(
            &schedule.queries[..schedule.query_count],
            encoder.codeword_len() / FIBER_SLOTS,
        )
        .map_err(|_| StateOnlyHidingRankGateError::Shape)?;
        let full_tails = if pcs_schedule.is_root_message() {
            (0..TRACE_ROWS)
                .map(|row| {
                    let mut message = vec![QM31::ZERO; TRACE_ROWS];
                    message[row] = QM31::ONE;
                    message
                })
                .collect::<Vec<_>>()
        } else {
            let dependent = raw_root0_row_pcs_tail_sparse(
                &encoder,
                domain_log,
                global_dependent,
                schedule,
                &indices.later,
                layout,
            )?;
            if dependent.len() != pcs_tail_qm31 {
                return Err(StateOnlyHidingRankGateError::Shape);
            }
            let full = (0..TRACE_ROWS)
                .map(|row| {
                    if row == global_dependent {
                        dependent.clone()
                    } else if active[row] {
                        rows[row].pcs_tail.clone()
                    } else {
                        rows[row]
                            .pcs_tail
                            .iter()
                            .copied()
                            .zip(&dependent)
                            .map(|(difference, dependent)| difference.add(*dependent))
                            .collect::<Vec<_>>()
                    }
                })
                .collect::<Vec<_>>();
            full
        };

        // Pin the cache reconstruction independently on the rows implicated
        // by the old balanced/unbalanced mismatch and across the domain.
        let guard_rows = [
            0usize,
            1,
            2,
            3,
            4,
            5,
            global_dependent,
            TRACE_ROWS / 2,
            TRACE_ROWS - 1,
        ];
        for row in guard_rows {
            let direct = if pcs_schedule.is_root_message() {
                let mut message = vec![QM31::ZERO; TRACE_ROWS];
                message[row] = QM31::ONE;
                message
            } else {
                raw_root0_row_pcs_tail_sparse(
                    &encoder,
                    domain_log,
                    row,
                    schedule,
                    &indices.later,
                    layout,
                )?
            };
            if direct != full_tails[row] {
                return Err(StateOnlyHidingRankGateError::Encoding);
            }
        }

        // Stronger ambient control: every unbalanced e_r source, across all
        // sixteen gamma-weighted columns, is summed through the sparse map and
        // compared with a dense C2/relation execution.
        let mut prng = 0x5e6d_616e_7469_6321u64;
        let mut combined_message = vec![QM31::ZERO; TRACE_ROWS];
        for power in powers[..STATE_ONLY_HIDING_C1_COLUMNS]
            .iter()
            .copied()
            .map(|power| semantic_pcs_delta.mul(power))
        {
            for (row, value) in combined_message.iter_mut().enumerate().skip(1) {
                prng ^= prng << 13;
                prng ^= prng >> 7;
                prng ^= prng << 17;
                let coefficient = M31((prng % 2_147_483_647u64) as u32);
                *value = value.add(power.mul_m31(coefficient));
                debug_assert!(row < TRACE_ROWS);
            }
        }
        let mut sparse_projection = vec![QM31::ZERO; pcs_tail_qm31];
        for (row, &coefficient) in combined_message.iter().enumerate().skip(1) {
            for (value, basis) in sparse_projection.iter_mut().zip(&full_tails[row]) {
                *value = value.add(coefficient.mul(*basis));
            }
        }
        let dense_projection = if pcs_schedule.is_root_message() {
            combined_message.clone()
        } else {
            raw_root0_message_pcs_tail_dense(
                &encoder,
                domain_log,
                &combined_message,
                schedule,
                &indices.later,
                layout,
            )?
        };
        if sparse_projection != dense_projection {
            return Err(StateOnlyHidingRankGateError::Encoding);
        }
        let mut projection_m31 = Vec::with_capacity(4 * dense_projection.len());
        append_qm31_coordinates(&mut projection_m31, dense_projection.iter().copied());
        witness_unbalanced_sparse_dense_fingerprint =
            m31_matrix_fingerprint("unbalanced_semantic_projection", &[projection_m31]);
        witness_unbalanced_sparse_dense_guard = true;

        // Exact physical control: canonicalize each column in the same basis
        // used by `apply_mask_material_for_layout`: active e_r; inactive
        // e_r-e_d(c); skip d(c).  Both the sparse PCS source and the dense
        // message use that identical per-column canonicalization.
        let mut physical_prng = 0x7068_7973_6963_616cu64;
        let mut physical_message = vec![QM31::ZERO; TRACE_ROWS];
        let mut physical_sparse_projection = vec![QM31::ZERO; pcs_tail_qm31];
        for (column, power) in powers[..STATE_ONLY_HIDING_C1_COLUMNS]
            .iter()
            .copied()
            .map(|power| semantic_pcs_delta.mul(power))
            .enumerate()
        {
            let dependent = semantic_inactive_dependents[column];
            for row in 1..TRACE_ROWS {
                if row == dependent {
                    continue;
                }
                physical_prng ^= physical_prng << 13;
                physical_prng ^= physical_prng >> 7;
                physical_prng ^= physical_prng << 17;
                let coefficient = M31((physical_prng % 2_147_483_647u64) as u32);
                let scaled = power.mul_m31(coefficient);
                physical_message[row] = physical_message[row].add(scaled);
                if !active[row] {
                    physical_message[dependent] = physical_message[dependent].sub(scaled);
                }
                for (index, value) in physical_sparse_projection.iter_mut().enumerate() {
                    let basis = if active[row] {
                        full_tails[row][index]
                    } else {
                        full_tails[row][index].sub(full_tails[dependent][index])
                    };
                    *value = value.add(scaled.mul(basis));
                }
            }
        }
        let physical_dense_projection = if pcs_schedule.is_root_message() {
            physical_message.clone()
        } else {
            raw_root0_message_pcs_tail_dense(
                &encoder,
                domain_log,
                &physical_message,
                schedule,
                &indices.later,
                layout,
            )?
        };
        if physical_sparse_projection != physical_dense_projection {
            return Err(StateOnlyHidingRankGateError::Encoding);
        }
        let mut physical_projection_m31 = Vec::with_capacity(4 * physical_dense_projection.len());
        append_qm31_coordinates(
            &mut physical_projection_m31,
            physical_dense_projection.iter().copied(),
        );
        witness_semantic_sparse_dense_fingerprint =
            m31_matrix_fingerprint("physical_semantic_projection", &[physical_projection_m31]);
        witness_semantic_sparse_dense_guard = true;
        witness_unbalanced_pcs_tails = Some(full_tails);

        // The native full-X fallback is an affine translation source, not a
        // late additive tail.  Condition the complete X message on every
        // separately visible X field first, then make its PCS kernel part of
        // the literal mask echelon before physical/legal/helper targets are
        // inserted.  The independently visible block contributes its own
        // rank to both sides of the full-View comparison.
        if matches!(
            late_switch_support,
            LateSwitchSupport::LeanNativeFullRootX
                | LateSwitchSupport::LeanNativeFullRootXRawOnlyControl
        ) {
            let epsilon = selected_late_switch_delta.ok_or(StateOnlyHidingRankGateError::Shape)?;
            let expose_target = late_switch_support == LateSwitchSupport::LeanNativeFullRootX;
            let conditioned =
                state_only_native_full_x_affine_rank::condition_native_full_x_affine_pcs(
                    schedule,
                    layout,
                    &rows,
                    witness_unbalanced_pcs_tails
                        .as_ref()
                        .ok_or(StateOnlyHidingRankGateError::Layout)?,
                    epsilon,
                    h_raw_qm31,
                    &witness_direct_sum_pcs,
                    expose_target,
                    false,
                )?;
            witness_direct_sum_extra_public_rank_m31 = 4 * conditioned.observation_rank_qm31;
            witness_direct_sum_pcs = conditioned.conditioned_pcs;
            witness_direct_sum_mask_view_rank_m31 = raw_mask_rank_m31
                + witness_direct_sum_extra_public_rank_m31
                + witness_direct_sum_sumcheck.rank
                + witness_direct_sum_pcs.rank;
        }

        if late_switch_support == LateSwitchSupport::MaskedSemanticNatural18SharedC2SingleCodeword {
            let delta = selected_late_switch_delta.ok_or(StateOnlyHidingRankGateError::Shape)?;
            let conditioned =
                state_only_reduced_high_switch_rank::condition_reduced_natural18_shared_c2_pcs(
                    &encoder,
                    domain_log,
                    schedule,
                    delta,
                    &rows,
                    h_raw_qm31,
                    pcs_tail_qm31,
                    &witness_direct_sum_pcs,
                )?;
            witness_direct_sum_extra_public_rank_m31 = 4 * conditioned.observation_rank_qm31;
            witness_direct_sum_pcs = conditioned.conditioned_pcs;
            witness_direct_sum_mask_view_rank_m31 = raw_mask_rank_m31
                + witness_direct_sum_extra_public_rank_m31
                + witness_direct_sum_sumcheck.rank
                + witness_direct_sum_pcs.rank;
        }

        // Sign/serialization identity guard.  Each semantic row oracle is
        // eq_z(row)*factor_c(z) at the terminal; the compressed wire must
        // reconstruct exactly that value, including the omitted-c1 sign.
        for column in 0..STATE_ONLY_HIDING_C1_COLUMNS {
            let factor_at_terminal = factor_at_schedule(
                factor_schedule,
                MaskFactor::Semantic(column),
                &schedule.prefix.z,
                coordinate_factored_mask_columns,
            );
            for row in 0..TRACE_ROWS {
                let got = compressed_mask_sumcheck_terminal(
                    &semantic_sumcheck_observations[column][row],
                    &schedule.prefix.z,
                )
                .ok_or(StateOnlyHidingRankGateError::Shape)?;
                let want = eq_weight(&schedule.prefix.z, row).mul(factor_at_terminal);
                if got != want {
                    return Err(StateOnlyHidingRankGateError::Relation);
                }
            }
        }
        witness_coupled_terminal_identity_guard = true;

        let mut semantic_augmented = pcs_rank.clone();
        let mut compatibility = CarryEchelon::new(sc_m31);
        let mut coupled_sumcheck = witness_direct_sum_sumcheck.clone();
        let mut coupled_pcs = witness_direct_sum_pcs.clone();
        for column in 0..STATE_ONLY_HIDING_C1_COLUMNS {
            let dependent = semantic_inactive_dependents[column];
            for row in 0..TRACE_ROWS {
                // Atomic block 0 is the owner-key invocation. Its pre-absorb
                // row is the public-layout constant
                // `[0^8, DOMAIN_OWNER_KEY, 8, 0^6]`; no same-statement
                // witness difference may alter any of these sixteen cells.
                if row == 0 || row == dependent {
                    continue;
                }
                let subtract = (!active[row]).then_some(dependent);
                let source_id = column * TRACE_ROWS + row;
                witness_semantic_superset_generators_m31 += 1;
                let raw = c1_raw_difference(&rows, row, subtract);
                let mut carry = vec![M31::ZERO; aux_m31];
                let pcs = scaled_qm31_difference(
                    &rows[row].pcs_tail,
                    subtract.map(|dependent| rows[dependent].pcs_tail.as_slice()),
                    semantic_pcs_delta.mul(powers[column]),
                );
                let pcs_start = sc_m31 + 4 * h_raw_qm31;
                carry[pcs_start..pcs_start + pcs.len()].copy_from_slice(&pcs);
                let post_raw = semantic_raw_echelons[column]
                    .quotient_existing(raw.clone(), carry)
                    .ok_or(StateOnlyHidingRankGateError::WitnessRawQuotient {
                        source: source_id,
                    })?;
                let (sc, pcs) = post_raw.split_at(sc_m31);

                // Literal block Gaussian elimination for the documented
                // direct-sum target.  A new sumcheck pivot is itself a new
                // public-view direction.  Only a true sumcheck kernel may
                // flow to the PCS quotient.
                if let CarryReduction::Kernel(post_sumcheck) =
                    witness_direct_sum_sumcheck.reduce_with_pivot(sc.to_vec(), pcs.to_vec())
                {
                    witness_direct_sum_pcs.insert(post_sumcheck);
                }

                // Valid-view embedding.  H is a public linear function of
                // the same committed semantic column, so a physical source
                // necessarily carries these exact mask-factor sumcheck
                // observations.  Any residual honest F-sumcheck difference
                // has zero initial claim and is added independently below.
                let coupled_carry = scaled_aux_difference(
                    &rows,
                    row,
                    subtract,
                    &semantic_sumcheck_observations[column],
                    QM31::ONE,
                    semantic_pcs_delta.mul(powers[column]),
                    4 * h_raw_qm31,
                    joint_pcs_m31,
                );
                let coupled_post_raw = semantic_raw_echelons[column]
                    .quotient_existing(raw, coupled_carry)
                    .ok_or(StateOnlyHidingRankGateError::WitnessRawQuotient {
                        source: source_id,
                    })?;
                let (coupled_sc, coupled_pcs_image) = coupled_post_raw.split_at(sc_m31);
                if let CarryReduction::Kernel(post_sumcheck) = coupled_sumcheck
                    .reduce_with_pivot(coupled_sc.to_vec(), coupled_pcs_image.to_vec())
                {
                    coupled_pcs.insert(post_sumcheck);
                }

                let (sc_remainder, mut pcs_remainder) =
                    sumcheck.remainder_existing(sc.to_vec(), pcs.to_vec());
                let compatibility_terminal =
                    compressed_mask_sumcheck_terminal_from_m31(&sc_remainder, &schedule.prefix.z)
                        .ok_or(StateOnlyHidingRankGateError::Shape)?;
                let next_pivot = compatibility.rank;
                pcs_remainder.extend((0..4).map(|index| {
                    if next_pivot < 4 && index == next_pivot {
                        M31::ONE
                    } else {
                        M31::ZERO
                    }
                }));
                match compatibility.reduce_with_pivot(sc_remainder, pcs_remainder) {
                    CarryReduction::Pivot { row: pivot, .. } => {
                        witness_compatibility_pivot_sources.push(source_id);
                        witness_compatibility_pivot_rows_m31.push(pivot);
                        witness_compatibility_terminal_columns_m31
                            .push(qm31_coordinates(compatibility_terminal).to_vec());
                    }
                    CarryReduction::Kernel(mut post_sumcheck) => {
                        let coefficients = post_sumcheck.split_off(joint_pcs_m31);
                        if let Some((pivot, value)) =
                            semantic_augmented.insert_with_pivot_value(post_sumcheck.clone())
                        {
                            witness_semantic_complement_images.push(post_sumcheck);
                            witness_semantic_sources.push(source_id);
                            witness_semantic_rows.push(pivot);
                            witness_semantic_values.push(value);
                            witness_semantic_kernel_coefficients_m31
                                .extend(coefficients.into_iter().map(|value| value.0));
                        }
                    }
                }
            }
        }
        witness_semantic_superset_rank = semantic_augmented.rank;
        let mut compatibility_terminal_map = ColumnEchelon::new(4);
        for column in &witness_compatibility_terminal_columns_m31 {
            compatibility_terminal_map.insert(column.clone());
        }
        witness_compatibility_terminal_map_rank_m31 = compatibility_terminal_map.rank;
        witness_compatibility_terminal_map_fingerprint = m31_matrix_fingerprint(
            "physical_compatibility_to_sumcheck_terminal",
            &witness_compatibility_terminal_columns_m31,
        );
        witness_direct_sum_physical_augmented_view_rank_m31 = raw_mask_rank_m31
            + witness_direct_sum_extra_public_rank_m31
            + witness_direct_sum_sumcheck.rank
            + witness_direct_sum_pcs.rank;
        witness_coupled_physical_augmented_view_rank_m31 = raw_mask_rank_m31
            + witness_direct_sum_extra_public_rank_m31
            + coupled_sumcheck.rank
            + coupled_pcs.rank;

        // Separately labelled upper-oracle stress test.  These e_r sources
        // are internally consistent across raw/PCS, but inactive e_r is not
        // emitted by `apply_mask_material_for_layout`; it is deliberately not
        // used by the physical containment decision below.
        let mut unbalanced_augmented = pcs_rank.clone();
        let mut unbalanced_compatibility = CarryEchelon::new(sc_m31);
        let mut unbalanced_direct_sumcheck = sumcheck.clone();
        let mut unbalanced_direct_pcs = pcs_rank.clone();
        let full_tails = witness_unbalanced_pcs_tails
            .as_ref()
            .ok_or(StateOnlyHidingRankGateError::Layout)?;
        for column in 0..STATE_ONLY_HIDING_C1_COLUMNS {
            for row in 1..TRACE_ROWS {
                let source_id = column * TRACE_ROWS + row;
                witness_unbalanced_semantic_superset_generators_m31 += 1;
                let raw = c1_raw_difference(&rows, row, None);
                let mut carry = vec![M31::ZERO; aux_m31];
                let pcs = scaled_qm31_difference(
                    &full_tails[row],
                    None,
                    semantic_pcs_delta.mul(powers[column]),
                );
                let pcs_start = sc_m31 + 4 * h_raw_qm31;
                carry[pcs_start..pcs_start + pcs.len()].copy_from_slice(&pcs);
                let post_raw = semantic_raw_echelons[column]
                    .quotient_existing(raw, carry)
                    .ok_or(StateOnlyHidingRankGateError::WitnessRawQuotient {
                        source: source_id,
                    })?;
                let claim = if weighted_inactive_sum.is_some_and(|config| {
                    matches!(
                        config.group,
                        WeightedInactiveSumGroup::Semantic
                            | WeightedInactiveSumGroup::SemanticPlusMaskOnly
                    )
                }) && !active[row]
                {
                    qm31_coordinates(powers[column]).to_vec()
                } else {
                    vec![M31::ZERO; weighted_aggregate_claim_rank_m31]
                };
                let post_claim =
                    if let Some(aggregate_claim) = weighted_aggregate_claim_echelon.as_ref() {
                        aggregate_claim
                            .quotient_existing(claim, post_raw)
                            .ok_or(StateOnlyHidingRankGateError::Layout)?
                    } else {
                        post_raw
                    };
                let (sc, pcs) = post_claim.split_at(sc_m31);

                if let CarryReduction::Kernel(post_sumcheck) =
                    unbalanced_direct_sumcheck.reduce_with_pivot(sc.to_vec(), pcs.to_vec())
                {
                    unbalanced_direct_pcs.insert(post_sumcheck);
                }
                let (sc_remainder, mut pcs_remainder) =
                    sumcheck.remainder_existing(sc.to_vec(), pcs.to_vec());
                let next_pivot = unbalanced_compatibility.rank;
                pcs_remainder.extend((0..4).map(|index| {
                    if next_pivot < 4 && index == next_pivot {
                        M31::ONE
                    } else {
                        M31::ZERO
                    }
                }));
                match unbalanced_compatibility.reduce_with_pivot(sc_remainder, pcs_remainder) {
                    CarryReduction::Pivot { .. } => {
                        witness_unbalanced_compatibility_pivot_sources.push(source_id);
                    }
                    CarryReduction::Kernel(mut post_sumcheck) => {
                        post_sumcheck.truncate(joint_pcs_m31);
                        if let Some((pivot, value)) =
                            unbalanced_augmented.insert_with_pivot_value(post_sumcheck)
                        {
                            witness_unbalanced_sources.push(source_id);
                            witness_unbalanced_rows.push(pivot);
                            witness_unbalanced_values.push(value);
                        }
                    }
                }
            }
        }
        witness_unbalanced_semantic_superset_rank = unbalanced_augmented.rank;
        witness_unbalanced_compatibility_rank_m31 = unbalanced_compatibility.rank;
        witness_direct_sum_unbalanced_physical_augmented_view_rank_m31 =
            raw_mask_rank_m31 + unbalanced_direct_sumcheck.rank + unbalanced_direct_pcs.rank;

        // Negative stress control only.  The first QM31 observation is the
        // unmasked Boolean-cube sum, but allowing all remaining 270 QM31
        // coordinates independently also allows a verifier-terminal
        // mismatch.  The valid conditional kernel is inserted separately
        // below and has only 269 QM31 directions.
        let mut sumcheck_augmented = semantic_augmented.clone();
        for sc_row in 4..sc_m31 {
            witness_legal_sumcheck_generators_m31 += 1;
            let mut sc = vec![M31::ZERO; sc_m31];
            sc[sc_row] = M31::ONE;
            let pcs = vec![M31::ZERO; joint_pcs_m31];

            if let CarryReduction::Kernel(post_sumcheck) =
                witness_direct_sum_sumcheck.reduce_with_pivot(sc.clone(), pcs.clone())
            {
                witness_direct_sum_pcs.insert(post_sumcheck);
            }

            let (sc_remainder, mut pcs_remainder) = sumcheck.remainder_existing(sc, pcs);
            pcs_remainder.extend([M31::ZERO; 4]);
            match compatibility.reduce_with_pivot(sc_remainder, pcs_remainder) {
                CarryReduction::Pivot { .. } => {}
                CarryReduction::Kernel(mut post_sumcheck) => {
                    post_sumcheck.truncate(joint_pcs_m31);
                    if let Some((pivot, value)) =
                        sumcheck_augmented.insert_with_pivot_value(post_sumcheck)
                    {
                        witness_sumcheck_sources.push(sc_row - 4);
                        witness_sumcheck_rows.push(pivot);
                        witness_sumcheck_values.push(value);
                    }
                }
            }
        }
        witness_legal_sumcheck_rank = sumcheck_augmented.rank;
        witness_compatibility_rank_m31 = compatibility.rank;

        // Conditional protocol fiber: the initial claim is already bound
        // before the wire, and the terminal is recomputed from the opened
        // statement values.  Span exactly the kernel of those two QM31
        // functionals, rather than the invalid zero-initial-only ambient
        // used by the independent direct-sum stress control above.
        for observation in 1..STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS {
            if observation == terminal_dependent {
                continue;
            }
            for coordinate in 0..4 {
                let basis = state_only_mask_tower_basis(coordinate);
                let dependent_value = QM31::ZERO.sub(
                    terminal_dependent_inverse
                        .mul(terminal_coefficients[observation])
                        .mul(basis),
                );
                let mut compressed = vec![QM31::ZERO; STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS];
                compressed[observation] = basis;
                compressed[terminal_dependent] = dependent_value;
                if compressed[0] != QM31::ZERO
                    || compressed_mask_sumcheck_terminal(&compressed, &schedule.prefix.z)
                        != Some(QM31::ZERO)
                {
                    return Err(StateOnlyHidingRankGateError::Relation);
                }
                let mut sc = Vec::with_capacity(sc_m31);
                append_qm31_coordinates(&mut sc, compressed);
                let pcs = vec![M31::ZERO; joint_pcs_m31];
                if let CarryReduction::Kernel(post_sumcheck) =
                    coupled_sumcheck.reduce_with_pivot(sc, pcs)
                {
                    coupled_pcs.insert(post_sumcheck);
                }
                witness_coupled_legal_sumcheck_generators_m31 += 1;
            }
        }
        if witness_coupled_legal_sumcheck_generators_m31
            != MASK_SUMCHECK_QUOTIENT_M31.saturating_sub(4)
        {
            return Err(StateOnlyHidingRankGateError::Shape);
        }
        witness_direct_sum_legal_augmented_view_rank_m31 = raw_mask_rank_m31
            + witness_direct_sum_extra_public_rank_m31
            + witness_direct_sum_sumcheck.rank
            + witness_direct_sum_pcs.rank;
        witness_coupled_legal_augmented_view_rank_m31 = raw_mask_rank_m31
            + witness_direct_sum_extra_public_rank_m31
            + coupled_sumcheck.rank
            + coupled_pcs.rank;

        // Active helper differences have zero raw and sumcheck images.  Add
        // them literally to the same final PCS quotient instead of relying
        // only on the earlier helper-containment assertion.
        let mut helper_augmented = witness_direct_sum_pcs.clone();
        for coordinate in 0..4 {
            let basis = state_only_mask_tower_basis(coordinate);
            for &row in &active_rows[..active_rows.len() - 1] {
                helper_augmented.insert(h_pcs_image(
                    &rows,
                    row,
                    active_dependent,
                    basis,
                    h_scale,
                    h_raw_qm31,
                    pcs_tail_qm31,
                ));
            }
        }
        witness_direct_sum_helper_augmented_view_rank_m31 = raw_mask_rank_m31
            + witness_direct_sum_extra_public_rank_m31
            + witness_direct_sum_sumcheck.rank
            + helper_augmented.rank;

        let mut coupled_helper_augmented = coupled_pcs.clone();
        for coordinate in 0..4 {
            let basis = state_only_mask_tower_basis(coordinate);
            for &row in &active_rows[..active_rows.len() - 1] {
                coupled_helper_augmented.insert(h_pcs_image(
                    &rows,
                    row,
                    active_dependent,
                    basis,
                    h_scale,
                    h_raw_qm31,
                    pcs_tail_qm31,
                ));
            }
        }
        witness_coupled_helper_augmented_view_rank_m31 = raw_mask_rank_m31
            + witness_direct_sum_extra_public_rank_m31
            + coupled_sumcheck.rank
            + coupled_helper_augmented.rank;

        if let Some(input) = witness_projection_input.as_ref() {
            if input.semantic_columns.len() != STATE_ONLY_HIDING_C1_COLUMNS
                || input
                    .semantic_columns
                    .iter()
                    .any(|column| column.len() != TRACE_ROWS)
                || input.sumcheck_observations.len() != STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS
            {
                return Err(StateOnlyHidingRankGateError::Shape);
            }

            let pcs_start = sc_m31 + 4 * h_raw_qm31;
            let mut projected = vec![M31::ZERO; aux_m31];
            for (column, semantic) in input.semantic_columns.iter().enumerate() {
                if semantic[0] != M31::ZERO {
                    return Err(StateOnlyHidingRankGateError::Shape);
                }
                let inactive_sum = inactive
                    .iter()
                    .fold(M31::ZERO, |sum, &row| sum.add(semantic[row]));
                if inactive_sum != M31::ZERO {
                    return Err(StateOnlyHidingRankGateError::Shape);
                }
                let dependent = semantic_inactive_dependents[column];
                let mut raw = vec![M31::ZERO; c1_raw_m31];
                let mut carry = vec![M31::ZERO; aux_m31];
                for (row, &scale) in semantic.iter().enumerate() {
                    if scale == M31::ZERO || row == 0 || row == dependent {
                        continue;
                    }
                    let subtract = (!active[row]).then_some(dependent);
                    let raw_image = c1_raw_difference(&rows, row, subtract);
                    add_scaled_m31(&mut raw, &raw_image, scale);
                    let pcs = scaled_qm31_difference(
                        &rows[row].pcs_tail,
                        subtract.map(|dependent| rows[dependent].pcs_tail.as_slice()),
                        semantic_pcs_delta.mul(powers[column]),
                    );
                    add_scaled_m31(&mut carry[pcs_start..pcs_start + pcs.len()], &pcs, scale);
                }
                let post_raw = semantic_raw_echelons[column]
                    .quotient_existing(raw, carry)
                    .ok_or(StateOnlyHidingRankGateError::WitnessRawQuotient { source: column })?;
                add_scaled_m31(&mut projected, &post_raw, M31::ONE);
            }

            let mut supplied_sumcheck = Vec::with_capacity(sc_m31);
            append_qm31_coordinates(
                &mut supplied_sumcheck,
                input
                    .sumcheck_observations
                    .iter()
                    .copied()
                    .map(|value| schedule.prefix.eta.mul(value)),
            );
            add_scaled_m31(&mut projected[..sc_m31], &supplied_sumcheck, M31::ONE);
            let (sc, pcs) = projected.split_at(sc_m31);
            let (compatibility_remainder, post_sumcheck) =
                sumcheck.remainder_existing(sc.to_vec(), pcs.to_vec());
            let compatibility_remainder_rows_m31 = compatibility_remainder
                .iter()
                .enumerate()
                .filter_map(|(row, &value)| (value != M31::ZERO).then_some(row))
                .collect::<Vec<_>>();
            let compatibility_remainder_values_m31 = compatibility_remainder_rows_m31
                .iter()
                .map(|&row| compatibility_remainder[row].0)
                .collect::<Vec<_>>();

            let pcs_quotient = pcs_rank.remainder_existing(post_sumcheck.clone());
            let pcs_quotient_rows_m31 = pcs_quotient
                .iter()
                .enumerate()
                .filter_map(|(row, &value)| (value != M31::ZERO).then_some(row))
                .collect::<Vec<_>>();
            let pcs_quotient_values_m31 = pcs_quotient_rows_m31
                .iter()
                .map(|&row| pcs_quotient[row].0)
                .collect::<Vec<_>>();
            let semantic_quotient_pivot_rows_m31 = witness_semantic_rows.clone();
            let semantic_quotient_coordinates_m31 = semantic_quotient_pivot_rows_m31
                .iter()
                .map(|&row| pcs_quotient[row].0)
                .collect::<Vec<_>>();

            let outside_conservative_superset =
                sumcheck_augmented.remainder_existing(post_sumcheck);
            let outside_conservative_superset_rows_m31 = outside_conservative_superset
                .iter()
                .enumerate()
                .filter_map(|(row, &value)| (value != M31::ZERO).then_some(row))
                .collect::<Vec<_>>();
            let outside_conservative_superset_values_m31 = outside_conservative_superset_rows_m31
                .iter()
                .map(|&row| outside_conservative_superset[row].0)
                .collect::<Vec<_>>();

            let mut fingerprint_rows = compatibility_remainder_rows_m31.clone();
            fingerprint_rows.extend(pcs_quotient_rows_m31.iter().map(|row| sc_m31 + *row));
            fingerprint_rows.extend(
                outside_conservative_superset_rows_m31
                    .iter()
                    .map(|row| sc_m31 + joint_pcs_m31 + *row),
            );
            let mut fingerprint_values = compatibility_remainder_values_m31.clone();
            fingerprint_values.extend_from_slice(&pcs_quotient_values_m31);
            fingerprint_values.extend_from_slice(&outside_conservative_superset_values_m31);
            let fingerprint_sources = (0..fingerprint_rows.len()).collect::<Vec<_>>();
            let fingerprint = rank_minor_fingerprint(
                "witness_difference_projection",
                &fingerprint_sources,
                &fingerprint_rows,
                &fingerprint_values,
            );
            witness_difference_projection = Some(WitnessDifferenceProjectionReport {
                compatibility_kernel: compatibility_remainder_rows_m31.is_empty(),
                compatibility_remainder_rows_m31,
                compatibility_remainder_values_m31,
                pcs_quotient_rows_m31,
                pcs_quotient_values_m31,
                semantic_quotient_pivot_rows_m31,
                semantic_quotient_coordinates_m31,
                inside_conservative_superset: outside_conservative_superset_rows_m31.is_empty(),
                outside_conservative_superset_rows_m31,
                outside_conservative_superset_values_m31,
                fingerprint,
            });
        }
    }

    let witness_semantic_superset_minor = RankMinorProvenance::from_parts(
        "witness_semantic_superset",
        witness_semantic_sources,
        witness_semantic_rows,
        witness_semantic_values,
    );
    let witness_legal_sumcheck_minor = RankMinorProvenance::from_parts(
        "witness_legal_sumcheck_superset",
        witness_sumcheck_sources,
        witness_sumcheck_rows,
        witness_sumcheck_values,
    );
    let witness_unbalanced_semantic_superset_minor = RankMinorProvenance::from_parts(
        "witness_unbalanced_upper_oracle_superset",
        witness_unbalanced_sources,
        witness_unbalanced_rows,
        witness_unbalanced_values,
    );

    let mut late_switch_source_rows = Vec::new();
    let mut late_switch_variables_qm31 = 0usize;
    let mut late_switch_conditioned_kernel_qm31 = 0usize;
    let mut late_switch_conditioned_rank = before;
    let mut late_switch_semantic_augmented_rank = before;
    let mut late_switch_semantic_new_pivots_m31 = Vec::new();
    let mut late_switch_contains_conservative_semantic_superset =
        witness_semantic_complement_images.is_empty();
    let mut late_switch_ambient_deficit_m31 = baseline_ambient_deficit_m31;
    let mut late_switch_complement_pivots_later_m31 = 0usize;
    let mut late_switch_complement_pivots_ood_m31 = 0usize;
    let mut late_switch_complement_pivots_relation_m31 = 0usize;
    let mut late_switch_complement_pivots_final_m31 = 0usize;
    let mut masked_switch_variables_qm31 = 0usize;
    let mut masked_switch_universal_mds_basis = false;
    let mut masked_switch_code_basis_rank_m31 = 0usize;
    let mut masked_switch_query_abscissae_distinct = false;
    let mut masked_switch_rank_retry_required = true;
    let mut masked_switch_code_basis_fingerprint = 0u64;
    let mut masked_switch_observation_rank_qm31 = 0usize;
    let mut masked_switch_without_u_observation_rank_qm31 = 0usize;
    let mut masked_switch_without_u_kernel_qm31 = 0usize;
    let mut masked_switch_u_observation_rank_redundant = false;
    let mut masked_switch_kernel_qm31 = 0usize;
    let mut masked_switch_q_randomness_rank_qm31 = 0usize;
    let mut masked_switch_q_coopening_rank_qm31 = 0usize;
    let mut masked_switch_otp_rank_qm31 = 0usize;
    let mut masked_switch_u_rank_qm31 = 0usize;
    let mut masked_switch_u_plus_legacy_ood_diagnostic_rank_qm31 = 0usize;
    let mut masked_switch_shared_c2_observation_rank_qm31 = 0usize;
    let mut masked_switch_shared_c2_kernel_qm31 = 0usize;
    let mut masked_switch_shared_c2_randomness_rank_qm31 = 0usize;
    let mut masked_switch_standalone_frontier_nodes = 0usize;
    let mut masked_switch_shared_root_increment_bytes = 0usize;
    let mut masked_switch_standalone_increment_bytes = 0usize;
    let mut late_switch_minor_sources = Vec::new();
    let mut late_switch_minor_rows = Vec::new();
    let mut late_switch_minor_values = Vec::new();
    let mut late_switch_observation_sources = Vec::new();
    let mut late_switch_observation_rows = Vec::new();
    let mut late_switch_observation_values = Vec::new();

    if matches!(
        late_switch_support,
        LateSwitchSupport::LeanNativeFullRootX
            | LateSwitchSupport::LeanNativeFullRootXRawOnlyControl
    ) {
        if schedule.query_count != 16 || pcs_schedule != PcsSchedule::Arity4x4 {
            return Err(StateOnlyHidingRankGateError::Shape);
        }
        let epsilon = selected_late_switch_delta.ok_or(StateOnlyHidingRankGateError::Shape)?;
        if epsilon == QM31::ZERO {
            return Err(StateOnlyHidingRankGateError::Shape);
        }
        let queries = &schedule.queries[..schedule.query_count];
        let relation_weights = initial_relation_weights(schedule, layout)?;

        // Literal native message basis: every root-zero C2 message row is an
        // independent QM31 variable. The verifier sees its four authenticated
        // C2 symbols at each query and one exact old-relation target tX. The
        // three point evaluations enter tX but are not separately serialized.
        let expose_target = late_switch_support == LateSwitchSupport::LeanNativeFullRootX;
        let observation_qm31 = FIBER_SLOTS * schedule.query_count + usize::from(expose_target);
        let observation_columns = (0..TRACE_ROWS)
            .map(|row| {
                let mut column = rows[row]
                    .layer0_m31
                    .iter()
                    .copied()
                    .map(|value| QM31::from_cm31(CM31::from_m31(value)))
                    .collect::<Vec<_>>();
                if expose_target {
                    column.push(relation_weights.weight_at(row as u32));
                }
                column
            })
            .collect::<Vec<_>>();
        let observation_rank_qm31 = qm31_column_rank(&observation_columns, observation_qm31);
        if observation_rank_qm31 != observation_qm31 {
            return Err(StateOnlyHidingRankGateError::Layout);
        }

        let full_tails = witness_unbalanced_pcs_tails
            .as_ref()
            .ok_or(StateOnlyHidingRankGateError::Layout)?;

        let mut quotient = CarryEchelon::new(4 * observation_qm31);
        let mut conditioned = pcs_rank.clone();
        for row in 0..TRACE_ROWS {
            for tower_coordinate in 0..4 {
                let basis = state_only_mask_tower_basis(tower_coordinate);
                let mut observation = Vec::with_capacity(4 * observation_qm31);
                append_qm31_coordinates(
                    &mut observation,
                    observation_columns[row]
                        .iter()
                        .copied()
                        .map(|value| value.mul(basis)),
                );
                let carry = first_later_pcs_image(&full_tails[row], epsilon.mul(basis), h_raw_qm31);
                let source_id = 4 * row + tower_coordinate;
                match quotient.reduce_with_pivot(observation, carry) {
                    CarryReduction::Pivot { row, value } => {
                        late_switch_observation_sources.push(source_id);
                        late_switch_observation_rows.push(row);
                        late_switch_observation_values.push(value);
                    }
                    CarryReduction::Kernel(kernel) => {
                        if let Some((pivot, value)) = conditioned.insert_with_pivot_value(kernel) {
                            late_switch_minor_sources.push(source_id);
                            late_switch_minor_rows.push(pivot);
                            late_switch_minor_values.push(value);
                            let tail_pivot = pivot.saturating_sub(4 * h_raw_qm31);
                            let later_m31 = 4 * (pcs_tail_qm31 - 40);
                            if tail_pivot < later_m31 {
                                late_switch_complement_pivots_later_m31 += 1;
                            } else if tail_pivot < later_m31 + 4 * 8 {
                                late_switch_complement_pivots_ood_m31 += 1;
                            } else if tail_pivot < later_m31 + 4 * (8 + 28) {
                                late_switch_complement_pivots_relation_m31 += 1;
                            } else {
                                late_switch_complement_pivots_final_m31 += 1;
                            }
                        }
                    }
                }
            }
        }
        if quotient.rank != 4 * observation_rank_qm31 {
            return Err(StateOnlyHidingRankGateError::Layout);
        }
        late_switch_conditioned_rank = conditioned.rank;
        late_switch_ambient_deficit_m31 =
            declared.rank.saturating_sub(late_switch_conditioned_rank);
        let pre_semantic = conditioned.rank;
        for image in &witness_semantic_complement_images {
            if let Some(pivot) = conditioned.insert_with_pivot(image.clone()) {
                late_switch_semantic_new_pivots_m31.push(pivot);
            }
        }
        late_switch_semantic_augmented_rank = conditioned.rank;
        late_switch_contains_conservative_semantic_superset = conditioned.rank == pre_semantic;

        late_switch_source_rows.extend(0..TRACE_ROWS);
        late_switch_variables_qm31 = TRACE_ROWS;
        late_switch_conditioned_kernel_qm31 = TRACE_ROWS - observation_rank_qm31;
        masked_switch_variables_qm31 = TRACE_ROWS;
        masked_switch_code_basis_rank_m31 = TRACE_ROWS;
        // The fixed fixture has full 65-row observation rank. A universal
        // all-q statement for that minor is not claimed by this rank run.
        masked_switch_rank_retry_required = true;
        masked_switch_code_basis_fingerprint = rank_minor_fingerprint(
            "native_full_root_identity_basis",
            &(0..TRACE_ROWS).collect::<Vec<_>>(),
            &(0..TRACE_ROWS).collect::<Vec<_>>(),
            &vec![1u32; TRACE_ROWS],
        );
        masked_switch_observation_rank_qm31 = observation_rank_qm31;
        masked_switch_kernel_qm31 = TRACE_ROWS - observation_rank_qm31;
        masked_switch_shared_c2_observation_rank_qm31 = observation_rank_qm31;
        masked_switch_shared_c2_kernel_qm31 = TRACE_ROWS - observation_rank_qm31;
        masked_switch_standalone_frontier_nodes =
            radix4_frontier_node_count(queries.to_vec(), encoder.codeword_len() / FIBER_SLOTS);
        masked_switch_shared_root_increment_bytes =
            16 * FIBER_SLOTS * schedule.query_count + 16 * usize::from(expose_target);
        masked_switch_standalone_increment_bytes = masked_switch_shared_root_increment_bytes
            + 32
            + 4
            + 32 * masked_switch_standalone_frontier_nodes;
    } else if matches!(
        late_switch_support,
        LateSwitchSupport::MaskedSlotZeroSingleCodeword
            | LateSwitchSupport::MaskedHighCoefficientSingleCodeword
            | LateSwitchSupport::MaskedSemanticHighSingleCodeword
            | LateSwitchSupport::MaskedSemanticHighSharedC2SingleCodeword
            | LateSwitchSupport::MaskedSemanticNatural18SharedC2SingleCodeword
            | LateSwitchSupport::MaskedFullXGammaLane
            | LateSwitchSupport::MaskedFullXGammaKernelLane
            | LateSwitchSupport::MaskedFullXFirstLaterLane
    ) {
        // One genuine pre-alpha source coordinate plus q+2 distinct late
        // message coordinates; q code-randomness coordinates mask q opens.
        let randomness = schedule.query_count;
        if randomness != 29 && randomness != 16 {
            return Err(StateOnlyHidingRankGateError::Shape);
        }
        let semantic_high_folded_single_codeword =
            late_switch_support == LateSwitchSupport::MaskedSemanticHighSingleCodeword;
        let semantic_high_shared_c2_single_codeword =
            late_switch_support == LateSwitchSupport::MaskedSemanticHighSharedC2SingleCodeword;
        let semantic_natural18_shared_c2_single_codeword =
            late_switch_support == LateSwitchSupport::MaskedSemanticNatural18SharedC2SingleCodeword;
        let semantic_high_single_codeword = semantic_high_folded_single_codeword
            || semantic_high_shared_c2_single_codeword
            || semantic_natural18_shared_c2_single_codeword;
        if semantic_high_single_codeword && randomness != 16 {
            return Err(StateOnlyHidingRankGateError::Shape);
        }
        let message = if semantic_high_folded_single_codeword
            || semantic_natural18_shared_c2_single_codeword
        {
            1
        } else if semantic_high_shared_c2_single_codeword {
            2
        } else {
            randomness + 3
        };
        let code_dimension = message + randomness;
        // The folded control has 17 logical coordinates but degree 17.  The
        // shared-C2 shape adds logical `1`, giving a square d=18 basis.
        let code_natural_dimension = if semantic_natural18_shared_c2_single_codeword {
            19
        } else {
            code_dimension + usize::from(semantic_high_folded_single_codeword)
        };
        let total_variables = 2 * code_dimension;
        let full_x_gamma_kernel_lane =
            late_switch_support == LateSwitchSupport::MaskedFullXGammaKernelLane;
        let full_x_gamma_lane = late_switch_support == LateSwitchSupport::MaskedFullXGammaLane
            || full_x_gamma_kernel_lane;
        let full_x_first_later_lane =
            late_switch_support == LateSwitchSupport::MaskedFullXFirstLaterLane;
        let physical_full_x_lane = full_x_gamma_lane || full_x_first_later_lane;
        let serialized_source_targets =
            late_switch_support == LateSwitchSupport::MaskedSlotZeroSingleCodeword;
        let early_coefficient = if semantic_high_single_codeword {
            18
        } else if late_switch_support == LateSwitchSupport::MaskedHighCoefficientSingleCodeword {
            message - 1
        } else {
            1
        };
        let early_row = FIBER_SLOTS * early_coefficient;
        // Source coordinates retain their exact old-view order.  The code
        // switch embeds those  q+3 coordinates into the complementary
        // ordinary-polynomial message space
        //   M = span{x, 1, x^(q+2), ..., x^(2q+2)}
        // and uses the universal randomness space
        //   R = (x^2+1) * P_<q.
        // M (+) R is all P_<2q+3.  Since P=3 mod 4, x^2+1 has no M31 root;
        // evaluation of R at any q distinct base-field points is therefore
        // diag(q_i^2+1) times a Vandermonde matrix and is always invertible.
        let mut source_message_coefficients = Vec::with_capacity(message);
        source_message_coefficients.push(early_coefficient);
        if semantic_high_shared_c2_single_codeword {
            source_message_coefficients.push(0);
        } else if !semantic_high_folded_single_codeword {
            source_message_coefficients
                .extend((0..message).filter(|&coefficient| coefficient != early_coefficient));
        }
        let mut message_ordinary_degrees = Vec::with_capacity(message);
        if semantic_high_folded_single_codeword {
            message_ordinary_degrees.push(1);
        } else if semantic_natural18_shared_c2_single_codeword {
            // B18 is a natural tensor-basis element, not ordinary x^18.  The
            // dedicated basis construction below ignores this placeholder.
            message_ordinary_degrees.push(18);
        } else if semantic_high_shared_c2_single_codeword {
            message_ordinary_degrees.extend([1, 0]);
        } else {
            message_ordinary_degrees.extend([1usize, 0]);
            message_ordinary_degrees.extend((randomness + 2)..code_dimension);
        }
        if message_ordinary_degrees.len() != message {
            return Err(StateOnlyHidingRankGateError::Shape);
        }
        let monomial_conversion = ordinary_monomials_in_natural_line_basis(code_natural_dimension);
        let code_basis = if semantic_natural18_shared_c2_single_codeword {
            let mut basis = Vec::with_capacity(code_dimension);
            let mut b18 = vec![M31::ZERO; code_natural_dimension];
            b18[18] = M31::ONE;
            basis.push(b18);
            for degree in 0..randomness {
                basis.push(
                    monomial_conversion[degree]
                        .iter()
                        .copied()
                        .zip(monomial_conversion[degree + 2].iter().copied())
                        .map(|(low, high)| low.add(high))
                        .collect(),
                );
            }
            masked_switch_code_basis_fingerprint =
                m31_matrix_fingerprint("semantic_natural18_shared_c2_b18_plus_x2p1_p16", &basis);
            basis
        } else if semantic_high_single_codeword {
            let mut basis = message_ordinary_degrees
                .iter()
                .map(|&degree| monomial_conversion[degree].clone())
                .collect::<Vec<_>>();
            for degree in 0..randomness {
                basis.push(
                    monomial_conversion[degree]
                        .iter()
                        .copied()
                        .zip(monomial_conversion[degree + 2].iter().copied())
                        .map(|(low, high)| low.add(high))
                        .collect(),
                );
            }
            masked_switch_code_basis_fingerprint = m31_matrix_fingerprint(
                if semantic_high_shared_c2_single_codeword {
                    "semantic_high_shared_c2_x_1_plus_x2p1_p16"
                } else {
                    "semantic_high_folded_x_plus_x2p1_p16"
                },
                &basis,
            );
            basis
        } else if randomness == 16 {
            if code_dimension != MASKED_SWITCH_UNIVERSAL_DIMENSION {
                return Err(StateOnlyHidingRankGateError::Shape);
            }
            masked_switch_code_basis_fingerprint = MASKED_SWITCH_UNIVERSAL_CODE_BASIS_FINGERPRINT;
            MASKED_SWITCH_UNIVERSAL_CODE_BASIS
                .iter()
                .map(|column| column.to_vec())
                .collect::<Vec<_>>()
        } else {
            let mut basis = message_ordinary_degrees
                .iter()
                .map(|&degree| monomial_conversion[degree].clone())
                .collect::<Vec<_>>();
            for degree in 0..randomness {
                basis.push(
                    monomial_conversion[degree]
                        .iter()
                        .copied()
                        .zip(monomial_conversion[degree + 2].iter().copied())
                        .map(|(low, high)| low.add(high))
                        .collect(),
                );
            }
            basis
        };
        let mut code_basis_rank = ColumnEchelon::new(code_natural_dimension);
        for column in &code_basis {
            code_basis_rank.insert(column.clone());
        }
        if code_basis.len() != code_dimension || code_basis_rank.rank != code_dimension {
            return Err(StateOnlyHidingRankGateError::Layout);
        }
        // Existing switches disclose the square natural-coefficient vector U.
        // The semantic-high subcode is rectangular (17 logical coordinates,
        // 18 natural coefficients), so its minimal d=17 wire discloses U in
        // the frozen logical basis instead.  Both are exact full-rank affine
        // reveals and retain U = F + delta X coordinate-for-coordinate.
        let u_reveal_basis = if semantic_high_folded_single_codeword
            || semantic_natural18_shared_c2_single_codeword
        {
            (0..code_dimension)
                .map(|coordinate| {
                    let mut column = vec![M31::ZERO; code_dimension];
                    column[coordinate] = M31::ONE;
                    column
                })
                .collect::<Vec<_>>()
        } else {
            code_basis.clone()
        };
        masked_switch_universal_mds_basis = true;
        masked_switch_code_basis_rank_m31 = code_basis_rank.rank;
        masked_switch_rank_retry_required = false;
        let delta = selected_late_switch_delta.unwrap_or(schedule.prefix.eta);
        if delta == QM31::ZERO {
            return Err(StateOnlyHidingRankGateError::Layout);
        }
        let queries = &schedule.queries[..schedule.query_count];
        let mut sorted_queries = queries.to_vec();
        sorted_queries.sort_unstable();
        sorted_queries.dedup();
        if sorted_queries.len() != randomness {
            return Err(StateOnlyHidingRankGateError::Shape);
        }
        let mut query_abscissae = queries
            .iter()
            .map(|&query| {
                line_domain_x_for_circle(domain_log, 1, query as usize)
                    .map_err(|_| StateOnlyHidingRankGateError::Encoding)
            })
            .collect::<Result<Vec<_>, _>>()?;
        query_abscissae.sort_unstable_by_key(|value| value.0);
        query_abscissae.dedup();
        masked_switch_query_abscissae_distinct = query_abscissae.len() == randomness;
        if !masked_switch_query_abscissae_distinct
            || query_abscissae
                .iter()
                .any(|&x| x.mul(x).add(M31::ONE) == M31::ZERO)
        {
            return Err(StateOnlyHidingRankGateError::Layout);
        }
        masked_switch_standalone_frontier_nodes = radix4_frontier_node_count(
            sorted_queries.clone(),
            encoder.codeword_len() / FIBER_SLOTS,
        );
        // The ordinary physical-X mode serializes its one target scalar.  In
        // the claim-preserving mode `L(X)=0` is enforced by the relation and
        // remains a rank-conditioning row, but no scalar is present on wire.
        masked_switch_shared_root_increment_bytes =
            usize::from(!full_x_gamma_kernel_lane) * 16 + 16 * code_dimension + 2 * 16 * randomness;
        masked_switch_standalone_increment_bytes = masked_switch_shared_root_increment_bytes
            + 32
            + 4
            + 32 * masked_switch_standalone_frontier_nodes;

        let indices = derive_circle_line_query_indices_for_count(
            queries,
            encoder.codeword_len() / FIBER_SLOTS,
        )
        .map_err(|_| StateOnlyHidingRankGateError::Shape)?;
        if physical_full_x_lane {
            // The physical X source message places natural line coefficient
            // `i` in root-zero C2 message row `4*i`.
            late_switch_source_rows.extend((0..code_dimension).map(|coefficient| 4 * coefficient));
        } else {
            // Legacy coefficient-selective diagnostics splice one root-zero
            // coordinate and q+2 freshly materialized root-one coordinates.
            late_switch_source_rows.push(early_row);
            late_switch_source_rows.extend(
                source_message_coefficients[1..]
                    .iter()
                    .map(|coefficient| 4 * coefficient),
            );
        }
        let first_later_natural_count = if full_x_first_later_lane {
            code_dimension + first_later_x_multiplier_degree
        } else {
            message
        };
        if first_later_natural_count > 256 {
            return Err(StateOnlyHidingRankGateError::Shape);
        }
        let first_later_tails = (0..first_later_natural_count)
            .map(|coefficient| {
                first_later_coefficient_tail(
                    &encoder,
                    domain_log,
                    coefficient,
                    schedule,
                    &indices.later,
                    layout,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        if first_later_tails
            .iter()
            .any(|tail| tail.len() != pcs_tail_qm31)
        {
            return Err(StateOnlyHidingRankGateError::Shape);
        }

        // Actual normalized line-code evaluations at the q root-one scalar
        // positions. Every coordinate is an ordinary natural line
        // coefficient; no post-alpha coefficient-selective scaling exists.
        let natural_code_columns = (0..first_later_natural_count.max(code_natural_dimension))
            .map(|coefficient| {
                first_later_coefficient_query_values(
                    &encoder,
                    domain_log,
                    coefficient,
                    schedule,
                    queries,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        if late_switch_support == LateSwitchSupport::MaskedHighCoefficientSingleCodeword {
            let certificate = profile21_high_switch_carry_certificate(queries)?;
            if certificate.evaluation_plus_leading_rank_qm31 != randomness + 1 {
                return Err(StateOnlyHidingRankGateError::Layout);
            }
            let exact_carry_columns = natural_code_columns[..message]
                .iter()
                .enumerate()
                .map(|(coefficient, column)| {
                    let mut column = column.clone();
                    column.push(if coefficient == early_coefficient {
                        QM31::ONE
                    } else {
                        QM31::ZERO
                    });
                    column
                })
                .collect::<Vec<_>>();
            if qm31_column_rank(&exact_carry_columns, randomness + 1) != randomness + 1 {
                return Err(StateOnlyHidingRankGateError::Layout);
            }
        }
        let code_columns = code_basis
            .iter()
            .map(|coefficients| {
                combine_natural_qm31_columns(
                    &natural_code_columns[..code_natural_dimension],
                    coefficients,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;

        // Bind the abstract polynomial proof to the exact production circle
        // encoder: each generated natural column must evaluate to its stated
        // ordinary polynomial at every sampled root-one abscissa. This guard
        // catches basis order, circle normalization, and query-layer drift.
        for (query_ordinal, &query) in queries.iter().enumerate() {
            let x = line_domain_x_for_circle(domain_log, 1, query as usize)
                .map_err(|_| StateOnlyHidingRankGateError::Encoding)?;
            for logical in 0..code_dimension {
                let expected = if semantic_natural18_shared_c2_single_codeword && logical == 0 {
                    natural_line_basis_polynomials(code_natural_dimension)[18]
                        .iter()
                        .rev()
                        .fold(M31::ZERO, |value, coefficient| {
                            value.mul(x).add(*coefficient)
                        })
                } else if logical < message {
                    x.pow(message_ordinary_degrees[logical] as u64)
                } else {
                    let degree = logical - message;
                    x.mul(x).add(M31::ONE).mul(x.pow(degree as u64))
                };
                if code_columns[logical][query_ordinal] != QM31::from_cm31(CM31::from_m31(expected))
                {
                    return Err(StateOnlyHidingRankGateError::Layout);
                }
            }
        }

        let first_later_multiplier_code_basis = if full_x_first_later_lane {
            let conversion = ordinary_monomials_in_natural_line_basis(first_later_natural_count);
            let multiplied = (0..code_dimension)
                .map(|logical| {
                    let base_terms = if logical < message {
                        vec![(message_ordinary_degrees[logical], M31::ONE)]
                    } else {
                        let degree = logical - message;
                        vec![(degree, M31::ONE), (degree + 2, M31::ONE)]
                    };
                    let mut ordinary = vec![M31::ZERO; first_later_natural_count];
                    for (base_degree, base_coefficient) in base_terms {
                        for (multiplier_degree, &multiplier_coefficient) in
                            first_later_x_multiplier_coefficients.iter().enumerate()
                        {
                            let degree = base_degree + multiplier_degree;
                            ordinary[degree] =
                                ordinary[degree].add(base_coefficient.mul(multiplier_coefficient));
                        }
                    }
                    let mut natural = vec![M31::ZERO; first_later_natural_count];
                    for (degree, &coefficient) in ordinary.iter().enumerate() {
                        if coefficient == M31::ZERO {
                            continue;
                        }
                        for (target, &basis) in natural.iter_mut().zip(&conversion[degree]) {
                            *target = target.add(coefficient.mul(basis));
                        }
                    }
                    natural
                })
                .collect::<Vec<_>>();

            for (query_ordinal, &query) in queries.iter().enumerate() {
                let x = line_domain_x_for_circle(domain_log, 1, query as usize)
                    .map_err(|_| StateOnlyHidingRankGateError::Encoding)?;
                let multiplier = first_later_x_multiplier_coefficients
                    .iter()
                    .rev()
                    .copied()
                    .fold(M31::ZERO, |value, coefficient| {
                        value.mul(x).add(coefficient)
                    });
                if multiplier == M31::ZERO {
                    return Err(StateOnlyHidingRankGateError::Layout);
                }
                for logical in 0..code_dimension {
                    let actual = natural_code_columns.iter().zip(&multiplied[logical]).fold(
                        QM31::ZERO,
                        |sum, (column, &coefficient)| {
                            sum.add(column[query_ordinal].mul_m31(coefficient))
                        },
                    );
                    let expected = code_columns[logical][query_ordinal].mul_m31(multiplier);
                    if actual != expected {
                        return Err(StateOnlyHidingRankGateError::Layout);
                    }
                }
            }
            multiplied
        } else {
            Vec::new()
        };

        // The same exact ordinary-polynomial multiplication is used by the
        // claim-preserving root-zero scan.  Unlike the first-later path, its
        // authenticated raw openings remain evaluations of X itself; only
        // the main gamma lane and its initial relation covector see pX.
        let full_x_gamma_multiplier_code_basis = if full_x_gamma_lane {
            let multiplied_natural_count = code_dimension + first_later_x_multiplier_degree;
            let conversion = ordinary_monomials_in_natural_line_basis(multiplied_natural_count);
            (0..code_dimension)
                .map(|logical| {
                    let base_terms = if logical < message {
                        vec![(message_ordinary_degrees[logical], M31::ONE)]
                    } else {
                        let degree = logical - message;
                        vec![(degree, M31::ONE), (degree + 2, M31::ONE)]
                    };
                    let mut ordinary = vec![M31::ZERO; multiplied_natural_count];
                    for (base_degree, base_coefficient) in base_terms {
                        for (multiplier_degree, &multiplier_coefficient) in
                            first_later_x_multiplier_coefficients.iter().enumerate()
                        {
                            let degree = base_degree + multiplier_degree;
                            ordinary[degree] =
                                ordinary[degree].add(base_coefficient.mul(multiplier_coefficient));
                        }
                    }
                    let mut natural = vec![M31::ZERO; multiplied_natural_count];
                    for (degree, &coefficient) in ordinary.iter().enumerate() {
                        if coefficient == M31::ZERO {
                            continue;
                        }
                        for (target, &basis) in natural.iter_mut().zip(&conversion[degree]) {
                            *target = target.add(coefficient.mul(basis));
                        }
                    }
                    natural
                })
                .collect::<Vec<_>>()
        } else {
            Vec::new()
        };

        let randomness_columns = &code_columns[message..];
        masked_switch_q_randomness_rank_qm31 = qm31_column_rank(randomness_columns, randomness);
        if masked_switch_q_randomness_rank_qm31 != randomness {
            return Err(StateOnlyHidingRankGateError::Layout);
        }
        if semantic_high_single_codeword
            && qm31_column_rank(&code_columns, randomness) != randomness
        {
            return Err(StateOnlyHidingRankGateError::Layout);
        }
        // Universal q16 identity for both semantic-high shapes. At distinct
        // abscissae the randomness minor is
        //   diag(q_i^2+1) * Vandermonde(q_i),
        // hence invertible over M31.  The d17 folded control has a unique
        // evaluation-kernel direction and its logical `x` coordinate is
        // nonzero. The d18 raw shape has two folded-kernel directions; the raw
        // four-symbol view below removes one and is asserted separately to
        // leave a unique production-conditioned direction.

        // With U fixed, dF = -delta*dX. Thus the two authenticated q
        // co-openings have columns (A v, -delta A v), whose rank is exactly
        // q; the 29 encoding-randomness coordinates absorb every query.
        let conditional_q_columns = code_columns
            .iter()
            .map(|column| {
                let mut pair = column.clone();
                pair.extend(column.iter().copied().map(|value| delta.neg().mul(value)));
                pair
            })
            .collect::<Vec<_>>();
        masked_switch_q_coopening_rank_qm31 =
            qm31_column_rank(&conditional_q_columns, 2 * randomness);

        // Exact widened-C2 source view.  The physical profile-21 verifier
        // authenticates all four circle symbols, so the real gamma-lane
        // quotient must use this map rather than its folded-line shorthand.
        let raw_natural_code_columns = (0..code_natural_dimension)
            .map(|coefficient| {
                first_layer0_coefficient_query_fibers(&encoder, coefficient, queries)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let raw_code_columns = code_basis
            .iter()
            .map(|coefficients| {
                combine_natural_qm31_columns(&raw_natural_code_columns, coefficients)
            })
            .collect::<Result<Vec<_>, _>>()?;
        // Literal production identity between the four authenticated C2
        // symbols and the folded scalar codeword X(q).  This validates the raw
        // leakage model, but does not bind a selective old-view carry which
        // omits the randomness coordinates (see the explicit caveat below).
        for logical in 0..code_dimension {
            for (query_ordinal, &query) in queries.iter().enumerate() {
                let start = FIBER_SLOTS * query_ordinal;
                let fiber: [QM31; FIBER_SLOTS] = raw_code_columns[logical]
                    [start..start + FIBER_SLOTS]
                    .try_into()
                    .map_err(|_| StateOnlyHidingRankGateError::Shape)?;
                let folded = aspis_core::circle_fri::normalized_circle_to_line_arity4_at_fiber_for_domain_log(
                    fiber,
                    schedule.alpha[0],
                    domain_log,
                    query as usize,
                )
                .map_err(|_| StateOnlyHidingRankGateError::Encoding)?;
                if folded != code_columns[logical][query_ordinal] {
                    return Err(StateOnlyHidingRankGateError::Layout);
                }
            }
        }
        masked_switch_shared_c2_randomness_rank_qm31 =
            qm31_column_rank(&raw_code_columns[message..], FIBER_SLOTS * randomness);
        if semantic_high_single_codeword && masked_switch_shared_c2_randomness_rank_qm31 == 0 {
            return Err(StateOnlyHidingRankGateError::Layout);
        }
        // Every semantic-high randomness direction has zero old-view PCS
        // carry below, while this exact authenticated q map has rank 16. Thus
        // no literal identity `S_X(q)=X(q)` can bind the selective carry to the
        // full committed X word. Any green rank result from these modes remains
        // an abstract/unbound candidate until an additional binding equation
        // is supplied. Carrying full X instead is modeled by the physical-X
        // probes, whose exact result is already RED.

        let target = if serialized_source_targets {
            let folded_weights = first_later_weights(schedule, layout)?;
            (0..message)
                .map(|variable| {
                    folded_weights.weight_at(source_message_coefficients[variable] as u32)
                })
                .collect::<Vec<_>>()
        } else {
            Vec::new()
        };

        let x_relation_target = if physical_full_x_lane {
            let weights = if full_x_gamma_lane {
                initial_relation_weights(schedule, layout)?
            } else {
                first_later_weights(schedule, layout)?
            };
            let relation_basis = if full_x_first_later_lane {
                &first_later_multiplier_code_basis
            } else if full_x_gamma_lane {
                &full_x_gamma_multiplier_code_basis
            } else {
                &code_basis
            };
            relation_basis
                .iter()
                .map(|column| {
                    column
                        .iter()
                        .copied()
                        .enumerate()
                        .filter(|(_, coefficient)| *coefficient != M31::ZERO)
                        .fold(QM31::ZERO, |sum, (natural, coefficient)| {
                            let row = if full_x_gamma_lane {
                                FIBER_SLOTS * natural
                            } else {
                                natural
                            };
                            sum.add(weights.weight_at(row as u32).mul_m31(coefficient))
                        })
                })
                .collect::<Vec<_>>()
        } else {
            Vec::new()
        };
        let u_relation_target = if full_x_first_later_lane {
            let weights = first_later_weights(schedule, layout)?;
            code_basis
                .iter()
                .map(|column| {
                    column
                        .iter()
                        .copied()
                        .enumerate()
                        .filter(|(_, coefficient)| *coefficient != M31::ZERO)
                        .fold(QM31::ZERO, |sum, (natural, coefficient)| {
                            sum.add(weights.weight_at(natural as u32).mul_m31(coefficient))
                        })
                })
                .collect::<Vec<_>>()
        } else {
            Vec::new()
        };

        // The legacy scalar-target path serializes
        //   U[2q+3], t_X, mu_F, A X[q], A F[q].
        // The high-coefficient candidate models the frozen target-free seam:
        //   U[2q+3], A X[q], A F[q].
        // The physical root-zero-X candidate serializes
        //   U[2q+3], xi_X, raw X[4q], raw F[4q],
        // where xi_X is the complete initial relation covector and is fixed
        // before gamma.  In all three paths tau=L(phi(U)) is derived from U.
        // The physical first-later-X candidate has the same affine View, but
        // its one X functional is the serialized tau=L(phi(U+X)).
        // Its post-delta tau=L(phi(U)) is deterministic from disclosed U and
        // therefore is not an independent affine observation row.  In both
        // paths A F=A U-delta*A X is left for exact elimination to discover.
        let target_observations = if physical_full_x_lane {
            1
        } else {
            2 * usize::from(serialized_source_targets)
        };
        let opening_observations = if physical_full_x_lane {
            FIBER_SLOTS * randomness
        } else {
            randomness
        };
        let observation_qm31 = code_dimension + target_observations + 2 * opening_observations;
        let mut observation_columns = Vec::with_capacity(total_variables);
        for variable in 0..total_variables {
            let fresh = variable >= code_dimension;
            let coordinate = variable % code_dimension;
            let mut column = vec![QM31::ZERO; observation_qm31];
            let reveal_scale = if fresh { QM31::ONE } else { delta };
            for (natural, &coefficient) in u_reveal_basis[coordinate].iter().enumerate() {
                column[natural] = reveal_scale.mul_m31(coefficient);
            }
            if serialized_source_targets && coordinate < message {
                column[code_dimension + usize::from(fresh)] = target[coordinate];
            } else if physical_full_x_lane && !fresh {
                column[code_dimension] = x_relation_target[coordinate];
            }
            let query_start =
                code_dimension + target_observations + usize::from(fresh) * opening_observations;
            let opened = if physical_full_x_lane {
                &raw_code_columns[coordinate]
            } else {
                &code_columns[coordinate]
            };
            for (query, value) in opened.iter().copied().enumerate() {
                column[query_start + query] = value;
            }
            observation_columns.push(column);
        }
        masked_switch_observation_rank_qm31 =
            qm31_column_rank(&observation_columns, observation_qm31);
        masked_switch_variables_qm31 = total_variables;
        masked_switch_kernel_qm31 =
            total_variables.saturating_sub(masked_switch_observation_rank_qm31);
        if full_x_first_later_lane {
            let without_u_observations = 1 + 2 * opening_observations;
            let without_u_columns = (0..total_variables)
                .map(|variable| {
                    let fresh = variable >= code_dimension;
                    let coordinate = variable % code_dimension;
                    let mut column = vec![QM31::ZERO; without_u_observations];
                    column[0] = if fresh {
                        u_relation_target[coordinate]
                    } else {
                        delta
                            .mul(u_relation_target[coordinate])
                            .add(x_relation_target[coordinate])
                    };
                    let query_start = 1 + usize::from(fresh) * opening_observations;
                    for (query, value) in raw_code_columns[coordinate].iter().copied().enumerate() {
                        column[query_start + query] = value;
                    }
                    column
                })
                .collect::<Vec<_>>();
            masked_switch_without_u_observation_rank_qm31 =
                qm31_column_rank(&without_u_columns, without_u_observations);
            masked_switch_without_u_kernel_qm31 =
                total_variables.saturating_sub(masked_switch_without_u_observation_rank_qm31);
            // Equal ranks of the two views would not by itself prove that the
            // disclosed U block is redundant: equal-dimensional row spaces
            // can be different.  Append U's complete natural-coefficient
            // reveal to the no-U view and test row-space containment exactly.
            // The union must also equal the original `(U, L(pX), AX, AF)`
            // view, because `L(U+pX) = L(U) + L(pX)`.
            let without_u_plus_u_columns = (0..total_variables)
                .map(|variable| {
                    let fresh = variable >= code_dimension;
                    let coordinate = variable % code_dimension;
                    let mut column = without_u_columns[variable].clone();
                    let reveal_scale = if fresh { QM31::ONE } else { delta };
                    column.extend(
                        code_basis[coordinate]
                            .iter()
                            .copied()
                            .map(|coefficient| reveal_scale.mul_m31(coefficient)),
                    );
                    column
                })
                .collect::<Vec<_>>();
            let without_u_plus_u_rank = qm31_column_rank(
                &without_u_plus_u_columns,
                without_u_observations + code_dimension,
            );
            if without_u_plus_u_rank != masked_switch_observation_rank_qm31 {
                return Err(StateOnlyHidingRankGateError::Layout);
            }
            masked_switch_u_observation_rank_redundant =
                without_u_plus_u_rank == masked_switch_without_u_observation_rank_qm31;
        }
        late_switch_variables_qm31 = code_dimension;
        late_switch_conditioned_kernel_qm31 = masked_switch_kernel_qm31;

        // Shared-root alternative: put X/F in two extra lanes of the
        // pre-alpha root-zero C2 leaf.  Verifying that leaf reveals four
        // circle symbols per q for each word, not merely their one
        // alpha-folded line value.  Rebuild the *complete* public-view map so
        // the Merkle saving cannot be booked while silently spending the
        // hiding kernel.
        let shared_c2_observations =
            code_dimension + target_observations + 2 * FIBER_SLOTS * randomness;
        let shared_c2_columns = (0..total_variables)
            .map(|variable| {
                let fresh = variable >= code_dimension;
                let coordinate = variable % code_dimension;
                let mut column = vec![QM31::ZERO; shared_c2_observations];
                let reveal_scale = if fresh { QM31::ONE } else { delta };
                for (natural, &coefficient) in u_reveal_basis[coordinate].iter().enumerate() {
                    column[natural] = reveal_scale.mul_m31(coefficient);
                }
                if serialized_source_targets && coordinate < message {
                    column[code_dimension + usize::from(fresh)] = target[coordinate];
                } else if physical_full_x_lane && !fresh {
                    column[code_dimension] = x_relation_target[coordinate];
                }
                let raw_start = code_dimension
                    + target_observations
                    + usize::from(fresh) * FIBER_SLOTS * randomness;
                for (observation, value) in raw_code_columns[coordinate].iter().copied().enumerate()
                {
                    column[raw_start + observation] = value;
                }
                column
            })
            .collect::<Vec<_>>();
        masked_switch_shared_c2_observation_rank_qm31 =
            qm31_column_rank(&shared_c2_columns, shared_c2_observations);
        masked_switch_shared_c2_kernel_qm31 =
            total_variables.saturating_sub(masked_switch_shared_c2_observation_rank_qm31);
        if semantic_high_shared_c2_single_codeword || semantic_natural18_shared_c2_single_codeword {
            late_switch_conditioned_kernel_qm31 = masked_switch_shared_c2_kernel_qm31;
        }

        let (conditioned_observation_columns, conditioned_observation_qm31, conditioned_view_rank) =
            if semantic_high_shared_c2_single_codeword
                || semantic_natural18_shared_c2_single_codeword
            {
                (
                    &shared_c2_columns,
                    shared_c2_observations,
                    masked_switch_shared_c2_observation_rank_qm31,
                )
            } else {
                (
                    &observation_columns,
                    observation_qm31,
                    masked_switch_observation_rank_qm31,
                )
            };

        // The U reveal is a full-rank affine OTP.  The following two
        // line-OOD Horner values are retained only as a legacy standalone
        // diagnostic: they are public linear forms of U, but the selected
        // profile-21 direct-q extension serializes no isolated switch beta
        // equations or values.
        let otp_columns = (0..total_variables)
            .map(|variable| {
                let fresh = variable >= code_dimension;
                let coordinate = variable % code_dimension;
                let mut column = vec![QM31::ZERO; code_dimension];
                let reveal_scale = if fresh { QM31::ONE } else { delta };
                for (natural, &coefficient) in u_reveal_basis[coordinate].iter().enumerate() {
                    column[natural] = reveal_scale.mul_m31(coefficient);
                }
                column
            })
            .collect::<Vec<_>>();
        masked_switch_otp_rank_qm31 = qm31_column_rank(&otp_columns, code_dimension);
        masked_switch_u_rank_qm31 = masked_switch_otp_rank_qm31;
        let betas = schedule.line_ood_points[0];
        let beta_weights = betas
            .iter()
            .map(|&beta| {
                let mut weights = WeightAccumulator::empty(8);
                weights
                    .add_line_tensor(QM31::ONE, beta)
                    .map_err(|_| StateOnlyHidingRankGateError::Layout)?;
                Ok(weights)
            })
            .collect::<Result<Vec<_>, StateOnlyHidingRankGateError>>()?;
        let u_plus_beta_columns = (0..code_dimension)
            .map(|coordinate| {
                let mut column = vec![QM31::ZERO; code_dimension + CANDIDATE_OOD_SAMPLES];
                for (natural, &coefficient) in u_reveal_basis[coordinate].iter().enumerate() {
                    column[natural] = QM31::from_cm31(CM31::from_m31(coefficient));
                }
                for sample in 0..CANDIDATE_OOD_SAMPLES {
                    column[code_dimension + sample] =
                        natural_line_linear_form(&beta_weights[sample], &code_basis[coordinate]);
                }
                column
            })
            .collect::<Vec<_>>();
        masked_switch_u_plus_legacy_ood_diagnostic_rank_qm31 =
            qm31_column_rank(&u_plus_beta_columns, code_dimension + CANDIDATE_OOD_SAMPLES);

        let full_x_code_tails = if full_x_gamma_lane {
            let raw_natural_tails = (0..code_dimension + first_later_x_multiplier_degree)
                .map(|natural| {
                    raw_root0_row_pcs_tail_sparse(
                        &encoder,
                        domain_log,
                        FIBER_SLOTS * natural,
                        schedule,
                        &indices.later,
                        layout,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            if raw_natural_tails
                .iter()
                .any(|tail| tail.len() != pcs_tail_qm31)
            {
                return Err(StateOnlyHidingRankGateError::Shape);
            }
            full_x_gamma_multiplier_code_basis
                .iter()
                .map(|coefficients| combine_natural_qm31_columns(&raw_natural_tails, coefficients))
                .collect::<Result<Vec<_>, _>>()?
        } else {
            Vec::new()
        };
        let full_x_first_later_code_tails = if full_x_first_later_lane {
            first_later_multiplier_code_basis
                .iter()
                .map(|coefficients| combine_natural_qm31_columns(&first_later_tails, coefficients))
                .collect::<Result<Vec<_>, _>>()?
        } else {
            Vec::new()
        };
        let full_x_gamma_scale = gamma_power(schedule.prefix.gamma, g_generator_index + 1);

        // Quotient every serialized switch field before inserting its old
        // View image. t_X is not appended to the old ambient vector: it
        // replaces the already-running target coordinate carried by p0.
        let mut quotient = CarryEchelon::new(4 * conditioned_observation_qm31);
        let mut conditioned = pcs_rank.clone();
        for variable in 0..total_variables {
            for tower_coordinate in 0..4 {
                let basis = state_only_mask_tower_basis(tower_coordinate);
                let mut observation = Vec::with_capacity(4 * conditioned_observation_qm31);
                append_qm31_coordinates(
                    &mut observation,
                    conditioned_observation_columns[variable]
                        .iter()
                        .copied()
                        .map(|value| value.mul(basis)),
                );
                let carry = if full_x_gamma_lane && variable < code_dimension {
                    first_later_pcs_image(
                        &full_x_code_tails[variable],
                        full_x_gamma_scale.mul(basis),
                        h_raw_qm31,
                    )
                } else if full_x_gamma_lane {
                    vec![M31::ZERO; joint_pcs_m31]
                } else if full_x_first_later_lane && variable < code_dimension {
                    first_later_pcs_image(
                        &full_x_first_later_code_tails[variable],
                        basis,
                        h_raw_qm31,
                    )
                } else if full_x_first_later_lane {
                    vec![M31::ZERO; joint_pcs_m31]
                } else if variable == 0 {
                    combined_pcs_image(&rows, early_row, basis, h_raw_qm31, pcs_tail_qm31)
                } else if variable < message {
                    first_later_pcs_image(
                        &first_later_tails[source_message_coefficients[variable]],
                        basis,
                        h_raw_qm31,
                    )
                } else {
                    vec![M31::ZERO; joint_pcs_m31]
                };
                let source_id = 4 * variable + tower_coordinate;
                match quotient.reduce_with_pivot(observation, carry) {
                    CarryReduction::Pivot { row, value } => {
                        late_switch_observation_sources.push(source_id);
                        late_switch_observation_rows.push(row);
                        late_switch_observation_values.push(value);
                    }
                    CarryReduction::Kernel(kernel) => {
                        if let Some((pivot, value)) = conditioned.insert_with_pivot_value(kernel) {
                            late_switch_minor_sources.push(source_id);
                            late_switch_minor_rows.push(pivot);
                            late_switch_minor_values.push(value);
                            let tail_pivot = pivot.saturating_sub(4 * h_raw_qm31);
                            let later_m31 = 4 * (pcs_tail_qm31 - 40);
                            if tail_pivot < later_m31 {
                                late_switch_complement_pivots_later_m31 += 1;
                            } else if tail_pivot < later_m31 + 4 * 8 {
                                late_switch_complement_pivots_ood_m31 += 1;
                            } else if tail_pivot < later_m31 + 4 * (8 + 28) {
                                late_switch_complement_pivots_relation_m31 += 1;
                            } else {
                                late_switch_complement_pivots_final_m31 += 1;
                            }
                        }
                    }
                }
            }
        }
        if quotient.rank != 4 * conditioned_view_rank {
            return Err(StateOnlyHidingRankGateError::Layout);
        }
        late_switch_conditioned_rank = conditioned.rank;
        late_switch_ambient_deficit_m31 =
            declared.rank.saturating_sub(late_switch_conditioned_rank);
        let pre_semantic = conditioned.rank;
        for image in &witness_semantic_complement_images {
            if let Some(pivot) = conditioned.insert_with_pivot(image.clone()) {
                late_switch_semantic_new_pivots_m31.push(pivot);
            }
        }
        late_switch_semantic_augmented_rank = conditioned.rank;
        late_switch_contains_conservative_semantic_superset = conditioned.rank == pre_semantic;
    } else if late_switch_probe {
        // Strict root-1 timing. Rows 1/2/3 collapse into folded coefficient
        // zero; rows 4,8,...,112 become coefficients 1..28. Round-zero OOD
        // and p0 were already serialized and are zero in every image below.
        match late_switch_support {
            LateSwitchSupport::StructuredSource31 => {
                late_switch_source_rows.extend([1usize, 2]);
                late_switch_source_rows.extend((1..=28).map(|index| 4 * index));
                late_switch_source_rows.push(3);
            }
            LateSwitchSupport::DistinctFolded31 => {
                late_switch_source_rows.extend((0..=30).map(|index| 4 * index));
            }
            LateSwitchSupport::None
            | LateSwitchSupport::WitnessDifferenceSuperset
            | LateSwitchSupport::MaskedSlotZeroSingleCodeword
            | LateSwitchSupport::MaskedHighCoefficientSingleCodeword
            | LateSwitchSupport::MaskedSemanticHighSingleCodeword
            | LateSwitchSupport::MaskedSemanticHighSharedC2SingleCodeword
            | LateSwitchSupport::MaskedSemanticNatural18SharedC2SingleCodeword
            | LateSwitchSupport::MaskedFullXGammaLane
            | LateSwitchSupport::MaskedFullXGammaKernelLane
            | LateSwitchSupport::MaskedFullXFirstLaterLane
            | LateSwitchSupport::LeanNativeFullRootX
            | LateSwitchSupport::LeanNativeFullRootXRawOnlyControl => {
                unreachable!()
            }
        }
        late_switch_variables_qm31 = late_switch_source_rows.len();
        late_switch_conditioned_kernel_qm31 = late_switch_variables_qm31 - 1;

        let indices = derive_circle_line_query_indices_for_count(
            &schedule.queries[..schedule.query_count],
            encoder.codeword_len() / FIBER_SLOTS,
        )
        .map_err(|_| StateOnlyHidingRankGateError::Shape)?;
        let maximum_coefficient = late_switch_source_rows
            .iter()
            .map(|row| row / 4)
            .max()
            .ok_or(StateOnlyHidingRankGateError::Layout)?;
        let first_later_tails = (0..=maximum_coefficient)
            .map(|coefficient| {
                first_later_coefficient_tail(
                    &encoder,
                    domain_log,
                    coefficient,
                    schedule,
                    &indices.later,
                    layout,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        if first_later_tails
            .iter()
            .any(|tail| tail.len() != pcs_tail_qm31)
        {
            return Err(StateOnlyHidingRankGateError::Shape);
        }
        let folded_weights = first_later_weights(schedule, layout)?;
        let alpha = schedule.alpha[0];
        let alpha_powers = [QM31::ONE, alpha, alpha.square(), alpha.pow(3)];
        let claim_coefficients = late_switch_source_rows
            .iter()
            .map(|row| alpha_powers[row & 3].mul(folded_weights.weight_at((row / 4) as u32)))
            .collect::<Vec<_>>();
        let dependent = late_switch_source_rows.len() - 1;
        let dependent_claim = claim_coefficients[dependent];
        if dependent_claim == QM31::ZERO {
            return Err(StateOnlyHidingRankGateError::Layout);
        }

        let mut conditioned = pcs_rank.clone();
        for variable in 0..dependent {
            let row = late_switch_source_rows[variable];
            let row_fold_scale = alpha_powers[row & 3];
            let dependent_row = late_switch_source_rows[dependent];
            let dependent_fold_scale = alpha_powers[dependent_row & 3];
            for coordinate in 0..4 {
                let basis = state_only_mask_tower_basis(coordinate);
                let left = first_later_pcs_image(
                    &first_later_tails[row / 4],
                    row_fold_scale.mul(dependent_claim).mul(basis),
                    h_raw_qm31,
                );
                let right = first_later_pcs_image(
                    &first_later_tails[dependent_row / 4],
                    dependent_fold_scale
                        .mul(claim_coefficients[variable])
                        .mul(basis),
                    h_raw_qm31,
                );
                if let Some(pivot) = conditioned.insert_with_pivot(
                    left.into_iter()
                        .zip(right)
                        .map(|(left, right)| left.sub(right))
                        .collect(),
                ) {
                    let tail_pivot = pivot.saturating_sub(4 * h_raw_qm31);
                    let later_m31 = 4 * (pcs_tail_qm31 - 40);
                    if tail_pivot < later_m31 {
                        late_switch_complement_pivots_later_m31 += 1;
                    } else if tail_pivot < later_m31 + 4 * 8 {
                        late_switch_complement_pivots_ood_m31 += 1;
                    } else if tail_pivot < later_m31 + 4 * (8 + 28) {
                        late_switch_complement_pivots_relation_m31 += 1;
                    } else {
                        late_switch_complement_pivots_final_m31 += 1;
                    }
                }
            }
        }
        late_switch_conditioned_rank = conditioned.rank;
        late_switch_ambient_deficit_m31 =
            declared.rank.saturating_sub(late_switch_conditioned_rank);
    }

    let late_switch_complement_minor = RankMinorProvenance::from_parts(
        if late_switch_support == LateSwitchSupport::MaskedSemanticHighSingleCodeword {
            "semantic_high_folded_complement"
        } else if late_switch_support == LateSwitchSupport::MaskedSemanticHighSharedC2SingleCodeword
        {
            "semantic_high_shared_c2_complement"
        } else if late_switch_support
            == LateSwitchSupport::MaskedSemanticNatural18SharedC2SingleCodeword
        {
            "semantic_natural18_shared_c2_complement"
        } else if matches!(
            late_switch_support,
            LateSwitchSupport::LeanNativeFullRootX
                | LateSwitchSupport::LeanNativeFullRootXRawOnlyControl
        ) {
            "native_full_root_x_complement"
        } else {
            "late_switch_complement_68"
        },
        late_switch_minor_sources,
        late_switch_minor_rows,
        late_switch_minor_values,
    );
    let late_switch_observation_minor = RankMinorProvenance::from_parts(
        if late_switch_support == LateSwitchSupport::MaskedSemanticHighSingleCodeword {
            "semantic_high_folded_observation"
        } else if late_switch_support == LateSwitchSupport::MaskedSemanticHighSharedC2SingleCodeword
        {
            "semantic_high_shared_c2_observation"
        } else if late_switch_support
            == LateSwitchSupport::MaskedSemanticNatural18SharedC2SingleCodeword
        {
            "semantic_natural18_shared_c2_observation"
        } else if matches!(
            late_switch_support,
            LateSwitchSupport::LeanNativeFullRootX
                | LateSwitchSupport::LeanNativeFullRootXRawOnlyControl
        ) {
            "native_full_root_x_observation"
        } else {
            "late_switch_observation_208"
        },
        late_switch_observation_sources,
        late_switch_observation_rows,
        late_switch_observation_values,
    );

    if coordinate_factored_mask_columns.is_none()
        && !late_switch_probe
        && !allow_ambient_deficit
        && before != declared.rank
    {
        return Err(StateOnlyHidingRankGateError::JointPcsRank {
            got: if late_switch_probe {
                late_switch_conditioned_rank
            } else {
                before
            },
            want: declared.rank,
            pre_helper: pre_helper_pcs_rank,
            declared_combined: declared_combined_rank,
            declared_inactive_helper: declared_inactive_helper_rank,
            declared_active_helper: declared.rank,
        });
    }

    Ok(StateOnlyHidingRankGateReport {
        pcs_schedule: match pcs_schedule {
            PcsSchedule::Arity4x4 => "arity4x4",
            PcsSchedule::Arity4ThenArity8 => "arity4_then_arity8_final32",
            PcsSchedule::RootMessage => "root_message_exact_sequence",
            PcsSchedule::RootMessageV6Log20 => "v6_log20_root_message_exact_sequence",
        },
        tail_qm31_probe: !tail_qm31_mask_factors.is_empty(),
        tail_qm31_mask_factor: match tail_qm31_mask_factors {
            [] => "none",
            [factor] => factor.label(),
            _ => "multiple_parameterized_host_only",
        },
        first_later_x_multiplier: if late_switch_support
            == LateSwitchSupport::MaskedFullXFirstLaterLane
            || late_switch_support == LateSwitchSupport::MaskedFullXGammaKernelLane
        {
            first_later_x_multiplier.label()
        } else {
            "none"
        },
        first_later_x_multiplier_degree,
        shared_linear_factor_probe: factor_schedule != FactorSchedule::Production,
        coordinate_factored_mask_columns: coordinate_factored_mask_columns.unwrap_or(0),
        late_switch_probe,
        complete_ambient_rank: sumcheck.rank == MASK_SUMCHECK_QUOTIENT_M31
            && if late_switch_probe {
                late_switch_ambient_deficit_m31 == 0
            } else {
                before == declared.rank
            },
        query_count: schedule.query_count,
        c1_raw_m31,
        g_raw_m31,
        masked_sumcheck_m31: sc_m31,
        masked_sumcheck_rank: sumcheck.rank,
        joint_pcs_m31,
        joint_pcs_declared_rank: declared.rank,
        joint_pcs_rank: before,
        helper_augmented_rank: augmented.rank,
        pre_helper_pcs_rank,
        declared_combined_rank,
        declared_inactive_helper_rank,
        semantic_mask_basis_m31,
        semantic_raw_kernel_m31,
        mask_only_basis_m31,
        mask_only_raw_kernel_m31,
        g_mask_basis_m31,
        g_raw_kernel_m31,
        tail_qm31_basis_m31,
        tail_qm31_raw_kernel_m31,
        post_sumcheck_kernel_m31,
        h_inactive_mask_basis_m31,
        ambient_combined_domain_qm31: TRACE_ROWS - 1,
        ambient_inactive_helper_domain_qm31: inactive.len() - 1,
        ambient_active_helper_domain_qm31: active_rows.len() - 1,
        baseline_valid_witness_containment,
        baseline_ambient_deficit_m31,
        witness_difference_probe,
        witness_semantic_superset_generators_m31,
        witness_semantic_superset_rank,
        witness_legal_sumcheck_generators_m31,
        witness_legal_sumcheck_rank,
        witness_compatibility_rank_m31,
        witness_direct_sum_mask_view_rank_m31: witness_difference_probe
            .then_some(witness_direct_sum_mask_view_rank_m31),
        witness_direct_sum_physical_augmented_view_rank_m31: witness_difference_probe
            .then_some(witness_direct_sum_physical_augmented_view_rank_m31),
        witness_direct_sum_legal_augmented_view_rank_m31: witness_difference_probe
            .then_some(witness_direct_sum_legal_augmented_view_rank_m31),
        witness_direct_sum_helper_augmented_view_rank_m31: witness_difference_probe
            .then_some(witness_direct_sum_helper_augmented_view_rank_m31),
        witness_direct_sum_physical_contained: witness_difference_probe.then_some(
            witness_direct_sum_physical_augmented_view_rank_m31
                == witness_direct_sum_mask_view_rank_m31,
        ),
        witness_direct_sum_legal_contained: witness_difference_probe.then_some(
            witness_direct_sum_legal_augmented_view_rank_m31
                == witness_direct_sum_mask_view_rank_m31,
        ),
        witness_direct_sum_helper_contained: witness_difference_probe.then_some(
            witness_direct_sum_helper_augmented_view_rank_m31
                == witness_direct_sum_mask_view_rank_m31,
        ),
        witness_direct_sum_unbalanced_physical_augmented_view_rank_m31: witness_difference_probe
            .then_some(witness_direct_sum_unbalanced_physical_augmented_view_rank_m31),
        witness_direct_sum_unbalanced_physical_contained: witness_difference_probe.then_some(
            witness_direct_sum_unbalanced_physical_augmented_view_rank_m31
                == witness_direct_sum_mask_view_rank_m31,
        ),
        witness_coupled_physical_augmented_view_rank_m31: witness_difference_probe
            .then_some(witness_coupled_physical_augmented_view_rank_m31),
        witness_coupled_legal_augmented_view_rank_m31: witness_difference_probe
            .then_some(witness_coupled_legal_augmented_view_rank_m31),
        witness_coupled_helper_augmented_view_rank_m31: witness_difference_probe
            .then_some(witness_coupled_helper_augmented_view_rank_m31),
        witness_coupled_physical_contained: witness_difference_probe.then_some(
            witness_coupled_physical_augmented_view_rank_m31
                == witness_direct_sum_mask_view_rank_m31,
        ),
        witness_coupled_legal_contained: witness_difference_probe.then_some(
            witness_coupled_legal_augmented_view_rank_m31 == witness_direct_sum_mask_view_rank_m31,
        ),
        witness_coupled_helper_contained: witness_difference_probe.then_some(
            witness_coupled_helper_augmented_view_rank_m31 == witness_direct_sum_mask_view_rank_m31,
        ),
        witness_coupled_legal_sumcheck_generators_m31,
        witness_coupled_terminal_dependent_observation,
        witness_coupled_terminal_functional_fingerprint,
        witness_coupled_terminal_identity_guard,
        witness_mask_raw_kernel_terminal_zero_sources_m31,
        witness_mask_raw_kernel_terminal_zero_guard,
        witness_h_zero_sumcheck_terminal_guard,
        witness_mask_sumcheck_equals_terminal_kernel,
        witness_compatibility_terminal_map_rank_m31,
        witness_compatibility_terminal_map_fingerprint,
        witness_compatibility_pivot_sources,
        witness_compatibility_pivot_rows_m31,
        witness_semantic_kernel_coefficients_m31,
        witness_semantic_sparse_dense_guard,
        witness_semantic_sparse_dense_fingerprint,
        witness_unbalanced_semantic_superset_generators_m31,
        witness_unbalanced_semantic_superset_rank,
        witness_unbalanced_compatibility_rank_m31,
        witness_unbalanced_compatibility_pivot_sources,
        witness_unbalanced_sparse_dense_guard,
        witness_unbalanced_sparse_dense_fingerprint,
        witness_unbalanced_semantic_superset_minor,
        witness_difference_projection,
        witness_semantic_superset_minor,
        witness_legal_sumcheck_minor,
        late_switch_source_rows,
        late_switch_variables_qm31,
        late_switch_conditioned_kernel_qm31,
        late_switch_conditioned_rank,
        late_switch_semantic_augmented_rank,
        late_switch_semantic_new_pivots_m31,
        late_switch_contains_conservative_semantic_superset,
        late_switch_ambient_deficit_m31,
        late_switch_complement_pivots_later_m31,
        late_switch_complement_pivots_ood_m31,
        late_switch_complement_pivots_relation_m31,
        late_switch_complement_pivots_final_m31,
        masked_switch_joint_probe: matches!(
            late_switch_support,
            LateSwitchSupport::MaskedSlotZeroSingleCodeword
                | LateSwitchSupport::MaskedHighCoefficientSingleCodeword
                | LateSwitchSupport::MaskedSemanticHighSingleCodeword
                | LateSwitchSupport::MaskedSemanticHighSharedC2SingleCodeword
                | LateSwitchSupport::MaskedSemanticNatural18SharedC2SingleCodeword
                | LateSwitchSupport::MaskedFullXGammaLane
                | LateSwitchSupport::MaskedFullXGammaKernelLane
                | LateSwitchSupport::MaskedFullXFirstLaterLane
                | LateSwitchSupport::LeanNativeFullRootX
                | LateSwitchSupport::LeanNativeFullRootXRawOnlyControl
        ),
        masked_switch_universal_mds_basis,
        masked_switch_code_basis_rank_m31,
        masked_switch_query_abscissae_distinct,
        masked_switch_rank_retry_required,
        masked_switch_code_basis_fingerprint,
        masked_switch_variables_qm31,
        masked_switch_observation_rank_qm31,
        masked_switch_without_u_observation_rank_qm31,
        masked_switch_without_u_kernel_qm31,
        masked_switch_u_observation_rank_redundant,
        masked_switch_kernel_qm31,
        masked_switch_q_randomness_rank_qm31,
        masked_switch_q_coopening_rank_qm31,
        masked_switch_otp_rank_qm31,
        masked_switch_u_rank_qm31,
        masked_switch_u_plus_legacy_ood_diagnostic_rank_qm31,
        masked_switch_shared_c2_observation_rank_qm31,
        masked_switch_shared_c2_kernel_qm31,
        masked_switch_shared_c2_randomness_rank_qm31,
        masked_switch_standalone_frontier_nodes,
        masked_switch_shared_root_increment_bytes,
        masked_switch_standalone_increment_bytes,
        coordinate_prefix_sumcheck_ranks,
        coordinate_prefix_pcs_ranks,
        raw_opening_minor,
        masked_sumcheck_minor,
        joint_raw_sumcheck_minor,
        post_sumcheck_pcs_minor,
        late_switch_complement_minor,
        late_switch_observation_minor,
        mask_basis_columns_examined: basis_columns,
        elapsed_millis: started.elapsed().as_millis(),
    })
}

/// Exact atomic profile-21 q16 scan for log-11 upper-half entropy in the
/// existing G and H oracle leaves. The literal profile-21 codeword domain stays
/// log 19, so doubling the message changes the diagnostic rate from 1/512 to
/// 1/256 and doubles the final coefficient vector from four to eight.
pub fn probe_atomic_state_only_profile21_upper_oracle_rank(
    schedule: &StateOnlyProfile21TranscriptScheduleResult,
) -> Result<AtomicProfile21UpperOracleRankReport, StateOnlyHidingRankGateError> {
    probe_atomic_state_only_profile21_upper_oracle_rank_at_insertion(schedule, 0, None)
}

/// One coordinate of the production-neutral zero-slice diagnostic. Exposed
/// separately so long scans can checkpoint completed coordinates.
pub fn probe_atomic_state_only_profile21_zero_slice_embedding_at(
    schedule: &StateOnlyProfile21TranscriptScheduleResult,
    insertion_coordinate: usize,
) -> Result<AtomicProfile21UpperOracleRankReport, StateOnlyHidingRankGateError> {
    probe_atomic_state_only_profile21_upper_oracle_rank_at_insertion(
        schedule,
        insertion_coordinate,
        None,
    )
}

fn probe_atomic_state_only_profile21_upper_oracle_rank_at_insertion(
    schedule: &StateOnlyProfile21TranscriptScheduleResult,
    insertion_coordinate: usize,
    affine_slice: Option<M31>,
) -> Result<AtomicProfile21UpperOracleRankReport, StateOnlyHidingRankGateError> {
    let started = Instant::now();
    let schedule = &schedule.base;
    if schedule.query_count != 16
        || schedule.prefix.z.len() != STATE_ONLY_HIDING_SUMCHECK_ROUNDS
        || insertion_coordinate > STATE_ONLY_HIDING_SUMCHECK_ROUNDS
    {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let domain_log = STATE_ONLY_LOG_ROWS + 9;
    let encoder = CircleEncoder::new_for_domain_log(domain_log);
    let inserted_value = affine_slice
        .map(|c| QM31::from_cm31(CM31::from_m31(c)))
        .unwrap_or(QM31::ZERO);
    let (physical_rows, later_indices) = extended_row_public_maps_sparse_atomic_profile21_at(
        &encoder,
        domain_log,
        schedule,
        insertion_coordinate,
        inserted_value,
    )?;
    let rows =
        canonicalize_extended_row_public_maps(&physical_rows, insertion_coordinate, affine_slice);
    let lower_row = |row| row;
    let upper_row = |row| TRACE_ROWS + row;
    let layer0_m31 = rows[0].layer0_m31.len();
    let c1_raw_m31 = layer0_m31 + 12;
    let g_raw_m31 = 4 * (layer0_m31 + 3);
    let pcs_tail_qm31 = rows[0].pcs_tail.len();
    if rows
        .iter()
        .any(|row| row.layer0_m31.len() != layer0_m31 || row.pcs_tail.len() != pcs_tail_qm31)
    {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let later_opened_symbols = later_indices
        .iter()
        .map(|indices| FIBER_SLOTS * indices.len())
        .sum::<usize>();
    let ood_values = CANDIDATE_ROUND_COUNT * CANDIDATE_OOD_SAMPLES;
    let relation_coefficients = CANDIDATE_ROUND_COUNT * 7;
    let final_coefficients = EXTENDED_TRACE_ROWS / FIBER_SLOTS.pow(CANDIDATE_ROUND_COUNT as u32);
    if final_coefficients != 8
        || pcs_tail_qm31
            != later_opened_symbols + ood_values + relation_coefficients + final_coefficients
    {
        return Err(StateOnlyHidingRankGateError::Shape);
    }

    let h_raw_qm31 = layer0_m31 + 3;
    let joint_pcs_m31 = 4 * (h_raw_qm31 + pcs_tail_qm31);
    let sc_m31 = 4 * STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS;
    let aux_m31 = sc_m31 + joint_pcs_m31;
    let lagrange = lagrange_basis();
    let active_rows = rank_active_rows(RankLayout::AtomicV3);
    let mut active = [false; TRACE_ROWS];
    for &row in active_rows {
        active[usize::from(row)] = true;
    }
    let inactive = (0..TRACE_ROWS)
        .filter(|row| !active[*row])
        .collect::<Vec<_>>();
    let global_dependent = inactive[0];
    let h_generator_index = STATE_ONLY_HIDING_C1_COLUMNS + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS;
    let g_generator_index = h_generator_index + 1;
    let powers = (0..=g_generator_index)
        .map(|column| gamma_power(schedule.prefix.gamma, column))
        .collect::<Vec<_>>();

    let mut base_sumcheck_kernel_images = Vec::new();
    let mut semantic_raw_echelons = Vec::with_capacity(STATE_ONLY_HIDING_C1_COLUMNS);
    let cells = atomic_state_only_relation_free_mask_cells_v3()
        .map_err(|_| StateOnlyHidingRankGateError::Layout)?;
    let mut cells_by_column = vec![Vec::new(); STATE_ONLY_HIDING_C1_COLUMNS];
    for cell in cells {
        cells_by_column[usize::from(cell.column)].push(usize::from(cell.row));
    }
    for (column, cells) in cells_by_column.iter().enumerate() {
        let dependent = cells
            .iter()
            .copied()
            .filter(|row| !active[*row])
            .last()
            .ok_or(StateOnlyHidingRankGateError::Layout)?;
        let observations = (0..TRACE_ROWS)
            .map(|row| {
                mask_sumcheck_observations(
                    row,
                    &schedule.prefix.z,
                    &lagrange,
                    MaskFactor::Semantic(column),
                    FactorSchedule::FullSharedLinear,
                    None,
                )
            })
            .collect::<Vec<_>>();
        let mut raw = CarryEchelon::new(c1_raw_m31);
        for &row in cells {
            if row == dependent {
                continue;
            }
            let subtract = (!active[row]).then_some(dependent);
            let embedded_row = lower_row(row);
            let embedded_subtract = subtract.map(lower_row);
            let aux = scaled_aux_difference(
                &rows,
                embedded_row,
                embedded_subtract,
                &observations,
                QM31::ONE,
                powers[column],
                4 * h_raw_qm31,
                joint_pcs_m31,
            );
            if let Some(kernel) = raw.reduce(
                c1_raw_difference(&rows, embedded_row, embedded_subtract),
                aux,
            ) {
                base_sumcheck_kernel_images.push(kernel);
            }
        }
        if raw.rank != c1_raw_m31 {
            return Err(StateOnlyHidingRankGateError::RawC1Rank {
                column,
                got: raw.rank,
                want: c1_raw_m31,
            });
        }
        semantic_raw_echelons.push(raw);
    }

    for mask_column in 0..STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS {
        let observations = (0..TRACE_ROWS)
            .map(|row| {
                mask_sumcheck_observations(
                    row,
                    &schedule.prefix.z,
                    &lagrange,
                    MaskFactor::MaskOnly(mask_column),
                    FactorSchedule::FullSharedLinear,
                    None,
                )
            })
            .collect::<Vec<_>>();
        let generator = STATE_ONLY_HIDING_C1_COLUMNS + mask_column;
        let mut raw = CarryEchelon::new(c1_raw_m31);
        for row in 0..TRACE_ROWS {
            if row == global_dependent {
                continue;
            }
            let subtract = (!active[row]).then_some(global_dependent);
            let embedded_row = lower_row(row);
            let embedded_subtract = subtract.map(lower_row);
            let aux = scaled_aux_difference(
                &rows,
                embedded_row,
                embedded_subtract,
                &observations,
                QM31::ONE,
                powers[generator],
                4 * h_raw_qm31,
                joint_pcs_m31,
            );
            if let Some(kernel) = raw.reduce(
                c1_raw_difference(&rows, embedded_row, embedded_subtract),
                aux,
            ) {
                base_sumcheck_kernel_images.push(kernel);
            }
        }
        if raw.rank != c1_raw_m31 {
            return Err(StateOnlyHidingRankGateError::RawC1Rank {
                column: generator,
                got: raw.rank,
                want: c1_raw_m31,
            });
        }
    }

    let lower_g_observations = (0..TRACE_ROWS)
        .map(|row| {
            mask_sumcheck_observations(
                row,
                &schedule.prefix.z,
                &lagrange,
                MaskFactor::ExplicitG,
                FactorSchedule::FullSharedLinear,
                None,
            )
        })
        .collect::<Vec<_>>();
    let mut g_raw = CarryEchelon::new(g_raw_m31);
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for row in 0..TRACE_ROWS {
            if row == global_dependent {
                continue;
            }
            let subtract = (!active[row]).then_some(global_dependent);
            let embedded_row = lower_row(row);
            let embedded_subtract = subtract.map(lower_row);
            let aux = scaled_aux_difference(
                &rows,
                embedded_row,
                embedded_subtract,
                &lower_g_observations,
                basis,
                basis.mul(powers[g_generator_index]),
                4 * h_raw_qm31,
                joint_pcs_m31,
            );
            if let Some(kernel) = g_raw.reduce(
                qm31_raw_difference(&rows, embedded_row, embedded_subtract, basis),
                aux,
            ) {
                base_sumcheck_kernel_images.push(kernel);
            }
        }
    }
    if g_raw.rank != g_raw_m31 {
        return Err(StateOnlyHidingRankGateError::RawGRank {
            got: g_raw.rank,
            want: g_raw_m31,
        });
    }

    let mut upper_g_raw_kernel_images = Vec::new();
    let mut upper_g_sources = Vec::new();
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for row in 0..TRACE_ROWS {
            let embedded_row = upper_row(row);
            let mut aux = vec![M31::ZERO; aux_m31];
            let pcs = scaled_qm31_difference(
                &rows[embedded_row].pcs_tail,
                None,
                basis.mul(powers[g_generator_index]),
            );
            let pcs_start = sc_m31 + 4 * h_raw_qm31;
            aux[pcs_start..pcs_start + pcs.len()].copy_from_slice(&pcs);
            if let Some(kernel) =
                g_raw.reduce(qm31_raw_difference(&rows, embedded_row, None, basis), aux)
            {
                upper_g_sources.push(4 * row + coordinate);
                upper_g_raw_kernel_images.push(kernel);
            }
        }
    }

    let mut sumcheck = CarryEchelon::new(sc_m31);
    let mut base_pcs_kernel_images = Vec::new();
    for image in &base_sumcheck_kernel_images {
        let (sc, pcs) = image.split_at(sc_m31);
        if let Some(kernel) = sumcheck.reduce(sc.to_vec(), pcs.to_vec()) {
            base_pcs_kernel_images.push(kernel);
        }
    }
    if sumcheck.rank != MASK_SUMCHECK_QUOTIENT_M31 {
        return Err(StateOnlyHidingRankGateError::MaskedSumcheckRank {
            got: sumcheck.rank,
            want: MASK_SUMCHECK_QUOTIENT_M31,
        });
    }
    let mut upper_g_pcs_images = Vec::with_capacity(upper_g_raw_kernel_images.len());
    let mut upper_g_pcs_sources = Vec::with_capacity(upper_g_raw_kernel_images.len());
    for (&source, image) in upper_g_sources.iter().zip(&upper_g_raw_kernel_images) {
        let (sc, pcs) = image.split_at(sc_m31);
        let kernel = sumcheck
            .quotient_existing(sc.to_vec(), pcs.to_vec())
            .ok_or(StateOnlyHidingRankGateError::Layout)?;
        upper_g_pcs_sources.push(source);
        upper_g_pcs_images.push(kernel);
    }

    let mut baseline_pcs = ColumnEchelon::new(joint_pcs_m31);
    for image in base_pcs_kernel_images {
        baseline_pcs.insert(image);
    }
    let h_scale = powers[h_generator_index];
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for &row in &inactive {
            if row != global_dependent {
                baseline_pcs.insert(h_pcs_image(
                    &rows,
                    lower_row(row),
                    lower_row(global_dependent),
                    basis,
                    h_scale,
                    h_raw_qm31,
                    pcs_tail_qm31,
                ));
            }
        }
    }
    let baseline_pcs_rank_m31 = baseline_pcs.rank;

    let mut upper_h_images = Vec::with_capacity(4 * TRACE_ROWS);
    let mut upper_h_sources = Vec::with_capacity(4 * TRACE_ROWS);
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for row in 0..TRACE_ROWS {
            let embedded_row = upper_row(row);
            upper_h_sources.push(4 * row + coordinate);
            upper_h_images.push(h_pcs_single_image(
                &rows,
                embedded_row,
                basis,
                h_scale,
                h_raw_qm31,
                pcs_tail_qm31,
            ));
        }
    }

    // Conservative same-statement semantic audit, identical in source scope
    // to the atomic profile-21 712 -> 716 tooth: all lower semantic cells
    // except the fixed owner-key row, plus every legal zero-initial-claim
    // sumcheck direction.
    let mut baseline_semantic = baseline_pcs.clone();
    let mut compatibility = CarryEchelon::new(sc_m31);
    let mut semantic_images = Vec::new();
    let mut semantic_sources = Vec::new();
    let mut semantic_rows = Vec::new();
    let mut semantic_values = Vec::new();
    let pcs_start = sc_m31 + 4 * h_raw_qm31;
    for column in 0..STATE_ONLY_HIDING_C1_COLUMNS {
        for row in 1..TRACE_ROWS {
            let source_id = column * TRACE_ROWS + row;
            let embedded_row = lower_row(row);
            let raw = c1_raw_difference(&rows, embedded_row, None);
            let mut carry = vec![M31::ZERO; aux_m31];
            let pcs = scaled_qm31_difference(&rows[embedded_row].pcs_tail, None, powers[column]);
            carry[pcs_start..pcs_start + pcs.len()].copy_from_slice(&pcs);
            let post_raw = semantic_raw_echelons[column]
                .quotient_existing(raw, carry)
                .ok_or(StateOnlyHidingRankGateError::WitnessRawQuotient { source: source_id })?;
            let (sc, pcs) = post_raw.split_at(sc_m31);
            let (sc_remainder, mut pcs_remainder) =
                sumcheck.remainder_existing(sc.to_vec(), pcs.to_vec());
            let next_pivot = compatibility.rank;
            pcs_remainder.extend((0..4).map(|index| {
                if next_pivot < 4 && index == next_pivot {
                    M31::ONE
                } else {
                    M31::ZERO
                }
            }));
            if let CarryReduction::Kernel(mut post_sumcheck) =
                compatibility.reduce_with_pivot(sc_remainder, pcs_remainder)
            {
                post_sumcheck.truncate(joint_pcs_m31);
                if let Some((pivot, value)) =
                    baseline_semantic.insert_with_pivot_value(post_sumcheck.clone())
                {
                    semantic_images.push(post_sumcheck);
                    semantic_sources.push(source_id);
                    semantic_rows.push(pivot);
                    semantic_values.push(value);
                }
            }
        }
    }
    if compatibility.rank != 4 {
        return Err(StateOnlyHidingRankGateError::Layout);
    }
    let baseline_semantic_augmented_rank_m31 = baseline_semantic.rank;
    let semantic_minor = RankMinorProvenance::from_parts(
        "atomic_profile21_log11_semantic",
        semantic_sources,
        semantic_rows,
        semantic_values,
    );

    let mut baseline_legal = baseline_semantic.clone();
    let mut legal_images = Vec::new();
    let mut legal_sources = Vec::new();
    let mut legal_rows = Vec::new();
    let mut legal_values = Vec::new();
    for sc_row in 4..sc_m31 {
        let mut sc = vec![M31::ZERO; sc_m31];
        sc[sc_row] = M31::ONE;
        let pcs = vec![M31::ZERO; joint_pcs_m31];
        let (sc_remainder, mut pcs_remainder) = sumcheck.remainder_existing(sc, pcs);
        pcs_remainder.extend([M31::ZERO; 4]);
        if let CarryReduction::Kernel(mut post_sumcheck) =
            compatibility.reduce_with_pivot(sc_remainder, pcs_remainder)
        {
            post_sumcheck.truncate(joint_pcs_m31);
            if let Some((pivot, value)) =
                baseline_legal.insert_with_pivot_value(post_sumcheck.clone())
            {
                legal_images.push(post_sumcheck);
                legal_sources.push(sc_row - 4);
                legal_rows.push(pivot);
                legal_values.push(value);
            }
        }
    }
    let baseline_legal_sumcheck_augmented_rank_m31 = baseline_legal.rank;
    let legal_sumcheck_minor = RankMinorProvenance::from_parts(
        "atomic_profile21_log11_legal_sumcheck",
        legal_sources,
        legal_rows,
        legal_values,
    );

    let mut variants = Vec::with_capacity(3);
    for (support, include_upper_g, include_upper_h, block) in [
        ("upper_g_only", true, false, "atomic_profile21_upper_g"),
        ("upper_h_only", false, true, "atomic_profile21_upper_h"),
        ("upper_g_and_h", true, true, "atomic_profile21_upper_g_h"),
    ] {
        let mut selected = baseline_pcs.clone();
        let mut upper_sources = Vec::new();
        let mut upper_rows = Vec::new();
        let mut upper_values = Vec::new();
        if include_upper_g {
            for (&source, image) in upper_g_pcs_sources.iter().zip(&upper_g_pcs_images) {
                if let Some((pivot, value)) = selected.insert_with_pivot_value(image.clone()) {
                    upper_sources.push(source);
                    upper_rows.push(pivot);
                    upper_values.push(value);
                }
            }
        }
        if include_upper_h {
            let offset = 4 * TRACE_ROWS;
            for (&source, image) in upper_h_sources.iter().zip(&upper_h_images) {
                if let Some((pivot, value)) = selected.insert_with_pivot_value(image.clone()) {
                    upper_sources.push(offset + source);
                    upper_rows.push(pivot);
                    upper_values.push(value);
                }
            }
        }
        let pcs_rank = selected.rank;
        let upper_new_pivots_m31 = upper_rows.clone();
        let upper_minor =
            RankMinorProvenance::from_parts(block, upper_sources, upper_rows, upper_values);

        let mut semantic_selected = selected;
        let mut semantic_new_pivots_m31 = Vec::new();
        for image in &semantic_images {
            if let Some(pivot) = semantic_selected.insert_with_pivot(image.clone()) {
                semantic_new_pivots_m31.push(pivot);
            }
        }
        let semantic_augmented_rank = semantic_selected.rank;
        let mut legal_new_pivots_m31 = Vec::new();
        for image in &legal_images {
            if let Some(pivot) = semantic_selected.insert_with_pivot(image.clone()) {
                legal_new_pivots_m31.push(pivot);
            }
        }
        let legal_sumcheck_augmented_rank = semantic_selected.rank;
        variants.push(AtomicProfile21UpperOracleVariantReport {
            support,
            pcs_rank,
            upper_new_pivots_m31,
            upper_minor,
            semantic_augmented_rank,
            semantic_new_pivots_m31,
            legal_sumcheck_augmented_rank,
            legal_sumcheck_new_pivots_m31: legal_new_pivots_m31,
            contains_conservative_semantic_and_legal_sumcheck: pcs_rank
                == legal_sumcheck_augmented_rank,
        });
    }

    let codeword_len = encoder.codeword_len();
    Ok(AtomicProfile21UpperOracleRankReport {
        query_count: schedule.query_count,
        message_log: EXTENDED_LOG_ROWS,
        codeword_domain_log: domain_log,
        codeword_len,
        rate_denominator: codeword_len / EXTENDED_TRACE_ROWS,
        codeword_len_at_rate_1_512: EXTENDED_TRACE_ROWS * 512,
        final_coefficients_qm31: final_coefficients,
        layer0_opened_symbols_per_oracle: layer0_m31,
        later_opened_symbols_per_oracle: later_opened_symbols,
        ood_values_per_oracle: ood_values,
        relation_coefficients_per_oracle: relation_coefficients,
        pcs_tail_qm31,
        joint_pcs_m31,
        masked_sumcheck_rank_m31: sumcheck.rank,
        baseline_pcs_rank_m31,
        baseline_semantic_augmented_rank_m31,
        baseline_legal_sumcheck_augmented_rank_m31,
        semantic_minor,
        legal_sumcheck_minor,
        variants,
        elapsed_millis: started.elapsed().as_millis(),
    })
}

/// Scans all eleven natural-coordinate placements of a new zero tensor
/// coordinate. This is deliberately host-only and does not alter the
/// production transcript or wire format.
pub fn probe_atomic_state_only_profile21_zero_slice_embedding_scan(
    schedule: &StateOnlyProfile21TranscriptScheduleResult,
) -> Result<AtomicProfile21ZeroSliceEmbeddingScanReport, StateOnlyHidingRankGateError> {
    let started = Instant::now();
    let mut variants = Vec::with_capacity(STATE_ONLY_HIDING_SUMCHECK_ROUNDS + 1);
    let mut codeword_domain_log = 0;
    let mut rate_denominator = 0;
    let coordinates = (0..=STATE_ONLY_HIDING_SUMCHECK_ROUNDS).collect::<Vec<_>>();
    let mut coordinate_reports = Vec::with_capacity(coordinates.len());
    for batch in coordinates.chunks(4) {
        let mut batch_reports = std::thread::scope(|scope| {
            let handles = batch
                .iter()
                .copied()
                .map(|insertion_coordinate| {
                    scope.spawn(move || {
                        let coordinate_started = Instant::now();
                        let report =
                            probe_atomic_state_only_profile21_upper_oracle_rank_at_insertion(
                                schedule,
                                insertion_coordinate,
                                None,
                            )?;
                        Ok::<_, StateOnlyHidingRankGateError>((
                            insertion_coordinate,
                            coordinate_started.elapsed().as_millis(),
                            report,
                        ))
                    })
                })
                .collect::<Vec<_>>();
            handles
                .into_iter()
                .map(|handle| {
                    handle
                        .join()
                        .map_err(|_| StateOnlyHidingRankGateError::Layout)?
                })
                .collect::<Result<Vec<_>, _>>()
        })?;
        coordinate_reports.append(&mut batch_reports);
    }
    for (insertion_coordinate, elapsed_millis, report) in coordinate_reports {
        codeword_domain_log = report.codeword_domain_log;
        rate_denominator = report.rate_denominator;
        let mask = report
            .variants
            .iter()
            .find(|variant| variant.support == "upper_g_only")
            .ok_or(StateOnlyHidingRankGateError::Shape)?;
        variants.push(AtomicProfile21ZeroSliceEmbeddingVariantReport {
            insertion_coordinate,
            baseline_pcs_rank_m31: report.baseline_pcs_rank_m31,
            mask_augmented_pcs_rank_m31: mask.pcs_rank,
            mask_new_pivots_m31: mask.upper_new_pivots_m31.clone(),
            semantic_augmented_rank_m31: mask.semantic_augmented_rank,
            semantic_new_pivots_m31: mask.semantic_new_pivots_m31.clone(),
            legal_sumcheck_augmented_rank_m31: mask.legal_sumcheck_augmented_rank,
            legal_sumcheck_new_pivots_m31: mask.legal_sumcheck_new_pivots_m31.clone(),
            contains_conservative_semantic_and_legal_sumcheck: mask
                .contains_conservative_semantic_and_legal_sumcheck,
            elapsed_millis,
        });
    }
    Ok(AtomicProfile21ZeroSliceEmbeddingScanReport {
        query_count: schedule.base.query_count,
        codeword_domain_log,
        rate_denominator,
        variants,
        failures: Vec::new(),
        elapsed_millis: started.elapsed().as_millis(),
    })
}

/// Tests the physically claim-preserving affine lift
/// `F(x,s)=F(x)+(s-c)R(x)`. The original message is duplicated across the two
/// inserted-bit slices, all public claims are evaluated at `s=c`, and the
/// existing full-QM31 G helper lane carries `(-c R, (1-c) R)`. Coordinates
/// consumed by the earliest radix-4 folds are tested first; the scan stops
/// after the first four-value coordinate batch containing the conservative
/// semantic and legal-sumcheck image.
pub fn probe_atomic_state_only_profile21_affine_slice_embedding_scan(
    schedule: &StateOnlyProfile21TranscriptScheduleResult,
) -> Result<AtomicProfile21AffineSliceEmbeddingScanReport, StateOnlyHidingRankGateError> {
    const SLICE_VALUES: [u32; 4] = [2, 3, 5, 7];
    const INSERTION_ORDER: [usize; STATE_ONLY_HIDING_SUMCHECK_ROUNDS + 1] =
        [10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0];
    let started = Instant::now();
    let mut variants = Vec::new();
    let mut codeword_domain_log = 0;
    let mut rate_denominator = 0;
    let mut stopped_on_first_containment = false;
    for insertion_coordinate in INSERTION_ORDER {
        let coordinate_reports = std::thread::scope(|scope| {
            let handles = SLICE_VALUES
                .into_iter()
                .map(|slice_value| {
                    scope.spawn(move || {
                        let coordinate_started = Instant::now();
                        let report =
                            probe_atomic_state_only_profile21_upper_oracle_rank_at_insertion(
                                schedule,
                                insertion_coordinate,
                                Some(M31(slice_value)),
                            )?;
                        Ok::<_, StateOnlyHidingRankGateError>((
                            slice_value,
                            coordinate_started.elapsed().as_millis(),
                            report,
                        ))
                    })
                })
                .collect::<Vec<_>>();
            handles
                .into_iter()
                .map(|handle| {
                    handle
                        .join()
                        .map_err(|_| StateOnlyHidingRankGateError::Layout)?
                })
                .collect::<Result<Vec<_>, _>>()
        })?;
        let mut coordinate_contains = false;
        for (slice_value, elapsed_millis, report) in coordinate_reports {
            codeword_domain_log = report.codeword_domain_log;
            rate_denominator = report.rate_denominator;
            let mask = report
                .variants
                .iter()
                .find(|variant| variant.support == "upper_g_only")
                .ok_or(StateOnlyHidingRankGateError::Shape)?;
            coordinate_contains |= mask.contains_conservative_semantic_and_legal_sumcheck;
            variants.push(AtomicProfile21AffineSliceEmbeddingVariantReport {
                insertion_coordinate,
                slice_value_m31: slice_value,
                baseline_pcs_rank_m31: report.baseline_pcs_rank_m31,
                mask_augmented_pcs_rank_m31: mask.pcs_rank,
                mask_new_pivots_m31: mask.upper_new_pivots_m31.clone(),
                semantic_augmented_rank_m31: mask.semantic_augmented_rank,
                semantic_new_pivots_m31: mask.semantic_new_pivots_m31.clone(),
                legal_sumcheck_augmented_rank_m31: mask.legal_sumcheck_augmented_rank,
                legal_sumcheck_new_pivots_m31: mask.legal_sumcheck_new_pivots_m31.clone(),
                contains_conservative_semantic_and_legal_sumcheck: mask
                    .contains_conservative_semantic_and_legal_sumcheck,
                elapsed_millis,
            });
        }
        if coordinate_contains {
            stopped_on_first_containment = true;
            break;
        }
    }
    Ok(AtomicProfile21AffineSliceEmbeddingScanReport {
        query_count: schedule.base.query_count,
        codeword_domain_log,
        rate_denominator,
        stopped_on_first_containment,
        variants,
        elapsed_millis: started.elapsed().as_millis(),
    })
}

/// Exact host-only rate-1/32 probe for a log-11 message embedded in a log-16
/// circle word. Semantic data and every statement point live in the lower
/// half; the existing committed G lane receives fresh upper-half entropy.
/// Deterministic folds are unchanged and no post-challenge word is chosen.
pub fn probe_state_only_log11_upper_g_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<StateOnlyHidingRankGateReport, StateOnlyHidingRankGateError> {
    let started = Instant::now();
    if schedule.query_count != 29 {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let domain_log = EXTENDED_LOG_ROWS + 5;
    let encoder = CircleEncoder::new_for_domain_log(domain_log);
    let rows = extended_row_public_maps(&encoder, domain_log, schedule)?;
    let layer0_m31 = rows[0].layer0_m31.len();
    let c1_raw_m31 = layer0_m31 + 12;
    let g_raw_m31 = 4 * (layer0_m31 + 3);
    let pcs_tail_qm31 = rows[0].pcs_tail.len();
    let h_raw_qm31 = layer0_m31 + 3;
    let joint_pcs_m31 = 4 * (h_raw_qm31 + pcs_tail_qm31);
    let sc_m31 = 4 * STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS;
    let aux_m31 = sc_m31 + joint_pcs_m31;
    let lagrange = lagrange_basis();

    let mut active = [false; TRACE_ROWS];
    for &row in state_only_copy_active_rows_v4() {
        active[usize::from(row)] = true;
    }
    let inactive = (0..TRACE_ROWS)
        .filter(|row| !active[*row])
        .collect::<Vec<_>>();
    let global_dependent = inactive[0];
    let h_generator_index = STATE_ONLY_HIDING_C1_COLUMNS + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS;
    let g_generator_index = h_generator_index + 1;
    let powers = (0..=g_generator_index)
        .map(|column| gamma_power(schedule.prefix.gamma, column))
        .collect::<Vec<_>>();

    let mut sumcheck_kernel_images = Vec::new();
    let mut basis_columns = 0usize;
    let mut semantic_mask_basis_m31 = 0usize;
    let mut semantic_raw_kernel_m31 = 0usize;
    let cells = state_only_relation_free_mask_cells_v4()
        .map_err(|_| StateOnlyHidingRankGateError::Layout)?;
    let mut cells_by_column = vec![Vec::new(); STATE_ONLY_HIDING_C1_COLUMNS];
    for cell in cells {
        cells_by_column[usize::from(cell.column)].push(usize::from(cell.row));
    }
    for (column, cells) in cells_by_column.iter().enumerate() {
        let dependent = cells
            .iter()
            .copied()
            .filter(|row| !active[*row])
            .last()
            .ok_or(StateOnlyHidingRankGateError::Layout)?;
        let observations = (0..TRACE_ROWS)
            .map(|row| {
                mask_sumcheck_observations(
                    row,
                    &schedule.prefix.z,
                    &lagrange,
                    MaskFactor::Semantic(column),
                    FactorSchedule::Production,
                    None,
                )
            })
            .collect::<Vec<_>>();
        let mut raw = CarryEchelon::new(c1_raw_m31);
        let mut column_basis = 0usize;
        for &row in cells {
            if row == dependent {
                continue;
            }
            let subtract = (!active[row]).then_some(dependent);
            let aux = scaled_aux_difference(
                &rows,
                row,
                subtract,
                &observations,
                QM31::ONE,
                powers[column],
                4 * h_raw_qm31,
                joint_pcs_m31,
            );
            basis_columns += 1;
            column_basis += 1;
            if let Some(kernel) = raw.reduce(c1_raw_difference(&rows, row, subtract), aux) {
                sumcheck_kernel_images.push(kernel);
            }
        }
        semantic_mask_basis_m31 += column_basis;
        semantic_raw_kernel_m31 += column_basis - raw.rank;
        if raw.rank != c1_raw_m31 {
            return Err(StateOnlyHidingRankGateError::RawC1Rank {
                column,
                got: raw.rank,
                want: c1_raw_m31,
            });
        }
    }

    let mut mask_only_basis_m31 = 0usize;
    let mut mask_only_raw_kernel_m31 = 0usize;
    for mask_column in 0..STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS {
        let observations = (0..TRACE_ROWS)
            .map(|row| {
                mask_sumcheck_observations(
                    row,
                    &schedule.prefix.z,
                    &lagrange,
                    MaskFactor::MaskOnly(mask_column),
                    FactorSchedule::Production,
                    None,
                )
            })
            .collect::<Vec<_>>();
        let generator = STATE_ONLY_HIDING_C1_COLUMNS + mask_column;
        let mut raw = CarryEchelon::new(c1_raw_m31);
        let mut column_basis = 0usize;
        for row in 0..TRACE_ROWS {
            if row == global_dependent {
                continue;
            }
            let subtract = (!active[row]).then_some(global_dependent);
            let aux = scaled_aux_difference(
                &rows,
                row,
                subtract,
                &observations,
                QM31::ONE,
                powers[generator],
                4 * h_raw_qm31,
                joint_pcs_m31,
            );
            basis_columns += 1;
            column_basis += 1;
            if let Some(kernel) = raw.reduce(c1_raw_difference(&rows, row, subtract), aux) {
                sumcheck_kernel_images.push(kernel);
            }
        }
        mask_only_basis_m31 += column_basis;
        mask_only_raw_kernel_m31 += column_basis - raw.rank;
        if raw.rank != c1_raw_m31 {
            return Err(StateOnlyHidingRankGateError::RawC1Rank {
                column: generator,
                got: raw.rank,
                want: c1_raw_m31,
            });
        }
    }

    let lower_g_observations = (0..TRACE_ROWS)
        .map(|row| {
            mask_sumcheck_observations(
                row,
                &schedule.prefix.z,
                &lagrange,
                MaskFactor::ExplicitG,
                FactorSchedule::Production,
                None,
            )
        })
        .collect::<Vec<_>>();
    let zero_observations = vec![QM31::ZERO; STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS];
    let mut g_raw = CarryEchelon::new(g_raw_m31);
    let mut g_mask_basis_m31 = 0usize;
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for row in 0..EXTENDED_TRACE_ROWS {
            if row == global_dependent {
                continue;
            }
            let subtract = (row < TRACE_ROWS && !active[row]).then_some(global_dependent);
            let observations = if row < TRACE_ROWS {
                &lower_g_observations
            } else {
                // Upper-half G coefficients vanish at every [0,z] terminal
                // and contribute no external masked-sumcheck observation.
                // Use one shared all-zero table for their auxiliary map.
                // `scaled_aux_difference` indexes by row, so construct the
                // zero carry directly below.
                &lower_g_observations
            };
            let raw_image = qm31_raw_difference(&rows, row, subtract, basis);
            let aux = if row < TRACE_ROWS {
                scaled_aux_difference(
                    &rows,
                    row,
                    subtract,
                    observations,
                    basis,
                    basis.mul(powers[g_generator_index]),
                    4 * h_raw_qm31,
                    joint_pcs_m31,
                )
            } else {
                let mut aux = vec![M31::ZERO; aux_m31];
                let pcs = scaled_qm31_difference(
                    &rows[row].pcs_tail,
                    None,
                    basis.mul(powers[g_generator_index]),
                );
                let pcs_start = sc_m31 + 4 * h_raw_qm31;
                aux[pcs_start..pcs_start + pcs.len()].copy_from_slice(&pcs);
                debug_assert_eq!(
                    zero_observations.len(),
                    STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS
                );
                aux
            };
            basis_columns += 1;
            g_mask_basis_m31 += 1;
            if let Some(kernel) = g_raw.reduce(raw_image, aux) {
                sumcheck_kernel_images.push(kernel);
            }
        }
    }
    if g_raw.rank != g_raw_m31 {
        return Err(StateOnlyHidingRankGateError::RawGRank {
            got: g_raw.rank,
            want: g_raw_m31,
        });
    }
    let g_raw_kernel_m31 = g_mask_basis_m31 - g_raw.rank;

    let mut sumcheck = CarryEchelon::new(sc_m31);
    let mut pcs_kernel_images = Vec::new();
    for image in &sumcheck_kernel_images {
        let (sc, pcs) = image.split_at(sc_m31);
        if let Some(kernel) = sumcheck.reduce(sc.to_vec(), pcs.to_vec()) {
            pcs_kernel_images.push(kernel);
        }
    }
    let post_sumcheck_kernel_m31 = pcs_kernel_images.len();
    let mut pcs_rank = ColumnEchelon::new(joint_pcs_m31);
    for image in pcs_kernel_images {
        pcs_rank.insert(image);
    }
    let pre_helper_pcs_rank = pcs_rank.rank;
    let h_scale = powers[h_generator_index];
    let mut h_inactive_mask_basis_m31 = 0usize;
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for &row in &inactive {
            if row != global_dependent {
                pcs_rank.insert(h_pcs_image(
                    &rows,
                    row,
                    global_dependent,
                    basis,
                    h_scale,
                    h_raw_qm31,
                    pcs_tail_qm31,
                ));
                h_inactive_mask_basis_m31 += 1;
                basis_columns += 1;
            }
        }
    }
    // A/B: the existing h lane also receives pre-commit upper-half entropy.
    // It is invisible at [0,z] and changes no leaf width.
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for row in TRACE_ROWS..EXTENDED_TRACE_ROWS {
            pcs_rank.insert(h_pcs_single_image(
                &rows,
                row,
                basis,
                h_scale,
                h_raw_qm31,
                pcs_tail_qm31,
            ));
            h_inactive_mask_basis_m31 += 1;
            basis_columns += 1;
        }
    }
    let before = pcs_rank.rank;

    let mut declared = ColumnEchelon::new(joint_pcs_m31);
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for row in 0..TRACE_ROWS {
            if row != global_dependent {
                declared.insert(combined_pcs_image(
                    &rows,
                    row,
                    basis,
                    h_raw_qm31,
                    pcs_tail_qm31,
                ));
            }
        }
    }
    let declared_combined_rank = declared.rank;
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for &row in &inactive {
            if row != global_dependent {
                declared.insert(h_pcs_image(
                    &rows,
                    row,
                    global_dependent,
                    basis,
                    h_scale,
                    h_raw_qm31,
                    pcs_tail_qm31,
                ));
            }
        }
    }
    let declared_inactive_helper_rank = declared.rank;
    let active_rows = (0..TRACE_ROWS)
        .filter(|row| active[*row])
        .collect::<Vec<_>>();
    let active_dependent = *active_rows
        .last()
        .ok_or(StateOnlyHidingRankGateError::Layout)?;
    let mut augmented = pcs_rank.clone();
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for &row in &active_rows[..active_rows.len() - 1] {
            let image = h_pcs_image(
                &rows,
                row,
                active_dependent,
                basis,
                h_scale,
                h_raw_qm31,
                pcs_tail_qm31,
            );
            declared.insert(image.clone());
            augmented.insert(image);
        }
    }
    let mut complete_augmented = pcs_rank.clone();
    for basis in declared.pivots.iter().flatten() {
        complete_augmented.insert(basis.clone());
    }
    let complete = sumcheck.rank == MASK_SUMCHECK_QUOTIENT_M31
        && augmented.rank == before
        && complete_augmented.rank == before;

    Ok(StateOnlyHidingRankGateReport {
        pcs_schedule: "log11-domain16-four-arity4-upper-g-h",
        tail_qm31_probe: false,
        tail_qm31_mask_factor: "none",
        first_later_x_multiplier: "none",
        first_later_x_multiplier_degree: 0,
        shared_linear_factor_probe: false,
        coordinate_factored_mask_columns: 0,
        late_switch_probe: false,
        complete_ambient_rank: complete,
        query_count: schedule.query_count,
        c1_raw_m31,
        g_raw_m31,
        masked_sumcheck_m31: sc_m31,
        masked_sumcheck_rank: sumcheck.rank,
        joint_pcs_m31,
        joint_pcs_declared_rank: declared.rank,
        joint_pcs_rank: before,
        helper_augmented_rank: complete_augmented.rank,
        pre_helper_pcs_rank,
        declared_combined_rank,
        declared_inactive_helper_rank,
        semantic_mask_basis_m31,
        semantic_raw_kernel_m31,
        mask_only_basis_m31,
        mask_only_raw_kernel_m31,
        g_mask_basis_m31,
        g_raw_kernel_m31,
        tail_qm31_basis_m31: 0,
        tail_qm31_raw_kernel_m31: 0,
        post_sumcheck_kernel_m31,
        h_inactive_mask_basis_m31,
        ambient_combined_domain_qm31: TRACE_ROWS - 1,
        ambient_inactive_helper_domain_qm31: inactive.len() - 1,
        ambient_active_helper_domain_qm31: active_rows.len() - 1,
        baseline_valid_witness_containment: augmented.rank == before,
        baseline_ambient_deficit_m31: declared.rank.saturating_sub(before),
        witness_difference_probe: false,
        witness_semantic_superset_generators_m31: 0,
        witness_semantic_superset_rank: before,
        witness_legal_sumcheck_generators_m31: 0,
        witness_legal_sumcheck_rank: before,
        witness_compatibility_rank_m31: 0,
        witness_direct_sum_mask_view_rank_m31: None,
        witness_direct_sum_physical_augmented_view_rank_m31: None,
        witness_direct_sum_legal_augmented_view_rank_m31: None,
        witness_direct_sum_helper_augmented_view_rank_m31: None,
        witness_direct_sum_physical_contained: None,
        witness_direct_sum_legal_contained: None,
        witness_direct_sum_helper_contained: None,
        witness_direct_sum_unbalanced_physical_augmented_view_rank_m31: None,
        witness_direct_sum_unbalanced_physical_contained: None,
        witness_coupled_physical_augmented_view_rank_m31: None,
        witness_coupled_legal_augmented_view_rank_m31: None,
        witness_coupled_helper_augmented_view_rank_m31: None,
        witness_coupled_physical_contained: None,
        witness_coupled_legal_contained: None,
        witness_coupled_helper_contained: None,
        witness_coupled_legal_sumcheck_generators_m31: 0,
        witness_coupled_terminal_dependent_observation: None,
        witness_coupled_terminal_functional_fingerprint: 0,
        witness_coupled_terminal_identity_guard: false,
        witness_mask_raw_kernel_terminal_zero_sources_m31: 0,
        witness_mask_raw_kernel_terminal_zero_guard: false,
        witness_h_zero_sumcheck_terminal_guard: false,
        witness_mask_sumcheck_equals_terminal_kernel: false,
        witness_compatibility_terminal_map_rank_m31: 0,
        witness_compatibility_terminal_map_fingerprint: 0,
        witness_compatibility_pivot_sources: Vec::new(),
        witness_compatibility_pivot_rows_m31: Vec::new(),
        witness_semantic_kernel_coefficients_m31: Vec::new(),
        witness_semantic_sparse_dense_guard: false,
        witness_semantic_sparse_dense_fingerprint: 0,
        witness_unbalanced_semantic_superset_generators_m31: 0,
        witness_unbalanced_semantic_superset_rank: before,
        witness_unbalanced_compatibility_rank_m31: 0,
        witness_unbalanced_compatibility_pivot_sources: Vec::new(),
        witness_unbalanced_sparse_dense_guard: false,
        witness_unbalanced_sparse_dense_fingerprint: 0,
        witness_unbalanced_semantic_superset_minor: RankMinorProvenance::empty(
            "witness_unbalanced_upper_oracle_superset",
        ),
        witness_difference_projection: None,
        witness_semantic_superset_minor: RankMinorProvenance::empty("witness_semantic_superset"),
        witness_legal_sumcheck_minor: RankMinorProvenance::empty("witness_legal_sumcheck_superset"),
        late_switch_source_rows: Vec::new(),
        late_switch_variables_qm31: 0,
        late_switch_conditioned_kernel_qm31: 0,
        late_switch_conditioned_rank: before,
        late_switch_semantic_augmented_rank: before,
        late_switch_semantic_new_pivots_m31: Vec::new(),
        late_switch_contains_conservative_semantic_superset: false,
        late_switch_ambient_deficit_m31: declared.rank.saturating_sub(before),
        late_switch_complement_pivots_later_m31: 0,
        late_switch_complement_pivots_ood_m31: 0,
        late_switch_complement_pivots_relation_m31: 0,
        late_switch_complement_pivots_final_m31: 0,
        masked_switch_joint_probe: false,
        masked_switch_universal_mds_basis: false,
        masked_switch_code_basis_rank_m31: 0,
        masked_switch_query_abscissae_distinct: false,
        masked_switch_rank_retry_required: true,
        masked_switch_code_basis_fingerprint: 0,
        masked_switch_variables_qm31: 0,
        masked_switch_observation_rank_qm31: 0,
        masked_switch_without_u_observation_rank_qm31: 0,
        masked_switch_without_u_kernel_qm31: 0,
        masked_switch_u_observation_rank_redundant: false,
        masked_switch_kernel_qm31: 0,
        masked_switch_q_randomness_rank_qm31: 0,
        masked_switch_q_coopening_rank_qm31: 0,
        masked_switch_otp_rank_qm31: 0,
        masked_switch_u_rank_qm31: 0,
        masked_switch_u_plus_legacy_ood_diagnostic_rank_qm31: 0,
        masked_switch_shared_c2_observation_rank_qm31: 0,
        masked_switch_shared_c2_kernel_qm31: 0,
        masked_switch_shared_c2_randomness_rank_qm31: 0,
        masked_switch_standalone_frontier_nodes: 0,
        masked_switch_shared_root_increment_bytes: 0,
        masked_switch_standalone_increment_bytes: 0,
        coordinate_prefix_sumcheck_ranks: Vec::new(),
        coordinate_prefix_pcs_ranks: Vec::new(),
        raw_opening_minor: RankMinorProvenance::empty("raw_openings_2244"),
        masked_sumcheck_minor: RankMinorProvenance::empty("masked_sumcheck_1080"),
        joint_raw_sumcheck_minor: RankMinorProvenance::empty("joint_raw_sumcheck_3324"),
        post_sumcheck_pcs_minor: RankMinorProvenance::empty("post_sumcheck_pcs_712"),
        late_switch_complement_minor: RankMinorProvenance::empty("late_switch_complement_68"),
        late_switch_observation_minor: RankMinorProvenance::empty("late_switch_observation_208"),
        mask_basis_columns_examined: basis_columns,
        elapsed_millis: started.elapsed().as_millis(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compressed_sumcheck_terminal_and_conditional_kernel_match_the_wire() {
        let challenges: [QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS] = core::array::from_fn(|round| {
            QM31::from_cm31(CM31::new(
                M31((17 + 29 * round) as u32),
                M31((23 + 31 * round) as u32),
            ))
            .add(state_only_mask_tower_basis(2).mul_m31(M31((round + 3) as u32)))
        });
        let mut running = QM31::from_cm31(CM31::new(M31(101), M31(103)))
            .add(state_only_mask_tower_basis(3).mul_m31(M31(107)));
        let mut compressed = Vec::with_capacity(STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS);
        compressed.push(running);
        for round in 0..STATE_ONLY_HIDING_SUMCHECK_ROUNDS {
            let mut polynomial = [QM31::ZERO; MASK_SUMCHECK_COEFFICIENTS];
            polynomial[0] =
                state_only_mask_tower_basis(round & 3).mul_m31(M31((113 + 37 * round) as u32));
            let mut high_sum = QM31::ZERO;
            for coefficient in 2..MASK_SUMCHECK_COEFFICIENTS {
                polynomial[coefficient] = state_only_mask_tower_basis(coefficient & 3)
                    .mul_m31(M31((127 + 41 * round + coefficient) as u32));
                high_sum = high_sum.add(polynomial[coefficient]);
            }
            polynomial[1] = running.sub(polynomial[0].add(polynomial[0])).sub(high_sum);
            compressed.push(polynomial[0]);
            compressed.extend_from_slice(&polynomial[2..]);
            assert_eq!(
                aspis_core::state_only_sumcheck::state_only_boundary_sum(&polynomial),
                running
            );
            running = aspis_core::state_only_sumcheck::evaluate_state_only_polynomial(
                &polynomial,
                challenges[round],
            );
        }
        assert_eq!(
            compressed.len(),
            STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS
        );
        assert_eq!(
            compressed_mask_sumcheck_terminal(&compressed, &challenges),
            Some(running)
        );

        let coefficients = compressed_mask_sumcheck_terminal_coefficients(&challenges);
        let dependent = (1..coefficients.len())
            .rev()
            .find(|&observation| coefficients[observation] != QM31::ZERO)
            .unwrap();
        let inverse = coefficients[dependent].inv();
        let mut generators = 0usize;
        for observation in 1..coefficients.len() {
            if observation == dependent {
                continue;
            }
            for coordinate in 0..4 {
                let basis = state_only_mask_tower_basis(coordinate);
                let mut vector = vec![QM31::ZERO; coefficients.len()];
                vector[observation] = basis;
                vector[dependent] =
                    QM31::ZERO.sub(inverse.mul(coefficients[observation]).mul(basis));
                assert_eq!(vector[0], QM31::ZERO);
                assert_eq!(
                    compressed_mask_sumcheck_terminal(&vector, &challenges),
                    Some(QM31::ZERO)
                );
                generators += 1;
            }
        }
        assert_eq!(generators, 1_076);
    }

    #[test]
    fn universal_masked_switch_basis_is_triangular_complement_and_mds() {
        use aspis_core::field::P;

        assert_eq!(P % 4, 3);
        for randomness in [16usize, 29] {
            let message = randomness + 3;
            let size = message + randomness;
            let natural = natural_line_basis_polynomials(size);
            let monomials = ordinary_monomials_in_natural_line_basis(size);

            // Generated triangular conversion must reconstruct every ordinary
            // monomial coefficient-for-coefficient and at extension points.
            for degree in 0..size {
                let mut reconstructed = vec![M31::ZERO; size];
                for (basis_index, &scale) in monomials[degree].iter().enumerate() {
                    for (ordinary_degree, &coefficient) in natural[basis_index].iter().enumerate() {
                        reconstructed[ordinary_degree] =
                            reconstructed[ordinary_degree].add(scale.mul(coefficient));
                    }
                }
                assert_eq!(reconstructed[degree], M31::ONE);
                reconstructed[degree] = M31::ZERO;
                assert!(reconstructed.iter().all(|value| *value == M31::ZERO));

                let point = QM31 {
                    c0: CM31::new(M31(17), M31(19)),
                    c1: CM31::new(M31(23), M31(29)),
                };
                let mut weights = WeightAccumulator::empty(8);
                weights.add_line_tensor(QM31::ONE, point).unwrap();
                assert_eq!(
                    natural_line_linear_form(&weights, &monomials[degree]),
                    point.pow(degree as u64)
                );
            }

            let mut code_basis = [1usize, 0]
                .into_iter()
                .chain((randomness + 2)..size)
                .map(|degree| monomials[degree].clone())
                .collect::<Vec<_>>();
            for degree in 0..randomness {
                code_basis.push(
                    monomials[degree]
                        .iter()
                        .copied()
                        .zip(monomials[degree + 2].iter().copied())
                        .map(|(low, high)| low.add(high))
                        .collect(),
                );
            }
            assert_eq!(code_basis.len(), size);
            let mut complement_rank = ColumnEchelon::new(size);
            for column in code_basis {
                complement_rank.insert(column);
            }
            assert_eq!(complement_rank.rank, size);

            // Exact MDS block at arbitrary distinct M31 points.  This is
            // diag(x_i^2+1)*Vandermonde; no schedule-dependent minor or
            // honest-prover retry is needed.
            let points = (0..randomness)
                .map(|index| M31((13 + 97 * index) as u32))
                .collect::<Vec<_>>();
            let mut mds_rank = ColumnEchelon::new(randomness);
            for degree in 0..randomness {
                mds_rank.insert(
                    points
                        .iter()
                        .copied()
                        .map(|x| x.mul(x).add(M31::ONE).mul(x.pow(degree as u64)))
                        .collect(),
                );
            }
            assert_eq!(mds_rank.rank, randomness);
        }
    }

    #[test]
    fn joint_elimination_rejects_a_cross_block_dependency() {
        // Both one-row projections separately have rank one.  The one shared
        // mask column cannot cover their two-row joint View.
        let mut separate_sc = ColumnEchelon::new(1);
        let mut separate_pcs = ColumnEchelon::new(1);
        assert!(separate_sc.insert(vec![M31::ONE]));
        assert!(separate_pcs.insert(vec![M31::ONE]));
        assert_eq!(separate_sc.rank, 1);
        assert_eq!(separate_pcs.rank, 1);

        let mut joint = CarryEchelon::new(1);
        assert!(joint.reduce(vec![M31::ONE], vec![M31::ONE]).is_none());
        let mut conditioned_pcs = ColumnEchelon::new(1);
        assert_eq!(conditioned_pcs.rank, 0);
        assert_ne!(joint.rank + conditioned_pcs.rank, 2);
    }

    #[test]
    fn missing_tail_mask_fails_after_raw_and_sumcheck_blocks_pass() {
        // One source covers the one-dimensional sumcheck block but leaves no
        // conditioned freedom for the independent one-dimensional PCS tail.
        let mut conditioned = CarryEchelon::new(1);
        assert!(conditioned
            .reduce(vec![M31::ONE], vec![M31::ZERO])
            .is_none());
        assert_eq!(conditioned.rank, 1);

        let mask_tail = ColumnEchelon::new(1);
        let mut declared_tail = ColumnEchelon::new(1);
        assert!(declared_tail.insert(vec![M31::ONE]));
        assert_eq!(mask_tail.rank, 0);
        assert_eq!(declared_tail.rank, 1);
        assert_ne!(mask_tail.rank, declared_tail.rank);
    }

    #[test]
    fn q29_two_pad_switch_has_exact_thirty_qm31_conditioned_dimensions() {
        const Q: usize = 29;
        const PADS: usize = 2;
        const VARIABLES: usize = Q + PADS;
        fn power(value: M31, exponent: usize) -> M31 {
            (0..exponent).fold(M31::ONE, |acc, _| acc.mul(value))
        }

        // Query observations touch only the 29 inherited randomness slots;
        // the two private OOD answers touch those slots and both fresh pads.
        // This is the exact block-triangular evaluation geometry required by
        // Construction 9.7, independent of the later circle transport.
        let columns = (0..VARIABLES)
            .map(|variable| {
                let mut image = Vec::with_capacity(VARIABLES);
                for query in 0..Q {
                    image.push(if variable < Q {
                        power(M31((query + 1) as u32), variable)
                    } else {
                        M31::ZERO
                    });
                }
                for ood in 0..PADS {
                    image.push(power(M31((Q + ood + 1) as u32), variable));
                }
                image
            })
            .collect::<Vec<_>>();
        let mut full = ColumnEchelon::new(VARIABLES);
        for column in &columns {
            full.insert(column.clone());
        }
        assert_eq!(full.rank, VARIABLES);

        // Condition on one dense verifier-carried switch identity.  The
        // displayed columns satisfy sum_i c_i*v_i=0 identically.
        let coefficients = (0..VARIABLES)
            .map(|index| M31((index + 2) as u32))
            .collect::<Vec<_>>();
        let last = coefficients[VARIABLES - 1];
        let mut conditioned = ColumnEchelon::new(VARIABLES);
        for variable in 0..VARIABLES - 1 {
            conditioned.insert(
                columns[variable]
                    .iter()
                    .copied()
                    .zip(columns[VARIABLES - 1].iter().copied())
                    .map(|(left, right)| left.mul(last).sub(right.mul(coefficients[variable])))
                    .collect(),
            );
        }
        assert_eq!(conditioned.rank, VARIABLES - 1);
    }

    #[test]
    fn adjacent_scalar_boundaries_do_not_imply_fold_consistency() {
        let alpha = QM31::from_cm31(CM31::from_m31(M31(9)));
        let boundary_claim = QM31::from_cm31(CM31::from_m31(M31(5)));
        let target_claim = QM31::from_cm31(CM31::from_m31(M31(7)));
        let mut polynomial = [QM31::ZERO; 7];
        polynomial[0] = boundary_claim.mul_m31(M31(4).inv());
        polynomial[1] = target_claim
            .sub(polynomial[0])
            .mul(alpha.try_inv().unwrap());
        assert_eq!(boundary_sum(&polynomial), boundary_claim);
        assert_eq!(evaluate_relation(&polynomial, alpha), target_claim);

        // The target is a valid natural coefficient vector satisfying the
        // next scalar claim, but it is not the deterministic fold of the
        // all-zero source. Without a word-level transition check, both
        // adjacent scalar equations accept this separation.
        let deterministic_fold = [QM31::ZERO; 4];
        let target = [target_claim, QM31::ZERO, QM31::ZERO, QM31::ZERO];
        let mut weights = WeightAccumulator::empty(2);
        weights
            .add_dense(vec![QM31::ONE, QM31::ZERO, QM31::ZERO, QM31::ZERO])
            .unwrap();
        assert_eq!(weights.dot(&target), target_claim);
        assert_ne!(target, deterministic_fold);
    }
}
