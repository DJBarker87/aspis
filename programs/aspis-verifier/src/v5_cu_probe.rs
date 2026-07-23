//! Opt-in, local-validator-only CU probes for proposed v5 Spend kernels.
//!
//! Runtime gamma, leaf values, and salts are read from a host-created account.
//! The kernel marker interval executes eighteen C1/C2 private-leaf hashes and
//! eighteen four-slot layer-zero recombinations, followed by the fixed
//! completion-marker and CU-log overhead. The preceding marker interval also
//! includes output allocation alongside parsing and power preparation. Output
//! sinking and the remaining transaction overhead are outside both intervals.
//!
//! Modes 5 to 8 isolate the PCS-relation seam for Component B. All parse and
//! gamma-combine the existing three claims for each of nineteen lanes. Their
//! functionals are batched with `[1, kappa, kappa^2]`. Modes 6 and 7
//! additionally parse a fourth claim per lane, derive `kappa^3`, and construct
//! the current prototype's 1024-row terminal covector: 271 state-coordinate weights, with
//! the copy-inactive pivot and all 752 pad rows zero. The fourth aggregate and
//! all live covector entries are scaled by `kappa^3`. Mode 6 adds that covector
//! to the existing relation accumulator and carries it through the same four
//! dual folds and final four-value dot. Mode 7 instead performs a rejected
//! standalone 1023-term row dot solely as a cost control.
//!
//! Mode 8 retains the same fourth claims but replaces the rejected prototype
//! covector with the candidate's ten aligned degree-27 blocks. Rounds zero to
//! six use 32-row blocks zero to six, rounds seven to nine use blocks 28 to 30,
//! and the initial state occupies row 992. Offsets 28 to 31 in each block have
//! zero terminal weight. The compact state derives `z^(1,2,4,8,16)` by
//! repeated squaring as the low degree bits are consumed, and retains each
//! fixed block selector. It carries the exact dual arity-four normalization
//! through the same four relation folds without materialising a 1024-value
//! vector.
//!
//! Mode 9 is the shared complete-v5 verification kernel. Historical host-only
//! diagnostics may feed it a synthetic prefix; the measured tag-67 SBF path
//! feeds it the sealed real-witness artifact and the live atomic statement.
//! It replays a domain-separated transcript through final grinding and
//! transcript-derived q18 positions, authenticates all five private-opening
//! sections, checks every FRI transition through the final polynomial, runs
//! four production-order OOD/relation sumchecks and the final tensor dot, and
//! retains mode 8's compact Component-B path. Tag 67 remains a CU artefact,
//! not a security-approved v5 proof: production sampling and Rust--Lean
//! correspondence for the B pivot and candidate Component C remain open.

#[path = "v5_wire_skeleton.rs"]
pub mod wire_skeleton;

#[path = "v5_private_openings.rs"]
pub mod private_openings;

#[path = "v5_fri_checks.rs"]
pub mod fri_checks;

#[path = "v5_good_gate_probe.rs"]
pub mod good_gate_probe;

use fri_checks::{check_v5_fri_queries, prepare_v5_pcs_claims, V5PreparedPcsClaims};
use private_openings::{
    verify_v5_private_openings, V5PrivateOpeningRoots, VerifiedV5PrivateOpenings,
};
use wire_skeleton::V5_WIRE_PREFIX_BYTES;

use solana_program::{
    account_info::AccountInfo, entrypoint::ProgramResult, program_error::ProgramError,
    pubkey::Pubkey,
};
#[cfg(not(target_os = "solana"))]
use solana_program::{log::sol_log_compute_units, msg};

use crate::lifecycle::{proof_account_finalized, uploaded_proof_bounds};
use crate::v5_atomic_terminal::{
    decode_v5_atomic_terminal_context, verify_v5_atomic_terminal_from_bytes,
    V5AtomicTerminalChallenges, V5AtomicTerminalClaims, VerifiedV5AtomicTerminal,
    V5_ATOMIC_TERMINAL_CONTEXT_BYTES,
};
use crate::v5_relation_stress::{
    verify_v5_relation_stress_with_additive, V5RelationStressAdditive, V5_RELATION_STRESS_BYTES,
    V5_RELATION_STRESS_CIRCLE_OFFSET, V5_RELATION_STRESS_FINAL_OFFSET,
    V5_RELATION_STRESS_LINE_OFFSET, V5_RELATION_STRESS_MIX_OFFSET, V5_RELATION_STRESS_OOD_OFFSET,
    V5_RELATION_STRESS_OOD_SAMPLES, V5_RELATION_STRESS_ROUNDS, V5_RELATION_STRESS_SUMCHECK_OFFSET,
};
use aspis_core::circle_hiding_prefix::PAYMENT_HIDING_QUERY_DRAW_LIMIT;
use aspis_core::circle_merkle::{CIRCLE_C1_LAYER0_TAG, CIRCLE_C2_LAYER0_TAG};
use aspis_core::field::{
    qm31_m31_dot4_prepared_limbs_4b2_bytes, qm31_m31_dot4_prepared_limbs_4b_bytes,
    qm31_power_table, qm31_sum_products2_prepared, qm31_sum_products3_prepared,
    PreparedQm31Multiplier, M31, QM31,
};
use aspis_core::proof::M31_CIRCLE_BASIS_DISCRIMINATOR;
use aspis_core::state_only_hiding::begin_state_only_masked_sumcheck;
use aspis_core::state_only_prefix::{
    STATE_ONLY_SPEND_BATCH_GRINDING_BITS, STATE_ONLY_SPEND_FOLD_GRINDING_BITS,
    STATE_ONLY_SPEND_GRINDING_BITS,
};
use aspis_core::state_only_private_merkle::{
    private_leaf_hash_record, STATE_ONLY_PRIVATE_LEAF_SALT_BYTES,
};
use aspis_core::state_only_query::{STATE_ONLY_C1_LEAF_BYTES, STATE_ONLY_FIBER_SLOTS};
use aspis_core::state_only_spend_query::{
    gamma_combine_state_only_spend_layer0_prepared, StateOnlySpendQueryPowers, SPEND_C2_LEAF_BYTES,
};
use aspis_core::state_only_sumcheck::{
    begin_state_only_zerocheck, verify_state_only_sumcheck_streaming, STATE_ONLY_SUMCHECK_BYTES,
};
use aspis_core::sumcheck::{WeightAccumulator, SUMCHECK_COEFFICIENTS};
use aspis_core::transcript::{label, Transcript};
use aspis_core::HashFn;
use aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_masks_v3;
use aspis_statement::{atomic_payment_statement_digest_v4, AtomicPaymentStatementV4};

pub const V5_CU_PROBE_TAG: u8 = 66;
/// The current production helper, including its fused three-product C2 sum.
pub const V5_CU_PROBE_PRODUCTION26_MODE: u8 = 0;
pub const V5_CU_PROBE_GENERIC26_NONFUSED_MODE: u8 = 1;
pub const V5_CU_PROBE_GENERIC16_NONFUSED_MODE: u8 = 2;
pub const V5_CU_PROBE_GENERIC16_FUSED_MODE: u8 = 3;
pub const V5_CU_PROBE_GENERIC26_FUSED_MODE: u8 = 4;
pub const V5_CU_PROBE_RELATION3_MODE: u8 = 5;
pub const V5_CU_PROBE_RELATION4_DENSE_MODE: u8 = 6;
pub const V5_CU_PROBE_RELATION4_STANDALONE_DOT_MODE: u8 = 7;
pub const V5_CU_PROBE_RELATION4_COMPACT_MODE: u8 = 8;
pub const V5_CU_PROBE_COMPOSITE_MODE: u8 = 9;
/// Complete instruction width: tag, mode, and expected 32-byte sink.
pub const V5_CU_PROBE_WIRE_BYTES: usize = 1 + 1 + 32;

#[cfg(all(
    feature = "v5-cu-probe",
    not(feature = "no-entrypoint"),
    not(feature = "spend-production")
))]
solana_program::entrypoint!(process_v5_cu_probe_instruction);

pub const V5_CU_PROBE_QUERY_COUNT: usize = 18;
pub const V5_CU_PROBE_PRODUCTION_C1_COLUMNS: usize = 26;
pub const V5_CU_PROBE_CANDIDATE_C1_COLUMNS: usize = 16;
pub const V5_CU_PROBE_C2_COLUMNS: usize = 3;
const M31_BYTES: usize = 4;
const QM31_BYTES: usize = 16;
pub const V5_CU_PROBE_PRODUCTION_C1_VALUE_BYTES: usize =
    STATE_ONLY_FIBER_SLOTS * V5_CU_PROBE_PRODUCTION_C1_COLUMNS * M31_BYTES;
pub const V5_CU_PROBE_CANDIDATE_C1_VALUE_BYTES: usize =
    STATE_ONLY_FIBER_SLOTS * V5_CU_PROBE_CANDIDATE_C1_COLUMNS * M31_BYTES;
pub const V5_CU_PROBE_C2_VALUE_BYTES: usize = SPEND_C2_LEAF_BYTES;
pub const V5_CU_PROBE_PRODUCTION_C1_RECORD_BYTES: usize =
    V5_CU_PROBE_PRODUCTION_C1_VALUE_BYTES + STATE_ONLY_PRIVATE_LEAF_SALT_BYTES;
pub const V5_CU_PROBE_CANDIDATE_C1_RECORD_BYTES: usize =
    V5_CU_PROBE_CANDIDATE_C1_VALUE_BYTES + STATE_ONLY_PRIVATE_LEAF_SALT_BYTES;
pub const V5_CU_PROBE_C2_RECORD_BYTES: usize =
    V5_CU_PROBE_C2_VALUE_BYTES + STATE_ONLY_PRIVATE_LEAF_SALT_BYTES;

pub const V5_CU_PROBE_RELATION_LANES: usize = 19;
pub const V5_CU_PROBE_RELATION_POINTS: usize = 3;
pub const V5_CU_PROBE_RELATION_CLAIMS_PER_LANE: usize = 4;
pub const V5_CU_PROBE_RELATION_LOG_ROWS: u32 = 10;
pub const V5_CU_PROBE_RELATION_FOLDS: usize = 4;
pub const V5_CU_PROBE_RELATION_FINAL_VALUES: usize = 4;
pub const V5_CU_PROBE_RELATION_DENSE_VALUES: usize = 1usize << V5_CU_PROBE_RELATION_LOG_ROWS;
const V5_ATOMIC_V3_INACTIVE_GROUP_MASKS: [u16; 7] =
    [0xe7ff, 0xe7fe, 0xeffe, 0x0000, 0xfff0, 0xfffa, 0xffff];
const V5_ATOMIC_V3_INACTIVE_ROW_GROUPS: [u8; 64] = [
    0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 2, 0, 1, 1, 3, 3, 3, 3, 4, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6,
];
const _: () = assert!(V5_ATOMIC_V3_INACTIVE_GROUP_MASKS.len() == 7);
const _: () = assert!(V5_ATOMIC_V3_INACTIVE_ROW_GROUPS.len() == 64);
const _: () = {
    let mut row = 0;
    while row < V5_ATOMIC_V3_INACTIVE_ROW_GROUPS.len() {
        assert!(
            (V5_ATOMIC_V3_INACTIVE_ROW_GROUPS[row] as usize)
                < V5_ATOMIC_V3_INACTIVE_GROUP_MASKS.len()
        );
        row += 1;
    }
};
pub const V5_CU_PROBE_B_MASK_COORDINATES: usize = 271;
pub const V5_CU_PROBE_B_PAD_COORDINATES: usize = 752;
const _: () = assert!(V5_CU_PROBE_B_MASK_COORDINATES + V5_CU_PROBE_B_PAD_COORDINATES == 1023);

pub const V5_CU_PROBE_B_STRUCTURED_BLOCKS: usize = 10;
pub const V5_CU_PROBE_B_BLOCK_ROWS: usize = 32;
pub const V5_CU_PROBE_B_BLOCK_SELECTORS: [u8; V5_CU_PROBE_B_STRUCTURED_BLOCKS] =
    [0, 1, 2, 3, 4, 5, 6, 28, 29, 30];
pub const V5_CU_PROBE_B_INITIAL_STATE_ROW: usize = 992;
pub const V5_CU_PROBE_B_DEPENDENT_PIVOT_ROW: usize = 993;

pub const V5_CU_REAL_PREFIX_MAGIC: [u8; 8] = *b"AV5PFX03";
pub const V5_CU_REAL_PREFIX_VERSION: u8 = 3;
pub const V5_CU_REAL_PREFIX_HEADER_BYTES: usize = 23;
pub const V5_CU_REAL_PREFIX_C1_ROOT_OFFSET: usize = V5_CU_REAL_PREFIX_HEADER_BYTES;
pub const V5_CU_REAL_PREFIX_C2_ROOT_OFFSET: usize = V5_CU_REAL_PREFIX_C1_ROOT_OFFSET + 32;
pub const V5_CU_REAL_PREFIX_INITIAL_B_CLAIM_OFFSET: usize = V5_CU_REAL_PREFIX_C2_ROOT_OFFSET + 32;
pub const V5_CU_REAL_PREFIX_SUMCHECK_OFFSET: usize =
    V5_CU_REAL_PREFIX_INITIAL_B_CLAIM_OFFSET + QM31_BYTES;
pub const V5_CU_REAL_PREFIX_CLAIMS_OFFSET: usize =
    V5_CU_REAL_PREFIX_SUMCHECK_OFFSET + STATE_ONLY_SUMCHECK_BYTES;
pub const V5_CU_REAL_PREFIX_TERMINAL_OFFSET: usize = V5_CU_REAL_PREFIX_CLAIMS_OFFSET
    + V5_CU_PROBE_RELATION_CLAIMS_PER_LANE * V5_CU_PROBE_RELATION_LANES * QM31_BYTES;
pub const V5_CU_REAL_PREFIX_INACTIVE_CLAIM_OFFSET: usize =
    V5_CU_REAL_PREFIX_TERMINAL_OFFSET + 3 * QM31_BYTES;
pub const V5_CU_REAL_PREFIX_RESERVED_OFFSET: usize =
    V5_CU_REAL_PREFIX_INACTIVE_CLAIM_OFFSET + QM31_BYTES;
pub const V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_BYTES: usize = 32;
pub const V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_COUNT: usize = 5;
pub const V5_CU_REAL_PREFIX_PUBLIC_FS_SALTS_OFFSET: usize = V5_CU_REAL_PREFIX_RESERVED_OFFSET;
pub const V5_CU_REAL_PREFIX_PUBLIC_FS_SALTS_BYTES: usize =
    V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_COUNT * V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_BYTES;
pub const V5_CU_REAL_PREFIX_ZERO_RESERVE_OFFSET: usize =
    V5_CU_REAL_PREFIX_PUBLIC_FS_SALTS_OFFSET + V5_CU_REAL_PREFIX_PUBLIC_FS_SALTS_BYTES;
const V5_CU_REAL_PREFIX_RESERVED_BYTES: usize =
    V5_WIRE_PREFIX_BYTES - V5_CU_REAL_PREFIX_ZERO_RESERVE_OFFSET;
// Literal mirrors for the source-extracted structural parser.  Compile-time
// equalities below bind them to the derived wire layout.
const V5_CU_REAL_PREFIX_ACCEPTED_BYTES: usize = 6_423;
const V5_CU_REAL_PREFIX_ZERO_TAIL_BYTES: usize = 400;
const V5_CU_REAL_PREFIX_C1_ROOT_OFFSET_EXACT: usize = 23;
const V5_CU_REAL_PREFIX_C2_ROOT_OFFSET_EXACT: usize = 55;

const _: () = assert!(V5_CU_REAL_PREFIX_C1_ROOT_OFFSET == 23);
const _: () = assert!(V5_CU_REAL_PREFIX_C2_ROOT_OFFSET == 55);
const _: () = assert!(V5_CU_REAL_PREFIX_C1_ROOT_OFFSET_EXACT == V5_CU_REAL_PREFIX_C1_ROOT_OFFSET);
const _: () = assert!(V5_CU_REAL_PREFIX_C2_ROOT_OFFSET_EXACT == V5_CU_REAL_PREFIX_C2_ROOT_OFFSET);
const _: () = assert!(V5_CU_REAL_PREFIX_INITIAL_B_CLAIM_OFFSET == 87);
const _: () = assert!(V5_CU_REAL_PREFIX_SUMCHECK_OFFSET == 103);
const _: () = assert!(V5_CU_REAL_PREFIX_CLAIMS_OFFSET == 4_583);
const _: () = assert!(V5_CU_REAL_PREFIX_TERMINAL_OFFSET == 5_799);
const _: () = assert!(V5_CU_REAL_PREFIX_INACTIVE_CLAIM_OFFSET == 5_847);
const _: () = assert!(V5_CU_REAL_PREFIX_RESERVED_OFFSET == 5_863);
const _: () = assert!(V5_CU_REAL_PREFIX_PUBLIC_FS_SALTS_BYTES == 160);
const _: () = assert!(V5_CU_REAL_PREFIX_ZERO_RESERVE_OFFSET == 6_023);
const _: () = assert!(V5_CU_REAL_PREFIX_ZERO_RESERVE_OFFSET < V5_WIRE_PREFIX_BYTES);
const _: () = assert!(V5_CU_REAL_PREFIX_RESERVED_BYTES == 400);
const _: () = assert!(V5_CU_REAL_PREFIX_RESERVED_BYTES % 8 == 0);
const _: () = assert!(V5_CU_REAL_PREFIX_ACCEPTED_BYTES == V5_WIRE_PREFIX_BYTES);
const _: () = assert!(V5_CU_REAL_PREFIX_ZERO_TAIL_BYTES == V5_CU_REAL_PREFIX_RESERVED_BYTES);

pub const V5_CU_PROBE_ACCOUNT_MAGIC: [u8; 8] = *b"AV5CUP08";
pub const V5_CU_PROBE_GAMMA_OFFSET: usize = V5_CU_PROBE_ACCOUNT_MAGIC.len();
/// Mode 9 carries only the authenticated sixteen-lane candidate records.
/// The retired twenty-six-lane comparison data is a tag-66 diagnostic sidecar
/// and is not part of this accepted grammar.
pub const V5_CU_PROBE_CANDIDATE_C1_OFFSET: usize = V5_CU_PROBE_GAMMA_OFFSET + QM31_BYTES;
pub const V5_CU_PROBE_C2_OFFSET: usize = V5_CU_PROBE_CANDIDATE_C1_OFFSET
    + V5_CU_PROBE_QUERY_COUNT * V5_CU_PROBE_CANDIDATE_C1_RECORD_BYTES;
pub const V5_CU_PROBE_RELATION_SCALES_OFFSET: usize =
    V5_CU_PROBE_C2_OFFSET + V5_CU_PROBE_QUERY_COUNT * V5_CU_PROBE_C2_RECORD_BYTES;
pub const V5_CU_PROBE_RELATION_POINTS_OFFSET: usize =
    V5_CU_PROBE_RELATION_SCALES_OFFSET + V5_CU_PROBE_RELATION_POINTS * QM31_BYTES;
pub const V5_CU_PROBE_RELATION_CLAIMS_OFFSET: usize = V5_CU_PROBE_RELATION_POINTS_OFFSET
    + V5_CU_PROBE_RELATION_POINTS * V5_CU_PROBE_RELATION_LOG_ROWS as usize * QM31_BYTES;
pub const V5_CU_PROBE_RELATION_ALPHAS_OFFSET: usize = V5_CU_PROBE_RELATION_CLAIMS_OFFSET
    + V5_CU_PROBE_RELATION_CLAIMS_PER_LANE * V5_CU_PROBE_RELATION_LANES * QM31_BYTES;
pub const V5_CU_PROBE_RELATION_FINAL_OFFSET: usize =
    V5_CU_PROBE_RELATION_ALPHAS_OFFSET + V5_CU_PROBE_RELATION_FOLDS * QM31_BYTES;
pub const V5_CU_PROBE_RELATION_FINAL_BYTES: usize = V5_CU_PROBE_RELATION_FINAL_VALUES * QM31_BYTES;
pub const V5_CU_PROBE_FOLD_NONCES_BYTES: usize = V5_CU_PROBE_RELATION_FOLDS * 8;
pub const V5_CU_PROBE_BATCH_NONCE_RELATIVE_OFFSET: usize = V5_CU_PROBE_FOLD_NONCES_BYTES;
pub const V5_CU_PROBE_BATCH_NONCE_OFFSET: usize =
    V5_CU_PROBE_RELATION_FINAL_OFFSET + V5_CU_PROBE_BATCH_NONCE_RELATIVE_OFFSET;
pub const V5_CU_PROBE_BATCH_NONCE_BYTES: usize = 8;
pub const V5_CU_PROBE_RELATION_FINAL_ZERO_TAIL_RELATIVE_OFFSET: usize =
    V5_CU_PROBE_BATCH_NONCE_RELATIVE_OFFSET + V5_CU_PROBE_BATCH_NONCE_BYTES;
pub const V5_CU_PROBE_RELATION_FINAL_ZERO_TAIL_OFFSET: usize =
    V5_CU_PROBE_RELATION_FINAL_OFFSET + V5_CU_PROBE_RELATION_FINAL_ZERO_TAIL_RELATIVE_OFFSET;
pub const V5_CU_PROBE_RELATION_FINAL_ZERO_TAIL_BYTES: usize =
    V5_CU_PROBE_RELATION_FINAL_BYTES - V5_CU_PROBE_RELATION_FINAL_ZERO_TAIL_RELATIVE_OFFSET;
pub const V5_CU_PROBE_PREFIX_OFFSET: usize =
    V5_CU_PROBE_RELATION_FINAL_OFFSET + V5_CU_PROBE_RELATION_FINAL_BYTES;
pub const V5_CU_PROBE_ATOMIC_TERMINAL_CONTEXT_OFFSET: usize =
    V5_CU_PROBE_PREFIX_OFFSET + V5_WIRE_PREFIX_BYTES;
pub const V5_CU_PROBE_PRIVATE_ROOTS_OFFSET: usize =
    V5_CU_PROBE_ATOMIC_TERMINAL_CONTEXT_OFFSET + V5_ATOMIC_TERMINAL_CONTEXT_BYTES;
// Proof-facing literal mirror. The compile-time equality keeps the executed
// parser tied to the derived grammar while giving Charon/Aeneas a closed
// constant instead of the entire account-layout dependency graph.
const V5_CU_PROBE_PREFIX_OFFSET_EXACT: usize = 11_112;
const V5_CU_PROBE_ATOMIC_TERMINAL_CONTEXT_OFFSET_EXACT: usize = 17_535;
const V5_CU_PROBE_PRIVATE_ROOTS_OFFSET_EXACT: usize = 17_975;
const V5_CU_PROBE_RELATION_FINAL_OFFSET_EXACT: usize = 11_048;
const V5_CU_PROBE_BATCH_NONCE_OFFSET_EXACT: usize = 11_080;
const V5_CU_PROBE_FINAL_NONCE_OFFSET_EXACT: usize = 19_127;
const V5_CU_PROBE_QUERY_SELECTOR_OFFSET_EXACT: usize = 19_135;
const _: () = assert!(V5_CU_PROBE_RELATION_FINAL_OFFSET == 11_048);
const _: () = assert!(V5_CU_PROBE_BATCH_NONCE_RELATIVE_OFFSET == 32);
const _: () = assert!(V5_CU_PROBE_BATCH_NONCE_OFFSET == 11_080);
const _: () = assert!(V5_CU_PROBE_RELATION_FINAL_ZERO_TAIL_RELATIVE_OFFSET == 40);
const _: () = assert!(V5_CU_PROBE_RELATION_FINAL_ZERO_TAIL_OFFSET == 11_088);
const _: () = assert!(V5_CU_PROBE_RELATION_FINAL_ZERO_TAIL_BYTES == 24);
const _: () = assert!(V5_CU_PROBE_RELATION_FINAL_OFFSET_EXACT == V5_CU_PROBE_RELATION_FINAL_OFFSET);
const _: () = assert!(V5_CU_PROBE_BATCH_NONCE_OFFSET_EXACT == V5_CU_PROBE_BATCH_NONCE_OFFSET);
const _: () = assert!(V5_CU_PROBE_PREFIX_OFFSET_EXACT == V5_CU_PROBE_PREFIX_OFFSET);
const _: () = assert!(
    V5_CU_PROBE_ATOMIC_TERMINAL_CONTEXT_OFFSET_EXACT == V5_CU_PROBE_ATOMIC_TERMINAL_CONTEXT_OFFSET
);
const _: () = assert!(V5_CU_PROBE_PRIVATE_ROOTS_OFFSET_EXACT == V5_CU_PROBE_PRIVATE_ROOTS_OFFSET);
pub const V5_CU_PROBE_PRIVATE_ROOT_BYTES: usize = 32 * 5;
pub const V5_CU_PROBE_FINAL_COEFFICIENTS_OFFSET: usize =
    V5_CU_PROBE_PRIVATE_ROOTS_OFFSET + V5_CU_PROBE_PRIVATE_ROOT_BYTES;
pub const V5_CU_PROBE_FINAL_COEFFICIENTS_BYTES: usize = 4 * QM31_BYTES;
pub const V5_CU_PROBE_RELATION_STRESS_OFFSET: usize =
    V5_CU_PROBE_FINAL_COEFFICIENTS_OFFSET + V5_CU_PROBE_FINAL_COEFFICIENTS_BYTES;
pub const V5_CU_PROBE_FINAL_NONCE_OFFSET: usize =
    V5_CU_PROBE_RELATION_STRESS_OFFSET + V5_RELATION_STRESS_BYTES;
pub const V5_CU_PROBE_QUERY_SELECTOR_OFFSET: usize = V5_CU_PROBE_FINAL_NONCE_OFFSET + 8;
pub const V5_CU_PROBE_PRIVATE_PROOF_OFFSET: usize = V5_CU_PROBE_QUERY_SELECTOR_OFFSET + 1;
const _: () = assert!(V5_CU_PROBE_FINAL_NONCE_OFFSET_EXACT == V5_CU_PROBE_FINAL_NONCE_OFFSET);
const _: () = assert!(V5_CU_PROBE_QUERY_SELECTOR_OFFSET_EXACT == V5_CU_PROBE_QUERY_SELECTOR_OFFSET);
/// Fixed account prefix. The canonical five-section opening occupies all
/// remaining bytes and therefore has no proof-carried length field.
pub const V5_CU_PROBE_ACCOUNT_BYTES: usize = V5_CU_PROBE_PRIVATE_PROOF_OFFSET;
/// Exact accepted-input envelope for the five canonical private-opening
/// sections.  The transcript produces at most eighteen distinct indices per
/// section.  For a radix-4 tree with a binary cap, the frontier is maximised
/// by keeping those indices in distinct parents until the finite level width
/// forces convergence.  The maxima below range over every reachable count
/// `1..=18`, not merely the three retained CU fixtures.
pub const V5_CU_PROBE_MAX_OPENING_COUNTS: [usize; 5] = [18, 18, 18, 18, 18];
pub const V5_CU_PROBE_MAX_OPENING_FRONTIER_NODES: [usize; 5] = [338, 338, 284, 230, 176];
pub const V5_CU_PROBE_MAX_OPENING_SECTION_BYTES: [usize; 5] =
    [16_006, 14_854, 10_822, 9_094, 7_366];
pub const V5_CU_PROBE_MAX_PRIVATE_PROOF_BYTES: usize = 58_142;
pub const V5_CU_PROBE_MAX_PROOF_BODY_BYTES: usize =
    V5_CU_PROBE_ACCOUNT_BYTES + V5_CU_PROBE_MAX_PRIVATE_PROOF_BYTES;
pub const V5_CU_PROBE_MAX_SEALED_PROOF_ACCOUNT_BYTES: usize =
    crate::PROOF_ACCOUNT_HEADER_LEN + V5_CU_PROBE_MAX_PROOF_BODY_BYTES;
const _: () = assert!(V5_CU_PROBE_MAX_PROOF_BODY_BYTES == 77_278);
const _: () = assert!(V5_CU_PROBE_MAX_SEALED_PROOF_ACCOUNT_BYTES == 77_318);
/// Tag-66-only sidecar retaining the old width-26 comparison input.  Mode 9
/// never parses this range and treats a sidecar as malformed private-proof
/// bytes.
pub const V5_CU_PROBE_PRODUCTION_C1_OFFSET: usize = V5_CU_PROBE_ACCOUNT_BYTES;
pub const V5_CU_PROBE_DIAGNOSTIC_PRIVATE_PROOF_OFFSET: usize = V5_CU_PROBE_PRODUCTION_C1_OFFSET
    + V5_CU_PROBE_QUERY_COUNT * V5_CU_PROBE_PRODUCTION_C1_RECORD_BYTES;
pub const V5_CU_PROBE_DIAGNOSTIC_ACCOUNT_BYTES: usize = V5_CU_PROBE_DIAGNOSTIC_PRIVATE_PROOF_OFFSET;
/// Provisional positions used only to construct query-independent roots before
/// the final transcript is known. They are never accepted by mode 9.
pub const V5_CU_PROBE_PROVISIONAL_QUERIES: [u32; V5_CU_PROBE_QUERY_COUNT] = [
    17, 7_018, 14_019, 21_020, 28_021, 35_022, 42_023, 49_024, 56_025, 63_026, 70_027, 77_028,
    84_029, 91_030, 98_031, 105_032, 112_033, 119_034,
];

const QUERY_SINK_BYTES: usize = 32 + 32 + STATE_ONLY_FIBER_SLOTS * QM31_BYTES;
const PROBE_SINK_MATERIAL_BYTES: usize = V5_CU_PROBE_QUERY_COUNT * QUERY_SINK_BYTES;
const SINK_DOMAIN: &[u8] = b"aspis-v5-cu-probe-v3";

#[derive(Clone, Copy)]
struct ProbeOutput {
    c1_hash: [u8; 32],
    c2_hash: [u8; 32],
    combined: [QM31; STATE_ONLY_FIBER_SLOTS],
}

const EMPTY_OUTPUT: ProbeOutput = ProbeOutput {
    c1_hash: [0; 32],
    c2_hash: [0; 32],
    combined: [QM31::ZERO; STATE_ONLY_FIBER_SLOTS],
};

struct ParsedProbeData<'a> {
    gamma: QM31,
    production_c1: &'a [u8],
    candidate_c1: &'a [u8],
    c2: &'a [u8],
    relation_scales: &'a [u8],
    relation_points: &'a [u8],
    relation_claims: &'a [u8],
    relation_alphas: &'a [u8],
    relation_final: &'a [u8],
    v5_fold_nonces: [u64; V5_CU_PROBE_RELATION_FOLDS],
    v5_batch_nonce: u64,
    v5_wire_prefix: &'a [u8],
    v5_atomic_terminal_context: &'a [u8],
    v5_private_roots: V5PrivateOpeningRoots,
    v5_final_coefficients: &'a [u8],
    v5_relation_stress: &'a [u8; V5_RELATION_STRESS_BYTES],
    v5_final_nonce: u64,
    v5_query_selector: u8,
    v5_private_proof: &'a [u8],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct V5WorkWireProjection {
    fold_nonces: [u64; V5_CU_PROBE_RELATION_FOLDS],
    batch_nonce: u64,
    final_nonce: u64,
    query_selector: u8,
}

#[inline(always)]
fn v5_work_wire_magic_is_valid(data: &[u8]) -> bool {
    data.len() >= 8
        && data[0] == V5_CU_PROBE_ACCOUNT_MAGIC[0]
        && data[1] == V5_CU_PROBE_ACCOUNT_MAGIC[1]
        && data[2] == V5_CU_PROBE_ACCOUNT_MAGIC[2]
        && data[3] == V5_CU_PROBE_ACCOUNT_MAGIC[3]
        && data[4] == V5_CU_PROBE_ACCOUNT_MAGIC[4]
        && data[5] == V5_CU_PROBE_ACCOUNT_MAGIC[5]
        && data[6] == V5_CU_PROBE_ACCOUNT_MAGIC[6]
        && data[7] == V5_CU_PROBE_ACCOUNT_MAGIC[7]
}

#[inline(always)]
fn v5_work_wire_u64(data: &[u8], offset: usize) -> u64 {
    u64::from_le_bytes([
        data[offset],
        data[offset + 1],
        data[offset + 2],
        data[offset + 3],
        data[offset + 4],
        data[offset + 5],
        data[offset + 6],
        data[offset + 7],
    ])
}

/// Pure projection called by the real mode-9 parser after its exact length
/// and account-magic guard. Literal offsets are compile-time tied to the
/// derived grammar above so source extraction sees the executed byte map.
#[inline(always)]
fn project_v5_work_wire(data: &[u8]) -> V5WorkWireProjection {
    V5WorkWireProjection {
        fold_nonces: [
            v5_work_wire_u64(data, V5_CU_PROBE_RELATION_FINAL_OFFSET_EXACT),
            v5_work_wire_u64(data, V5_CU_PROBE_RELATION_FINAL_OFFSET_EXACT + 8),
            v5_work_wire_u64(data, V5_CU_PROBE_RELATION_FINAL_OFFSET_EXACT + 16),
            v5_work_wire_u64(data, V5_CU_PROBE_RELATION_FINAL_OFFSET_EXACT + 24),
        ],
        batch_nonce: v5_work_wire_u64(data, V5_CU_PROBE_BATCH_NONCE_OFFSET_EXACT),
        final_nonce: v5_work_wire_u64(data, V5_CU_PROBE_FINAL_NONCE_OFFSET_EXACT),
        query_selector: data[V5_CU_PROBE_QUERY_SELECTOR_OFFSET_EXACT],
    }
}

impl ParsedProbeData<'_> {
    fn production_c1_record(&self, query: usize) -> Option<&[u8]> {
        let start = query * V5_CU_PROBE_PRODUCTION_C1_RECORD_BYTES;
        self.production_c1
            .get(start..start + V5_CU_PROBE_PRODUCTION_C1_RECORD_BYTES)
    }

    fn candidate_c1_record(&self, query: usize) -> &[u8] {
        let start = query * V5_CU_PROBE_CANDIDATE_C1_RECORD_BYTES;
        &self.candidate_c1[start..start + V5_CU_PROBE_CANDIDATE_C1_RECORD_BYTES]
    }

    fn c2_record(&self, query: usize) -> &[u8] {
        let start = query * V5_CU_PROBE_C2_RECORD_BYTES;
        &self.c2[start..start + V5_CU_PROBE_C2_RECORD_BYTES]
    }
}

#[inline(always)]
fn parse_v5_wire_prefix(data: &[u8]) -> &[u8] {
    &data[V5_CU_PROBE_PREFIX_OFFSET_EXACT..V5_CU_PROBE_ATOMIC_TERMINAL_CONTEXT_OFFSET_EXACT]
}

#[inline(always)]
fn parse_v5_private_roots_at(data: &[u8], start: usize) -> V5PrivateOpeningRoots {
    V5PrivateOpeningRoots {
        c1: *real_v5_prefix_root(data, start),
        c2: *real_v5_prefix_root(data, start + 32),
        later: [
            *real_v5_prefix_root(data, start + 64),
            *real_v5_prefix_root(data, start + 96),
            *real_v5_prefix_root(data, start + 128),
        ],
    }
}

#[inline(always)]
fn parse_v5_private_roots(data: &[u8]) -> V5PrivateOpeningRoots {
    parse_v5_private_roots_at(data, V5_CU_PROBE_PRIVATE_ROOTS_OFFSET_EXACT)
}

#[inline(always)]
fn v5_prefix_roots_match_private(prefix: &[u8], private_roots: &V5PrivateOpeningRoots) -> bool {
    real_v5_prefix_root(prefix, V5_CU_REAL_PREFIX_C1_ROOT_OFFSET_EXACT) == &private_roots.c1
        && real_v5_prefix_root(prefix, V5_CU_REAL_PREFIX_C2_ROOT_OFFSET_EXACT) == &private_roots.c2
}

fn parse_probe_data_with_layout<'a>(
    data: &'a [u8],
    production_c1_range: Option<(usize, usize)>,
    private_proof_offset: usize,
) -> Result<ParsedProbeData<'a>, ProgramError> {
    if data.len() < private_proof_offset || !v5_work_wire_magic_is_valid(data) {
        return Err(ProgramError::InvalidAccountData);
    }
    let work_wire = project_v5_work_wire(data);
    let production_c1 = match production_c1_range {
        Some((start, end)) => data
            .get(start..end)
            .ok_or(ProgramError::InvalidAccountData)?,
        None => &data[0..0],
    };
    let gamma =
        QM31::from_le_bytes(&data[V5_CU_PROBE_GAMMA_OFFSET..V5_CU_PROBE_GAMMA_OFFSET + QM31_BYTES])
            .ok_or(ProgramError::InvalidAccountData)?;
    let relation_final = &data[V5_CU_PROBE_RELATION_FINAL_OFFSET..V5_CU_PROBE_PREFIX_OFFSET];
    Ok(ParsedProbeData {
        gamma,
        production_c1,
        candidate_c1: &data[V5_CU_PROBE_CANDIDATE_C1_OFFSET..V5_CU_PROBE_C2_OFFSET],
        c2: &data[V5_CU_PROBE_C2_OFFSET..V5_CU_PROBE_RELATION_SCALES_OFFSET],
        relation_scales: &data
            [V5_CU_PROBE_RELATION_SCALES_OFFSET..V5_CU_PROBE_RELATION_POINTS_OFFSET],
        relation_points: &data
            [V5_CU_PROBE_RELATION_POINTS_OFFSET..V5_CU_PROBE_RELATION_CLAIMS_OFFSET],
        relation_claims: &data
            [V5_CU_PROBE_RELATION_CLAIMS_OFFSET..V5_CU_PROBE_RELATION_ALPHAS_OFFSET],
        relation_alphas: &data
            [V5_CU_PROBE_RELATION_ALPHAS_OFFSET..V5_CU_PROBE_RELATION_FINAL_OFFSET],
        relation_final,
        v5_fold_nonces: work_wire.fold_nonces,
        v5_batch_nonce: work_wire.batch_nonce,
        v5_wire_prefix: parse_v5_wire_prefix(data),
        v5_atomic_terminal_context: &data
            [V5_CU_PROBE_ATOMIC_TERMINAL_CONTEXT_OFFSET..V5_CU_PROBE_PRIVATE_ROOTS_OFFSET],
        v5_private_roots: parse_v5_private_roots(data),
        v5_final_coefficients: &data
            [V5_CU_PROBE_FINAL_COEFFICIENTS_OFFSET..V5_CU_PROBE_RELATION_STRESS_OFFSET],
        v5_relation_stress: data
            [V5_CU_PROBE_RELATION_STRESS_OFFSET..V5_CU_PROBE_FINAL_NONCE_OFFSET]
            .try_into()
            .unwrap(),
        v5_final_nonce: work_wire.final_nonce,
        v5_query_selector: work_wire.query_selector,
        v5_private_proof: &data[private_proof_offset..],
    })
}

/// Parse the exact mode-9 body.  Its fixed prefix is immediately followed by
/// the five authenticated private-opening sections.
fn parse_probe_data(data: &[u8]) -> Result<ParsedProbeData<'_>, ProgramError> {
    // Canonical section counts and tree topology make every longer body
    // impossible. Reject it before transcript replay or Merkle hashing so an
    // over-allocated proof account cannot enlarge the accepted CU surface.
    if data.len() > V5_CU_PROBE_MAX_PROOF_BODY_BYTES {
        return Err(ProgramError::InvalidAccountData);
    }
    parse_probe_data_with_layout(data, None, V5_CU_PROBE_PRIVATE_PROOF_OFFSET)
}

/// Parse the tag-66 comparison fixture.  The width-26 input is a sidecar after
/// the repaired mode-9 fixed prefix and before the diagnostic private suffix.
#[cfg(not(target_os = "solana"))]
fn parse_diagnostic_probe_data(data: &[u8]) -> Result<ParsedProbeData<'_>, ProgramError> {
    parse_probe_data_with_layout(
        data,
        Some((
            V5_CU_PROBE_PRODUCTION_C1_OFFSET,
            V5_CU_PROBE_DIAGNOSTIC_PRIVATE_PROOF_OFFSET,
        )),
        V5_CU_PROBE_DIAGNOSTIC_PRIVATE_PROOF_OFFSET,
    )
}

/// Select the narrowest tag-66 host grammar actually consumed by `mode`.
/// Width-26 kernels retain the comparison-only production-C1 sidecar.  The
/// width-16 and relation-control modes use only fields in the repaired fixed
/// prefix; this shorter grammar is host/tag-66 diagnostic behavior only.
/// Mode 9 keeps the sealed runtime grammar and unknown modes fail before any
/// account-layout parser is invoked.
#[cfg(not(target_os = "solana"))]
fn parse_probe_data_for_mode(mode: u8, data: &[u8]) -> Result<ParsedProbeData<'_>, ProgramError> {
    match mode {
        V5_CU_PROBE_PRODUCTION26_MODE
        | V5_CU_PROBE_GENERIC26_NONFUSED_MODE
        | V5_CU_PROBE_GENERIC26_FUSED_MODE => parse_diagnostic_probe_data(data),
        V5_CU_PROBE_GENERIC16_NONFUSED_MODE
        | V5_CU_PROBE_GENERIC16_FUSED_MODE
        | V5_CU_PROBE_RELATION3_MODE
        | V5_CU_PROBE_RELATION4_DENSE_MODE
        | V5_CU_PROBE_RELATION4_STANDALONE_DOT_MODE
        | V5_CU_PROBE_RELATION4_COMPACT_MODE
        | V5_CU_PROBE_COMPOSITE_MODE => parse_probe_data(data),
        _ => Err(ProgramError::InvalidInstructionData),
    }
}

fn verify_v5_private_suffix<'a>(
    parsed: &'a ParsedProbeData<'a>,
    queries: &[u32; V5_CU_PROBE_QUERY_COUNT],
) -> Result<VerifiedV5PrivateOpenings<'a>, ProgramError> {
    let verified = verify_v5_private_openings(
        crate::verify::sbf_hashv,
        &parsed.v5_private_roots,
        queries,
        parsed.v5_private_proof,
    )
    .map_err(|_| ProgramError::InvalidAccountData)?;
    if verified.c1.records != parsed.candidate_c1 || verified.c2.records != parsed.c2 {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(verified)
}

fn stress_qm31(parsed: &ParsedProbeData<'_>, offset: usize) -> Result<QM31, ProgramError> {
    QM31::from_le_bytes(&parsed.v5_relation_stress[offset..offset + QM31_BYTES])
        .ok_or(ProgramError::InvalidAccountData)
}

fn absorb_real_v5_ood(
    transcript: &mut Transcript,
    label_value: u8,
    round: usize,
    sample: usize,
    value: QM31,
) {
    let mut record = [0u8; 18];
    record[0] = round as u8;
    record[1] = sample as u8;
    value.write_le_bytes(&mut record[2..]);
    transcript.absorb(label_value, &record);
}

fn absorb_real_v5_relation_sumcheck(
    transcript: &mut Transcript,
    round: usize,
    polynomial_bytes: &[u8],
) {
    let mut record = [0u8; 1 + SUMCHECK_COEFFICIENTS * QM31_BYTES];
    record[0] = round as u8;
    record[1..].copy_from_slice(polynomial_bytes);
    transcript.absorb(label::M31_CIRCLE_RELATION_SUMCHECK, &record);
}

const _: () = assert!(STATE_ONLY_SPEND_BATCH_GRINDING_BITS == 37);
const _: () = assert!(STATE_ONLY_SPEND_FOLD_GRINDING_BITS[0] == 34);
const _: () = assert!(STATE_ONLY_SPEND_FOLD_GRINDING_BITS[1] == 33);
const _: () = assert!(STATE_ONLY_SPEND_FOLD_GRINDING_BITS[2] == 30);
const _: () = assert!(STATE_ONLY_SPEND_FOLD_GRINDING_BITS[3] == 25);
const _: () = assert!(STATE_ONLY_SPEND_GRINDING_BITS == 32);
const _: () = assert!(label::M31_PAYMENT_BATCH_POW_NONCE == 28);
const _: () = assert!(label::M31_CIRCLE_FOLD_POW_NONCE == 20);
const _: () = assert!(label::GRIND_NONCE == 5);

#[inline(always)]
fn v5_batch_work_difficulty() -> u8 {
    37
}

#[inline(always)]
fn v5_fold_work_difficulty(round: usize) -> Option<u8> {
    match round {
        0 => Some(34),
        1 => Some(33),
        2 => Some(30),
        3 => Some(25),
        _ => None,
    }
}

#[inline(always)]
fn v5_final_work_difficulty() -> u8 {
    32
}

#[inline(always)]
fn v5_fold_work_record(round: usize, nonce: u64) -> [u8; 9] {
    let bytes = nonce.to_le_bytes();
    [
        round as u8,
        bytes[0],
        bytes[1],
        bytes[2],
        bytes[3],
        bytes[4],
        bytes[5],
        bytes[6],
        bytes[7],
    ]
}

#[inline(always)]
fn v5_batch_work_record(nonce: u64) -> [u8; 8] {
    nonce.to_le_bytes()
}

#[inline(always)]
fn v5_final_work_record(nonce: u64) -> [u8; 8] {
    nonce.to_le_bytes()
}

#[inline(always)]
fn v5_fold_work_absorb_input(round: usize, nonce: u64) -> (u8, [u8; 9]) {
    (
        label::M31_CIRCLE_FOLD_POW_NONCE,
        v5_fold_work_record(round, nonce),
    )
}

#[inline(always)]
fn v5_batch_work_absorb_input(nonce: u64) -> (u8, [u8; 8]) {
    (
        label::M31_PAYMENT_BATCH_POW_NONCE,
        v5_batch_work_record(nonce),
    )
}

#[inline(always)]
fn v5_final_work_absorb_input(nonce: u64) -> (u8, [u8; 8]) {
    (label::GRIND_NONCE, v5_final_work_record(nonce))
}

fn absorb_real_v5_fold_nonce(transcript: &mut Transcript, round: usize, nonce: u64) {
    let (label, record) = v5_fold_work_absorb_input(round, nonce);
    transcript.absorb(label, &record);
}

#[inline(always)]
fn absorb_real_v5_batch_nonce(transcript: &mut Transcript, nonce: u64) {
    let (label, record) = v5_batch_work_absorb_input(nonce);
    transcript.absorb(label, &record);
}

#[inline(always)]
fn absorb_real_v5_final_nonce(transcript: &mut Transcript, nonce: u64) {
    let (label, record) = v5_final_work_absorb_input(nonce);
    transcript.absorb(label, &record);
}

#[inline(always)]
fn v5_real_work_is_valid(transcript: &Transcript, nonce: u64, bits: u8) -> bool {
    transcript.grinding_ok(nonce, bits)
}

#[inline(always)]
fn require_real_v5_work(transcript: &Transcript, nonce: u64, bits: u8) -> ProgramResult {
    if !v5_real_work_is_valid(transcript, nonce, bits) {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}

#[inline(always)]
fn check_and_absorb_real_v5_batch_nonce(transcript: &mut Transcript, nonce: u64) -> ProgramResult {
    require_real_v5_work(transcript, nonce, v5_batch_work_difficulty())?;
    absorb_real_v5_batch_nonce(transcript, nonce);
    Ok(())
}

#[inline(always)]
fn check_and_absorb_real_v5_fold_nonce(
    transcript: &mut Transcript,
    round: usize,
    nonce: u64,
) -> ProgramResult {
    let bits = v5_fold_work_difficulty(round).ok_or(ProgramError::InvalidAccountData)?;
    require_real_v5_work(transcript, nonce, bits)?;
    absorb_real_v5_fold_nonce(transcript, round, nonce);
    Ok(())
}

#[inline(always)]
fn check_and_absorb_real_v5_final_nonce(transcript: &mut Transcript, nonce: u64) -> ProgramResult {
    require_real_v5_work(transcript, nonce, v5_final_work_difficulty())?;
    absorb_real_v5_final_nonce(transcript, nonce);
    Ok(())
}

#[inline(always)]
fn verify_v5_relation_final_zero_tail(relation_final: &[u8]) -> ProgramResult {
    if !v5_relation_final_zero_tail_is_valid(relation_final) {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}

#[inline(always)]
fn v5_relation_final_zero_tail_is_valid(relation_final: &[u8]) -> bool {
    if relation_final.len() != 64 {
        return false;
    }
    let mut offset = 40usize;
    while offset < 64 {
        if relation_final[offset] != 0 {
            return false;
        }
        offset += 1;
    }
    true
}

fn replay_real_v5_relation_rounds(
    mut transcript: Transcript,
    parsed: &ParsedProbeData<'_>,
) -> Result<Transcript, ProgramError> {
    verify_v5_relation_final_zero_tail(parsed.relation_final)?;
    for round in 0..V5_RELATION_STRESS_ROUNDS {
        for sample in 0..V5_RELATION_STRESS_OOD_SAMPLES {
            if round == 0 {
                let point = transcript
                    .challenge_secure_circle_point()
                    .map_err(|_| ProgramError::InvalidAccountData)?;
                let point_offset = V5_RELATION_STRESS_CIRCLE_OFFSET + (2 * sample) * QM31_BYTES;
                if stress_qm31(parsed, point_offset)? != point.x
                    || stress_qm31(parsed, point_offset + QM31_BYTES)? != point.y
                {
                    return Err(ProgramError::InvalidAccountData);
                }
            } else {
                let point = transcript
                    .challenge_ood_qm31()
                    .map_err(|_| ProgramError::InvalidAccountData)?;
                let point_index = (round - 1) * V5_RELATION_STRESS_OOD_SAMPLES + sample;
                if stress_qm31(
                    parsed,
                    V5_RELATION_STRESS_LINE_OFFSET + point_index * QM31_BYTES,
                )? != point
                {
                    return Err(ProgramError::InvalidAccountData);
                }
            }
            let observation = round * V5_RELATION_STRESS_OOD_SAMPLES + sample;
            let value = stress_qm31(
                parsed,
                V5_RELATION_STRESS_OOD_OFFSET + observation * QM31_BYTES,
            )?;
            absorb_real_v5_ood(
                &mut transcript,
                if round == 0 {
                    label::M31_CIRCLE_OOD_VALUE
                } else {
                    label::M31_LINE_OOD_VALUE
                },
                round,
                sample,
                value,
            );
            let mix = transcript
                .challenge_qm31()
                .map_err(|_| ProgramError::InvalidAccountData)?;
            if stress_qm31(
                parsed,
                V5_RELATION_STRESS_MIX_OFFSET + observation * QM31_BYTES,
            )? != mix
            {
                return Err(ProgramError::InvalidAccountData);
            }
        }

        let sumcheck_start =
            V5_RELATION_STRESS_SUMCHECK_OFFSET + round * SUMCHECK_COEFFICIENTS * QM31_BYTES;
        let sumcheck_end = sumcheck_start + SUMCHECK_COEFFICIENTS * QM31_BYTES;
        absorb_real_v5_relation_sumcheck(
            &mut transcript,
            round,
            &parsed.v5_relation_stress[sumcheck_start..sumcheck_end],
        );
        let nonce = parsed.v5_fold_nonces[round];
        check_and_absorb_real_v5_fold_nonce(&mut transcript, round, nonce)?;
        let alpha = transcript
            .challenge_qm31()
            .map_err(|_| ProgramError::InvalidAccountData)?;
        if decode_qm31(parsed.relation_alphas, round)? != alpha {
            return Err(ProgramError::InvalidAccountData);
        }
        if round < parsed.v5_private_roots.later.len() {
            absorb_real_v5_round_root(
                &mut transcript,
                round + 1,
                &parsed.v5_private_roots.later[round],
                v5_public_fs_salt(parsed.v5_wire_prefix, round + 2),
            );
        }
    }
    Ok(transcript)
}

fn context_statement_and_digest(
    hash: HashFn,
    parsed: &ParsedProbeData<'_>,
) -> Result<(AtomicPaymentStatementV4, [u8; 32]), ProgramError> {
    let (statement, _) =
        decode_v5_atomic_terminal_context(parsed.v5_atomic_terminal_context, QM31::ONE)
            .map_err(|_| ProgramError::InvalidAccountData)?;
    let digest = atomic_payment_statement_digest_v4(&statement, hash)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    Ok((statement, digest))
}

/// Replay the exact real-witness transcript through all four relation rounds,
/// stopping immediately before the final polynomial is absorbed.
pub fn v5_complete_transcript_before_final(
    hash: HashFn,
    account_data: &[u8],
) -> Result<Transcript, ProgramError> {
    let parsed = parse_probe_data(account_data)?;
    let (statement, digest) = context_statement_and_digest(hash, &parsed)?;
    let (_, transcript) = verify_v5_wire_prefix(&parsed, &statement, &digest, hash)?;
    replay_real_v5_relation_rounds(transcript, &parsed)
}

pub fn v5_complete_transcript_before_final_with_statement_digest(
    hash: HashFn,
    account_data: &[u8],
    statement_digest: &[u8; 32],
) -> Result<Transcript, ProgramError> {
    let parsed = parse_probe_data(account_data)?;
    let (statement, context_digest) = context_statement_and_digest(hash, &parsed)?;
    if &context_digest != statement_digest {
        return Err(ProgramError::InvalidAccountData);
    }
    let (_, transcript) = verify_v5_wire_prefix(&parsed, &statement, statement_digest, hash)?;
    replay_real_v5_relation_rounds(transcript, &parsed)
}

fn derive_v5_complete_queries_from_transcript(
    transcript: Transcript,
    parsed: &ParsedProbeData<'_>,
) -> Result<([QM31; 4], [u32; V5_CU_PROBE_QUERY_COUNT]), ProgramError> {
    derive_v5_complete_queries_for_selector_from_transcript(
        transcript,
        parsed,
        parsed.v5_query_selector,
    )
}

fn derive_v5_complete_queries_for_selector_from_transcript(
    mut transcript: Transcript,
    parsed: &ParsedProbeData<'_>,
    selector: u8,
) -> Result<([QM31; 4], [u32; V5_CU_PROBE_QUERY_COUNT]), ProgramError> {
    let stress_final = &parsed.v5_relation_stress
        [V5_RELATION_STRESS_FINAL_OFFSET..V5_RELATION_STRESS_FINAL_OFFSET + 4 * QM31_BYTES];
    if stress_final != parsed.v5_final_coefficients || !v5_query_selector_is_valid(selector) {
        return Err(ProgramError::InvalidAccountData);
    }
    let mut final_polynomial = [QM31::ZERO; 4];
    for (index, value) in final_polynomial.iter_mut().enumerate() {
        *value = decode_qm31(parsed.v5_final_coefficients, index)?;
    }
    transcript.absorb(
        label::M31_CIRCLE_FINAL_TENSOR_POLY,
        parsed.v5_final_coefficients,
    );
    check_and_absorb_real_v5_final_nonce(&mut transcript, parsed.v5_final_nonce)?;
    transcript.absorb(label::M31_STATE_ONLY_QUERY_CANDIDATE, &[selector]);
    let queries: [u32; V5_CU_PROBE_QUERY_COUNT] = transcript
        .challenge_queries_without_replacement(
            V5_CU_PROBE_QUERY_COUNT,
            1 << 17,
            PAYMENT_HIDING_QUERY_DRAW_LIMIT,
        )
        .map_err(|_| ProgramError::InvalidAccountData)?
        .try_into()
        .map_err(|_| ProgramError::InvalidAccountData)?;
    Ok((final_polynomial, queries))
}

/// Derive and evaluate exactly the serialized public candidate. Verifier
/// acceptance is the selected-good relation: the selector is in range and its
/// public schedule is good. Other candidates belong only to the honest
/// prover's least-good policy and do not participate in verifier acceptance.
#[inline(always)]
fn v5_query_selector_is_valid(selected: u8) -> bool {
    selected < 3
}

fn checked_v5_selected_good_candidate<T: Copy>(
    selected: u8,
    mut derive: impl FnMut(u8) -> Result<T, ProgramError>,
    mut evaluate: impl FnMut(u8, &T) -> Result<bool, ProgramError>,
) -> Result<T, ProgramError> {
    if !v5_query_selector_is_valid(selected) {
        return Err(ProgramError::InvalidAccountData);
    }
    let candidate = derive(selected)?;
    if !evaluate(selected, &candidate)? {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(candidate)
}

/// Reconstruct the serialized q18 schedule branch from the pre-selector
/// transcript and evaluate GoodA/GoodB on that branch. The selected schedule
/// is returned so the PCS verifier consumes it without sampling a second time.
/// Honest prover leastness is not a verifier premise.
fn derive_v5_selected_good_queries_from_transcript(
    transcript: Transcript,
    parsed: &ParsedProbeData<'_>,
    point: &[QM31; V5_CU_PROBE_RELATION_LOG_ROWS as usize],
) -> Result<([QM31; 4], [u32; V5_CU_PROBE_QUERY_COUNT]), ProgramError> {
    let selected = parsed.v5_query_selector;
    checked_v5_selected_good_candidate(
        selected,
        |candidate| {
            derive_v5_complete_queries_for_selector_from_transcript(
                transcript.clone(),
                parsed,
                candidate,
            )
        },
        |_candidate, output| {
            let queries = output.1;
            good_gate_probe::candidate_is_good(point, queries)
                .ok_or(ProgramError::InvalidAccountData)
        },
    )
}

fn derive_v5_complete_queries(
    hash: HashFn,
    account_data: &[u8],
    parsed: &ParsedProbeData<'_>,
) -> Result<([QM31; 4], [u32; V5_CU_PROBE_QUERY_COUNT]), ProgramError> {
    derive_v5_complete_queries_from_transcript(
        v5_complete_transcript_before_final(hash, account_data)?,
        parsed,
    )
}

fn derive_v5_complete_queries_with_statement_digest(
    hash: HashFn,
    account_data: &[u8],
    parsed: &ParsedProbeData<'_>,
    statement_digest: &[u8; 32],
) -> Result<([QM31; 4], [u32; V5_CU_PROBE_QUERY_COUNT]), ProgramError> {
    derive_v5_complete_queries_from_transcript(
        v5_complete_transcript_before_final_with_statement_digest(
            hash,
            account_data,
            statement_digest,
        )?,
        parsed,
    )
}

pub fn v5_complete_queries(
    hash: HashFn,
    account_data: &[u8],
) -> Result<[u32; V5_CU_PROBE_QUERY_COUNT], ProgramError> {
    let parsed = parse_probe_data(account_data)?;
    derive_v5_complete_queries(hash, account_data, &parsed).map(|(_, queries)| queries)
}

pub fn v5_complete_queries_with_statement_digest(
    hash: HashFn,
    account_data: &[u8],
    statement_digest: &[u8; 32],
) -> Result<[u32; V5_CU_PROBE_QUERY_COUNT], ProgramError> {
    let parsed = parse_probe_data(account_data)?;
    derive_v5_complete_queries_with_statement_digest(hash, account_data, &parsed, statement_digest)
        .map(|(_, queries)| queries)
}

/// Host-side correspondence hook: replay the actual verifier transcript once
/// and return the exact fixed matrices/determinants for all three selector
/// branches. The matrix arithmetic is the same function linked into SBF.
#[cfg(not(target_os = "solana"))]
pub fn v5_good_gate_evaluations(
    hash: HashFn,
    account_data: &[u8],
) -> Result<[good_gate_probe::GoodGateEvaluation; 3], ProgramError> {
    let parsed = parse_probe_data(account_data)?;
    let (verified_prefix, prefix_transcript) = verify_v5_wire_prefix_from_context(&parsed, hash)?;
    let relation_transcript = replay_real_v5_relation_rounds(prefix_transcript, &parsed)?;
    let evaluate = |selector| {
        let (_, queries) = derive_v5_complete_queries_for_selector_from_transcript(
            relation_transcript.clone(),
            &parsed,
            selector,
        )?;
        good_gate_probe::evaluate_candidate(&verified_prefix.round_challenges, queries)
            .ok_or(ProgramError::InvalidAccountData)
    };
    Ok([evaluate(0)?, evaluate(1)?, evaluate(2)?])
}

#[derive(Clone, Copy)]
struct GenericPrepared<const C1_COLUMNS: usize> {
    c1_weight_limbs: [[u32; 4]; C1_COLUMNS],
    helpers: [PreparedQm31Multiplier; V5_CU_PROBE_C2_COLUMNS],
}

fn prepare_generic26(gamma: QM31) -> GenericPrepared<V5_CU_PROBE_PRODUCTION_C1_COLUMNS> {
    let powers = qm31_power_table::<29>(gamma);
    GenericPrepared {
        c1_weight_limbs: core::array::from_fn(|index| {
            let weight = powers[index];
            [weight.c0.a.0, weight.c0.b.0, weight.c1.a.0, weight.c1.b.0]
        }),
        helpers: core::array::from_fn(|index| {
            PreparedQm31Multiplier::new(powers[V5_CU_PROBE_PRODUCTION_C1_COLUMNS + index])
        }),
    }
}

fn prepare_generic16(gamma: QM31) -> GenericPrepared<V5_CU_PROBE_CANDIDATE_C1_COLUMNS> {
    let powers = qm31_power_table::<19>(gamma);
    GenericPrepared {
        c1_weight_limbs: core::array::from_fn(|index| {
            let weight = powers[index];
            [weight.c0.a.0, weight.c0.b.0, weight.c1.a.0, weight.c1.b.0]
        }),
        helpers: core::array::from_fn(|index| {
            PreparedQm31Multiplier::new(powers[V5_CU_PROBE_CANDIDATE_C1_COLUMNS + index])
        }),
    }
}

enum PreparedMode {
    Production26(StateOnlySpendQueryPowers),
    Generic26Nonfused(GenericPrepared<V5_CU_PROBE_PRODUCTION_C1_COLUMNS>),
    Generic16Nonfused(GenericPrepared<V5_CU_PROBE_CANDIDATE_C1_COLUMNS>),
    Generic16Fused(GenericPrepared<V5_CU_PROBE_CANDIDATE_C1_COLUMNS>),
    Generic26Fused(GenericPrepared<V5_CU_PROBE_PRODUCTION_C1_COLUMNS>),
    Relation3(PreparedRelation),
    Relation4Dense(PreparedRelation),
    Relation4StandaloneDot(PreparedRelation),
    Relation4Compact(PreparedRelation),
}

struct PreparedRelation {
    weights: WeightAccumulator,
    relation_value: QM31,
    alphas: [QM31; V5_CU_PROBE_RELATION_FOLDS],
    final_values: [QM31; V5_CU_PROBE_RELATION_FINAL_VALUES],
    extra_work: RelationExtraWork,
}

enum RelationExtraWork {
    None,
    Compact(CompactBTerminalWeights),
    StandaloneDot {
        covector: Vec<QM31>,
        pivot: usize,
        lane_value: QM31,
    },
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum RelationVariant {
    ThreeClaims,
    FourClaimsSharedFold,
    FourClaimsStandaloneDot,
    FourClaimsCompact,
}

fn relation_variant(mode: u8) -> Option<RelationVariant> {
    match mode {
        V5_CU_PROBE_RELATION3_MODE => Some(RelationVariant::ThreeClaims),
        V5_CU_PROBE_RELATION4_DENSE_MODE => Some(RelationVariant::FourClaimsSharedFold),
        V5_CU_PROBE_RELATION4_STANDALONE_DOT_MODE => Some(RelationVariant::FourClaimsStandaloneDot),
        V5_CU_PROBE_RELATION4_COMPACT_MODE => Some(RelationVariant::FourClaimsCompact),
        _ => None,
    }
}

fn decode_qm31(bytes: &[u8], index: usize) -> Result<QM31, ProgramError> {
    let start = index
        .checked_mul(QM31_BYTES)
        .ok_or(ProgramError::InvalidAccountData)?;
    QM31::from_le_bytes(
        bytes
            .get(start..start + QM31_BYTES)
            .ok_or(ProgramError::InvalidAccountData)?,
    )
    .ok_or(ProgramError::InvalidAccountData)
}

// Historical transcript-domain bytes retained byte-for-byte with the host.
// `AV5PFX03` and its explicit version gate the wire grammar; changing this
// literal intentionally forks the Fiat--Shamir schedule.
const V5_REAL_HOST_TRANSCRIPT_DOMAIN: &[u8] = b"aspis-v5-real-witness-cu-v1";

#[derive(Clone, Copy)]
struct VerifiedRealV5Wire {
    eta: QM31,
    round_challenges: [QM31; V5_CU_PROBE_RELATION_LOG_ROWS as usize],
    gamma: QM31,
    kappa: QM31,
    terminal_real: QM31,
    terminal_mask: QM31,
    terminal_masked: QM31,
    inactive_claim: QM31,
}

fn decode_prefix_qm31(prefix: &[u8], offset: usize) -> Result<QM31, ProgramError> {
    QM31::from_le_bytes(
        prefix
            .get(offset..offset + QM31_BYTES)
            .ok_or(ProgramError::InvalidAccountData)?,
    )
    .ok_or(ProgramError::InvalidAccountData)
}

fn encode_relation_points(
    point: &[QM31; V5_CU_PROBE_RELATION_LOG_ROWS as usize],
) -> [u8; V5_CU_PROBE_RELATION_POINTS * V5_CU_PROBE_RELATION_LOG_ROWS as usize * QM31_BYTES] {
    let points = [
        *point,
        v5_binary_successor_point(point),
        v5_xor12_point(point),
    ];
    let mut bytes =
        [0u8; V5_CU_PROBE_RELATION_POINTS * V5_CU_PROBE_RELATION_LOG_ROWS as usize * QM31_BYTES];
    for (point_index, coordinates) in points.iter().enumerate() {
        for (coordinate, value) in coordinates.iter().enumerate() {
            let start =
                (point_index * V5_CU_PROBE_RELATION_LOG_ROWS as usize + coordinate) * QM31_BYTES;
            value.write_le_bytes(&mut bytes[start..start + QM31_BYTES]);
        }
    }
    bytes
}

/// Polynomial binary increment under the deployed big-endian MLE convention.
/// Kept local because the host trace builder is intentionally not exported to
/// the Solana target.
fn v5_binary_successor_point(point: &[QM31; 10]) -> [QM31; 10] {
    let mut successor = [QM31::ZERO; 10];
    let mut carry = QM31::ONE;
    for coordinate in (0..point.len()).rev() {
        let value = point[coordinate];
        let value_times_carry = value.mul(carry);
        successor[coordinate] = value
            .add(carry)
            .sub(value_times_carry.add(value_times_carry));
        carry = value_times_carry;
    }
    successor
}

/// Toggle row-index bits two and three (`12 = 0b1100`) under the same MLE
/// convention as the host trace builder.
fn v5_xor12_point(point: &[QM31; 10]) -> [QM31; 10] {
    let mut shifted = *point;
    for bit in [2usize, 3] {
        let coordinate = point.len() - 1 - bit;
        shifted[coordinate] = QM31::ONE.sub(shifted[coordinate]);
    }
    shifted
}

fn v5_public_fs_salt(
    prefix: &[u8],
    section: usize,
) -> &[u8; V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_BYTES] {
    let start =
        V5_CU_REAL_PREFIX_PUBLIC_FS_SALTS_OFFSET + section * V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_BYTES;
    match prefix[start..start + V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_BYTES].try_into() {
        Ok(salt) => salt,
        Err(_) => panic!("invalid v5 public Fiat-Shamir salt bounds"),
    }
}

#[inline(always)]
fn real_v5_prefix_root(prefix: &[u8], start: usize) -> &[u8; 32] {
    match prefix[start..start + 32].try_into() {
        Ok(root) => root,
        Err(_) => panic!("invalid v5 root bounds"),
    }
}

#[inline(always)]
fn real_v5_round_root_record(
    layer: usize,
    root: &[u8; 32],
    public_fs_salt: &[u8; V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_BYTES],
) -> [u8; 65] {
    let mut record = [0u8; 65];
    record[0] = layer as u8;
    record[1..33].copy_from_slice(root);
    record[33..].copy_from_slice(public_fs_salt);
    record
}

#[inline(always)]
fn real_v5_c2_root_record(
    root: &[u8; 32],
    public_fs_salt: &[u8; V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_BYTES],
) -> [u8; 64] {
    let mut record = [0u8; 64];
    record[..32].copy_from_slice(root);
    record[32..].copy_from_slice(public_fs_salt);
    record
}

#[inline(always)]
fn real_v5_round_root_absorb_input(
    layer: usize,
    root: &[u8; 32],
    public_fs_salt: &[u8; V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_BYTES],
) -> (u8, [u8; 65]) {
    (
        label::M31_CIRCLE_ROUND_ROOT,
        real_v5_round_root_record(layer, root, public_fs_salt),
    )
}

#[inline(always)]
fn real_v5_c2_root_absorb_input(
    root: &[u8; 32],
    public_fs_salt: &[u8; V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_BYTES],
) -> (u8, [u8; 64]) {
    (
        label::M31_CIRCLE_C2_ROOT,
        real_v5_c2_root_record(root, public_fs_salt),
    )
}

fn absorb_real_v5_round_root(
    transcript: &mut Transcript,
    layer: usize,
    root: &[u8; 32],
    public_fs_salt: &[u8; V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_BYTES],
) {
    let (label, record) = real_v5_round_root_absorb_input(layer, root, public_fs_salt);
    transcript.absorb(label, &record);
}

fn absorb_real_v5_c2_root(
    transcript: &mut Transcript,
    root: &[u8; 32],
    public_fs_salt: &[u8; V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_BYTES],
) {
    let (label, record) = real_v5_c2_root_absorb_input(root, public_fs_salt);
    transcript.absorb(label, &record);
}

#[inline(always)]
fn verify_live_statement_digest(
    live_statement: &AtomicPaymentStatementV4,
    statement_digest: &[u8; 32],
    hash: HashFn,
) -> ProgramResult {
    let expected_digest = atomic_payment_statement_digest_v4(live_statement, hash)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    if &expected_digest != statement_digest {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}

#[inline(always)]
fn v5_reserved_tail_is_zero(bytes: &[u8]) -> bool {
    if bytes.len() != V5_CU_REAL_PREFIX_ZERO_TAIL_BYTES {
        return false;
    }
    let mut offset = 0;
    while offset < V5_CU_REAL_PREFIX_ZERO_TAIL_BYTES {
        let word = u64::from_le_bytes([
            bytes[offset],
            bytes[offset + 1],
            bytes[offset + 2],
            bytes[offset + 3],
            bytes[offset + 4],
            bytes[offset + 5],
            bytes[offset + 6],
            bytes[offset + 7],
        ]);
        if word != 0 {
            return false;
        }
        offset += 8;
    }
    true
}

#[inline(always)]
fn verify_v5_reserved_tail(bytes: &[u8]) -> ProgramResult {
    if !v5_reserved_tail_is_zero(bytes) {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}

/// Pure structural predicate for the fixed v5 prefix header.  Keeping this
/// separate from transcript replay makes the exact accepted byte grammar
/// available to source extraction without changing the production check.
#[inline(always)]
fn v5_wire_prefix_header_is_valid(prefix: &[u8]) -> bool {
    prefix.len() == V5_CU_REAL_PREFIX_ACCEPTED_BYTES
        && prefix[0] == V5_CU_REAL_PREFIX_MAGIC[0]
        && prefix[1] == V5_CU_REAL_PREFIX_MAGIC[1]
        && prefix[2] == V5_CU_REAL_PREFIX_MAGIC[2]
        && prefix[3] == V5_CU_REAL_PREFIX_MAGIC[3]
        && prefix[4] == V5_CU_REAL_PREFIX_MAGIC[4]
        && prefix[5] == V5_CU_REAL_PREFIX_MAGIC[5]
        && prefix[6] == V5_CU_REAL_PREFIX_MAGIC[6]
        && prefix[7] == V5_CU_REAL_PREFIX_MAGIC[7]
        && prefix[8] == V5_CU_REAL_PREFIX_VERSION
        && prefix[9] == 0
        && prefix[10] == 0
        && prefix[11] == 1
        && prefix[12] == 192
        && prefix[13] == 0
        && prefix[14] == 16
        && prefix[15] == 3
        && prefix[16] == 1
        && prefix[17] == 2
        && prefix[18] == 3
        && prefix[19] == 10
        && prefix[20] == 27
        && prefix[21] == 4
        && prefix[22] == 0
}

#[inline(never)]
fn verify_v5_wire_prefix(
    parsed: &ParsedProbeData<'_>,
    live_statement: &AtomicPaymentStatementV4,
    statement_digest: &[u8; 32],
    hash: HashFn,
) -> Result<(VerifiedRealV5Wire, Transcript), ProgramError> {
    let prefix = parsed.v5_wire_prefix;
    if !v5_wire_prefix_header_is_valid(prefix) {
        return Err(ProgramError::InvalidAccountData);
    }
    // The five public FS salts occupy the first 160 bytes of the old reserve.
    // This remaining tail is exactly 400 bytes. Checking its 50 safely decoded words
    // preserves the byte-for-byte all-zero predicate while avoiding a
    // verifier loop over every individual reserved byte.
    verify_v5_reserved_tail(&prefix[V5_CU_REAL_PREFIX_ZERO_RESERVE_OFFSET..])?;

    if !v5_prefix_roots_match_private(prefix, &parsed.v5_private_roots) {
        return Err(ProgramError::InvalidAccountData);
    }
    let c1_root = &parsed.v5_private_roots.c1;
    let c2_root = &parsed.v5_private_roots.c2;

    verify_live_statement_digest(live_statement, statement_digest, hash)?;

    let mut transcript = Transcript::new(hash);
    transcript.absorb(label::PROFILE, V5_REAL_HOST_TRANSCRIPT_DOMAIN);
    transcript.absorb(label::M31_CIRCLE_BASIS, M31_CIRCLE_BASIS_DISCRIMINATOR);
    transcript.absorb(label::STATEMENT, statement_digest);
    absorb_real_v5_round_root(&mut transcript, 0, c1_root, v5_public_fs_salt(prefix, 0));
    let lambda = transcript
        .challenge_qm31()
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let chi = transcript
        .challenge_qm31()
        .map_err(|_| ProgramError::InvalidAccountData)?;
    absorb_real_v5_c2_root(&mut transcript, c2_root, v5_public_fs_salt(prefix, 1));
    let batching = begin_state_only_zerocheck(&mut transcript)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let initial_claim = decode_prefix_qm31(prefix, V5_CU_REAL_PREFIX_INITIAL_B_CLAIM_OFFSET)?;
    let eta = begin_state_only_masked_sumcheck(&mut transcript, initial_claim)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let semantic = verify_state_only_sumcheck_streaming(
        &mut transcript,
        &prefix[V5_CU_REAL_PREFIX_SUMCHECK_OFFSET..V5_CU_REAL_PREFIX_CLAIMS_OFFSET],
        initial_claim,
    )
    .map_err(|_| ProgramError::InvalidAccountData)?;

    let expected_points = encode_relation_points(&semantic.point);
    if parsed.relation_points != expected_points
        || &prefix[V5_CU_REAL_PREFIX_CLAIMS_OFFSET..V5_CU_REAL_PREFIX_TERMINAL_OFFSET]
            != parsed.relation_claims
    {
        return Err(ProgramError::InvalidAccountData);
    }
    transcript.absorb(label::M31_CIRCLE_STATEMENT_POINTS, parsed.relation_points);
    transcript.absorb(
        label::M31_CIRCLE_STATEMENT_EVALUATIONS,
        parsed.relation_claims,
    );

    let terminal_real = decode_prefix_qm31(prefix, V5_CU_REAL_PREFIX_TERMINAL_OFFSET)?;
    let terminal_mask = decode_prefix_qm31(prefix, V5_CU_REAL_PREFIX_TERMINAL_OFFSET + QM31_BYTES)?;
    let terminal_masked =
        decode_prefix_qm31(prefix, V5_CU_REAL_PREFIX_TERMINAL_OFFSET + 2 * QM31_BYTES)?;
    if terminal_masked != semantic.terminal_claim {
        return Err(ProgramError::InvalidAccountData);
    }
    transcript.absorb(
        label::CLAIM,
        &prefix[V5_CU_REAL_PREFIX_TERMINAL_OFFSET..V5_CU_REAL_PREFIX_INACTIVE_CLAIM_OFFSET],
    );
    check_and_absorb_real_v5_batch_nonce(&mut transcript, parsed.v5_batch_nonce)?;
    let gamma = transcript
        .challenge_nonzero_qm31()
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let inactive_claim = decode_prefix_qm31(prefix, V5_CU_REAL_PREFIX_INACTIVE_CLAIM_OFFSET)?;
    transcript.absorb(
        label::SECOND_PHASE_CLAIM,
        &prefix[V5_CU_REAL_PREFIX_INACTIVE_CLAIM_OFFSET..V5_CU_REAL_PREFIX_RESERVED_OFFSET],
    );
    let kappa = transcript
        .challenge_nonzero_qm31()
        .map_err(|_| ProgramError::InvalidAccountData)?;
    if parsed.gamma != gamma
        || decode_qm31(parsed.relation_scales, 0)? != QM31::ONE
        || decode_qm31(parsed.relation_scales, 1)? != kappa
        || decode_qm31(parsed.relation_scales, 2)? != kappa.square()
    {
        return Err(ProgramError::InvalidAccountData);
    }

    let (context_statement, context) =
        decode_v5_atomic_terminal_context(parsed.v5_atomic_terminal_context, eta)
            .map_err(|_| ProgramError::InvalidAccountData)?;
    let expected_context = V5AtomicTerminalChallenges {
        lambda,
        chi,
        theta: batching.theta,
        zerocheck_point: batching.zerocheck_point,
        mu: batching.mu,
        eta,
    };
    if &context_statement != live_statement || context != expected_context {
        return Err(ProgramError::InvalidAccountData);
    }

    Ok((
        VerifiedRealV5Wire {
            eta,
            round_challenges: semantic.point,
            gamma,
            kappa,
            terminal_real,
            terminal_mask,
            terminal_masked,
            inactive_claim,
        },
        transcript,
    ))
}

fn verify_v5_wire_prefix_from_context(
    parsed: &ParsedProbeData<'_>,
    hash: HashFn,
) -> Result<(VerifiedRealV5Wire, Transcript), ProgramError> {
    let (statement, digest) = context_statement_and_digest(hash, parsed)?;
    verify_v5_wire_prefix(parsed, &statement, &digest, hash)
}

/// Check the real atomic-v3 semantic terminal against the v5 authenticated
/// point/claim tables carried by the isolated mode-9 account.
///
/// The context region is a host fixture encoding, not an authority: its
/// statement must exactly equal the live statement constructed by the atomic
/// state wrapper, `eta` comes from the verified pre-challenge prefix, and the
/// terminal evaluation point must equal the ten verified B-round challenges.
fn verify_mode9_atomic_terminal_parsed(
    parsed: &ParsedProbeData<'_>,
    live_statement: &AtomicPaymentStatementV4,
    statement_digest: &[u8; 32],
) -> Result<VerifiedV5AtomicTerminal, ProgramError> {
    let (verified_prefix, _) = verify_v5_wire_prefix(
        parsed,
        live_statement,
        statement_digest,
        crate::verify::sbf_hashv,
    )?;
    verify_mode9_atomic_terminal_with_prefix(parsed, live_statement, &verified_prefix)
}

fn verify_mode9_atomic_terminal_with_prefix(
    parsed: &ParsedProbeData<'_>,
    live_statement: &AtomicPaymentStatementV4,
    verified_prefix: &VerifiedRealV5Wire,
) -> Result<VerifiedV5AtomicTerminal, ProgramError> {
    let (_, challenges) =
        decode_v5_atomic_terminal_context(parsed.v5_atomic_terminal_context, verified_prefix.eta)
            .map_err(|_| ProgramError::InvalidAccountData)?;

    verify_v5_atomic_terminal_from_bytes(
        live_statement,
        parsed.relation_points,
        parsed.relation_claims,
        &challenges,
        V5AtomicTerminalClaims {
            real: verified_prefix.terminal_real,
            mask: verified_prefix.terminal_mask,
            masked: verified_prefix.terminal_masked,
        },
    )
    .map_err(|_| ProgramError::InvalidAccountData)
}

/// Account-backed seam used by the local atomic state-transition wrapper.
/// This parses the exact mode-9 artifact and never trusts a proof-carried
/// duplicate of the live pool statement.
pub fn verify_mode9_atomic_terminal(
    account_data: &[u8],
    live_statement: &AtomicPaymentStatementV4,
) -> Result<VerifiedV5AtomicTerminal, ProgramError> {
    let parsed = parse_probe_data(account_data)?;
    let statement_digest =
        atomic_payment_statement_digest_v4(live_statement, crate::verify::sbf_hashv)
            .map_err(|_| ProgramError::InvalidAccountData)?;
    verify_mode9_atomic_terminal_parsed(&parsed, live_statement, &statement_digest)
}

fn prepare_relation_base_with_kappa_inner(
    parsed: &ParsedProbeData<'_>,
    variant: RelationVariant,
    kappa: QM31,
    inactive_claim: QM31,
    prepared_claims: Option<&V5PreparedPcsClaims>,
) -> Result<
    (
        PreparedRelation,
        [QM31; V5_CU_PROBE_RELATION_LOG_ROWS as usize],
        QM31,
    ),
    ProgramError,
> {
    let lane_powers = prepared_claims
        .is_none()
        .then(|| qm31_power_table::<V5_CU_PROBE_RELATION_LANES>(parsed.gamma));
    let mut weights = WeightAccumulator::empty(V5_CU_PROBE_RELATION_LOG_ROWS);
    let mut relation_value = inactive_claim;
    let mut terminal_point = [QM31::ZERO; V5_CU_PROBE_RELATION_LOG_ROWS as usize];
    let kappa2 = kappa.square();
    let point_scales = [QM31::ONE, kappa, kappa2];

    for point in 0..V5_CU_PROBE_RELATION_POINTS {
        let scale = point_scales[point];
        let coordinates = (0..V5_CU_PROBE_RELATION_LOG_ROWS as usize)
            .map(|coordinate| {
                decode_qm31(
                    parsed.relation_points,
                    point * V5_CU_PROBE_RELATION_LOG_ROWS as usize + coordinate,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        if point == 0 {
            terminal_point.copy_from_slice(&coordinates);
        }
        weights
            .add_multilinear(scale, coordinates)
            .map_err(|_| ProgramError::InvalidAccountData)?;
        let claim = if let Some(prepared) = prepared_claims {
            prepared.point_claims()[point]
        } else {
            let lane_powers = lane_powers
                .as_ref()
                .expect("literal relation path prepares gamma powers");
            (0..V5_CU_PROBE_RELATION_LANES).try_fold(
                QM31::ZERO,
                |sum, lane| -> Result<QM31, ProgramError> {
                    let value = decode_qm31(
                        parsed.relation_claims,
                        point * V5_CU_PROBE_RELATION_LANES + lane,
                    )?;
                    Ok(sum.add(lane_powers[lane].mul(value)))
                },
            )?
        };
        relation_value = relation_value.add(scale.mul(claim));
    }

    let dense_scale = if variant != RelationVariant::ThreeClaims {
        let kappa3 = kappa2.mul(kappa);
        let dense_claim = if let Some(prepared) = prepared_claims {
            prepared.point_claims()[V5_CU_PROBE_RELATION_POINTS]
        } else {
            let lane_powers = lane_powers
                .as_ref()
                .expect("literal relation path prepares gamma powers");
            (0..V5_CU_PROBE_RELATION_LANES).try_fold(
                QM31::ZERO,
                |sum, lane| -> Result<QM31, ProgramError> {
                    let value = decode_qm31(
                        parsed.relation_claims,
                        V5_CU_PROBE_RELATION_POINTS * V5_CU_PROBE_RELATION_LANES + lane,
                    )?;
                    Ok(sum.add(lane_powers[lane].mul(value)))
                },
            )?
        };
        relation_value = relation_value.add(kappa3.mul(dense_claim));
        kappa3
    } else {
        QM31::ZERO
    };

    weights
        .add_grouped_64x16_binary_masks_deferred_prepared(
            &V5_ATOMIC_V3_INACTIVE_ROW_GROUPS,
            &V5_ATOMIC_V3_INACTIVE_GROUP_MASKS,
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;

    let alphas = core::array::from_fn(|index| {
        decode_qm31(parsed.relation_alphas, index).unwrap_or(QM31::ZERO)
    });
    let real_prefix = parsed.v5_wire_prefix.get(..8) == Some(&V5_CU_REAL_PREFIX_MAGIC);
    let final_values = core::array::from_fn(|index| {
        decode_qm31(
            if real_prefix {
                parsed.v5_final_coefficients
            } else {
                parsed.relation_final
            },
            index,
        )
        .unwrap_or(QM31::ZERO)
    });
    if !real_prefix && (alphas.contains(&QM31::ZERO) || final_values.contains(&QM31::ZERO)) {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok((
        PreparedRelation {
            weights,
            relation_value,
            alphas,
            final_values,
            extra_work: RelationExtraWork::None,
        },
        terminal_point,
        dense_scale,
    ))
}

fn prepare_relation_base_with_kappa(
    parsed: &ParsedProbeData<'_>,
    variant: RelationVariant,
    kappa: QM31,
    inactive_claim: QM31,
) -> Result<
    (
        PreparedRelation,
        [QM31; V5_CU_PROBE_RELATION_LOG_ROWS as usize],
        QM31,
    ),
    ProgramError,
> {
    prepare_relation_base_with_kappa_inner(parsed, variant, kappa, inactive_claim, None)
}

fn prepare_relation_base_with_kappa_prepared(
    parsed: &ParsedProbeData<'_>,
    variant: RelationVariant,
    kappa: QM31,
    inactive_claim: QM31,
    prepared_claims: &V5PreparedPcsClaims,
) -> Result<
    (
        PreparedRelation,
        [QM31; V5_CU_PROBE_RELATION_LOG_ROWS as usize],
        QM31,
    ),
    ProgramError,
> {
    prepare_relation_base_with_kappa_inner(
        parsed,
        variant,
        kappa,
        inactive_claim,
        Some(prepared_claims),
    )
}

fn prepare_relation_base(
    parsed: &ParsedProbeData<'_>,
    variant: RelationVariant,
) -> Result<
    (
        PreparedRelation,
        [QM31; V5_CU_PROBE_RELATION_LOG_ROWS as usize],
        QM31,
    ),
    ProgramError,
> {
    prepare_relation_base_with_kappa(
        parsed,
        variant,
        decode_qm31(parsed.relation_scales, 0)?,
        QM31::ZERO,
    )
}

fn copy_inactive_row(masks: &[u16; 64], row: usize) -> bool {
    masks[row >> 4] & (1 << (row & 15)) != 0
}

fn v5_b_pivot_row() -> usize {
    let masks = atomic_state_only_copy_inactive_row_masks_v3();
    (0..V5_CU_PROBE_RELATION_DENSE_VALUES)
        .find(|&row| copy_inactive_row(&masks, row))
        .expect("the pinned copy-inactive functional is nonzero")
}

fn free_coordinate_row(coordinate: usize, pivot: usize) -> usize {
    debug_assert!(coordinate < V5_CU_PROBE_RELATION_DENSE_VALUES - 1);
    if coordinate < pivot {
        coordinate
    } else {
        coordinate + 1
    }
}

/// Exact on-chain spelling of the rejected free-coordinate control covector.
///
/// This path is intentionally unreachable from the compact candidate and the
/// composite mode.  Only modes 6 and 7 may pay for/materialise it.
fn derive_v5_b_terminal_covector(
    mode: u8,
    point: &[QM31; V5_CU_PROBE_RELATION_LOG_ROWS as usize],
    scale: QM31,
) -> Result<(Vec<QM31>, usize), ProgramError> {
    if !matches!(
        mode,
        V5_CU_PROBE_RELATION4_DENSE_MODE | V5_CU_PROBE_RELATION4_STANDALONE_DOT_MODE
    ) {
        return Err(ProgramError::InvalidInstructionData);
    }
    const ROUNDS: usize = 10;
    const DEGREE: usize = 27;
    let pivot = v5_b_pivot_row();
    let half = QM31::ONE.half();
    // The host prototype uses a fixed array. The SBF stack is only 4 KiB, so
    // the executable spelling materialises the same 271 values on the heap.
    let mut coordinate_weights = vec![QM31::ZERO; V5_CU_PROBE_B_MASK_COORDINATES];
    coordinate_weights[0] = half.pow(ROUNDS as u64);
    for (round, challenge) in point.iter().copied().enumerate() {
        let later_round_scale = half.pow((ROUNDS - 1 - round) as u64);
        let mut challenge_power = challenge;
        for degree in 1..=DEGREE {
            let coordinate = 1 + round * DEGREE + degree - 1;
            coordinate_weights[coordinate] = later_round_scale.mul(challenge_power.sub(half));
            challenge_power = challenge_power.mul(challenge);
        }
    }
    let mut covector = vec![QM31::ZERO; V5_CU_PROBE_RELATION_DENSE_VALUES];
    for (coordinate, weight) in coordinate_weights.into_iter().enumerate() {
        covector[free_coordinate_row(coordinate, pivot)] = scale.mul(weight);
    }
    Ok((covector, pivot))
}

#[derive(Clone, Copy)]
struct CompactBTerminalBlock {
    scale: QM31,
    /// Before fold zero these are `z` and `z^2`; before fold one they are
    /// `z^4` and `z^8`; afterwards `power_lo` carries the folded upper half
    /// of the truncated degree block.
    power_lo: QM31,
    power_hi: QM31,
    /// High five bits of the row index. Each component occupies one aligned
    /// 32-row block before the zero fixed coefficients are imposed.
    selector: u8,
}

#[derive(Clone, Copy)]
struct CompactBTerminalWeights {
    blocks: [CompactBTerminalBlock; V5_CU_PROBE_B_STRUCTURED_BLOCKS],
    delta_scale: QM31,
    folds: u8,
}

pub const V5_CU_PROBE_B_COMPACT_STATE_BYTES: usize =
    core::mem::size_of::<CompactBTerminalWeights>();
pub const V5_CU_PROBE_B_COMPACT_DYNAMIC_HEAP_BYTES: usize = 0;

impl CompactBTerminalWeights {
    fn new(point: &[QM31; V5_CU_PROBE_RELATION_LOG_ROWS as usize], scale: QM31) -> Self {
        let mut block_scales = [QM31::ZERO; V5_CU_PROBE_B_STRUCTURED_BLOCKS];
        block_scales[V5_CU_PROBE_B_STRUCTURED_BLOCKS - 1] = scale;
        for round in (0..V5_CU_PROBE_B_STRUCTURED_BLOCKS - 1).rev() {
            block_scales[round] = block_scales[round + 1].half();
        }
        let blocks = core::array::from_fn(|component| {
            let z1 = point[component];
            CompactBTerminalBlock {
                scale: block_scales[component],
                power_lo: z1,
                power_hi: z1.square(),
                selector: V5_CU_PROBE_B_BLOCK_SELECTORS[component],
            }
        });
        Self {
            blocks,
            delta_scale: block_scales[0].half(),
            folds: 0,
        }
    }

    /// Apply one exact dual arity-four fold. The first two folds consume the
    /// five-bit degree, the third consumes degree bit four and selector bit
    /// zero, and the fourth consumes selector bits one and two.
    fn fold(&mut self, alpha: QM31) {
        debug_assert!(self.folds < V5_CU_PROBE_RELATION_FOLDS as u8);
        let alpha2 = alpha.square();
        let alpha3 = alpha2.mul(alpha);
        let prepared_powers = [
            PreparedQm31Multiplier::new(alpha3),
            PreparedQm31Multiplier::new(alpha2),
            PreparedQm31Multiplier::new(alpha),
        ];
        for block in &mut self.blocks {
            let factor = match self.folds {
                0 => {
                    let z1 = block.power_lo;
                    let z2 = block.power_hi;
                    let factor = QM31::ONE.add(qm31_sum_products3_prepared(
                        &prepared_powers,
                        &[z1, z2, z2.mul(z1)],
                    ));
                    block.power_lo = z2.square();
                    block.power_hi = block.power_lo.square();
                    factor
                }
                1 => {
                    let z4 = block.power_lo;
                    let z8 = block.power_hi;
                    let lower_factor = QM31::ONE
                        .add(qm31_sum_products3_prepared(
                            &prepared_powers,
                            &[z4, z8, z8.mul(z4)],
                        ))
                        .half()
                        .half();
                    let upper_factor = z8
                        .square()
                        .mul(QM31::ONE.add(qm31_sum_products2_prepared(
                            &[prepared_powers[0], prepared_powers[1]],
                            &[z4, z8],
                        )))
                        .half()
                        .half();
                    let common_scale = block.scale;
                    block.scale = common_scale.mul(lower_factor);
                    block.power_lo = common_scale.mul(upper_factor);
                    block.power_hi = QM31::ZERO;
                    continue;
                }
                2 => if block.selector & 1 == 0 {
                    block.scale.add(prepared_powers[0].mul(block.power_lo))
                } else {
                    qm31_sum_products2_prepared(
                        &[prepared_powers[1], prepared_powers[2]],
                        &[block.scale, block.power_lo],
                    )
                }
                .half()
                .half(),
                3 => match (block.selector >> 1) & 3 {
                    0 => QM31::ONE,
                    1 => alpha3,
                    2 => alpha2,
                    3 => alpha,
                    _ => unreachable!(),
                },
                _ => unreachable!(),
            };
            if self.folds == 2 {
                block.scale = factor;
                block.power_lo = QM31::ZERO;
            } else {
                block.scale = block.scale.mul(factor.half().half());
            }
        }
        let delta_factor = match self.folds {
            0 | 1 => QM31::ONE,
            2 => alpha2,
            3 => alpha,
            _ => unreachable!(),
        }
        .half()
        .half();
        self.delta_scale = self.delta_scale.mul(delta_factor);
        self.folds += 1;
    }

    fn final_weights(&self) -> [QM31; V5_CU_PROBE_RELATION_FINAL_VALUES] {
        debug_assert_eq!(self.folds, V5_CU_PROBE_RELATION_FOLDS as u8);
        let mut output = [QM31::ZERO; V5_CU_PROBE_RELATION_FINAL_VALUES];
        for block in self.blocks {
            let final_index = usize::from(block.selector >> 3);
            output[final_index] = output[final_index].add(block.scale);
        }
        output[V5_CU_PROBE_RELATION_FINAL_VALUES - 1] =
            output[V5_CU_PROBE_RELATION_FINAL_VALUES - 1].add(self.delta_scale);
        output
    }

    fn dot(&self, values: &[QM31; V5_CU_PROBE_RELATION_FINAL_VALUES]) -> QM31 {
        self.final_weights()
            .into_iter()
            .zip(values.iter().copied())
            .fold(QM31::ZERO, |sum, (weight, value)| {
                sum.add(weight.mul(value))
            })
    }
}

impl V5RelationStressAdditive for CompactBTerminalWeights {
    #[inline(always)]
    fn fold(&mut self, alpha: QM31) {
        CompactBTerminalWeights::fold(self, alpha);
    }

    #[inline(always)]
    fn dot(&self, final_coefficients: &[QM31; V5_CU_PROBE_RELATION_FINAL_VALUES]) -> QM31 {
        CompactBTerminalWeights::dot(self, final_coefficients)
    }
}

enum DerivedRelationOpening {
    None,
    Dense(Vec<QM31>, usize),
    Compact(CompactBTerminalWeights),
}

fn install_relation_covector(
    relation: &mut PreparedRelation,
    variant: RelationVariant,
    opening: DerivedRelationOpening,
) -> Result<(), ProgramError> {
    match (variant, opening) {
        (RelationVariant::ThreeClaims, DerivedRelationOpening::None) => {}
        (RelationVariant::FourClaimsSharedFold, DerivedRelationOpening::Dense(covector, _)) => {
            relation
                .weights
                .add_dense(covector)
                .map_err(|_| ProgramError::InvalidAccountData)?;
        }
        (
            RelationVariant::FourClaimsStandaloneDot,
            DerivedRelationOpening::Dense(covector, pivot),
        ) => {
            relation.extra_work = RelationExtraWork::StandaloneDot {
                covector,
                pivot,
                lane_value: relation.final_values[0],
            };
        }
        (RelationVariant::FourClaimsCompact, DerivedRelationOpening::Compact(compact)) => {
            relation.extra_work = RelationExtraWork::Compact(compact);
        }
        _ => return Err(ProgramError::InvalidAccountData),
    }
    Ok(())
}

fn prepare_relation(
    parsed: &ParsedProbeData<'_>,
    mode: u8,
    variant: RelationVariant,
) -> Result<PreparedRelation, ProgramError> {
    let (mut relation, terminal_point, dense_scale) = prepare_relation_base(parsed, variant)?;
    let opening = match variant {
        RelationVariant::ThreeClaims => DerivedRelationOpening::None,
        RelationVariant::FourClaimsSharedFold | RelationVariant::FourClaimsStandaloneDot => {
            let (covector, pivot) =
                derive_v5_b_terminal_covector(mode, &terminal_point, dense_scale)?;
            DerivedRelationOpening::Dense(covector, pivot)
        }
        RelationVariant::FourClaimsCompact => DerivedRelationOpening::Compact(
            CompactBTerminalWeights::new(&terminal_point, dense_scale),
        ),
    };
    install_relation_covector(&mut relation, variant, opening)?;
    Ok(relation)
}

fn prepare_mode(mode: u8, parsed: &ParsedProbeData<'_>) -> Result<PreparedMode, ProgramError> {
    match mode {
        V5_CU_PROBE_PRODUCTION26_MODE => Ok(PreparedMode::Production26(
            StateOnlySpendQueryPowers::new(parsed.gamma),
        )),
        V5_CU_PROBE_GENERIC26_NONFUSED_MODE => Ok(PreparedMode::Generic26Nonfused(
            prepare_generic26(parsed.gamma),
        )),
        V5_CU_PROBE_GENERIC16_NONFUSED_MODE => Ok(PreparedMode::Generic16Nonfused(
            prepare_generic16(parsed.gamma),
        )),
        V5_CU_PROBE_GENERIC16_FUSED_MODE => Ok(PreparedMode::Generic16Fused(prepare_generic16(
            parsed.gamma,
        ))),
        V5_CU_PROBE_GENERIC26_FUSED_MODE => Ok(PreparedMode::Generic26Fused(prepare_generic26(
            parsed.gamma,
        ))),
        V5_CU_PROBE_RELATION3_MODE => Ok(PreparedMode::Relation3(prepare_relation(
            parsed,
            mode,
            RelationVariant::ThreeClaims,
        )?)),
        V5_CU_PROBE_RELATION4_DENSE_MODE => Ok(PreparedMode::Relation4Dense(prepare_relation(
            parsed,
            mode,
            RelationVariant::FourClaimsSharedFold,
        )?)),
        V5_CU_PROBE_RELATION4_STANDALONE_DOT_MODE => Ok(PreparedMode::Relation4StandaloneDot(
            prepare_relation(parsed, mode, RelationVariant::FourClaimsStandaloneDot)?,
        )),
        V5_CU_PROBE_RELATION4_COMPACT_MODE => Ok(PreparedMode::Relation4Compact(prepare_relation(
            parsed,
            mode,
            RelationVariant::FourClaimsCompact,
        )?)),
        _ => Err(ProgramError::InvalidInstructionData),
    }
}

fn generic_combine<const C1_COLUMNS: usize, const FUSED_HELPERS: bool>(
    c1_value: &[u8],
    c2_value: &[u8],
    prepared: &GenericPrepared<C1_COLUMNS>,
) -> Result<[QM31; STATE_ONLY_FIBER_SLOTS], ProgramError> {
    if c1_value.len() != STATE_ONLY_FIBER_SLOTS * C1_COLUMNS * M31_BYTES
        || c2_value.len() != V5_CU_PROBE_C2_VALUE_BYTES
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let mut combined = if C1_COLUMNS % 4 == 0 {
        qm31_m31_dot4_prepared_limbs_4b_bytes::<C1_COLUMNS>(&prepared.c1_weight_limbs, c1_value)
    } else {
        qm31_m31_dot4_prepared_limbs_4b2_bytes::<C1_COLUMNS>(&prepared.c1_weight_limbs, c1_value)
    }
    .ok_or(ProgramError::InvalidAccountData)?;
    let mut helper_values = [[QM31::ZERO; V5_CU_PROBE_C2_COLUMNS]; STATE_ONLY_FIBER_SLOTS];
    for helper in 0..V5_CU_PROBE_C2_COLUMNS {
        for (slot, values) in helper_values.iter_mut().enumerate() {
            let offset = (helper * STATE_ONLY_FIBER_SLOTS + slot) * QM31_BYTES;
            values[helper] = QM31::from_le_bytes(&c2_value[offset..offset + QM31_BYTES])
                .ok_or(ProgramError::InvalidAccountData)?;
        }
    }
    for (slot, output) in combined.iter_mut().enumerate() {
        let helper_sum = if FUSED_HELPERS {
            qm31_sum_products3_prepared(&prepared.helpers, &helper_values[slot])
        } else {
            qm31_sum_products2_prepared(
                &[prepared.helpers[0], prepared.helpers[1]],
                &[helper_values[slot][0], helper_values[slot][1]],
            )
            .add(prepared.helpers[2].mul(helper_values[slot][2]))
        };
        *output = output.add(helper_sum);
    }
    Ok(combined)
}

fn c1_record_for_mode<'a>(
    mode: u8,
    parsed: &'a ParsedProbeData<'a>,
    query: usize,
) -> Result<&'a [u8], ProgramError> {
    if mode == V5_CU_PROBE_PRODUCTION26_MODE
        || mode == V5_CU_PROBE_GENERIC26_NONFUSED_MODE
        || mode == V5_CU_PROBE_GENERIC26_FUSED_MODE
    {
        parsed
            .production_c1_record(query)
            .ok_or(ProgramError::InvalidAccountData)
    } else {
        Ok(parsed.candidate_c1_record(query))
    }
}

#[inline(never)]
fn run_marked_kernel(
    mode: u8,
    parsed: &ParsedProbeData<'_>,
    prepared: &mut PreparedMode,
    outputs: &mut [ProbeOutput],
) -> Result<(), ProgramError> {
    if outputs.len() != V5_CU_PROBE_QUERY_COUNT {
        return Err(ProgramError::InvalidAccountData);
    }
    let relation = match prepared {
        PreparedMode::Relation3(relation)
        | PreparedMode::Relation4Dense(relation)
        | PreparedMode::Relation4StandaloneDot(relation)
        | PreparedMode::Relation4Compact(relation) => Some(relation),
        _ => None,
    };
    if let Some(relation) = relation {
        outputs[0].combined[0] = run_relation_kernel(relation);
        return Ok(());
    }

    for (query, output) in outputs.iter_mut().enumerate() {
        let c1_record = c1_record_for_mode(mode, parsed, query)?;
        let c2_record = parsed.c2_record(query);
        let c1_hash =
            private_leaf_hash_record(crate::verify::sbf_hashv, CIRCLE_C1_LAYER0_TAG, c1_record);
        let c2_hash =
            private_leaf_hash_record(crate::verify::sbf_hashv, CIRCLE_C2_LAYER0_TAG, c2_record);
        let combined = match prepared {
            PreparedMode::Production26(powers) => gamma_combine_state_only_spend_layer0_prepared(
                &c1_record[..STATE_ONLY_C1_LEAF_BYTES],
                &c2_record[..SPEND_C2_LEAF_BYTES],
                powers,
            )
            .map_err(|_| ProgramError::InvalidAccountData)?,
            PreparedMode::Generic26Nonfused(powers) => {
                generic_combine::<V5_CU_PROBE_PRODUCTION_C1_COLUMNS, false>(
                    &c1_record[..V5_CU_PROBE_PRODUCTION_C1_VALUE_BYTES],
                    &c2_record[..V5_CU_PROBE_C2_VALUE_BYTES],
                    powers,
                )?
            }
            PreparedMode::Generic16Nonfused(powers) => {
                generic_combine::<V5_CU_PROBE_CANDIDATE_C1_COLUMNS, false>(
                    &c1_record[..V5_CU_PROBE_CANDIDATE_C1_VALUE_BYTES],
                    &c2_record[..V5_CU_PROBE_C2_VALUE_BYTES],
                    powers,
                )?
            }
            PreparedMode::Generic16Fused(powers) => {
                generic_combine::<V5_CU_PROBE_CANDIDATE_C1_COLUMNS, true>(
                    &c1_record[..V5_CU_PROBE_CANDIDATE_C1_VALUE_BYTES],
                    &c2_record[..V5_CU_PROBE_C2_VALUE_BYTES],
                    powers,
                )?
            }
            PreparedMode::Generic26Fused(powers) => {
                generic_combine::<V5_CU_PROBE_PRODUCTION_C1_COLUMNS, true>(
                    &c1_record[..V5_CU_PROBE_PRODUCTION_C1_VALUE_BYTES],
                    &c2_record[..V5_CU_PROBE_C2_VALUE_BYTES],
                    powers,
                )?
            }
            PreparedMode::Relation3(_)
            | PreparedMode::Relation4Dense(_)
            | PreparedMode::Relation4StandaloneDot(_)
            | PreparedMode::Relation4Compact(_) => unreachable!(),
        };
        *output = ProbeOutput {
            c1_hash,
            c2_hash,
            combined,
        };
    }
    Ok(())
}

fn run_relation_kernel(relation: &mut PreparedRelation) -> QM31 {
    for alpha in relation.alphas {
        relation.weights.fold(alpha);
        if let RelationExtraWork::Compact(compact) = &mut relation.extra_work {
            compact.fold(alpha);
        }
    }
    let extra = match &relation.extra_work {
        RelationExtraWork::None => QM31::ZERO,
        RelationExtraWork::Compact(compact) => compact.dot(&relation.final_values),
        RelationExtraWork::StandaloneDot {
            covector,
            pivot,
            lane_value,
        } => covector
            .iter()
            .copied()
            .enumerate()
            .filter(|(row, _)| row != pivot)
            .fold(QM31::ZERO, |sum, (_, weight)| {
                sum.add(lane_value.mul(weight))
            }),
    };
    relation
        .weights
        .dot(&relation.final_values)
        .add(relation.relation_value)
        .add(extra)
}

fn decode_v5_fri_alphas(
    parsed: &ParsedProbeData<'_>,
) -> Result<[QM31; V5_CU_PROBE_RELATION_FOLDS], ProgramError> {
    let mut alphas = [QM31::ZERO; V5_CU_PROBE_RELATION_FOLDS];
    for (round, alpha) in alphas.iter_mut().enumerate() {
        *alpha = decode_qm31(parsed.relation_alphas, round)?;
    }
    Ok(alphas)
}

/// Build the accepting relation tail for the exact point/copy/Component-B
/// initial claim parsed from this stress account. This host-only helper keeps
/// the sumcheck boundary equal to the same claim consumed on SBF.
#[cfg(not(target_os = "solana"))]
pub fn build_v5_complete_relation_stress_tail(
    account_data: &[u8],
) -> Result<[u8; V5_RELATION_STRESS_BYTES], ProgramError> {
    let parsed = parse_probe_data(account_data)?;
    build_v5_complete_relation_stress_tail_from_parsed(&parsed)
}

/// Build a relation tail for the tag-66 comparison fixture, whose retired
/// width-26 records live in a sidecar excluded from the mode-9 grammar.
#[cfg(not(target_os = "solana"))]
pub fn build_v5_complete_relation_stress_tail_for_diagnostics(
    account_data: &[u8],
) -> Result<[u8; V5_RELATION_STRESS_BYTES], ProgramError> {
    let parsed = parse_diagnostic_probe_data(account_data)?;
    build_v5_complete_relation_stress_tail_from_parsed(&parsed)
}

#[cfg(not(target_os = "solana"))]
fn build_v5_complete_relation_stress_tail_from_parsed(
    parsed: &ParsedProbeData<'_>,
) -> Result<[u8; V5_RELATION_STRESS_BYTES], ProgramError> {
    let (verified_prefix, _) =
        verify_v5_wire_prefix_from_context(parsed, crate::verify::sbf_hashv)?;
    let (relation, _, _) = prepare_relation_base_with_kappa(
        parsed,
        RelationVariant::FourClaimsCompact,
        verified_prefix.kappa,
        verified_prefix.inactive_claim,
    )?;
    let alphas = decode_v5_fri_alphas(parsed)?;
    Ok(
        crate::v5_relation_stress::build_v5_relation_stress_tail_for_initial_claim(
            relation.relation_value,
            alphas,
        ),
    )
}

fn outputs_sink(mode: u8, outputs: &[ProbeOutput]) -> Result<[u8; 32], ProgramError> {
    if outputs.len() != V5_CU_PROBE_QUERY_COUNT {
        return Err(ProgramError::InvalidAccountData);
    }
    if relation_variant(mode).is_some() {
        let mut value = [0u8; QM31_BYTES];
        outputs[0].combined[0].write_le_bytes(&mut value);
        return Ok(crate::verify::sbf_hashv(&[SINK_DOMAIN, &[mode], &value]));
    }
    let mut material = vec![0u8; PROBE_SINK_MATERIAL_BYTES];
    for (query, output) in outputs.iter().enumerate() {
        let start = query * QUERY_SINK_BYTES;
        material[start..start + 32].copy_from_slice(&output.c1_hash);
        material[start + 32..start + 64].copy_from_slice(&output.c2_hash);
        for (slot, value) in output.combined.iter().enumerate() {
            let offset = start + 64 + slot * QM31_BYTES;
            value.write_le_bytes(&mut material[offset..offset + QM31_BYTES]);
        }
    }
    Ok(crate::verify::sbf_hashv(&[SINK_DOMAIN, &[mode], &material]))
}

#[inline(never)]
fn verify_mode9_fri_phase(
    parsed: &ParsedProbeData<'_>,
    queries: &[u32; V5_CU_PROBE_QUERY_COUNT],
    final_polynomial: &[QM31; V5_CU_PROBE_RELATION_FINAL_VALUES],
    alphas: &[QM31; V5_CU_PROBE_RELATION_FOLDS],
    gamma: QM31,
) -> Result<(QM31, V5PreparedPcsClaims), ProgramError> {
    let private_openings = verify_v5_private_suffix(parsed, queries)?;
    let prepared_claims = prepare_v5_pcs_claims(gamma, parsed.relation_claims)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let fri = check_v5_fri_queries(
        &private_openings,
        &prepared_claims,
        *alphas,
        *final_polynomial,
        M31::inv,
    )
    .map_err(|_| ProgramError::InvalidAccountData)?;
    Ok((fri.folded_layer0_sum, prepared_claims))
}

#[inline(never)]
fn verify_mode9_relation_phase(
    parsed: &ParsedProbeData<'_>,
    final_polynomial: &[QM31; V5_CU_PROBE_RELATION_FINAL_VALUES],
    alphas: &[QM31; V5_CU_PROBE_RELATION_FOLDS],
    kappa: QM31,
    inactive_claim: QM31,
    round_challenges: &[QM31; V5_CU_PROBE_RELATION_LOG_ROWS as usize],
    prepared_claims: &V5PreparedPcsClaims,
) -> Result<QM31, ProgramError> {
    let (relation, _, dense_scale) = prepare_relation_base_with_kappa_prepared(
        parsed,
        RelationVariant::FourClaimsCompact,
        kappa,
        inactive_claim,
        prepared_claims,
    )?;
    let compact = CompactBTerminalWeights::new(round_challenges, dense_scale);
    let relation_stress = verify_v5_relation_stress_with_additive(
        relation.weights,
        relation.relation_value,
        *alphas,
        parsed.v5_relation_stress,
        compact,
    )
    .map_err(|_| ProgramError::InvalidAccountData)?;
    if relation_stress.final_coefficients != *final_polynomial {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(relation_stress.terminal_claim)
}

#[inline(never)]
fn verify_mode9_composite_with_live_statement(
    account_data: &[u8],
    parsed: &ParsedProbeData<'_>,
    live_statement: &AtomicPaymentStatementV4,
    statement_digest: &[u8; 32],
) -> Result<QM31, ProgramError> {
    let (verified_prefix, prefix_transcript) = verify_v5_wire_prefix(
        parsed,
        live_statement,
        statement_digest,
        crate::verify::sbf_hashv,
    )?;
    let terminal_masked =
        verify_mode9_atomic_terminal_with_prefix(parsed, live_statement, &verified_prefix)?.masked;
    let gamma = verified_prefix.gamma;
    let kappa = verified_prefix.kappa;
    let inactive_claim = verified_prefix.inactive_claim;
    let round_challenges = verified_prefix.round_challenges;
    let relation_transcript = replay_real_v5_relation_rounds(prefix_transcript, parsed)?;
    let (final_polynomial, queries) = derive_v5_selected_good_queries_from_transcript(
        relation_transcript,
        parsed,
        &round_challenges,
    )?;
    let alphas = decode_v5_fri_alphas(parsed)?;
    let (fri_sum, prepared_claims) =
        verify_mode9_fri_phase(parsed, &queries, &final_polynomial, &alphas, gamma)?;
    let relation_claim = verify_mode9_relation_phase(
        parsed,
        &final_polynomial,
        &alphas,
        kappa,
        inactive_claim,
        &round_challenges,
        &prepared_claims,
    )?;
    // Tie the raw slice to this verification call. All parsing above borrows
    // from exactly these uploaded proof bytes.
    core::hint::black_box(account_data.len());
    Ok(fri_sum.add(relation_claim).add(terminal_masked))
}

/// Return the exact declared body of one sealed tag-67 proof account.  The
/// generic upload lifecycle permits over-allocation, but the candidate v5 wire
/// has no account-padding grammar: every released account byte must belong to
/// the declared proof body.
fn exact_uploaded_v5_proof_body(data: &[u8]) -> Result<&[u8], ProgramError> {
    if !proof_account_finalized(data) {
        return Err(ProgramError::InvalidAccountData);
    }
    let (proof_start, proof_end) = uploaded_proof_bounds(data)?;
    if proof_end != data.len() {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(&data[proof_start..proof_end])
}

/// Full real-witness v5 CU verifier callback for the live atomic state
/// transition. The proof account must be sealed, the canonical statement
/// digest is recomputed and transcript-bound, and every semantic, relation,
/// FRI, and five-section opening check runs before state can mutate.
#[inline(never)]
pub fn verify_uploaded_v5_mode9_cu_fixture(
    proof_account: &AccountInfo,
    live_statement: &AtomicPaymentStatementV4,
    statement_digest: &[u8; 32],
) -> ProgramResult {
    // `verify_v5_wire_prefix` below recomputes this digest from the same
    // immutable live statement before constructing or advancing a transcript.
    let data = proof_account.try_borrow_data()?;
    let account_data = exact_uploaded_v5_proof_body(&data)?;
    let parsed = parse_probe_data(account_data)?;
    let terminal = verify_mode9_composite_with_live_statement(
        account_data,
        &parsed,
        live_statement,
        statement_digest,
    )?;
    core::hint::black_box(terminal);
    Ok(())
}

/// Compute the checked sink from the same runtime account bytes supplied to
/// the verifier. Host diagnostics use it for tag 66; the tag-67 transaction
/// instead runs [`verify_uploaded_v5_mode9_cu_fixture`] against live state.
#[cfg(not(target_os = "solana"))]
pub fn probe_sink(mode: u8, account_data: &[u8]) -> Result<[u8; 32], ProgramError> {
    let parsed = parse_probe_data_for_mode(mode, account_data)?;
    let mut outputs = vec![EMPTY_OUTPUT; V5_CU_PROBE_QUERY_COUNT];
    if mode == V5_CU_PROBE_COMPOSITE_MODE {
        let (verified_prefix, prefix_transcript) =
            verify_v5_wire_prefix_from_context(&parsed, crate::verify::sbf_hashv)?;
        let relation_transcript = replay_real_v5_relation_rounds(prefix_transcript, &parsed)?;
        let (final_polynomial, queries) = derive_v5_selected_good_queries_from_transcript(
            relation_transcript,
            &parsed,
            &verified_prefix.round_challenges,
        )?;
        let private_openings = verify_v5_private_suffix(&parsed, &queries)?;
        let alphas = decode_v5_fri_alphas(&parsed)?;
        let prepared_claims = prepare_v5_pcs_claims(parsed.gamma, parsed.relation_claims)
            .map_err(|_| ProgramError::InvalidAccountData)?;
        let fri = check_v5_fri_queries(
            &private_openings,
            &prepared_claims,
            alphas,
            final_polynomial,
            M31::inv,
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;
        let (relation, _, dense_scale) = prepare_relation_base_with_kappa_prepared(
            &parsed,
            RelationVariant::FourClaimsCompact,
            verified_prefix.kappa,
            verified_prefix.inactive_claim,
            &prepared_claims,
        )?;
        let compact = CompactBTerminalWeights::new(&verified_prefix.round_challenges, dense_scale);
        let relation_stress = verify_v5_relation_stress_with_additive(
            relation.weights,
            relation.relation_value,
            alphas,
            parsed.v5_relation_stress,
            compact,
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;
        if relation_stress.final_coefficients != final_polynomial {
            return Err(ProgramError::InvalidAccountData);
        }
        outputs[0].combined[0] = outputs[0].combined[0]
            .add(fri.folded_layer0_sum)
            .add(relation_stress.terminal_claim)
            .add(verified_prefix.terminal_masked);
    } else {
        let mut prepared = prepare_mode(mode, &parsed)?;
        run_marked_kernel(mode, &parsed, &mut prepared, &mut outputs)?;
    }
    outputs_sink(mode, &outputs)
}

fn v5_lifecycle_take<const N: usize>(wire: &mut &[u8]) -> Result<[u8; N], ProgramError> {
    let (head, tail) = wire
        .split_first_chunk::<N>()
        .ok_or(ProgramError::InvalidInstructionData)?;
    *wire = tail;
    Ok(*head)
}

fn require_exact_v5_lifecycle_accounts(accounts: &[AccountInfo], expected: usize) -> ProgramResult {
    if accounts.len() == expected {
        Ok(())
    } else {
        Err(ProgramError::NotEnoughAccountKeys)
    }
}

fn process_v5_feature_lifecycle_tag(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    let (&tag, mut wire) = instruction_data
        .split_first()
        .ok_or(ProgramError::InvalidInstructionData)?;
    match tag {
        0 => {
            let total_len = u32::from_le_bytes(v5_lifecycle_take::<4>(&mut wire)?);
            if !wire.is_empty() {
                return Err(ProgramError::InvalidInstructionData);
            }
            require_exact_v5_lifecycle_accounts(accounts, 2)?;
            crate::lifecycle::init_proof(program_id, accounts, total_len)
        }
        1 => {
            let offset = u32::from_le_bytes(v5_lifecycle_take::<4>(&mut wire)?);
            let chunk_len = u32::from_le_bytes(v5_lifecycle_take::<4>(&mut wire)?) as usize;
            if wire.len() != chunk_len {
                return Err(ProgramError::InvalidInstructionData);
            }
            require_exact_v5_lifecycle_accounts(accounts, 2)?;
            crate::lifecycle::upload_chunk(program_id, accounts, offset, wire)
        }
        62 => {
            if !wire.is_empty() {
                return Err(ProgramError::InvalidInstructionData);
            }
            require_exact_v5_lifecycle_accounts(accounts, 2)?;
            crate::lifecycle::finalize_proof(program_id, accounts)
        }
        63 => {
            let sequence = u64::from_le_bytes(v5_lifecycle_take::<8>(&mut wire)?);
            let anchor = v5_lifecycle_take::<32>(&mut wire)?;
            let domain_tag_len = u32::from_le_bytes(v5_lifecycle_take::<4>(&mut wire)?) as usize;
            if wire.len() != domain_tag_len {
                return Err(ProgramError::InvalidInstructionData);
            }
            require_exact_v5_lifecycle_accounts(accounts, 1)?;
            crate::lifecycle::initialize_atomic_pool(program_id, accounts, sequence, anchor, wire)
        }
        64 => {
            if !wire.is_empty() {
                return Err(ProgramError::InvalidInstructionData);
            }
            require_exact_v5_lifecycle_accounts(accounts, 2)?;
            crate::lifecycle::close_proof(program_id, accounts)
        }
        _ => Err(ProgramError::InvalidInstructionData),
    }
}

fn try_process_v5_feature_lifecycle_tag(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> Option<ProgramResult> {
    matches!(instruction_data.first(), Some(0 | 1 | 62 | 63 | 64))
        .then(|| process_v5_feature_lifecycle_tag(program_id, accounts, instruction_data))
}

/// Isolated candidate entrypoint. It accepts the complete tag-67 CU wrapper
/// plus the existing proof/pool lifecycle subset needed to materialize a
/// devnet fixture. It retains tag-66 diagnostics for host tests. The
/// production dispatcher references none of these feature-gated routes.
pub fn process_v5_cu_probe_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    if instruction_data.first().copied()
        == Some(crate::v5_full_transaction::V5_FULL_CU_TRANSACTION_TAG)
    {
        return crate::v5_full_transaction::process_v5_full_cu_transaction_with_verifier(
            program_id,
            accounts,
            instruction_data,
            verify_uploaded_v5_mode9_cu_fixture,
        );
    }
    if let Some(result) =
        try_process_v5_feature_lifecycle_tag(program_id, accounts, instruction_data)
    {
        return result;
    }
    #[cfg(not(target_os = "solana"))]
    {
        process_v5_cu_probe_tag66_instruction(program_id, accounts, instruction_data)
    }
    #[cfg(target_os = "solana")]
    {
        // The measured SBF contains tag 67 and the minimal account-lifecycle
        // subset above. The older ten-mode tag-66 instrumentation remains
        // host-testable but is not linked into this candidate artifact.
        Err(ProgramError::InvalidInstructionData)
    }
}

/// Keep the historical multi-mode measurement handler in a separate frame.
/// The real tag-67 transaction never needs its large diagnostic locals.
#[inline(never)]
#[cfg(not(target_os = "solana"))]
fn process_v5_cu_probe_tag66_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    if accounts.len() != 1
        || accounts[0].owner != program_id
        || accounts[0].is_signer
        || accounts[0].is_writable
        || instruction_data.len() != V5_CU_PROBE_WIRE_BYTES
        || instruction_data[0] != V5_CU_PROBE_TAG
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    let mode = instruction_data[1];
    let expected: [u8; 32] = instruction_data[2..].try_into().unwrap();

    msg!("aspis-cu:v5-probe-parse-start");
    sol_log_compute_units();
    let account_data = accounts[0].try_borrow_data()?;
    let parsed = parse_probe_data_for_mode(mode, &account_data)?;
    let mut outputs = vec![EMPTY_OUTPUT; V5_CU_PROBE_QUERY_COUNT];

    if mode == V5_CU_PROBE_COMPOSITE_MODE {
        msg!("aspis-cu:v5-probe-prefix-start");
        sol_log_compute_units();
        let (verified_prefix, _) =
            verify_v5_wire_prefix_from_context(&parsed, crate::verify::sbf_hashv)?;
        msg!("aspis-cu:v5-probe-prefix-complete");
        sol_log_compute_units();

        msg!("aspis-cu:v5-probe-query-binding-start");
        sol_log_compute_units();
        let (final_polynomial, queries) =
            derive_v5_complete_queries(crate::verify::sbf_hashv, &account_data, &parsed)?;
        msg!("aspis-cu:v5-probe-query-binding-complete");
        sol_log_compute_units();

        msg!("aspis-cu:v5-probe-private-start");
        sol_log_compute_units();
        let private_openings = verify_v5_private_suffix(&parsed, &queries)?;
        msg!("aspis-cu:v5-probe-private-complete");
        sol_log_compute_units();

        msg!("aspis-cu:v5-probe-fri-prepare-start");
        sol_log_compute_units();
        let alphas = decode_v5_fri_alphas(&parsed)?;
        let prepared_claims = prepare_v5_pcs_claims(parsed.gamma, parsed.relation_claims)
            .map_err(|_| ProgramError::InvalidAccountData)?;
        msg!("aspis-cu:v5-probe-fri-prepare-complete");
        sol_log_compute_units();

        msg!("aspis-cu:v5-probe-fri-start");
        sol_log_compute_units();
        let fri = check_v5_fri_queries(
            &private_openings,
            &prepared_claims,
            alphas,
            final_polynomial,
            M31::inv,
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;
        msg!("aspis-cu:v5-probe-fri-complete");
        sol_log_compute_units();

        let (relation, _, dense_scale) = prepare_relation_base_with_kappa_prepared(
            &parsed,
            RelationVariant::FourClaimsCompact,
            verified_prefix.kappa,
            verified_prefix.inactive_claim,
            &prepared_claims,
        )?;
        msg!("aspis-cu:v5-probe-claims-complete");
        sol_log_compute_units();
        let compact = CompactBTerminalWeights::new(&verified_prefix.round_challenges, dense_scale);
        msg!("aspis-cu:v5-probe-covector-complete");
        sol_log_compute_units();

        msg!("aspis-cu:v5-probe-relation-stress-start");
        sol_log_compute_units();
        let relation_stress = verify_v5_relation_stress_with_additive(
            relation.weights,
            relation.relation_value,
            alphas,
            parsed.v5_relation_stress,
            compact,
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;
        if relation_stress.final_coefficients != final_polynomial {
            return Err(ProgramError::InvalidAccountData);
        }
        msg!("aspis-cu:v5-probe-relation-stress-complete");
        sol_log_compute_units();

        outputs[0].combined[0] = outputs[0].combined[0]
            .add(fri.folded_layer0_sum)
            .add(relation_stress.terminal_claim)
            .add(verified_prefix.terminal_masked);
    } else if let Some(variant) = relation_variant(mode) {
        // All common relation preparation and the lane-claim aggregation are
        // complete at the first boundary. Comparing modes 5 and 6 therefore
        // isolates the fourth set of nineteen canonical claims.
        let (relation, terminal_point, dense_scale) = prepare_relation_base(&parsed, variant)?;
        msg!("aspis-cu:v5-probe-claims-complete");
        sol_log_compute_units();

        // Dense control modes retain the rejected prototype materialisation.
        // The compact candidate derives only its ten power ladders and fixed
        // singleton, with no 1024-value allocation.
        let opening = match variant {
            RelationVariant::ThreeClaims => DerivedRelationOpening::None,
            RelationVariant::FourClaimsSharedFold | RelationVariant::FourClaimsStandaloneDot => {
                let (covector, pivot) =
                    derive_v5_b_terminal_covector(mode, &terminal_point, dense_scale)?;
                DerivedRelationOpening::Dense(covector, pivot)
            }
            RelationVariant::FourClaimsCompact => DerivedRelationOpening::Compact(
                CompactBTerminalWeights::new(&terminal_point, dense_scale),
            ),
        };
        msg!("aspis-cu:v5-probe-covector-complete");
        sol_log_compute_units();

        let mut relation = relation;
        install_relation_covector(&mut relation, variant, opening)?;
        let mut prepared = match variant {
            RelationVariant::ThreeClaims => PreparedMode::Relation3(relation),
            RelationVariant::FourClaimsSharedFold => PreparedMode::Relation4Dense(relation),
            RelationVariant::FourClaimsStandaloneDot => {
                PreparedMode::Relation4StandaloneDot(relation)
            }
            RelationVariant::FourClaimsCompact => PreparedMode::Relation4Compact(relation),
        };
        run_marked_kernel(mode, &parsed, &mut prepared, &mut outputs)?;
        msg!("aspis-cu:v5-probe-kernel-complete");
        sol_log_compute_units();
    } else {
        let mut prepared = prepare_mode(mode, &parsed)?;
        msg!("aspis-cu:v5-probe-kernel-start");
        sol_log_compute_units();
        run_marked_kernel(mode, &parsed, &mut prepared, &mut outputs)?;
        msg!("aspis-cu:v5-probe-kernel-complete");
        sol_log_compute_units();
    }

    // Sink and check every hash and field result only after the end marker,
    // keeping output serialisation and the final SHA-256 outside the kernel.
    let actual = outputs_sink(mode, &outputs)?;
    if actual == expected {
        Ok(())
    } else {
        Err(ProgramError::InvalidInstructionData)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lifecycle::{PROOF_ACCOUNT_HEADER_LEN, PROOF_ACCOUNT_MAGIC};
    use crate::wire::AspisInstruction;
    use crate::{id, test_support::make_account};
    use aspis_core::field::{M31, P};
    use aspis_statement::{
        encode_atomic_payment_statement_v4, AtomicPaymentStatementV4, SpendPublic,
        ATOMIC_PAYMENT_STATEMENT_DOMAIN, VALUE_LIMIT,
    };
    use borsh::to_vec;

    const WORK_TEST_VALID_NONCE: u64 = 0x776f_726b_2d6f_6b21;

    fn controlled_work_hash(inputs: &[&[u8]]) -> [u8; 32] {
        let valid = WORK_TEST_VALID_NONCE.to_le_bytes();
        if inputs.len() == 3 && inputs[1] == [3] {
            return if inputs[2] == valid.as_slice() {
                [0u8; 32]
            } else {
                [0xffu8; 32]
            };
        }
        crate::verify::sbf_hashv(inputs)
    }

    fn threshold_work_hash(inputs: &[&[u8]]) -> [u8; 32] {
        let mut digest = [0u8; 32];
        if inputs.len() == 3 && inputs[1] == [3] {
            let head = u64::from_le_bytes(inputs[2].try_into().unwrap());
            digest[..8].copy_from_slice(&head.to_be_bytes());
        }
        digest
    }

    fn work_test_transcript() -> Transcript {
        let mut transcript = Transcript::new(controlled_work_hash);
        transcript.absorb(label::PROFILE, V5_REAL_HOST_TRANSCRIPT_DOMAIN);
        transcript.absorb(label::STATEMENT, &[0x5a; 32]);
        transcript
    }

    fn former_direct_work_wire_u64(data: &[u8], offset: usize) -> u64 {
        u64::from_le_bytes(data[offset..offset + 8].try_into().unwrap())
    }

    fn former_direct_work_wire_projection(data: &[u8]) -> V5WorkWireProjection {
        V5WorkWireProjection {
            fold_nonces: core::array::from_fn(|round| {
                former_direct_work_wire_u64(data, V5_CU_PROBE_RELATION_FINAL_OFFSET + round * 8)
            }),
            batch_nonce: former_direct_work_wire_u64(data, V5_CU_PROBE_BATCH_NONCE_OFFSET),
            final_nonce: former_direct_work_wire_u64(data, V5_CU_PROBE_FINAL_NONCE_OFFSET),
            query_selector: data[V5_CU_PROBE_QUERY_SELECTOR_OFFSET],
        }
    }

    fn former_direct_zero_tail_is_valid(relation_final: &[u8]) -> bool {
        relation_final.len() == V5_CU_PROBE_RELATION_FINAL_BYTES
            && !relation_final[V5_CU_PROBE_RELATION_FINAL_ZERO_TAIL_RELATIVE_OFFSET..]
                .iter()
                .any(|byte| *byte != 0)
    }

    #[test]
    fn tag67_extraction_work_projection_matches_former_direct_spelling() {
        for seed in 0u8..=255 {
            let mut data = vec![0u8; V5_CU_PROBE_PRIVATE_PROOF_OFFSET];
            data[..V5_CU_PROBE_ACCOUNT_MAGIC.len()].copy_from_slice(&V5_CU_PROBE_ACCOUNT_MAGIC);
            for round in 0..V5_CU_PROBE_RELATION_FOLDS {
                let start = V5_CU_PROBE_RELATION_FINAL_OFFSET + round * 8;
                for byte in 0..8 {
                    data[start + byte] = seed.wrapping_add((round * 8 + byte) as u8);
                }
            }
            for byte in 0..8 {
                data[V5_CU_PROBE_BATCH_NONCE_OFFSET + byte] = seed.wrapping_add((32 + byte) as u8);
                data[V5_CU_PROBE_FINAL_NONCE_OFFSET + byte] = seed.wrapping_add((40 + byte) as u8);
            }
            data[V5_CU_PROBE_QUERY_SELECTOR_OFFSET] = seed % 3;
            let expected = former_direct_work_wire_projection(&data);
            let actual = project_v5_work_wire(&data);
            assert_eq!(actual, expected, "seed {seed}");

            let parsed = parse_probe_data(&data).expect("canonical fixed work-wire shape");
            assert_eq!(parsed.v5_fold_nonces, actual.fold_nonces);
            assert_eq!(parsed.v5_batch_nonce, actual.batch_nonce);
            assert_eq!(parsed.v5_final_nonce, actual.final_nonce);
            assert_eq!(parsed.v5_query_selector, actual.query_selector);
        }
    }

    #[test]
    fn tag67_extraction_guards_match_former_magic_zero_tail_and_selector_spelling() {
        let mut data = vec![0u8; V5_CU_PROBE_PRIVATE_PROOF_OFFSET];
        data[..V5_CU_PROBE_ACCOUNT_MAGIC.len()].copy_from_slice(&V5_CU_PROBE_ACCOUNT_MAGIC);
        assert!(v5_work_wire_magic_is_valid(&data));
        for byte in 0..V5_CU_PROBE_ACCOUNT_MAGIC.len() {
            let saved = data[byte];
            data[byte] ^= 1;
            assert!(!v5_work_wire_magic_is_valid(&data));
            assert!(parse_probe_data(&data).is_err());
            data[byte] = saved;
        }
        for length in 0..V5_CU_PROBE_ACCOUNT_MAGIC.len() {
            assert!(!v5_work_wire_magic_is_valid(&data[..length]));
        }

        let mut relation_final = [0u8; V5_CU_PROBE_RELATION_FINAL_BYTES];
        assert_eq!(
            v5_relation_final_zero_tail_is_valid(&relation_final),
            former_direct_zero_tail_is_valid(&relation_final)
        );
        for offset in 0..relation_final.len() {
            relation_final[offset] = 1;
            assert_eq!(
                v5_relation_final_zero_tail_is_valid(&relation_final),
                former_direct_zero_tail_is_valid(&relation_final),
                "relation-final offset {offset}"
            );
            relation_final[offset] = 0;
        }
        for length in 0..relation_final.len() {
            assert_eq!(
                v5_relation_final_zero_tail_is_valid(&relation_final[..length]),
                former_direct_zero_tail_is_valid(&relation_final[..length]),
                "relation-final length {length}"
            );
        }
        for selector in u8::MIN..=u8::MAX {
            assert_eq!(v5_query_selector_is_valid(selector), selector < 3);
        }
    }

    #[test]
    fn tag67_extraction_work_records_and_difficulties_match_former_spelling() {
        for nonce in [0, 1, u64::from(u32::MAX), 0x0123_4567_89ab_cdef, u64::MAX] {
            assert_eq!(v5_batch_work_record(nonce), nonce.to_le_bytes());
            assert_eq!(v5_final_work_record(nonce), nonce.to_le_bytes());
            for round in 0..4 {
                let mut former = [0u8; 9];
                former[0] = round as u8;
                former[1..].copy_from_slice(&nonce.to_le_bytes());
                assert_eq!(v5_fold_work_record(round, nonce), former);
                assert_eq!(
                    v5_fold_work_absorb_input(round, nonce),
                    (label::M31_CIRCLE_FOLD_POW_NONCE, former)
                );
                assert_eq!(
                    v5_fold_work_difficulty(round),
                    STATE_ONLY_SPEND_FOLD_GRINDING_BITS.get(round).copied()
                );
            }
            assert_eq!(
                v5_batch_work_absorb_input(nonce),
                (label::M31_PAYMENT_BATCH_POW_NONCE, nonce.to_le_bytes())
            );
            assert_eq!(
                v5_final_work_absorb_input(nonce),
                (label::GRIND_NONCE, nonce.to_le_bytes())
            );
        }
        assert_eq!(
            v5_batch_work_difficulty(),
            STATE_ONLY_SPEND_BATCH_GRINDING_BITS
        );
        assert_eq!(v5_final_work_difficulty(), STATE_ONLY_SPEND_GRINDING_BITS);
        for round in 4..12 {
            assert_eq!(v5_fold_work_difficulty(round), None);
        }
    }

    #[test]
    fn v5_feature_lifecycle_requires_exact_wires_accounts_and_tags() {
        let wires = [
            (
                to_vec(&AspisInstruction::InitProof { total_len: 4 }).unwrap(),
                2,
            ),
            (
                to_vec(&AspisInstruction::UploadChunk {
                    offset: 0,
                    chunk: vec![1, 2, 3, 4],
                })
                .unwrap(),
                2,
            ),
            (to_vec(&AspisInstruction::FinalizeProof).unwrap(), 2),
            (
                to_vec(&AspisInstruction::InitializeAtomicPool {
                    sequence: 7,
                    anchor: [0u8; 32],
                    domain_tag: b"devnet".to_vec(),
                })
                .unwrap(),
                1,
            ),
            (to_vec(&AspisInstruction::CloseFinalizedProof).unwrap(), 2),
        ];
        let owner = id();
        let key = Pubkey::new_unique();
        let mut lamports = 1;
        let mut data = [];
        let dummy = make_account(&key, &owner, &mut lamports, &mut data, false, false);

        for (wire, expected_accounts) in wires {
            assert_eq!(
                process_v5_cu_probe_instruction(&owner, &[], &wire),
                Err(ProgramError::NotEnoughAccountKeys),
                "exact lifecycle tag {} did not reach its account-count gate",
                wire[0]
            );
            let excess_accounts = vec![dummy.clone(); expected_accounts + 1];
            assert_eq!(
                process_v5_cu_probe_instruction(&owner, &excess_accounts, &wire),
                Err(ProgramError::NotEnoughAccountKeys),
                "lifecycle tag {} accepted excess accounts",
                wire[0]
            );
            for end in 0..wire.len() {
                assert_eq!(
                    process_v5_cu_probe_instruction(&owner, &[], &wire[..end]),
                    Err(ProgramError::InvalidInstructionData),
                    "lifecycle tag {} accepted prefix length {end}",
                    wire[0]
                );
            }
            let mut trailing = wire.clone();
            trailing.push(0);
            assert_eq!(
                process_v5_cu_probe_instruction(&owner, &[], &trailing),
                Err(ProgramError::InvalidInstructionData),
                "lifecycle tag {} accepted a trailing byte",
                wire[0]
            );
        }

        for rejected in [2u8, 59, 60, 61, 65, 68, u8::MAX] {
            assert_eq!(
                process_v5_cu_probe_instruction(&owner, &[], &[rejected]),
                Err(ProgramError::InvalidInstructionData),
                "feature-only entrypoint accepted forbidden tag {rejected}"
            );
        }

        let mut bad_upload_len = to_vec(&AspisInstruction::UploadChunk {
            offset: 0,
            chunk: vec![1, 2, 3, 4],
        })
        .unwrap();
        bad_upload_len[5..9].copy_from_slice(&5u32.to_le_bytes());
        assert_eq!(
            process_v5_cu_probe_instruction(&owner, &[], &bad_upload_len),
            Err(ProgramError::InvalidInstructionData)
        );

        let mut bad_domain_len = to_vec(&AspisInstruction::InitializeAtomicPool {
            sequence: 7,
            anchor: [0u8; 32],
            domain_tag: b"devnet".to_vec(),
        })
        .unwrap();
        bad_domain_len[41..45].copy_from_slice(&7u32.to_le_bytes());
        assert_eq!(
            process_v5_cu_probe_instruction(&owner, &[], &bad_domain_len),
            Err(ProgramError::InvalidInstructionData)
        );
    }

    #[test]
    fn v5_feature_lifecycle_uploads_seals_and_closes_exact_proof() {
        let owner = id();
        let system_owner = Pubkey::default();
        let proof_key = Pubkey::new_unique();
        let authority_key = Pubkey::new_unique();
        let refund_key = Pubkey::new_unique();
        let mut proof_lamports = 500;
        let mut authority_lamports = 1;
        let mut refund_lamports = 10;
        let mut proof_data = [0u8; PROOF_ACCOUNT_HEADER_LEN + 4];
        let mut authority_data = [];
        let mut refund_data = [];
        let proof = make_account(
            &proof_key,
            &owner,
            &mut proof_lamports,
            &mut proof_data,
            true,
            true,
        );
        let authority = make_account(
            &authority_key,
            &system_owner,
            &mut authority_lamports,
            &mut authority_data,
            true,
            false,
        );
        let refund = make_account(
            &refund_key,
            &system_owner,
            &mut refund_lamports,
            &mut refund_data,
            true,
            true,
        );

        let init = to_vec(&AspisInstruction::InitProof { total_len: 4 }).unwrap();
        assert_eq!(
            process_v5_cu_probe_instruction(&owner, &[proof.clone(), authority.clone()], &init,),
            Ok(())
        );
        {
            let data = proof.try_borrow_data().unwrap();
            assert_eq!(&data[..4], &PROOF_ACCOUNT_MAGIC);
            assert_eq!(&data[4..8], &4u32.to_le_bytes());
            assert_eq!(&data[8..PROOF_ACCOUNT_HEADER_LEN], authority_key.as_ref());
        }

        let upload = to_vec(&AspisInstruction::UploadChunk {
            offset: 0,
            chunk: vec![1, 2, 3, 4],
        })
        .unwrap();
        assert_eq!(
            process_v5_cu_probe_instruction(&owner, &[proof.clone(), authority.clone()], &upload,),
            Ok(())
        );
        assert_eq!(
            &proof.try_borrow_data().unwrap()[PROOF_ACCOUNT_HEADER_LEN..],
            &[1, 2, 3, 4]
        );

        let before_bad_upload = proof.try_borrow_data().unwrap().to_vec();
        let bad_upload = to_vec(&AspisInstruction::UploadChunk {
            offset: 4,
            chunk: vec![5],
        })
        .unwrap();
        assert_eq!(
            process_v5_cu_probe_instruction(
                &owner,
                &[proof.clone(), authority.clone()],
                &bad_upload,
            ),
            Err(ProgramError::InvalidInstructionData)
        );
        assert_eq!(proof.try_borrow_data().unwrap().as_ref(), before_bad_upload);

        let finalize = to_vec(&AspisInstruction::FinalizeProof).unwrap();
        assert_eq!(
            process_v5_cu_probe_instruction(&owner, &[proof.clone(), authority.clone()], &finalize,),
            Ok(())
        );
        assert!(
            proof.try_borrow_data().unwrap()[8..PROOF_ACCOUNT_HEADER_LEN]
                .iter()
                .all(|byte| *byte == 0)
        );

        let sealed = proof.try_borrow_data().unwrap().to_vec();
        assert_eq!(
            process_v5_cu_probe_instruction(&owner, &[proof.clone(), authority.clone()], &upload,),
            Err(ProgramError::InvalidAccountData)
        );
        assert_eq!(
            process_v5_cu_probe_instruction(&owner, &[proof.clone(), authority.clone()], &finalize,),
            Err(ProgramError::InvalidAccountData)
        );
        assert_eq!(proof.try_borrow_data().unwrap().as_ref(), sealed);

        let close = to_vec(&AspisInstruction::CloseFinalizedProof).unwrap();
        assert_eq!(
            process_v5_cu_probe_instruction(&owner, &[proof.clone(), refund.clone()], &close),
            Ok(())
        );
        assert_eq!(proof.lamports(), 0);
        assert_eq!(refund.lamports(), 510);
        assert_ne!(&proof.try_borrow_data().unwrap()[..4], &PROOF_ACCOUNT_MAGIC);
    }

    #[test]
    fn v5_feature_lifecycle_initializes_runtime_domain_bound_pool_once() {
        let owner = id();
        let pool_key = Pubkey::new_unique();
        let mut pool_lamports = 500;
        let mut pool_data = [0u8; crate::atomic_payment::ATOMIC_POOL_STATE_LEN];
        let pool = make_account(
            &pool_key,
            &owner,
            &mut pool_lamports,
            &mut pool_data,
            true,
            true,
        );
        let wire = to_vec(&AspisInstruction::InitializeAtomicPool {
            sequence: 7,
            anchor: [0u8; 32],
            domain_tag: b"devnet".to_vec(),
        })
        .unwrap();
        assert_eq!(
            process_v5_cu_probe_instruction(&owner, &[pool.clone()], &wire),
            Ok(())
        );
        let state =
            crate::atomic_payment::AtomicPoolStateV2::decode(&pool.try_borrow_data().unwrap())
                .unwrap();
        assert_eq!(state.sequence, 7);
        assert_eq!(state.anchor, [0u8; 32]);
        assert_eq!(
            state.deployment_domain,
            aspis_statement::atomic_deployment_domain(
                crate::verify::sbf_hashv,
                &owner.to_bytes(),
                b"devnet",
            )
        );
        let initialized = pool.try_borrow_data().unwrap().to_vec();
        assert_eq!(
            process_v5_cu_probe_instruction(&owner, &[pool.clone()], &wire),
            Err(ProgramError::InvalidAccountData)
        );
        assert_eq!(pool.try_borrow_data().unwrap().as_ref(), initialized);
    }

    #[test]
    fn tag67_work_profile_and_relation_final_offsets_are_exact() {
        assert_eq!(STATE_ONLY_SPEND_BATCH_GRINDING_BITS, 37);
        assert_eq!(STATE_ONLY_SPEND_FOLD_GRINDING_BITS, [34, 33, 30, 25]);
        assert_eq!(STATE_ONLY_SPEND_GRINDING_BITS, 32);

        assert_eq!(V5_CU_PROBE_RELATION_FINAL_OFFSET, 11_048);
        assert_eq!(V5_CU_PROBE_BATCH_NONCE_RELATIVE_OFFSET, 32);
        assert_eq!(V5_CU_PROBE_BATCH_NONCE_OFFSET, 11_080);
        assert_eq!(V5_CU_PROBE_RELATION_FINAL_ZERO_TAIL_RELATIVE_OFFSET, 40);
        assert_eq!(V5_CU_PROBE_RELATION_FINAL_ZERO_TAIL_OFFSET, 11_088);
        assert_eq!(V5_CU_PROBE_RELATION_FINAL_ZERO_TAIL_BYTES, 24);
        assert_eq!(V5_CU_PROBE_PREFIX_OFFSET, 11_112);

        let mut data = vec![0u8; V5_CU_PROBE_PRIVATE_PROOF_OFFSET];
        data[..V5_CU_PROBE_ACCOUNT_MAGIC.len()].copy_from_slice(&V5_CU_PROBE_ACCOUNT_MAGIC);
        data[V5_CU_PROBE_BATCH_NONCE_OFFSET
            ..V5_CU_PROBE_BATCH_NONCE_OFFSET + V5_CU_PROBE_BATCH_NONCE_BYTES]
            .copy_from_slice(&WORK_TEST_VALID_NONCE.to_le_bytes());
        let parsed = parse_probe_data(&data).expect("exact mode-9 work layout");
        assert_eq!(parsed.v5_batch_nonce, WORK_TEST_VALID_NONCE);
        assert_eq!(
            verify_v5_relation_final_zero_tail(parsed.relation_final),
            Ok(())
        );
    }

    #[test]
    fn tag67_each_deployed_work_threshold_accepts_exactly_below_its_boundary() {
        let transcript = Transcript::new(threshold_work_hash);
        let deployed = [
            ("batch", STATE_ONLY_SPEND_BATCH_GRINDING_BITS),
            ("fold 0", STATE_ONLY_SPEND_FOLD_GRINDING_BITS[0]),
            ("fold 1", STATE_ONLY_SPEND_FOLD_GRINDING_BITS[1]),
            ("fold 2", STATE_ONLY_SPEND_FOLD_GRINDING_BITS[2]),
            ("fold 3", STATE_ONLY_SPEND_FOLD_GRINDING_BITS[3]),
            ("final", STATE_ONLY_SPEND_GRINDING_BITS),
        ];

        for (stage, bits) in deployed {
            let threshold = 1u64 << (64 - u32::from(bits));
            assert_eq!(
                require_real_v5_work(&transcript, threshold - 1, bits),
                Ok(()),
                "{stage} rejected the largest valid digest head at {bits} bits"
            );
            assert_eq!(
                require_real_v5_work(&transcript, threshold, bits),
                Err(ProgramError::InvalidAccountData),
                "{stage} accepted the first invalid digest head at {bits} bits"
            );
        }
    }

    #[test]
    fn tag67_relation_final_zero_tail_covers_every_remaining_byte() {
        let mut relation_final = [0u8; V5_CU_PROBE_RELATION_FINAL_BYTES];
        relation_final[V5_CU_PROBE_BATCH_NONCE_RELATIVE_OFFSET
            ..V5_CU_PROBE_RELATION_FINAL_ZERO_TAIL_RELATIVE_OFFSET]
            .copy_from_slice(&WORK_TEST_VALID_NONCE.to_le_bytes());
        assert_eq!(verify_v5_relation_final_zero_tail(&relation_final), Ok(()));
        for byte in V5_CU_PROBE_RELATION_FINAL_ZERO_TAIL_RELATIVE_OFFSET..relation_final.len() {
            relation_final[byte] = 1 << (byte & 7);
            assert_eq!(
                verify_v5_relation_final_zero_tail(&relation_final),
                Err(ProgramError::InvalidAccountData),
                "relative tail byte {byte}, absolute byte {}",
                V5_CU_PROBE_RELATION_FINAL_OFFSET + byte
            );
            relation_final[byte] = 0;
        }
        assert_eq!(
            verify_v5_relation_final_zero_tail(&relation_final[..relation_final.len() - 1]),
            Err(ProgramError::InvalidAccountData)
        );
    }

    #[test]
    fn tag67_new_outer_magic_rejects_the_old_workless_grammar() {
        assert_eq!(V5_CU_PROBE_ACCOUNT_MAGIC, *b"AV5CUP08");
        let mut data = vec![0u8; V5_CU_PROBE_PRIVATE_PROOF_OFFSET];
        data[..V5_CU_PROBE_ACCOUNT_MAGIC.len()].copy_from_slice(b"AV5CUP07");
        assert!(parse_probe_data(&data).is_err());
        data[..V5_CU_PROBE_ACCOUNT_MAGIC.len()].copy_from_slice(&V5_CU_PROBE_ACCOUNT_MAGIC);
        assert!(parse_probe_data(&data).is_ok());
    }

    #[test]
    fn tag67_batch_work_is_checked_before_its_dedicated_absorb() {
        let base = work_test_transcript();
        let mut actual = base.clone();
        check_and_absorb_real_v5_batch_nonce(&mut actual, WORK_TEST_VALID_NONCE).unwrap();
        let mut expected = base.clone();
        absorb_real_v5_batch_nonce(&mut expected, WORK_TEST_VALID_NONCE);
        assert_eq!(actual.diagnostic_state(), expected.diagnostic_state());

        let mut invalid = base;
        let before = invalid.diagnostic_state();
        assert_eq!(
            check_and_absorb_real_v5_batch_nonce(&mut invalid, WORK_TEST_VALID_NONCE + 1),
            Err(ProgramError::InvalidAccountData)
        );
        assert_eq!(invalid.diagnostic_state(), before);
    }

    #[test]
    fn tag67_fold_work_binds_round_records_and_rejects_permutation() {
        let base = work_test_transcript();
        let mut round_states = [[0u8; 32]; V5_CU_PROBE_RELATION_FOLDS];
        for round in 0..V5_CU_PROBE_RELATION_FOLDS {
            let mut actual = base.clone();
            check_and_absorb_real_v5_fold_nonce(&mut actual, round, WORK_TEST_VALID_NONCE).unwrap();
            let mut expected = base.clone();
            absorb_real_v5_fold_nonce(&mut expected, round, WORK_TEST_VALID_NONCE);
            assert_eq!(actual.diagnostic_state(), expected.diagnostic_state());
            round_states[round] = actual.diagnostic_state();

            let mut invalid = base.clone();
            let before = invalid.diagnostic_state();
            assert_eq!(
                check_and_absorb_real_v5_fold_nonce(&mut invalid, round, WORK_TEST_VALID_NONCE + 1,),
                Err(ProgramError::InvalidAccountData),
                "round {round}"
            );
            assert_eq!(invalid.diagnostic_state(), before);
        }
        for left in 0..V5_CU_PROBE_RELATION_FOLDS {
            for right in left + 1..V5_CU_PROBE_RELATION_FOLDS {
                assert_ne!(round_states[left], round_states[right]);
            }
        }

        let mut ordered = base.clone();
        check_and_absorb_real_v5_fold_nonce(&mut ordered, 0, WORK_TEST_VALID_NONCE).unwrap();
        check_and_absorb_real_v5_fold_nonce(&mut ordered, 1, WORK_TEST_VALID_NONCE).unwrap();
        let mut permuted = base;
        check_and_absorb_real_v5_fold_nonce(&mut permuted, 1, WORK_TEST_VALID_NONCE).unwrap();
        check_and_absorb_real_v5_fold_nonce(&mut permuted, 0, WORK_TEST_VALID_NONCE).unwrap();
        assert_ne!(ordered.diagnostic_state(), permuted.diagnostic_state());
    }

    #[test]
    fn tag67_final_work_cannot_substitute_for_batch_work() {
        let base = work_test_transcript();
        let mut batch = base.clone();
        check_and_absorb_real_v5_batch_nonce(&mut batch, WORK_TEST_VALID_NONCE).unwrap();
        let mut final_work = base.clone();
        check_and_absorb_real_v5_final_nonce(&mut final_work, WORK_TEST_VALID_NONCE).unwrap();
        assert_ne!(batch.diagnostic_state(), final_work.diagnostic_state());

        let mut invalid = base;
        let before = invalid.diagnostic_state();
        assert_eq!(
            check_and_absorb_real_v5_final_nonce(&mut invalid, WORK_TEST_VALID_NONCE ^ 1),
            Err(ProgramError::InvalidAccountData)
        );
        assert_eq!(invalid.diagnostic_state(), before);
    }

    fn verify_v5_reserved_tail_bytewise(bytes: &[u8]) -> ProgramResult {
        if bytes.len() == V5_CU_REAL_PREFIX_RESERVED_BYTES && bytes.iter().all(|&byte| byte == 0) {
            Ok(())
        } else {
            Err(ProgramError::InvalidAccountData)
        }
    }

    #[test]
    fn tag67_selected_good_boundary_rejects_every_out_of_range_selector_before_work() {
        for selected in 3..=u8::MAX {
            let mut derived = false;
            let mut evaluated = false;
            assert_eq!(
                checked_v5_selected_good_candidate(
                    selected,
                    |_| {
                        derived = true;
                        Ok(0u8)
                    },
                    |_, _| {
                        evaluated = true;
                        Ok(true)
                    },
                ),
                Err(ProgramError::InvalidAccountData),
                "selector {selected}"
            );
            assert!(!derived, "selector {selected} reached derivation");
            assert!(!evaluated, "selector {selected} reached Good evaluation");
        }
    }

    #[test]
    fn tag67_selected_good_accepts_even_when_earlier_candidates_are_good() {
        for (selected, evaluations) in [(1u8, [true, true, false]), (2u8, [true, true, true])] {
            let mut derived = [false; 3];
            let mut evaluated = [false; 3];
            assert_eq!(
                checked_v5_selected_good_candidate(
                    selected,
                    |candidate| {
                        let candidate = usize::from(candidate);
                        derived[candidate] = true;
                        Ok(candidate as u8)
                    },
                    |candidate, _| {
                        let candidate = usize::from(candidate);
                        evaluated[candidate] = true;
                        Ok(evaluations[candidate])
                    },
                ),
                Ok(selected)
            );
            assert_eq!(
                derived,
                core::array::from_fn(|candidate| candidate == usize::from(selected))
            );
            assert_eq!(
                evaluated,
                core::array::from_fn(|candidate| candidate == usize::from(selected))
            );
        }
    }

    #[test]
    fn tag67_selected_good_boundary_rejects_bad_selected_branch() {
        let evaluations = [true, false, true];
        let mut derived = [false; 3];
        let mut evaluated = [false; 3];
        assert_eq!(
            checked_v5_selected_good_candidate(
                1,
                |candidate| {
                    let candidate = usize::from(candidate);
                    derived[candidate] = true;
                    Ok(candidate as u8)
                },
                |candidate, _| {
                    let candidate = usize::from(candidate);
                    evaluated[candidate] = true;
                    Ok(evaluations[candidate])
                },
            ),
            Err(ProgramError::InvalidAccountData)
        );
        assert_eq!(derived, [false, true, false]);
        assert_eq!(evaluated, [false, true, false]);
    }

    #[test]
    fn tag67_live_helper_rejects_its_transcript_schedule_at_the_all_zero_point() {
        // Exercise the exact seam reached after prefix/relation authentication:
        // the verifier receives an already-replayed transcript and the
        // authenticated ten-round point, but no caller-supplied q18 schedule.
        let mut data = vec![0u8; V5_CU_PROBE_ACCOUNT_BYTES];
        data[..V5_CU_PROBE_ACCOUNT_MAGIC.len()].copy_from_slice(&V5_CU_PROBE_ACCOUNT_MAGIC);
        let final_polynomial = [QM31::ONE, QM31::ZERO, QM31::ONE, QM31::ZERO];
        for (index, value) in final_polynomial.iter().copied().enumerate() {
            let fixed_offset = V5_CU_PROBE_FINAL_COEFFICIENTS_OFFSET + index * QM31_BYTES;
            value.write_le_bytes(&mut data[fixed_offset..fixed_offset + QM31_BYTES]);
            let authenticated_offset = V5_CU_PROBE_RELATION_STRESS_OFFSET
                + V5_RELATION_STRESS_FINAL_OFFSET
                + index * QM31_BYTES;
            value
                .write_le_bytes(&mut data[authenticated_offset..authenticated_offset + QM31_BYTES]);
        }
        data[V5_CU_PROBE_FINAL_NONCE_OFFSET..V5_CU_PROBE_QUERY_SELECTOR_OFFSET]
            .copy_from_slice(&WORK_TEST_VALID_NONCE.to_le_bytes());
        data[V5_CU_PROBE_QUERY_SELECTOR_OFFSET] = 0;
        let parsed = parse_probe_data(&data).expect("exact fixed mode-9 prefix");

        let mut authenticated_transcript = Transcript::new(controlled_work_hash);
        authenticated_transcript.absorb(label::PROFILE, V5_REAL_HOST_TRANSCRIPT_DOMAIN);
        authenticated_transcript.absorb(label::M31_CIRCLE_BASIS, M31_CIRCLE_BASIS_DISCRIMINATOR);
        authenticated_transcript.absorb(label::STATEMENT, &[0x53; 32]);
        absorb_real_v5_round_root(
            &mut authenticated_transcript,
            0,
            &[0xc1; 32],
            &[0x51; V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_BYTES],
        );

        let (derived_final, queries) = derive_v5_complete_queries_for_selector_from_transcript(
            authenticated_transcript.clone(),
            &parsed,
            0,
        )
        .expect("derive the actual selector-zero transcript schedule");
        assert_eq!(derived_final, final_polynomial);
        let mut sorted_queries = queries;
        sorted_queries.sort_unstable();
        assert!(sorted_queries.windows(2).all(|pair| pair[0] != pair[1]));

        let all_zero_point = [QM31::ZERO; V5_CU_PROBE_RELATION_LOG_ROWS as usize];
        assert_eq!(
            good_gate_probe::candidate_is_good(&all_zero_point, queries),
            Some(false)
        );
        assert_eq!(
            derive_v5_selected_good_queries_from_transcript(
                authenticated_transcript,
                &parsed,
                &all_zero_point,
            ),
            Err(ProgramError::InvalidAccountData)
        );
    }

    #[test]
    fn tag67_selector_is_the_last_byte_of_the_fixed_mode9_prefix() {
        assert_eq!(V5_CU_PROBE_QUERY_SELECTOR_OFFSET, 19_135);
        assert_eq!(V5_CU_PROBE_PRIVATE_PROOF_OFFSET, 19_136);
        assert_eq!(
            V5_CU_PROBE_PRIVATE_PROOF_OFFSET,
            V5_CU_PROBE_QUERY_SELECTOR_OFFSET + 1
        );
        assert_eq!(V5_CU_PROBE_ACCOUNT_BYTES, V5_CU_PROBE_PRIVATE_PROOF_OFFSET);
    }

    #[test]
    fn tag67_selector_zero_derives_and_evaluates_only_zero() {
        let schedules = [
            [0x10u32; V5_CU_PROBE_QUERY_COUNT],
            [0x21u32; V5_CU_PROBE_QUERY_COUNT],
            [0x32u32; V5_CU_PROBE_QUERY_COUNT],
        ];
        let mut derived = [false; 3];
        let mut evaluated = [false; 3];
        assert_eq!(
            checked_v5_selected_good_candidate(
                0,
                |candidate| {
                    let candidate = usize::from(candidate);
                    derived[candidate] = true;
                    Ok(schedules[candidate])
                },
                |candidate, schedule| {
                    let candidate = usize::from(candidate);
                    evaluated[candidate] = true;
                    assert_eq!(*schedule, schedules[candidate]);
                    Ok(true)
                },
            ),
            Ok(schedules[0])
        );
        assert_eq!(derived, [true, false, false]);
        assert_eq!(evaluated, [true, false, false]);
    }

    #[test]
    fn tag67_selected_queries_equal_the_prederived_branch() {
        let schedules = [
            [0x40u32; V5_CU_PROBE_QUERY_COUNT],
            [0x51u32; V5_CU_PROBE_QUERY_COUNT],
            [0x62u32; V5_CU_PROBE_QUERY_COUNT],
        ];
        let evaluations = [false, false, true];
        let mut derived = [false; 3];
        let mut evaluated = [false; 3];
        let selected = checked_v5_selected_good_candidate(
            2,
            |candidate| {
                let candidate = usize::from(candidate);
                derived[candidate] = true;
                Ok(schedules[candidate])
            },
            |candidate, schedule| {
                let candidate = usize::from(candidate);
                evaluated[candidate] = true;
                assert_eq!(*schedule, schedules[candidate]);
                Ok(evaluations[candidate])
            },
        );
        assert_eq!(selected, Ok(schedules[2]));
        assert_eq!(derived, [false, false, true]);
        assert_eq!(evaluated, [false, false, true]);
    }

    #[test]
    fn tag67_evaluator_is_truth_table_equivalent_to_selected_good() {
        let mut bits = 0u8;
        while bits < 8 {
            let evaluations = [bits & 1 != 0, bits & 2 != 0, bits & 4 != 0];
            let mut selected = 0u8;
            while selected < 3 {
                let mut derived = [false; 3];
                let mut evaluated = [false; 3];
                let actual = checked_v5_selected_good_candidate(
                    selected,
                    |candidate| {
                        let index = usize::from(candidate);
                        derived[index] = true;
                        Ok(candidate)
                    },
                    |candidate, _| {
                        let index = usize::from(candidate);
                        evaluated[index] = true;
                        Ok(evaluations[index])
                    },
                );
                let expected = evaluations[usize::from(selected)];
                assert_eq!(
                    actual,
                    if expected {
                        Ok(selected)
                    } else {
                        Err(ProgramError::InvalidAccountData)
                    },
                    "selector {selected}, bits {bits:03b}"
                );
                assert_eq!(
                    derived,
                    core::array::from_fn(|candidate| candidate == usize::from(selected))
                );
                assert_eq!(
                    evaluated,
                    core::array::from_fn(|candidate| candidate == usize::from(selected))
                );
                selected += 1;
            }
            bits += 1;
        }
    }

    #[test]
    fn tag67_rejects_one_byte_after_exact_declared_proof_body() {
        let proof_body = *b"exact-v5-body";
        let mut account = vec![0u8; PROOF_ACCOUNT_HEADER_LEN + proof_body.len()];
        account[..4].copy_from_slice(&PROOF_ACCOUNT_MAGIC);
        account[4..8].copy_from_slice(&(proof_body.len() as u32).to_le_bytes());
        account[PROOF_ACCOUNT_HEADER_LEN..].copy_from_slice(&proof_body);

        assert_eq!(
            exact_uploaded_v5_proof_body(&account),
            Ok(proof_body.as_slice())
        );
        account.push(0x5a);
        assert_eq!(
            exact_uploaded_v5_proof_body(&account),
            Err(ProgramError::InvalidAccountData)
        );
    }

    #[test]
    fn wire_prefix_header_predicate_matches_exact_accepted_grammar() {
        let fixed_header = [
            b'A', b'V', b'5', b'P', b'F', b'X', b'0', b'3', 3, 0, 0, 1, 192, 0, 16, 3, 1, 2, 3, 10,
            27, 4, 0,
        ];
        let mut prefix = [0u8; V5_CU_REAL_PREFIX_ACCEPTED_BYTES];
        prefix[..fixed_header.len()].copy_from_slice(&fixed_header);
        assert!(v5_wire_prefix_header_is_valid(&prefix));

        for index in 0..fixed_header.len() {
            prefix[index] ^= 1;
            assert!(
                !v5_wire_prefix_header_is_valid(&prefix),
                "mutated fixed-header byte {index}"
            );
            prefix[index] ^= 1;
        }

        prefix[fixed_header.len()] = 0xa5;
        assert!(v5_wire_prefix_header_is_valid(&prefix));
        assert!(!v5_wire_prefix_header_is_valid(&prefix[..prefix.len() - 1]));
        let extended = [0u8; V5_CU_REAL_PREFIX_ACCEPTED_BYTES + 1];
        assert!(!v5_wire_prefix_header_is_valid(&extended));
    }

    #[test]
    fn reserved_tail_word_scan_matches_bytewise_reference_exhaustively() {
        let mut tail = [0u8; V5_CU_REAL_PREFIX_RESERVED_BYTES];
        assert_eq!(verify_v5_reserved_tail(&tail), Ok(()));
        assert_eq!(
            verify_v5_reserved_tail(&tail),
            verify_v5_reserved_tail_bytewise(&tail)
        );

        // Every one of the 400 byte positions independently carries one
        // nonzero bit, covering every possible early-exit location.
        for byte in 0..tail.len() {
            tail[byte] = 1 << (byte & 7);
            assert_eq!(
                verify_v5_reserved_tail(&tail),
                verify_v5_reserved_tail_bytewise(&tail),
                "one-hot byte {byte}"
            );
            tail[byte] = 0;
        }

        let extremes = [
            1u64,
            1u64 << 63,
            u64::MAX,
            0xaa55_aa55_aa55_aa55,
            0x55aa_55aa_55aa_55aa,
        ];
        for word in 0..V5_CU_REAL_PREFIX_RESERVED_BYTES / 8 {
            for (extreme, value) in extremes.iter().copied().enumerate() {
                tail[word * 8..word * 8 + 8].copy_from_slice(&value.to_le_bytes());
                assert_eq!(
                    verify_v5_reserved_tail(&tail),
                    verify_v5_reserved_tail_bytewise(&tail),
                    "word {word} extreme {extreme}"
                );
                tail[word * 8..word * 8 + 8].fill(0);
            }
        }

        let mut random = 0x7265_7365_7276_6564u64;
        for sample in 0..256 {
            for word in 0..V5_CU_REAL_PREFIX_RESERVED_BYTES / 8 {
                random ^= random << 13;
                random ^= random >> 7;
                random ^= random << 17;
                tail[word * 8..word * 8 + 8].copy_from_slice(&random.to_le_bytes());
            }
            assert_eq!(
                verify_v5_reserved_tail(&tail),
                verify_v5_reserved_tail_bytewise(&tail),
                "random sample {sample}"
            );
        }

        let truncated = &tail[..V5_CU_REAL_PREFIX_RESERVED_BYTES - 1];
        assert_eq!(
            verify_v5_reserved_tail(truncated),
            verify_v5_reserved_tail_bytewise(truncated)
        );
        assert_eq!(
            verify_v5_reserved_tail(truncated),
            Err(ProgramError::InvalidAccountData)
        );
        let extended = [0u8; V5_CU_REAL_PREFIX_RESERVED_BYTES + 1];
        assert_eq!(
            verify_v5_reserved_tail(&extended),
            verify_v5_reserved_tail_bytewise(&extended)
        );
        assert_eq!(
            verify_v5_reserved_tail(&extended),
            Err(ProgramError::InvalidAccountData)
        );
    }

    #[test]
    fn public_fs_salts_use_first_160_reserved_bytes_and_allow_zero() {
        assert_eq!(V5_CU_REAL_PREFIX_PUBLIC_FS_SALTS_OFFSET, 5_863);
        assert_eq!(V5_CU_REAL_PREFIX_PUBLIC_FS_SALTS_BYTES, 160);
        assert_eq!(V5_CU_REAL_PREFIX_ZERO_RESERVE_OFFSET, 6_023);

        let mut prefix = [0u8; V5_WIRE_PREFIX_BYTES];
        for section in 0..V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_COUNT {
            let start = V5_CU_REAL_PREFIX_PUBLIC_FS_SALTS_OFFSET
                + section * V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_BYTES;
            prefix[start..start + V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_BYTES].fill(section as u8 + 1);
        }
        for section in 0..V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_COUNT {
            assert_eq!(
                v5_public_fs_salt(&prefix, section),
                &[section as u8 + 1; V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_BYTES]
            );
        }
        assert_eq!(
            verify_v5_reserved_tail(&prefix[V5_CU_REAL_PREFIX_ZERO_RESERVE_OFFSET..]),
            Ok(())
        );

        prefix[V5_CU_REAL_PREFIX_PUBLIC_FS_SALTS_OFFSET..V5_CU_REAL_PREFIX_ZERO_RESERVE_OFFSET]
            .fill(0);
        for section in 0..V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_COUNT {
            assert_eq!(
                v5_public_fs_salt(&prefix, section),
                &[0u8; V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_BYTES]
            );
        }
    }

    #[test]
    fn real_prefix_root_parser_reads_exact_c1_and_c2_windows() {
        let mut prefix = [0u8; V5_WIRE_PREFIX_BYTES];
        let c1 = core::array::from_fn(|index| 0x10u8.wrapping_add(index as u8));
        let c2 = core::array::from_fn(|index| 0x90u8.wrapping_add(index as u8));
        prefix[V5_CU_REAL_PREFIX_C1_ROOT_OFFSET..V5_CU_REAL_PREFIX_C2_ROOT_OFFSET]
            .copy_from_slice(&c1);
        prefix[V5_CU_REAL_PREFIX_C2_ROOT_OFFSET..V5_CU_REAL_PREFIX_INITIAL_B_CLAIM_OFFSET]
            .copy_from_slice(&c2);

        assert_eq!(
            real_v5_prefix_root(&prefix, V5_CU_REAL_PREFIX_C1_ROOT_OFFSET),
            &c1
        );
        assert_eq!(
            real_v5_prefix_root(&prefix, V5_CU_REAL_PREFIX_C2_ROOT_OFFSET),
            &c2
        );
        assert_ne!(
            real_v5_prefix_root(&prefix, V5_CU_REAL_PREFIX_C1_ROOT_OFFSET),
            real_v5_prefix_root(&prefix, V5_CU_REAL_PREFIX_C2_ROOT_OFFSET)
        );
    }

    #[test]
    fn private_root_parser_reads_exact_five_windows() {
        let mut data = vec![0u8; V5_CU_PROBE_PRIVATE_PROOF_OFFSET];
        let expected = V5PrivateOpeningRoots {
            c1: [0x11; 32],
            c2: [0x22; 32],
            later: [[0x33; 32], [0x44; 32], [0x55; 32]],
        };
        let roots = [
            expected.c1,
            expected.c2,
            expected.later[0],
            expected.later[1],
            expected.later[2],
        ];
        for (index, root) in roots.iter().enumerate() {
            let start = V5_CU_PROBE_PRIVATE_ROOTS_OFFSET + index * 32;
            data[start..start + 32].copy_from_slice(root);
        }

        assert_eq!(parse_v5_private_roots(&data), expected);
    }

    #[test]
    fn wire_prefix_parser_reads_exact_account_window() {
        let mut data = vec![0u8; V5_CU_PROBE_PRIVATE_PROOF_OFFSET];
        for (index, byte) in data
            [V5_CU_PROBE_PREFIX_OFFSET..V5_CU_PROBE_ATOMIC_TERMINAL_CONTEXT_OFFSET]
            .iter_mut()
            .enumerate()
        {
            *byte = index.wrapping_mul(29).wrapping_add(7) as u8;
        }
        assert_eq!(
            parse_v5_wire_prefix(&data),
            &data[V5_CU_PROBE_PREFIX_OFFSET..V5_CU_PROBE_ATOMIC_TERMINAL_CONTEXT_OFFSET]
        );
        assert_eq!(parse_v5_wire_prefix(&data).len(), V5_WIRE_PREFIX_BYTES);
    }

    #[test]
    fn prefix_private_root_binding_checks_both_roots() {
        let mut prefix = [0u8; V5_WIRE_PREFIX_BYTES];
        let private_roots = V5PrivateOpeningRoots {
            c1: [0x16; 32],
            c2: [0x27; 32],
            later: [[0x38; 32], [0x49; 32], [0x5a; 32]],
        };
        prefix[V5_CU_REAL_PREFIX_C1_ROOT_OFFSET..V5_CU_REAL_PREFIX_C2_ROOT_OFFSET]
            .copy_from_slice(&private_roots.c1);
        prefix[V5_CU_REAL_PREFIX_C2_ROOT_OFFSET..V5_CU_REAL_PREFIX_INITIAL_B_CLAIM_OFFSET]
            .copy_from_slice(&private_roots.c2);
        assert!(v5_prefix_roots_match_private(&prefix, &private_roots));

        prefix[V5_CU_REAL_PREFIX_C1_ROOT_OFFSET] ^= 1;
        assert!(!v5_prefix_roots_match_private(&prefix, &private_roots));
        prefix[V5_CU_REAL_PREFIX_C1_ROOT_OFFSET] ^= 1;
        prefix[V5_CU_REAL_PREFIX_C2_ROOT_OFFSET] ^= 1;
        assert!(!v5_prefix_roots_match_private(&prefix, &private_roots));
    }

    #[test]
    fn public_fs_root_records_bind_exact_root_and_salt_bytes() {
        let root = core::array::from_fn(|index| 0x40u8.wrapping_add(index as u8));
        let salt = core::array::from_fn(|index| 0xa0u8.wrapping_add(index as u8));

        let round = real_v5_round_root_record(2, &root, &salt);
        let round_input = real_v5_round_root_absorb_input(2, &root, &salt);
        assert_eq!(round_input, (label::M31_CIRCLE_ROUND_ROOT, round));
        assert_eq!(round[0], 2);
        assert_eq!(&round[1..33], &root);
        assert_eq!(&round[33..], &salt);

        let c2 = real_v5_c2_root_record(&root, &salt);
        let c2_input = real_v5_c2_root_absorb_input(&root, &salt);
        assert_eq!(c2_input, (label::M31_CIRCLE_C2_ROOT, c2));
        assert_eq!(&c2[..32], &root);
        assert_eq!(&c2[32..], &salt);

        let wrong_root = [0x41; 32];
        let wrong_salt = [0xa1; 32];
        assert_ne!(real_v5_round_root_record(2, &wrong_root, &salt), round);
        assert_ne!(real_v5_round_root_record(2, &root, &wrong_salt), round);
        assert_ne!(real_v5_round_root_record(1, &root, &salt), round);
        assert_ne!(real_v5_c2_root_record(&wrong_root, &salt), c2);
        assert_ne!(real_v5_c2_root_record(&root, &wrong_salt), c2);
    }

    fn next_m31(state: &mut u64) -> M31 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        M31((*state % u64::from(P)) as u32)
    }

    fn next_qm31(state: &mut u64) -> QM31 {
        QM31 {
            c0: aspis_core::field::CM31::new(next_m31(state), next_m31(state)),
            c1: aspis_core::field::CM31::new(next_m31(state), next_m31(state)),
        }
    }

    fn statement_digest_reference(
        statement: &AtomicPaymentStatementV4,
        digest: &[u8; 32],
    ) -> ProgramResult {
        let expected = atomic_payment_statement_digest_v4(statement, crate::verify::sbf_hashv)
            .map_err(|_| ProgramError::InvalidAccountData)?;
        if &expected == digest {
            Ok(())
        } else {
            Err(ProgramError::InvalidAccountData)
        }
    }

    fn digest_words(seed: u32) -> [M31; 8] {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn digest_test_statement() -> AtomicPaymentStatementV4 {
        AtomicPaymentStatementV4 {
            pool: [9; 32],
            sequence: 7,
            spend: SpendPublic {
                anchor: digest_words(10),
                nullifier: digest_words(20),
                output_commitment: digest_words(30),
                asset_id: M31(40),
                fee: 50,
            },
            output_anchor: digest_words(60),
            deployment_domain: [70; 32],
        }
    }

    #[test]
    fn prefix_digest_check_subsumes_removed_outer_check_for_every_statement_field() {
        let statement = digest_test_statement();
        let digest = atomic_payment_statement_digest_v4(&statement, crate::verify::sbf_hashv)
            .expect("canonical statement");
        let payload = encode_atomic_payment_statement_v4(&statement).unwrap();
        assert_eq!(
            digest,
            crate::verify::sbf_hashv(&[ATOMIC_PAYMENT_STATEMENT_DOMAIN, &payload])
        );
        assert_eq!(
            verify_live_statement_digest(&statement, &digest, crate::verify::sbf_hashv),
            statement_digest_reference(&statement, &digest)
        );
        assert_eq!(statement_digest_reference(&statement, &digest), Ok(()));

        let mut mutations = Vec::new();
        let mut mutated = statement.clone();
        mutated.pool[0] ^= 1;
        mutations.push(("pool", mutated));
        let mut mutated = statement.clone();
        mutated.sequence += 1;
        mutations.push(("sequence", mutated));
        let mut mutated = statement.clone();
        mutated.spend.anchor[0] = M31(mutated.spend.anchor[0].0 + 1);
        mutations.push(("anchor", mutated));
        let mut mutated = statement.clone();
        mutated.spend.nullifier[0] = M31(mutated.spend.nullifier[0].0 + 1);
        mutations.push(("nullifier", mutated));
        let mut mutated = statement.clone();
        mutated.spend.output_commitment[0] = M31(mutated.spend.output_commitment[0].0 + 1);
        mutations.push(("output_commitment", mutated));
        let mut mutated = statement.clone();
        mutated.spend.asset_id = M31(mutated.spend.asset_id.0 + 1);
        mutations.push(("asset_id", mutated));
        let mut mutated = statement.clone();
        mutated.spend.fee += 1;
        mutations.push(("fee", mutated));
        let mut mutated = statement.clone();
        mutated.output_anchor[0] = M31(mutated.output_anchor[0].0 + 1);
        mutations.push(("output_anchor", mutated));
        let mut mutated = statement.clone();
        mutated.deployment_domain[0] ^= 1;
        mutations.push(("deployment_domain", mutated));

        for (field, mutated) in mutations {
            let prefix_result =
                verify_live_statement_digest(&mutated, &digest, crate::verify::sbf_hashv);
            let removed_outer_result = statement_digest_reference(&mutated, &digest);
            assert_eq!(prefix_result, removed_outer_result, "field {field}");
            assert_eq!(
                prefix_result,
                Err(ProgramError::InvalidAccountData),
                "field {field}"
            );

            let mutated_digest =
                atomic_payment_statement_digest_v4(&mutated, crate::verify::sbf_hashv).unwrap();
            assert_ne!(mutated_digest, digest, "field {field}");
            assert_eq!(
                verify_live_statement_digest(&mutated, &mutated_digest, crate::verify::sbf_hashv),
                statement_digest_reference(&mutated, &mutated_digest),
                "field {field} matched digest"
            );
            assert_eq!(
                statement_digest_reference(&mutated, &mutated_digest),
                Ok(()),
                "field {field} matched digest"
            );
        }

        for (case, invalid) in [
            {
                let mut invalid = statement.clone();
                invalid.spend.asset_id = M31(P);
                ("noncanonical asset", invalid)
            },
            {
                let mut invalid = statement;
                invalid.spend.fee = VALUE_LIMIT;
                ("out-of-range fee", invalid)
            },
        ] {
            assert_eq!(
                verify_live_statement_digest(&invalid, &digest, crate::verify::sbf_hashv),
                statement_digest_reference(&invalid, &digest),
                "case {case}"
            );
            assert_eq!(
                statement_digest_reference(&invalid, &digest),
                Err(ProgramError::InvalidAccountData),
                "case {case}"
            );
        }
    }

    fn account_data() -> Vec<u8> {
        let mut state = 0x5a17_9c31_26f0_0012;
        let mut data = vec![0u8; V5_CU_PROBE_DIAGNOSTIC_ACCOUNT_BYTES];
        data[..V5_CU_PROBE_ACCOUNT_MAGIC.len()].copy_from_slice(&V5_CU_PROBE_ACCOUNT_MAGIC);
        next_qm31(&mut state).write_le_bytes(
            &mut data[V5_CU_PROBE_GAMMA_OFFSET..V5_CU_PROBE_GAMMA_OFFSET + QM31_BYTES],
        );
        for query in 0..V5_CU_PROBE_QUERY_COUNT {
            let production_start =
                V5_CU_PROBE_PRODUCTION_C1_OFFSET + query * V5_CU_PROBE_PRODUCTION_C1_RECORD_BYTES;
            for slot in 0..STATE_ONLY_FIBER_SLOTS {
                for column in 0..V5_CU_PROBE_PRODUCTION_C1_COLUMNS {
                    let value = next_m31(&mut state);
                    let offset = production_start
                        + (slot * V5_CU_PROBE_PRODUCTION_C1_COLUMNS + column) * M31_BYTES;
                    data[offset..offset + M31_BYTES].copy_from_slice(&value.to_le_bytes());
                }
            }
            for salt in 0..STATE_ONLY_PRIVATE_LEAF_SALT_BYTES {
                data[production_start + V5_CU_PROBE_PRODUCTION_C1_VALUE_BYTES + salt] =
                    next_m31(&mut state).0 as u8;
            }
            let candidate_start =
                V5_CU_PROBE_CANDIDATE_C1_OFFSET + query * V5_CU_PROBE_CANDIDATE_C1_RECORD_BYTES;
            for slot in 0..STATE_ONLY_FIBER_SLOTS {
                for column in 0..V5_CU_PROBE_CANDIDATE_C1_COLUMNS {
                    let source = production_start
                        + (slot * V5_CU_PROBE_PRODUCTION_C1_COLUMNS + column) * M31_BYTES;
                    let target = candidate_start
                        + (slot * V5_CU_PROBE_CANDIDATE_C1_COLUMNS + column) * M31_BYTES;
                    let word = data[source..source + M31_BYTES].to_vec();
                    data[target..target + M31_BYTES].copy_from_slice(&word);
                }
            }
            let salt = data[production_start + V5_CU_PROBE_PRODUCTION_C1_VALUE_BYTES
                ..production_start + V5_CU_PROBE_PRODUCTION_C1_RECORD_BYTES]
                .to_vec();
            data[candidate_start + V5_CU_PROBE_CANDIDATE_C1_VALUE_BYTES
                ..candidate_start + V5_CU_PROBE_CANDIDATE_C1_RECORD_BYTES]
                .copy_from_slice(&salt);

            let c2_start = V5_CU_PROBE_C2_OFFSET + query * V5_CU_PROBE_C2_RECORD_BYTES;
            for helper in 0..V5_CU_PROBE_C2_COLUMNS {
                for slot in 0..STATE_ONLY_FIBER_SLOTS {
                    let offset = c2_start + (helper * STATE_ONLY_FIBER_SLOTS + slot) * QM31_BYTES;
                    next_qm31(&mut state).write_le_bytes(&mut data[offset..offset + QM31_BYTES]);
                }
            }
            for salt in 0..STATE_ONLY_PRIVATE_LEAF_SALT_BYTES {
                data[c2_start + V5_CU_PROBE_C2_VALUE_BYTES + salt] = next_m31(&mut state).0 as u8;
            }
        }
        for index in 0..V5_CU_PROBE_RELATION_POINTS {
            let offset = V5_CU_PROBE_RELATION_SCALES_OFFSET + index * QM31_BYTES;
            next_qm31(&mut state).write_le_bytes(&mut data[offset..offset + QM31_BYTES]);
        }
        for index in 0..V5_CU_PROBE_RELATION_POINTS * V5_CU_PROBE_RELATION_LOG_ROWS as usize {
            let offset = V5_CU_PROBE_RELATION_POINTS_OFFSET + index * QM31_BYTES;
            next_qm31(&mut state).write_le_bytes(&mut data[offset..offset + QM31_BYTES]);
        }
        for index in 0..V5_CU_PROBE_RELATION_CLAIMS_PER_LANE * V5_CU_PROBE_RELATION_LANES {
            let offset = V5_CU_PROBE_RELATION_CLAIMS_OFFSET + index * QM31_BYTES;
            next_qm31(&mut state).write_le_bytes(&mut data[offset..offset + QM31_BYTES]);
        }
        for index in 0..V5_CU_PROBE_RELATION_FOLDS {
            let offset = V5_CU_PROBE_RELATION_ALPHAS_OFFSET + index * QM31_BYTES;
            next_qm31(&mut state).write_le_bytes(&mut data[offset..offset + QM31_BYTES]);
        }
        for index in 0..V5_CU_PROBE_RELATION_FINAL_VALUES {
            let offset = V5_CU_PROBE_RELATION_FINAL_OFFSET + index * QM31_BYTES;
            next_qm31(&mut state).write_le_bytes(&mut data[offset..offset + QM31_BYTES]);
        }
        let prefix = wire_skeleton::build_deterministic_synthetic_v5_wire(crate::verify::sbf_hashv);
        data[V5_CU_PROBE_PREFIX_OFFSET..V5_CU_PROBE_ATOMIC_TERMINAL_CONTEXT_OFFSET]
            .copy_from_slice(&prefix);
        data[V5_CU_PROBE_RELATION_CLAIMS_OFFSET..V5_CU_PROBE_RELATION_ALPHAS_OFFSET]
            .copy_from_slice(
                &prefix[wire_skeleton::V5_WIRE_OPENINGS_OFFSET
                    ..wire_skeleton::V5_WIRE_TERMINALS_OFFSET],
            );
        data
    }

    fn literal<const C1_COLUMNS: usize, const TOTAL_COLUMNS: usize>(
        gamma: QM31,
        c1: &[u8],
        c2: &[u8],
    ) -> [QM31; STATE_ONLY_FIBER_SLOTS] {
        let powers = qm31_power_table::<TOTAL_COLUMNS>(gamma);
        let mut result = [QM31::ZERO; STATE_ONLY_FIBER_SLOTS];
        for (slot, output) in result.iter_mut().enumerate() {
            for column in 0..C1_COLUMNS {
                let offset = (slot * C1_COLUMNS + column) * M31_BYTES;
                let value =
                    M31::from_le_bytes(c1[offset..offset + M31_BYTES].try_into().unwrap()).unwrap();
                *output = output.add(powers[column].mul_m31(value));
            }
            for helper in 0..V5_CU_PROBE_C2_COLUMNS {
                let offset = (helper * STATE_ONLY_FIBER_SLOTS + slot) * QM31_BYTES;
                let value = QM31::from_le_bytes(&c2[offset..offset + QM31_BYTES]).unwrap();
                *output = output.add(powers[C1_COLUMNS + helper].mul(value));
            }
        }
        result
    }

    fn literal_structured_b_covector(
        point: &[QM31; V5_CU_PROBE_RELATION_LOG_ROWS as usize],
        scale: QM31,
    ) -> Vec<QM31> {
        let half = QM31::ONE.half();
        let mut values = vec![QM31::ZERO; V5_CU_PROBE_RELATION_DENSE_VALUES];
        for (round, (&selector, &z)) in V5_CU_PROBE_B_BLOCK_SELECTORS
            .iter()
            .zip(point.iter())
            .enumerate()
        {
            let block_scale = scale.mul(half.pow((9 - round) as u64));
            let mut power = QM31::ONE;
            let start = usize::from(selector) * V5_CU_PROBE_B_BLOCK_ROWS;
            for degree in 0..28 {
                values[start + degree] = block_scale.mul(power);
                power = power.mul(z);
            }
        }
        values[V5_CU_PROBE_B_INITIAL_STATE_ROW] =
            values[V5_CU_PROBE_B_INITIAL_STATE_ROW].add(scale.mul(half.pow(10)));
        values
    }

    #[test]
    fn every_slot_matches_production_generic_fused_and_literal_paths() {
        let data = account_data();
        let parsed = parse_diagnostic_probe_data(&data).unwrap();
        let production_powers = StateOnlySpendQueryPowers::new(parsed.gamma);
        let generic26 = prepare_generic26(parsed.gamma);
        let generic16 = prepare_generic16(parsed.gamma);
        for query in 0..V5_CU_PROBE_QUERY_COUNT {
            let c1_26 = parsed.production_c1_record(query).unwrap();
            let c1_16 = parsed.candidate_c1_record(query);
            let c2 = parsed.c2_record(query);
            let production = gamma_combine_state_only_spend_layer0_prepared(
                &c1_26[..V5_CU_PROBE_PRODUCTION_C1_VALUE_BYTES],
                &c2[..V5_CU_PROBE_C2_VALUE_BYTES],
                &production_powers,
            )
            .unwrap();
            let generic26_nonfused = generic_combine::<V5_CU_PROBE_PRODUCTION_C1_COLUMNS, false>(
                &c1_26[..V5_CU_PROBE_PRODUCTION_C1_VALUE_BYTES],
                &c2[..V5_CU_PROBE_C2_VALUE_BYTES],
                &generic26,
            )
            .unwrap();
            let generic26_fused = generic_combine::<V5_CU_PROBE_PRODUCTION_C1_COLUMNS, true>(
                &c1_26[..V5_CU_PROBE_PRODUCTION_C1_VALUE_BYTES],
                &c2[..V5_CU_PROBE_C2_VALUE_BYTES],
                &generic26,
            )
            .unwrap();
            let literal26 = literal::<V5_CU_PROBE_PRODUCTION_C1_COLUMNS, 29>(
                parsed.gamma,
                &c1_26[..V5_CU_PROBE_PRODUCTION_C1_VALUE_BYTES],
                &c2[..V5_CU_PROBE_C2_VALUE_BYTES],
            );
            assert_eq!(production, generic26_nonfused, "query {query}");
            assert_eq!(generic26_nonfused, generic26_fused, "query {query}");
            assert_eq!(generic26_fused, literal26, "query {query}");

            let generic16_nonfused = generic_combine::<V5_CU_PROBE_CANDIDATE_C1_COLUMNS, false>(
                &c1_16[..V5_CU_PROBE_CANDIDATE_C1_VALUE_BYTES],
                &c2[..V5_CU_PROBE_C2_VALUE_BYTES],
                &generic16,
            )
            .unwrap();
            let generic16_fused = generic_combine::<V5_CU_PROBE_CANDIDATE_C1_COLUMNS, true>(
                &c1_16[..V5_CU_PROBE_CANDIDATE_C1_VALUE_BYTES],
                &c2[..V5_CU_PROBE_C2_VALUE_BYTES],
                &generic16,
            )
            .unwrap();
            let literal16 = literal::<V5_CU_PROBE_CANDIDATE_C1_COLUMNS, 19>(
                parsed.gamma,
                &c1_16[..V5_CU_PROBE_CANDIDATE_C1_VALUE_BYTES],
                &c2[..V5_CU_PROBE_C2_VALUE_BYTES],
            );
            assert_eq!(generic16_nonfused, generic16_fused, "query {query}");
            assert_eq!(generic16_fused, literal16, "query {query}");
        }
    }

    #[test]
    fn frozen_atomic_v3_inactive_groups_match_generator_and_every_dual_fold() {
        let generated = atomic_state_only_copy_inactive_row_masks_v3();
        for high in 0..64 {
            let group = usize::from(V5_ATOMIC_V3_INACTIVE_ROW_GROUPS[high]);
            assert_eq!(V5_ATOMIC_V3_INACTIVE_GROUP_MASKS[group], generated[high]);
            for low in 0..16 {
                let expected = generated[high] & (1 << low) != 0;
                let prepared = V5_ATOMIC_V3_INACTIVE_GROUP_MASKS[group] & (1 << low) != 0;
                assert_eq!(prepared, expected, "row {}", 16 * high + low);
            }
        }

        for high in 0..64 {
            let mut mutated = V5_ATOMIC_V3_INACTIVE_ROW_GROUPS;
            mutated[high] = (mutated[high] + 1) % V5_ATOMIC_V3_INACTIVE_GROUP_MASKS.len() as u8;
            let original_mask = generated[high];
            let mutated_mask = V5_ATOMIC_V3_INACTIVE_GROUP_MASKS[usize::from(mutated[high])];
            assert_ne!(
                mutated_mask, original_mask,
                "row-group mutation {high} must be observable"
            );
            let changed_low = (original_mask ^ mutated_mask).trailing_zeros() as usize;
            let mut mutated_weights = WeightAccumulator::empty(V5_CU_PROBE_RELATION_LOG_ROWS);
            mutated_weights
                .add_grouped_64x16_binary_masks_deferred_prepared(
                    &mutated,
                    &V5_ATOMIC_V3_INACTIVE_GROUP_MASKS,
                )
                .unwrap();
            assert_ne!(
                mutated_weights.weight_at((16 * high + changed_low) as u32),
                if original_mask & (1 << changed_low) == 0 {
                    QM31::ZERO
                } else {
                    QM31::ONE
                },
                "row-group mutation {high} must change the prepared covector"
            );
        }
        for group in 0..V5_ATOMIC_V3_INACTIVE_GROUP_MASKS.len() {
            let high = V5_ATOMIC_V3_INACTIVE_ROW_GROUPS
                .iter()
                .position(|&candidate| usize::from(candidate) == group)
                .expect("every frozen mask group is used");
            for bit in 0..16 {
                let mut mutated = V5_ATOMIC_V3_INACTIVE_GROUP_MASKS;
                mutated[group] ^= 1 << bit;
                let mut mutated_weights = WeightAccumulator::empty(V5_CU_PROBE_RELATION_LOG_ROWS);
                mutated_weights
                    .add_grouped_64x16_binary_masks_deferred_prepared(
                        &V5_ATOMIC_V3_INACTIVE_ROW_GROUPS,
                        &mutated,
                    )
                    .unwrap();
                assert_ne!(
                    mutated_weights.weight_at((16 * high + bit) as u32),
                    if generated[high] & (1 << bit) == 0 {
                        QM31::ZERO
                    } else {
                        QM31::ONE
                    },
                    "mask mutation group={group} bit={bit} must change the prepared covector"
                );
            }
        }

        let mut invalid_groups = V5_ATOMIC_V3_INACTIVE_ROW_GROUPS;
        invalid_groups[0] = V5_ATOMIC_V3_INACTIVE_GROUP_MASKS.len() as u8;
        let mut invalid = WeightAccumulator::empty(V5_CU_PROBE_RELATION_LOG_ROWS);
        assert_eq!(
            invalid.add_grouped_64x16_binary_masks_deferred_prepared(
                &invalid_groups,
                &V5_ATOMIC_V3_INACTIVE_GROUP_MASKS,
            ),
            Err(aspis_core::sumcheck::TensorWeightError::Grouped64x16PreparedShape)
        );
        assert_eq!(
            invalid.add_grouped_64x16_binary_masks_deferred_prepared(
                &V5_ATOMIC_V3_INACTIVE_ROW_GROUPS,
                &[],
            ),
            Err(aspis_core::sumcheck::TensorWeightError::Grouped64x16PreparedShape)
        );

        let explicit = generated
            .iter()
            .flat_map(|&mask| {
                (0..16).map(move |low| {
                    if mask & (1 << low) == 0 {
                        QM31::ZERO
                    } else {
                        QM31::ONE
                    }
                })
            })
            .collect::<Vec<_>>();
        let mut reference = WeightAccumulator::empty(V5_CU_PROBE_RELATION_LOG_ROWS);
        reference.add_dense(explicit).unwrap();
        let mut prepared = WeightAccumulator::empty(V5_CU_PROBE_RELATION_LOG_ROWS);
        prepared
            .add_grouped_64x16_binary_masks_deferred_prepared(
                &V5_ATOMIC_V3_INACTIVE_ROW_GROUPS,
                &V5_ATOMIC_V3_INACTIVE_GROUP_MASKS,
            )
            .unwrap();
        let mut state = 0x4652_4f5a_454e_5633;
        for round in 0..=V5_CU_PROBE_RELATION_FOLDS {
            let live = V5_CU_PROBE_RELATION_DENSE_VALUES >> (2 * round);
            let values = (0..live).map(|_| next_qm31(&mut state)).collect::<Vec<_>>();
            for index in 0..live as u32 {
                assert_eq!(
                    prepared.weight_at(index),
                    reference.weight_at(index),
                    "round={round} index={index}"
                );
            }
            assert_eq!(
                aspis_core::sumcheck::polynomial_for_extension(&values, &prepared),
                aspis_core::sumcheck::polynomial_for_extension(&values, &reference),
                "round={round} polynomial"
            );
            assert_eq!(
                prepared.dot(&values),
                reference.dot(&values),
                "round={round} dot"
            );
            if round < V5_CU_PROBE_RELATION_FOLDS {
                let alpha = next_qm31(&mut state);
                assert_ne!(alpha, QM31::ZERO, "round={round} off-domain challenge");
                assert_ne!(alpha, QM31::ONE, "round={round} off-domain challenge");
                reference.fold(alpha);
                prepared.fold(alpha);
            }
        }
    }

    #[test]
    fn prepared_v5_claims_preserve_point_major_relation_exactly() {
        let data = account_data();
        let parsed = parse_diagnostic_probe_data(&data).unwrap();
        let prepared = prepare_v5_pcs_claims(parsed.gamma, parsed.relation_claims).unwrap();
        let powers = qm31_power_table::<V5_CU_PROBE_RELATION_LANES>(parsed.gamma);
        for point in 0..V5_CU_PROBE_RELATION_CLAIMS_PER_LANE {
            let literal = (0..V5_CU_PROBE_RELATION_LANES).fold(QM31::ZERO, |sum, lane| {
                let value = decode_qm31(
                    parsed.relation_claims,
                    point * V5_CU_PROBE_RELATION_LANES + lane,
                )
                .unwrap();
                sum.add(powers[lane].mul(value))
            });
            assert_eq!(prepared.point_claims()[point], literal, "point {point}");
        }

        let mut kappa_state = 0x5150_434c_4149_4d53;
        let mut inactive_state = 0x494e_4143_5449_5645;
        let kappa = next_qm31(&mut kappa_state);
        let inactive_claim = next_qm31(&mut inactive_state);
        for variant in [
            RelationVariant::ThreeClaims,
            RelationVariant::FourClaimsCompact,
        ] {
            let (literal, literal_point, literal_scale) =
                prepare_relation_base_with_kappa(&parsed, variant, kappa, inactive_claim).unwrap();
            let (shared, shared_point, shared_scale) = prepare_relation_base_with_kappa_prepared(
                &parsed,
                variant,
                kappa,
                inactive_claim,
                &prepared,
            )
            .unwrap();
            assert_eq!(shared.relation_value, literal.relation_value);
            assert_eq!(shared.alphas, literal.alphas);
            assert_eq!(shared.final_values, literal.final_values);
            assert_eq!(shared_point, literal_point);
            assert_eq!(shared_scale, literal_scale);
            for index in 0..V5_CU_PROBE_RELATION_DENSE_VALUES as u32 {
                assert_eq!(
                    shared.weights.weight_at(index),
                    literal.weights.weight_at(index),
                    "weight {index}"
                );
            }
        }
    }

    #[test]
    fn prepared_v5_claims_and_literal_relation_reject_same_noncanonical_claim() {
        let mut data = account_data();
        data[V5_CU_PROBE_RELATION_CLAIMS_OFFSET..V5_CU_PROBE_RELATION_CLAIMS_OFFSET + 4]
            .copy_from_slice(&P.to_le_bytes());
        let parsed = parse_diagnostic_probe_data(&data).unwrap();
        assert!(prepare_v5_pcs_claims(parsed.gamma, parsed.relation_claims).is_err());
        assert!(prepare_relation_base_with_kappa(
            &parsed,
            RelationVariant::FourClaimsCompact,
            QM31::ONE,
            QM31::ZERO,
        )
        .is_err());
        assert!(prepare_v5_pcs_claims(
            parsed.gamma,
            &parsed.relation_claims[..parsed.relation_claims.len() - 1],
        )
        .is_err());
    }

    #[test]
    fn isolated_wire_checks_runtime_account_and_noncomposite_sinks() {
        let modes = [
            V5_CU_PROBE_PRODUCTION26_MODE,
            V5_CU_PROBE_GENERIC26_NONFUSED_MODE,
            V5_CU_PROBE_GENERIC16_NONFUSED_MODE,
            V5_CU_PROBE_GENERIC16_FUSED_MODE,
            V5_CU_PROBE_GENERIC26_FUSED_MODE,
            V5_CU_PROBE_RELATION3_MODE,
            V5_CU_PROBE_RELATION4_DENSE_MODE,
            V5_CU_PROBE_RELATION4_STANDALONE_DOT_MODE,
            V5_CU_PROBE_RELATION4_COMPACT_MODE,
        ];
        let mut lamports = 10_000_000;
        let key = Pubkey::new_unique();
        let owner = id();
        let mut data = account_data();
        let account = make_account(&key, &owner, &mut lamports, &mut data, false, false);
        for mode in modes {
            let mut wire = vec![V5_CU_PROBE_TAG, mode];
            wire.extend_from_slice(&probe_sink(mode, &account.try_borrow_data().unwrap()).unwrap());
            assert_eq!(
                process_v5_cu_probe_instruction(&owner, &[account.clone()], &wire),
                Ok(())
            );
            wire[2] ^= 1;
            assert_eq!(
                process_v5_cu_probe_instruction(&owner, &[account.clone()], &wire),
                Err(ProgramError::InvalidInstructionData)
            );
        }
        assert_eq!(
            probe_sink(10, &data),
            Err(ProgramError::InvalidInstructionData)
        );
        assert_eq!(
            probe_sink(V5_CU_PROBE_COMPOSITE_MODE, &data),
            Err(ProgramError::InvalidAccountData)
        );
    }

    #[test]
    fn composite_arithmetic_matches_the_two_isolated_kernels() {
        let data = account_data();
        let parsed = parse_diagnostic_probe_data(&data).unwrap();
        let mut outputs = vec![EMPTY_OUTPUT; V5_CU_PROBE_QUERY_COUNT];
        let mut layer_zero = PreparedMode::Generic16Fused(prepare_generic16(parsed.gamma));
        run_marked_kernel(
            V5_CU_PROBE_GENERIC16_FUSED_MODE,
            &parsed,
            &mut layer_zero,
            &mut outputs,
        )
        .unwrap();
        let isolated_layer_zero = outputs.clone();

        let verified_prefix = wire_skeleton::verify_synthetic_v5_wire(
            parsed.v5_wire_prefix,
            crate::verify::sbf_hashv,
        )
        .unwrap();
        let (mut relation, _, dense_scale) = prepare_relation_base_with_kappa(
            &parsed,
            RelationVariant::FourClaimsCompact,
            verified_prefix.kappa,
            QM31::ZERO,
        )
        .unwrap();
        relation.extra_work = RelationExtraWork::Compact(CompactBTerminalWeights::new(
            &verified_prefix.round_challenges,
            dense_scale,
        ));
        let relation_value = run_relation_kernel(&mut relation);
        outputs[0].combined[0] = outputs[0].combined[0]
            .add(relation_value)
            .add(verified_prefix.terminal_masked);

        assert_eq!(
            outputs[0].combined[0],
            isolated_layer_zero[0].combined[0]
                .add(relation_value)
                .add(verified_prefix.terminal_masked)
        );
        assert_ne!(
            outputs_sink(V5_CU_PROBE_COMPOSITE_MODE, &outputs).unwrap(),
            [0u8; 32]
        );
    }

    #[test]
    fn component_b_covector_has_exact_prototype_support() {
        let data = account_data();
        let parsed = parse_diagnostic_probe_data(&data).unwrap();
        let (_, point, scale) =
            prepare_relation_base(&parsed, RelationVariant::FourClaimsSharedFold).unwrap();
        let (covector, pivot) =
            derive_v5_b_terminal_covector(V5_CU_PROBE_RELATION4_DENSE_MODE, &point, scale).unwrap();
        assert_eq!(covector.len(), 1024);
        assert_eq!(covector[pivot], QM31::ZERO);
        for coordinate in V5_CU_PROBE_B_MASK_COORDINATES..V5_CU_PROBE_RELATION_DENSE_VALUES - 1 {
            assert_eq!(covector[free_coordinate_row(coordinate, pivot)], QM31::ZERO);
        }
        assert_eq!(
            covector.iter().filter(|value| !value.is_zero()).count(),
            V5_CU_PROBE_B_MASK_COORDINATES
        );
    }

    #[test]
    fn compact_component_b_weights_match_literal_dense_four_fold() {
        let mut state = 0xc04d_9a11_5e17_0021;
        for case in 0..32 {
            let point = core::array::from_fn(|_| next_qm31(&mut state));
            let scale = next_qm31(&mut state);
            let alphas: [QM31; V5_CU_PROBE_RELATION_FOLDS] =
                core::array::from_fn(|_| next_qm31(&mut state));

            let mut literal = WeightAccumulator::empty(V5_CU_PROBE_RELATION_LOG_ROWS);
            literal
                .add_dense(literal_structured_b_covector(&point, scale))
                .unwrap();
            let mut compact = CompactBTerminalWeights::new(&point, scale);
            for alpha in alphas {
                literal.fold(alpha);
                compact.fold(alpha);
            }
            for (index, compact_weight) in compact.final_weights().into_iter().enumerate() {
                assert_eq!(
                    compact_weight,
                    literal.weight_at(index as u32),
                    "case {case}, final index {index}"
                );
            }
        }
    }

    #[test]
    fn compact_component_b_layout_and_memory_are_pinned() {
        assert_eq!(
            V5_CU_PROBE_B_BLOCK_SELECTORS,
            [0, 1, 2, 3, 4, 5, 6, 28, 29, 30]
        );
        assert_eq!(V5_CU_PROBE_B_INITIAL_STATE_ROW, 992);
        assert_eq!(V5_CU_PROBE_B_DEPENDENT_PIVOT_ROW, 993);
        let point = [QM31::from_cm31(aspis_core::field::CM31::from_m31(M31(3)));
            V5_CU_PROBE_RELATION_LOG_ROWS as usize];
        let literal = literal_structured_b_covector(&point, QM31::ONE);
        for selector in V5_CU_PROBE_B_BLOCK_SELECTORS {
            let start = usize::from(selector) * V5_CU_PROBE_B_BLOCK_ROWS;
            assert!(literal[start..start + 28]
                .iter()
                .all(|value| !value.is_zero()));
            assert_eq!(&literal[start + 28..start + 32], &[QM31::ZERO; 4]);
        }
        assert_eq!(literal[V5_CU_PROBE_B_DEPENDENT_PIVOT_ROW], QM31::ZERO);
        assert_eq!(V5_CU_PROBE_B_COMPACT_DYNAMIC_HEAP_BYTES, 0);
        assert!(
            V5_CU_PROBE_B_COMPACT_STATE_BYTES
                < V5_CU_PROBE_RELATION_DENSE_VALUES * core::mem::size_of::<QM31>()
        );
    }

    #[test]
    fn constants_pin_runtime_surface() {
        assert_eq!(V5_CU_PROBE_WIRE_BYTES, 34);
        assert_eq!(V5_CU_PROBE_CANDIDATE_C1_OFFSET, 24);
        assert_eq!(V5_CU_PROBE_PREFIX_OFFSET, 11_112);
        assert_eq!(V5_CU_PROBE_ATOMIC_TERMINAL_CONTEXT_OFFSET, 17_535);
        assert_eq!(V5_ATOMIC_TERMINAL_CONTEXT_BYTES, 440);
        assert_eq!(V5_CU_PROBE_PRIVATE_ROOTS_OFFSET, 17_975);
        assert_eq!(V5_CU_PROBE_FINAL_COEFFICIENTS_OFFSET, 18_135);
        assert_eq!(V5_CU_PROBE_ACCOUNT_BYTES, 19_136);
        assert_eq!(V5_CU_PROBE_PRODUCTION_C1_OFFSET, 19_136);
        assert_eq!(V5_CU_PROBE_DIAGNOSTIC_ACCOUNT_BYTES, 27_200);
        assert_eq!(V5_CU_PROBE_PROVISIONAL_QUERIES.len(), 18);
        assert_eq!(V5_CU_PROBE_PRODUCTION_C1_VALUE_BYTES, 416);
        assert_eq!(V5_CU_PROBE_CANDIDATE_C1_VALUE_BYTES, 256);
        assert_eq!(V5_CU_PROBE_C2_VALUE_BYTES, 192);
    }

    fn maximum_radix4_binary_cap_frontier(binary_depth: u32, count: usize) -> usize {
        let mut level_capacity = 1usize << binary_depth;
        let mut current = count;
        let mut frontier = 0usize;
        for _ in 0..binary_depth / 2 {
            level_capacity /= 4;
            let next = current.min(level_capacity);
            frontier += 4 * next - current;
            current = next;
        }
        if binary_depth % 2 == 1 && current == 1 {
            frontier += 1;
        }
        frontier
    }

    #[test]
    fn tag67_private_opening_and_proof_account_maxima_are_exact() {
        use super::private_openings::{V5_PRIVATE_DEPTHS, V5_PRIVATE_VALUE_WIDTHS};

        let mut section_maxima = [0usize; 5];
        let mut frontier_at_maximum = [0usize; 5];
        for section in 0..5 {
            for count in 1..=V5_CU_PROBE_QUERY_COUNT {
                let frontier =
                    maximum_radix4_binary_cap_frontier(V5_PRIVATE_DEPTHS[section], count);
                let bytes = 2 + count * (V5_PRIVATE_VALUE_WIDTHS[section] + 32) + 4 + frontier * 32;
                if bytes > section_maxima[section] {
                    section_maxima[section] = bytes;
                    frontier_at_maximum[section] = frontier;
                }
            }
        }
        assert_eq!(V5_CU_PROBE_MAX_OPENING_COUNTS, [18; 5]);
        assert_eq!(frontier_at_maximum, V5_CU_PROBE_MAX_OPENING_FRONTIER_NODES);
        assert_eq!(section_maxima, V5_CU_PROBE_MAX_OPENING_SECTION_BYTES);
        assert_eq!(
            section_maxima.into_iter().sum::<usize>(),
            V5_CU_PROBE_MAX_PRIVATE_PROOF_BYTES
        );
        assert_eq!(V5_CU_PROBE_MAX_PROOF_BODY_BYTES, 77_278);
        assert_eq!(V5_CU_PROBE_MAX_SEALED_PROOF_ACCOUNT_BYTES, 77_318);

        let mut maximum = vec![0u8; V5_CU_PROBE_MAX_PROOF_BODY_BYTES];
        maximum[..V5_CU_PROBE_ACCOUNT_MAGIC.len()].copy_from_slice(&V5_CU_PROBE_ACCOUNT_MAGIC);
        assert!(parse_probe_data(&maximum).is_ok());
        maximum.push(0);
        assert_eq!(
            parse_probe_data(&maximum).map(|_| ()),
            Err(ProgramError::InvalidAccountData)
        );
    }
}
