//! Aspis SpendV0 statement layer, built evaluator-first.
//!
//! This crate deliberately contains no proof system. It defines the exact
//! M31-native hash, spend relations, economic failure modes, and isolated
//! constraint-composition kernel that Stage 2 must make correct before any
//! statement proof is wired into the PCS.

#![no_std]

extern crate alloc;

pub mod composition;
pub mod logup;
pub mod poseidon2;
pub mod spend;
pub mod split;
pub mod trace_v4;
pub mod wide_v4;

pub use composition::{
    evaluate_composition_probe, evaluate_composition_probe_optimized, CompositionProbe,
    CompositionProbeResult,
};
#[cfg(feature = "insecure-test-logup-compression")]
pub use logup::compress_tagged_tuple_insecure_lambda_zero;
pub use logup::{
    build_10bit_range_logup_rows, build_logup_helper, compress_tagged_tuple,
    forge_post_chi_multiplicities, logup_compression_kat, verify_logup_constraints, LogUpError,
    LogUpMainRow, LogUpSide, LOGUP_COMPRESSION_KAT_EXPECTED, RANGE_TABLE_SIZE,
};
pub use poseidon2::{
    hash_fields, hash_fields_with_trace, permute, permute_optimized_with_trace, Digest,
    Poseidon2RoundKind, Poseidon2RoundTransition, DIGEST_ELEMS, POSEIDON2_ROUNDS, POSEIDON2_WIDTH,
    RATE,
};
pub use spend::{
    decompose_10bit_limbs, derive_nullifier, derive_owner_key, evaluate_spend,
    evaluate_spend_with_range_lookup, merkle_root, note_commitment, output_commitment,
    verify_10bit_range_lookup, EvaluationContext, MerklePath, RangeLookupWitness, SpendError,
    SpendPublic, SpendWitness, RANGE_LIMBS_PER_VALUE, RANGE_LIMB_BITS, RANGE_LIMB_LIMIT,
    VALUE_LIMIT,
};
pub use split::{
    ReceiptBinding, ReceiptError, ReceiptStatus, SplitVerificationReceipt, TERMINAL_POINT_LEN,
};
pub use trace_v4::{
    build_spend_trace_v4, copy_layout, is_absorption_row, is_poseidon_active_row,
    is_poseidon_padding_row, merkle_boundary_layout, permutation_block_schedule, poseidon_row_kind,
    validate_spend_trace_v4, witness_aux_layout, CopyLayout, CopyLink, CopyLinkKind, CopyTuple,
    HashInvocationKind, MerkleBoundaryBinding, PermutationBlock, PoseidonRowKind, SpendTraceV4,
    TraceBuildError, TraceCell, TracePublicOutputs, TraceValidationError, TupleLimb,
    WitnessAuxLayout, ABSORPTION_COPY_LINK_COUNT, ABSORPTION_ROW_IN_BLOCK, ACTIVE_ROWS_PER_BLOCK,
    ALLOCATED_PERMUTATION_ROWS, AUX_ABSORPTION_PRODUCER_ROW_START, AUX_WITNESS_ROW_START,
    BLOCK_ROWS, COPY_LINK_COUNT, DEAD_ROW_START_IN_BLOCK, MULTIPLICITY_COLUMN, PERMUTATION_COUNT,
    POSEIDON_ACTIVE_ROWS, SEMANTIC_INGRESS_COPY_LINK_COUNT, STATE_AND_INTERFACE_COLUMNS,
    STATE_COPY_LINK_COUNT, TRACE_ROWS,
};
pub use wide_v4::{
    combine_exact_wide_bytes_prepared, combine_exact_wide_fiber, combine_exact_wide_fiber_baseline,
    combine_exact_wide_fiber_prepared, prepare_exact_wide_weights, ExactWideFiber,
    ExactWideWeights, C1_COLUMNS as WIDE_V4_C1_COLUMNS, C1_FIBER_BYTES as WIDE_V4_C1_FIBER_BYTES,
    C2_COLUMNS as WIDE_V4_C2_COLUMNS, C2_FIBER_BYTES as WIDE_V4_C2_FIBER_BYTES,
    TOTAL_COLUMNS as WIDE_V4_TOTAL_COLUMNS,
};
