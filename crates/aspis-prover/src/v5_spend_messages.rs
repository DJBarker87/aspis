//! Layer-zero message construction for V5.
//!
//! This module starts from the atomic-v3 statement and witness, builds the
//! real sixteen-column semantic trace, applies one atomic-conditioned
//! Component-A mask per existing column, builds the ordinary atomic-v3 copy
//! LogUp helper with its standard inactive-row padding, and places structured
//! Components B and C in the other two already-budgeted QM31 lanes.
//!
//! The resulting messages are encoded with the real log-19 circle encoder
//! (rate 1/512) and committed with the same salted private-Merkle primitive
//! used by Spend.  C1 leaves are exactly 256 bytes and C2 leaves exactly 192
//! bytes.  No synthetic digest stands in for either root.
//!
//! The production host builder composes these messages with the transcript,
//! mixed sumcheck, private openings, and later folds.

use aspis_core::circle_fri::FIXED_ARITY4_ROUNDS;
use aspis_core::circle_line_merkle::{
    derive_circle_line_query_indices_for_count, CircleLineMerkleError, CircleLineQueryIndices,
    CIRCLE_LINE_TAGS,
};
use aspis_core::circle_merkle::{CIRCLE_C1_LAYER0_TAG, CIRCLE_C2_LAYER0_TAG};
use aspis_core::field::{qm31_power_table, M31, QM31};
use aspis_core::state_only_private_merkle::STATE_ONLY_PRIVATE_LEAF_SALT_BYTES;
use aspis_core::state_only_private_openings::{
    verify_state_only_private_opening_from_proof, StateOnlyPrivateOpening,
    StateOnlyPrivateOpeningError,
};
use aspis_core::HashFn;
use aspis_statement::atomic_state_only_registry::{
    build_atomic_state_only_copy_helper_v3, AtomicStateOnlyRegistryErrorV3,
};
use aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_masks_v3;
use aspis_statement::atomic_state_only_trace::{
    build_atomic_state_only_trace_v3, AtomicStateOnlyTraceV3Error,
};
use aspis_statement::{
    state_only_copy_helper_sum, AtomicPaymentStatementV4, SpendWitness, StateOnlyTraceFoundation,
};

use super::component_c::{v5_c_inactive_functional, V5ComponentCLane};
use super::{
    atomic_m31_block_mask_coefficient_sum, mask_m31_column, M31BlockMask, V5MaskError,
    V5_CODEWORD_LEN, V5_DOMAIN_LOG, V5_SEMANTIC_C1_LANES, V5_TRACE_ROWS,
};
use crate::circle_candidate::{
    build_fold_commitments_for_domain_log, CircleCandidateError, CircleEncoder,
    CircleFoldCommitments, COMBINED_LAYER_LEAF_BYTES,
};
use crate::state_only_hiding::{
    apply_atomic_state_only_h1_padding_mask_v3, StateOnlyMaskBuildError,
};
use crate::state_only_private_openings::{
    build_state_only_private_merkle_tree, serialize_state_only_private_opening,
    StateOnlyPrivateOpeningBuildError,
};
use crate::v5_sumcheck_mask::{V5SumcheckMask, V5_SUMCHECK_MASK_RANDOMNESS};

pub const V5_C1_LANES: usize = V5_SEMANTIC_C1_LANES;
pub const V5_C2_LANES: usize = 3;
pub const V5_HCOPY_LANE: usize = 0;
pub const V5_COMPONENT_B_LANE: usize = 1;
pub const V5_COMPONENT_C_LANE: usize = 2;
pub const V5_FIBRE_SLOTS: usize = 4;
pub const V5_C1_LEAF_BYTES: usize = V5_C1_LANES * V5_FIBRE_SLOTS * 4;
pub const V5_C2_LEAF_BYTES: usize = V5_C2_LANES * V5_FIBRE_SLOTS * 16;
pub const V5_LAYER_ZERO_BINARY_DEPTH: u32 = V5_DOMAIN_LOG - 2;
pub const V5_LAYER_ZERO_LEAVES: usize = V5_CODEWORD_LEN / V5_FIBRE_SLOTS;
pub const V5_TOTAL_LANES: usize = V5_C1_LANES + V5_C2_LANES;
pub const V5_PCS_ROUNDS: usize = FIXED_ARITY4_ROUNDS as usize;
pub const V5_LATER_LAYERS: usize = V5_PCS_ROUNDS - 1;
pub const V5_PRIVATE_SECTIONS: usize = 2 + V5_LATER_LAYERS;
pub const V5_PRIVATE_DEPTHS: [u32; V5_PRIVATE_SECTIONS] = [17, 17, 15, 13, 11];
pub const V5_PRIVATE_WIDTHS: [usize; V5_PRIVATE_SECTIONS] = [256, 192, 64, 64, 64];
pub const V5_PRIVATE_TAGS: [u8; V5_PRIVATE_SECTIONS] = [
    CIRCLE_C1_LAYER0_TAG,
    CIRCLE_C2_LAYER0_TAG,
    CIRCLE_LINE_TAGS[0],
    CIRCLE_LINE_TAGS[1],
    CIRCLE_LINE_TAGS[2],
];

/// Legacy diagnostic status retained for the older CU stress artifact.
///
/// The production V5 host does not use this status value.
pub const V5_CU_STRESS_ONLY_STATUS: &str =
    "CU stress only: Component C is rejected and no v5 security claim is made";

/// The ten degree-27 messages occupy seven low blocks and three high blocks.
pub const V5_B_ROUND_BLOCKS: [usize; 10] = [0, 1, 2, 3, 4, 5, 6, 28, 29, 30];
pub const V5_B_ROUND_BLOCK_ROWS: usize = 32;
pub const V5_B_ROUND_COEFFICIENTS: usize = 28;
pub const V5_B_ROUND_FREE_COEFFICIENTS: usize = 27;
pub const V5_B_INITIAL_CLAIM_ROW: usize = 992;
pub const V5_B_INACTIVE_PIVOT_ROW: usize = 993;
pub const V5_B_PAD_START: usize = 224;
pub const V5_B_PAD_COORDINATES: usize = 255;
pub const V5_B_STATE_COORDINATES: usize = V5_SUMCHECK_MASK_RANDOMNESS;
pub const V5_B_PHYSICAL_FREE_COORDINATES: usize = V5_B_STATE_COORDINATES + V5_B_PAD_COORDINATES;
pub const V5_B_AFFINE_FREE_COORDINATES: usize = V5_B_PHYSICAL_FREE_COORDINATES + 1;
pub const V5_B_PIVOT_PAD_PRODUCTION_OBLIGATION: &str =
    "sample the Component-B inactive pivot pad freshly and independently before committing C2";

const _: () = assert!(V5_C1_LANES == 16);
const _: () = assert!(V5_C2_LANES == 3);
const _: () = assert!(V5_TOTAL_LANES == 19);
const _: () = assert!(V5_PCS_ROUNDS == 4);
const _: () = assert!(V5_PRIVATE_SECTIONS == 5);
const _: () = assert!(V5_C1_LEAF_BYTES == 256);
const _: () = assert!(V5_C2_LEAF_BYTES == 192);
const _: () = assert!(V5_LAYER_ZERO_BINARY_DEPTH == 17);
const _: () = assert!(V5_LAYER_ZERO_LEAVES == 1 << V5_LAYER_ZERO_BINARY_DEPTH);
const _: () = assert!(V5_B_STATE_COORDINATES == 271);
const _: () = assert!(V5_B_PHYSICAL_FREE_COORDINATES == 526);
const _: () = assert!(V5_B_AFFINE_FREE_COORDINATES == 527);
const _: () = assert!(V5_B_PAD_START + V5_B_PAD_COORDINATES == 479);
const _: () = assert!(V5_B_INACTIVE_PIVOT_ROW < V5_TRACE_ROWS);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V5SpendMessageError {
    AtomicTrace(AtomicStateOnlyTraceV3Error),
    AtomicCopy(AtomicStateOnlyRegistryErrorV3),
    ComponentA(V5MaskError),
    HcopyPadding(StateOnlyMaskBuildError),
    Circle(CircleCandidateError),
    PrivateMerkle(StateOnlyPrivateOpeningBuildError),
    Query(CircleLineMerkleError),
    OpeningVerify {
        section: u8,
        error: StateOnlyPrivateOpeningError,
    },
    OpeningTrailingBytes {
        offset: usize,
        remaining: usize,
    },
    LayerZeroRootMismatch,
    ComponentARelation {
        lane: usize,
    },
    HcopyRelation,
    ComponentBRelation,
    ComponentCRelation,
    MessageShape,
}

impl core::fmt::Display for V5SpendMessageError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::AtomicTrace(error) => write!(formatter, "atomic-v3 trace error: {error:?}"),
            Self::AtomicCopy(error) => write!(formatter, "atomic-v3 copy error: {error:?}"),
            Self::ComponentA(error) => write!(formatter, "component-A error: {error:?}"),
            Self::HcopyPadding(error) => write!(formatter, "Hcopy padding error: {error:?}"),
            Self::Circle(error) => write!(formatter, "circle encoding error: {error}"),
            Self::PrivateMerkle(error) => write!(formatter, "private Merkle error: {error:?}"),
            Self::Query(error) => write!(formatter, "query geometry error: {error:?}"),
            Self::OpeningVerify { section, error } => {
                write!(formatter, "opening section {section} failed: {error:?}")
            }
            Self::OpeningTrailingBytes { offset, remaining } => write!(
                formatter,
                "opening has {remaining} trailing bytes at offset {offset}"
            ),
            Self::LayerZeroRootMismatch => {
                formatter.write_str("rebuilt layer-zero root does not match the committed root")
            }
            Self::ComponentARelation { lane } => {
                write!(
                    formatter,
                    "component-A lane {lane} does not preserve the atomic relation"
                )
            }
            Self::HcopyRelation => formatter.write_str("Hcopy does not satisfy its zero claim"),
            Self::ComponentBRelation => formatter.write_str(
                "component B inactive functional does not equal its committed pivot pad",
            ),
            Self::ComponentCRelation => {
                formatter.write_str("component C does not satisfy the atomic inactive relation")
            }
            Self::MessageShape => formatter.write_str("v5 message shape mismatch"),
        }
    }
}

impl std::error::Error for V5SpendMessageError {}

impl From<AtomicStateOnlyTraceV3Error> for V5SpendMessageError {
    fn from(error: AtomicStateOnlyTraceV3Error) -> Self {
        Self::AtomicTrace(error)
    }
}

impl From<AtomicStateOnlyRegistryErrorV3> for V5SpendMessageError {
    fn from(error: AtomicStateOnlyRegistryErrorV3) -> Self {
        Self::AtomicCopy(error)
    }
}

impl From<V5MaskError> for V5SpendMessageError {
    fn from(error: V5MaskError) -> Self {
        Self::ComponentA(error)
    }
}

impl From<StateOnlyMaskBuildError> for V5SpendMessageError {
    fn from(error: StateOnlyMaskBuildError) -> Self {
        Self::HcopyPadding(error)
    }
}

impl From<CircleCandidateError> for V5SpendMessageError {
    fn from(error: CircleCandidateError) -> Self {
        Self::Circle(error)
    }
}

impl From<StateOnlyPrivateOpeningBuildError> for V5SpendMessageError {
    fn from(error: StateOnlyPrivateOpeningBuildError) -> Self {
        Self::PrivateMerkle(error)
    }
}

impl From<CircleLineMerkleError> for V5SpendMessageError {
    fn from(error: CircleLineMerkleError) -> Self {
        Self::Query(error)
    }
}

fn atomic_inactive(row: usize) -> bool {
    let masks = atomic_state_only_copy_inactive_row_masks_v3();
    let high = row >> 4u32;
    let low = (row & 15) as u32;
    masks[high] & (1u16 << low) != 0
}

fn atomic_inactive_sum_m31(values: &[M31]) -> Option<M31> {
    (values.len() == V5_TRACE_ROWS).then(|| {
        values
            .iter()
            .copied()
            .enumerate()
            .filter(|(row, _)| atomic_inactive(*row))
            .fold(M31::ZERO, |sum, (_, value)| sum.add(value))
    })
}

fn atomic_inactive_sum_qm31(values: &[QM31]) -> Option<QM31> {
    if values.len() != V5_TRACE_ROWS {
        return None;
    }
    let mut sum = QM31::ZERO;
    let mut row = 0usize;
    while row < values.len() {
        if atomic_inactive(row) {
            sum = sum.add(values[row]);
        }
        row += 1;
    }
    Some(sum)
}

const fn b_block_row(round: usize, offset: usize) -> usize {
    V5_B_ROUND_BLOCKS[round] * V5_B_ROUND_BLOCK_ROWS + offset
}

/// Structured Component-B message used by the compact production path.
///
/// The initial mask claim and the 270 independent round coefficients are
/// committed in the exact 32-row block layout used by the compact terminal
/// calculation.  The ten dependent constants are derived.  The caller's fresh
/// pivot pad is committed at the atomic inactive row 993 after cancelling all
/// other inactive-row values, so the lane's inactive functional is exactly
/// that pad. Offsets 28..31 in every selected block remain fixed zero.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct V5StructuredBLane {
    values: [QM31; V5_TRACE_ROWS],
    pivot_pad: QM31,
}

impl V5StructuredBLane {
    pub fn encode(
        mask: &V5SumcheckMask,
        pads: &[QM31; V5_B_PAD_COORDINATES],
        pivot_pad: QM31,
    ) -> Result<Self, V5SpendMessageError> {
        if !atomic_inactive(V5_B_INACTIVE_PIVOT_ROW) {
            return Err(V5SpendMessageError::ComponentBRelation);
        }
        let mut values = [QM31::ZERO; V5_TRACE_ROWS];
        values[V5_B_INITIAL_CLAIM_ROW] = mask.initial_claim();

        let mut round = 0usize;
        while round < 10 {
            let mut offset = 0usize;
            while offset < V5_B_ROUND_COEFFICIENTS {
                let value = mask.commitment_coefficient(round, offset);
                values[b_block_row(round, offset)] = value;
                offset += 1;
            }
            round += 1;
        }
        let mut offset = 0usize;
        while offset < V5_B_PAD_COORDINATES {
            values[V5_B_PAD_START + offset] = pads[offset];
            offset += 1;
        }
        let inactive_without_pivot = match atomic_inactive_sum_qm31(&values) {
            Some(value) => value,
            None => return Err(V5SpendMessageError::ComponentBRelation),
        };
        values[V5_B_INACTIVE_PIVOT_ROW] = pivot_pad.add(inactive_without_pivot.neg());
        match atomic_inactive_sum_qm31(&values) {
            Some(value) if value == pivot_pad => {}
            _ => return Err(V5SpendMessageError::ComponentBRelation),
        }
        Ok(Self { values, pivot_pad })
    }

    pub const fn values(&self) -> &[QM31; V5_TRACE_ROWS] {
        &self.values
    }

    pub const fn pivot_pad(&self) -> QM31 {
        self.pivot_pad
    }
}

/// The complete layer-zero messages in generator order:
/// `semantic[0..16], Hcopy, B, C`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct V5SpendMessages {
    pub c1: [Vec<M31>; V5_C1_LANES],
    pub c2: [Vec<QM31>; V5_C2_LANES],
}

/// Copy the fixed Component-B lane in increasing physical-row order.
///
/// This indexed spelling is equivalent to `values().to_vec()` and keeps the
/// exact committed row order visible to the Rust-to-Lean extraction pipeline.
pub(crate) fn component_b_message_values(component_b: &V5StructuredBLane) -> Vec<QM31> {
    let mut values = Vec::with_capacity(V5_TRACE_ROWS);
    let mut row = 0usize;
    while row < V5_TRACE_ROWS {
        values.push(component_b.values[row]);
        row += 1;
    }
    values
}

/// Assemble the three committed C2 lanes in their production order.
/// Keeping this move-only constructor separate makes the Component-B lane-one
/// binding independently extractable without duplicating message logic.
pub(crate) fn assemble_v5_c2_messages(
    hcopy: Vec<QM31>,
    component_b: Vec<QM31>,
    component_c: Vec<QM31>,
) -> [Vec<QM31>; V5_C2_LANES] {
    [hcopy, component_b, component_c]
}

/// Real log-19 codewords, packed private-tree values, and their salted roots.
pub struct V5EncodedLayerZero {
    pub messages: V5SpendMessages,
    pub encoded_c1: Vec<Vec<M31>>,
    pub encoded_c2: Vec<Vec<QM31>>,
    pub c1_values: Vec<u8>,
    pub c2_values: Vec<u8>,
    pub c1_root: [u8; 32],
    pub c2_root: [u8; 32],
}

/// Caller-owned salts for all five private PCS trees.  The expected counts
/// are `2^17, 2^17, 2^15, 2^13, 2^11` respectively.
#[derive(Clone, Copy)]
pub struct V5PcsSalts<'a> {
    pub c1: &'a [[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]],
    pub c2: &'a [[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]],
    pub later: [&'a [[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]]; V5_LATER_LAYERS],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V5PcsRoots {
    pub c1: [u8; 32],
    pub c2: [u8; 32],
    pub later: [[u8; 32]; V5_LATER_LAYERS],
}

impl V5PcsRoots {
    fn as_array(self) -> [[u8; 32]; V5_PRIVATE_SECTIONS] {
        [
            self.c1,
            self.c2,
            self.later[0],
            self.later[1],
            self.later[2],
        ]
    }
}

/// Canonical five-section private-opening suffix, using the existing
/// `count || (value || salt)* || frontier` grammar in every section.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct V5BuiltPcsOpenings {
    pub bytes: Vec<u8>,
    pub indices: CircleLineQueryIndices,
    pub section_bytes: [usize; V5_PRIVATE_SECTIONS],
    pub frontier_nodes: [usize; V5_PRIVATE_SECTIONS],
}

/// Complete host PCS stress artefact through the fourth fold.  The explicit
/// status string is part of the value so callers cannot reasonably confuse
/// this integration/CU path with a security-approved v5 proof.
pub struct V5CuStressPcsArtifact {
    pub security_status: &'static str,
    pub layer_zero: V5EncodedLayerZero,
    pub combined_message: Vec<QM31>,
    pub combined_codeword: Vec<QM31>,
    pub folds: CircleFoldCommitments,
    pub later_values: [Vec<u8>; V5_LATER_LAYERS],
    pub roots: V5PcsRoots,
    pub openings: V5BuiltPcsOpenings,
}

/// Zero-copy authenticated view of a v5 five-section opening suffix.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedV5PcsOpenings<'a> {
    pub c1: StateOnlyPrivateOpening<'a>,
    pub c2: StateOnlyPrivateOpening<'a>,
    pub later: [StateOnlyPrivateOpening<'a>; V5_LATER_LAYERS],
    pub indices: CircleLineQueryIndices,
    pub end: usize,
}

/// Apply Component A to a real atomic-v3 trace, checking both its 95-variable
/// coefficient equation and the exact deployed inactive-row functional.
fn apply_component_a(
    trace: &mut StateOnlyTraceFoundation,
    masks: &[M31BlockMask; V5_C1_LANES],
) -> Result<(), V5SpendMessageError> {
    for (lane, mask) in masks.iter().enumerate() {
        if atomic_m31_block_mask_coefficient_sum(mask) != M31::ZERO {
            return Err(V5SpendMessageError::ComponentARelation { lane });
        }
        let before =
            atomic_inactive_sum_m31(&trace.c1[lane]).ok_or(V5SpendMessageError::MessageShape)?;
        let masked = mask_m31_column(&trace.c1[lane], mask)?;
        let after = atomic_inactive_sum_m31(&masked).ok_or(V5SpendMessageError::MessageShape)?;
        if before != after {
            return Err(V5SpendMessageError::ComponentARelation { lane });
        }
        trace.c1[lane] = masked;
    }
    Ok(())
}

/// Build the real atomic-v3 v5 messages.  The caller supplies already-sampled
/// and domain-separated masks; sampling/transcript order is a later seam.
pub fn build_v5_spend_messages(
    statement: &AtomicPaymentStatementV4,
    witness: &SpendWitness,
    component_a: &[M31BlockMask; V5_C1_LANES],
    hcopy_padding: &[QM31; V5_TRACE_ROWS],
    component_b: &V5StructuredBLane,
    component_c: &V5ComponentCLane,
    lambda: QM31,
    chi: QM31,
) -> Result<V5SpendMessages, V5SpendMessageError> {
    let mut atomic = build_atomic_state_only_trace_v3(statement, witness)?;
    let mut trace = core::mem::take(&mut atomic.trace);
    apply_component_a(&mut trace, component_a)?;

    let mut hcopy = build_atomic_state_only_copy_helper_v3(&trace, lambda, chi)?;
    apply_atomic_state_only_h1_padding_mask_v3(&mut hcopy, hcopy_padding)?;
    if state_only_copy_helper_sum(&hcopy) != Some(QM31::ZERO)
        || atomic_inactive_sum_qm31(&hcopy) != Some(QM31::ZERO)
    {
        return Err(V5SpendMessageError::HcopyRelation);
    }
    if atomic_inactive_sum_qm31(component_b.values()) != Some(component_b.pivot_pad()) {
        return Err(V5SpendMessageError::ComponentBRelation);
    }
    if v5_c_inactive_functional(component_c.values()) != QM31::ZERO {
        return Err(V5SpendMessageError::ComponentCRelation);
    }

    let c1 = core::mem::take(&mut trace.c1);
    let component_b_values = component_b_message_values(component_b);
    let component_c_values = component_c.values().to_vec();
    let c2 = assemble_v5_c2_messages(hcopy, component_b_values, component_c_values);
    Ok(V5SpendMessages { c1, c2 })
}

fn encode_messages(
    messages: &V5SpendMessages,
) -> Result<(Vec<Vec<M31>>, Vec<Vec<QM31>>), V5SpendMessageError> {
    let encoder = CircleEncoder::new_for_domain_log(V5_DOMAIN_LOG);
    let encoded_c1 = messages
        .c1
        .iter()
        .map(|message| encoder.encode_c1_message(message))
        .collect::<Result<Vec<_>, _>>()?;
    let encoded_c2 = messages
        .c2
        .iter()
        .map(|message| encoder.encode_c2_message(message))
        .collect::<Result<Vec<_>, _>>()?;
    Ok((encoded_c1, encoded_c2))
}

/// Byte ordinal of one M31 limb inside a v5 C1 layer-zero leaf.
///
/// Leaves are slot-major, then lane-major, then little-endian byte order.
/// This helper is called by the production packer so the runtime
/// ordering is available as a first-order extraction target.
fn c1_leaf_m31_byte_ordinal(slot: usize, lane: usize, byte: usize) -> usize {
    (slot * V5_C1_LANES + lane) * 4 + byte
}

fn pack_c1_values(encoded: &[Vec<M31>]) -> Result<Vec<u8>, V5SpendMessageError> {
    if encoded.len() != V5_C1_LANES {
        return Err(V5SpendMessageError::MessageShape);
    }
    let mut lane = 0usize;
    let mut wrong_column_length = false;
    while lane < encoded.len() {
        wrong_column_length |= encoded[lane].len() != V5_CODEWORD_LEN;
        lane += 1;
    }
    if wrong_column_length {
        return Err(V5SpendMessageError::MessageShape);
    }

    let mut values = Vec::with_capacity(V5_LAYER_ZERO_LEAVES * V5_C1_LEAF_BYTES);
    let mut fibre = 0usize;
    while fibre < V5_LAYER_ZERO_LEAVES {
        let mut slot = 0usize;
        while slot < V5_FIBRE_SLOTS {
            let index = V5_FIBRE_SLOTS * fibre + slot;
            let mut lane = 0usize;
            while lane < encoded.len() {
                let word = encoded[lane][index].to_le_bytes();
                let mut byte = 0usize;
                while byte < 4 {
                    let ordinal = c1_leaf_m31_byte_ordinal(slot, lane, byte);
                    values.push(word[ordinal & 3]);
                    byte += 1;
                }
                lane += 1;
            }
            slot += 1;
        }
        fibre += 1;
    }
    debug_assert_eq!(values.len(), V5_LAYER_ZERO_LEAVES * V5_C1_LEAF_BYTES);
    Ok(values)
}

fn pack_c2_values(encoded: &[Vec<QM31>]) -> Result<Vec<u8>, V5SpendMessageError> {
    if encoded.len() != V5_C2_LANES || encoded.iter().any(|column| column.len() != V5_CODEWORD_LEN)
    {
        return Err(V5SpendMessageError::MessageShape);
    }
    let mut values = Vec::with_capacity(V5_LAYER_ZERO_LEAVES * V5_C2_LEAF_BYTES);
    for fibre in 0..V5_LAYER_ZERO_LEAVES {
        for helper in encoded {
            for slot in 0..V5_FIBRE_SLOTS {
                let index = V5_FIBRE_SLOTS * fibre + slot;
                let start = values.len();
                values.resize(start + 16, 0);
                helper[index].write_le_bytes(&mut values[start..start + 16]);
            }
        }
    }
    debug_assert_eq!(values.len(), V5_LAYER_ZERO_LEAVES * V5_C2_LEAF_BYTES);
    Ok(values)
}

/// Commit already-packed v5 layer-zero values with the production salted
/// private-Merkle primitive and the production C1/C2 tree tags.
pub fn v5_layer_zero_roots(
    c1_values: &[u8],
    c2_values: &[u8],
    c1_salts: &[[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]],
    c2_salts: &[[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]],
    hash: HashFn,
) -> Result<([u8; 32], [u8; 32]), V5SpendMessageError> {
    let c1_tree = build_state_only_private_merkle_tree(
        hash,
        V5_LAYER_ZERO_BINARY_DEPTH,
        CIRCLE_C1_LAYER0_TAG,
        V5_C1_LEAF_BYTES,
        c1_values,
        c1_salts,
    )?;
    let c1_root = c1_tree.root();
    drop(c1_tree);
    let c2_tree = build_state_only_private_merkle_tree(
        hash,
        V5_LAYER_ZERO_BINARY_DEPTH,
        CIRCLE_C2_LAYER0_TAG,
        V5_C2_LEAF_BYTES,
        c2_values,
        c2_salts,
    )?;
    Ok((c1_root, c2_tree.root()))
}

/// Encode and commit a pre-built message set.
pub fn encode_and_commit_v5_spend_messages(
    messages: V5SpendMessages,
    c1_salts: &[[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]],
    c2_salts: &[[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]],
    hash: HashFn,
) -> Result<V5EncodedLayerZero, V5SpendMessageError> {
    let (encoded_c1, encoded_c2) = encode_messages(&messages)?;
    let c1_values = pack_c1_values(&encoded_c1)?;
    let c2_values = pack_c2_values(&encoded_c2)?;
    let (c1_root, c2_root) = v5_layer_zero_roots(&c1_values, &c2_values, c1_salts, c2_salts, hash)?;
    Ok(V5EncodedLayerZero {
        messages,
        encoded_c1,
        encoded_c2,
        c1_values,
        c2_values,
        c1_root,
        c2_root,
    })
}

fn gamma_combine_v5_values(
    c1: &[Vec<M31>],
    c2: &[Vec<QM31>],
    gamma: QM31,
    expected_len: usize,
) -> Result<Vec<QM31>, V5SpendMessageError> {
    if c1.len() != V5_C1_LANES
        || c2.len() != V5_C2_LANES
        || c1.iter().any(|column| column.len() != expected_len)
        || c2.iter().any(|column| column.len() != expected_len)
    {
        return Err(V5SpendMessageError::MessageShape);
    }
    let powers = qm31_power_table::<V5_TOTAL_LANES>(gamma);
    let mut combined = vec![QM31::ZERO; expected_len];
    for (column, power) in c1.iter().zip(powers[..V5_C1_LANES].iter().copied()) {
        for (output, value) in combined.iter_mut().zip(column) {
            *output = output.add(power.mul_m31(*value));
        }
    }
    for (column, power) in c2.iter().zip(powers[V5_C1_LANES..].iter().copied()) {
        for (output, value) in combined.iter_mut().zip(column) {
            *output = output.add(power.mul(*value));
        }
    }
    Ok(combined)
}

/// Gamma-combine all nineteen natural-basis messages in generator order.
pub fn gamma_combine_v5_messages(
    messages: &V5SpendMessages,
    gamma: QM31,
) -> Result<Vec<QM31>, V5SpendMessageError> {
    gamma_combine_v5_values(&messages.c1, &messages.c2, gamma, V5_TRACE_ROWS)
}

/// Gamma-combine all nineteen real log-19 codewords in generator order.
pub fn gamma_combine_v5_codewords(
    layer_zero: &V5EncodedLayerZero,
    gamma: QM31,
) -> Result<Vec<QM31>, V5SpendMessageError> {
    gamma_combine_v5_values(
        &layer_zero.encoded_c1,
        &layer_zero.encoded_c2,
        gamma,
        V5_CODEWORD_LEN,
    )
}

fn flatten_combined_leaves(leaves: &[[u8; COMBINED_LAYER_LEAF_BYTES]]) -> Vec<u8> {
    let mut values = Vec::with_capacity(leaves.len() * COMBINED_LAYER_LEAF_BYTES);
    for leaf in leaves {
        values.extend_from_slice(leaf);
    }
    values
}

/// Build a complete host-side PCS suffix from a real nineteen-lane message
/// set.  Gamma, fold challenges, query indices and all salts are explicit
/// caller inputs; this function neither samples nor claims a Fiat--Shamir
/// transcript.  The current Component C makes this a CU stress path only.
pub fn build_v5_cu_stress_pcs_artifact(
    messages: V5SpendMessages,
    gamma: QM31,
    alphas: [QM31; V5_PCS_ROUNDS],
    queries: &[u32],
    salts: V5PcsSalts<'_>,
    hash: HashFn,
) -> Result<V5CuStressPcsArtifact, V5SpendMessageError> {
    let layer_zero = encode_and_commit_v5_spend_messages(messages, salts.c1, salts.c2, hash)?;
    let combined_message = gamma_combine_v5_messages(&layer_zero.messages, gamma)?;
    let combined_codeword = gamma_combine_v5_codewords(&layer_zero, gamma)?;
    let folds = build_fold_commitments_for_domain_log(
        &combined_codeword,
        &combined_message,
        alphas,
        V5_DOMAIN_LOG,
        hash,
    )?;
    let later_values: [Vec<u8>; V5_LATER_LAYERS] =
        core::array::from_fn(|layer| flatten_combined_leaves(&folds.committed_leaves[layer]));

    let indices = derive_circle_line_query_indices_for_count(queries, V5_LAYER_ZERO_LEAVES)?;
    let section_indices: [&[u32]; V5_PRIVATE_SECTIONS] = [
        &indices.layer0,
        &indices.layer0,
        &indices.later[0],
        &indices.later[1],
        &indices.later[2],
    ];
    let section_values: [&[u8]; V5_PRIVATE_SECTIONS] = [
        &layer_zero.c1_values,
        &layer_zero.c2_values,
        &later_values[0],
        &later_values[1],
        &later_values[2],
    ];
    let section_salts: [&[[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]]; V5_PRIVATE_SECTIONS] = [
        salts.c1,
        salts.c2,
        salts.later[0],
        salts.later[1],
        salts.later[2],
    ];

    let mut roots = [[0u8; 32]; V5_PRIVATE_SECTIONS];
    let mut opening_bytes = Vec::new();
    let mut section_bytes = [0usize; V5_PRIVATE_SECTIONS];
    let mut frontier_nodes = [0usize; V5_PRIVATE_SECTIONS];
    for section in 0..V5_PRIVATE_SECTIONS {
        let tree = build_state_only_private_merkle_tree(
            hash,
            V5_PRIVATE_DEPTHS[section],
            V5_PRIVATE_TAGS[section],
            V5_PRIVATE_WIDTHS[section],
            section_values[section],
            section_salts[section],
        )?;
        roots[section] = tree.root();
        let opening = serialize_state_only_private_opening(
            &tree,
            section_values[section],
            section_salts[section],
            section_indices[section],
        )?;
        section_bytes[section] = opening.bytes.len();
        frontier_nodes[section] = opening.frontier_nodes;
        opening_bytes.extend_from_slice(&opening.bytes);
    }
    if roots[0] != layer_zero.c1_root || roots[1] != layer_zero.c2_root {
        return Err(V5SpendMessageError::LayerZeroRootMismatch);
    }

    let roots = V5PcsRoots {
        c1: roots[0],
        c2: roots[1],
        later: [roots[2], roots[3], roots[4]],
    };
    let openings = V5BuiltPcsOpenings {
        bytes: opening_bytes,
        indices,
        section_bytes,
        frontier_nodes,
    };
    Ok(V5CuStressPcsArtifact {
        security_status: V5_CU_STRESS_ONLY_STATUS,
        layer_zero,
        combined_message,
        combined_codeword,
        folds,
        later_values,
        roots,
        openings,
    })
}

/// Authenticate the complete five-section v5 suffix with the existing
/// private-opening grammar, but with v5's 256-byte C1 width.
pub fn verify_v5_pcs_openings<'a>(
    hash: HashFn,
    roots: &V5PcsRoots,
    queries: &[u32],
    proof_bytes: &'a [u8],
) -> Result<VerifiedV5PcsOpenings<'a>, V5SpendMessageError> {
    let indices = derive_circle_line_query_indices_for_count(queries, V5_LAYER_ZERO_LEAVES)?;
    let section_indices: [&[u32]; V5_PRIVATE_SECTIONS] = [
        &indices.layer0,
        &indices.layer0,
        &indices.later[0],
        &indices.later[1],
        &indices.later[2],
    ];
    let roots = roots.as_array();
    let mut remainder = proof_bytes;
    let mut parsed: [Option<StateOnlyPrivateOpening<'a>>; V5_PRIVATE_SECTIONS] =
        [None; V5_PRIVATE_SECTIONS];
    for section in 0..V5_PRIVATE_SECTIONS {
        let (opening, next) = verify_state_only_private_opening_from_proof(
            hash,
            &roots[section],
            V5_PRIVATE_DEPTHS[section],
            V5_PRIVATE_TAGS[section],
            V5_PRIVATE_WIDTHS[section],
            section_indices[section],
            remainder,
        )
        .map_err(|error| V5SpendMessageError::OpeningVerify {
            section: section as u8,
            error,
        })?;
        parsed[section] = Some(opening);
        remainder = next;
    }
    if !remainder.is_empty() {
        return Err(V5SpendMessageError::OpeningTrailingBytes {
            offset: proof_bytes.len() - remainder.len(),
            remaining: remainder.len(),
        });
    }
    Ok(VerifiedV5PcsOpenings {
        c1: parsed[0].unwrap(),
        c2: parsed[1].unwrap(),
        later: [parsed[2].unwrap(), parsed[3].unwrap(), parsed[4].unwrap()],
        indices,
        end: proof_bytes.len(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::{CM31, M31};
    use aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_active_rows_v3;
    use aspis_statement::atomic_state_only_trace::atomic_merkle_root_v3;
    use aspis_statement::{
        derive_nullifier, derive_owner_key, note_commitment, output_commitment, Digest, MerklePath,
        SpendPublic,
    };

    use crate::v5_mask::{sample_atomic_m31_lane_masks, Qm31WordSource, V5_ACTIVE_ROW_END};
    use crate::HOST_HASH;

    struct XorShift(u64);

    impl Qm31WordSource for XorShift {
        fn next_word(&mut self) -> u32 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            (x >> 21) as u32
        }
    }

    fn q(seed: u32) -> QM31 {
        QM31 {
            c0: CM31::new(M31(seed * 1_003 + 1), M31(seed * 1_009 + 3)),
            c1: CM31::new(M31(seed * 1_021 + 5), M31(seed * 1_031 + 7)),
        }
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn fixture() -> (AtomicPaymentStatementV4, SpendWitness) {
        let nullifier_key = digest(101);
        let input_salt = digest(301);
        let output_salt = digest(501);
        let output_owner_key = digest(701);
        let asset_id = M31(17);
        let value = 1_000_000;
        let value_out = 999_999;
        let merkle_path = MerklePath {
            siblings: (0..20).map(|level| digest(1_000 + 31 * level)).collect(),
            index: 0x5_a5a5,
        };
        let witness = SpendWitness {
            nullifier_key,
            input_salt,
            output_salt,
            output_owner_key,
            input_asset_id: asset_id,
            value,
            value_out,
            merkle_path,
        };
        let input = note_commitment(
            &derive_owner_key(&nullifier_key),
            value,
            asset_id,
            &input_salt,
        );
        let output = output_commitment(&output_owner_key, value_out, asset_id, &output_salt);
        let statement = AtomicPaymentStatementV4 {
            pool: [0x5a; 32],
            sequence: 73,
            spend: SpendPublic {
                anchor: atomic_merkle_root_v3(input, &witness.merkle_path).unwrap(),
                nullifier: derive_nullifier(&nullifier_key, &input_salt),
                output_commitment: output,
                asset_id,
                fee: 1,
            },
            output_anchor: atomic_merkle_root_v3(output, &witness.merkle_path).unwrap(),
            deployment_domain: [0x5d; 32],
        };
        (statement, witness)
    }

    fn component_a() -> [M31BlockMask; V5_C1_LANES] {
        let mut sources: [XorShift; V5_C1_LANES] =
            core::array::from_fn(|lane| XorShift(0xa531_0000_0000_0001 ^ lane as u64));
        sample_atomic_m31_lane_masks(&mut sources).unwrap()
    }

    fn hcopy_padding() -> [QM31; V5_TRACE_ROWS] {
        let mut active = [false; V5_TRACE_ROWS];
        for &row in atomic_state_only_copy_active_rows_v3() {
            active[usize::from(row)] = true;
        }
        let pivot = (0..V5_TRACE_ROWS).find(|row| !active[*row]).unwrap();
        let mut padding = [QM31::ZERO; V5_TRACE_ROWS];
        let mut sum = QM31::ZERO;
        for row in 0..V5_TRACE_ROWS {
            if !active[row] && row != pivot {
                padding[row] = q(10_000 + row as u32);
                sum = sum.add(padding[row]);
            }
        }
        padding[pivot] = sum.neg();
        padding
    }

    fn components() -> (
        [M31BlockMask; V5_C1_LANES],
        [QM31; V5_TRACE_ROWS],
        V5StructuredBLane,
        V5ComponentCLane,
    ) {
        let b_mask = V5SumcheckMask::sample(&mut XorShift(0xb500_0000_0000_0001)).unwrap();
        let pads = core::array::from_fn(|index| q(20_000 + index as u32));
        let b = V5StructuredBLane::encode(&b_mask, &pads, q(29_999)).unwrap();
        let c = V5ComponentCLane::sample(&mut XorShift(0xc500_0000_0000_0001)).unwrap();
        (component_a(), hcopy_padding(), b, c)
    }

    fn salts_for_count(domain: u8, count: usize) -> Vec<[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]> {
        (0..count)
            .map(|leaf| {
                core::array::from_fn(|byte| {
                    domain
                        .wrapping_add((leaf as u8).wrapping_mul(37))
                        .wrapping_add((byte as u8).wrapping_mul(19))
                })
            })
            .collect()
    }

    fn salts(domain: u8) -> Vec<[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]> {
        salts_for_count(domain, V5_LAYER_ZERO_LEAVES)
    }

    fn iterator_reference_pack_c1_values(
        encoded: &[Vec<M31>],
    ) -> Result<Vec<u8>, V5SpendMessageError> {
        if encoded.len() != V5_C1_LANES
            || encoded.iter().any(|column| column.len() != V5_CODEWORD_LEN)
        {
            return Err(V5SpendMessageError::MessageShape);
        }
        let mut values = Vec::with_capacity(V5_LAYER_ZERO_LEAVES * V5_C1_LEAF_BYTES);
        for fibre in 0..V5_LAYER_ZERO_LEAVES {
            for slot in 0..V5_FIBRE_SLOTS {
                let index = V5_FIBRE_SLOTS * fibre + slot;
                for column in encoded {
                    values.extend_from_slice(&column[index].to_le_bytes());
                }
            }
        }
        Ok(values)
    }

    #[test]
    fn indexed_c1_packer_matches_original_expression_and_ordinals() {
        for slot in 0..V5_FIBRE_SLOTS {
            for lane in 0..V5_C1_LANES {
                for byte in 0..4 {
                    assert_eq!(
                        c1_leaf_m31_byte_ordinal(slot, lane, byte),
                        (slot * V5_C1_LANES + lane) * 4 + byte
                    );
                }
            }
        }

        let mut encoded = vec![vec![M31::ZERO; V5_CODEWORD_LEN]; V5_C1_LANES];
        for lane in 0..V5_C1_LANES {
            for slot in 0..V5_FIBRE_SLOTS {
                encoded[lane][slot] = M31((1 + 17 * lane + slot) as u32);
                encoded[lane][4 * (V5_LAYER_ZERO_LEAVES - 1) + slot] =
                    M31((1_001 + 19 * lane + slot) as u32);
            }
        }
        assert_eq!(
            pack_c1_values(&encoded),
            iterator_reference_pack_c1_values(&encoded)
        );

        let wrong_lane_count = &encoded[..V5_C1_LANES - 1];
        assert_eq!(
            pack_c1_values(wrong_lane_count),
            iterator_reference_pack_c1_values(wrong_lane_count)
        );
        encoded[3].pop();
        assert_eq!(
            pack_c1_values(&encoded),
            iterator_reference_pack_c1_values(&encoded)
        );
    }

    #[test]
    fn structured_b_has_the_pinned_layout_and_atomic_relation() {
        let mask = V5SumcheckMask::sample(&mut XorShift(0xb517_1a90_5eed_0001)).unwrap();
        let pads = core::array::from_fn(|index| q(30_000 + index as u32));
        let pivot_pad = q(39_999);
        let lane = V5StructuredBLane::encode(&mask, &pads, pivot_pad).unwrap();
        let values = lane.values();
        let coordinates = mask.commitment_coordinates();

        assert_eq!(values[V5_B_INITIAL_CLAIM_ROW], coordinates[0]);
        for round in 0..10 {
            let start = 1 + round * V5_B_ROUND_FREE_COEFFICIENTS;
            for offset in 1..V5_B_ROUND_COEFFICIENTS {
                assert_eq!(
                    values[b_block_row(round, offset)],
                    coordinates[start + offset - 1]
                );
            }
            assert!((V5_B_ROUND_COEFFICIENTS..V5_B_ROUND_BLOCK_ROWS)
                .all(|offset| values[b_block_row(round, offset)] == QM31::ZERO));
        }
        assert_eq!(
            &values[V5_B_PAD_START..V5_B_PAD_START + V5_B_PAD_COORDINATES],
            &pads
        );
        assert_eq!(lane.pivot_pad(), pivot_pad);
        assert_eq!(atomic_inactive_sum_qm31(values), Some(pivot_pad));

        let replacement_pad = q(40_000);
        let replacement = V5StructuredBLane::encode(&mask, &pads, replacement_pad).unwrap();
        let delta = replacement_pad.add(pivot_pad.neg());
        for row in 0..V5_TRACE_ROWS {
            let expected_delta = if row == V5_B_INACTIVE_PIVOT_ROW {
                delta
            } else {
                QM31::ZERO
            };
            assert_eq!(
                replacement.values()[row].add(values[row].neg()),
                expected_delta
            );
        }
    }

    #[test]
    fn component_b_copy_and_c2_slot_constructor_preserve_exact_order() {
        let mask = V5SumcheckMask::sample(&mut XorShift(0xb517_c2c0_5eed_0001)).unwrap();
        let pads = core::array::from_fn(|index| q(41_000 + index as u32));
        let lane = V5StructuredBLane::encode(&mask, &pads, q(49_999)).unwrap();

        let copied = component_b_message_values(&lane);
        assert_eq!(copied, lane.values().to_vec());

        let hcopy = vec![q(50_001), q(50_002)];
        let component_c = vec![q(50_003), q(50_004), q(50_005)];
        let assembled = assemble_v5_c2_messages(hcopy.clone(), copied.clone(), component_c.clone());
        assert_eq!(assembled[V5_HCOPY_LANE], hcopy);
        assert_eq!(assembled[V5_COMPONENT_B_LANE], copied);
        assert_eq!(assembled[V5_COMPONENT_C_LANE], component_c);
    }

    #[test]
    fn real_atomic_messages_preserve_semantics_and_all_inactive_relations() {
        let (statement, witness) = fixture();
        let mut original_atomic = build_atomic_state_only_trace_v3(&statement, &witness).unwrap();
        let original = core::mem::take(&mut original_atomic.trace);
        let (a, padding, b, c) = components();
        let lambda = q(40_001);
        let chi = q(40_002);
        let messages =
            build_v5_spend_messages(&statement, &witness, &a, &padding, &b, &c, lambda, chi)
                .unwrap();

        assert_eq!(messages.c1.len(), 16);
        assert_eq!(messages.c2.len(), 3);
        assert!(messages
            .c1
            .iter()
            .chain(core::iter::empty())
            .all(|column| column.len() == V5_TRACE_ROWS));
        assert!(messages
            .c2
            .iter()
            .all(|column| column.len() == V5_TRACE_ROWS));
        for lane in 0..V5_C1_LANES {
            assert_eq!(
                &messages.c1[lane][..=V5_ACTIVE_ROW_END],
                &original.c1[lane][..=V5_ACTIVE_ROW_END]
            );
            assert_eq!(
                atomic_inactive_sum_m31(&messages.c1[lane]),
                atomic_inactive_sum_m31(&original.c1[lane])
            );
        }
        assert_eq!(
            atomic_inactive_sum_qm31(&messages.c2[V5_HCOPY_LANE]),
            Some(QM31::ZERO)
        );
        assert_eq!(
            atomic_inactive_sum_qm31(&messages.c2[V5_COMPONENT_B_LANE]),
            Some(b.pivot_pad())
        );
        assert_eq!(
            atomic_inactive_sum_qm31(&messages.c2[V5_COMPONENT_C_LANE]),
            Some(QM31::ZERO)
        );
        assert_eq!(
            state_only_copy_helper_sum(&messages.c2[V5_HCOPY_LANE]),
            Some(QM31::ZERO)
        );
        assert_eq!(messages.c2[V5_COMPONENT_B_LANE], b.values());
        assert_eq!(messages.c2[V5_COMPONENT_C_LANE], c.values());
    }

    #[test]
    fn real_log19_codewords_make_reproducible_256_and_192_byte_private_roots() {
        let (statement, witness) = fixture();
        let (a, padding, b, c) = components();
        let messages = build_v5_spend_messages(
            &statement,
            &witness,
            &a,
            &padding,
            &b,
            &c,
            q(50_001),
            q(50_002),
        )
        .unwrap();
        let c1_salts = salts(0xc1);
        let c2_salts = salts(0xc2);
        let built =
            encode_and_commit_v5_spend_messages(messages, &c1_salts, &c2_salts, HOST_HASH).unwrap();

        assert_eq!(built.encoded_c1.len(), 16);
        assert_eq!(built.encoded_c2.len(), 3);
        assert!(built
            .encoded_c1
            .iter()
            .all(|word| word.len() == V5_CODEWORD_LEN));
        assert!(built
            .encoded_c2
            .iter()
            .all(|word| word.len() == V5_CODEWORD_LEN));
        assert_eq!(V5_CODEWORD_LEN / V5_TRACE_ROWS, 512);
        assert_eq!(built.c1_values.len(), V5_LAYER_ZERO_LEAVES * 256);
        assert_eq!(built.c2_values.len(), V5_LAYER_ZERO_LEAVES * 192);
        assert_ne!(built.c1_root, [0u8; 32]);
        assert_ne!(built.c2_root, [0u8; 32]);

        let repeated = v5_layer_zero_roots(
            &built.c1_values,
            &built.c2_values,
            &c1_salts,
            &c2_salts,
            HOST_HASH,
        )
        .unwrap();
        assert_eq!(repeated, (built.c1_root, built.c2_root));
    }

    #[test]
    fn complete_cu_stress_pcs_round_trips_all_five_private_sections() {
        let (statement, witness) = fixture();
        let (a, padding, b, c) = components();
        let messages = build_v5_spend_messages(
            &statement,
            &witness,
            &a,
            &padding,
            &b,
            &c,
            q(60_001),
            q(60_002),
        )
        .unwrap();
        let c1_salts = salts(0x51);
        let c2_salts = salts(0x52);
        let later_salts: [Vec<[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]>; V5_LATER_LAYERS] = [
            salts_for_count(0x61, 1 << 15),
            salts_for_count(0x62, 1 << 13),
            salts_for_count(0x63, 1 << 11),
        ];
        let queries: [u32; 18] =
            core::array::from_fn(|index| ((17 + 7_001 * index) % V5_LAYER_ZERO_LEAVES) as u32);
        let artifact = build_v5_cu_stress_pcs_artifact(
            messages,
            q(60_003),
            [q(60_004), q(60_005), q(60_006), q(60_007)],
            &queries,
            V5PcsSalts {
                c1: &c1_salts,
                c2: &c2_salts,
                later: [&later_salts[0], &later_salts[1], &later_salts[2]],
            },
            HOST_HASH,
        )
        .unwrap();

        assert_eq!(artifact.security_status, V5_CU_STRESS_ONLY_STATUS);
        assert_eq!(artifact.combined_message.len(), V5_TRACE_ROWS);
        assert_eq!(artifact.combined_codeword.len(), V5_CODEWORD_LEN);
        assert_eq!(
            artifact
                .folds
                .committed_evaluations
                .each_ref()
                .map(Vec::len),
            [1 << 17, 1 << 15, 1 << 13]
        );
        assert_eq!(
            artifact.folds.committed_leaves.each_ref().map(Vec::len),
            [1 << 15, 1 << 13, 1 << 11]
        );
        assert_eq!(artifact.folds.final_evaluations.len(), 1 << 11);
        assert_eq!(artifact.folds.final_coefficients.len(), 4);
        assert_eq!(
            artifact.later_values.each_ref().map(Vec::len),
            [64 << 15, 64 << 13, 64 << 11]
        );
        assert!(artifact
            .roots
            .as_array()
            .iter()
            .all(|root| *root != [0; 32]));
        assert_eq!(artifact.openings.indices.layer0.len(), queries.len());
        assert!(artifact
            .openings
            .section_bytes
            .iter()
            .all(|bytes| *bytes > 0));

        let verified = verify_v5_pcs_openings(
            HOST_HASH,
            &artifact.roots,
            &queries,
            &artifact.openings.bytes,
        )
        .unwrap();
        assert_eq!(verified.end, artifact.openings.bytes.len());
        assert_eq!(verified.indices, artifact.openings.indices);

        let opened = [
            verified.c1,
            verified.c2,
            verified.later[0],
            verified.later[1],
            verified.later[2],
        ];
        let packed: [&[u8]; V5_PRIVATE_SECTIONS] = [
            &artifact.layer_zero.c1_values,
            &artifact.layer_zero.c2_values,
            &artifact.later_values[0],
            &artifact.later_values[1],
            &artifact.later_values[2],
        ];
        let indices: [&[u32]; V5_PRIVATE_SECTIONS] = [
            &verified.indices.layer0,
            &verified.indices.layer0,
            &verified.indices.later[0],
            &verified.indices.later[1],
            &verified.indices.later[2],
        ];
        for section in 0..V5_PRIVATE_SECTIONS {
            assert_eq!(opened[section].value_width, V5_PRIVATE_WIDTHS[section]);
            assert_eq!(opened[section].count, indices[section].len());
            for (ordinal, index) in indices[section].iter().copied().enumerate() {
                let start = index as usize * V5_PRIVATE_WIDTHS[section];
                assert_eq!(
                    opened[section].value(ordinal).unwrap(),
                    &packed[section][start..start + V5_PRIVATE_WIDTHS[section]]
                );
            }
        }

        let mut corrupted = artifact.openings.bytes.clone();
        corrupted[2] ^= 1;
        assert!(matches!(
            verify_v5_pcs_openings(HOST_HASH, &artifact.roots, &queries, &corrupted),
            Err(V5SpendMessageError::OpeningVerify { section: 0, .. })
        ));
    }
}
