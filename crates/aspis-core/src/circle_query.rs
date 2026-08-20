//! Fixed per-query arithmetic consistency for the M31 circle candidate.
//!
//! The caller supplies leaves that were authenticated elsewhere. This module
//! only canonical-decodes their fixed layouts, gamma-combines layer zero,
//! follows one query through four normalized arity-4 folds, and checks the
//! natural-order terminal tensor. It does not parse a proof, authenticate a
//! Merkle path, drive a transcript, enable tag 24, or accept a proof.

use crate::circle_fri::{
    evaluate_final_line_tensor, evaluate_final_line_tensor_ref, fixed_line_domain_x,
    map_fixed_query, normalized_circle_to_line_arity4_at_fiber,
    normalized_circle_to_line_arity4_prepared,
    normalized_circle_to_line_arity4_prepared_multipliers,
    normalized_circle_to_line_arity4_prepared_polynomial_candidate,
    normalized_line_arity4_at_fiber, normalized_line_arity4_prepared,
    normalized_line_arity4_prepared_multipliers, normalized_line_arity4_prepared_polynomial_refs,
    CircleFriError, FixedQueryPath, FIXED_ARITY4_ROUNDS, FIXED_FINAL_LINE_LAYER,
    FIXED_QUERY_FIBER_COUNT,
};
use crate::field::{
    qm31_m31_dot4_prepared_limbs49_bytes, qm31_power_table, PreparedQm31Multiplier, CM31, M31, P,
    QM31,
};
use crate::proof::{M31_CIRCLE_C1_COLUMNS, M31_CIRCLE_C1_FIBER_LEN, SECOND_PHASE_LEAF_LEN_V4_S2};

pub const CIRCLE_QUERY_C1_LEAF_BYTES: usize = M31_CIRCLE_C1_FIBER_LEN;
pub const CIRCLE_QUERY_C2_LEAF_BYTES: usize = SECOND_PHASE_LEAF_LEN_V4_S2;
pub const CIRCLE_QUERY_LATER_LEAF_BYTES: usize = 4 * 16;
pub const CIRCLE_QUERY_LATER_LAYERS: usize = 3;
pub const CIRCLE_QUERY_C1_SLOT_BYTES: usize = M31_CIRCLE_C1_COLUMNS * 4;
pub const CIRCLE_QUERY_C2_HELPER_BYTES: usize = 4 * 16;
pub const CIRCLE_QUERY_QM31_BYTES: usize = 16;
pub const CIRCLE_QUERY_TOTAL_COLUMNS: usize = M31_CIRCLE_C1_COLUMNS + 2;

/// Byte offset of one M31 C1 symbol inside the slot-major layer-zero leaf.
pub const fn c1_symbol_offset(slot: usize, column: usize) -> Option<usize> {
    if slot < 4 && column < M31_CIRCLE_C1_COLUMNS {
        Some((slot * M31_CIRCLE_C1_COLUMNS + column) * 4)
    } else {
        None
    }
}

/// Byte offset of one QM31 C2 symbol inside the helper-major layer-zero leaf.
pub const fn c2_symbol_offset(helper: usize, slot: usize) -> Option<usize> {
    if helper < 2 && slot < 4 {
        Some((helper * 4 + slot) * CIRCLE_QUERY_QM31_BYTES)
    } else {
        None
    }
}

/// Byte offset of one QM31 slot inside any later 64-byte leaf.
pub const fn later_slot_offset(slot: usize) -> Option<usize> {
    if slot < 4 {
        Some(slot * CIRCLE_QUERY_QM31_BYTES)
    } else {
        None
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CircleQueryLeaf {
    C1,
    C2,
    Later(u8),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CircleQueryError {
    QueryOutOfRange {
        query: usize,
    },
    LeafLength {
        leaf: CircleQueryLeaf,
        expected: usize,
        actual: usize,
    },
    NonCanonicalM31 {
        offset: usize,
    },
    NonCanonicalQm31 {
        leaf: CircleQueryLeaf,
        offset: usize,
    },
    C1KernelInvariant,
    LayerValueMismatch {
        layer: u8,
        offset: usize,
    },
    TerminalValueMismatch {
        final_index: usize,
    },
    Fold(CircleFriError),
}

impl From<CircleFriError> for CircleQueryError {
    fn from(error: CircleFriError) -> Self {
        Self::Fold(error)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CircleQueryCheck {
    pub path: FixedQueryPath,
    pub combined_layer0: [QM31; 4],
    /// Matched values at layers 1, 2, and 3, followed by the terminal value.
    pub folded_values: [QM31; FIXED_ARITY4_ROUNDS as usize],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CircleQueryGammaPowers {
    pub c1_limbs: [[u32; 4]; M31_CIRCLE_C1_COLUMNS],
    pub helpers: [PreparedQm31Multiplier; 2],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CircleQueryFoldInverses {
    pub circle: [M31; 2],
    pub later: [[M31; 3]; CIRCLE_QUERY_LATER_LAYERS],
    pub final_x: M31,
}

impl CircleQueryGammaPowers {
    pub fn new(gamma: QM31) -> Self {
        let powers = qm31_power_table::<CIRCLE_QUERY_TOTAL_COLUMNS>(gamma);
        Self::from_full_table(&powers)
    }

    pub fn from_full_table(powers: &[QM31; CIRCLE_QUERY_TOTAL_COLUMNS]) -> Self {
        let c1: [QM31; M31_CIRCLE_C1_COLUMNS] = core::array::from_fn(|index| powers[index]);
        Self {
            c1_limbs: c1.map(|weight| [weight.c0.a.0, weight.c0.b.0, weight.c1.a.0, weight.c1.b.0]),
            helpers: [
                PreparedQm31Multiplier::new(powers[M31_CIRCLE_C1_COLUMNS]),
                PreparedQm31Multiplier::new(powers[M31_CIRCLE_C1_COLUMNS + 1]),
            ],
        }
    }
}

fn check_leaf_length(
    leaf: &[u8],
    kind: CircleQueryLeaf,
    expected: usize,
) -> Result<(), CircleQueryError> {
    if leaf.len() != expected {
        return Err(CircleQueryError::LeafLength {
            leaf: kind,
            expected,
            actual: leaf.len(),
        });
    }
    Ok(())
}

fn first_noncanonical_m31_offset(bytes: &[u8]) -> Option<usize> {
    bytes
        .chunks_exact(4)
        .enumerate()
        .find_map(|(index, bytes)| {
            M31::from_le_bytes(bytes.try_into().ok()?)
                .is_none()
                .then_some(index * 4)
        })
}

pub(crate) fn canonical_m31_leaf_error(bytes: &[u8]) -> CircleQueryError {
    match first_noncanonical_m31_offset(bytes) {
        Some(offset) => CircleQueryError::NonCanonicalM31 { offset },
        None => CircleQueryError::C1KernelInvariant,
    }
}

/// Decode and gamma-combine one exact layer-zero C1/C2 pair.
///
/// C1 is slot-major with powers `0..=48`; C2 is helper-major with powers 49
/// and 50. The fused C1 byte kernel still reports the first invalid byte
/// offset through an explicit canonicality scan on rejection.
pub fn gamma_combine_fixed_layer0(
    c1_leaf: &[u8],
    c2_leaf: &[u8],
    gamma: QM31,
) -> Result<[QM31; 4], CircleQueryError> {
    let powers = CircleQueryGammaPowers::new(gamma);
    gamma_combine_fixed_layer0_prepared(c1_leaf, c2_leaf, &powers)
}

pub fn gamma_combine_fixed_layer0_prepared(
    c1_leaf: &[u8],
    c2_leaf: &[u8],
    powers: &CircleQueryGammaPowers,
) -> Result<[QM31; 4], CircleQueryError> {
    check_leaf_length(c1_leaf, CircleQueryLeaf::C1, CIRCLE_QUERY_C1_LEAF_BYTES)?;
    check_leaf_length(c2_leaf, CircleQueryLeaf::C2, CIRCLE_QUERY_C2_LEAF_BYTES)?;

    let mut combined = match qm31_m31_dot4_prepared_limbs49_bytes(&powers.c1_limbs, c1_leaf) {
        Some(combined) => combined,
        None => return Err(canonical_m31_leaf_error(c1_leaf)),
    };
    for (helper, power) in powers.helpers.into_iter().enumerate() {
        for (slot, value) in combined.iter_mut().enumerate() {
            let offset = (helper * 4 + slot) * CIRCLE_QUERY_QM31_BYTES;
            let symbol = QM31::from_le_bytes(&c2_leaf[offset..offset + CIRCLE_QUERY_QM31_BYTES])
                .ok_or(CircleQueryError::NonCanonicalQm31 {
                    leaf: CircleQueryLeaf::C2,
                    offset,
                })?;
            *value = value.add(power.mul(symbol));
        }
    }
    Ok(combined)
}

fn decode_later_leaf(leaf: &[u8], layer: u8) -> Result<[QM31; 4], CircleQueryError> {
    let kind = CircleQueryLeaf::Later(layer);
    check_leaf_length(leaf, kind, CIRCLE_QUERY_LATER_LEAF_BYTES)?;
    let mut values = [QM31::ZERO; 4];
    for (slot, value) in values.iter_mut().enumerate() {
        let offset = slot * CIRCLE_QUERY_QM31_BYTES;
        let encoded = &leaf[offset..offset + CIRCLE_QUERY_QM31_BYTES];
        let limbs = [
            u32::from_le_bytes(encoded[0..4].try_into().unwrap()),
            u32::from_le_bytes(encoded[4..8].try_into().unwrap()),
            u32::from_le_bytes(encoded[8..12].try_into().unwrap()),
            u32::from_le_bytes(encoded[12..16].try_into().unwrap()),
        ];
        if limbs.iter().any(|&limb| limb >= P) {
            return Err(CircleQueryError::NonCanonicalQm31 { leaf: kind, offset });
        }
        *value = QM31 {
            c0: CM31::new(M31(limbs[0]), M31(limbs[1])),
            c1: CM31::new(M31(limbs[2]), M31(limbs[3])),
        };
    }
    Ok(values)
}

/// Validate a complete later leaf in the same slot order as
/// `decode_later_leaf`, but materialize only the slot consumed by this
/// transition.  Rejection priority and offsets remain byte-for-byte equal to
/// the full decoder; the other three canonical values are simply not copied
/// into a dead array.
fn decode_selected_later_slot(
    leaf: &[u8],
    layer: u8,
    selected_slot: usize,
) -> Result<QM31, CircleQueryError> {
    let kind = CircleQueryLeaf::Later(layer);
    check_leaf_length(leaf, kind, CIRCLE_QUERY_LATER_LEAF_BYTES)?;
    if selected_slot >= 4 {
        return Err(CircleQueryError::QueryOutOfRange {
            query: selected_slot,
        });
    }
    let mut selected = [0u32; 4];
    for slot in 0..4 {
        let offset = slot * CIRCLE_QUERY_QM31_BYTES;
        let encoded = &leaf[offset..offset + CIRCLE_QUERY_QM31_BYTES];
        let limbs = [
            u32::from_le_bytes(encoded[0..4].try_into().unwrap()),
            u32::from_le_bytes(encoded[4..8].try_into().unwrap()),
            u32::from_le_bytes(encoded[8..12].try_into().unwrap()),
            u32::from_le_bytes(encoded[12..16].try_into().unwrap()),
        ];
        if limbs.iter().any(|&limb| limb >= P) {
            return Err(CircleQueryError::NonCanonicalQm31 { leaf: kind, offset });
        }
        if slot == selected_slot {
            selected = limbs;
        }
    }
    Ok(QM31 {
        c0: CM31::new(M31(selected[0]), M31(selected[1])),
        c1: CM31::new(M31(selected[2]), M31(selected[3])),
    })
}

/// Verification-only entry point for the exact private decoder above.
///
/// This is absent from normal verifier builds.  The isolated Kani package
/// enables `formal-verification` to compare the unchanged production decoder
/// universally with a loop-free reference that Charon/Aeneas can translate.
#[cfg(feature = "formal-verification")]
#[doc(hidden)]
pub fn formal_decode_later_leaf(
    leaf: &[u8],
    layer: u8,
) -> Result<[QM31; 4], CircleQueryError> {
    decode_later_leaf(leaf, layer)
}

/// Verification-only entry point for the exact selected-slot decoder above.
#[cfg(feature = "formal-verification")]
#[doc(hidden)]
pub fn formal_decode_selected_later_slot(
    leaf: &[u8],
    layer: u8,
    selected_slot: usize,
) -> Result<QM31, CircleQueryError> {
    decode_selected_later_slot(leaf, layer, selected_slot)
}

fn require_layer_value(
    layer: u8,
    leaf: &[QM31; 4],
    slot: u8,
    expected: QM31,
) -> Result<(), CircleQueryError> {
    if leaf[usize::from(slot)] != expected {
        return Err(CircleQueryError::LayerValueMismatch {
            layer,
            offset: usize::from(slot) * CIRCLE_QUERY_QM31_BYTES,
        });
    }
    Ok(())
}

/// Check one fixed query's arithmetic chain through the circle candidate.
///
/// The three later leaves must already correspond to authenticated leaf
/// indices `q>>2`, `q>>4`, and `q>>6`; this function checks the slots selected
/// by the intervening two-bit chunks. Merkle authentication and leaf-index
/// binding remain the caller's responsibility.
pub fn check_fixed_circle_query(
    c1_leaf: &[u8],
    c2_leaf: &[u8],
    later_leaves: [&[u8]; CIRCLE_QUERY_LATER_LAYERS],
    query: usize,
    gamma: QM31,
    alphas: [QM31; FIXED_ARITY4_ROUNDS as usize],
    final_natural: [QM31; 4],
) -> Result<CircleQueryCheck, CircleQueryError> {
    let powers = CircleQueryGammaPowers::new(gamma);
    check_fixed_circle_query_prepared(
        c1_leaf,
        c2_leaf,
        later_leaves,
        query,
        &powers,
        alphas,
        final_natural,
    )
}

pub fn check_fixed_circle_query_prepared(
    c1_leaf: &[u8],
    c2_leaf: &[u8],
    later_leaves: [&[u8]; CIRCLE_QUERY_LATER_LAYERS],
    query: usize,
    powers: &CircleQueryGammaPowers,
    alphas: [QM31; FIXED_ARITY4_ROUNDS as usize],
    final_natural: [QM31; 4],
) -> Result<CircleQueryCheck, CircleQueryError> {
    if query >= FIXED_QUERY_FIBER_COUNT {
        return Err(CircleQueryError::QueryOutOfRange { query });
    }
    let path = map_fixed_query(query)?;
    let combined_layer0 = gamma_combine_fixed_layer0_prepared(c1_leaf, c2_leaf, powers)?;
    let later = [
        decode_later_leaf(later_leaves[0], 1)?,
        decode_later_leaf(later_leaves[1], 2)?,
        decode_later_leaf(later_leaves[2], 3)?,
    ];

    let layer1 =
        normalized_circle_to_line_arity4_at_fiber(combined_layer0, alphas[0], path.layer0_fiber)?;
    require_layer_value(1, &later[0], path.later[0].slot, layer1)?;

    let layer2 = normalized_line_arity4_at_fiber(later[0], alphas[1], 1, path.later[0].leaf)?;
    require_layer_value(2, &later[1], path.later[1].slot, layer2)?;

    let layer3 = normalized_line_arity4_at_fiber(later[1], alphas[2], 2, path.later[1].leaf)?;
    require_layer_value(3, &later[2], path.later[2].slot, layer3)?;

    let terminal = normalized_line_arity4_at_fiber(later[2], alphas[3], 3, path.later[2].leaf)?;
    let final_x = fixed_line_domain_x(FIXED_FINAL_LINE_LAYER, path.final_index)?;
    if evaluate_final_line_tensor(final_natural, final_x) != terminal {
        return Err(CircleQueryError::TerminalValueMismatch {
            final_index: path.final_index,
        });
    }

    Ok(CircleQueryCheck {
        path,
        combined_layer0,
        folded_values: [layer1, layer2, layer3, terminal],
    })
}

pub fn check_fixed_circle_query_fully_prepared(
    c1_leaf: &[u8],
    c2_leaf: &[u8],
    later_leaves: [&[u8]; CIRCLE_QUERY_LATER_LAYERS],
    query: usize,
    powers: &CircleQueryGammaPowers,
    inverses: CircleQueryFoldInverses,
    alphas: [QM31; FIXED_ARITY4_ROUNDS as usize],
    final_natural: [QM31; 4],
) -> Result<CircleQueryCheck, CircleQueryError> {
    if query >= FIXED_QUERY_FIBER_COUNT {
        return Err(CircleQueryError::QueryOutOfRange { query });
    }
    let path = map_fixed_query(query)?;
    let combined_layer0 = gamma_combine_fixed_layer0_prepared(c1_leaf, c2_leaf, powers)?;
    let later = [
        decode_later_leaf(later_leaves[0], 1)?,
        decode_later_leaf(later_leaves[1], 2)?,
        decode_later_leaf(later_leaves[2], 3)?,
    ];

    let layer1 = normalized_circle_to_line_arity4_prepared(
        combined_layer0,
        alphas[0],
        inverses.circle[0],
        inverses.circle[1],
    );
    require_layer_value(1, &later[0], path.later[0].slot, layer1)?;
    let layer2 = normalized_line_arity4_prepared(later[0], alphas[1], inverses.later[0]);
    require_layer_value(2, &later[1], path.later[1].slot, layer2)?;
    let layer3 = normalized_line_arity4_prepared(later[1], alphas[2], inverses.later[1]);
    require_layer_value(3, &later[2], path.later[2].slot, layer3)?;
    let terminal = normalized_line_arity4_prepared(later[2], alphas[3], inverses.later[2]);
    if evaluate_final_line_tensor(final_natural, inverses.final_x) != terminal {
        return Err(CircleQueryError::TerminalValueMismatch {
            final_index: path.final_index,
        });
    }
    Ok(CircleQueryCheck {
        path,
        combined_layer0,
        folded_values: [layer1, layer2, layer3, terminal],
    })
}

pub fn check_fixed_layer0_transition_prepared(
    c1_leaf: &[u8],
    c2_leaf: &[u8],
    layer1_leaf: &[u8],
    query: usize,
    powers: &CircleQueryGammaPowers,
    inverses: [M31; 2],
    alpha: PreparedQm31Multiplier,
    alpha_squared: PreparedQm31Multiplier,
) -> Result<(), CircleQueryError> {
    check_layer0_transition_prepared_for_fiber_count(
        c1_leaf,
        c2_leaf,
        layer1_leaf,
        query,
        FIXED_QUERY_FIBER_COUNT,
        powers,
        inverses,
        alpha,
        alpha_squared,
    )
}

pub fn check_layer0_transition_prepared_for_fiber_count(
    c1_leaf: &[u8],
    c2_leaf: &[u8],
    layer1_leaf: &[u8],
    query: usize,
    fiber_count: usize,
    powers: &CircleQueryGammaPowers,
    inverses: [M31; 2],
    alpha: PreparedQm31Multiplier,
    alpha_squared: PreparedQm31Multiplier,
) -> Result<(), CircleQueryError> {
    let combined = gamma_combine_fixed_layer0_prepared(c1_leaf, c2_leaf, powers)?;
    check_combined_layer0_transition_prepared_for_fiber_count(
        combined,
        layer1_leaf,
        query,
        fiber_count,
        inverses,
        alpha,
        alpha_squared,
    )
}

pub(crate) fn check_combined_layer0_transition_prepared_for_fiber_count(
    combined: [QM31; 4],
    layer1_leaf: &[u8],
    query: usize,
    fiber_count: usize,
    inverses: [M31; 2],
    alpha: PreparedQm31Multiplier,
    alpha_squared: PreparedQm31Multiplier,
) -> Result<(), CircleQueryError> {
    let path = crate::circle_fri::map_query_for_fiber_count(query, fiber_count)?;
    let layer1_leaf = decode_later_leaf(layer1_leaf, 1)?;
    let folded = normalized_circle_to_line_arity4_prepared_multipliers(
        combined,
        alpha,
        alpha_squared,
        inverses[0],
        inverses[1],
    );
    require_layer_value(1, &layer1_leaf, path.later[0].slot, folded)
}

/// Exact polynomial-basis variant of
/// [`check_combined_layer0_transition_prepared_for_fiber_count`].
pub(crate) fn check_combined_layer0_transition_prepared_polynomial_for_fiber_count(
    combined: [QM31; 4],
    layer1_leaf: &[u8],
    query: usize,
    fiber_count: usize,
    inverses: [M31; 2],
    alpha: PreparedQm31Multiplier,
    alpha_squared: PreparedQm31Multiplier,
    alpha_cubed: PreparedQm31Multiplier,
) -> Result<(), CircleQueryError> {
    let path = crate::circle_fri::map_query_for_fiber_count(query, fiber_count)?;
    let layer1_leaf = decode_later_leaf(layer1_leaf, 1)?;
    let folded = normalized_circle_to_line_arity4_prepared_polynomial_candidate(
        combined,
        alpha,
        alpha_squared,
        alpha_cubed,
        inverses[0],
        inverses[1],
    );
    require_layer_value(1, &layer1_leaf, path.later[0].slot, folded)
}

pub fn check_fixed_line_transition_prepared(
    incoming_leaf: &[u8],
    outgoing_leaf: &[u8],
    incoming_leaf_index: usize,
    layer: u8,
    inverses: [M31; 3],
    alpha: PreparedQm31Multiplier,
    alpha_squared: PreparedQm31Multiplier,
) -> Result<(), CircleQueryError> {
    let incoming = decode_later_leaf(incoming_leaf, layer)?;
    let outgoing = decode_later_leaf(outgoing_leaf, layer + 1)?;
    let folded =
        normalized_line_arity4_prepared_multipliers(incoming, alpha, alpha_squared, inverses);
    require_layer_value(
        layer + 1,
        &outgoing,
        (incoming_leaf_index & 3) as u8,
        folded,
    )
}

/// Exact polynomial-basis variant of [`check_fixed_line_transition_prepared`].
///
/// Decoding, canonicality, slot selection and errors are unchanged.  Only the
/// reduction schedule for the identical cubic fold polynomial differs.
pub fn check_fixed_line_transition_prepared_polynomial(
    incoming_leaf: &[u8],
    outgoing_leaf: &[u8],
    incoming_leaf_index: usize,
    layer: u8,
    inverses: [M31; 3],
    alpha: PreparedQm31Multiplier,
    alpha_squared: PreparedQm31Multiplier,
    alpha_cubed: PreparedQm31Multiplier,
) -> Result<(), CircleQueryError> {
    check_fixed_line_transition_prepared_polynomial_powers(
        incoming_leaf,
        outgoing_leaf,
        incoming_leaf_index,
        layer,
        inverses,
        &[alpha, alpha_squared, alpha_cubed],
    )
}

/// Borrowed-power form of
/// [`check_fixed_line_transition_prepared_polynomial`].
pub fn check_fixed_line_transition_prepared_polynomial_powers(
    incoming_leaf: &[u8],
    outgoing_leaf: &[u8],
    incoming_leaf_index: usize,
    layer: u8,
    inverses: [M31; 3],
    alpha_powers: &[PreparedQm31Multiplier; 3],
) -> Result<(), CircleQueryError> {
    let incoming = decode_later_leaf(incoming_leaf, layer)?;
    let slot = incoming_leaf_index & 3;
    let outgoing = decode_selected_later_slot(outgoing_leaf, layer + 1, slot)?;
    let folded = normalized_line_arity4_prepared_polynomial_refs(&incoming, alpha_powers, inverses);
    if outgoing != folded {
        return Err(CircleQueryError::LayerValueMismatch {
            layer: layer + 1,
            offset: slot * CIRCLE_QUERY_QM31_BYTES,
        });
    }
    Ok(())
}

pub fn check_fixed_terminal_transition_prepared(
    incoming_leaf: &[u8],
    final_natural: [QM31; 4],
    final_index: usize,
    inverses: [M31; 3],
    final_x: M31,
    alpha: PreparedQm31Multiplier,
    alpha_squared: PreparedQm31Multiplier,
) -> Result<(), CircleQueryError> {
    let incoming = decode_later_leaf(incoming_leaf, 3)?;
    let terminal =
        normalized_line_arity4_prepared_multipliers(incoming, alpha, alpha_squared, inverses);
    if evaluate_final_line_tensor(final_natural, final_x) != terminal {
        return Err(CircleQueryError::TerminalValueMismatch { final_index });
    }
    Ok(())
}

/// Exact polynomial-basis variant of
/// [`check_fixed_terminal_transition_prepared`].
pub fn check_fixed_terminal_transition_prepared_polynomial(
    incoming_leaf: &[u8],
    final_natural: [QM31; 4],
    final_index: usize,
    inverses: [M31; 3],
    final_x: M31,
    alpha: PreparedQm31Multiplier,
    alpha_squared: PreparedQm31Multiplier,
    alpha_cubed: PreparedQm31Multiplier,
) -> Result<(), CircleQueryError> {
    check_fixed_terminal_transition_prepared_polynomial_powers(
        incoming_leaf,
        final_natural,
        final_index,
        inverses,
        final_x,
        &[alpha, alpha_squared, alpha_cubed],
    )
}

/// Borrowed-power form of
/// [`check_fixed_terminal_transition_prepared_polynomial`].
pub fn check_fixed_terminal_transition_prepared_polynomial_powers(
    incoming_leaf: &[u8],
    final_natural: [QM31; 4],
    final_index: usize,
    inverses: [M31; 3],
    final_x: M31,
    alpha_powers: &[PreparedQm31Multiplier; 3],
) -> Result<(), CircleQueryError> {
    check_fixed_terminal_transition_prepared_polynomial_refs(
        incoming_leaf,
        &final_natural,
        final_index,
        inverses,
        final_x,
        alpha_powers,
    )
}

/// Fully borrowed form of
/// [`check_fixed_terminal_transition_prepared_polynomial_powers`].
pub fn check_fixed_terminal_transition_prepared_polynomial_refs(
    incoming_leaf: &[u8],
    final_natural: &[QM31; 4],
    final_index: usize,
    inverses: [M31; 3],
    final_x: M31,
    alpha_powers: &[PreparedQm31Multiplier; 3],
) -> Result<(), CircleQueryError> {
    let incoming = decode_later_leaf(incoming_leaf, 3)?;
    let terminal =
        normalized_line_arity4_prepared_polynomial_refs(&incoming, alpha_powers, inverses);
    if evaluate_final_line_tensor_ref(final_natural, final_x) != terminal {
        return Err(CircleQueryError::TerminalValueMismatch { final_index });
    }
    Ok(())
}

#[cfg(test)]
mod polynomial_transition_tests {
    use super::*;
    use crate::field::{CM31, P};

    fn next_m31(state: &mut u64) -> M31 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        M31((*state % u64::from(P)) as u32)
    }

    fn next_qm31(state: &mut u64) -> QM31 {
        QM31 {
            c0: CM31::new(next_m31(state), next_m31(state)),
            c1: CM31::new(next_m31(state), next_m31(state)),
        }
    }

    fn encode(values: &[QM31; 4]) -> [u8; CIRCLE_QUERY_LATER_LEAF_BYTES] {
        let mut bytes = [0u8; CIRCLE_QUERY_LATER_LEAF_BYTES];
        for (slot, value) in values.iter().enumerate() {
            value.write_le_bytes(&mut bytes[slot * 16..(slot + 1) * 16]);
        }
        bytes
    }

    #[test]
    fn manual_later_decoders_match_qm31_bytes_and_rejection_offsets() {
        let mut state = 0x4c41_5445_5244_4543u64;
        for case in 0..128usize {
            let values = core::array::from_fn(|_| next_qm31(&mut state));
            let encoded = encode(&values);
            assert_eq!(decode_later_leaf(&encoded, 2), Ok(values));
            for selected_slot in 0..4 {
                assert_eq!(
                    decode_selected_later_slot(&encoded, 2, selected_slot),
                    Ok(values[selected_slot]),
                    "case {case}, selected slot {selected_slot}",
                );
            }
        }

        let canonical = encode(&[QM31::ZERO; 4]);
        for bad_slot in 0..4 {
            for bad_limb in 0..4 {
                let offset = bad_slot * CIRCLE_QUERY_QM31_BYTES;
                let limb_offset = offset + bad_limb * 4;
                let mut noncanonical = canonical;
                noncanonical[limb_offset..limb_offset + 4].copy_from_slice(&P.to_le_bytes());
                let expected = CircleQueryError::NonCanonicalQm31 {
                    leaf: CircleQueryLeaf::Later(2),
                    offset,
                };
                assert_eq!(decode_later_leaf(&noncanonical, 2), Err(expected));
                for selected_slot in 0..4 {
                    assert_eq!(
                        decode_selected_later_slot(&noncanonical, 2, selected_slot),
                        Err(expected),
                        "bad slot {bad_slot}, limb {bad_limb}, selected slot {selected_slot}",
                    );
                }
            }
        }
    }

    #[test]
    fn polynomial_transition_wrappers_match_nested_acceptance_and_canonical_teeth() {
        let mut state = 0x504f_4c59_5452_414eu64;
        for case in 0..128usize {
            let incoming_values = core::array::from_fn(|_| next_qm31(&mut state));
            let alpha_value = next_qm31(&mut state);
            let alpha_squared_value = alpha_value.square();
            let alpha = PreparedQm31Multiplier::new(alpha_value);
            let alpha_squared = PreparedQm31Multiplier::new(alpha_squared_value);
            let alpha_cubed = PreparedQm31Multiplier::new(alpha_squared_value.mul(alpha_value));
            let inverses = core::array::from_fn(|_| next_m31(&mut state));
            let folded = normalized_line_arity4_prepared_multipliers(
                incoming_values,
                alpha,
                alpha_squared,
                inverses,
            );
            let incoming = encode(&incoming_values);
            let slot = case & 3;
            let mut outgoing_values = core::array::from_fn(|_| next_qm31(&mut state));
            outgoing_values[slot] = folded;
            let outgoing = encode(&outgoing_values);
            let nested = check_fixed_line_transition_prepared(
                &incoming,
                &outgoing,
                case,
                1,
                inverses,
                alpha,
                alpha_squared,
            );
            let polynomial = check_fixed_line_transition_prepared_polynomial(
                &incoming,
                &outgoing,
                case,
                1,
                inverses,
                alpha,
                alpha_squared,
                alpha_cubed,
            );
            assert_eq!(polynomial, nested, "valid line case {case}");
            assert_eq!(polynomial, Ok(()));

            let final_natural = [folded, QM31::ZERO, QM31::ZERO, QM31::ZERO];
            let final_x = next_m31(&mut state);
            let nested_terminal = check_fixed_terminal_transition_prepared(
                &incoming,
                final_natural,
                case,
                inverses,
                final_x,
                alpha,
                alpha_squared,
            );
            let polynomial_terminal = check_fixed_terminal_transition_prepared_polynomial(
                &incoming,
                final_natural,
                case,
                inverses,
                final_x,
                alpha,
                alpha_squared,
                alpha_cubed,
            );
            assert_eq!(polynomial_terminal, nested_terminal, "terminal case {case}");
            assert_eq!(
                check_fixed_terminal_transition_prepared_polynomial_refs(
                    &incoming,
                    &final_natural,
                    case,
                    inverses,
                    final_x,
                    &[alpha, alpha_squared, alpha_cubed],
                ),
                polynomial_terminal,
                "borrowed terminal case {case}",
            );

            let mut noncanonical_incoming = incoming;
            noncanonical_incoming[..4].copy_from_slice(&P.to_le_bytes());
            assert_eq!(
                check_fixed_line_transition_prepared_polynomial(
                    &noncanonical_incoming,
                    &outgoing,
                    case,
                    1,
                    inverses,
                    alpha,
                    alpha_squared,
                    alpha_cubed,
                ),
                check_fixed_line_transition_prepared(
                    &noncanonical_incoming,
                    &outgoing,
                    case,
                    1,
                    inverses,
                    alpha,
                    alpha_squared,
                ),
                "canonical tooth case {case}",
            );

            let mut noncanonical_outgoing = outgoing;
            let bad_slot = (case >> 2) & 3;
            let bad_limb = case & 3;
            let bad_offset = bad_slot * 16 + bad_limb * 4;
            noncanonical_outgoing[bad_offset..bad_offset + 4].copy_from_slice(&P.to_le_bytes());
            assert_eq!(
                check_fixed_line_transition_prepared_polynomial(
                    &incoming,
                    &noncanonical_outgoing,
                    case,
                    1,
                    inverses,
                    alpha,
                    alpha_squared,
                    alpha_cubed,
                ),
                check_fixed_line_transition_prepared(
                    &incoming,
                    &noncanonical_outgoing,
                    case,
                    1,
                    inverses,
                    alpha,
                    alpha_squared,
                ),
                "outgoing canonical tooth case {case}",
            );
        }
    }
}
