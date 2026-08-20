use aspis_core::circle_fri::{
    evaluate_final_line_tensor_ref, normalized_line_arity4_prepared_polynomial_refs,
};
use aspis_core::circle_query::{
    check_fixed_line_transition_prepared_polynomial_powers,
    check_fixed_terminal_transition_prepared_polynomial_refs, formal_decode_later_leaf,
    formal_decode_selected_later_slot, CircleQueryError, CircleQueryLeaf, CIRCLE_QUERY_QM31_BYTES,
};
use aspis_core::field::{PreparedQm31Multiplier, M31, QM31};

fn decode_later_slot_reference(
    leaf: &[u8; 4 * CIRCLE_QUERY_QM31_BYTES],
    layer: u8,
    slot: usize,
) -> Result<QM31, CircleQueryError> {
    let offset = slot * CIRCLE_QUERY_QM31_BYTES;
    QM31::from_le_bytes(&leaf[offset..offset + CIRCLE_QUERY_QM31_BYTES]).ok_or(
        CircleQueryError::NonCanonicalQm31 {
            leaf: CircleQueryLeaf::Later(layer),
            offset,
        },
    )
}

fn decode_later_leaf_reference(
    leaf: &[u8; 4 * CIRCLE_QUERY_QM31_BYTES],
    layer: u8,
) -> Result<[QM31; 4], CircleQueryError> {
    // Written without an iterator or loop so Charon/Aeneas can translate the
    // reference without introducing an opaque loop boundary.  The four calls
    // preserve production's validation and rejection order exactly.
    Ok([
        decode_later_slot_reference(leaf, layer, 0)?,
        decode_later_slot_reference(leaf, layer, 1)?,
        decode_later_slot_reference(leaf, layer, 2)?,
        decode_later_slot_reference(leaf, layer, 3)?,
    ])
}

fn decode_selected_later_slot_reference(
    leaf: &[u8; 4 * CIRCLE_QUERY_QM31_BYTES],
    layer: u8,
    selected_slot: usize,
) -> Result<QM31, CircleQueryError> {
    if selected_slot >= 4 {
        return Err(CircleQueryError::QueryOutOfRange {
            query: selected_slot,
        });
    }
    // Production validates all four slots before returning the selected one.
    let all = decode_later_leaf_reference(leaf, layer)?;
    Ok(all[selected_slot])
}

/// Loop-simple reference for the two private production decoders and the
/// shallow line-transition driver.  The field fold is deliberately the same
/// public production helper; its value semantics are proved separately in
/// Lean.
pub fn line_transition_reference(
    incoming_leaf: &[u8; 4 * CIRCLE_QUERY_QM31_BYTES],
    outgoing_leaf: &[u8; 4 * CIRCLE_QUERY_QM31_BYTES],
    incoming_leaf_index: usize,
    layer: u8,
    inverses: [M31; 3],
    alpha_powers: &[PreparedQm31Multiplier; 3],
) -> Result<(), CircleQueryError> {
    let incoming = decode_later_leaf_reference(incoming_leaf, layer)?;
    let slot = incoming_leaf_index & 3;
    // Production validates every outgoing slot, in order, before returning
    // the selected one.  A full reference decode preserves that rejection
    // order exactly.
    let outgoing_all = decode_later_leaf_reference(outgoing_leaf, layer.wrapping_add(1))?;
    let outgoing = outgoing_all[slot];
    let folded = normalized_line_arity4_prepared_polynomial_refs(&incoming, alpha_powers, inverses);
    if outgoing != folded {
        return Err(CircleQueryError::LayerValueMismatch {
            layer: layer.wrapping_add(1),
            offset: slot * CIRCLE_QUERY_QM31_BYTES,
        });
    }
    Ok(())
}

/// Loop-simple reference for the terminal decoder and comparison driver.
pub fn terminal_transition_reference(
    incoming_leaf: &[u8; 4 * CIRCLE_QUERY_QM31_BYTES],
    final_natural: &[QM31; 4],
    final_index: usize,
    inverses: [M31; 3],
    final_x: M31,
    alpha_powers: &[PreparedQm31Multiplier; 3],
) -> Result<(), CircleQueryError> {
    let incoming = decode_later_leaf_reference(incoming_leaf, 3)?;
    let terminal =
        normalized_line_arity4_prepared_polynomial_refs(&incoming, alpha_powers, inverses);
    if evaluate_final_line_tensor_ref(final_natural, final_x) != terminal {
        return Err(CircleQueryError::TerminalValueMismatch { final_index });
    }
    Ok(())
}

#[cfg(kani)]
mod proofs {
    use super::*;
    use aspis_core::field::{CM31, P};

    fn any_m31() -> M31 {
        let raw: u32 = kani::any();
        kani::assume(raw < P);
        M31(raw)
    }

    fn any_qm31() -> QM31 {
        QM31 {
            c0: CM31::new(any_m31(), any_m31()),
            c1: CM31::new(any_m31(), any_m31()),
        }
    }

    fn any_inverses() -> [M31; 3] {
        [any_m31(), any_m31(), any_m31()]
    }

    fn any_prepared_powers() -> [PreparedQm31Multiplier; 3] {
        [
            PreparedQm31Multiplier::new(any_qm31()),
            PreparedQm31Multiplier::new(any_qm31()),
            PreparedQm31Multiplier::new(any_qm31()),
        ]
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn unchanged_full_decoder_equals_reference() {
        let leaf: [u8; 64] = kani::any();
        let layer: u8 = kani::any();

        assert_eq!(
            formal_decode_later_leaf(&leaf, layer),
            decode_later_leaf_reference(&leaf, layer)
        );
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn unchanged_selected_decoder_equals_reference() {
        let leaf: [u8; 64] = kani::any();
        let layer: u8 = kani::any();
        let selected_slot: usize = kani::any();
        kani::assume(selected_slot < 4);

        assert_eq!(
            formal_decode_selected_later_slot(&leaf, layer, selected_slot),
            decode_selected_later_slot_reference(&leaf, layer, selected_slot)
        );
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn unchanged_line_transition_equals_reference() {
        let incoming: [u8; 64] = kani::any();
        let outgoing: [u8; 64] = kani::any();
        let incoming_index: usize = kani::any();
        let layer: u8 = if kani::any::<bool>() { 1 } else { 2 };
        let inverses = any_inverses();
        let alpha_powers = any_prepared_powers();

        let production = check_fixed_line_transition_prepared_polynomial_powers(
            &incoming,
            &outgoing,
            incoming_index,
            layer,
            inverses,
            &alpha_powers,
        );
        let reference = line_transition_reference(
            &incoming,
            &outgoing,
            incoming_index,
            layer,
            inverses,
            &alpha_powers,
        );
        assert_eq!(production, reference);
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn unchanged_terminal_transition_equals_reference() {
        let incoming: [u8; 64] = kani::any();
        let final_natural = [any_qm31(), any_qm31(), any_qm31(), any_qm31()];
        let final_index: usize = kani::any();
        let inverses = any_inverses();
        let final_x = any_m31();
        let alpha_powers = any_prepared_powers();

        let production = check_fixed_terminal_transition_prepared_polynomial_refs(
            &incoming,
            &final_natural,
            final_index,
            inverses,
            final_x,
            &alpha_powers,
        );
        let reference = terminal_transition_reference(
            &incoming,
            &final_natural,
            final_index,
            inverses,
            final_x,
            &alpha_powers,
        );
        assert_eq!(production, reference);
    }
}
