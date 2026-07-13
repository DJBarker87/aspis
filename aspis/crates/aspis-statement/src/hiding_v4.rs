//! Candidate zero-width hiding padding for the frozen v4 payment trace.
//!
//! This module identifies witness cells which are outside the semantic trace,
//! copy layout, public bindings, and range table multiplicity column. Filling
//! these cells with private randomness preserves the Boolean payment relation
//! while adding entropy to the existing C1 circle-code messages.
//!
//! This is only one component of a hiding construction. In particular it does
//! not by itself hide the multiplicity column, either C2 helper, the payment
//! sumcheck transcript, or every later PCS opening.

use alloc::{vec, vec::Vec};

use aspis_core::field::M31;

use crate::trace_v4::{
    copy_layout, merkle_boundary_layout, source_relation_layout, witness_aux_layout, SpendTraceV4,
    TraceCell, TupleLimb, AUX_ABSORPTION_PRODUCER_ROW_START, AUX_WITNESS_ROW_START,
    MULTIPLICITY_COLUMN, PERMUTATION_COUNT, STATE_AND_INTERFACE_COLUMNS, TRACE_ROWS,
};

/// First row after every frozen auxiliary producer/copy row.
pub const HIDING_PADDING_ROW_START: usize = AUX_ABSORPTION_PRODUCER_ROW_START + PERMUTATION_COUNT;
pub const HIDING_PADDING_ROW_COUNT: usize = TRACE_ROWS - HIDING_PADDING_ROW_START;
/// Columns 0..47 are unused on the padding rows. Column 48 remains the range
/// table multiplicity witness and is deliberately excluded.
pub const HIDING_PADDING_COLUMN_COUNT: usize = STATE_AND_INTERFACE_COLUMNS;
pub const HIDING_PADDING_CELL_COUNT: usize = HIDING_PADDING_ROW_COUNT * HIDING_PADDING_COLUMN_COUNT;
pub const EXPANDED_HIDING_PADDING_CELL_COUNT: usize = 10_702;
/// Pinned after deriving the layout from the frozen v4 trace dependency
/// registry. A selected production layout will promote this guard into the
/// build-time generator alongside the copy-routing fingerprint.
pub const PINNED_EXPANDED_HIDING_PADDING_LAYOUT_FINGERPRINT: u64 = 0xd1a0_49c4_58a3_9d93;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HidingPaddingError {
    Shape,
    RandomnessLength { expected: usize, actual: usize },
}

/// Fixed column-major layout used by the prover's mask sampler.
pub fn hiding_padding_cells_v4() -> Vec<TraceCell> {
    let mut cells = Vec::with_capacity(HIDING_PADDING_CELL_COUNT);
    for column in 0..HIDING_PADDING_COLUMN_COUNT {
        for row in HIDING_PADDING_ROW_START..TRACE_ROWS {
            cells.push(TraceCell {
                row: row as u16,
                column: column as u8,
            });
        }
    }
    cells
}

fn cell_index(cell: TraceCell) -> usize {
    usize::from(cell.row) * (MULTIPLICITY_COLUMN + 1) + usize::from(cell.column)
}

fn mark_cell(used: &mut [bool], cell: TraceCell) {
    used[cell_index(cell)] = true;
}

fn mark_cells<const N: usize>(used: &mut [bool], cells: [TraceCell; N]) {
    for cell in cells {
        mark_cell(used, cell);
    }
}

/// Larger host probe which also reclaims unused cells in the frozen auxiliary
/// slab. The dependency list is derived independently from the trace layouts;
/// the relation-preservation test below is the guard against an omitted read.
/// This layout is not yet selected for the production prover.
pub fn expanded_hiding_padding_cells_v4() -> Vec<TraceCell> {
    let columns = MULTIPLICITY_COLUMN + 1;
    let mut used = vec![false; TRACE_ROWS * columns];

    // The fixed-table multiplicity witness is read on every row.
    for row in 0..TRACE_ROWS {
        mark_cell(
            &mut used,
            TraceCell {
                row: row as u16,
                column: MULTIPLICITY_COLUMN as u8,
            },
        );
    }

    for link in copy_layout().links {
        for tuple in [link.producer, link.consumer] {
            for limb in tuple.limbs {
                if let TupleLimb::Cell(cell) = limb {
                    mark_cell(&mut used, cell);
                }
            }
        }
    }
    for binding in source_relation_layout() {
        for column in [binding.left_column, binding.right_column] {
            mark_cell(
                &mut used,
                TraceCell {
                    row: (AUX_ABSORPTION_PRODUCER_ROW_START + usize::from(binding.block)) as u16,
                    column,
                },
            );
        }
    }
    for binding in merkle_boundary_layout() {
        mark_cell(&mut used, binding.path_bit);
        mark_cells(&mut used, binding.left);
        mark_cells(&mut used, binding.right);
        mark_cells(&mut used, binding.current);
        mark_cells(&mut used, binding.sibling);
    }
    let aux = witness_aux_layout();
    mark_cells(&mut used, aux.nullifier_key);
    mark_cells(&mut used, aux.input_salt);
    mark_cells(&mut used, aux.output_salt);
    mark_cells(&mut used, aux.output_owner_key);
    mark_cell(&mut used, aux.input_asset_id);
    mark_cell(&mut used, aux.value);
    mark_cell(&mut used, aux.value_out);
    for sibling in aux.merkle_siblings {
        mark_cells(&mut used, sibling);
    }
    mark_cell(&mut used, aux.merkle_path_index);
    mark_cells(&mut used, aux.merkle_path_bits);
    mark_cells(&mut used, aux.input_value_limbs);
    mark_cells(&mut used, aux.output_value_limbs);
    mark_cell(&mut used, aux.input_value_reconstruction);
    mark_cell(&mut used, aux.output_value_reconstruction);
    mark_cell(&mut used, aux.output_value_for_balance);
    // Public output asset source, defined directly in the constraint registry.
    mark_cell(
        &mut used,
        TraceCell {
            row: (AUX_ABSORPTION_PRODUCER_ROW_START + 47) as u16,
            column: 34,
        },
    );

    let mut cells = Vec::new();
    for column in 0..STATE_AND_INTERFACE_COLUMNS {
        for row in AUX_WITNESS_ROW_START..TRACE_ROWS {
            let cell = TraceCell {
                row: row as u16,
                column: column as u8,
            };
            if !used[cell_index(cell)] {
                cells.push(cell);
            }
        }
    }
    cells
}

pub fn expanded_hiding_padding_layout_fingerprint() -> u64 {
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    for cell in expanded_hiding_padding_cells_v4() {
        for byte in cell.row.to_le_bytes().into_iter().chain([cell.column]) {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
    hash
}

/// Fill every fixed hiding-padding cell from caller-supplied private
/// randomness. Randomness generation belongs to the host prover; the
/// statement crate only owns the layout and exact mutation.
pub fn apply_hiding_padding_v4(
    trace: &mut SpendTraceV4,
    randomness: &[M31],
) -> Result<(), HidingPaddingError> {
    if trace.c1.iter().any(|column| column.len() != TRACE_ROWS) {
        return Err(HidingPaddingError::Shape);
    }
    if randomness.len() != HIDING_PADDING_CELL_COUNT {
        return Err(HidingPaddingError::RandomnessLength {
            expected: HIDING_PADDING_CELL_COUNT,
            actual: randomness.len(),
        });
    }
    let mut index = 0;
    for column in 0..HIDING_PADDING_COLUMN_COUNT {
        for row in HIDING_PADDING_ROW_START..TRACE_ROWS {
            trace.c1[column][row] = randomness[index];
            index += 1;
        }
    }
    debug_assert_eq!(index, randomness.len());
    // The range-table multiplicity column is outside the layout by design.
    debug_assert_eq!(HIDING_PADDING_COLUMN_COUNT, MULTIPLICITY_COLUMN);
    Ok(())
}

pub fn apply_expanded_hiding_padding_v4(
    trace: &mut SpendTraceV4,
    randomness: &[M31],
) -> Result<(), HidingPaddingError> {
    if trace.c1.iter().any(|column| column.len() != TRACE_ROWS) {
        return Err(HidingPaddingError::Shape);
    }
    let cells = expanded_hiding_padding_cells_v4();
    if randomness.len() != cells.len() {
        return Err(HidingPaddingError::RandomnessLength {
            expected: cells.len(),
            actual: randomness.len(),
        });
    }
    for (cell, value) in cells.into_iter().zip(randomness.iter().copied()) {
        trace.c1[usize::from(cell.column)][usize::from(cell.row)] = value;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        build_payment_helpers_v4, build_spend_trace_v4, derive_nullifier, derive_owner_key,
        evaluate_constraint_row, merkle_root, note_commitment, output_commitment,
        trace_openings_at_point, validate_spend_trace_v4, verify_payment_helpers_v4,
        ConstraintContextV4, Digest, MerklePath, SpendPublic, SpendWitness,
    };
    use aspis_core::field::{CM31, P, QM31};

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + index as u32 * 17))
    }

    fn spend_fixture() -> (SpendPublic, SpendWitness) {
        let nullifier_key = digest(101);
        let input_salt = digest(301);
        let output_salt = digest(501);
        let output_owner_key = digest(701);
        let asset_id = M31(17);
        let value = 1_000_000;
        let value_out = 999_999;
        let owner_key = derive_owner_key(&nullifier_key);
        let note = note_commitment(&owner_key, value, asset_id, &input_salt);
        let merkle_path = MerklePath {
            siblings: (0..20).map(|level| digest(1_000 + level * 29)).collect(),
            index: 0x5_4321,
        };
        let public = SpendPublic {
            anchor: merkle_root(note, &merkle_path).unwrap(),
            nullifier: derive_nullifier(&nullifier_key, &input_salt),
            output_commitment: output_commitment(
                &output_owner_key,
                value_out,
                asset_id,
                &output_salt,
            ),
            asset_id,
            fee: 1,
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
        (public, witness)
    }

    fn test_challenges() -> (QM31, QM31) {
        (
            QM31 {
                c0: CM31::new(M31(101), M31(211)),
                c1: CM31::new(M31(307), M31(401)),
            },
            QM31 {
                c0: CM31::new(M31(503), M31(601)),
                c1: CM31::new(M31(701), M31(809)),
            },
        )
    }

    #[test]
    fn padding_layout_is_exact_and_excludes_the_multiplicity_column() {
        assert_eq!(HIDING_PADDING_ROW_START, 857);
        assert_eq!(HIDING_PADDING_ROW_COUNT, 167);
        assert_eq!(HIDING_PADDING_COLUMN_COUNT, 48);
        assert_eq!(HIDING_PADDING_CELL_COUNT, 8_016);
        let cells = hiding_padding_cells_v4();
        assert_eq!(cells.len(), HIDING_PADDING_CELL_COUNT);
        assert_eq!(
            cells[0],
            TraceCell {
                row: 857,
                column: 0
            }
        );
        assert_eq!(
            cells[HIDING_PADDING_ROW_COUNT - 1],
            TraceCell {
                row: 1023,
                column: 0,
            }
        );
        assert_eq!(
            *cells.last().unwrap(),
            TraceCell {
                row: 1023,
                column: 47,
            }
        );
        assert!(cells
            .iter()
            .all(|cell| usize::from(cell.column) != MULTIPLICITY_COLUMN));
    }

    #[test]
    fn random_padding_preserves_every_boolean_payment_constraint() {
        let (public, witness) = spend_fixture();
        let mut trace = build_spend_trace_v4(&public, &witness).unwrap();
        let original = trace.clone();
        let randomness = (0..HIDING_PADDING_CELL_COUNT)
            .map(|index| M31(((index as u64 * 1_315_423_911 + 0x51a7) % u64::from(P)) as u32))
            .collect::<Vec<_>>();
        apply_hiding_padding_v4(&mut trace, &randomness).unwrap();

        validate_spend_trace_v4(&public, &trace).unwrap();
        let (lambda, chi) = test_challenges();
        let helpers = build_payment_helpers_v4(&trace, lambda, chi).unwrap();
        let original_helpers = build_payment_helpers_v4(&original, lambda, chi).unwrap();
        assert_eq!(helpers.copy_rows, original_helpers.copy_rows);
        assert_eq!(helpers.h1, original_helpers.h1);
        assert_eq!(helpers.h2, original_helpers.h2);
        // Inactive range-row denominator values are deliberately retained in
        // the cleared identity, so `range_rows` records the padding values.
        // Their zero producer weights make the helper itself unchanged.
        verify_payment_helpers_v4(&helpers, chi).unwrap();
        let context = ConstraintContextV4 {
            public: &public,
            trace: &trace,
            helpers: &helpers,
            chi,
        };
        for row in 0..TRACE_ROWS {
            assert!(evaluate_constraint_row(&context, row)
                .unwrap()
                .iter()
                .all(|residual| *residual == QM31::ZERO));
        }

        let point: [QM31; 10] = core::array::from_fn(|index| QM31 {
            c0: CM31::new(M31(101 + index as u32 * 13), M31(211 + index as u32 * 17)),
            c1: CM31::new(M31(307 + index as u32 * 19), M31(401 + index as u32 * 23)),
        });
        let before = trace_openings_at_point(&original, &original_helpers, &point).unwrap();
        let after = trace_openings_at_point(&trace, &helpers, &point).unwrap();
        for column in 0..HIDING_PADDING_COLUMN_COUNT {
            assert_ne!(before.c1[column], after.c1[column]);
        }
        assert_eq!(
            before.c1[MULTIPLICITY_COLUMN],
            after.c1[MULTIPLICITY_COLUMN]
        );
        assert_eq!(before.c2, after.c2);
    }

    #[test]
    fn expanded_padding_preserves_every_boolean_payment_constraint() {
        let (public, witness) = spend_fixture();
        let mut trace = build_spend_trace_v4(&public, &witness).unwrap();
        let original = trace.clone();
        let cells = expanded_hiding_padding_cells_v4();
        std::eprintln!("expanded hiding padding cells: {}", cells.len());
        std::eprintln!(
            "expanded hiding padding fingerprint: {:#018x}",
            expanded_hiding_padding_layout_fingerprint()
        );
        let mut per_column = [0usize; STATE_AND_INTERFACE_COLUMNS];
        for cell in &cells {
            per_column[usize::from(cell.column)] += 1;
        }
        std::eprintln!("expanded hiding padding per column: {per_column:?}");
        assert_eq!(cells.len(), EXPANDED_HIDING_PADDING_CELL_COUNT);
        assert_eq!(
            expanded_hiding_padding_layout_fingerprint(),
            PINNED_EXPANDED_HIDING_PADDING_LAYOUT_FINGERPRINT
        );
        let randomness = (0..cells.len())
            .map(|index| M31(((index as u64 * 2_654_435_761 + 0xa517) % u64::from(P)) as u32))
            .collect::<Vec<_>>();
        apply_expanded_hiding_padding_v4(&mut trace, &randomness).unwrap();

        validate_spend_trace_v4(&public, &trace).unwrap();
        let (lambda, chi) = test_challenges();
        let helpers = build_payment_helpers_v4(&trace, lambda, chi).unwrap();
        let original_helpers = build_payment_helpers_v4(&original, lambda, chi).unwrap();
        assert_eq!(helpers.copy_rows, original_helpers.copy_rows);
        assert_eq!(helpers.h1, original_helpers.h1);
        assert_eq!(helpers.h2, original_helpers.h2);
        verify_payment_helpers_v4(&helpers, chi).unwrap();
        let context = ConstraintContextV4 {
            public: &public,
            trace: &trace,
            helpers: &helpers,
            chi,
        };
        for row in 0..TRACE_ROWS {
            assert!(evaluate_constraint_row(&context, row)
                .unwrap()
                .iter()
                .all(|residual| *residual == QM31::ZERO));
        }
    }
}
