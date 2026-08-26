//! Relation-free C1 masking layout for the Pool V1 payment trace.
//!
//! This is a host/compiler inventory.  The allocation-bounded terminal omits
//! the corresponding zero constraints, but does not build this `Vec` on SBF.

use alloc::vec::Vec;

use crate::{poseidon2::POSEIDON2_WIDTH, trace_v4::TraceCell};

use super::{
    payment_semantic_registry::{
        build_pool_v1_payment_semantic_registry_v1, pool_v1_payment_aux_cell_is_used_v1,
        pool_v1_payment_value_aux_v1, PoolV1PaymentSemanticRegistryErrorV1,
        PoolV1PaymentTupleLimbV1,
    },
    payment_trace::{
        PoolV1PaymentTraceVariantV1, POOL_V1_PAYMENT_TRACE_BLOCK_ROWS,
        POOL_V1_PAYMENT_TRACE_PERMUTATION_ROWS, POOL_V1_PAYMENT_TRACE_ROWS,
    },
};

pub const POOL_V1_PAYMENT_RELATION_FREE_PADDING_LOCAL_ROW_START_V1: usize = 13;

fn auxiliary_cell_is_relation_used(row: usize, column: usize) -> bool {
    if pool_v1_payment_aux_cell_is_used_v1(row, column) {
        return true;
    }
    // Direct-range lanes explicitly bind column ten to zero in the successor
    // and xor12 views.  They are not witness payload cells, but are relation
    // inputs and therefore cannot be masking material.
    (0..3).any(|value| {
        let base = usize::from(pool_v1_payment_value_aux_v1(value).unwrap().source.row);
        column == 10 && (row == base + 1 || row == (base ^ 12))
    })
}

/// Every Pool payment C1 cell which is absent from Poseidon, payment
/// semantics, public bindings, and both variants' copy registries.
///
/// The ordered inventory is deliberately variant-independent.  It contains
/// rows 13..15 of the 49 permutation blocks and undeclared cells in the
/// auxiliary tail.  The registry walk is an independent mechanical guard
/// that excludes any affine copy endpoint if a future layout changes.
pub fn pool_v1_payment_relation_free_mask_cells_v1(
) -> Result<Vec<TraceCell>, PoolV1PaymentSemanticRegistryErrorV1> {
    let mut copy_occupied = [false; POOL_V1_PAYMENT_TRACE_ROWS * POSEIDON2_WIDTH];
    for variant in [
        PoolV1PaymentTraceVariantV1::PrivateTransfer,
        PoolV1PaymentTraceVariantV1::Withdrawal,
    ] {
        for link in build_pool_v1_payment_semantic_registry_v1(variant)?.links {
            for tuple in [link.producer, link.consumer] {
                for limb in tuple.limbs {
                    if let PoolV1PaymentTupleLimbV1::AffineCell { cell, .. } = limb {
                        copy_occupied[usize::from(cell.column) * POOL_V1_PAYMENT_TRACE_ROWS
                            + usize::from(cell.row)] = true;
                    }
                }
            }
        }
    }

    let mut cells = Vec::new();
    for column in 0..POSEIDON2_WIDTH {
        for row in 0..POOL_V1_PAYMENT_TRACE_ROWS {
            let padding = row < POOL_V1_PAYMENT_TRACE_PERMUTATION_ROWS
                && row % POOL_V1_PAYMENT_TRACE_BLOCK_ROWS
                    >= POOL_V1_PAYMENT_RELATION_FREE_PADDING_LOCAL_ROW_START_V1;
            let undeclared_auxiliary = row >= POOL_V1_PAYMENT_TRACE_PERMUTATION_ROWS
                && !auxiliary_cell_is_relation_used(row, column);
            if (padding || undeclared_auxiliary)
                && !copy_occupied[column * POOL_V1_PAYMENT_TRACE_ROWS + row]
            {
                cells.push(TraceCell {
                    row: row as u16,
                    column: column as u8,
                });
            }
        }
    }
    Ok(cells)
}

pub fn pool_v1_payment_relation_free_mask_fingerprint_v1(
) -> Result<u64, PoolV1PaymentSemanticRegistryErrorV1> {
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    for cell in pool_v1_payment_relation_free_mask_cells_v1()? {
        for byte in cell.row.to_le_bytes().into_iter().chain([cell.column]) {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
    Ok(hash)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inventory_is_column_major_complete_and_copy_disjoint() {
        let cells = pool_v1_payment_relation_free_mask_cells_v1().unwrap();
        assert_eq!(cells.len(), 5_428);
        assert_eq!(
            pool_v1_payment_relation_free_mask_fingerprint_v1().unwrap(),
            0xfceb_68f3_197c_3351,
        );
        assert!(cells
            .windows(2)
            .all(|pair| { (pair[0].column, pair[0].row) < (pair[1].column, pair[1].row) }));

        for column in 0..POSEIDON2_WIDTH {
            for row in 0..POOL_V1_PAYMENT_TRACE_ROWS {
                let expected = (row < POOL_V1_PAYMENT_TRACE_PERMUTATION_ROWS
                    && row % POOL_V1_PAYMENT_TRACE_BLOCK_ROWS >= 13)
                    || (row >= POOL_V1_PAYMENT_TRACE_PERMUTATION_ROWS
                        && !auxiliary_cell_is_relation_used(row, column));
                assert_eq!(
                    cells
                        .binary_search_by_key(&(column as u8, row as u16), |cell| {
                            (cell.column, cell.row)
                        })
                        .is_ok(),
                    expected,
                    "cell ({row}, {column})",
                );
            }
        }

        for variant in [
            PoolV1PaymentTraceVariantV1::PrivateTransfer,
            PoolV1PaymentTraceVariantV1::Withdrawal,
        ] {
            for link in build_pool_v1_payment_semantic_registry_v1(variant)
                .unwrap()
                .links
            {
                for tuple in [link.producer, link.consumer] {
                    for limb in tuple.limbs {
                        if let PoolV1PaymentTupleLimbV1::AffineCell { cell, .. } = limb {
                            assert!(!cells.contains(&cell), "copy endpoint {cell:?}");
                        }
                    }
                }
            }
        }
    }
}
