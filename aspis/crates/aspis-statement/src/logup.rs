//! LogUp helper construction and exact local-relation oracle.
//!
//! This module pins the algebra Stage 2 will put behind C2. It does not yet
//! connect the columns to the PCS: callers still own C1 layout, selectors,
//! transcript order, the helper commitment, and the `sum(h) = 0` claim.

use alloc::vec::Vec;

use aspis_core::field::{CM31, M31, QM31};

pub const RANGE_TABLE_SIZE: usize = 1 << 10;

/// Canonical little-endian QM31 encoding of [`logup_compression_kat`].
///
/// A change means the tagged-tuple encoding moved and must be treated as a
/// deliberate statement-protocol change, not silently re-pinned.
pub const LOGUP_COMPRESSION_KAT_EXPECTED: [u8; 16] = [
    84, 25, 5, 102, 233, 45, 246, 7, 176, 105, 135, 89, 34, 91, 195, 120,
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LogUpMainRow {
    pub producer_value: QM31,
    pub consumer_value: QM31,
    pub producer_weight: M31,
    pub consumer_weight: M31,
}

/// Three row-local range queries plus one fixed-table consumer. The six
/// private 10-bit limbs occupy two rows, keeping the cleared local identity
/// at degree five (degree six after the zerocheck equality factor).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RangeLogUpRow {
    pub producer_values: [QM31; 3],
    pub producer_weights: [M31; 3],
    pub consumer_value: QM31,
    pub consumer_weight: M31,
}

/// Up to two tagged copy producers and two consumers on one trace row. The
/// frozen v4 layout currently reaches two producers only for the balance
/// bridge; the symmetric shape keeps the verifier rule stable if a future
/// row also receives two consumers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CopyLogUpRow {
    pub producer_values: [QM31; 2],
    pub producer_weights: [M31; 2],
    pub consumer_values: [QM31; 2],
    pub consumer_weights: [M31; 2],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LogUpSide {
    Producer,
    Consumer,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LogUpError {
    LengthMismatch,
    TooManyRangeQueries,
    RangeValueOutOfTable { query: usize, value: u16 },
    ActivePole { row: usize, side: LogUpSide },
    RowRelationMismatch { row: usize },
    TotalSumMismatch,
}

#[inline(always)]
fn lift(value: M31) -> QM31 {
    QM31::from_cm31(CM31::from_m31(value))
}

/// Compress a tagged M31 tuple as `tag + sum_i lambda^(i + 1) * value_i`.
/// Tags are verifier-computable wiring constants, never witness values.
pub fn compress_tagged_tuple(tag: M31, values: &[M31], lambda: QM31) -> QM31 {
    let mut compressed = lift(tag);
    let mut power = lambda;
    for value in values {
        compressed = compressed.add(power.mul_m31(*value));
        power = power.mul(lambda);
    }
    compressed
}

/// Deliberately broken pre-fix compression for adversarial teeth tests.
///
/// This API is absent from normal builds. It assigns coefficient one to both
/// the tag and first data limb, reproducing the coupled collision fixed by
/// [`compress_tagged_tuple`]. Never enable this feature in a verifier build.
#[cfg(feature = "insecure-test-logup-compression")]
pub fn compress_tagged_tuple_insecure_lambda_zero(tag: M31, values: &[M31], lambda: QM31) -> QM31 {
    let mut compressed = lift(tag);
    let mut power = QM31::ONE;
    for value in values {
        compressed = compressed.add(power.mul_m31(*value));
        power = power.mul(lambda);
    }
    compressed
}

/// Fixed host/SBF known-answer vector for tagged-tuple compression.
pub fn logup_compression_kat() -> QM31 {
    let lambda = QM31 {
        c0: CM31 {
            a: M31(1_234_567),
            b: M31(7_654_321),
        },
        c1: CM31 {
            a: M31(99),
            b: M31(101),
        },
    };
    compress_tagged_tuple(
        M31(0x1357_9bdf),
        &[
            M31(0x0246_8ace),
            M31(0x1020_3040),
            M31(0x3141_5926),
            M31(0x5a5a_5a5a),
        ],
        lambda,
    )
}

/// Construct the post-chi helper column
///
/// `h = sel_P/(chi - phi_P) - sel_C/(chi - phi_C)`.
///
/// Only active terms have denominators. Hitting an active committed value is
/// reported as a completeness pole rather than silently inverting zero.
pub fn build_logup_helper(rows: &[LogUpMainRow], chi: QM31) -> Result<Vec<QM31>, LogUpError> {
    let mut helper = Vec::with_capacity(rows.len());
    for (row_index, row) in rows.iter().enumerate() {
        let mut value = QM31::ZERO;
        if row.producer_weight != M31::ZERO {
            let denominator = chi.sub(row.producer_value);
            let inverse = denominator.try_inv().ok_or(LogUpError::ActivePole {
                row: row_index,
                side: LogUpSide::Producer,
            })?;
            value = value.add(inverse.mul_m31(row.producer_weight));
        }
        if row.consumer_weight != M31::ZERO {
            let denominator = chi.sub(row.consumer_value);
            let inverse = denominator.try_inv().ok_or(LogUpError::ActivePole {
                row: row_index,
                side: LogUpSide::Consumer,
            })?;
            value = value.sub(inverse.mul_m31(row.consumer_weight));
        }
        helper.push(value);
    }
    Ok(helper)
}

/// Construct the post-chi helper for the two-row, three-query range layout.
pub fn build_range_logup_helper(
    rows: &[RangeLogUpRow],
    chi: QM31,
) -> Result<Vec<QM31>, LogUpError> {
    let mut helper = Vec::with_capacity(rows.len());
    for (row_index, row) in rows.iter().enumerate() {
        let mut value = QM31::ZERO;
        for (producer_value, weight) in row.producer_values.into_iter().zip(row.producer_weights) {
            if weight != M31::ZERO {
                let inverse = chi
                    .sub(producer_value)
                    .try_inv()
                    .ok_or(LogUpError::ActivePole {
                        row: row_index,
                        side: LogUpSide::Producer,
                    })?;
                value = value.add(inverse.mul_m31(weight));
            }
        }
        if row.consumer_weight != M31::ZERO {
            let inverse = chi
                .sub(row.consumer_value)
                .try_inv()
                .ok_or(LogUpError::ActivePole {
                    row: row_index,
                    side: LogUpSide::Consumer,
                })?;
            value = value.sub(inverse.mul_m31(row.consumer_weight));
        }
        helper.push(value);
    }
    Ok(helper)
}

/// Construct the copy helper for the bounded multi-endpoint row layout.
pub fn build_copy_logup_helper(rows: &[CopyLogUpRow], chi: QM31) -> Result<Vec<QM31>, LogUpError> {
    let mut helper = Vec::with_capacity(rows.len());
    for (row_index, row) in rows.iter().enumerate() {
        let mut value = QM31::ZERO;
        for (producer_value, weight) in row.producer_values.into_iter().zip(row.producer_weights) {
            if weight != M31::ZERO {
                value = value.add(
                    chi.sub(producer_value)
                        .try_inv()
                        .ok_or(LogUpError::ActivePole {
                            row: row_index,
                            side: LogUpSide::Producer,
                        })?
                        .mul_m31(weight),
                );
            }
        }
        for (consumer_value, weight) in row.consumer_values.into_iter().zip(row.consumer_weights) {
            if weight != M31::ZERO {
                value = value.sub(
                    chi.sub(consumer_value)
                        .try_inv()
                        .ok_or(LogUpError::ActivePole {
                            row: row_index,
                            side: LogUpSide::Consumer,
                        })?
                        .mul_m31(weight),
                );
            }
        }
        helper.push(value);
    }
    Ok(helper)
}

/// Division-free degree-five copy identity (degree six with zerocheck eq).
pub fn copy_logup_residual(row: CopyLogUpRow, helper: QM31, chi: QM31) -> QM31 {
    let denominators = [
        chi.sub(row.producer_values[0]),
        chi.sub(row.producer_values[1]),
        chi.sub(row.consumer_values[0]),
        chi.sub(row.consumer_values[1]),
    ];
    let product_without = |excluded: usize| {
        (0..4)
            .filter(|&index| index != excluded)
            .fold(QM31::ONE, |product, index| product.mul(denominators[index]))
    };
    let all = denominators
        .into_iter()
        .fold(QM31::ONE, |product, denominator| product.mul(denominator));
    let mut residual = helper.mul(all);
    for producer in 0..2 {
        residual = residual.sub(product_without(producer).mul_m31(row.producer_weights[producer]));
    }
    for consumer in 0..2 {
        residual =
            residual.add(product_without(2 + consumer).mul_m31(row.consumer_weights[consumer]));
    }
    residual
}

pub fn verify_copy_logup_constraints(
    rows: &[CopyLogUpRow],
    helper: &[QM31],
    chi: QM31,
) -> Result<(), LogUpError> {
    if rows.len() != helper.len() {
        return Err(LogUpError::LengthMismatch);
    }
    let mut total = QM31::ZERO;
    for (row_index, (&row, &h)) in rows.iter().zip(helper).enumerate() {
        if copy_logup_residual(row, h, chi) != QM31::ZERO {
            return Err(LogUpError::RowRelationMismatch { row: row_index });
        }
        total = total.add(h);
    }
    if total != QM31::ZERO {
        return Err(LogUpError::TotalSumMismatch);
    }
    Ok(())
}

/// Division-free degree-five local identity for [`RangeLogUpRow`].
/// Inactive producer weights are zero, but their base-field denominators are
/// retained as harmless common factors. Because `chi` is sampled in QM31
/// outside M31, those factors cannot vanish on Boolean trace rows.
pub fn range_logup_residual(row: RangeLogUpRow, helper: QM31, chi: QM31) -> QM31 {
    let producer_denominators = row.producer_values.map(|value| chi.sub(value));
    let consumer_denominator = chi.sub(row.consumer_value);
    let producer_product = producer_denominators[0]
        .mul(producer_denominators[1])
        .mul(producer_denominators[2]);
    let mut residual = helper.mul(consumer_denominator).mul(producer_product);
    for producer in 0..3 {
        let other_product = producer_denominators[(producer + 1) % 3]
            .mul(producer_denominators[(producer + 2) % 3]);
        residual = residual.sub(
            consumer_denominator
                .mul(other_product)
                .mul_m31(row.producer_weights[producer]),
        );
    }
    residual.add(producer_product.mul_m31(row.consumer_weight))
}

/// Check the range helper's cleared local identities and global zero sum.
pub fn verify_range_logup_constraints(
    rows: &[RangeLogUpRow],
    helper: &[QM31],
    chi: QM31,
) -> Result<(), LogUpError> {
    if rows.len() != helper.len() {
        return Err(LogUpError::LengthMismatch);
    }
    let mut total = QM31::ZERO;
    for (row_index, (&row, &h)) in rows.iter().zip(helper).enumerate() {
        if range_logup_residual(row, h, chi) != QM31::ZERO {
            return Err(LogUpError::RowRelationMismatch { row: row_index });
        }
        total = total.add(h);
    }
    if total != QM31::ZERO {
        return Err(LogUpError::TotalSumMismatch);
    }
    Ok(())
}

/// Check the degree-3 row relation and the global `sum(h) = 0` claim.
pub fn verify_logup_constraints(
    rows: &[LogUpMainRow],
    helper: &[QM31],
    chi: QM31,
) -> Result<(), LogUpError> {
    if rows.len() != helper.len() {
        return Err(LogUpError::LengthMismatch);
    }

    let mut total = QM31::ZERO;
    for (row_index, (row, h)) in rows.iter().zip(helper).enumerate() {
        let producer_denominator = chi.sub(row.producer_value);
        let consumer_denominator = chi.sub(row.consumer_value);
        let left = h.mul(producer_denominator).mul(consumer_denominator);
        let right = consumer_denominator
            .mul_m31(row.producer_weight)
            .sub(producer_denominator.mul_m31(row.consumer_weight));
        if left != right {
            return Err(LogUpError::RowRelationMismatch { row: row_index });
        }
        total = total.add(*h);
    }
    if total != QM31::ZERO {
        return Err(LogUpError::TotalSumMismatch);
    }
    Ok(())
}

/// Teeth-only attack constructor for the canonical challenge order.
///
/// If the consumer multiplicity column could be committed after `chi`, the
/// adversary knows `chi` when choosing multiplicities and cancels one
/// out-of-table producer pole exactly: `sum_v m_v / (chi - v) = 1 /
/// (chi - w)` is four M31-linear equations in the four unknowns
/// `m_0..m_3`, generically solvable by elimination. Every local relation
/// and `sum(h) = 0` then accept a non-member. The canonical order
/// (multiplicity column in C1, before `chi` exists) removes this freedom;
/// the below-characteristic condition only ever applies to the
/// producer-side integer counts, never to committed consumer weights.
/// Returns `None` on a pole hit or singular basis, impossible for a
/// challenge sampled outside the base field.
pub fn forge_post_chi_multiplicities(chi: QM31, nonmember: QM31) -> Option<[M31; 4]> {
    let coords = |value: QM31| [value.c0.a, value.c0.b, value.c1.a, value.c1.b];
    let target = coords(chi.sub(nonmember).try_inv()?);
    let mut matrix = [[M31::ZERO; 5]; 4];
    for (column, value) in (0u32..4).enumerate() {
        let basis = coords(chi.sub(lift(M31(value))).try_inv()?);
        for (matrix_row, basis_coordinate) in matrix.iter_mut().zip(basis) {
            matrix_row[column] = basis_coordinate;
        }
    }
    for (matrix_row, target_coordinate) in matrix.iter_mut().zip(target) {
        matrix_row[4] = target_coordinate;
    }
    for pivot in 0..4 {
        let pivot_row = (pivot..4).find(|&row| matrix[row][pivot] != M31::ZERO)?;
        matrix.swap(pivot, pivot_row);
        let scale = matrix[pivot][pivot].inv();
        for entry in &mut matrix[pivot][pivot..] {
            *entry = entry.mul(scale);
        }
        let pivot_values = matrix[pivot];
        for (row_index, row) in matrix.iter_mut().enumerate() {
            if row_index != pivot && row[pivot] != M31::ZERO {
                let factor = row[pivot];
                for (entry, pivot_entry) in row[pivot..].iter_mut().zip(&pivot_values[pivot..]) {
                    *entry = entry.sub(pivot_entry.mul(factor));
                }
            }
        }
    }
    Some([matrix[0][4], matrix[1][4], matrix[2][4], matrix[3][4]])
}

/// Build the C1-side rows for an unlimited-multiplicity lookup into the fixed
/// M31 table `[0, 1024)`. Query values occupy the first `queries.len()` rows;
/// table multiplicities occupy all 1024 consumer rows.
pub fn build_10bit_range_logup_rows(queries: &[u16]) -> Result<Vec<LogUpMainRow>, LogUpError> {
    if queries.len() > RANGE_TABLE_SIZE {
        return Err(LogUpError::TooManyRangeQueries);
    }
    let mut multiplicities = [0u16; RANGE_TABLE_SIZE];
    for (query, value) in queries.iter().copied().enumerate() {
        if value as usize >= RANGE_TABLE_SIZE {
            return Err(LogUpError::RangeValueOutOfTable { query, value });
        }
        multiplicities[value as usize] += 1;
    }

    Ok((0..RANGE_TABLE_SIZE)
        .map(|row| LogUpMainRow {
            producer_value: if row < queries.len() {
                lift(M31(u32::from(queries[row])))
            } else {
                QM31::ZERO
            },
            consumer_value: lift(M31(row as u32)),
            producer_weight: if row < queries.len() {
                M31::ONE
            } else {
                M31::ZERO
            },
            consumer_weight: M31(u32::from(multiplicities[row])),
        })
        .collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    fn challenge() -> QM31 {
        // Nonzero u component guarantees this challenge is outside the base
        // field containing the fixed table and query values.
        QM31 {
            c0: CM31::new(M31(1_234_567), M31(7_654_321)),
            c1: CM31::new(M31(99), M31(101)),
        }
    }

    #[test]
    fn tagged_tuple_compression_binds_tag_and_limb_order() {
        let lambda = challenge();
        let tuple = compress_tagged_tuple(M31(7), &[M31(11), M31(13), M31(17)], lambda);
        assert_ne!(
            tuple,
            compress_tagged_tuple(M31(8), &[M31(11), M31(13), M31(17)], lambda)
        );
        assert_ne!(
            tuple,
            compress_tagged_tuple(M31(7), &[M31(13), M31(11), M31(17)], lambda)
        );
    }

    #[test]
    fn tagged_tuple_compression_rejects_coupled_tag_first_limb_collision() {
        let lambda = challenge();
        let tuple = compress_tagged_tuple(M31(7), &[M31(11), M31(13)], lambda);

        // With a coefficient of one on the first limb, moving delta from that
        // limb into the tag leaves the compressed value unchanged.
        let coupled_shift = compress_tagged_tuple(M31(10), &[M31(8), M31(13)], lambda);
        assert_ne!(tuple, coupled_shift);
    }

    #[cfg(feature = "insecure-test-logup-compression")]
    #[test]
    fn coupled_tag_first_limb_collision_has_teeth_against_weakened_compression() {
        let lambda = challenge();
        let tuple = [M31(11), M31(13)];
        let shifted = [M31(8), M31(13)];

        assert_eq!(
            compress_tagged_tuple_insecure_lambda_zero(M31(7), &tuple, lambda),
            compress_tagged_tuple_insecure_lambda_zero(M31(10), &shifted, lambda)
        );
        assert_ne!(
            compress_tagged_tuple(M31(7), &tuple, lambda),
            compress_tagged_tuple(M31(10), &shifted, lambda)
        );
    }

    #[test]
    fn coupled_tag_first_limb_shifts_never_collide_for_deterministic_random_deltas() {
        let lambda = challenge();
        let tag = M31(0x1357_9bdf);
        let tuple = [M31(0x0246_8ace), M31(0x1020_3040), M31(0x3141_5926)];
        let expected = compress_tagged_tuple(tag, &tuple, lambda);
        let mut state = 0xd1b5_4a32_d192_ed03u64;

        for _ in 0..512 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let delta = M31((state % u64::from(aspis_core::field::P - 1)) as u32 + 1);
            let shifted = [tuple[0].sub(delta), tuple[1], tuple[2]];
            #[cfg(feature = "insecure-test-logup-compression")]
            assert_eq!(
                compress_tagged_tuple_insecure_lambda_zero(tag, &tuple, lambda),
                compress_tagged_tuple_insecure_lambda_zero(tag.add(delta), &shifted, lambda),
                "weakened lambda^0 encoding lost its coupled collision for delta {}",
                delta.0
            );
            assert_ne!(
                expected,
                compress_tagged_tuple(tag.add(delta), &shifted, lambda),
                "nonzero delta {} produced a coupled collision",
                delta.0
            );
        }
    }

    #[test]
    fn logup_compression_kat_is_pinned() {
        let mut phi = [0u8; 16];
        logup_compression_kat().write_le_bytes(&mut phi);
        assert_eq!(
            phi, LOGUP_COMPRESSION_KAT_EXPECTED,
            "LogUp compression KAT drifted; re-pin only for a deliberate statement-protocol change"
        );
    }

    #[test]
    fn honest_10bit_range_logup_satisfies_rows_and_total() {
        let rows = build_10bit_range_logup_rows(&[0, 1, 1, 17, 511, 1023]).unwrap();
        let helper = build_logup_helper(&rows, challenge()).unwrap();
        assert_eq!(
            verify_logup_constraints(&rows, &helper, challenge()),
            Ok(())
        );
    }

    #[test]
    fn helper_and_multiplicity_corruptions_have_teeth() {
        let mut rows = build_10bit_range_logup_rows(&[0, 1, 1, 17, 511, 1023]).unwrap();
        let mut helper = build_logup_helper(&rows, challenge()).unwrap();
        helper[17] = helper[17].add(QM31::ONE);
        assert_eq!(
            verify_logup_constraints(&rows, &helper, challenge()),
            Err(LogUpError::RowRelationMismatch { row: 17 })
        );

        rows[1].consumer_weight = rows[1].consumer_weight.add(M31::ONE);
        let helper = build_logup_helper(&rows, challenge()).unwrap();
        assert_eq!(
            verify_logup_constraints(&rows, &helper, challenge()),
            Err(LogUpError::TotalSumMismatch)
        );
    }

    #[test]
    fn nonmember_and_active_poles_reject() {
        assert_eq!(
            build_10bit_range_logup_rows(&[1024]),
            Err(LogUpError::RangeValueOutOfTable {
                query: 0,
                value: 1024
            })
        );

        let rows = vec![LogUpMainRow {
            producer_value: lift(M31(5)),
            consumer_value: lift(M31(5)),
            producer_weight: M31::ONE,
            consumer_weight: M31::ONE,
        }];
        assert_eq!(
            build_logup_helper(&rows, lift(M31(5))),
            Err(LogUpError::ActivePole {
                row: 0,
                side: LogUpSide::Producer
            })
        );
    }

    #[test]
    fn post_chi_multiplicities_defeat_the_lookup_without_canonical_order() {
        // Attack demonstration, not a property of the argument: with the
        // multiplicity column chosen after chi, four fractional
        // multiplicities cancel an out-of-table producer and every check
        // accepts. The canonical order commits multiplicities in C1 before
        // chi exists, which is exactly what makes this unbuildable.
        let chi = challenge();
        let nonmember = lift(M31(1024));
        let mut rows = build_10bit_range_logup_rows(&[]).unwrap();
        rows[0].producer_value = nonmember;
        rows[0].producer_weight = M31::ONE;
        let forged = forge_post_chi_multiplicities(chi, nonmember).unwrap();
        assert!(forged.iter().any(|weight| *weight != M31::ZERO));
        for (row, multiplicity) in forged.into_iter().enumerate() {
            rows[row].consumer_weight = multiplicity;
        }
        let helper = build_logup_helper(&rows, chi).unwrap();
        assert_eq!(verify_logup_constraints(&rows, &helper, chi), Ok(()));
    }

    #[test]
    fn local_relations_alone_do_not_replace_total_sum() {
        // This is the exact teeth vector for the extra batched claim: the
        // local helper relation can be satisfied for a value outside the
        // table, but `sum(h) = 0` catches the unmatched pole.
        let mut rows = build_10bit_range_logup_rows(&[]).unwrap();
        rows[0].producer_value = lift(M31(1024));
        rows[0].producer_weight = M31::ONE;
        let helper = build_logup_helper(&rows, challenge()).unwrap();
        assert_eq!(
            verify_logup_constraints(&rows, &helper, challenge()),
            Err(LogUpError::TotalSumMismatch)
        );
    }
}
