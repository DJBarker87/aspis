//! LogUp helper construction and exact local-relation oracle.
//!
//! This module pins the algebra Stage 2 will put behind C2. It does not yet
//! connect the columns to the PCS: callers still own C1 layout, selectors,
//! transcript order, the helper commitment, and the `sum(h) = 0` claim.

use alloc::vec::Vec;

use aspis_core::field::{CM31, M31, QM31};

pub const RANGE_TABLE_SIZE: usize = 1 << 10;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LogUpMainRow {
    pub producer_value: QM31,
    pub consumer_value: QM31,
    pub producer_weight: M31,
    pub consumer_weight: M31,
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

/// Compress a tagged M31 tuple as `tag + sum_i lambda^i * value_i`.
/// Tags are verifier-computable wiring constants, never witness values.
pub fn compress_tagged_tuple(tag: M31, values: &[M31], lambda: QM31) -> QM31 {
    let mut compressed = lift(tag);
    let mut power = QM31::ONE;
    for value in values {
        compressed = compressed.add(power.mul_m31(*value));
        power = power.mul(lambda);
    }
    compressed
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
