//! Exact copy-helper foundation for the eight-lane pair-forest oracle.
//!
//! This module deliberately does not activate a verifier profile.  It gives
//! the honest prover and the eventual compiled terminal one shared source of
//! truth for the forest copy table, helper, and active-row polynomial.

use alloc::{vec, vec::Vec};

use aspis_core::field::{M31, QM31};

use crate::state_only_poseidon::StateOnlyPoseidonOpenings;
use crate::{constraints_v4::multilinear_evaluate, logup::build_copy_logup_helper};

use super::{
    pair_forest_hiding::pool_v1_pair_forest_copy_active_rows_v1,
    pair_forest_hiding::{
        pool_v1_pair_forest_path_base_row_v1, POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1,
    },
    pair_forest_trace::{
        build_pool_v1_pair_forest_copy_registry_v1, pool_v1_pair_forest_copy_rows_v1,
        PoolV1PairForestTraceV1,
    },
    pair_trace::{
        PoolV1PairCopyTupleV1, PoolV1PairCopyWeightV1, PoolV1PairTraceErrorV1,
        PoolV1PairTraceVariantV1, PoolV1PairTupleLimbV1,
    },
    pair_tree_profile::POOL_V1_PAIR_TRACE_ROWS,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestCopyTerminalV1 {
    pub residual: QM31,
    pub active: QM31,
}

/// The 17 non-Poseidon lanes for all 24 private membership directions.  The
/// row selector aggregates the same equation over every path slot, matching
/// the legacy payment terminal without adding a claim.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestPathTerminalV1 {
    pub direction_booleanity: QM31,
    pub ordered_children: [QM31; 16],
}

#[derive(Clone, Copy)]
struct CopyRowExtensionV1 {
    producer_values: [QM31; 2],
    producer_weights: [QM31; 2],
    consumer_values: [QM31; 2],
    consumer_weights: [QM31; 2],
}

#[inline]
fn lift(value: M31) -> QM31 {
    QM31::from_cm31(aspis_core::field::CM31::from_m31(value))
}

#[inline]
fn eq_row(point: &[QM31; 10], row: usize) -> QM31 {
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

/// Evaluate all 24 private path ordering equations from the frozen
/// `(z, successor(z))` subset of the frozen three-opening geometry. This is
/// intentionally a separate cheap source-layout gate as well as a component
/// of the compiled forest terminal: the unselected child is the sibling
/// witness itself, so no redundant sibling copy or extra PCS opening is
/// required.
pub fn evaluate_pool_v1_pair_forest_path_terminal_v1(
    openings: &StateOnlyPoseidonOpenings,
    point: &[QM31; 10],
) -> Result<PoolV1PairForestPathTerminalV1, PoolV1PairTraceErrorV1> {
    let selector =
        (0..POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1).try_fold(QM31::ZERO, |sum, level| {
            pool_v1_pair_forest_path_base_row_v1(level)
                .map(|row| sum.add(eq_row(point, row)))
                .ok_or(PoolV1PairTraceErrorV1::Shape)
        })?;
    let bit = openings.z[0];
    let mut ordered_children = [QM31::ZERO; 16];
    for lane in 0..8 {
        let current = openings.z[1 + lane];
        ordered_children[lane] = selector
            .mul(QM31::ONE.sub(bit))
            .mul(openings.succ_z[lane].sub(current));
        ordered_children[8 + lane] = selector
            .mul(bit)
            .mul(openings.succ_z[8 + lane].sub(current));
    }
    Ok(PoolV1PairForestPathTerminalV1 {
        direction_booleanity: selector.mul(bit.mul(bit.sub(QM31::ONE))),
        ordered_children,
    })
}

fn copy_weight(
    weight: PoolV1PairCopyWeightV1,
    append_index: u64,
    variant: PoolV1PairTraceVariantV1,
) -> M31 {
    match weight {
        PoolV1PairCopyWeightV1::One => M31::ONE,
        PoolV1PairCopyWeightV1::PrivateTransferOnly => M31(u32::from(
            variant == PoolV1PairTraceVariantV1::PrivateTransfer,
        )),
        PoolV1PairCopyWeightV1::WithdrawalOnly => {
            M31(u32::from(variant == PoolV1PairTraceVariantV1::Withdrawal))
        }
        PoolV1PairCopyWeightV1::AppendCurrentLeft { level } => {
            M31(1 - ((append_index >> level) & 1) as u32)
        }
        PoolV1PairCopyWeightV1::AppendCurrentRight { level } => {
            M31(((append_index >> level) & 1) as u32)
        }
    }
}

fn compressed_opened_tuple(
    tuple: PoolV1PairCopyTupleV1,
    tag: M31,
    selector: QM31,
    openings: &[QM31; 16],
    powers: &[QM31; 16],
) -> QM31 {
    let mut value = selector.mul_m31(tag);
    for (limb, power) in tuple.limbs.into_iter().zip(powers) {
        let opened = match limb {
            PoolV1PairTupleLimbV1::Zero => QM31::ZERO,
            PoolV1PairTupleLimbV1::Cell { source, offset } => {
                openings[usize::from(source.cell.column)].add(lift(offset))
            }
        };
        value = value.add(selector.mul(opened).mul(*power));
    }
    value
}

fn copy_residual(row: CopyRowExtensionV1, helper: QM31, chi: QM31) -> QM31 {
    let denominator = [
        chi.sub(row.producer_values[0]),
        chi.sub(row.producer_values[1]),
        chi.sub(row.consumer_values[0]),
        chi.sub(row.consumer_values[1]),
    ];
    let producer_denominator = denominator[0].mul(denominator[1]);
    let consumer_denominator = denominator[2].mul(denominator[3]);
    let producer_numerator = row.producer_weights[0]
        .mul(denominator[1])
        .add(row.producer_weights[1].mul(denominator[0]));
    let consumer_numerator = row.consumer_weights[0]
        .mul(denominator[3])
        .add(row.consumer_weights[1].mul(denominator[2]));
    producer_denominator
        .mul(helper.mul(consumer_denominator).add(consumer_numerator))
        .sub(consumer_denominator.mul(producer_numerator))
}

/// Construct the unique forest LogUp helper from the literal typed copy
/// registry.  The append index remains an explicit input because append-side
/// links are selected by its live lane-path bits.
pub fn build_pool_v1_pair_forest_copy_helper_v1(
    trace: &PoolV1PairForestTraceV1,
    append_index: u64,
    lambda: QM31,
    chi: QM31,
) -> Result<Vec<QM31>, PoolV1PairTraceErrorV1> {
    let rows = pool_v1_pair_forest_copy_rows_v1(trace, append_index, lambda)?;
    build_copy_logup_helper(&rows, chi).map_err(|_| PoolV1PairTraceErrorV1::CopyImbalance)
}

/// Evaluate the exact forest copy lane from the sixteen merged-C1 openings
/// and one H1 opening used by the selected Tag-73 terminal.  Stable and late
/// banks intentionally share the same opening vector: bank disjointness is
/// checked before C1 commitment by the merged-trace compiler.
pub fn evaluate_pool_v1_pair_forest_copy_terminal_v1(
    openings: &[QM31; 16],
    h1_z: QM31,
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
    append_index: u64,
    variant: PoolV1PairTraceVariantV1,
) -> Result<PoolV1PairForestCopyTerminalV1, PoolV1PairTraceErrorV1> {
    let registry = build_pool_v1_pair_forest_copy_registry_v1()?;
    let mut powers = [QM31::ZERO; 16];
    let mut power = lambda;
    for output in &mut powers {
        *output = power;
        power = power.mul(lambda);
    }
    let mut row = CopyRowExtensionV1 {
        producer_values: [QM31::ZERO; 2],
        producer_weights: [QM31::ZERO; 2],
        consumer_values: [QM31::ZERO; 2],
        consumer_weights: [QM31::ZERO; 2],
    };
    let mut producer_arity = [0u8; POOL_V1_PAIR_TRACE_ROWS];
    let mut consumer_arity = [0u8; POOL_V1_PAIR_TRACE_ROWS];
    let mut active_rows = [false; POOL_V1_PAIR_TRACE_ROWS];
    for link in registry {
        let weight = copy_weight(link.weight, append_index, variant);
        for (tuple, arity, values, weights) in [
            (
                link.producer,
                &mut producer_arity,
                &mut row.producer_values,
                &mut row.producer_weights,
            ),
            (
                link.consumer,
                &mut consumer_arity,
                &mut row.consumer_values,
                &mut row.consumer_weights,
            ),
        ] {
            let endpoint_row = usize::from(tuple.row);
            let slot = usize::from(arity[endpoint_row]);
            if slot >= 2 {
                return Err(PoolV1PairTraceErrorV1::CopyLayout);
            }
            arity[endpoint_row] += 1;
            active_rows[endpoint_row] = true;
            let selector = eq_row(point, endpoint_row);
            weights[slot] = weights[slot].add(selector.mul_m31(weight));
            values[slot] = values[slot].add(compressed_opened_tuple(
                tuple, link.tag, selector, openings, &powers,
            ));
        }
    }
    let active = active_rows
        .into_iter()
        .enumerate()
        .filter(|(_, active)| *active)
        .fold(QM31::ZERO, |sum, (row, _)| sum.add(eq_row(point, row)));
    Ok(PoolV1PairForestCopyTerminalV1 {
        residual: active.mul(copy_residual(row, h1_z, chi)),
        active,
    })
}

/// Evaluate the exact multilinear indicator of rows carrying at least one
/// endpoint in the forest copy registry.  The same row inventory is used by
/// mask balancing, so inactive helper padding cannot be confused with a
/// constrained LogUp row.
pub fn pool_v1_pair_forest_copy_active_at_point_v1(
    point: &[QM31; 10],
) -> Result<QM31, PoolV1PairTraceErrorV1> {
    let mut active = vec![M31::ZERO; POOL_V1_PAIR_TRACE_ROWS];
    for row in
        pool_v1_pair_forest_copy_active_rows_v1().map_err(|_| PoolV1PairTraceErrorV1::CopyLayout)?
    {
        active[usize::from(row)] = M31::ONE;
    }
    multilinear_evaluate(&active, point).ok_or(PoolV1PairTraceErrorV1::Shape)
}

pub fn pool_v1_pair_forest_copy_helper_sum_v1(h1: &[QM31]) -> Option<QM31> {
    (h1.len() == POOL_V1_PAIR_TRACE_ROWS).then(|| h1.iter().copied().fold(QM31::ZERO, QM31::add))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn q(value: u32) -> QM31 {
        lift(M31(value))
    }

    fn boolean_point(row: usize) -> [QM31; 10] {
        core::array::from_fn(|coordinate| q(((row >> (9 - coordinate)) & 1) as u32))
    }

    #[test]
    fn path_terminal_is_exact_on_each_authenticated_path_slot() {
        for level in 0..POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1 {
            let base = pool_v1_pair_forest_path_base_row_v1(level).unwrap();
            let current: [QM31; 8] = core::array::from_fn(|lane| q(10 + lane as u32));
            let sibling: [QM31; 8] = core::array::from_fn(|lane| q(30 + lane as u32));
            for bit in [QM31::ZERO, QM31::ONE] {
                let mut openings = StateOnlyPoseidonOpenings {
                    z: [QM31::ZERO; 16],
                    succ_z: [QM31::ZERO; 16],
                    xor12_z: [QM31::ZERO; 16],
                };
                openings.z[0] = bit;
                openings.z[1..9].copy_from_slice(&current);
                openings.xor12_z[..8].copy_from_slice(&sibling);
                for lane in 0..8 {
                    if bit == QM31::ZERO {
                        openings.succ_z[lane] = current[lane];
                        openings.succ_z[8 + lane] = sibling[lane];
                    } else {
                        openings.succ_z[lane] = sibling[lane];
                        openings.succ_z[8 + lane] = current[lane];
                    }
                }
                let terminal =
                    evaluate_pool_v1_pair_forest_path_terminal_v1(&openings, &boolean_point(base))
                        .unwrap();
                assert_eq!(terminal.direction_booleanity, QM31::ZERO);
                assert!(terminal
                    .ordered_children
                    .into_iter()
                    .all(|residual| residual == QM31::ZERO));
                let selected_lane = if bit == QM31::ZERO { 0 } else { 8 };
                openings.succ_z[selected_lane] = openings.succ_z[selected_lane].add(QM31::ONE);
                assert_ne!(
                    evaluate_pool_v1_pair_forest_path_terminal_v1(&openings, &boolean_point(base),)
                        .unwrap()
                        .ordered_children[selected_lane],
                    QM31::ZERO
                );
            }
        }
    }

    #[test]
    fn forest_active_indicator_is_boolean_on_every_domain_row() {
        let active = pool_v1_pair_forest_copy_active_rows_v1().unwrap();
        assert_eq!(active.len(), 214);
        let mut seen = [false; POOL_V1_PAIR_TRACE_ROWS];
        for row in active {
            assert!(!seen[usize::from(row)]);
            seen[usize::from(row)] = true;
        }
        assert_eq!(seen.into_iter().filter(|value| *value).count(), 214);
    }

    #[test]
    fn helper_sum_rejects_every_noncanonical_length() {
        assert_eq!(
            pool_v1_pair_forest_copy_helper_sum_v1(&vec![QM31::ZERO; 1024]),
            Some(QM31::ZERO)
        );
        assert_eq!(
            pool_v1_pair_forest_copy_helper_sum_v1(&vec![QM31::ZERO; 1023]),
            None
        );
        assert_eq!(
            pool_v1_pair_forest_copy_helper_sum_v1(&vec![QM31::ZERO; 1025]),
            None
        );
    }

    #[test]
    fn compiled_copy_terminal_uses_the_exact_active_polynomial_and_append_bits() {
        let point: [QM31; 10] = core::array::from_fn(|index| q(2 + index as u32));
        let openings: [QM31; 16] = core::array::from_fn(|index| q(100 + index as u32));
        let active = pool_v1_pair_forest_copy_active_at_point_v1(&point).unwrap();
        let even = evaluate_pool_v1_pair_forest_copy_terminal_v1(
            &openings,
            q(313),
            &point,
            q(17),
            q(29),
            0,
            PoolV1PairTraceVariantV1::PrivateTransfer,
        )
        .unwrap();
        let odd = evaluate_pool_v1_pair_forest_copy_terminal_v1(
            &openings,
            q(313),
            &point,
            q(17),
            q(29),
            1,
            PoolV1PairTraceVariantV1::PrivateTransfer,
        )
        .unwrap();
        assert_eq!(even.active, active);
        assert_eq!(odd.active, active);
        assert_ne!(even.residual, odd.residual);
    }

    #[test]
    fn active_polynomial_is_exact_on_boolean_rows() {
        let active = pool_v1_pair_forest_copy_active_rows_v1().unwrap();
        for row in [0usize, 11, 864, 876, 997, 1023] {
            let point: [QM31; 10] =
                core::array::from_fn(|coordinate| q(((row >> (9 - coordinate)) & 1) as u32));
            let expected = QM31::from_cm31(aspis_core::field::CM31::from_m31(M31(u32::from(
                active.binary_search(&(row as u16)).is_ok(),
            ))));
            assert_eq!(
                pool_v1_pair_forest_copy_active_at_point_v1(&point).unwrap(),
                expected,
                "row {row}"
            );
        }
    }
}
