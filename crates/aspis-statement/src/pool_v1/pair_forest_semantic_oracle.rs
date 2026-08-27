//! Exact copy-helper foundation for the eight-lane pair-forest oracle.
//!
//! This module deliberately does not activate a verifier profile.  It gives
//! the honest prover and the eventual compiled terminal one shared source of
//! truth for the forest copy table, helper, and active-row polynomial.

use alloc::{vec, vec::Vec};

use aspis_core::field::{M31, QM31};

use crate::{constraints_v4::multilinear_evaluate, logup::build_copy_logup_helper};

use super::{
    pair_forest_hiding::pool_v1_pair_forest_copy_active_rows_v1,
    pair_forest_trace::{pool_v1_pair_forest_copy_rows_v1, PoolV1PairForestTraceV1},
    pair_trace::PoolV1PairTraceErrorV1,
    pair_tree_profile::POOL_V1_PAIR_TRACE_ROWS,
};

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
}
