//! Compute-envelope constraints used to shape the V5 masking design.
//!
//! The measured v4 atomic transaction used 1,344,003 of 1,400,000 compute
//! units.  V5 therefore has no budget for an additional commitment pass or a
//! literal 96-by-96 determinant inside the program.  This module pins the
//! shape that the CU-feasible V5 implementation respects:
//!
//! * five authenticated trees, with no additional opening section;
//! * no wider leaf than the corresponding v4 tree;
//! * the same q=18 four-round PCS schedule;
//! * the same ten degree-27 sumcheck rounds; and
//! * no on-chain dense determinant.
//!
//! These compile-time assertions define the structural budget. Runtime
//! measurements and the accepted-input ceiling are recorded separately in the
//! V5 release evidence.

use aspis_core::circle_prefix::{CANDIDATE_OOD_SAMPLES, CANDIDATE_ROUND_COUNT};
use aspis_core::state_only_prefix::{
    STATE_ONLY_SPEND_QUERY_COUNT, STATE_ONLY_SPEND_ZERO_FACTOR_SHAPE,
};
use aspis_core::state_only_spend_openings::{
    SPEND_PRIVATE_DEPTHS, SPEND_PRIVATE_SECTION_COUNT, SPEND_PRIVATE_VALUE_WIDTHS,
};
use aspis_core::state_only_sumcheck::{
    STATE_ONLY_SUMCHECK_COEFFICIENTS, STATE_ONLY_SUMCHECK_DEGREE, STATE_ONLY_SUMCHECK_ROUNDS,
};

/// Mainnet v4 measurement, retained as the literal feasibility baseline.
pub const V4_MAINNET_ATOMIC_CU: u64 = 1_344_003;
pub const SOLANA_TRANSACTION_CU_LIMIT: u64 = 1_400_000;
pub const V4_MAINNET_HEADROOM_CU: u64 = SOLANA_TRANSACTION_CU_LIMIT - V4_MAINNET_ATOMIC_CU;

pub const V5_PRIVATE_SECTION_COUNT: usize = 5;
pub const V5_PRIVATE_DEPTHS: [u32; V5_PRIVATE_SECTION_COUNT] = [17, 17, 15, 13, 11];

/// Sixteen M31 semantic lanes, four symbols per opened fibre.
pub const V5_C1_COLUMNS: usize = 16;
pub const V5_FIBRE_SLOTS: usize = 4;
pub const V5_C1_VALUE_BYTES: usize = V5_C1_COLUMNS * V5_FIBRE_SLOTS * 4;

/// The complete budget for sumcheck/DEEP binding auxiliaries.  Three QM31
/// lanes replace v4's H/G/D width; they do not add a fourth lane or tree.
pub const V5_C2_AUXILIARY_LANES: usize = 3;
pub const V5_C2_VALUE_BYTES: usize = V5_C2_AUXILIARY_LANES * V5_FIBRE_SLOTS * 16;

pub const V5_PRIVATE_VALUE_WIDTHS: [usize; V5_PRIVATE_SECTION_COUNT] =
    [V5_C1_VALUE_BYTES, V5_C2_VALUE_BYTES, 64, 64, 64];

pub const V5_QUERY_COUNT: u16 = 18;
pub const V5_PCS_ROUNDS: usize = 4;
pub const V5_OOD_SAMPLES_PER_ROUND: usize = 2;
pub const V5_SUMCHECK_ROUNDS: usize = 10;
pub const V5_SUMCHECK_DEGREE: usize = 27;
pub const V5_SUMCHECK_COEFFICIENTS: usize = 28;

/// The verifier must not evaluate a dense determinant.  This flag says
/// nothing about whether a future component needs an honest-prover retry;
/// component A's current q18 model instead proves rank for every injective
/// four-fibre schedule.
pub const V5_ONCHAIN_DENSE_DETERMINANT: bool = false;

const _: () = assert!(V4_MAINNET_HEADROOM_CU == 55_997);
const _: () = assert!(V5_PRIVATE_SECTION_COUNT == SPEND_PRIVATE_SECTION_COUNT);
const _: () = assert!(V5_PRIVATE_DEPTHS[0] == SPEND_PRIVATE_DEPTHS[0]);
const _: () = assert!(V5_PRIVATE_DEPTHS[1] == SPEND_PRIVATE_DEPTHS[1]);
const _: () = assert!(V5_PRIVATE_DEPTHS[2] == SPEND_PRIVATE_DEPTHS[2]);
const _: () = assert!(V5_PRIVATE_DEPTHS[3] == SPEND_PRIVATE_DEPTHS[3]);
const _: () = assert!(V5_PRIVATE_DEPTHS[4] == SPEND_PRIVATE_DEPTHS[4]);
const _: () = assert!(V5_PRIVATE_VALUE_WIDTHS[0] <= SPEND_PRIVATE_VALUE_WIDTHS[0]);
const _: () = assert!(V5_PRIVATE_VALUE_WIDTHS[1] <= SPEND_PRIVATE_VALUE_WIDTHS[1]);
const _: () = assert!(V5_PRIVATE_VALUE_WIDTHS[2] <= SPEND_PRIVATE_VALUE_WIDTHS[2]);
const _: () = assert!(V5_PRIVATE_VALUE_WIDTHS[3] <= SPEND_PRIVATE_VALUE_WIDTHS[3]);
const _: () = assert!(V5_PRIVATE_VALUE_WIDTHS[4] <= SPEND_PRIVATE_VALUE_WIDTHS[4]);
const _: () = assert!(V5_QUERY_COUNT == STATE_ONLY_SPEND_QUERY_COUNT);
const _: () = assert!(V5_QUERY_COUNT == STATE_ONLY_SPEND_ZERO_FACTOR_SHAPE.query_count);
const _: () = assert!(V5_PCS_ROUNDS == CANDIDATE_ROUND_COUNT);
const _: () = assert!(V5_OOD_SAMPLES_PER_ROUND == CANDIDATE_OOD_SAMPLES);
const _: () = assert!(V5_SUMCHECK_ROUNDS == STATE_ONLY_SUMCHECK_ROUNDS);
const _: () = assert!(V5_SUMCHECK_DEGREE == STATE_ONLY_SUMCHECK_DEGREE);
const _: () = assert!(V5_SUMCHECK_COEFFICIENTS == STATE_ONLY_SUMCHECK_COEFFICIENTS);
const _: () = assert!(!V5_ONCHAIN_DENSE_DETERMINANT);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn v5_candidate_stays_inside_the_measured_v4_tree_envelope() {
        assert_eq!(V4_MAINNET_HEADROOM_CU, 55_997);
        assert_eq!(V5_PRIVATE_SECTION_COUNT, SPEND_PRIVATE_SECTION_COUNT);
        assert_eq!(V5_PRIVATE_DEPTHS, SPEND_PRIVATE_DEPTHS);
        assert_eq!(V5_PRIVATE_VALUE_WIDTHS, [256, 192, 64, 64, 64]);
        for (v5, v4) in V5_PRIVATE_VALUE_WIDTHS
            .into_iter()
            .zip(SPEND_PRIVATE_VALUE_WIDTHS)
        {
            assert!(v5 <= v4);
        }
        assert!(!V5_ONCHAIN_DENSE_DETERMINANT);
    }

    #[test]
    fn v5_candidate_does_not_buy_hiding_with_more_soundness_work() {
        assert_eq!(V5_QUERY_COUNT, 18);
        assert_eq!(V5_PCS_ROUNDS, 4);
        assert_eq!(V5_OOD_SAMPLES_PER_ROUND, 2);
        assert_eq!(V5_SUMCHECK_ROUNDS, 10);
        assert_eq!(V5_SUMCHECK_DEGREE, 27);
        assert_eq!(V5_SUMCHECK_COEFFICIENTS, 28);
    }
}
