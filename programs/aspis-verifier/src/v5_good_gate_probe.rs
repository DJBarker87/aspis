//! Exact, feature-gated verifier arithmetic for the public v5 GoodA/GoodB
//! schedule predicates.  This module is reachable only through the isolated
//! `v5-cu-probe` verifier; it is not part of the production dispatcher.
//!
//! The fixed columns are exactly the ones formalised by
//! `V5ComponentADeployedTerminalApplicability` and
//! `V5ComponentBSpendDifferenceCoverage`: A directions `0..12` and B
//! directions `0..4`, in block-major order.  The conversion table is the
//! sparse parity layout of `ordinary_monomials_in_natural_line_basis(48)`.

#[cfg(test)]
use aspis_core::circle_fri::selected_circle_fiber_points_shared;
use aspis_core::circle_fri::{
    BaseCirclePoint, RATE512_CIRCLE_HIGH9_WINDOW, RATE512_CIRCLE_LOW8_WINDOW,
};
#[cfg(test)]
use aspis_core::field::qm31_m31_dot;
use aspis_core::field::{qm31_sum_products2_prepared, PreparedQm31Multiplier, CM31, M31, P, QM31};
#[cfg(test)]
use aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_masks_v3;

use super::V5_CU_PROBE_QUERY_COUNT;

pub const GOOD_A_SIZE: usize = 12;
pub const GOOD_B_SIZE: usize = 4;
const KERNEL_DEGREE: usize = 36;
/// The candidate C1 codeword has domain log 19, hence `2^(19-2)` fibres.
/// This is intentionally distinct from the ten-variable relation/MLE domain.
const C1_DOMAIN_LOG: u32 = 19;
const C1_QUERY_LOG: u32 = C1_DOMAIN_LOG - 2;
const C1_FIBER_COUNT: usize = 1usize << C1_QUERY_LOG;
const A_NATURAL_WIDTH: usize = 48;
#[cfg(test)]
const B_NATURAL_WIDTH: usize = 40;

const M31_MODULUS_U64: u64 = P as u64;
const M31_MODULUS_SQUARED: u64 = M31_MODULUS_U64 * M31_MODULUS_U64;
const QUERY_KERNEL_FUSED_MAX: u64 =
    (M31_MODULUS_U64 - 1) * (M31_MODULUS_U64 - 1) + (M31_MODULUS_U64 - 1);
const _: () = assert!(QUERY_KERNEL_FUSED_MAX < (1u64 << 62));
const _: () =
    assert!(M31_MODULUS_SQUARED - (M31_MODULUS_U64 - 1) * (M31_MODULUS_U64 - 1) == 4_294_967_293);
const _: () = assert!(
    M31_MODULUS_SQUARED + (M31_MODULUS_U64 - 1) * (M31_MODULUS_U64 - 1)
        == 9_223_372_023_969_873_925
);
const _: () =
    assert!(M31_MODULUS_SQUARED + (M31_MODULUS_U64 - 1) * (M31_MODULUS_U64 - 1) < (1u64 << 63));

/// Exact natural-coordinate support of the inactive-copy functional in the
/// deployed p block (`row = 256 + 2 * natural`). This is generated from
/// `atomic_state_only_copy_inactive_row_masks_v3`; keeping the support itself
/// avoids rebuilding all 64 mask words for each of the four GoodB columns.
const B_INACTIVE_NATURAL_SUPPORT: [u8; 30] = [
    1, 2, 3, 4, 5, 7, 9, 10, 11, 12, 13, 15, 17, 18, 19, 20, 21, 23, 25, 26, 27, 28, 29, 31, 33,
    34, 35, 36, 37, 39,
];

/// `trailing_ones(2 * index + 1)` for the 24 odd natural coordinates below
/// `A_NATURAL_WIDTH`. The sparse shift has fixed support, so no runtime bit
/// scan is needed in the production path.
const ODD_NATURAL_TRAILING_ONES: [u8; A_NATURAL_WIDTH / 2] = [
    1, 2, 1, 3, 1, 2, 1, 4, 1, 2, 1, 3, 1, 2, 1, 5, 1, 2, 1, 3, 1, 2, 1, 4,
];

/// `x^(2r)` and `x^(2r+1)` have the same coefficient row after parity is
/// stripped. Entry `[r][k]` multiplies natural coordinate
/// `2*k + degree%2`. Zeros after the triangular support are retained only to
/// keep fixed-size, allocation-free verifier data.
const MONOMIAL_TO_NATURAL_PARITY: [[u32; 24]; 24] = [
    [
        1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ],
    [
        1073741824, 1073741824, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ],
    [
        805306368, 1073741824, 268435456, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0,
    ],
    [
        671088640, 939524096, 402653184, 134217728, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0,
    ],
    [
        587202560, 805306368, 469762048, 268435456, 16777216, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0,
    ],
    [
        528482304, 696254464, 503316480, 369098752, 41943040, 8388608, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0,
    ],
    [
        484442112, 612368384, 517996544, 436207616, 69206016, 25165824, 2097152, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ],
    [
        449839104, 548405248, 521142272, 477102080, 95420416, 47185920, 7340032, 1048576, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ],
    [
        421724160, 499122176, 516947968, 499122176, 119275520, 71303168, 15728640, 4194304, 65536,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ],
    [
        398295040, 460423168, 508035072, 508035072, 140378112, 95289344, 26738688, 9961472, 294912,
        32768, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ],
    [
        378380288, 429359104, 496132096, 508035072, 158760960, 117833728, 39682048, 18350080,
        778240, 163840, 8192, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ],
    [
        361181184, 403869696, 482414592, 502083584, 174637056, 138297344, 53886976, 29016064,
        1576960, 471040, 45056, 4096, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ],
    [
        346131968, 382525440, 467695616, 492249088, 188280320, 156467200, 68771840, 41451520,
        2720256, 1024000, 141312, 24576, 512, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ],
    [
        332819200, 364328704, 452541440, 479972352, 199969536, 172373760, 83865600, 55111680,
        4209920, 1872128, 332800, 82944, 3328, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ],
    [
        320932800, 348573952, 437345984, 466256896, 209963712, 186171648, 98804160, 69488640,
        6027840, 3041024, 655168, 207872, 12096, 1792, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ],
    [
        310235040, 334753376, 422380704, 451801440, 218492960, 198067680, 113317152, 84146400,
        8143200, 4534432, 1139808, 431520, 32480, 6944, 480, 32, 0, 0, 0, 0, 0, 0, 0, 0,
    ],
    [
        300540195, 322494208, 407829056, 437091072, 225756880, 208280320, 127212096, 98731776,
        10518300, 6338816, 1811392, 785664, 71920, 19712, 1984, 256, 1, 0, 0, 0, 0, 0, 0, 0,
    ],
    [
        1365442601, 1385259025, 393810848, 422460064, 231926376, 217018600, 140359072, 112971936,
        13112814, 8428558, 2686816, 1298528, 139128, 45816, 5984, 1120, 1073741832, 1073741824, 0,
        0, 0, 0, 0, 0,
    ],
    [
        552033434, 1375350813, 1185706108, 408135456, 237146838, 224472488, 152677170, 126665504,
        1089628502, 10770686, 1077517003, 1992672, 243474, 92472, 14726, 3552, 805306407,
        1073741828, 268435456, 0, 0, 0, 0, 0,
    ],
    [
        1215658969, 2037433947, 1575595533, 796920782, 241541661, 230809663, 164123083, 139671337,
        1629414646, 550199594, 541949341, 1613496661, 394383, 167973, 31369, 9139, 1744830595,
        2013265941, 402653185, 134217728, 0, 0, 0, 0,
    ],
    [
        1561077133, 1626546458, 959515537, 112516334, 563982717, 236175662, 1248423615, 151897210,
        894238878, 1089807120, 1348769646, 1077723001, 1812540145, 281178, 1073801786, 20254,
        2130706788, 1879048268, 201326598, 1342177280, 16777216, 0, 0, 0,
    ],
    [
        1881822571, 520069972, 1988265290, 1609757759, 374086967, 1473821013, 1794971849,
        1773902236, 58475068, 992022999, 1753138265, 139504500, 772622818, 1980152485, 536976251,
        536911020, 1568670526, 2004877528, 905969686, 771751939, 176160768, 8388608, 0, 0,
    ],
    [
        326054034, 127204448, 989718666, 725269701, 1246891692, 923953990, 1172545825, 710695219,
        2049719910, 1598990857, 1696321919, 2020063206, 1502772382, 302645828, 360883090,
        1610685459, 861931195, 1786774027, 610271298, 1912602636, 991952896, 92274688, 2097152, 0,
    ],
    [
        1252654445, 226629241, 1244848782, 1931236007, 2107671782, 1085422841, 458064303,
        941620522, 480024583, 750613560, 142311740, 784450739, 1549326687, 902709105, 121903455,
        2059526098, 1905265858, 1324352611, 693108903, 1261436967, 1831862273, 542113792, 24117248,
        1048576,
    ],
];

pub type GoodAMatrix = [[M31; GOOD_A_SIZE]; GOOD_A_SIZE];
pub type GoodBMatrix = [[QM31; GOOD_B_SIZE]; GOOD_B_SIZE];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GoodGateEvaluation {
    pub queries: [u32; V5_CU_PROBE_QUERY_COUNT],
    pub good_a_matrix: GoodAMatrix,
    pub good_a_determinant: M31,
    pub good_b_matrix: GoodBMatrix,
    pub good_b_determinant: QM31,
}

impl GoodGateEvaluation {
    #[inline(always)]
    pub fn is_good(self) -> bool {
        !self.good_a_determinant.is_zero() && !self.good_b_determinant.is_zero()
    }
}

#[inline(always)]
fn m31_coordinates(value: QM31) -> [M31; 4] {
    [value.c0.a, value.c0.b, value.c1.a, value.c1.b]
}

#[inline(always)]
fn m31_mul_add_reduced(product_left: M31, product_right: M31, addend: M31) -> M31 {
    let raw = u64::from(product_left.0) * u64::from(product_right.0) + u64::from(addend.0);
    debug_assert!(raw <= QUERY_KERNEL_FUSED_MAX);
    M31::reduce_u64(raw)
}

/// Exact SBF-visible spelling of `aspis_statement::binary_successor_point`,
/// whose host export is intentionally cfg-disabled on Solana.
fn binary_successor_point(point: &[QM31; 10]) -> [QM31; 10] {
    let mut successor = [QM31::ZERO; 10];
    let mut carry = QM31::ONE;
    let mut coordinate = point.len();
    while coordinate > 0 {
        coordinate -= 1;
        let value = point[coordinate];
        let value_times_carry = value.mul(carry);
        successor[coordinate] = value
            .add(carry)
            .sub(value_times_carry.add(value_times_carry));
        carry = value_times_carry;
    }
    successor
}

/// Exact SBF-visible spelling of `aspis_statement::xor12_point`, whose host
/// export is intentionally cfg-disabled on Solana.
#[cfg(test)]
fn xor12_point(point: &[QM31; 10]) -> [QM31; 10] {
    let mut shifted = *point;
    shifted[7] = QM31::ONE.sub(shifted[7]);
    shifted[6] = QM31::ONE.sub(shifted[6]);
    shifted
}

#[inline(always)]
fn add_base_circle_points(left: BaseCirclePoint, right: BaseCirclePoint) -> BaseCirclePoint {
    BaseCirclePoint {
        x: left.x.mul(right.x).sub(left.y.mul(right.y)),
        y: left.x.mul(right.y).add(left.y.mul(right.x)),
    }
}

/// Exact log-19 branch of `selected_circle_fiber_points_shared` for one
/// already range-checked fibre.  Keeping the fallible range scan outside the
/// caller's arithmetic loop is semantics-identical and makes the real GoodA
/// call graph consumable by the pinned Rust-to-Lean translator.
#[inline(always)]
fn selected_c1_fiber_point_prevalidated(fiber: u32) -> BaseCirclePoint {
    let natural = (fiber as usize).reverse_bits() >> (usize::BITS - C1_QUERY_LOG);
    let [low_x, low_y] = RATE512_CIRCLE_LOW8_WINDOW[natural & 0xff];
    let high_index = natural >> 8;
    let mut point = BaseCirclePoint {
        x: M31(low_x),
        y: M31(low_y),
    };
    if high_index != 0 {
        let [high_x, high_y] = RATE512_CIRCLE_HIGH9_WINDOW[high_index];
        point = add_base_circle_points(
            point,
            BaseCirclePoint {
                x: M31(high_x),
                y: M31(high_y),
            },
        );
    }
    point
}

fn query_kernel(queries: &[u32; V5_CU_PROBE_QUERY_COUNT]) -> Option<[M31; 37]> {
    // Prevalidate before materialization so an invalid public schedule still
    // rejects, but no fallible return occurs inside the arithmetic loop.
    let mut query_ordinal = 0usize;
    let mut all_queries_in_range = true;
    while query_ordinal < V5_CU_PROBE_QUERY_COUNT {
        all_queries_in_range &= (queries[query_ordinal] as usize) < C1_FIBER_COUNT;
        query_ordinal += 1;
    }
    if !all_queries_in_range {
        return None;
    }

    // K(X) = product_i (X^2 - x_i^2) is even. Build its degree-18
    // polynomial in Z = X^2, then embed it into the even coordinates. This
    // is coefficient-for-coefficient identical and avoids traversing the
    // eighteen identically-zero odd coefficients at every product step.
    let mut z_polynomial = [M31::ZERO; V5_CU_PROBE_QUERY_COUNT + 1];
    z_polynomial[0] = M31::ONE;
    let mut degree = 0usize;
    query_ordinal = 0;
    while query_ordinal < V5_CU_PROBE_QUERY_COUNT {
        let point = selected_c1_fiber_point_prevalidated(queries[query_ordinal]);
        let x = point.x;
        let constant = x.mul(x).neg();
        degree += 1;
        z_polynomial[degree] = z_polynomial[degree - 1];
        let mut coefficient = degree - 1;
        while coefficient > 0 {
            // This is exactly `previous + current * constant` modulo M31.
            // Canonical inputs put the unreduced value below 2^62, so the
            // verifier can perform one reduction instead of multiplying and
            // then canonically adding in a second reduction.
            z_polynomial[coefficient] = m31_mul_add_reduced(
                z_polynomial[coefficient],
                constant,
                z_polynomial[coefficient - 1],
            );
            coefficient -= 1;
        }
        z_polynomial[0] = z_polynomial[0].mul(constant);
        query_ordinal += 1;
    }
    if degree != V5_CU_PROBE_QUERY_COUNT || z_polynomial[degree] != M31::ONE {
        return None;
    }
    let mut polynomial = [M31::ZERO; KERNEL_DEGREE + 1];
    let mut coefficient = 0usize;
    while coefficient <= degree {
        polynomial[2 * coefficient] = z_polynomial[coefficient];
        coefficient += 1;
    }
    Some(polynomial)
}

/// Literal allocation-heavy predecessor retained as a differential oracle for
/// the in-place recurrence above.
#[cfg(test)]
fn query_kernel_reference(
    queries: &[u32; V5_CU_PROBE_QUERY_COUNT],
) -> Option<[M31; KERNEL_DEGREE + 1]> {
    let points = selected_circle_fiber_points_shared(C1_DOMAIN_LOG, queries).ok()?;
    let mut z_polynomial = [M31::ZERO; V5_CU_PROBE_QUERY_COUNT + 1];
    z_polynomial[0] = M31::ONE;
    let mut degree = 0usize;
    for point in points {
        let constant = point.x.mul(point.x).neg();
        let mut next = [M31::ZERO; V5_CU_PROBE_QUERY_COUNT + 1];
        let mut coefficient = 0usize;
        while coefficient <= degree {
            next[coefficient] = next[coefficient].add(z_polynomial[coefficient].mul(constant));
            next[coefficient + 1] = next[coefficient + 1].add(z_polynomial[coefficient]);
            coefficient += 1;
        }
        z_polynomial = next;
        degree += 1;
    }
    if degree != V5_CU_PROBE_QUERY_COUNT || z_polynomial[degree] != M31::ONE {
        return None;
    }
    let mut polynomial = [M31::ZERO; KERNEL_DEGREE + 1];
    let mut coefficient = 0usize;
    while coefficient <= degree {
        polynomial[2 * coefficient] = z_polynomial[coefficient];
        coefficient += 1;
    }
    Some(polynomial)
}

#[cfg(test)]
fn ordinary_a_direction(kernel: &[M31; 37], shift: usize) -> [M31; A_NATURAL_WIDTH] {
    let mut ordinary = [M31::ZERO; A_NATURAL_WIDTH];
    let mut degree = 0usize;
    while degree <= KERNEL_DEGREE {
        ordinary[degree] = ordinary[degree].sub(kernel[degree]);
        ordinary[degree + shift] = ordinary[degree + shift].add(kernel[degree]);
        degree += 1;
    }
    ordinary
}

#[cfg(test)]
fn ordinary_b_direction(kernel: &[M31; 37], shift: usize) -> [M31; A_NATURAL_WIDTH] {
    let mut ordinary = [M31::ZERO; A_NATURAL_WIDTH];
    let mut degree = 0usize;
    while degree <= KERNEL_DEGREE {
        ordinary[degree + shift] = ordinary[degree + shift].add(kernel[degree]);
        degree += 1;
    }
    ordinary
}

#[cfg(test)]
fn ordinary_to_natural(ordinary: &[M31; A_NATURAL_WIDTH], width: usize) -> [M31; A_NATURAL_WIDTH] {
    let mut natural = [M31::ZERO; A_NATURAL_WIDTH];
    let mut degree = 0usize;
    while degree < width {
        let coefficient = ordinary[degree];
        if coefficient.is_zero() {
            degree += 1;
            continue;
        }
        let parity = degree & 1;
        let support = degree / 2 + 1;
        let mut k = 0usize;
        while k < support {
            let weight = M31(MONOMIAL_TO_NATURAL_PARITY[degree / 2][k]);
            natural[parity + 2 * k] = natural[parity + 2 * k].add(coefficient.mul(weight));
            k += 1;
        }
        degree += 1;
    }
    natural
}

/// Convert the exact even degree-36 query kernel directly into the even
/// natural coordinates. Each output uses support `row >= natural`, and four
/// maximal M31 products fit in one `u64`; the at-most-five reduced blocks then
/// fit far below `u64::MAX`. This is the same triangular conversion as
/// `ordinary_to_natural`, without scanning the 29 known-zero ordinary slots or
/// canonically adding after every scalar product.
fn even_kernel_to_natural(kernel: &[M31; KERNEL_DEGREE + 1]) -> [M31; A_NATURAL_WIDTH] {
    let mut natural = [M31::ZERO; A_NATURAL_WIDTH];
    let mut natural_coordinate = 0usize;
    while natural_coordinate <= KERNEL_DEGREE / 2 {
        let mut outer = 0u64;
        let mut block_start = natural_coordinate;
        while block_start <= KERNEL_DEGREE / 2 {
            let block_end = core::cmp::min(block_start + 4, KERNEL_DEGREE / 2 + 1);
            let mut raw = 0u64;
            let mut ordinary_half_degree = block_start;
            while ordinary_half_degree < block_end {
                raw += u64::from(kernel[2 * ordinary_half_degree].0)
                    * u64::from(
                        MONOMIAL_TO_NATURAL_PARITY[ordinary_half_degree][natural_coordinate],
                    );
                ordinary_half_degree += 1;
            }
            outer += u64::from(M31::reduce_u64(raw).0);
            block_start = block_end;
        }
        natural[2 * natural_coordinate] = M31::reduce_u64(outer);
        natural_coordinate += 1;
    }
    natural
}

/// Exact 6-variable MLE suffix for relation coordinates 3..8. The last
/// relation coordinate is the low bit of each aligned p/q row pair, so it is
/// factored once per terminal below instead of being rebuilt in all 128
/// suffix leaves. This is the literal identity
/// `eq(r, 2*i+b) = eq(r[3..9], i) * (b ? r[9] : 1-r[9])`.
fn mle_six_coordinate_suffix_weights(point: &[QM31; 10]) -> [QM31; 64] {
    let mut weights = [QM31::ZERO; 64];
    weights[0] = QM31::ONE;
    let mut width = 1usize;
    let mut coordinate = 3usize;
    while coordinate < 9 {
        let prepared_coordinate = PreparedQm31Multiplier::new(point[coordinate]);
        let mut index = width;
        while index > 0 {
            index -= 1;
            let parent = weights[index];
            let right = prepared_coordinate.mul(parent);
            weights[2 * index] = parent.sub(right);
            weights[2 * index + 1] = right;
        }
        width *= 2;
        coordinate += 1;
    }
    debug_assert_eq!(width, 64);
    weights
}

#[cfg(test)]
fn mle_three_bit_prefix(point: &[QM31; 10], high_bits: usize) -> QM31 {
    debug_assert!(high_bits < 8);
    let mut prefix = QM31::ONE;
    let mut coordinate = 0usize;
    while coordinate < 3 {
        let bit = (high_bits >> (2 - coordinate)) & 1;
        prefix = if bit == 0 {
            prefix.mul(QM31::ONE.sub(point[coordinate]))
        } else {
            prefix.mul(point[coordinate])
        };
        coordinate += 1;
    }
    prefix
}

/// The two deployed three-bit prefixes, sharing their middle-coordinate
/// multiplier. Algebraically these are `p0*p1*p2` and
/// `(1-p0)*p1*(1-p2)`; the latter factor is expanded as
/// `1-p0-p2+p0*p2` so both results use the same prepared `p1`.
fn deployed_three_bit_prefixes(point: &[QM31; 10]) -> (QM31, QM31) {
    let p0_times_p2 = point[0].mul(point[2]);
    let prepared_p1 = PreparedQm31Multiplier::new(point[1]);
    let a_prefix = prepared_p1.mul(p0_times_p2);
    let b_outer = QM31::ONE.sub(point[0]).sub(point[2]).add(p0_times_p2);
    let b_prefix = prepared_p1.mul(b_outer);
    (a_prefix, b_prefix)
}

fn evaluate_shifted_in_aligned_block(
    natural: &[M31; A_NATURAL_WIDTH],
    shift: usize,
    suffix_weights: &[QM31; 64],
    suffix_xor_mask: usize,
) -> QM31 {
    debug_assert!(shift < GOOD_A_SIZE);
    debug_assert!(suffix_xor_mask < suffix_weights.len());
    let support_end = KERNEL_DEGREE + shift + 1;
    debug_assert!(support_end <= natural.len());

    // Walk the exact parity support directly. Successive logical terms are
    // still reduced in blocks of four, exactly as in `qm31_m31_dot`; only the
    // temporary contiguous weight/value copies have been removed.
    let mut sums = [0u64; 4];
    let mut index = shift & 1;
    while index < support_end {
        let block_end = core::cmp::min(index + 8, support_end);
        let mut raw = [0u64; 4];
        while index < block_end {
            let weight = suffix_weights[index ^ suffix_xor_mask];
            let value = u64::from(natural[index].0);
            raw[0] += u64::from(weight.c0.a.0) * value;
            raw[1] += u64::from(weight.c0.b.0) * value;
            raw[2] += u64::from(weight.c1.a.0) * value;
            raw[3] += u64::from(weight.c1.b.0) * value;
            index += 2;
        }
        let mut limb = 0usize;
        while limb < raw.len() {
            sums[limb] += u64::from(M31::reduce_u64(raw[limb]).0);
            limb += 1;
        }
    }
    QM31 {
        c0: CM31::new(M31::reduce_u64(sums[0]), M31::reduce_u64(sums[1])),
        c1: CM31::new(M31::reduce_u64(sums[2]), M31::reduce_u64(sums[3])),
    }
}

/// Evaluate the base and xor12 terminal dots in one traversal. The two
/// outputs retain the exact product grouping and reduction boundaries of two
/// independent `evaluate_shifted_in_aligned_block` calls; only the public
/// support traversal and natural-coordinate load are shared.
fn evaluate_shifted_in_aligned_block_base_xor(
    natural: &[M31; A_NATURAL_WIDTH],
    shift: usize,
    suffix_weights: &[QM31; 64],
    suffix_xor_mask: usize,
) -> [QM31; 2] {
    debug_assert!(shift < GOOD_A_SIZE);
    debug_assert!(suffix_xor_mask < suffix_weights.len());
    let support_end = KERNEL_DEGREE + shift + 1;
    debug_assert!(support_end <= natural.len());

    let mut base_sums = [0u64; 4];
    let mut xor_sums = [0u64; 4];
    let mut index = shift & 1;
    while index < support_end {
        let block_end = core::cmp::min(index + 8, support_end);
        let mut base_raw = [0u64; 4];
        let mut xor_raw = [0u64; 4];
        while index < block_end {
            let base_weight = suffix_weights[index];
            let xor_weight = suffix_weights[index ^ suffix_xor_mask];
            let value = u64::from(natural[index].0);
            base_raw[0] += u64::from(base_weight.c0.a.0) * value;
            base_raw[1] += u64::from(base_weight.c0.b.0) * value;
            base_raw[2] += u64::from(base_weight.c1.a.0) * value;
            base_raw[3] += u64::from(base_weight.c1.b.0) * value;
            xor_raw[0] += u64::from(xor_weight.c0.a.0) * value;
            xor_raw[1] += u64::from(xor_weight.c0.b.0) * value;
            xor_raw[2] += u64::from(xor_weight.c1.a.0) * value;
            xor_raw[3] += u64::from(xor_weight.c1.b.0) * value;
            index += 2;
        }
        let mut limb = 0usize;
        while limb < base_raw.len() {
            base_sums[limb] += u64::from(M31::reduce_u64(base_raw[limb]).0);
            xor_sums[limb] += u64::from(M31::reduce_u64(xor_raw[limb]).0);
            limb += 1;
        }
    }
    [
        QM31 {
            c0: CM31::new(M31::reduce_u64(base_sums[0]), M31::reduce_u64(base_sums[1])),
            c1: CM31::new(M31::reduce_u64(base_sums[2]), M31::reduce_u64(base_sums[3])),
        },
        QM31 {
            c0: CM31::new(M31::reduce_u64(xor_sums[0]), M31::reduce_u64(xor_sums[1])),
            c1: CM31::new(M31::reduce_u64(xor_sums[2]), M31::reduce_u64(xor_sums[3])),
        },
    ]
}

/// Literal staged predecessor retained as a differential oracle for the
/// direct parity-strided dot product above.
#[cfg(test)]
fn evaluate_shifted_in_aligned_block_reference(
    natural: &[M31; A_NATURAL_WIDTH],
    shift: usize,
    suffix_weights: &[QM31; 64],
    suffix_xor_mask: usize,
) -> QM31 {
    let mut weights = [QM31::ZERO; 24];
    let mut values = [M31::ZERO; 24];
    let mut count = 0usize;
    // K is even and multiplication by X flips parity, so S^shift K has
    // support only on natural indices congruent to shift modulo two.
    // Its exact ordinary degree is 36 + shift, hence the fixed 24-entry
    // buffers cover the largest (shift 11) parity support without padding
    // the arithmetic dot product with known-zero terms.
    let mut index = shift & 1;
    let support_end = KERNEL_DEGREE + shift + 1;
    while index < support_end {
        weights[count] = suffix_weights[index ^ suffix_xor_mask];
        values[count] = natural[index];
        count += 1;
        index += 2;
    }
    qm31_m31_dot(&weights[..count], &values[..count])
}

fn evaluate_b_inactive(natural: &[M31; A_NATURAL_WIDTH]) -> QM31 {
    let mut raw = 0u64;
    for &index in &B_INACTIVE_NATURAL_SUPPORT {
        raw += u64::from(natural[usize::from(index)].0);
    }
    debug_assert!(raw < 30 * M31_MODULUS_U64);
    let value = M31::reduce_u64(raw);
    QM31::from_cm31(CM31::from_m31(value))
}

#[cfg(test)]
fn evaluate_b_inactive_reference(natural: &[M31; A_NATURAL_WIDTH]) -> QM31 {
    let masks = atomic_state_only_copy_inactive_row_masks_v3();
    let mut value = M31::ZERO;
    let mut index = 0usize;
    while index < B_NATURAL_WIDTH {
        let row = 256 + 2 * index;
        if masks[row >> 4] & (1 << (row & 15)) != 0 {
            value = value.add(natural[index]);
        }
        index += 1;
    }
    QM31::from_cm31(CM31::from_m31(value))
}

/// Exact trailing-one count for the only indices reachable by
/// `natural_mul_x`.  Keeping this tiny indexed loop in the verifier makes the
/// production control flow directly translatable by pinned Aeneas; the
/// standard-library `usize::trailing_ones` intrinsic is otherwise opaque to
/// that toolchain.
#[cfg(test)]
fn natural_shift_trailing_ones(mut index: usize) -> usize {
    let mut count = 0usize;
    while index & 1 == 1 {
        count += 1;
        index >>= 1;
    }
    count
}

/// Multiplication by `X` in the deployed natural tensor basis. For an even
/// index the result is the next basis vector. For an odd index, repeatedly
/// applying `T_n(X)^2 = (T_{2n}(X) + 1) / 2` across the trailing-one carry
/// yields at most six terms. This is the 89-nonzero reachable part of
/// `Conv * ordinaryShift * Conv^-1` checked by
/// `tools/v5_good_gate_sparse_shift.py`.
#[cfg(test)]
fn natural_mul_x_reference(input: &[M31; A_NATURAL_WIDTH]) -> [M31; A_NATURAL_WIDTH] {
    // Every caller has ordinary degree at most 46 before this operation.
    debug_assert!(input[47].is_zero());
    let mut output = [M31::ZERO; A_NATURAL_WIDTH];
    let mut index = 0usize;
    while index < 47 {
        let coefficient = input[index];
        if coefficient.is_zero() {
            index += 1;
            continue;
        }
        if index & 1 == 0 {
            output[index + 1] = output[index + 1].add(coefficient);
        } else {
            let trailing_ones = natural_shift_trailing_ones(index);
            let mut carry = 1usize;
            let mut scaled = coefficient;
            while carry <= trailing_ones {
                scaled = scaled.half();
                let target = index - ((1usize << carry) - 1);
                output[target] = output[target].add(scaled);
                carry += 1;
            }
            output[index + 1] = output[index + 1].add(scaled);
        }
        index += 1;
    }
    output
}

/// Multiplication by `X` on the exact support of `X^shift K`, where `K` is the
/// even degree-36 query kernel and `shift <= 10`. The parity and final occupied
/// coordinate are public constants of the requested direction. Iterating only
/// that support removes all data-dependent zero skips; odd-index carry lengths
/// come from the complete 24-entry table above.
fn natural_mul_x_fixed_support(
    input: &[M31; A_NATURAL_WIDTH],
    shift: usize,
) -> [M31; A_NATURAL_WIDTH] {
    debug_assert!(shift < GOOD_A_SIZE - 1);
    debug_assert!(input[A_NATURAL_WIDTH - 1].is_zero());
    let mut output = [M31::ZERO; A_NATURAL_WIDTH];
    let support_end = KERNEL_DEGREE + shift + 1;
    let mut index = shift & 1;
    while index < support_end {
        let coefficient = input[index];
        if index & 1 == 0 {
            output[index + 1] = output[index + 1].add(coefficient);
        } else {
            let trailing_ones = usize::from(ODD_NATURAL_TRAILING_ONES[index >> 1]);
            let mut carry = 1usize;
            let mut scaled = coefficient;
            while carry <= trailing_ones {
                scaled = scaled.half();
                let target = index - ((1usize << carry) - 1);
                output[target] = output[target].add(scaled);
                carry += 1;
            }
            output[index + 1] = output[index + 1].add(scaled);
        }
        index += 2;
    }
    output
}

fn good_shifted_directions(kernel: &[M31; 37]) -> Vec<[M31; A_NATURAL_WIDTH]> {
    let base = even_kernel_to_natural(kernel);
    let mut shifted_directions = Vec::with_capacity(GOOD_A_SIZE);
    shifted_directions.push(base);

    let mut shifted = base;
    let mut shift = 1usize;
    while shift <= 11 {
        shifted = natural_mul_x_fixed_support(&shifted, shift - 1);
        shifted_directions.push(shifted);
        shift += 1;
    }
    debug_assert_eq!(shifted_directions.len(), GOOD_A_SIZE);
    shifted_directions
}

#[derive(Clone, Copy)]
struct PreparedTerminalScales {
    a_p: PreparedQm31Multiplier,
    a_q: PreparedQm31Multiplier,
    b_p: PreparedQm31Multiplier,
}

fn prepared_terminal_scales(
    a_prefix: QM31,
    b_prefix: QM31,
    last_coordinate: QM31,
) -> PreparedTerminalScales {
    let one_minus_last = QM31::ONE.sub(last_coordinate);
    PreparedTerminalScales {
        a_p: PreparedQm31Multiplier::new(a_prefix.mul(one_minus_last)),
        a_q: PreparedQm31Multiplier::new(a_prefix.mul(last_coordinate)),
        b_p: PreparedQm31Multiplier::new(b_prefix.mul(one_minus_last)),
    }
}

fn fill_good_terminal_from_dots(
    a_matrix: &mut GoodAMatrix,
    b_matrix: &mut GoodBMatrix,
    dots: &[QM31; GOOD_A_SIZE],
    scales: PreparedTerminalScales,
    terminal: usize,
) {
    // The first eleven A columns are (X^s - 1)K in the p block.
    let mut direction = 0usize;
    while direction < GOOD_A_SIZE - 1 {
        let value = scales.a_p.mul(dots[direction + 1].sub(dots[0]));
        let limbs = m31_coordinates(value);
        let mut limb = 0usize;
        while limb < limbs.len() {
            a_matrix[4 * terminal + limb][direction] = limbs[limb];
            limb += 1;
        }
        direction += 1;
    }

    // The twelfth A column is (X - 1)K in the q block.
    let q_value = scales.a_q.mul(dots[1].sub(dots[0]));
    let q_limbs = m31_coordinates(q_value);
    let mut limb = 0usize;
    while limb < q_limbs.len() {
        a_matrix[4 * terminal + limb][GOOD_A_SIZE - 1] = q_limbs[limb];
        limb += 1;
    }

    direction = 0;
    while direction < GOOD_B_SIZE {
        b_matrix[terminal + 1][direction] = scales.b_p.mul(dots[direction]);
        direction += 1;
    }
}

fn fill_good_base_and_xor_terminals(
    a_matrix: &mut GoodAMatrix,
    b_matrix: &mut GoodBMatrix,
    shifted_directions: &[[M31; A_NATURAL_WIDTH]],
    point: &[QM31; 10],
) {
    // In the six-coordinate tree (coordinates 3..8), relation coordinates
    // 6 and 7 occupy index bits 2 and 1.
    const XOR12_SUFFIX_MASK: usize = (1 << 2) | (1 << 1);
    let suffix_weights = mle_six_coordinate_suffix_weights(point);
    let (a_prefix, b_prefix) = deployed_three_bit_prefixes(point);
    let scales = prepared_terminal_scales(a_prefix, b_prefix, point[9]);
    let mut base_dots = [QM31::ZERO; GOOD_A_SIZE];
    let mut xor_dots = [QM31::ZERO; GOOD_A_SIZE];
    let mut shift = 0usize;
    while shift < GOOD_A_SIZE {
        let pair = evaluate_shifted_in_aligned_block_base_xor(
            &shifted_directions[shift],
            shift,
            &suffix_weights,
            XOR12_SUFFIX_MASK,
        );
        base_dots[shift] = pair[0];
        xor_dots[shift] = pair[1];
        shift += 1;
    }
    fill_good_terminal_from_dots(a_matrix, b_matrix, &base_dots, scales, 0);
    // xor12 flips relation coordinates 6 and 7. In the seven-variable
    // suffix (coordinates 3..9), those are index bits 3 and 2. Its weights
    // are therefore an exact XOR permutation of the original suffix tree;
    // the three-bit prefix is unchanged.
    fill_good_terminal_from_dots(a_matrix, b_matrix, &xor_dots, scales, 2);
}

fn fill_good_successor_terminal(
    a_matrix: &mut GoodAMatrix,
    b_matrix: &mut GoodBMatrix,
    shifted_directions: &[[M31; A_NATURAL_WIDTH]],
    successor: &[QM31; 10],
) {
    let suffix_weights = mle_six_coordinate_suffix_weights(successor);
    let mut dots = [QM31::ZERO; GOOD_A_SIZE];
    let mut shift = 0usize;
    while shift < GOOD_A_SIZE {
        dots[shift] = evaluate_shifted_in_aligned_block(
            &shifted_directions[shift],
            shift,
            &suffix_weights,
            0,
        );
        shift += 1;
    }
    let (a_prefix, b_prefix) = deployed_three_bit_prefixes(successor);
    let scales = prepared_terminal_scales(a_prefix, b_prefix, successor[9]);
    fill_good_terminal_from_dots(a_matrix, b_matrix, &dots, scales, 1);
}

fn good_matrices(kernel: &[M31; 37], point: &[QM31; 10]) -> (GoodAMatrix, GoodBMatrix) {
    let shifted_directions = good_shifted_directions(kernel);
    let mut a_matrix = [[M31::ZERO; GOOD_A_SIZE]; GOOD_A_SIZE];
    let mut b_matrix = [[QM31::ZERO; GOOD_B_SIZE]; GOOD_B_SIZE];
    let mut direction = 0usize;
    while direction < GOOD_B_SIZE {
        b_matrix[0][direction] = evaluate_b_inactive(&shifted_directions[direction]);
        direction += 1;
    }

    fill_good_base_and_xor_terminals(&mut a_matrix, &mut b_matrix, &shifted_directions, point);

    let successor = binary_successor_point(point);
    fill_good_successor_terminal(
        &mut a_matrix,
        &mut b_matrix,
        &shifted_directions,
        &successor,
    );
    (a_matrix, b_matrix)
}

fn m31_determinant(mut matrix: GoodAMatrix) -> M31 {
    let mut determinant = M31::ONE;
    let mut column = 0usize;
    while column < GOOD_A_SIZE {
        let mut pivot = column;
        while pivot < GOOD_A_SIZE && matrix[pivot][column].is_zero() {
            pivot += 1;
        }
        if pivot == GOOD_A_SIZE {
            return M31::ZERO;
        }
        if pivot != column {
            matrix.swap(pivot, column);
            determinant = determinant.neg();
        }
        let pivot_value = matrix[column][column];
        determinant = determinant.mul(pivot_value);
        let inverse = pivot_value.inv();
        let pivot_row = matrix[column];
        let mut row = column + 1;
        while row < GOOD_A_SIZE {
            let scale = matrix[row][column].mul(inverse);
            let mut entry = column;
            while entry < GOOD_A_SIZE {
                matrix[row][entry] = matrix[row][entry].sub(scale.mul(pivot_row[entry]));
                entry += 1;
            }
            row += 1;
        }
        column += 1;
    }
    determinant
}

fn qm31_determinant(mut matrix: GoodBMatrix) -> QM31 {
    let mut determinant = QM31::ONE;
    let mut column = 0usize;
    while column < GOOD_B_SIZE {
        let mut pivot = column;
        while pivot < GOOD_B_SIZE && matrix[pivot][column].is_zero() {
            pivot += 1;
        }
        if pivot == GOOD_B_SIZE {
            return QM31::ZERO;
        }
        if pivot != column {
            matrix.swap(pivot, column);
            determinant = determinant.neg();
        }
        let pivot_value = matrix[column][column];
        determinant = determinant.mul(pivot_value);
        let inverse = pivot_value.inv();
        let pivot_row = matrix[column];
        let mut row = column + 1;
        while row < GOOD_B_SIZE {
            let scale = matrix[row][column].mul(inverse);
            let mut entry = column;
            while entry < GOOD_B_SIZE {
                matrix[row][entry] = matrix[row][entry].sub(scale.mul(pivot_row[entry]));
                entry += 1;
            }
            row += 1;
        }
        column += 1;
    }
    determinant
}

/// One exact M31 fraction-free update with one modular reduction.
///
/// Every input is canonical, so both products are at most `(P - 1)^2`.
/// Adding `P^2` before the subtraction makes the raw numerator nonnegative,
/// and the complete interval
/// `[P^2 - (P - 1)^2, P^2 + (P - 1)^2]` lies strictly below `2^63`.
#[inline(always)]
fn m31_fraction_free_update(value: M31, pivot: M31, leading: M31, pivot_row_value: M31) -> M31 {
    let positive = u64::from(value.0) * u64::from(pivot.0);
    let negative = u64::from(leading.0) * u64::from(pivot_row_value.0);
    M31::reduce_u64(positive + M31_MODULUS_SQUARED - negative)
}

/// One exact QM31 fraction-free update. The two fixed left factors are
/// prepared once per eliminated row; their eighteen M31 products share the
/// same nine bounded Karatsuba accumulators and therefore only nine reductions.
#[inline(always)]
fn qm31_fraction_free_update(
    prepared: &[PreparedQm31Multiplier; 2],
    value: QM31,
    pivot_row_value: QM31,
) -> QM31 {
    qm31_sum_products2_prepared(prepared, &[value, pivot_row_value])
}

/// Fraction-free Gaussian elimination. Every successful step is the exact
/// invertible row operation `row := pivot * row - leading * pivot_row`, with
/// nonzero `pivot`; therefore this returns true exactly when the determinant
/// above is nonzero, without paying for twelve inversions on-chain.
fn m31_matrix_nonsingular(mut matrix: GoodAMatrix) -> bool {
    let mut column = 0usize;
    while column < GOOD_A_SIZE {
        let mut pivot = column;
        while pivot < GOOD_A_SIZE && matrix[pivot][column].is_zero() {
            pivot += 1;
        }
        if pivot == GOOD_A_SIZE {
            return false;
        }
        if pivot != column {
            matrix.swap(pivot, column);
        }
        let pivot_value = matrix[column][column];
        let pivot_row = matrix[column];
        let mut row = column + 1;
        while row < GOOD_A_SIZE {
            let leading = matrix[row][column];
            matrix[row][column] = M31::ZERO;
            let mut entry = column + 1;
            while entry < GOOD_A_SIZE {
                matrix[row][entry] = m31_fraction_free_update(
                    matrix[row][entry],
                    pivot_value,
                    leading,
                    pivot_row[entry],
                );
                entry += 1;
            }
            row += 1;
        }
        column += 1;
    }
    true
}

fn qm31_matrix_nonsingular(mut matrix: GoodBMatrix) -> bool {
    let mut column = 0usize;
    while column < GOOD_B_SIZE {
        let mut pivot = column;
        while pivot < GOOD_B_SIZE && matrix[pivot][column].is_zero() {
            pivot += 1;
        }
        if pivot == GOOD_B_SIZE {
            return false;
        }
        if pivot != column {
            matrix.swap(pivot, column);
        }
        let pivot_value = matrix[column][column];
        let pivot_row = matrix[column];
        let mut row = column + 1;
        if row < GOOD_B_SIZE {
            let prepared_pivot = PreparedQm31Multiplier::new(pivot_value);
            while row < GOOD_B_SIZE {
                let leading = matrix[row][column];
                matrix[row][column] = QM31::ZERO;
                let prepared = [prepared_pivot, PreparedQm31Multiplier::new(leading.neg())];
                let mut entry = column + 1;
                while entry < GOOD_B_SIZE {
                    matrix[row][entry] =
                        qm31_fraction_free_update(&prepared, matrix[row][entry], pivot_row[entry]);
                    entry += 1;
                }
                row += 1;
            }
        }
        column += 1;
    }
    true
}

#[cfg(test)]
fn m31_matrix_nonsingular_reference(mut matrix: GoodAMatrix) -> bool {
    let mut column = 0usize;
    while column < GOOD_A_SIZE {
        let mut pivot = column;
        while pivot < GOOD_A_SIZE && matrix[pivot][column].is_zero() {
            pivot += 1;
        }
        if pivot == GOOD_A_SIZE {
            return false;
        }
        if pivot != column {
            matrix.swap(pivot, column);
        }
        let pivot_value = matrix[column][column];
        let pivot_row = matrix[column];
        let mut row = column + 1;
        while row < GOOD_A_SIZE {
            let leading = matrix[row][column];
            matrix[row][column] = M31::ZERO;
            let mut entry = column + 1;
            while entry < GOOD_A_SIZE {
                matrix[row][entry] = matrix[row][entry]
                    .mul(pivot_value)
                    .sub(leading.mul(pivot_row[entry]));
                entry += 1;
            }
            row += 1;
        }
        column += 1;
    }
    true
}

#[cfg(test)]
fn qm31_matrix_nonsingular_reference(mut matrix: GoodBMatrix) -> bool {
    let mut column = 0usize;
    while column < GOOD_B_SIZE {
        let mut pivot = column;
        while pivot < GOOD_B_SIZE && matrix[pivot][column].is_zero() {
            pivot += 1;
        }
        if pivot == GOOD_B_SIZE {
            return false;
        }
        if pivot != column {
            matrix.swap(pivot, column);
        }
        let pivot_value = matrix[column][column];
        let pivot_row = matrix[column];
        let mut row = column + 1;
        while row < GOOD_B_SIZE {
            let leading = matrix[row][column];
            matrix[row][column] = QM31::ZERO;
            let mut entry = column + 1;
            while entry < GOOD_B_SIZE {
                matrix[row][entry] = matrix[row][entry]
                    .mul(pivot_value)
                    .sub(leading.mul(pivot_row[entry]));
                entry += 1;
            }
            row += 1;
        }
        column += 1;
    }
    true
}

/// Recompute the exact fixed GoodA and GoodB matrices from one public
/// terminal point and one transcript-derived q18 candidate.
pub fn evaluate_candidate(
    point: &[QM31; 10],
    queries: [u32; V5_CU_PROBE_QUERY_COUNT],
) -> Option<GoodGateEvaluation> {
    let kernel = query_kernel(&queries)?;
    let (good_a_matrix, good_b_matrix) = good_matrices(&kernel, point);
    let good_a_determinant = m31_determinant(good_a_matrix);
    let good_b_determinant = qm31_determinant(good_b_matrix);
    Some(GoodGateEvaluation {
        queries,
        good_a_matrix,
        good_a_determinant,
        good_b_matrix,
        good_b_determinant,
    })
}

/// SBF predicate path. It constructs byte-for-byte the same two matrices as
/// `evaluate_candidate`, then uses fraction-free elimination, which is
/// equivalent to testing the two exact determinants for nonzeroness.
pub fn candidate_is_good(
    point: &[QM31; 10],
    queries: [u32; V5_CU_PROBE_QUERY_COUNT],
) -> Option<bool> {
    let kernel = query_kernel(&queries)?;
    let (good_a_matrix, good_b_matrix) = good_matrices(&kernel, point);
    let good_a = m31_matrix_nonsingular(good_a_matrix);
    let good_b = qm31_matrix_nonsingular(good_b_matrix);
    Some(good_a && good_b)
}

/// Exact least-good rule after all three public candidates have been
/// evaluated. No earlier branch may be good and the selected branch must be.
pub fn selected_is_least_good(selected: u8, evaluations: &[bool; 3]) -> bool {
    let selected = usize::from(selected);
    selected < evaluations.len()
        && evaluations[selected]
        && evaluations[..selected].iter().all(|good| !good)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn qm31(limbs: [u32; 4]) -> QM31 {
        QM31 {
            c0: CM31::new(M31(limbs[0]), M31(limbs[1])),
            c1: CM31::new(M31(limbs[2]), M31(limbs[3])),
        }
    }

    fn random_m31(state: &mut u64) -> M31 {
        *state ^= *state << 13;
        *state ^= *state >> 7;
        *state ^= *state << 17;
        M31((*state % u64::from(P)) as u32)
    }

    fn random_qm31(state: &mut u64) -> QM31 {
        qm31([
            random_m31(state).0,
            random_m31(state).0,
            random_m31(state).0,
            random_m31(state).0,
        ])
    }

    fn mle_six_coordinate_suffix_weights_reference(point: &[QM31; 10]) -> [QM31; 64] {
        let mut weights = [QM31::ZERO; 64];
        weights[0] = QM31::ONE;
        let mut width = 1usize;
        let mut coordinate = 3usize;
        while coordinate < 9 {
            let mut index = width;
            while index > 0 {
                index -= 1;
                let parent = weights[index];
                let right = point[coordinate].mul(parent);
                weights[2 * index] = parent.sub(right);
                weights[2 * index + 1] = right;
            }
            width *= 2;
            coordinate += 1;
        }
        weights
    }

    fn fill_good_terminal_reference(
        a_matrix: &mut GoodAMatrix,
        b_matrix: &mut GoodBMatrix,
        shifted_directions: &[[M31; A_NATURAL_WIDTH]],
        suffix_weights: &[QM31; 64],
        suffix_xor_mask: usize,
        a_prefix: QM31,
        b_prefix: QM31,
        last_coordinate: QM31,
        terminal: usize,
    ) {
        let mut dots = [QM31::ZERO; GOOD_A_SIZE];
        let mut shift = 0usize;
        while shift < GOOD_A_SIZE {
            dots[shift] = evaluate_shifted_in_aligned_block_reference(
                &shifted_directions[shift],
                shift,
                suffix_weights,
                suffix_xor_mask,
            );
            shift += 1;
        }

        let one_minus_last = QM31::ONE.sub(last_coordinate);
        let a_p_prefix = a_prefix.mul(one_minus_last);
        let a_q_prefix = a_prefix.mul(last_coordinate);
        let b_p_prefix = b_prefix.mul(one_minus_last);
        let mut direction = 0usize;
        while direction < GOOD_A_SIZE - 1 {
            let limbs = m31_coordinates(a_p_prefix.mul(dots[direction + 1].sub(dots[0])));
            let mut limb = 0usize;
            while limb < limbs.len() {
                a_matrix[4 * terminal + limb][direction] = limbs[limb];
                limb += 1;
            }
            direction += 1;
        }
        let q_limbs = m31_coordinates(a_q_prefix.mul(dots[1].sub(dots[0])));
        let mut limb = 0usize;
        while limb < q_limbs.len() {
            a_matrix[4 * terminal + limb][GOOD_A_SIZE - 1] = q_limbs[limb];
            limb += 1;
        }
        direction = 0;
        while direction < GOOD_B_SIZE {
            b_matrix[terminal + 1][direction] = b_p_prefix.mul(dots[direction]);
            direction += 1;
        }
    }

    fn good_matrices_reference(
        kernel: &[M31; KERNEL_DEGREE + 1],
        point: &[QM31; 10],
    ) -> (GoodAMatrix, GoodBMatrix) {
        const XOR12_SUFFIX_MASK: usize = (1 << 2) | (1 << 1);
        let shifted_directions = good_shifted_directions(kernel);
        let mut a_matrix = [[M31::ZERO; GOOD_A_SIZE]; GOOD_A_SIZE];
        let mut b_matrix = [[QM31::ZERO; GOOD_B_SIZE]; GOOD_B_SIZE];
        let mut direction = 0usize;
        while direction < GOOD_B_SIZE {
            b_matrix[0][direction] = evaluate_b_inactive_reference(&shifted_directions[direction]);
            direction += 1;
        }

        let suffix_weights = mle_six_coordinate_suffix_weights_reference(point);
        let a_prefix = mle_three_bit_prefix(point, 0b111);
        let b_prefix = mle_three_bit_prefix(point, 0b010);
        fill_good_terminal_reference(
            &mut a_matrix,
            &mut b_matrix,
            &shifted_directions,
            &suffix_weights,
            0,
            a_prefix,
            b_prefix,
            point[9],
            0,
        );
        fill_good_terminal_reference(
            &mut a_matrix,
            &mut b_matrix,
            &shifted_directions,
            &suffix_weights,
            XOR12_SUFFIX_MASK,
            a_prefix,
            b_prefix,
            point[9],
            2,
        );

        let successor = binary_successor_point(point);
        let successor_suffix = mle_six_coordinate_suffix_weights_reference(&successor);
        fill_good_terminal_reference(
            &mut a_matrix,
            &mut b_matrix,
            &shifted_directions,
            &successor_suffix,
            0,
            mle_three_bit_prefix(&successor, 0b111),
            mle_three_bit_prefix(&successor, 0b010),
            successor[9],
            1,
        );
        (a_matrix, b_matrix)
    }

    fn candidate_is_good_reference(
        point: &[QM31; 10],
        queries: [u32; V5_CU_PROBE_QUERY_COUNT],
    ) -> Option<bool> {
        let kernel = query_kernel_reference(&queries)?;
        let (good_a_matrix, good_b_matrix) = good_matrices_reference(&kernel, point);
        Some(
            m31_matrix_nonsingular_reference(good_a_matrix)
                && qm31_matrix_nonsingular_reference(good_b_matrix),
        )
    }

    fn assert_matrix_decisions_match(a: GoodAMatrix, b: GoodBMatrix) -> (bool, bool) {
        let fused_a = m31_matrix_nonsingular(a);
        let fused_b = qm31_matrix_nonsingular(b);
        assert_eq!(fused_a, m31_matrix_nonsingular_reference(a));
        assert_eq!(fused_b, qm31_matrix_nonsingular_reference(b));
        assert_eq!(fused_a, !m31_determinant(a).is_zero());
        assert_eq!(fused_b, !qm31_determinant(b).is_zero());
        (fused_a, fused_b)
    }

    #[test]
    fn fused_m31_mul_add_matches_edges_bound_and_random() {
        let edges = [M31::ZERO, M31::ONE, M31(P - 1)];
        for product_left in edges {
            for product_right in edges {
                for addend in edges {
                    assert_eq!(
                        m31_mul_add_reduced(product_left, product_right, addend),
                        product_left.mul(product_right).add(addend)
                    );
                }
            }
        }
        assert_eq!(
            QUERY_KERNEL_FUSED_MAX,
            u64::from(P - 1) * u64::from(P - 1) + u64::from(P - 1)
        );
        assert!(QUERY_KERNEL_FUSED_MAX < (1u64 << 62));

        let mut state = 0x6d75_6c61_6464_7635u64;
        let mut sample = 0usize;
        while sample < 4_096 {
            let product_left = random_m31(&mut state);
            let product_right = random_m31(&mut state);
            let addend = random_m31(&mut state);
            assert_eq!(
                m31_mul_add_reduced(product_left, product_right, addend),
                product_left.mul(product_right).add(addend),
                "random sample {sample}"
            );
            sample += 1;
        }
    }

    #[test]
    fn prepared_suffix_and_shared_prefixes_match_literal_formulas() {
        let maximal = qm31([P - 1; 4]);
        let alternating = qm31([P - 1, 0, 1, P - 2]);
        let edges = [QM31::ZERO, QM31::ONE, maximal, alternating];
        for p0 in edges {
            for p1 in edges {
                for p2 in edges {
                    let mut point = [QM31::ZERO; 10];
                    point[0] = p0;
                    point[1] = p1;
                    point[2] = p2;
                    assert_eq!(
                        deployed_three_bit_prefixes(&point),
                        (
                            mle_three_bit_prefix(&point, 0b111),
                            mle_three_bit_prefix(&point, 0b010),
                        )
                    );
                }
            }
        }

        let mut edge_point = [maximal; 10];
        for value in edges {
            let mut coordinate = 3usize;
            while coordinate < 9 {
                edge_point[coordinate] = value;
                coordinate += 1;
            }
            assert_eq!(
                mle_six_coordinate_suffix_weights(&edge_point),
                mle_six_coordinate_suffix_weights_reference(&edge_point)
            );
        }

        let mut state = 0x7072_6570_7375_6666u64;
        let mut sample = 0usize;
        while sample < 512 {
            let point = core::array::from_fn(|_| random_qm31(&mut state));
            assert_eq!(
                mle_six_coordinate_suffix_weights(&point),
                mle_six_coordinate_suffix_weights_reference(&point),
                "suffix sample {sample}"
            );
            assert_eq!(
                deployed_three_bit_prefixes(&point),
                (
                    mle_three_bit_prefix(&point, 0b111),
                    mle_three_bit_prefix(&point, 0b010),
                ),
                "prefix sample {sample}"
            );
            sample += 1;
        }
    }

    #[test]
    fn fused_m31_fraction_free_update_matches_edges_bounds_and_random() {
        let edges = [M31::ZERO, M31::ONE, M31(P - 1)];
        for value in edges {
            for pivot in edges {
                for leading in edges {
                    for pivot_row_value in edges {
                        assert_eq!(
                            m31_fraction_free_update(value, pivot, leading, pivot_row_value,),
                            value.mul(pivot).sub(leading.mul(pivot_row_value)),
                            "edge value={} pivot={} leading={} pivot_row={}",
                            value.0,
                            pivot.0,
                            leading.0,
                            pivot_row_value.0,
                        );
                    }
                }
            }
        }

        let maximal_product = u64::from(P - 1) * u64::from(P - 1);
        assert_eq!(M31_MODULUS_SQUARED - maximal_product, 4_294_967_293);
        assert_eq!(
            M31_MODULUS_SQUARED + maximal_product,
            9_223_372_023_969_873_925
        );
        assert!(M31_MODULUS_SQUARED + maximal_product < (1u64 << 63));

        let mut state = 0x6672_6163_7469_6f6eu64;
        let mut sample = 0usize;
        while sample < 4_096 {
            let value = random_m31(&mut state);
            let pivot = random_m31(&mut state);
            let leading = random_m31(&mut state);
            let pivot_row_value = random_m31(&mut state);
            assert_eq!(
                m31_fraction_free_update(value, pivot, leading, pivot_row_value),
                value.mul(pivot).sub(leading.mul(pivot_row_value)),
                "random sample {sample}"
            );
            sample += 1;
        }
    }

    #[test]
    fn prepared_qm31_fraction_free_update_matches_edges_and_random() {
        let maximal = qm31([P - 1; 4]);
        let alternating = qm31([P - 1, 0, 1, P - 2]);
        let edges = [QM31::ZERO, QM31::ONE, maximal, alternating];
        for value in edges {
            for pivot in edges {
                for leading in edges {
                    for pivot_row_value in edges {
                        let prepared = [
                            PreparedQm31Multiplier::new(pivot),
                            PreparedQm31Multiplier::new(leading.neg()),
                        ];
                        assert_eq!(
                            qm31_fraction_free_update(&prepared, value, pivot_row_value),
                            value.mul(pivot).sub(leading.mul(pivot_row_value))
                        );
                    }
                }
            }
        }

        let mut state = 0x716d_3331_6675_7365u64;
        let mut sample = 0usize;
        while sample < 2_048 {
            let value = random_qm31(&mut state);
            let pivot = random_qm31(&mut state);
            let leading = random_qm31(&mut state);
            let pivot_row_value = random_qm31(&mut state);
            let prepared = [
                PreparedQm31Multiplier::new(pivot),
                PreparedQm31Multiplier::new(leading.neg()),
            ];
            assert_eq!(
                qm31_fraction_free_update(&prepared, value, pivot_row_value),
                value.mul(pivot).sub(leading.mul(pivot_row_value)),
                "random sample {sample}"
            );
            sample += 1;
        }
    }

    /// This fixture is produced by the exact current mode-9 host builder.
    /// Several q18 indices exceed the log-17 fibre count, so this also
    /// permanently detects accidental use of the relation log in place of
    /// the live log-19 C1 domain.
    #[test]
    fn current_fixture_selector_zero_matches_host_certificates() {
        let point = [
            qm31([404107582, 1727074950, 929436228, 337050246]),
            qm31([1551059663, 276722441, 1042656822, 513863785]),
            qm31([164049145, 1996763382, 1728701267, 1725471872]),
            qm31([1579020738, 1603896284, 1206833734, 1303440574]),
            qm31([444095533, 1733870221, 271870451, 46368227]),
            qm31([1281619349, 328022466, 1429624261, 972991110]),
            qm31([1204014726, 1716417842, 1524198052, 774277607]),
            qm31([1082422057, 694365077, 591158920, 1683812251]),
            qm31([1577214774, 1016671131, 411456236, 1648869862]),
            qm31([758441825, 1940717419, 1517866177, 737596238]),
        ];
        let queries = [
            115997, 51779, 92617, 43401, 78758, 66857, 81115, 39787, 112113, 76348, 73402, 59549,
            82876, 101923, 86422, 120558, 124241, 68942,
        ];
        let kernel = query_kernel(&queries).unwrap();
        assert_eq!(
            kernel.map(|coefficient| coefficient.0),
            [
                519620177, 0, 528764235, 0, 671819249, 0, 2140992514, 0, 1843223343, 0, 1094648776,
                0, 1064183334, 0, 1834578843, 0, 113403409, 0, 785436993, 0, 852377093, 0,
                1757436383, 0, 1641054439, 0, 479908979, 0, 1253767301, 0, 1177649036, 0,
                1272219910, 0, 2076166121, 0, 1,
            ]
        );
        let evaluation = evaluate_candidate(&point, queries).unwrap();
        assert_eq!(
            evaluation
                .good_a_matrix
                .map(|matrix_row| matrix_row.map(|entry| entry.0)),
            [
                [
                    478933871, 1389306168, 1301508847, 601113137, 1343064338, 1116107897,
                    538315754, 208360263, 1619472116, 1226019598, 422135760, 1423216147,
                ],
                [
                    513823415, 1128317070, 478783203, 491820112, 1663526088, 1108316311,
                    1683940281, 251046859, 130572886, 570517234, 1499570247, 48852529,
                ],
                [
                    1362468244, 264300151, 1435388776, 1697501892, 1686929892, 1301551981,
                    1352208899, 775121542, 1410083153, 1095277642, 166362380, 267574853,
                ],
                [
                    1098962808, 609194254, 2126440640, 353607599, 1020076395, 1811117627,
                    443708284, 1489519528, 433151634, 755881888, 963533458, 2071033599,
                ],
                [
                    1595969664, 393999516, 1395352878, 438605900, 857312908, 1879763202,
                    1224249377, 2040748501, 645394943, 1898127716, 1030972322, 994411103,
                ],
                [
                    1132164920, 2053621945, 1022434451, 1539148183, 1420907131, 1295171113,
                    374496010, 1866729958, 1073579588, 2064159009, 548050728, 1931373637,
                ],
                [
                    1170000740, 1887260042, 1617024355, 1579797109, 81616899, 1483738249,
                    210169269, 492665207, 563015342, 1522742364, 1371280460, 1653655386,
                ],
                [
                    435053671, 803250683, 434008863, 1524952018, 171243022, 474171660, 1831492465,
                    1557070114, 1205148058, 32644510, 1607857114, 417531636,
                ],
                [
                    845922390, 1405338316, 1503773937, 1612209634, 1326207377, 2099734683,
                    1827704055, 1578902566, 1046416700, 541230732, 1219268093, 780505556,
                ],
                [
                    52240688, 840593458, 620201061, 503657710, 1257098218, 1042118120, 649053095,
                    375490688, 1025554698, 1009494594, 900838602, 520035018,
                ],
                [
                    1102552152, 565947668, 2046331480, 2043436497, 1394058347, 1948571232,
                    175563703, 2139482202, 2016739051, 1411298040, 1076631, 1511589546,
                ],
                [
                    140626554, 970617680, 1383172367, 731297219, 831824231, 519396000, 1942619378,
                    359211631, 2005256770, 2015081168, 255765726, 1480652075,
                ],
            ]
        );
        assert_eq!(evaluation.good_a_determinant, M31(602656396));
        assert_eq!(
            m31_coordinates(evaluation.good_b_determinant).map(|limb| limb.0),
            [1928607552, 117324003, 1989941058, 1151427657]
        );
        assert!(evaluation.is_good());
        assert_eq!(candidate_is_good(&point, queries), Some(true));
        assert_eq!(
            m31_matrix_nonsingular(evaluation.good_a_matrix),
            !evaluation.good_a_determinant.is_zero()
        );
        assert_eq!(
            qm31_matrix_nonsingular(evaluation.good_b_matrix),
            !evaluation.good_b_determinant.is_zero()
        );
    }

    #[test]
    fn in_place_query_kernel_matches_literal_reference_on_distinct_schedules() {
        const FIBER_MASK: u32 = (1 << (C1_DOMAIN_LOG - 2)) - 1;
        let mut state = 0x716b_6572_6e65_6c35u64;
        let mut sample = 0usize;
        while sample < 64 {
            let start = random_m31(&mut state).0 & FIBER_MASK;
            let mut step = random_m31(&mut state).0 & FIBER_MASK;
            step |= 1;
            let queries = core::array::from_fn(|index| {
                start.wrapping_add((index as u32).wrapping_mul(step)) & FIBER_MASK
            });
            let mut sorted = queries;
            sorted.sort_unstable();
            assert!(sorted.windows(2).all(|pair| pair[0] != pair[1]));
            assert_eq!(query_kernel(&queries), query_kernel_reference(&queries));
            sample += 1;
        }
    }

    #[test]
    fn prevalidated_log19_point_helper_matches_shared_materializer_exhaustively() {
        let fibers = (0..C1_FIBER_COUNT as u32).collect::<Vec<_>>();
        let shared = selected_circle_fiber_points_shared(C1_DOMAIN_LOG, &fibers).unwrap();
        assert_eq!(shared.len(), C1_FIBER_COUNT);
        let mut fiber = 0usize;
        while fiber < C1_FIBER_COUNT {
            assert_eq!(
                selected_c1_fiber_point_prevalidated(fiber as u32),
                shared[fiber],
                "fiber {fiber}"
            );
            fiber += 1;
        }
    }

    #[test]
    fn query_kernel_rejects_every_out_of_range_position() {
        let valid = core::array::from_fn(|index| index as u32);
        let mut ordinal = 0usize;
        while ordinal < V5_CU_PROBE_QUERY_COUNT {
            let mut queries = valid;
            queries[ordinal] = C1_FIBER_COUNT as u32;
            assert_eq!(query_kernel(&queries), None, "ordinal {ordinal}");
            ordinal += 1;
        }
    }

    #[test]
    fn even_kernel_transform_matches_dense_reference_on_every_basis_and_random_input() {
        let reference = |kernel: &[M31; KERNEL_DEGREE + 1]| {
            let mut ordinary = [M31::ZERO; A_NATURAL_WIDTH];
            ordinary[..kernel.len()].copy_from_slice(kernel);
            ordinary_to_natural(&ordinary, A_NATURAL_WIDTH)
        };

        let mut half_degree = 0usize;
        while half_degree <= KERNEL_DEGREE / 2 {
            for coefficient in [M31::ONE, M31(P - 1)] {
                let mut kernel = [M31::ZERO; KERNEL_DEGREE + 1];
                kernel[2 * half_degree] = coefficient;
                assert_eq!(even_kernel_to_natural(&kernel), reference(&kernel));
            }
            half_degree += 1;
        }

        let maximal = core::array::from_fn(|degree| {
            if degree & 1 == 0 {
                M31(P - 1)
            } else {
                M31::ZERO
            }
        });
        assert_eq!(even_kernel_to_natural(&maximal), reference(&maximal));

        let mut state = 0x6576_656e_6b65_726eu64;
        let mut sample = 0usize;
        while sample < 256 {
            let kernel = core::array::from_fn(|degree| {
                if degree & 1 == 0 {
                    random_m31(&mut state)
                } else {
                    M31::ZERO
                }
            });
            assert_eq!(even_kernel_to_natural(&kernel), reference(&kernel));
            sample += 1;
        }
    }

    #[test]
    fn fixed_inactive_support_matches_masks_on_every_basis_and_random_input() {
        let masks = atomic_state_only_copy_inactive_row_masks_v3();
        let mut prior = None;
        for &natural in &B_INACTIVE_NATURAL_SUPPORT {
            let natural = usize::from(natural);
            assert!(natural < B_NATURAL_WIDTH);
            if let Some(prior) = prior {
                assert!(prior < natural);
            }
            prior = Some(natural);
        }
        let mut natural = 0usize;
        while natural < B_NATURAL_WIDTH {
            let row = 256 + 2 * natural;
            assert_eq!(
                B_INACTIVE_NATURAL_SUPPORT
                    .binary_search(&(natural as u8))
                    .is_ok(),
                masks[row >> 4] & (1 << (row & 15)) != 0,
                "natural coordinate {natural}"
            );
            natural += 1;
        }
        natural = 0;
        while natural < A_NATURAL_WIDTH {
            let mut basis = [M31::ZERO; A_NATURAL_WIDTH];
            basis[natural] = M31::ONE;
            assert_eq!(
                evaluate_b_inactive(&basis),
                evaluate_b_inactive_reference(&basis),
                "basis coordinate {natural}"
            );
            natural += 1;
        }

        let mut state = 0x696e_6163_7469_7665u64;
        let mut sample = 0usize;
        while sample < 256 {
            let values = core::array::from_fn(|_| random_m31(&mut state));
            assert_eq!(
                evaluate_b_inactive(&values),
                evaluate_b_inactive_reference(&values)
            );
            sample += 1;
        }
    }

    #[test]
    fn grouped_strided_dot_matches_staged_reference_exhaustively_and_at_bounds() {
        const XOR12_SUFFIX_MASK: usize = (1 << 2) | (1 << 1);
        const ACTUAL_MASKS: [usize; 2] = [0, XOR12_SUFFIX_MASK];

        for suffix_xor_mask in ACTUAL_MASKS {
            let mut shift = 0usize;
            while shift < GOOD_A_SIZE {
                // Every pair of natural and suffix basis coordinates, in
                // every QM31 output limb, catches an omitted coordinate, an
                // extra coordinate, or a wrong parity/XOR permutation.
                let mut natural_index = 0usize;
                while natural_index < A_NATURAL_WIDTH {
                    let mut suffix_index = 0usize;
                    while suffix_index < 64 {
                        let mut limb = 0usize;
                        while limb < 4 {
                            let mut natural = [M31::ZERO; A_NATURAL_WIDTH];
                            natural[natural_index] = M31::ONE;
                            let mut suffix_weights = [QM31::ZERO; 64];
                            let mut limbs = [0u32; 4];
                            limbs[limb] = 1;
                            suffix_weights[suffix_index] = qm31(limbs);
                            assert_eq!(
                                evaluate_shifted_in_aligned_block(
                                    &natural,
                                    shift,
                                    &suffix_weights,
                                    suffix_xor_mask,
                                ),
                                evaluate_shifted_in_aligned_block_reference(
                                    &natural,
                                    shift,
                                    &suffix_weights,
                                    suffix_xor_mask,
                                ),
                                "shift {shift}, mask {suffix_xor_mask}, natural {natural_index}, suffix {suffix_index}, limb {limb}"
                            );
                            limb += 1;
                        }
                        suffix_index += 1;
                    }
                    natural_index += 1;
                }

                // Pin the near-modulus single-product case independently of
                // the all-max vector below.
                let support_end = KERNEL_DEGREE + shift + 1;
                let mut index = shift & 1;
                while index < support_end {
                    let mut limb = 0usize;
                    while limb < 4 {
                        let mut natural = [M31::ZERO; A_NATURAL_WIDTH];
                        natural[index] = M31(P - 1);
                        let mut suffix_weights = [QM31::ZERO; 64];
                        let mut limbs = [0u32; 4];
                        limbs[limb] = P - 1;
                        suffix_weights[index ^ suffix_xor_mask] = qm31(limbs);
                        assert_eq!(
                            evaluate_shifted_in_aligned_block(
                                &natural,
                                shift,
                                &suffix_weights,
                                suffix_xor_mask,
                            ),
                            evaluate_shifted_in_aligned_block_reference(
                                &natural,
                                shift,
                                &suffix_weights,
                                suffix_xor_mask,
                            ),
                            "P-1 shift {shift}, mask {suffix_xor_mask}, natural {index}, limb {limb}"
                        );
                        limb += 1;
                    }
                    index += 2;
                }

                // Maximal canonical products exercise the exact four-product
                // u64 bound in every full block and the six-block outer bound.
                let mut maximal_natural = [M31::ZERO; A_NATURAL_WIDTH];
                index = shift & 1;
                while index < support_end {
                    maximal_natural[index] = M31(P - 1);
                    index += 2;
                }
                let maximal_weight = qm31([P - 1; 4]);
                let maximal_suffix = [maximal_weight; 64];
                assert_eq!(
                    evaluate_shifted_in_aligned_block(
                        &maximal_natural,
                        shift,
                        &maximal_suffix,
                        suffix_xor_mask,
                    ),
                    evaluate_shifted_in_aligned_block_reference(
                        &maximal_natural,
                        shift,
                        &maximal_suffix,
                        suffix_xor_mask,
                    ),
                    "maximal shift {shift}, mask {suffix_xor_mask}"
                );

                let mut state =
                    0x6772_6f75_7065_6400u64 ^ ((shift as u64) << 8) ^ suffix_xor_mask as u64;
                let mut sample = 0usize;
                while sample < 128 {
                    let natural = core::array::from_fn(|_| random_m31(&mut state));
                    let suffix_weights = core::array::from_fn(|_| random_qm31(&mut state));
                    assert_eq!(
                        evaluate_shifted_in_aligned_block(
                            &natural,
                            shift,
                            &suffix_weights,
                            suffix_xor_mask,
                        ),
                        evaluate_shifted_in_aligned_block_reference(
                            &natural,
                            shift,
                            &suffix_weights,
                            suffix_xor_mask,
                        ),
                        "random shift {shift}, mask {suffix_xor_mask}, sample {sample}"
                    );
                    sample += 1;
                }
                shift += 1;
            }
        }
    }

    #[test]
    fn paired_base_xor_dot_matches_two_independent_paths() {
        const XOR12_SUFFIX_MASK: usize = (1 << 2) | (1 << 1);
        let mut shift = 0usize;
        while shift < GOOD_A_SIZE {
            let support_end = KERNEL_DEGREE + shift + 1;
            let mut natural_index = shift & 1;
            while natural_index < support_end {
                let mut suffix_index = 0usize;
                while suffix_index < 64 {
                    let mut limb = 0usize;
                    while limb < 4 {
                        let mut natural = [M31::ZERO; A_NATURAL_WIDTH];
                        natural[natural_index] = M31(P - 1);
                        let mut suffix_weights = [QM31::ZERO; 64];
                        let mut limbs = [0u32; 4];
                        limbs[limb] = P - 1;
                        suffix_weights[suffix_index] = qm31(limbs);
                        let pair = evaluate_shifted_in_aligned_block_base_xor(
                            &natural,
                            shift,
                            &suffix_weights,
                            XOR12_SUFFIX_MASK,
                        );
                        assert_eq!(
                            pair,
                            [
                                evaluate_shifted_in_aligned_block(
                                    &natural,
                                    shift,
                                    &suffix_weights,
                                    0,
                                ),
                                evaluate_shifted_in_aligned_block(
                                    &natural,
                                    shift,
                                    &suffix_weights,
                                    XOR12_SUFFIX_MASK,
                                ),
                            ],
                            "shift {shift}, natural {natural_index}, suffix {suffix_index}, limb {limb}"
                        );
                        limb += 1;
                    }
                    suffix_index += 1;
                }
                natural_index += 2;
            }

            let maximal_natural = [M31(P - 1); A_NATURAL_WIDTH];
            let maximal_suffix = [qm31([P - 1; 4]); 64];
            assert_eq!(
                evaluate_shifted_in_aligned_block_base_xor(
                    &maximal_natural,
                    shift,
                    &maximal_suffix,
                    XOR12_SUFFIX_MASK,
                ),
                [
                    evaluate_shifted_in_aligned_block(&maximal_natural, shift, &maximal_suffix, 0,),
                    evaluate_shifted_in_aligned_block(
                        &maximal_natural,
                        shift,
                        &maximal_suffix,
                        XOR12_SUFFIX_MASK,
                    ),
                ],
                "maximal shift {shift}"
            );

            let mut state = 0x7061_6972_646f_7400u64 ^ shift as u64;
            let mut sample = 0usize;
            while sample < 128 {
                let natural = core::array::from_fn(|_| random_m31(&mut state));
                let suffix_weights = core::array::from_fn(|_| random_qm31(&mut state));
                assert_eq!(
                    evaluate_shifted_in_aligned_block_base_xor(
                        &natural,
                        shift,
                        &suffix_weights,
                        XOR12_SUFFIX_MASK,
                    ),
                    [
                        evaluate_shifted_in_aligned_block(&natural, shift, &suffix_weights, 0,),
                        evaluate_shifted_in_aligned_block(
                            &natural,
                            shift,
                            &suffix_weights,
                            XOR12_SUFFIX_MASK,
                        ),
                    ],
                    "random shift {shift}, sample {sample}"
                );
                sample += 1;
            }
            shift += 1;
        }
    }

    #[test]
    fn least_good_accepts_exact_first_good_branch() {
        assert!(selected_is_least_good(0, &[true, true, true]));
        assert!(selected_is_least_good(1, &[false, true, true]));
        assert!(selected_is_least_good(2, &[false, false, true]));
    }

    #[test]
    fn least_good_rejects_nonleast_selected_branch() {
        assert!(!selected_is_least_good(1, &[true, true, true]));
        assert!(!selected_is_least_good(2, &[false, true, true]));
    }

    #[test]
    fn least_good_rejects_bad_selected_branch() {
        assert!(!selected_is_least_good(0, &[false, true, true]));
        assert!(!selected_is_least_good(1, &[false, false, true]));
        assert!(!selected_is_least_good(2, &[false, false, false]));
    }

    #[test]
    fn least_good_rejects_out_of_range_selector() {
        assert!(!selected_is_least_good(3, &[false, false, true]));
        assert!(!selected_is_least_good(u8::MAX, &[true, true, true]));
    }

    #[test]
    fn evaluate_through_selected_is_truth_table_equivalent_to_least_good() {
        let mut bits = 0u8;
        while bits < 8 {
            let evaluations = [bits & 1 != 0, bits & 2 != 0, bits & 4 != 0];
            let mut selected = 0u8;
            while selected < 3 {
                let mut incremental = true;
                let mut candidate = 0usize;
                while candidate <= usize::from(selected) {
                    incremental &= if candidate < usize::from(selected) {
                        !evaluations[candidate]
                    } else {
                        evaluations[candidate]
                    };
                    candidate += 1;
                }
                assert_eq!(
                    incremental,
                    selected_is_least_good(selected, &evaluations),
                    "truth-table mismatch for selector {selected}, bits {bits:03b}"
                );
                selected += 1;
            }
            bits += 1;
        }
    }

    #[test]
    fn natural_shift_trailing_ones_matches_intrinsic_on_full_reachable_domain() {
        let mut index = 0usize;
        while index < A_NATURAL_WIDTH - 1 {
            assert_eq!(
                natural_shift_trailing_ones(index),
                index.trailing_ones() as usize,
                "reachable natural index {index}"
            );
            index += 1;
        }
        let mut odd = 1usize;
        while odd < A_NATURAL_WIDTH {
            assert_eq!(
                usize::from(ODD_NATURAL_TRAILING_ONES[odd >> 1]),
                odd.trailing_ones() as usize,
                "fixed odd natural index {odd}"
            );
            odd += 2;
        }
    }

    #[test]
    fn natural_mul_x_matches_dense_conversion_for_every_reachable_monomial() {
        let mut degree = 0usize;
        while degree < 47 {
            let mut ordinary = [M31::ZERO; A_NATURAL_WIDTH];
            ordinary[degree] = M31::ONE;
            let natural = ordinary_to_natural(&ordinary, A_NATURAL_WIDTH);
            ordinary[degree] = M31::ZERO;
            ordinary[degree + 1] = M31::ONE;
            let expected = ordinary_to_natural(&ordinary, A_NATURAL_WIDTH);
            assert_eq!(
                natural_mul_x_reference(&natural),
                expected,
                "degree {degree}"
            );
            degree += 1;
        }
    }

    #[test]
    fn fixed_support_shift_matches_reference_on_every_reachable_basis_and_random_input() {
        let mut shift = 0usize;
        while shift < GOOD_A_SIZE - 1 {
            let support_end = KERNEL_DEGREE + shift + 1;
            let mut index = shift & 1;
            while index < support_end {
                for coefficient in [M31::ONE, M31(P - 1)] {
                    let mut basis = [M31::ZERO; A_NATURAL_WIDTH];
                    basis[index] = coefficient;
                    assert_eq!(
                        natural_mul_x_fixed_support(&basis, shift),
                        natural_mul_x_reference(&basis),
                        "shift {shift}, basis coordinate {index}"
                    );
                }
                index += 2;
            }

            let mut state = 0x7368_6966_7400_0000u64 ^ shift as u64;
            let mut sample = 0usize;
            while sample < 128 {
                let mut input = [M31::ZERO; A_NATURAL_WIDTH];
                index = shift & 1;
                while index < support_end {
                    input[index] = random_m31(&mut state);
                    index += 2;
                }
                assert_eq!(
                    natural_mul_x_fixed_support(&input, shift),
                    natural_mul_x_reference(&input),
                    "shift {shift}, sample {sample}"
                );
                sample += 1;
            }
            shift += 1;
        }
    }

    #[test]
    fn sparse_shift_chain_matches_all_dense_good_a_and_good_b_directions() {
        let queries = [
            115997, 51779, 92617, 43401, 78758, 66857, 81115, 39787, 112113, 76348, 73402, 59549,
            82876, 101923, 86422, 120558, 124241, 68942,
        ];
        let kernel = query_kernel(&queries).unwrap();
        let shifted_directions = good_shifted_directions(&kernel);
        let mut shift = 0usize;
        while shift < GOOD_B_SIZE {
            assert_eq!(
                shifted_directions[shift],
                ordinary_to_natural(&ordinary_b_direction(&kernel, shift), A_NATURAL_WIDTH),
                "GoodB shift {shift}"
            );
            shift += 1;
        }
        shift = 1;
        while shift <= 11 {
            let mut difference = [M31::ZERO; A_NATURAL_WIDTH];
            let mut index = 0usize;
            while index < A_NATURAL_WIDTH {
                difference[index] =
                    shifted_directions[shift][index].sub(shifted_directions[0][index]);
                index += 1;
            }
            assert_eq!(
                difference,
                ordinary_to_natural(&ordinary_a_direction(&kernel, shift), A_NATURAL_WIDTH),
                "GoodA shift {shift}"
            );
            shift += 1;
        }
    }

    #[test]
    fn xor12_suffix_is_exact_index_permutation() {
        const XOR12_SUFFIX_MASK: usize = (1 << 2) | (1 << 1);
        let mut point = [QM31::ZERO; 10];
        let mut coordinate = 0usize;
        while coordinate < point.len() {
            point[coordinate] = QM31::from_cm31(CM31::from_m31(M31((coordinate + 2) as u32)));
            coordinate += 1;
        }
        let base = mle_six_coordinate_suffix_weights(&point);
        let shifted = mle_six_coordinate_suffix_weights(&xor12_point(&point));
        let mut index = 0usize;
        while index < base.len() {
            assert_eq!(shifted[index], base[index ^ XOR12_SUFFIX_MASK]);
            index += 1;
        }
        assert_eq!(
            mle_three_bit_prefix(&point, 0b111),
            mle_three_bit_prefix(&xor12_point(&point), 0b111)
        );
        assert_eq!(
            mle_three_bit_prefix(&point, 0b010),
            mle_three_bit_prefix(&xor12_point(&point), 0b010)
        );
    }

    #[test]
    fn fraction_free_elimination_rejects_concrete_dependent_rows() {
        let mut a = [[M31::ZERO; GOOD_A_SIZE]; GOOD_A_SIZE];
        let mut b = [[QM31::ZERO; GOOD_B_SIZE]; GOOD_B_SIZE];
        let mut index = 0usize;
        while index < GOOD_A_SIZE {
            a[index][index] = M31::ONE;
            index += 1;
        }
        index = 0;
        while index < GOOD_B_SIZE {
            b[index][index] = QM31::ONE;
            index += 1;
        }
        assert_eq!(assert_matrix_decisions_match(a, b), (true, true));
        a[GOOD_A_SIZE - 1] = a[0];
        b[GOOD_B_SIZE - 1] = b[0];
        assert_eq!(assert_matrix_decisions_match(a, b), (false, false));
    }

    #[test]
    fn fraction_free_fusion_matches_boundaries_pivot_swaps_and_random_matrices() {
        let mut maximal_a = [[M31::ZERO; GOOD_A_SIZE]; GOOD_A_SIZE];
        let mut maximal_b = [[QM31::ZERO; GOOD_B_SIZE]; GOOD_B_SIZE];
        let maximal_qm31 = qm31([P - 1; 4]);
        let mut index = 0usize;
        while index < GOOD_A_SIZE {
            maximal_a[index][index] = M31(P - 1);
            index += 1;
        }
        index = 0;
        while index < GOOD_B_SIZE {
            maximal_b[index][index] = maximal_qm31;
            index += 1;
        }
        assert_eq!(
            assert_matrix_decisions_match(maximal_a, maximal_b),
            (true, true)
        );

        // Moving the first pivot below a zero forces the row-swap path while
        // retaining the same nonzero diagonal product up to sign.
        maximal_a.swap(0, 1);
        maximal_b.swap(0, 1);
        assert_eq!(
            assert_matrix_decisions_match(maximal_a, maximal_b),
            (true, true)
        );

        let mut state = 0x6d61_7472_6978_6666u64;
        let mut sample = 0usize;
        while sample < 64 {
            // Upper-triangular matrices make every below-pivot leading value
            // zero. Nonzero random diagonals make nonsingularity structural.
            let mut a = [[M31::ZERO; GOOD_A_SIZE]; GOOD_A_SIZE];
            let mut b = [[QM31::ZERO; GOOD_B_SIZE]; GOOD_B_SIZE];
            let mut row = 0usize;
            while row < GOOD_A_SIZE {
                let mut entry = row;
                while entry < GOOD_A_SIZE {
                    let value = random_m31(&mut state);
                    a[row][entry] = if entry == row && value.is_zero() {
                        M31::ONE
                    } else {
                        value
                    };
                    entry += 1;
                }
                row += 1;
            }
            row = 0;
            while row < GOOD_B_SIZE {
                let mut entry = row;
                while entry < GOOD_B_SIZE {
                    let value = random_qm31(&mut state);
                    b[row][entry] = if entry == row && value.is_zero() {
                        QM31::ONE
                    } else {
                        value
                    };
                    entry += 1;
                }
                row += 1;
            }
            assert_eq!(assert_matrix_decisions_match(a, b), (true, true));

            let mut swapped_a = a;
            let mut swapped_b = b;
            swapped_a.swap(0, 1);
            swapped_b.swap(0, 1);
            assert_eq!(
                assert_matrix_decisions_match(swapped_a, swapped_b),
                (true, true),
                "pivot-swap sample {sample}"
            );

            let mut singular_a = a;
            let mut singular_b = b;
            singular_a[GOOD_A_SIZE - 1] = singular_a[0];
            singular_b[GOOD_B_SIZE - 1] = singular_b[0];
            assert_eq!(
                assert_matrix_decisions_match(singular_a, singular_b),
                (false, false),
                "dependent-row sample {sample}"
            );
            sample += 1;
        }
    }

    #[test]
    fn fused_full_candidate_decisions_match_reference_on_public_inputs() {
        const FIBER_MASK: u32 = (1 << (C1_DOMAIN_LOG - 2)) - 1;
        let mut state = 0x6361_6e64_6964_6174u64;
        let mut sample = 0usize;
        while sample < 48 {
            let start = random_m31(&mut state).0 & FIBER_MASK;
            let step = (random_m31(&mut state).0 & FIBER_MASK) | 1;
            let queries = core::array::from_fn(|index| {
                start.wrapping_add((index as u32).wrapping_mul(step)) & FIBER_MASK
            });
            let mut sorted = queries;
            sorted.sort_unstable();
            assert!(sorted.windows(2).all(|pair| pair[0] != pair[1]));

            let point = match sample % 12 {
                0 => [QM31::ZERO; 10],
                1 => [QM31::ONE; 10],
                2 => [qm31([P - 1; 4]); 10],
                _ => core::array::from_fn(|_| random_qm31(&mut state)),
            };
            let kernel = query_kernel(&queries).unwrap();
            let reference_kernel = query_kernel_reference(&queries).unwrap();
            assert_eq!(kernel, reference_kernel, "kernel sample {sample}");
            assert_eq!(
                good_matrices(&kernel, &point),
                good_matrices_reference(&reference_kernel, &point),
                "complete matrices sample {sample}"
            );
            assert_eq!(
                candidate_is_good(&point, queries),
                candidate_is_good_reference(&point, queries),
                "candidate sample {sample}"
            );
            sample += 1;
        }
    }
}
