//! Arithmetic-only verifier primitives for the fixed M31 circle-PCS candidate.
//!
//! The formulas and storage order are pinned to Stwo commit
//! `5d10e6b4baa559766e7bbae133b918121211a9c5` and to
//! `docs/stage2-m31-production-plan.md`. This module does not parse proofs,
//! derive transcript challenges, authenticate commitments, or accept a proof.

use alloc::{vec, vec::Vec};

use crate::field::{
    m31_batch_inverse_with, qm31_sum_products3_prepared, PreparedQm31Multiplier, CM31, M31, QM31,
};
use crate::params::{CIRCLE_GEN, CIRCLE_LOG_ORDER};

/// The candidate message has 2^10 coefficients.
pub const FIXED_TRACE_LOG_SIZE: u32 = 10;
/// The rate-1/4 circle codeword has 2^12 symbols.
pub const FIXED_CIRCLE_DOMAIN_LOG_SIZE: u32 = 12;
/// One query names one four-symbol layer-zero fiber.
pub const FIXED_QUERY_LOG_SIZE: u32 = 10;
pub const FIXED_CIRCLE_DOMAIN_SIZE: usize = 1 << FIXED_CIRCLE_DOMAIN_LOG_SIZE;
pub const FIXED_QUERY_FIBER_COUNT: usize = 1 << FIXED_QUERY_LOG_SIZE;
/// Four arity-4 reductions take 1,024 coefficients to four coefficients.
pub const FIXED_ARITY4_ROUNDS: u8 = 4;
/// Later committed line layers are 1, 2, and 3; layer 4 is the final domain.
pub const FIXED_FINAL_LINE_LAYER: u8 = 4;

const CIRCLE_INDEX_MASK: u64 = (1u64 << CIRCLE_LOG_ORDER) - 1;

include!(concat!(env!("OUT_DIR"), "/circle_tables.rs"));

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BaseCirclePoint {
    pub x: M31,
    pub y: M31,
}

impl BaseCirclePoint {
    #[inline(always)]
    fn add(self, rhs: Self) -> Self {
        Self {
            x: self.x.mul(rhs.x).sub(self.y.mul(rhs.y)),
            y: self.x.mul(rhs.y).add(self.y.mul(rhs.x)),
        }
    }

    #[inline(always)]
    fn conjugate(self) -> Self {
        Self {
            x: self.x,
            y: self.y.neg(),
        }
    }
}

/// Materialize the 1,024 fixed layer-zero slot-zero points with two group
/// exponentiations followed by a sequential walk, rather than one
/// exponentiation per queried fiber.
pub fn materialize_fixed_circle_fiber_points() -> Vec<BaseCirclePoint> {
    let half_log_size = FIXED_CIRCLE_DOMAIN_LOG_SIZE - 1;
    let mut point = point_from_group_index(half_odds_initial_index(half_log_size));
    let step = point_from_group_index(half_odds_step_index(half_log_size));
    let mut points = vec![
        BaseCirclePoint {
            x: M31::ONE,
            y: M31::ZERO,
        };
        FIXED_QUERY_FIBER_COUNT
    ];
    for natural_index in 0..FIXED_QUERY_FIBER_COUNT {
        let fiber = bit_reverse_index(natural_index, FIXED_CIRCLE_DOMAIN_LOG_SIZE - 2).unwrap();
        points[fiber] = point;
        point = point.add(step);
    }
    points
}

/// Materialize one complete bit-reversed line domain with two group
/// exponentiations and a sequential walk.
pub fn materialize_line_domain_x_for_log(log_size: u32) -> Result<Vec<M31>, CircleFriError> {
    if log_size + 2 > CIRCLE_LOG_ORDER {
        return Err(CircleFriError::InvalidBitReverseLength);
    }
    let size = 1usize << log_size;
    let mut point = point_from_group_index(half_odds_initial_index(log_size));
    let step = point_from_group_index(half_odds_step_index(log_size));
    let mut values = vec![M31::ZERO; size];
    for natural_index in 0..size {
        let stored_index = bit_reverse_index(natural_index, log_size)?;
        values[stored_index] = point.x;
        point = point.add(step);
    }
    Ok(values)
}

fn selected_sequential_points(
    initial_index: u64,
    step_index: u64,
    natural_and_output: &mut [(usize, usize)],
) -> Vec<BaseCirclePoint> {
    natural_and_output.sort_unstable_by_key(|entry| entry.0);
    let mut outputs = vec![
        BaseCirclePoint {
            x: M31::ONE,
            y: M31::ZERO,
        };
        natural_and_output.len()
    ];
    let mut point = point_from_group_index(initial_index);
    let step = point_from_group_index(step_index);
    let mut natural = 0usize;
    for &(target, output) in natural_and_output.iter() {
        while natural < target {
            point = point.add(step);
            natural += 1;
        }
        outputs[output] = point;
    }
    outputs
}

pub fn materialize_fixed_circle_fiber_points_selected(
    fibers: &[u32],
) -> Result<Vec<BaseCirclePoint>, CircleFriError> {
    let mut selected = Vec::with_capacity(fibers.len());
    for (output, &fiber) in fibers.iter().enumerate() {
        if fiber as usize >= FIXED_QUERY_FIBER_COUNT {
            return Err(CircleFriError::CircleFiberOutOfRange);
        }
        let natural = bit_reverse_index(fiber as usize, FIXED_QUERY_LOG_SIZE)?;
        selected.push((natural, output));
    }
    let half_log_size = FIXED_CIRCLE_DOMAIN_LOG_SIZE - 1;
    Ok(selected_sequential_points(
        half_odds_initial_index(half_log_size),
        half_odds_step_index(half_log_size),
        &mut selected,
    ))
}

pub fn materialize_line_domain_x_selected(
    log_size: u32,
    stored_indices: &[usize],
) -> Result<Vec<M31>, CircleFriError> {
    let size = 1usize << log_size;
    let mut selected = Vec::with_capacity(stored_indices.len());
    for (output, &stored) in stored_indices.iter().enumerate() {
        if stored >= size {
            return Err(CircleFriError::LineIndexOutOfRange);
        }
        selected.push((bit_reverse_index(stored, log_size)?, output));
    }
    Ok(selected_sequential_points(
        half_odds_initial_index(log_size),
        half_odds_step_index(log_size),
        &mut selected,
    )
    .into_iter()
    .map(|point| point.x)
    .collect())
}

/// The three line coordinates used by two consecutive normalized line folds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LineArity4Coordinates {
    pub first_pair_x: M31,
    pub second_pair_x: M31,
    pub second_fold_x: M31,
}

/// Query-local fold coordinates for one circle-FRI opening forest.
///
/// Every vector is ordinal-aligned with the corresponding authenticated
/// index slice supplied to [`derive_query_fold_inverses_for_circle`].  This
/// is the small-binary alternative to linking a complete domain-sized table
/// of public coordinates into a verifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DerivedCircleQueryFoldInverses {
    pub circle: Vec<[M31; 2]>,
    pub later: [Vec<[M31; 3]>; 3],
    pub final_x: Vec<M31>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FoldDenominator {
    CircleY,
    CircleX,
    LineFirstPairX,
    LineSecondPairX,
    LineSecondFoldX,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CircleFriError {
    CircleIndexOutOfRange,
    CircleFiberOutOfRange,
    InvalidLineLayer,
    InvalidLineFoldLayer,
    LineIndexOutOfRange,
    LineFiberOutOfRange,
    QueryOutOfRange,
    InvalidBitReverseLength,
    BitReverseIndexOutOfRange,
    ZeroDenominator(FoldDenominator),
    InvalidInverseBackend,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LaterQueryLocation {
    pub leaf: usize,
    pub slot: u8,
}

/// Fixed query propagation from a layer-zero fiber through the three later
/// committed line layers and into the final 16-point line domain.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FixedQueryPath {
    pub layer0_fiber: usize,
    pub later: [LaterQueryLocation; 3],
    pub final_index: usize,
}

#[inline(always)]
fn point_from_group_index(index: u64) -> BaseCirclePoint {
    let point = CIRCLE_GEN.pow(index & CIRCLE_INDEX_MASK);
    BaseCirclePoint {
        x: point.a,
        y: point.b,
    }
}

/// Materialize selected slot-zero circle-fiber points while sharing the
/// power-of-two group basis across every query.
///
/// Calling `circle_fiber_point_for_domain_log` independently would repeat a
/// full group exponentiation for every query.  Here the fixed initial point
/// and the powers of the fixed step are built once, after which one selected
/// point costs only the set bits of the bit-reversed fiber index.  The result
/// is algebraically identical to `circle_fiber_point_for_domain_log` and is
/// returned in caller order.
pub fn selected_circle_fiber_points_shared(
    domain_log_size: u32,
    fibers: &[u32],
) -> Result<Vec<BaseCirclePoint>, CircleFriError> {
    let query_log_size = domain_log_size
        .checked_sub(2)
        .ok_or(CircleFriError::InvalidBitReverseLength)?;
    if domain_log_size == 0 || domain_log_size > CIRCLE_LOG_ORDER - 1 {
        return Err(CircleFriError::InvalidBitReverseLength);
    }
    let fiber_count = 1usize
        .checked_shl(query_log_size)
        .ok_or(CircleFriError::InvalidBitReverseLength)?;

    if domain_log_size == 19 {
        let mut points = Vec::with_capacity(fibers.len());
        for &fiber in fibers {
            if fiber as usize >= fiber_count {
                return Err(CircleFriError::CircleFiberOutOfRange);
            }
            // `fiber < 2^17` was just checked, so the generic helper's
            // checked shift and identical range test are redundant here.
            let natural = (fiber as usize).reverse_bits() >> (usize::BITS - 17);
            let [low_x, low_y] = RATE512_CIRCLE_LOW8_WINDOW[natural & 0xff];
            let high_index = natural >> 8;
            let mut point = BaseCirclePoint {
                x: M31(low_x),
                y: M31(low_y),
            };
            if high_index != 0 {
                let [high_x, high_y] = RATE512_CIRCLE_HIGH9_WINDOW[high_index];
                point = point.add(BaseCirclePoint {
                    x: M31(high_x),
                    y: M31(high_y),
                });
            }
            points.push(point);
        }
        return Ok(points);
    }

    let initial = point_from_group_index(half_odds_initial_index(domain_log_size - 1));
    let mut step_power = point_from_group_index(half_odds_step_index(domain_log_size - 1));
    let mut step_powers = Vec::with_capacity(query_log_size as usize);
    for _ in 0..query_log_size {
        step_powers.push(step_power);
        step_power = step_power.add(step_power);
    }

    let mut points = Vec::with_capacity(fibers.len());
    for &fiber in fibers {
        if fiber as usize >= fiber_count {
            return Err(CircleFriError::CircleFiberOutOfRange);
        }
        let natural = bit_reverse_index(fiber as usize, query_log_size)?;
        let mut point = initial;
        for (bit, &power) in step_powers.iter().enumerate() {
            if natural & (1usize << bit) != 0 {
                point = point.add(power);
            }
        }
        points.push(point);
    }
    Ok(points)
}

#[inline(always)]
fn double_point(point: BaseCirclePoint) -> BaseCirclePoint {
    // Exact complex squaring.  Specializing the equal operands removes two
    // redundant M31 products from `point.add(point)`:
    // (x + y)(x - y) = x^2 - y^2 and 2xy = xy + xy.
    BaseCirclePoint {
        x: point.x.add(point.y).mul(point.x.sub(point.y)),
        y: point.x.mul(point.y).double(),
    }
}

/// Remove the order-four rotation identifying a symbol's slot within a
/// bit-reversed arity-four line fiber.  Since `G^(2^29) = (0,-1)`, all four
/// cases are swaps/sign changes and require no field multiplication.
#[inline(always)]
fn remove_line_slot_rotation(point: BaseCirclePoint, slot: u32) -> BaseCirclePoint {
    match slot {
        0 => point,
        1 => BaseCirclePoint {
            x: point.x.neg(),
            y: point.y.neg(),
        },
        2 => BaseCirclePoint {
            x: point.y.neg(),
            y: point.x,
        },
        3 => BaseCirclePoint {
            x: point.y,
            y: point.x.neg(),
        },
        _ => unreachable!(),
    }
}

/// Derive the slot-zero points of a parent line layer from an already
/// materialized child layer.  Circle-to-line applies one group doubling;
/// each subsequent arity-four line fold applies two.  The authenticated
/// query forest guarantees that every requested parent has a child; this
/// helper nevertheless checks the relation and fails closed.
fn derive_parent_line_points(
    child_indices: &[u32],
    child_points: &[BaseCirclePoint],
    parent_indices: &[u32],
    doublings: u8,
) -> Result<Vec<BaseCirclePoint>, CircleFriError> {
    if child_indices.len() != child_points.len() {
        return Err(CircleFriError::QueryOutOfRange);
    }
    let mut parents = Vec::with_capacity(parent_indices.len());
    let mut child_ordinal = 0usize;
    for &parent in parent_indices {
        while child_ordinal < child_indices.len() && child_indices[child_ordinal] >> 2 < parent {
            child_ordinal += 1;
        }
        let child_index = *child_indices
            .get(child_ordinal)
            .ok_or(CircleFriError::QueryOutOfRange)?;
        if child_index >> 2 != parent {
            return Err(CircleFriError::QueryOutOfRange);
        }
        debug_assert!(doublings == 1 || doublings == 2);
        let mut point = double_point(child_points[child_ordinal]);
        if doublings == 2 {
            point = double_point(point);
        }
        parents.push(remove_line_slot_rotation(point, child_index & 3));
    }
    Ok(parents)
}

/// Derive exactly the public fold coordinates touched by one authenticated
/// query forest and batch-invert all denominators with one injected inverse.
///
/// This computes the same values as the generated `*_CIRCLE_INV_*`,
/// `*_LINE*_INV`, and `*_FINAL_X` tables.  It changes neither proof bytes nor
/// transcript challenges; it is solely a representation choice for public
/// verifier constants.  `later[0..3]` must be the successive unique parent
/// sets (`q>>2`, `q>>4`, `q>>6`) of `layer0`.
pub fn derive_query_fold_inverses_for_circle(
    domain_log_size: u32,
    layer0: &[u32],
    later: [&[u32]; 3],
    inverse: fn(M31) -> M31,
) -> Result<DerivedCircleQueryFoldInverses, CircleFriError> {
    // Four arity-four rounds must leave a nonempty final line domain.
    if domain_log_size < 8 || domain_log_size > CIRCLE_LOG_ORDER - 1 {
        return Err(CircleFriError::InvalidBitReverseLength);
    }

    let circle_points = selected_circle_fiber_points_shared(domain_log_size, layer0)?;
    let line1_points = derive_parent_line_points(layer0, &circle_points, later[0], 1)?;
    let line2_points = derive_parent_line_points(later[0], &line1_points, later[1], 2)?;
    let line3_points = derive_parent_line_points(later[1], &line2_points, later[2], 2)?;
    let line_points = [&line1_points, &line2_points, &line3_points];

    let denominator_count = layer0
        .len()
        .checked_mul(2)
        .and_then(|count| {
            later.iter().try_fold(count, |count, indices| {
                indices
                    .len()
                    .checked_mul(3)
                    .and_then(|extra| count.checked_add(extra))
            })
        })
        .ok_or(CircleFriError::QueryOutOfRange)?;
    let mut denominators = Vec::with_capacity(denominator_count);
    for point in &circle_points {
        let x = point.x.double();
        let y = point.y.double();
        if x.is_zero() {
            return Err(CircleFriError::ZeroDenominator(FoldDenominator::CircleX));
        }
        if y.is_zero() {
            return Err(CircleFriError::ZeroDenominator(FoldDenominator::CircleY));
        }
        denominators.extend_from_slice(&[x, y]);
    }
    for points in line_points {
        for &point in points {
            // Adding G^(2^29)=(0,-1) maps the first pair point to the
            // second, so its x-coordinate is the first point's y.
            // Only the doubled point's x-coordinate is released here.  On
            // the circle it is 2*x^2-1, so avoid materializing the unused y.
            let coordinates = [
                point.x.double(),
                point.y.double(),
                double_x(point.x).double(),
            ];
            for (coordinate, kind) in coordinates.into_iter().zip([
                FoldDenominator::LineFirstPairX,
                FoldDenominator::LineSecondPairX,
                FoldDenominator::LineSecondFoldX,
            ]) {
                if coordinate.is_zero() {
                    return Err(CircleFriError::ZeroDenominator(kind));
                }
                denominators.push(coordinate);
            }
        }
    }
    debug_assert_eq!(denominators.len(), denominator_count);

    let mut flat_inverses = vec![M31::ZERO; denominators.len()];
    m31_batch_inverse_with(&denominators, &mut flat_inverses, inverse);
    if let (Some(denominator), Some(inverse)) = (denominators.first(), flat_inverses.first()) {
        // Montgomery batch inversion applies one common backend-error factor
        // to every output, so one nonzero product check validates the single
        // injected inversion and consequently the complete batch.
        if denominator.mul(*inverse) != M31::ONE {
            return Err(CircleFriError::InvalidInverseBackend);
        }
    }
    let mut cursor = 0usize;
    let mut circle = Vec::with_capacity(layer0.len());
    for _ in layer0 {
        circle.push([flat_inverses[cursor], flat_inverses[cursor + 1]]);
        cursor += 2;
    }
    let later_inverses: [Vec<[M31; 3]>; 3] = core::array::from_fn(|layer| {
        let mut values = Vec::with_capacity(later[layer].len());
        for _ in later[layer] {
            values.push([
                flat_inverses[cursor],
                flat_inverses[cursor + 1],
                flat_inverses[cursor + 2],
            ]);
            cursor += 3;
        }
        values
    });
    debug_assert_eq!(cursor, flat_inverses.len());

    let final_x = line3_points
        .iter()
        .map(|point| double_x(double_x(point.x)))
        .collect();
    Ok(DerivedCircleQueryFoldInverses {
        circle,
        later: later_inverses,
        final_x,
    })
}

#[inline(always)]
fn half_odds_initial_index(log_size: u32) -> u64 {
    1u64 << (CIRCLE_LOG_ORDER - (log_size + 2))
}

#[inline(always)]
fn half_odds_step_index(log_size: u32) -> u64 {
    1u64 << (CIRCLE_LOG_ORDER - log_size)
}

fn circle_domain_point_for_log(
    log_size: u32,
    stored_index: usize,
) -> Result<BaseCirclePoint, CircleFriError> {
    if log_size == 0 || log_size > CIRCLE_LOG_ORDER - 1 {
        return Err(CircleFriError::InvalidBitReverseLength);
    }
    let natural_index = bit_reverse_index(stored_index, log_size)?;
    let half_size = 1usize << (log_size - 1);
    let half_log_size = log_size - 1;
    let (index, conjugate) = if natural_index < half_size {
        (natural_index, false)
    } else {
        (natural_index - half_size, true)
    };
    let exponent = half_odds_initial_index(half_log_size)
        .wrapping_add(half_odds_step_index(half_log_size).wrapping_mul(index as u64))
        & CIRCLE_INDEX_MASK;
    let point = point_from_group_index(exponent);
    Ok(if conjugate { point.conjugate() } else { point })
}

fn line_domain_x_for_log(log_size: u32, stored_index: usize) -> Result<M31, CircleFriError> {
    if log_size + 2 > CIRCLE_LOG_ORDER {
        return Err(CircleFriError::InvalidBitReverseLength);
    }
    let natural_index = bit_reverse_index(stored_index, log_size)?;
    let exponent = half_odds_initial_index(log_size)
        .wrapping_add(half_odds_step_index(log_size).wrapping_mul(natural_index as u64))
        & CIRCLE_INDEX_MASK;
    Ok(point_from_group_index(exponent).x)
}

fn line_fold_coordinates_for_log(
    log_size: u32,
    fiber: usize,
) -> Result<LineArity4Coordinates, CircleFriError> {
    if log_size < 2 || log_size + 2 > CIRCLE_LOG_ORDER {
        return Err(CircleFriError::InvalidLineFoldLayer);
    }
    let fiber_count = (1usize << log_size) >> 2;
    if fiber >= fiber_count {
        return Err(CircleFriError::LineFiberOutOfRange);
    }
    let first = fiber << 2;
    Ok(LineArity4Coordinates {
        first_pair_x: line_domain_x_for_log(log_size, first)?,
        second_pair_x: line_domain_x_for_log(log_size, first + 2)?,
        second_fold_x: line_domain_x_for_log(log_size - 1, fiber << 1)?,
    })
}

/// Return the point at a bit-reversed symbol index of the fixed 4,096-symbol
/// canonical circle domain.
pub fn fixed_circle_domain_point(index: usize) -> Result<BaseCirclePoint, CircleFriError> {
    if index >= FIXED_CIRCLE_DOMAIN_SIZE {
        return Err(CircleFriError::CircleIndexOutOfRange);
    }
    circle_domain_point_for_log(FIXED_CIRCLE_DOMAIN_LOG_SIZE, index)
}

/// Return slot zero `(x,y)` for one fixed layer-zero four-symbol fiber.
pub fn fixed_circle_fiber_point(fiber: usize) -> Result<BaseCirclePoint, CircleFriError> {
    if fiber >= FIXED_QUERY_FIBER_COUNT {
        return Err(CircleFriError::CircleFiberOutOfRange);
    }
    fixed_circle_domain_point(fiber << 2)
}

/// Slot-zero point for one four-symbol fiber of an explicitly sized circle
/// domain. Used by the rate-1/16 diagnostic while the selected profile keeps
/// the fixed wrappers above.
pub fn circle_fiber_point_for_domain_log(
    domain_log_size: u32,
    fiber: usize,
) -> Result<BaseCirclePoint, CircleFriError> {
    let fiber_count = 1usize
        .checked_shl(
            domain_log_size
                .checked_sub(2)
                .ok_or(CircleFriError::InvalidBitReverseLength)?,
        )
        .ok_or(CircleFriError::InvalidBitReverseLength)?;
    if fiber >= fiber_count {
        return Err(CircleFriError::CircleFiberOutOfRange);
    }
    circle_domain_point_for_log(domain_log_size, fiber << 2)
}

/// Log size of fixed line layer `1..=4`: 10, 8, 6, or 4.
pub fn fixed_line_domain_log_size(layer: u8) -> Result<u32, CircleFriError> {
    if !(1..=FIXED_FINAL_LINE_LAYER).contains(&layer) {
        return Err(CircleFriError::InvalidLineLayer);
    }
    Ok(FIXED_CIRCLE_DOMAIN_LOG_SIZE - 2 * u32::from(layer))
}

pub fn line_domain_log_size_for_circle(
    circle_domain_log_size: u32,
    layer: u8,
) -> Result<u32, CircleFriError> {
    if !(1..=FIXED_FINAL_LINE_LAYER).contains(&layer) {
        return Err(CircleFriError::InvalidLineLayer);
    }
    circle_domain_log_size
        .checked_sub(2 * u32::from(layer))
        .ok_or(CircleFriError::InvalidLineLayer)
}

/// Return the x-coordinate at a bit-reversed symbol index of a fixed later
/// line layer. Layer 4 is the final 16-point evaluation domain.
pub fn fixed_line_domain_x(layer: u8, index: usize) -> Result<M31, CircleFriError> {
    let log_size = fixed_line_domain_log_size(layer)?;
    if index >= 1usize << log_size {
        return Err(CircleFriError::LineIndexOutOfRange);
    }
    line_domain_x_for_log(log_size, index)
}

pub fn line_domain_x_for_circle(
    circle_domain_log_size: u32,
    layer: u8,
    index: usize,
) -> Result<M31, CircleFriError> {
    let log_size = line_domain_log_size_for_circle(circle_domain_log_size, layer)?;
    if index >= 1usize << log_size {
        return Err(CircleFriError::LineIndexOutOfRange);
    }
    line_domain_x_for_log(log_size, index)
}

/// Return the three public denominator coordinates for one arity-4 fold of a
/// committed line layer (`layer=1..=3`).
pub fn fixed_line_fold_coordinates(
    layer: u8,
    fiber: usize,
) -> Result<LineArity4Coordinates, CircleFriError> {
    if !(1..FIXED_FINAL_LINE_LAYER).contains(&layer) {
        return Err(CircleFriError::InvalidLineFoldLayer);
    }
    line_fold_coordinates_for_log(fixed_line_domain_log_size(layer)?, fiber)
}

pub fn line_fold_coordinates_for_circle(
    circle_domain_log_size: u32,
    layer: u8,
    fiber: usize,
) -> Result<LineArity4Coordinates, CircleFriError> {
    if !(1..FIXED_FINAL_LINE_LAYER).contains(&layer) {
        return Err(CircleFriError::InvalidLineFoldLayer);
    }
    line_fold_coordinates_for_log(
        line_domain_log_size_for_circle(circle_domain_log_size, layer)?,
        fiber,
    )
}

/// Checked bit reversal. The same involution converts natural Aspis relation
/// order to Stwo coefficient storage order and converts it back.
pub fn bit_reverse_index(index: usize, log_size: u32) -> Result<usize, CircleFriError> {
    let size = 1usize
        .checked_shl(log_size)
        .ok_or(CircleFriError::InvalidBitReverseLength)?;
    if index >= size {
        return Err(CircleFriError::BitReverseIndexOutOfRange);
    }
    if log_size == 0 {
        Ok(0)
    } else {
        Ok(index.reverse_bits() >> (usize::BITS - log_size))
    }
}

fn bit_reverse_in_place<T>(values: &mut [T]) -> Result<(), CircleFriError> {
    if values.is_empty() || !values.len().is_power_of_two() {
        return Err(CircleFriError::InvalidBitReverseLength);
    }
    let log_size = values.len().ilog2();
    for index in 0..values.len() {
        let reversed = bit_reverse_index(index, log_size)?;
        if reversed > index {
            values.swap(index, reversed);
        }
    }
    Ok(())
}

/// Convert a **later line-layer** natural adjacent-fold vector `R_r` into
/// Stwo `LinePoly` bit-reversed coefficient storage `S_r` without allocating.
///
/// Do not call this on layer-zero circle coefficients: the fixed candidate's
/// `S_0 <- R_0` embedding is byte-direct and deliberately has no extra
/// bit-reversal step.
pub fn later_line_natural_to_stwo_storage<T>(values: &mut [T]) -> Result<(), CircleFriError> {
    bit_reverse_in_place(values)
}

/// Convert a later Stwo `LinePoly` bit-reversed coefficient vector back to
/// natural adjacent-fold order. This is not a layer-zero circle helper.
pub fn later_line_stwo_storage_to_natural<T>(values: &mut [T]) -> Result<(), CircleFriError> {
    bit_reverse_in_place(values)
}

#[inline(always)]
fn inverse_double(value: M31, denominator: FoldDenominator) -> Result<M31, CircleFriError> {
    if value.is_zero() {
        return Err(CircleFriError::ZeroDenominator(denominator));
    }
    Ok(value.double().inv())
}

/// Aspis-normalized circle-to-line fold followed by one line fold. The slots
/// must be `(x,y),(x,-y),(-x,-y),(-x,y)`. This is exactly one quarter of
/// Stwo's two raw inverse-butterfly folds.
pub fn normalized_circle_to_line_arity4(
    values: [QM31; 4],
    alpha: QM31,
    point: BaseCirclePoint,
) -> Result<QM31, CircleFriError> {
    let inv_2y = inverse_double(point.y, FoldDenominator::CircleY)?;
    let inv_2x = inverse_double(point.x, FoldDenominator::CircleX)?;
    Ok(normalized_circle_to_line_arity4_prepared(
        values, alpha, inv_2x, inv_2y,
    ))
}

pub fn normalized_circle_to_line_arity4_prepared(
    values: [QM31; 4],
    alpha: QM31,
    inv_2x: M31,
    inv_2y: M31,
) -> QM31 {
    normalized_circle_to_line_arity4_prepared_with_square(
        values,
        alpha,
        alpha.square(),
        inv_2x,
        inv_2y,
    )
}

pub fn normalized_circle_to_line_arity4_prepared_with_square(
    values: [QM31; 4],
    alpha: QM31,
    alpha_squared: QM31,
    inv_2x: M31,
    inv_2y: M31,
) -> QM31 {
    let positive = values[0]
        .add(values[1])
        .half()
        .add(alpha.mul(values[0].sub(values[1]).mul_m31(inv_2y)));
    let negative = values[2]
        .add(values[3])
        .half()
        .add(alpha.mul(values[2].sub(values[3]).mul_m31(inv_2y.neg())));
    positive
        .add(negative)
        .half()
        .add(alpha_squared.mul(positive.sub(negative).mul_m31(inv_2x)))
}

pub fn normalized_circle_to_line_arity4_prepared_multipliers(
    values: [QM31; 4],
    alpha: PreparedQm31Multiplier,
    alpha_squared: PreparedQm31Multiplier,
    inv_2x: M31,
    inv_2y: M31,
) -> QM31 {
    let positive = values[0]
        .add(values[1])
        .half()
        .add(alpha.mul(values[0].sub(values[1]).mul_m31(inv_2y)));
    let negative = values[2]
        .add(values[3])
        .half()
        .add(alpha.mul(values[2].sub(values[3]).mul_m31(inv_2y.neg())));
    positive
        .add(negative)
        .half()
        .add(alpha_squared.mul(positive.sub(negative).mul_m31(inv_2x)))
}

/// Append-only exact polynomial-basis candidate for the normalized circle
/// arity-four fold.
///
/// This evaluates the identical cubic in `alpha` as the nested butterflies,
/// but accumulates the `alpha`, `alpha^2`, and `alpha^3` terms with one lazy
/// prepared dot.  The second circle pair uses `-inv_2y`, exactly matching
/// [`normalized_circle_to_line_arity4_prepared_multipliers`].
pub fn normalized_circle_to_line_arity4_prepared_polynomial_candidate(
    values: [QM31; 4],
    alpha: PreparedQm31Multiplier,
    alpha_squared: PreparedQm31Multiplier,
    alpha_cubed: PreparedQm31Multiplier,
    inv_2x: M31,
    inv_2y: M31,
) -> QM31 {
    normalized_circle_to_line_arity4_prepared_polynomial_powers(
        values,
        &[alpha, alpha_squared, alpha_cubed],
        inv_2x,
        inv_2y,
    )
}

/// Borrowed-power form of
/// [`normalized_circle_to_line_arity4_prepared_polynomial_candidate`].
/// The arithmetic is identical; callers that reuse one challenge-power table
/// across many queries avoid transporting three 36-byte prepared values into
/// every fold.
pub fn normalized_circle_to_line_arity4_prepared_polynomial_powers(
    values: [QM31; 4],
    alpha_powers: &[PreparedQm31Multiplier; 3],
    inv_2x: M31,
    inv_2y: M31,
) -> QM31 {
    normalized_circle_to_line_arity4_prepared_polynomial_refs(&values, alpha_powers, inv_2x, inv_2y)
}

/// Fully borrowed form of
/// [`normalized_circle_to_line_arity4_prepared_polynomial_powers`].
/// This preserves the same cubic and prepared multipliers while avoiding a
/// 64-byte value-array copy at each query.
pub fn normalized_circle_to_line_arity4_prepared_polynomial_refs(
    values: &[QM31; 4],
    alpha_powers: &[PreparedQm31Multiplier; 3],
    inv_2x: M31,
    inv_2y: M31,
) -> QM31 {
    normalized_arity4_prepared_polynomial_candidate(
        values,
        alpha_powers,
        [inv_2y, inv_2y.neg(), inv_2x],
    )
}

/// Coordinate-resolving wrapper for a fixed layer-zero fiber.
pub fn normalized_circle_to_line_arity4_at_fiber(
    values: [QM31; 4],
    alpha: QM31,
    fiber: usize,
) -> Result<QM31, CircleFriError> {
    normalized_circle_to_line_arity4(values, alpha, fixed_circle_fiber_point(fiber)?)
}

pub fn normalized_circle_to_line_arity4_at_fiber_for_domain_log(
    values: [QM31; 4],
    alpha: QM31,
    domain_log_size: u32,
    fiber: usize,
) -> Result<QM31, CircleFriError> {
    normalized_circle_to_line_arity4(
        values,
        alpha,
        circle_fiber_point_for_domain_log(domain_log_size, fiber)?,
    )
}

/// Two normalized line folds over one consecutive four-symbol Stwo fiber.
/// The second challenge is `alpha^2`, not a fresh challenge.
pub fn normalized_line_arity4(
    values: [QM31; 4],
    alpha: QM31,
    coordinates: LineArity4Coordinates,
) -> Result<QM31, CircleFriError> {
    let inverses = [
        inverse_double(coordinates.first_pair_x, FoldDenominator::LineFirstPairX)?,
        inverse_double(coordinates.second_pair_x, FoldDenominator::LineSecondPairX)?,
        inverse_double(coordinates.second_fold_x, FoldDenominator::LineSecondFoldX)?,
    ];
    Ok(normalized_line_arity4_prepared(values, alpha, inverses))
}

pub fn normalized_line_arity4_prepared(values: [QM31; 4], alpha: QM31, inverses: [M31; 3]) -> QM31 {
    normalized_line_arity4_prepared_with_square(values, alpha, alpha.square(), inverses)
}

pub fn normalized_line_arity4_prepared_with_square(
    values: [QM31; 4],
    alpha: QM31,
    alpha_squared: QM31,
    inverses: [M31; 3],
) -> QM31 {
    let fold = |left: QM31, right: QM31, challenge: QM31, inverse: M31| {
        left.add(right)
            .half()
            .add(challenge.mul(left.sub(right).mul_m31(inverse)))
    };
    let first = fold(values[0], values[1], alpha, inverses[0]);
    let second = fold(values[2], values[3], alpha, inverses[1]);
    fold(first, second, alpha_squared, inverses[2])
}

pub fn normalized_line_arity4_prepared_multipliers(
    values: [QM31; 4],
    alpha: PreparedQm31Multiplier,
    alpha_squared: PreparedQm31Multiplier,
    inverses: [M31; 3],
) -> QM31 {
    let fold = |left: QM31, right: QM31, challenge: PreparedQm31Multiplier, inverse: M31| {
        left.add(right)
            .half()
            .add(challenge.mul(left.sub(right).mul_m31(inverse)))
    };
    let first = fold(values[0], values[1], alpha, inverses[0]);
    let second = fold(values[2], values[3], alpha, inverses[1]);
    fold(first, second, alpha_squared, inverses[2])
}

/// Append-only exact polynomial-basis candidate for a normalized line
/// arity-four fold.
pub fn normalized_line_arity4_prepared_polynomial_candidate(
    values: [QM31; 4],
    alpha: PreparedQm31Multiplier,
    alpha_squared: PreparedQm31Multiplier,
    alpha_cubed: PreparedQm31Multiplier,
    inverses: [M31; 3],
) -> QM31 {
    normalized_line_arity4_prepared_polynomial_powers(
        values,
        &[alpha, alpha_squared, alpha_cubed],
        inverses,
    )
}

/// Borrowed-power form of
/// [`normalized_line_arity4_prepared_polynomial_candidate`].
pub fn normalized_line_arity4_prepared_polynomial_powers(
    values: [QM31; 4],
    alpha_powers: &[PreparedQm31Multiplier; 3],
    inverses: [M31; 3],
) -> QM31 {
    normalized_line_arity4_prepared_polynomial_refs(&values, alpha_powers, inverses)
}

/// Fully borrowed form of
/// [`normalized_line_arity4_prepared_polynomial_powers`].
pub fn normalized_line_arity4_prepared_polynomial_refs(
    values: &[QM31; 4],
    alpha_powers: &[PreparedQm31Multiplier; 3],
    inverses: [M31; 3],
) -> QM31 {
    normalized_arity4_prepared_polynomial_candidate(values, alpha_powers, inverses)
}

#[inline(always)]
fn normalized_arity4_prepared_polynomial_candidate(
    values: &[QM31; 4],
    alpha_powers: &[PreparedQm31Multiplier; 3],
    inverses: [M31; 3],
) -> QM31 {
    // Expanding the two nested folds gives
    // c0 + alpha*c1 + alpha^2*c2 + alpha^3*c3, where all coordinate
    // multipliers remain in M31.  The expansion is an identity over QM31;
    // it changes only the reduction schedule of the three generic products.
    let left_sum = values[0].add(values[1]);
    let right_sum = values[2].add(values[3]);
    let left_scaled_difference = values[0].sub(values[1]).mul_m31(inverses[0]);
    let right_scaled_difference = values[2].sub(values[3]).mul_m31(inverses[1]);
    let constant = left_sum.add(right_sum).half().half();
    let linear = left_scaled_difference.add(right_scaled_difference).half();
    let quadratic = left_sum.sub(right_sum).half().mul_m31(inverses[2]);
    let cubic = left_scaled_difference
        .sub(right_scaled_difference)
        .mul_m31(inverses[2]);
    constant.add(qm31_sum_products3_prepared(
        alpha_powers,
        &[linear, quadratic, cubic],
    ))
}

/// Coordinate-resolving wrapper for one fixed committed line-layer fiber.
pub fn normalized_line_arity4_at_fiber(
    values: [QM31; 4],
    alpha: QM31,
    layer: u8,
    fiber: usize,
) -> Result<QM31, CircleFriError> {
    normalized_line_arity4(values, alpha, fixed_line_fold_coordinates(layer, fiber)?)
}

pub fn normalized_line_arity4_at_fiber_for_domain_log(
    values: [QM31; 4],
    alpha: QM31,
    circle_domain_log_size: u32,
    layer: u8,
    fiber: usize,
) -> Result<QM31, CircleFriError> {
    normalized_line_arity4(
        values,
        alpha,
        line_fold_coordinates_for_circle(circle_domain_log_size, layer, fiber)?,
    )
}

/// Map a fixed layer-zero query fiber through later leaf/slot positions.
pub fn map_fixed_query(query: usize) -> Result<FixedQueryPath, CircleFriError> {
    map_query_for_fiber_count(query, FIXED_QUERY_FIBER_COUNT)
}

pub fn map_query_for_fiber_count(
    query: usize,
    fiber_count: usize,
) -> Result<FixedQueryPath, CircleFriError> {
    if query >= fiber_count {
        return Err(CircleFriError::QueryOutOfRange);
    }
    let mut incoming = query;
    let mut later = [LaterQueryLocation { leaf: 0, slot: 0 }; 3];
    for location in &mut later {
        *location = LaterQueryLocation {
            leaf: incoming >> 2,
            slot: (incoming & 3) as u8,
        };
        incoming >>= 2;
    }
    Ok(FixedQueryPath {
        layer0_fiber: query,
        later,
        final_index: incoming,
    })
}

#[inline(always)]
fn double_x(x: M31) -> M31 {
    x.mul(x).double().sub(M31::ONE)
}

/// Evaluate four natural-order line-tensor coefficients against
/// `[1, x, pi(x), x*pi(x)]`.
pub fn evaluate_final_line_tensor(coefficients: [QM31; 4], x: M31) -> QM31 {
    evaluate_final_line_tensor_ref(&coefficients, x)
}

/// Borrowed-coefficient form of [`evaluate_final_line_tensor`].
pub fn evaluate_final_line_tensor_ref(coefficients: &[QM31; 4], x: M31) -> QM31 {
    let pi_x = double_x(x);
    let x_pi_x = x.mul(pi_x);
    // Each output limb is a three-term M31 dot.  Three maximal products fit
    // in u64, so reduce once per limb instead of once per product.  This is
    // exactly c1*x + c2*pi(x) + c3*x*pi(x), with no polynomial change.
    let dot = |a: M31, b: M31, c: M31| {
        M31::reduce_u64(
            u64::from(a.0) * u64::from(x.0)
                + u64::from(b.0) * u64::from(pi_x.0)
                + u64::from(c.0) * u64::from(x_pi_x.0),
        )
    };
    coefficients[0].add(QM31 {
        c0: CM31::new(
            dot(
                coefficients[1].c0.a,
                coefficients[2].c0.a,
                coefficients[3].c0.a,
            ),
            dot(
                coefficients[1].c0.b,
                coefficients[2].c0.b,
                coefficients[3].c0.b,
            ),
        ),
        c1: CM31::new(
            dot(
                coefficients[1].c1.a,
                coefficients[2].c1.a,
                coefficients[3].c1.a,
            ),
            dot(
                coefficients[1].c1.b,
                coefficients[2].c1.b,
                coefficients[3].c1.b,
            ),
        ),
    })
}

/// Evaluate natural final coefficients at the final domain point selected by
/// a fixed layer-zero query.
pub fn evaluate_final_line_tensor_at_query(
    coefficients: [QM31; 4],
    query: usize,
) -> Result<QM31, CircleFriError> {
    let path = map_fixed_query(query)?;
    let x = fixed_line_domain_x(FIXED_FINAL_LINE_LAYER, path.final_index)?;
    Ok(evaluate_final_line_tensor(coefficients, x))
}

pub fn evaluate_final_line_tensor_at_query_for_domain_log(
    coefficients: [QM31; 4],
    query: usize,
    circle_domain_log_size: u32,
) -> Result<QM31, CircleFriError> {
    let fiber_count = 1usize << (circle_domain_log_size - 2);
    let path = map_query_for_fiber_count(query, fiber_count)?;
    let x = line_domain_x_for_circle(
        circle_domain_log_size,
        FIXED_FINAL_LINE_LAYER,
        path.final_index,
    )?;
    Ok(evaluate_final_line_tensor(coefficients, x))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{CM31, P};
    use alloc::vec::Vec;

    const OFFICIAL_CIRCLE_LOG2_EVALUATION: [u32; 4] =
        [2_147_450_878, 163_843, 32_767, 2_147_319_810];
    const OFFICIAL_LINE_LOG3_X: [u32; 8] = [
        1_179_735_656,
        967_747_991,
        1_241_207_368,
        906_276_279,
        1_415_090_252,
        732_393_395,
        2_112_881_577,
        34_602_070,
    ];

    #[test]
    fn sequential_domain_materialization_matches_random_access_exactly() {
        let fibers = materialize_fixed_circle_fiber_points();
        for (fiber, point) in fibers.into_iter().enumerate() {
            assert_eq!(point, fixed_circle_fiber_point(fiber).unwrap());
        }
        for log_size in 4..=10 {
            let values = materialize_line_domain_x_for_log(log_size).unwrap();
            for (index, value) in values.into_iter().enumerate() {
                assert_eq!(value, line_domain_x_for_log(log_size, index).unwrap());
            }
        }
        let selected_fibers = [0, 1, 17, 511, 1_023, 17];
        let selected = materialize_fixed_circle_fiber_points_selected(&selected_fibers).unwrap();
        for (fiber, point) in selected_fibers.into_iter().zip(selected) {
            assert_eq!(point, fixed_circle_fiber_point(fiber as usize).unwrap());
        }
        let selected_indices = [0usize, 3, 17, 255, 1_023, 17];
        let selected = materialize_line_domain_x_selected(10, &selected_indices).unwrap();
        for (index, value) in selected_indices.into_iter().zip(selected) {
            assert_eq!(value, line_domain_x_for_log(10, index).unwrap());
        }
    }

    #[test]
    fn build_generated_fold_tables_match_random_access_exactly() {
        for fiber in 0..FIXED_QUERY_FIBER_COUNT {
            let point = fixed_circle_fiber_point(fiber).unwrap();
            assert_eq!(M31(FIXED_CIRCLE_INV_2X[fiber]), point.x.double().inv());
            assert_eq!(M31(FIXED_CIRCLE_INV_2Y[fiber]), point.y.double().inv());
        }
        for (layer, table) in [
            (1u8, &FIXED_LINE1_INV[..]),
            (2, &FIXED_LINE2_INV[..]),
            (3, &FIXED_LINE3_INV[..]),
        ] {
            for fiber in 0..table.len() / 3 {
                let coordinates = fixed_line_fold_coordinates(layer, fiber).unwrap();
                assert_eq!(
                    M31(table[3 * fiber]),
                    coordinates.first_pair_x.double().inv()
                );
                assert_eq!(
                    M31(table[3 * fiber + 1]),
                    coordinates.second_pair_x.double().inv()
                );
                assert_eq!(
                    M31(table[3 * fiber + 2]),
                    coordinates.second_fold_x.double().inv()
                );
            }
        }
        for (index, &x) in FIXED_FINAL_X.iter().enumerate() {
            assert_eq!(
                M31(x),
                fixed_line_domain_x(FIXED_FINAL_LINE_LAYER, index).unwrap()
            );
        }

        for fiber in 0..RATE16_CIRCLE_INV_2X.len() {
            let point = circle_fiber_point_for_domain_log(14, fiber).unwrap();
            assert_eq!(M31(RATE16_CIRCLE_INV_2X[fiber]), point.x.double().inv());
            assert_eq!(M31(RATE16_CIRCLE_INV_2Y[fiber]), point.y.double().inv());
        }
        for (layer, table) in [
            (1u8, &RATE16_LINE1_INV[..]),
            (2, &RATE16_LINE2_INV[..]),
            (3, &RATE16_LINE3_INV[..]),
        ] {
            for fiber in 0..table.len() / 3 {
                let coordinates = line_fold_coordinates_for_circle(14, layer, fiber).unwrap();
                assert_eq!(
                    M31(table[3 * fiber]),
                    coordinates.first_pair_x.double().inv()
                );
                assert_eq!(
                    M31(table[3 * fiber + 1]),
                    coordinates.second_pair_x.double().inv()
                );
                assert_eq!(
                    M31(table[3 * fiber + 2]),
                    coordinates.second_fold_x.double().inv()
                );
            }
        }
        for (index, &x) in RATE16_FINAL_X.iter().enumerate() {
            assert_eq!(
                M31(x),
                line_domain_x_for_circle(14, FIXED_FINAL_LINE_LAYER, index).unwrap()
            );
        }

        for fiber in 0..RATE32_CIRCLE_INV_2X.len() {
            let point = circle_fiber_point_for_domain_log(15, fiber).unwrap();
            assert_eq!(M31(RATE32_CIRCLE_INV_2X[fiber]), point.x.double().inv());
            assert_eq!(M31(RATE32_CIRCLE_INV_2Y[fiber]), point.y.double().inv());
        }
        for (layer, table) in [
            (1u8, &RATE32_LINE1_INV[..]),
            (2, &RATE32_LINE2_INV[..]),
            (3, &RATE32_LINE3_INV[..]),
        ] {
            for fiber in 0..table.len() / 3 {
                let coordinates = line_fold_coordinates_for_circle(15, layer, fiber).unwrap();
                assert_eq!(
                    M31(table[3 * fiber]),
                    coordinates.first_pair_x.double().inv()
                );
                assert_eq!(
                    M31(table[3 * fiber + 1]),
                    coordinates.second_pair_x.double().inv()
                );
                assert_eq!(
                    M31(table[3 * fiber + 2]),
                    coordinates.second_fold_x.double().inv()
                );
            }
        }
        for (index, &x) in RATE32_FINAL_X.iter().enumerate() {
            assert_eq!(
                M31(x),
                line_domain_x_for_circle(15, FIXED_FINAL_LINE_LAYER, index).unwrap()
            );
        }

        assert_eq!(RATE512_CIRCLE_INV_2X.len(), 1 << 17);
        assert_eq!(RATE512_CIRCLE_INV_2Y.len(), 1 << 17);
        for fiber in [0usize, 1, 137, 4_096, 65_535, 131_071] {
            let point = circle_fiber_point_for_domain_log(19, fiber).unwrap();
            assert_eq!(M31(RATE512_CIRCLE_INV_2X[fiber]), point.x.double().inv());
            assert_eq!(M31(RATE512_CIRCLE_INV_2Y[fiber]), point.y.double().inv());
        }
        for (layer, table) in [
            (1u8, &RATE512_LINE1_INV[..]),
            (2, &RATE512_LINE2_INV[..]),
            (3, &RATE512_LINE3_INV[..]),
        ] {
            for fiber in [0usize, 1, table.len() / 6, table.len() / 3 - 1] {
                let coordinates = line_fold_coordinates_for_circle(19, layer, fiber).unwrap();
                assert_eq!(
                    M31(table[3 * fiber]),
                    coordinates.first_pair_x.double().inv()
                );
                assert_eq!(
                    M31(table[3 * fiber + 1]),
                    coordinates.second_pair_x.double().inv()
                );
                assert_eq!(
                    M31(table[3 * fiber + 2]),
                    coordinates.second_fold_x.double().inv()
                );
            }
        }
        for index in [
            0usize,
            1,
            RATE512_FINAL_X.len() / 2,
            RATE512_FINAL_X.len() - 1,
        ] {
            assert_eq!(
                M31(RATE512_FINAL_X[index]),
                line_domain_x_for_circle(19, FIXED_FINAL_LINE_LAYER, index).unwrap()
            );
        }
    }

    #[test]
    fn query_local_rate512_coordinates_match_all_six_generated_tables() {
        // Cover every arity-four slot, both index boundaries, and a stable
        // pseudorandom spread through the full 17-bit query space.
        let mut queries = vec![
            0u32, 1, 2, 3, 4, 7, 8, 15, 16, 137, 4_096, 65_535, 131_068, 131_069, 131_070, 131_071,
        ];
        let mut state = 0x243f_6a88_85a3_08d3u64;
        for _ in 0..64 {
            state ^= state >> 12;
            state ^= state << 25;
            state ^= state >> 27;
            queries.push((state as u32) & ((1 << 17) - 1));
        }
        queries.sort_unstable();
        queries.dedup();
        let later: [Vec<u32>; 3] = core::array::from_fn(|layer| {
            let mut indices = queries
                .iter()
                .map(|query| query >> (2 * (layer + 1)))
                .collect::<Vec<_>>();
            indices.dedup();
            indices
        });
        let derived = derive_query_fold_inverses_for_circle(
            19,
            &queries,
            [&later[0], &later[1], &later[2]],
            M31::inv,
        )
        .unwrap();

        for (ordinal, &query) in queries.iter().enumerate() {
            assert_eq!(
                derived.circle[ordinal],
                [
                    M31(RATE512_CIRCLE_INV_2X[query as usize]),
                    M31(RATE512_CIRCLE_INV_2Y[query as usize]),
                ]
            );
        }
        let tables: [&[u32]; 3] = [&RATE512_LINE1_INV, &RATE512_LINE2_INV, &RATE512_LINE3_INV];
        for layer in 0..3 {
            for (ordinal, &index) in later[layer].iter().enumerate() {
                let offset = index as usize * 3;
                assert_eq!(
                    derived.later[layer][ordinal],
                    [
                        M31(tables[layer][offset]),
                        M31(tables[layer][offset + 1]),
                        M31(tables[layer][offset + 2]),
                    ]
                );
            }
        }
        for (ordinal, &index) in later[2].iter().enumerate() {
            assert_eq!(
                derived.final_x[ordinal],
                M31(RATE512_FINAL_X[index as usize])
            );
        }
    }

    #[test]
    fn rate512_line_precomputes_match_the_formula_exhaustively() {
        assert_eq!(RATE512_LINE1_INV.len() % 3, 0);
        assert_eq!(RATE512_LINE2_INV.len() % 3, 0);
        assert_eq!(RATE512_LINE3_INV.len() % 3, 0);
        assert_eq!(RATE512_LINE3_INV.len() / 3, RATE512_FINAL_X.len());
        for (layer, table) in [
            (1u8, &RATE512_LINE1_INV[..]),
            (2, &RATE512_LINE2_INV[..]),
            (3, &RATE512_LINE3_INV[..]),
        ] {
            for index in 0..table.len() / 3 {
                let coordinates = line_fold_coordinates_for_circle(19, layer, index).unwrap();
                let inverses = [
                    M31(table[3 * index]),
                    M31(table[3 * index + 1]),
                    M31(table[3 * index + 2]),
                ];
                for (coordinate, inverse) in [
                    coordinates.first_pair_x,
                    coordinates.second_pair_x,
                    coordinates.second_fold_x,
                ]
                .into_iter()
                .zip(inverses)
                {
                    assert_eq!(
                        coordinate.double().mul(inverse),
                        M31::ONE,
                        "line{layer} inverse at fiber {index}",
                    );
                }
                assert_eq!(
                    inverses,
                    [
                        coordinates.first_pair_x.double().inv(),
                        coordinates.second_pair_x.double().inv(),
                        coordinates.second_fold_x.double().inv(),
                    ],
                    "line{layer} index {index}",
                );
            }
        }
        for index in 0..RATE512_FINAL_X.len() {
            assert_eq!(
                M31(RATE512_FINAL_X[index]),
                line_domain_x_for_circle(19, FIXED_FINAL_LINE_LAYER, index).unwrap(),
                "final index {index}",
            );
        }
    }

    #[test]
    fn rate512_split_window_matches_every_circle_fiber_point() {
        let query_log_size = 17u32;
        let fibers = (0..1usize << query_log_size)
            .map(|natural| bit_reverse_index(natural, query_log_size).unwrap() as u32)
            .collect::<Vec<_>>();
        let actual = selected_circle_fiber_points_shared(19, &fibers).unwrap();
        let mut expected = point_from_group_index(half_odds_initial_index(18));
        let step = point_from_group_index(half_odds_step_index(18));
        for (natural, point) in actual.into_iter().enumerate() {
            let fiber = fibers[natural] as usize;
            assert_eq!(point, expected, "natural index {natural}");
            assert_eq!(
                point.x.double().mul(M31(RATE512_CIRCLE_INV_2X[fiber])),
                M31::ONE,
                "circle x inverse at stored fiber {fiber}",
            );
            assert_eq!(
                point.y.double().mul(M31(RATE512_CIRCLE_INV_2Y[fiber])),
                M31::ONE,
                "circle y inverse at stored fiber {fiber}",
            );
            assert_eq!(
                double_point(point),
                point.add(point),
                "doubling parity at natural index {natural}",
            );
            expected = expected.add(step);
        }
    }

    #[test]
    fn query_local_coordinate_derivation_rejects_a_non_parent_forest() {
        assert_eq!(
            derive_query_fold_inverses_for_circle(19, &[7], [&[2], &[0], &[0]], M31::inv),
            Err(CircleFriError::QueryOutOfRange)
        );
        assert_eq!(
            derive_query_fold_inverses_for_circle(19, &[7], [&[1], &[0], &[1]], M31::inv),
            Err(CircleFriError::QueryOutOfRange)
        );
        assert_eq!(
            derive_query_fold_inverses_for_circle(19, &[7], [&[1], &[1], &[0]], M31::inv),
            Err(CircleFriError::QueryOutOfRange)
        );
    }

    #[test]
    fn query_local_coordinate_derivation_rejects_faulty_inverse_backends() {
        fn zero_inverse(_: M31) -> M31 {
            M31::ZERO
        }

        fn wrong_nonzero_inverse(value: M31) -> M31 {
            value.inv().add(M31::ONE)
        }

        let queries = [0u32];
        let layer1 = [0u32];
        let layer2 = [0u32];
        let layer3 = [0u32];
        let later = [&layer1[..], &layer2[..], &layer3[..]];
        assert_eq!(
            derive_query_fold_inverses_for_circle(19, &queries, later, zero_inverse),
            Err(CircleFriError::InvalidInverseBackend)
        );
        assert_eq!(
            derive_query_fold_inverses_for_circle(19, &queries, later, wrong_nonzero_inverse),
            Err(CircleFriError::InvalidInverseBackend)
        );
        assert!(derive_query_fold_inverses_for_circle(19, &queries, later, M31::inv).is_ok());
    }
    const OFFICIAL_LINE_EVALUATIONS: [[u32; 4]; 8] = [
        [2_050_460_445, 1_621_393_214, 987_369_631, 182_601_986],
        [881_735_737, 1_347_325_488, 1_457_813_322, 1_358_185_272],
        [2_144_020_592, 1_959_998_540, 1_822_144_424, 1_397_437_748],
        [1_372_394_555, 1_520_680_523, 35_373_177, 1_364_737_696],
        [1_407_536_563, 1_500_747_131, 2_031_962_867, 1_578_661_056],
        [1_057_190_745, 1_409_218_935, 1_933_881_962, 1_080_251_264],
        [1_058_194_856, 282_106_502, 883_008_744, 252_189_861],
        [765_884_750, 1_095_947_918, 1_585_864_132, 1_375_869_737],
    ];
    const OFFICIAL_LINE_FOLD2: [[u32; 4]; 2] = [
        [1_791_673_657, 156_816_650, 2_000_504_088, 2_112_974_310],
        [153_418_649, 1_165_133_557, 1_613_259_006, 1_640_413_761],
    ];

    #[derive(Clone, Copy)]
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 >> 12;
            self.0 ^= self.0 << 25;
            self.0 ^= self.0 >> 27;
            self.0 = self.0.wrapping_mul(0x2545_f491_4f6c_dd1d);
            self.0
        }

        fn m31(&mut self) -> M31 {
            M31((self.next() as u32) % P)
        }

        fn qm31(&mut self) -> QM31 {
            QM31 {
                c0: CM31::new(self.m31(), self.m31()),
                c1: CM31::new(self.m31(), self.m31()),
            }
        }
    }

    fn q(value: [u32; 4]) -> QM31 {
        QM31 {
            c0: CM31::new(M31(value[0]), M31(value[1])),
            c1: CM31::new(M31(value[2]), M31(value[3])),
        }
    }

    fn coordinates(value: QM31) -> [u32; 4] {
        [value.c0.a.0, value.c0.b.0, value.c1.a.0, value.c1.b.0]
    }

    #[test]
    fn polynomial_basis_fold_candidates_match_nested_folds_at_random_points() {
        let mut rng = Rng(0x504f_4c59_464f_4c44);
        for case in 0..512 {
            let values = core::array::from_fn(|_| rng.qm31());
            let alpha = rng.qm31();
            let alpha_squared_value = alpha.square();
            let alpha_cubed_value = alpha_squared_value.mul(alpha);
            let alpha = PreparedQm31Multiplier::new(alpha);
            let alpha_squared = PreparedQm31Multiplier::new(alpha_squared_value);
            let alpha_cubed = PreparedQm31Multiplier::new(alpha_cubed_value);
            let alpha_powers = [alpha, alpha_squared, alpha_cubed];
            let inverses = [rng.m31(), rng.m31(), rng.m31()];
            let line = normalized_line_arity4_prepared_polynomial_candidate(
                values,
                alpha,
                alpha_squared,
                alpha_cubed,
                inverses,
            );
            assert_eq!(
                line,
                normalized_line_arity4_prepared_multipliers(values, alpha, alpha_squared, inverses,),
                "line case {case}",
            );
            assert_eq!(
                normalized_line_arity4_prepared_polynomial_powers(values, &alpha_powers, inverses,),
                line,
                "borrowed line powers case {case}",
            );
            assert_eq!(
                normalized_line_arity4_prepared_polynomial_refs(&values, &alpha_powers, inverses,),
                line,
                "borrowed line values case {case}",
            );
            let circle = normalized_circle_to_line_arity4_prepared_polynomial_candidate(
                values,
                alpha,
                alpha_squared,
                alpha_cubed,
                inverses[2],
                inverses[0],
            );
            assert_eq!(
                circle,
                normalized_circle_to_line_arity4_prepared_multipliers(
                    values,
                    alpha,
                    alpha_squared,
                    inverses[2],
                    inverses[0],
                ),
                "circle case {case}",
            );
            assert_eq!(
                normalized_circle_to_line_arity4_prepared_polynomial_powers(
                    values,
                    &alpha_powers,
                    inverses[2],
                    inverses[0],
                ),
                circle,
                "borrowed circle powers case {case}",
            );
            assert_eq!(
                normalized_circle_to_line_arity4_prepared_polynomial_refs(
                    &values,
                    &alpha_powers,
                    inverses[2],
                    inverses[0],
                ),
                circle,
                "borrowed circle values case {case}",
            );
            assert_eq!(
                evaluate_final_line_tensor_ref(&values, inverses[0]),
                evaluate_final_line_tensor(values, inverses[0]),
                "borrowed final tensor case {case}",
            );
        }
    }

    #[test]
    fn borrowed_fold_inputs_match_value_wrappers_at_field_extremes() {
        let maximal = QM31 {
            c0: CM31::new(M31(P - 1), M31(P - 1)),
            c1: CM31::new(M31(P - 1), M31(P - 1)),
        };
        let alternating = QM31 {
            c0: CM31::new(M31(P - 1), M31::ZERO),
            c1: CM31::new(M31::ZERO, M31(P - 1)),
        };
        let corpus = [QM31::ZERO, QM31::ONE, maximal, alternating];
        let inverse_corpus = [M31::ZERO, M31::ONE, M31(P - 1)];

        for case in 0..corpus.len() {
            let values = core::array::from_fn(|slot| corpus[(slot + case) % corpus.len()]);
            let alpha_value = corpus[case];
            let alpha_squared = alpha_value.square();
            let alpha_powers = [
                PreparedQm31Multiplier::new(alpha_value),
                PreparedQm31Multiplier::new(alpha_squared),
                PreparedQm31Multiplier::new(alpha_squared.mul(alpha_value)),
            ];
            let inverses =
                core::array::from_fn(|index| inverse_corpus[(index + case) % inverse_corpus.len()]);
            assert_eq!(
                normalized_line_arity4_prepared_polynomial_refs(&values, &alpha_powers, inverses,),
                normalized_line_arity4_prepared_polynomial_powers(values, &alpha_powers, inverses,),
                "extreme line case {case}",
            );
            assert_eq!(
                normalized_circle_to_line_arity4_prepared_polynomial_refs(
                    &values,
                    &alpha_powers,
                    inverses[2],
                    inverses[0],
                ),
                normalized_circle_to_line_arity4_prepared_polynomial_powers(
                    values,
                    &alpha_powers,
                    inverses[2],
                    inverses[0],
                ),
                "extreme circle case {case}",
            );
            assert_eq!(
                evaluate_final_line_tensor_ref(&values, inverses[1]),
                evaluate_final_line_tensor(values, inverses[1]),
                "extreme final tensor case {case}",
            );
        }
    }

    fn raw_circle_fold(values: [QM31; 4], alpha: QM31, point: BaseCirclePoint) -> QM31 {
        let inv_y = point.y.inv();
        let positive = values[0]
            .add(values[1])
            .add(alpha.mul(values[0].sub(values[1]).mul_m31(inv_y)));
        let negative = values[2]
            .add(values[3])
            .add(alpha.mul(values[2].sub(values[3]).mul_m31(inv_y.neg())));
        positive.add(negative).add(
            alpha
                .square()
                .mul(positive.sub(negative).mul_m31(point.x.inv())),
        )
    }

    fn raw_line_fold(values: [QM31; 4], alpha: QM31, coordinates: LineArity4Coordinates) -> QM31 {
        let first = values[0].add(values[1]).add(
            alpha.mul(
                values[0]
                    .sub(values[1])
                    .mul_m31(coordinates.first_pair_x.inv()),
            ),
        );
        let second = values[2].add(values[3]).add(
            alpha.mul(
                values[2]
                    .sub(values[3])
                    .mul_m31(coordinates.second_pair_x.inv()),
            ),
        );
        first.add(second).add(
            alpha
                .square()
                .mul(first.sub(second).mul_m31(coordinates.second_fold_x.inv())),
        )
    }

    fn evaluate_stwo_storage4(coefficients: [QM31; 4], x: M31) -> QM31 {
        // Independent recursive LinePoly evaluation: split the bit-reversed
        // storage vector in half and evaluate both halves at pi(x).
        let pi_x = double_x(x);
        let left = coefficients[0].add(coefficients[1].mul_m31(pi_x));
        let right = coefficients[2].add(coefficients[3].mul_m31(pi_x));
        left.add(right.mul_m31(x))
    }

    #[test]
    fn official_circle_and_line_domain_anchors_match() {
        // Stwo's circle FFT coefficient slice is already ordered by the
        // tensor basis [1,y,x,xy] at log size two. Unlike each later
        // `LinePoly`, S_0 is not bit-reversed again before circle encoding.
        let tensor_coefficients = [M31(1), M31(3), M31(2), M31(4)];
        for (index, expected) in OFFICIAL_CIRCLE_LOG2_EVALUATION.iter().enumerate() {
            let point = circle_domain_point_for_log(2, index).unwrap();
            let actual = tensor_coefficients[0]
                .add(tensor_coefficients[1].mul(point.y))
                .add(tensor_coefficients[2].mul(point.x))
                .add(tensor_coefficients[3].mul(point.x.mul(point.y)));
            assert_eq!(actual.0, *expected);
        }

        for (index, expected) in OFFICIAL_LINE_LOG3_X.iter().enumerate() {
            assert_eq!(line_domain_x_for_log(3, index).unwrap().0, *expected);
        }
    }

    #[test]
    fn official_raw_line_fold_is_four_times_normalized() {
        let alpha = q([127, 131, 137, 139]);
        for fiber in 0..2 {
            let values =
                core::array::from_fn(|slot| q(OFFICIAL_LINE_EVALUATIONS[(fiber << 2) + slot]));
            let normalized = normalized_line_arity4(
                values,
                alpha,
                line_fold_coordinates_for_log(3, fiber).unwrap(),
            )
            .unwrap();
            assert_eq!(
                coordinates(normalized.mul_m31(M31(4))),
                OFFICIAL_LINE_FOLD2[fiber]
            );
        }
    }

    #[test]
    fn fixed_circle_domain_and_slot_geometry_are_exhaustive() {
        let half_log = FIXED_CIRCLE_DOMAIN_LOG_SIZE - 1;
        let mut point = point_from_group_index(half_odds_initial_index(half_log));
        let step = point_from_group_index(half_odds_step_index(half_log));
        let half = FIXED_CIRCLE_DOMAIN_SIZE / 2;
        for natural_index in 0..half {
            let stored = bit_reverse_index(natural_index, FIXED_CIRCLE_DOMAIN_LOG_SIZE).unwrap();
            let stored_conjugate =
                bit_reverse_index(natural_index + half, FIXED_CIRCLE_DOMAIN_LOG_SIZE).unwrap();
            assert_eq!(fixed_circle_domain_point(stored).unwrap(), point);
            assert_eq!(
                fixed_circle_domain_point(stored_conjugate).unwrap(),
                point.conjugate()
            );
            point = point.add(step);
        }

        for fiber in 0..FIXED_QUERY_FIBER_COUNT {
            let p = fixed_circle_fiber_point(fiber).unwrap();
            let slots: [BaseCirclePoint; 4] = core::array::from_fn(|slot| {
                fixed_circle_domain_point((fiber << 2) + slot).unwrap()
            });
            assert_eq!(slots[0], p);
            assert_eq!(slots[1], p.conjugate());
            assert_eq!(
                slots[2],
                BaseCirclePoint {
                    x: p.x.neg(),
                    y: p.y.neg()
                }
            );
            assert_eq!(
                slots[3],
                BaseCirclePoint {
                    x: p.x.neg(),
                    y: p.y
                }
            );
            assert_eq!(p.x.mul(p.x).add(p.y.mul(p.y)), M31::ONE);
        }
    }

    #[test]
    fn fixed_line_domains_and_fold_coordinates_are_exhaustive() {
        for layer in 1..=FIXED_FINAL_LINE_LAYER {
            let log_size = fixed_line_domain_log_size(layer).unwrap();
            let size = 1usize << log_size;
            let mut point = point_from_group_index(half_odds_initial_index(log_size));
            let step = point_from_group_index(half_odds_step_index(log_size));
            for natural_index in 0..size {
                let stored = bit_reverse_index(natural_index, log_size).unwrap();
                assert_eq!(fixed_line_domain_x(layer, stored).unwrap(), point.x);
                point = point.add(step);
            }
        }

        for layer in 1..FIXED_FINAL_LINE_LAYER {
            let log_size = fixed_line_domain_log_size(layer).unwrap();
            for fiber in 0..(1usize << (log_size - 2)) {
                let coordinates = fixed_line_fold_coordinates(layer, fiber).unwrap();
                assert_eq!(
                    coordinates.first_pair_x,
                    fixed_line_domain_x(layer, fiber << 2).unwrap()
                );
                assert_eq!(
                    coordinates.second_pair_x,
                    fixed_line_domain_x(layer, (fiber << 2) + 2).unwrap()
                );
                assert!(!coordinates.first_pair_x.is_zero());
                assert!(!coordinates.second_pair_x.is_zero());
                assert!(!coordinates.second_fold_x.is_zero());
            }
        }
    }

    #[test]
    fn normalized_folds_match_independent_raw_stwo_factor_four() {
        let mut rng = Rng(0x4349_5243_4c45_4652);
        for fiber in 0..FIXED_QUERY_FIBER_COUNT {
            let values = core::array::from_fn(|_| rng.qm31());
            let alpha = rng.qm31();
            let point = fixed_circle_fiber_point(fiber).unwrap();
            let normalized = normalized_circle_to_line_arity4(values, alpha, point).unwrap();
            assert_eq!(
                normalized.mul_m31(M31(4)),
                raw_circle_fold(values, alpha, point)
            );
            assert_eq!(
                normalized,
                normalized_circle_to_line_arity4_at_fiber(values, alpha, fiber).unwrap()
            );
        }

        for layer in 1..FIXED_FINAL_LINE_LAYER {
            let log_size = fixed_line_domain_log_size(layer).unwrap();
            for fiber in 0..(1usize << (log_size - 2)) {
                let values = core::array::from_fn(|_| rng.qm31());
                let alpha = rng.qm31();
                let coordinates = fixed_line_fold_coordinates(layer, fiber).unwrap();
                let normalized = normalized_line_arity4(values, alpha, coordinates).unwrap();
                assert_eq!(
                    normalized.mul_m31(M31(4)),
                    raw_line_fold(values, alpha, coordinates)
                );
                assert_eq!(
                    normalized,
                    normalized_line_arity4_at_fiber(values, alpha, layer, fiber).unwrap()
                );
            }
        }
    }

    #[test]
    fn storage_bridge_and_query_mapping_are_exhaustive() {
        for log_size in 0..=FIXED_CIRCLE_DOMAIN_LOG_SIZE {
            let len = 1usize << log_size;
            let mut values = (0..len).collect::<Vec<_>>();
            let original = values.clone();
            later_line_natural_to_stwo_storage(&mut values).unwrap();
            for (stored, value) in values.iter().enumerate() {
                assert_eq!(*value, bit_reverse_index(stored, log_size).unwrap());
            }
            later_line_stwo_storage_to_natural(&mut values).unwrap();
            assert_eq!(values, original);
        }

        for query in 0..FIXED_QUERY_FIBER_COUNT {
            let path = map_fixed_query(query).unwrap();
            assert_eq!(path.layer0_fiber, query);
            assert_eq!(path.later[0].leaf, query >> 2);
            assert_eq!(path.later[0].slot, (query & 3) as u8);
            assert_eq!(path.later[1].leaf, query >> 4);
            assert_eq!(path.later[1].slot, ((query >> 2) & 3) as u8);
            assert_eq!(path.later[2].leaf, query >> 6);
            assert_eq!(path.later[2].slot, ((query >> 4) & 3) as u8);
            assert_eq!(path.final_index, query >> 6);
        }
    }

    #[test]
    fn final_tensor_matches_stwo_storage_evaluation_for_every_query() {
        let mut rng = Rng(0x4649_4e41_4c54_454e);
        for query in 0..FIXED_QUERY_FIBER_COUNT {
            let natural = core::array::from_fn(|_| rng.qm31());
            let path = map_fixed_query(query).unwrap();
            let x = fixed_line_domain_x(FIXED_FINAL_LINE_LAYER, path.final_index).unwrap();
            let mut stored = natural;
            later_line_natural_to_stwo_storage(&mut stored).unwrap();
            let expected = evaluate_stwo_storage4(stored, x);
            assert_eq!(evaluate_final_line_tensor(natural, x), expected);
            assert_eq!(
                evaluate_final_line_tensor_at_query(natural, query).unwrap(),
                expected
            );
        }
    }

    #[test]
    fn public_bounds_and_zero_denominators_are_explicit_errors() {
        assert_eq!(
            fixed_circle_domain_point(FIXED_CIRCLE_DOMAIN_SIZE),
            Err(CircleFriError::CircleIndexOutOfRange)
        );
        assert_eq!(
            fixed_circle_fiber_point(FIXED_QUERY_FIBER_COUNT),
            Err(CircleFriError::CircleFiberOutOfRange)
        );
        assert_eq!(
            fixed_line_domain_x(0, 0),
            Err(CircleFriError::InvalidLineLayer)
        );
        assert_eq!(
            fixed_line_domain_x(1, 1 << 10),
            Err(CircleFriError::LineIndexOutOfRange)
        );
        assert_eq!(
            fixed_line_fold_coordinates(FIXED_FINAL_LINE_LAYER, 0),
            Err(CircleFriError::InvalidLineFoldLayer)
        );
        assert_eq!(
            map_fixed_query(FIXED_QUERY_FIBER_COUNT),
            Err(CircleFriError::QueryOutOfRange)
        );
        assert_eq!(
            bit_reverse_index(4, 2),
            Err(CircleFriError::BitReverseIndexOutOfRange)
        );
        assert_eq!(
            later_line_natural_to_stwo_storage::<u8>(&mut []),
            Err(CircleFriError::InvalidBitReverseLength)
        );
        assert_eq!(
            later_line_natural_to_stwo_storage(&mut [0u8; 3]),
            Err(CircleFriError::InvalidBitReverseLength)
        );

        let values = [QM31::ZERO; 4];
        assert_eq!(
            normalized_circle_to_line_arity4(
                values,
                QM31::ONE,
                BaseCirclePoint {
                    x: M31::ONE,
                    y: M31::ZERO
                }
            ),
            Err(CircleFriError::ZeroDenominator(FoldDenominator::CircleY))
        );
        assert_eq!(
            normalized_circle_to_line_arity4(
                values,
                QM31::ONE,
                BaseCirclePoint {
                    x: M31::ZERO,
                    y: M31::ONE
                }
            ),
            Err(CircleFriError::ZeroDenominator(FoldDenominator::CircleX))
        );

        let valid = M31::ONE;
        for (coordinates, expected) in [
            (
                LineArity4Coordinates {
                    first_pair_x: M31::ZERO,
                    second_pair_x: valid,
                    second_fold_x: valid,
                },
                FoldDenominator::LineFirstPairX,
            ),
            (
                LineArity4Coordinates {
                    first_pair_x: valid,
                    second_pair_x: M31::ZERO,
                    second_fold_x: valid,
                },
                FoldDenominator::LineSecondPairX,
            ),
            (
                LineArity4Coordinates {
                    first_pair_x: valid,
                    second_pair_x: valid,
                    second_fold_x: M31::ZERO,
                },
                FoldDenominator::LineSecondFoldX,
            ),
        ] {
            assert_eq!(
                normalized_line_arity4(values, QM31::ONE, coordinates),
                Err(CircleFriError::ZeroDenominator(expected))
            );
        }
    }
}
