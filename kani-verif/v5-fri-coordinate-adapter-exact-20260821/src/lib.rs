//! Extraction-friendly spelling of the released V5 FRI coordinate helper.
//!
//! The reference below is the Rust source that the recorded Charon/Aeneas
//! extraction adapter expresses: domain 19, the `M31::inv` backend, explicit
//! later-layer slices, and `while` loops in place of unsupported iterators and
//! a mutable `array::from_fn` closure. It is not linked into the verifier.

use aspis_core::circle_fri::{
    BaseCirclePoint, CircleFriError, DerivedCircleQueryFoldInverses, FoldDenominator,
    RATE512_CIRCLE_HIGH9_WINDOW, RATE512_CIRCLE_LOW8_WINDOW,
};
use aspis_core::field::M31;

#[inline(always)]
fn point_add(left: BaseCirclePoint, right: BaseCirclePoint) -> BaseCirclePoint {
    BaseCirclePoint {
        x: left.x.mul(right.x).sub(left.y.mul(right.y)),
        y: left.x.mul(right.y).add(left.y.mul(right.x)),
    }
}

#[inline(always)]
fn double_point(point: BaseCirclePoint) -> BaseCirclePoint {
    BaseCirclePoint {
        x: point.x.add(point.y).mul(point.x.sub(point.y)),
        y: point.x.mul(point.y).double(),
    }
}

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

#[inline(always)]
fn double_x(x: M31) -> M31 {
    x.mul(x).double().sub(M31::ONE)
}

/// Adapter spelling of `selected_circle_fiber_points_shared`.
pub fn adapter_selected_circle_fiber_points_shared(
    domain_log_size: u32,
    fibers: &[u32],
) -> (Vec<BaseCirclePoint>, bool) {
    let fiber_count = 1usize << 17;
    let mut valid = domain_log_size == 19;
    let mut validation_ordinal = 0usize;
    while validation_ordinal < fibers.len() {
        if fibers[validation_ordinal] as usize >= fiber_count {
            valid = false;
        }
        validation_ordinal += 1;
    }
    let mut points = Vec::with_capacity(fibers.len());
    let mut fiber_ordinal = 0usize;
    while fiber_ordinal < fibers.len() {
        let fiber = fibers[fiber_ordinal];
        let natural = (fiber as usize).reverse_bits() >> (usize::BITS - 17);
        let [low_x, low_y] = RATE512_CIRCLE_LOW8_WINDOW[natural & 0xff];
        let high_index = natural >> 8;
        let mut point = BaseCirclePoint {
            x: M31(low_x),
            y: M31(low_y),
        };
        if high_index != 0 {
            let [high_x, high_y] = RATE512_CIRCLE_HIGH9_WINDOW[high_index];
            point = point_add(
                point,
                BaseCirclePoint {
                    x: M31(high_x),
                    y: M31(high_y),
                },
            );
        }
        points.push(point);
        fiber_ordinal += 1;
    }
    (points, valid)
}

fn adapter_derive_parent_line_points(
    child_indices: &[u32],
    child_points: &[BaseCirclePoint],
    parent_indices: &[u32],
    doublings: u8,
) -> (Vec<BaseCirclePoint>, bool) {
    let mut parents = Vec::with_capacity(parent_indices.len());
    let mut child_ordinal = 0usize;
    let mut parent_ordinal = 0usize;
    let mut valid = child_indices.len() == child_points.len();
    while parent_ordinal < parent_indices.len() && valid {
        let parent = parent_indices[parent_ordinal];
        while child_ordinal < child_indices.len() && child_indices[child_ordinal] >> 2 < parent {
            child_ordinal += 1;
        }
        if child_ordinal >= child_indices.len() {
            valid = false;
        } else {
            let child_index = child_indices[child_ordinal];
            if child_index >> 2 != parent {
                valid = false;
            } else {
                debug_assert!(doublings == 1 || doublings == 2);
                let mut point = double_point(child_points[child_ordinal]);
                if doublings == 2 {
                    point = double_point(point);
                }
                parents.push(remove_line_slot_rotation(point, child_index & 3));
                parent_ordinal += 1;
            }
        }
    }
    (parents, valid)
}

/// Exact extraction-adapter spelling of the coordinate helper.
///
/// This intentionally preserves the adapter's rejection behavior as well as
/// its accepted output, even though the Kani equality theorem only invokes it
/// on the released accepted-path input shape.
pub fn adapter_derive_query_fold_inverses_for_circle(
    domain_log_size: u32,
    layer0: &[u32],
    line1: &[u32],
    line2: &[u32],
    line3: &[u32],
) -> Result<DerivedCircleQueryFoldInverses, CircleFriError> {
    if domain_log_size < 8 || domain_log_size > 30 {
        return Err(CircleFriError::InvalidBitReverseLength);
    }

    let (circle_points, circle_valid) =
        adapter_selected_circle_fiber_points_shared(domain_log_size, layer0);
    if !circle_valid {
        return Err(CircleFriError::CircleFiberOutOfRange);
    }
    let (line1_points, line1_valid) =
        adapter_derive_parent_line_points(layer0, &circle_points, line1, 1);
    if !line1_valid {
        return Err(CircleFriError::QueryOutOfRange);
    }
    let (line2_points, line2_valid) =
        adapter_derive_parent_line_points(line1, &line1_points, line2, 2);
    if !line2_valid {
        return Err(CircleFriError::QueryOutOfRange);
    }
    let (line3_points, line3_valid) =
        adapter_derive_parent_line_points(line2, &line2_points, line3, 2);
    if !line3_valid {
        return Err(CircleFriError::QueryOutOfRange);
    }

    let denominator_count = layer0.len() * 2 + line1.len() * 3 + line2.len() * 3 + line3.len() * 3;
    let mut denominators = Vec::with_capacity(denominator_count);
    let mut zero_denominator = None;
    let mut circle_ordinal = 0usize;
    while circle_ordinal < circle_points.len() {
        let point = circle_points[circle_ordinal];
        let x = point.x.double();
        let y = point.y.double();
        if x.is_zero() {
            zero_denominator = Some(FoldDenominator::CircleX);
        }
        if y.is_zero() {
            zero_denominator = Some(FoldDenominator::CircleY);
        }
        denominators.extend_from_slice(&[x, y]);
        circle_ordinal += 1;
    }

    let mut line_layer = 0usize;
    while line_layer < 3 {
        let points = match line_layer {
            0 => &line1_points,
            1 => &line2_points,
            _ => &line3_points,
        };
        let mut point_ordinal = 0usize;
        while point_ordinal < points.len() {
            let point = points[point_ordinal];
            let coordinates = [
                point.x.double(),
                point.y.double(),
                double_x(point.x).double(),
            ];
            let kinds = [
                FoldDenominator::LineFirstPairX,
                FoldDenominator::LineSecondPairX,
                FoldDenominator::LineSecondFoldX,
            ];
            let mut coordinate_ordinal = 0usize;
            while coordinate_ordinal < 3 {
                let coordinate = coordinates[coordinate_ordinal];
                let kind = kinds[coordinate_ordinal];
                if coordinate.is_zero() {
                    zero_denominator = Some(kind);
                }
                denominators.push(coordinate);
                coordinate_ordinal += 1;
            }
            point_ordinal += 1;
        }
        line_layer += 1;
    }
    if let Some(kind) = zero_denominator {
        return Err(CircleFriError::ZeroDenominator(kind));
    }
    debug_assert_eq!(denominators.len(), denominator_count);

    let mut flat_inverses = vec![M31::ZERO; denominators.len()];
    if !denominators.is_empty() {
        let mut accumulator = M31::ONE;
        let mut index = 0usize;
        while index < denominators.len() {
            flat_inverses[index] = accumulator;
            accumulator = accumulator.mul(denominators[index]);
            index += 1;
        }
        let mut accumulator_inverse = M31::inv(accumulator);
        let mut suffix = denominators.len();
        while suffix > 0 {
            suffix -= 1;
            let prefix = flat_inverses[suffix];
            flat_inverses[suffix] = prefix.mul(accumulator_inverse);
            accumulator_inverse = accumulator_inverse.mul(denominators[suffix]);
        }
    }
    if let (Some(denominator), Some(inverse)) = (denominators.first(), flat_inverses.first()) {
        if denominator.mul(*inverse) != M31::ONE {
            return Err(CircleFriError::InvalidInverseBackend);
        }
    }

    let mut cursor = 0usize;
    let mut circle = Vec::with_capacity(layer0.len());
    let mut circle_output_ordinal = 0usize;
    while circle_output_ordinal < layer0.len() {
        circle.push([flat_inverses[cursor], flat_inverses[cursor + 1]]);
        cursor += 2;
        circle_output_ordinal += 1;
    }

    let mut later0 = Vec::with_capacity(line1.len());
    let mut ordinal0 = 0usize;
    while ordinal0 < line1.len() {
        later0.push([
            flat_inverses[cursor],
            flat_inverses[cursor + 1],
            flat_inverses[cursor + 2],
        ]);
        cursor += 3;
        ordinal0 += 1;
    }
    let mut later1 = Vec::with_capacity(line2.len());
    let mut ordinal1 = 0usize;
    while ordinal1 < line2.len() {
        later1.push([
            flat_inverses[cursor],
            flat_inverses[cursor + 1],
            flat_inverses[cursor + 2],
        ]);
        cursor += 3;
        ordinal1 += 1;
    }
    let mut later2 = Vec::with_capacity(line3.len());
    let mut ordinal2 = 0usize;
    while ordinal2 < line3.len() {
        later2.push([
            flat_inverses[cursor],
            flat_inverses[cursor + 1],
            flat_inverses[cursor + 2],
        ]);
        cursor += 3;
        ordinal2 += 1;
    }
    let later = [later0, later1, later2];
    debug_assert_eq!(cursor, flat_inverses.len());

    let mut final_x = Vec::with_capacity(line3_points.len());
    let mut final_ordinal = 0usize;
    while final_ordinal < line3_points.len() {
        final_x.push(double_x(double_x(line3_points[final_ordinal].x)));
        final_ordinal += 1;
    }
    Ok(DerivedCircleQueryFoldInverses {
        circle,
        later,
        final_x,
    })
}

#[cfg(kani)]
mod proofs;
