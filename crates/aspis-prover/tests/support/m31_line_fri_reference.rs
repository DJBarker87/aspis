//! Test-only scalar port of Stwo's later line-FRI formulas.
//!
//! Pinned to `starkware-libs/stwo@5d10e6b4baa559766e7bbae133b918121211a9c5`:
//! `core/circle.rs`, `core/poly/line.rs`, `core/fft.rs`, `core/fri.rs`, and
//! `core/queries.rs`. This module deliberately preserves Stwo's unnormalized
//! inverse butterfly: every line fold contributes a factor of two.

#![allow(dead_code)]

use aspis_core::field::{CM31, M31, QM31};

pub const STWO_REFERENCE_COMMIT: &str = "5d10e6b4baa559766e7bbae133b918121211a9c5";
pub const STWO_LINE_FRI_CORPUS_DOMAIN: &[u8] = b"aspis:host:stwo-line-fri-corpus:v1";

const CIRCLE_LOG_ORDER: u32 = 31;
const CIRCLE_ORDER: usize = 1usize << CIRCLE_LOG_ORDER;
const CIRCLE_INDEX_MASK: usize = CIRCLE_ORDER - 1;
const CIRCLE_GENERATOR: CirclePoint = CirclePoint {
    x: M31(2),
    y: M31(1_268_011_823),
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CirclePoint {
    pub x: M31,
    pub y: M31,
}

impl CirclePoint {
    const fn identity() -> Self {
        Self {
            x: M31::ONE,
            y: M31::ZERO,
        }
    }

    fn add(self, rhs: Self) -> Self {
        Self {
            x: self.x.mul(rhs.x).sub(self.y.mul(rhs.y)),
            y: self.x.mul(rhs.y).add(self.y.mul(rhs.x)),
        }
    }

    fn double(self) -> Self {
        self.add(self)
    }

    fn mul(self, mut scalar: usize) -> Self {
        let mut result = Self::identity();
        let mut power = self;
        while scalar != 0 {
            if scalar & 1 != 0 {
                result = result.add(power);
            }
            power = power.double();
            scalar >>= 1;
        }
        result
    }

    fn log_order(self) -> u32 {
        let mut order = 0;
        let mut x = self.x;
        while x != M31::ONE {
            x = double_x_base(x);
            order += 1;
            assert!(order <= CIRCLE_LOG_ORDER);
        }
        order
    }
}

/// The x-coordinates of a circle coset, matching Stwo's `LineDomain`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LineDomain {
    initial_index: usize,
    step_index: usize,
    log_size: u32,
}

impl LineDomain {
    /// Construct the x-projection of `initial + <G_log_size>`.
    pub fn new(initial_index: usize, log_size: u32) -> Self {
        assert!(log_size <= CIRCLE_LOG_ORDER);
        let initial_index = initial_index & CIRCLE_INDEX_MASK;
        let initial = CIRCLE_GENERATOR.mul(initial_index);
        match log_size {
            0 => {}
            1 => assert!(initial.x != M31::ZERO, "coset x-coordinates not unique"),
            _ => assert!(
                initial.log_order() >= log_size + 2,
                "coset x-coordinates not unique"
            ),
        }
        Self {
            initial_index,
            step_index: 1usize << (CIRCLE_LOG_ORDER - log_size),
            log_size,
        }
    }

    /// Stwo's canonical `LineDomain::new(Coset::half_odds(log_size))`.
    pub fn half_odds(log_size: u32) -> Self {
        assert!(log_size + 2 <= CIRCLE_LOG_ORDER);
        Self::new(1usize << (CIRCLE_LOG_ORDER - (log_size + 2)), log_size)
    }

    pub const fn log_size(self) -> u32 {
        self.log_size
    }

    pub const fn size(self) -> usize {
        1usize << self.log_size
    }

    pub const fn initial_index(self) -> usize {
        self.initial_index
    }

    pub fn index_at(self, index: usize) -> usize {
        self.initial_index
            .wrapping_add(self.step_index.wrapping_mul(index))
            & CIRCLE_INDEX_MASK
    }

    pub fn at(self, index: usize) -> M31 {
        CIRCLE_GENERATOR.mul(self.index_at(index)).x
    }

    pub fn double(self) -> Self {
        assert!(self.log_size > 0);
        Self {
            initial_index: self.initial_index.wrapping_mul(2) & CIRCLE_INDEX_MASK,
            step_index: self.step_index.wrapping_mul(2) & CIRCLE_INDEX_MASK,
            log_size: self.log_size - 1,
        }
    }

    pub fn repeated_double(self, folds: u32) -> Self {
        (0..folds).fold(self, |domain, _| domain.double())
    }
}

pub fn bit_reverse_index(index: usize, log_size: u32) -> usize {
    if log_size == 0 {
        0
    } else {
        index.reverse_bits() >> (usize::BITS - log_size)
    }
}

pub fn bit_reverse<T>(values: &mut [T]) {
    assert!(values.len().is_power_of_two());
    let log_size = values.len().ilog2();
    for index in 0..values.len() {
        let reversed = bit_reverse_index(index, log_size);
        if reversed > index {
            values.swap(index, reversed);
        }
    }
}

fn double_x_base(x: M31) -> M31 {
    let square = x.mul(x);
    square.add(square).sub(M31::ONE)
}

fn double_x_secure(x: QM31) -> QM31 {
    x.square().add(x.square()).sub(QM31::ONE)
}

pub fn lift(value: M31) -> QM31 {
    QM31::from_cm31(CM31::from_m31(value))
}

/// Evaluate Stwo bit-reversed `LinePoly` coefficients at one secure x.
pub fn evaluate_line_poly(coefficients: &[QM31], x: QM31) -> QM31 {
    assert!(coefficients.len().is_power_of_two());
    if coefficients.len() == 1 {
        return coefficients[0];
    }
    let (left, right) = coefficients.split_at(coefficients.len() / 2);
    let doubled_x = double_x_secure(x);
    evaluate_line_poly(left, doubled_x).add(x.mul(evaluate_line_poly(right, doubled_x)))
}

/// Evaluate on a line domain and return Stwo's bit-reversed value order.
pub fn evaluate_on_domain(coefficients: &[QM31], domain: LineDomain) -> Vec<QM31> {
    assert!(coefficients.len() <= domain.size());
    (0..domain.size())
        .map(|index| {
            let natural_index = bit_reverse_index(index, domain.log_size());
            evaluate_line_poly(coefficients, lift(domain.at(natural_index)))
        })
        .collect()
}

/// One pinned Stwo line fold. This is intentionally unnormalized.
pub fn fold_line(evaluations: &[QM31], domain: LineDomain, alpha: QM31) -> (LineDomain, Vec<QM31>) {
    assert_eq!(evaluations.len(), domain.size());
    assert!(evaluations.len() >= 2, "evaluation too small");
    let folded = evaluations
        .chunks_exact(2)
        .enumerate()
        .map(|(pair, values)| {
            let natural_index = bit_reverse_index(pair << 1, domain.log_size());
            let inverse_x = domain.at(natural_index).inv();
            let f0 = values[0].add(values[1]);
            let f1 = values[0].sub(values[1]).mul_m31(inverse_x);
            f0.add(alpha.mul(f1))
        })
        .collect();
    (domain.double(), folded)
}

/// Two Stwo line folds, matching one Aspis radix-4 round.
pub fn fold_line_arity4(
    evaluations: &[QM31],
    domain: LineDomain,
    alpha: QM31,
) -> (LineDomain, Vec<QM31>) {
    assert!(evaluations.len() >= 4);
    let (domain, first) = fold_line(evaluations, domain, alpha);
    fold_line(&first, domain, alpha.square())
}

/// Fold one four-value bit-reversed fiber at `fiber_start` in `source_domain`.
pub fn fold_line_fiber4(
    values: [QM31; 4],
    source_domain: LineDomain,
    fiber_start: usize,
    alpha: QM31,
) -> QM31 {
    assert_eq!(fiber_start & 3, 0);
    assert!(fiber_start + 4 <= source_domain.size());
    let domain_initial_index = bit_reverse_index(fiber_start, source_domain.log_size());
    let fiber_domain = LineDomain::new(source_domain.index_at(domain_initial_index), 2);
    fold_line_arity4(&values, fiber_domain, alpha).1[0]
}

/// Coefficient-side image of one unnormalized Stwo line fold.
pub fn fold_line_coefficients(coefficients: &[QM31], alpha: QM31) -> Vec<QM31> {
    assert!(coefficients.len().is_power_of_two());
    assert!(coefficients.len() >= 2);
    let (even, odd) = coefficients.split_at(coefficients.len() / 2);
    even.iter()
        .zip(odd)
        .map(|(&even, &odd)| {
            let folded = even.add(alpha.mul(odd));
            folded.add(folded)
        })
        .collect()
}

/// Coefficient-side image of one Aspis radix-4 round.
pub fn fold_line_coefficients_arity4(coefficients: &[QM31], alpha: QM31) -> Vec<QM31> {
    let first = fold_line_coefficients(coefficients, alpha);
    fold_line_coefficients(&first, alpha.square())
}

/// Aspis relation-vector fold in unchanged natural MLE coordinate order.
pub fn fold_adjacent_natural_arity4(coefficients: &[QM31], alpha: QM31) -> Vec<QM31> {
    assert_eq!(coefficients.len() % 4, 0);
    let alpha_squared = alpha.square();
    let alpha_cubed = alpha_squared.mul(alpha);
    coefficients
        .chunks_exact(4)
        .map(|chunk| {
            chunk[0]
                .add(alpha.mul(chunk[1]))
                .add(alpha_squared.mul(chunk[2]))
                .add(alpha_cubed.mul(chunk[3]))
        })
        .collect()
}

pub fn scale(values: &[QM31], scalar: M31) -> Vec<QM31> {
    values.iter().map(|value| value.mul_m31(scalar)).collect()
}

/// Stwo query propagation across `folds` binary line folds.
pub fn fold_queries(positions: &[usize], log_domain_size: u32, folds: u32) -> Vec<usize> {
    assert!(folds <= log_domain_size);
    let mut positions = positions.to_vec();
    positions.sort_unstable();
    positions.dedup();
    let mut folded = Vec::with_capacity(positions.len());
    for position in positions {
        assert!(position < 1usize << log_domain_size);
        let position = position >> folds;
        if folded.last().copied() != Some(position) {
            folded.push(position);
        }
    }
    folded
}
