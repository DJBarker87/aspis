//! Test-only M31 circle-polynomial reference machinery.
//!
//! This is a narrow scalar port of the circle-domain and CPU FFT formulas in
//! `starkware-libs/stwo@5d10e6b4baa559766e7bbae133b918121211a9c5`:
//!
//! - `core/circle.rs` (`M31_CIRCLE_GEN`, circle addition, canonical cosets),
//! - `core/poly/utils.rs` (bit-reversed tensor-basis folding),
//! - `prover/backend/cpu/circle.rs` (twiddles and circle FFT), and
//! - `prover/backend/cpu/fri.rs` (circle-to-line then line folding).
//!
//! It is deliberately not production PCS code. Its only job is to make the
//! candidate representation independently executable in host conformance
//! tests without adding Stwo's full prover dependency graph to Aspis.

#![allow(dead_code)]

use aspis_core::field::{M31, QM31};

pub const STWO_REFERENCE_COMMIT: &str = "5d10e6b4baa559766e7bbae133b918121211a9c5";
pub const TRACE_LOG_SIZE: u32 = 10;
pub const DOMAIN_LOG_SIZE: u32 = 12;
/// The trace vector is the multilinear message table in big-endian Boolean
/// index order. It is fed directly to the low-degree encoder as its
/// coefficient/message vector; it is not interpolated as AIR evaluations.
pub const MESSAGE_COORDINATE_ORDER: &[u8] = b"multilinear-hypercube:big-endian-index";

/// Test-only candidate discriminator. Production adoption still requires a
/// separately allocated envelope version/flag and transcript-KAT re-pin.
pub const CANDIDATE_WIRE_DISCRIMINATOR: &[u8] = b"aspis:c1:m31-circle:v0";
/// Production integration requires a circle-tensor OOD accumulator rather
/// than the current geometric monomial-weight accumulator.
pub const REQUIRED_OOD_WEIGHT_ACCUMULATOR: &[u8] = b"circle-tensor:[y,x,pi(x),...]";
/// Production integration must re-pin the transcript from the new wire tag,
/// roots, circle OOD point/claims, and all downstream challenges.
pub const REQUIRED_TRANSCRIPT_KAT: &[u8] = b"new-envelope-version+circle-roots+ood+downstream";
pub const CANDIDATE_C1_COLUMNS: usize = 49;
pub const CANDIDATE_FIBER_SLOTS: usize = 4;
pub const CANDIDATE_C1_LEAF_BYTES: usize = CANDIDATE_C1_COLUMNS * CANDIDATE_FIBER_SLOTS * 4;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CirclePoint {
    pub x: M31,
    pub y: M31,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SecureCirclePoint {
    pub x: QM31,
    pub y: QM31,
}

const CIRCLE_LOG_ORDER: u32 = 31;
const CIRCLE_GENERATOR: CirclePoint = CirclePoint {
    x: M31(2),
    y: M31(1_268_011_823),
};

impl CirclePoint {
    fn identity() -> Self {
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

    fn neg(self) -> Self {
        Self {
            x: self.x,
            y: self.y.neg(),
        }
    }

    fn mul(self, mut scalar: usize) -> Self {
        let mut result = Self::identity();
        let mut power = self;
        while scalar != 0 {
            if scalar & 1 == 1 {
                result = result.add(power);
            }
            power = power.double();
            scalar >>= 1;
        }
        result
    }
}

#[derive(Clone, Copy)]
struct Coset {
    initial: CirclePoint,
    step: CirclePoint,
    log_size: u32,
}

impl Coset {
    fn half_odds(log_size: u32) -> Self {
        let initial_index = 1usize << (CIRCLE_LOG_ORDER - (log_size + 2));
        let step_index = 1usize << (CIRCLE_LOG_ORDER - log_size);
        Self {
            initial: CIRCLE_GENERATOR.mul(initial_index),
            step: CIRCLE_GENERATOR.mul(step_index),
            log_size,
        }
    }

    fn size(self) -> usize {
        1usize << self.log_size
    }

    fn point(self, index: usize) -> CirclePoint {
        self.initial.add(self.step.mul(index))
    }

    fn double(self) -> Self {
        assert!(self.log_size > 0);
        Self {
            initial: self.initial.double(),
            step: self.step.double(),
            log_size: self.log_size - 1,
        }
    }
}

pub fn bit_reverse_index(index: usize, log_size: u32) -> usize {
    if log_size == 0 {
        0
    } else {
        index.reverse_bits() >> (usize::BITS - log_size)
    }
}

fn bit_reverse<T>(values: &mut [T]) {
    let log_size = values.len().ilog2();
    for index in 0..values.len() {
        let reversed = bit_reverse_index(index, log_size);
        if reversed > index {
            values.swap(index, reversed);
        }
    }
}

/// Point corresponding to a bit-reversed circle-codeword index.
pub fn bit_reversed_domain_point(index: usize, log_size: u32) -> CirclePoint {
    let natural_index = bit_reverse_index(index, log_size);
    let half = 1usize << (log_size - 1);
    let half_coset = Coset::half_odds(log_size - 1);
    if natural_index < half {
        half_coset.point(natural_index)
    } else {
        half_coset.point(natural_index - half).neg()
    }
}

fn butterfly(values: &mut [M31], index0: usize, index1: usize, twiddle: M31) {
    let left = values[index0];
    let weighted_right = values[index1].mul(twiddle);
    values[index0] = left.add(weighted_right);
    values[index1] = left.sub(weighted_right);
}

fn fft_layer(values: &mut [M31], layer: usize, block: usize, twiddle: M31) {
    for lane in 0..(1usize << layer) {
        let index0 = (block << (layer + 1)) + lane;
        let index1 = index0 + (1usize << layer);
        butterfly(values, index0, index1, twiddle);
    }
}

fn slow_precompute_twiddles(mut coset: Coset) -> Vec<M31> {
    let mut twiddles = Vec::with_capacity(coset.size());
    while coset.log_size != 0 {
        let layer_start = twiddles.len();
        twiddles.extend((0..coset.size() / 2).map(|index| coset.point(index).x));
        bit_reverse(&mut twiddles[layer_start..]);
        coset = coset.double();
    }
    // Stwo pads the size-(n-1) tree to n with an unused nonzero element.
    twiddles.push(M31::ONE);
    twiddles
}

fn line_twiddle_layers(twiddles: &[M31], line_log_size: u32) -> Vec<Vec<M31>> {
    let mut layers = (0..line_log_size)
        .map(|layer| {
            let len = 1usize << layer;
            twiddles[twiddles.len() - 2 * len..twiddles.len() - len].to_vec()
        })
        .collect::<Vec<_>>();
    layers.reverse();
    layers
}

fn circle_twiddles(first_line_layer: &[M31]) -> Vec<M31> {
    let mut result = Vec::with_capacity(first_line_layer.len() * 2);
    for pair in first_line_layer.chunks_exact(2) {
        let x = pair[0];
        let y = pair[1];
        result.extend([y, y.neg(), x.neg(), x]);
    }
    result
}

/// Evaluate bit-reversed circle-FFT coefficients on the canonical M31 circle
/// domain, returning code symbols in Stwo's bit-reversed evaluation order.
pub fn encode_circle(coefficients: &[M31], domain_log_size: u32) -> Vec<M31> {
    assert!(coefficients.len().is_power_of_two());
    assert!(coefficients.len() <= 1usize << domain_log_size);
    let mut values = vec![M31::ZERO; 1usize << domain_log_size];
    values[..coefficients.len()].copy_from_slice(coefficients);

    if domain_log_size == 1 {
        let y = Coset::half_odds(0).initial.y;
        butterfly(&mut values, 0, 1, y);
        return values;
    }

    let half_coset = Coset::half_odds(domain_log_size - 1);
    if domain_log_size == 2 {
        let CirclePoint { x, y } = half_coset.initial;
        butterfly(&mut values, 0, 2, x);
        butterfly(&mut values, 1, 3, x);
        butterfly(&mut values, 0, 1, y);
        butterfly(&mut values, 2, 3, y.neg());
        return values;
    }

    let twiddles = slow_precompute_twiddles(half_coset);
    let line_layers = line_twiddle_layers(&twiddles, domain_log_size - 1);
    let first_circle_layer = circle_twiddles(&line_layers[0]);

    for (layer, twiddles) in line_layers.iter().enumerate().rev() {
        for (block, twiddle) in twiddles.iter().copied().enumerate() {
            fft_layer(&mut values, layer + 1, block, twiddle);
        }
    }
    for (block, twiddle) in first_circle_layer.into_iter().enumerate() {
        fft_layer(&mut values, 0, block, twiddle);
    }
    values
}

fn double_x_base(x: M31) -> M31 {
    x.mul(x).double().sub(M31::ONE)
}

pub fn double_x_secure(x: QM31) -> QM31 {
    x.square().add(x.square()).sub(QM31::ONE)
}

/// Direct tensor-basis evaluation, independent of the FFT implementation.
pub fn evaluate_circle_base(coefficients: &[M31], point: CirclePoint) -> M31 {
    assert!(coefficients.len().is_power_of_two());
    let mut values = coefficients.to_vec();
    let mut factor = point.y;
    while values.len() > 1 {
        for index in 0..values.len() / 2 {
            values[index] = values[2 * index].add(factor.mul(values[2 * index + 1]));
        }
        values.truncate(values.len() / 2);
        factor = if values.len() == coefficients.len() / 2 {
            point.x
        } else {
            double_x_base(factor)
        };
    }
    values[0]
}

pub fn evaluate_circle_secure(coefficients: &[QM31], point: SecureCirclePoint) -> QM31 {
    assert!(coefficients.len().is_power_of_two());
    let mut values = coefficients.to_vec();
    let mut factor = point.y;
    let mut first = true;
    while values.len() > 1 {
        for index in 0..values.len() / 2 {
            values[index] = values[2 * index].add(factor.mul(values[2 * index + 1]));
        }
        values.truncate(values.len() / 2);
        factor = if first {
            first = false;
            point.x
        } else {
            double_x_secure(factor)
        };
    }
    values[0]
}

pub fn evaluate_line_secure(coefficients: &[QM31], mut x: QM31) -> QM31 {
    assert!(coefficients.len().is_power_of_two());
    let mut values = coefficients.to_vec();
    while values.len() > 1 {
        for index in 0..values.len() / 2 {
            values[index] = values[2 * index].add(x.mul(values[2 * index + 1]));
        }
        values.truncate(values.len() / 2);
        x = double_x_secure(x);
    }
    values[0]
}

pub fn fold_first_two_coefficients(
    coefficients: &[QM31],
    y_factor: QM31,
    x_factor: QM31,
) -> Vec<QM31> {
    assert_eq!(coefficients.len() % 4, 0);
    coefficients
        .chunks_exact(4)
        .map(|chunk| {
            chunk[0]
                .add(y_factor.mul(chunk[1]))
                .add(x_factor.mul(chunk[2]))
                .add(x_factor.mul(y_factor).mul(chunk[3]))
        })
        .collect()
}

/// Aspis-normalized circle-to-line plus line fold for one four-slot fiber.
pub fn normalized_fold4(values: [QM31; 4], alpha: QM31, x: M31, y: M31) -> QM31 {
    let inv_2x = x.double().inv();
    let inv_2y = y.double().inv();
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
        .add(alpha.square().mul(positive.sub(negative).mul_m31(inv_2x)))
}

pub fn secure_circle_point(parameter: QM31) -> SecureCirclePoint {
    let square = parameter.square();
    let inverse = QM31::ONE.add(square).inv();
    SecureCirclePoint {
        x: QM31::ONE.sub(square).mul(inverse),
        y: parameter.add(parameter).mul(inverse),
    }
}

pub fn lift(value: M31) -> QM31 {
    QM31::from_cm31(aspis_core::field::CM31::from_m31(value))
}
