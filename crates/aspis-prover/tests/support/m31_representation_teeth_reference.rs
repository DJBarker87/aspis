//! Host-only deliberately weakened representation validators.
//!
//! Every `weakened_*` function encodes one named bug from the Stage 2
//! teeth-first matrix. None of this module is linked by the prover library or
//! the SBF program; it exists only as integration-test support.

#![allow(dead_code)]

#[path = "m31_circle_reference.rs"]
pub mod circle;
#[path = "m31_line_fri_reference.rs"]
pub mod line_fri;

use aspis_core::field::{CM31, M31, M31_QUARTER, P, QM31};
use aspis_prover::multilinear_eval;
use sha2::{Digest, Sha256};

const CIRCLE_LOG_ORDER: u32 = 31;
const CIRCLE_GENERATOR: Point = Point {
    x: M31(2),
    y: M31(1_268_011_823),
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Point {
    x: M31,
    y: M31,
}

impl Point {
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
}

#[derive(Clone, Copy)]
struct Coset {
    initial: Point,
    step: Point,
    log_size: u32,
}

impl Coset {
    fn half_odds(log_size: u32) -> Self {
        Self {
            initial: CIRCLE_GENERATOR.mul(1usize << (CIRCLE_LOG_ORDER - (log_size + 2))),
            step: CIRCLE_GENERATOR.mul(1usize << (CIRCLE_LOG_ORDER - log_size)),
            log_size,
        }
    }

    const fn size(self) -> usize {
        1usize << self.log_size
    }

    fn point(self, index: usize) -> Point {
        self.initial.add(self.step.mul(index))
    }

    fn double(self) -> Self {
        Self {
            initial: self.initial.double(),
            step: self.step.double(),
            log_size: self.log_size - 1,
        }
    }
}

fn bit_reverse<T>(values: &mut [T]) {
    let log_size = values.len().ilog2();
    for index in 0..values.len() {
        let reversed = circle::bit_reverse_index(index, log_size);
        if reversed > index {
            values.swap(index, reversed);
        }
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

fn inverse_butterfly(values: &mut [M31], index0: usize, index1: usize, twiddle: M31) {
    let left = values[index0];
    let right = values[index1];
    values[index0] = left.add(right).half();
    values[index1] = left.sub(right).half().mul(twiddle.inv());
}

fn inverse_fft_layer(values: &mut [M31], layer: usize, block: usize, twiddle: M31) {
    for lane in 0..(1usize << layer) {
        let index0 = (block << (layer + 1)) + lane;
        let index1 = index0 + (1usize << layer);
        inverse_butterfly(values, index0, index1, twiddle);
    }
}

/// Invert the exact scalar circle encoder on a full-size codeword. This is
/// used only to model the incorrect "trace values are AIR evaluations"
/// reinterpretation.
pub fn inverse_circle_codeword(evaluations: &[M31], domain_log_size: u32) -> Vec<M31> {
    assert_eq!(evaluations.len(), 1usize << domain_log_size);
    let mut values = evaluations.to_vec();
    match domain_log_size {
        0 => return values,
        1 => {
            let y = Coset::half_odds(0).initial.y;
            inverse_butterfly(&mut values, 0, 1, y);
            return values;
        }
        2 => {
            let Point { x, y } = Coset::half_odds(1).initial;
            inverse_butterfly(&mut values, 0, 1, y);
            inverse_butterfly(&mut values, 2, 3, y.neg());
            inverse_butterfly(&mut values, 0, 2, x);
            inverse_butterfly(&mut values, 1, 3, x);
            return values;
        }
        _ => {}
    }

    let half_coset = Coset::half_odds(domain_log_size - 1);
    let twiddles = slow_precompute_twiddles(half_coset);
    let line_layers = line_twiddle_layers(&twiddles, domain_log_size - 1);
    let first_circle_layer = circle_twiddles(&line_layers[0]);

    for (block, twiddle) in first_circle_layer.into_iter().enumerate() {
        inverse_fft_layer(&mut values, 0, block, twiddle);
    }
    for (layer, twiddles) in line_layers.iter().enumerate() {
        for (block, twiddle) in twiddles.iter().copied().enumerate() {
            inverse_fft_layer(&mut values, layer + 1, block, twiddle);
        }
    }
    values
}

pub fn digest_m31(label: &[u8], values: &[M31]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(label);
    hasher.update((values.len() as u32).to_le_bytes());
    for value in values {
        hasher.update(value.to_le_bytes());
    }
    hasher.finalize().into()
}

pub fn digest_qm31(label: &[u8], values: &[QM31]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(label);
    hasher.update((values.len() as u32).to_le_bytes());
    let mut bytes = [0u8; 16];
    for value in values {
        value.write_le_bytes(&mut bytes);
        hasher.update(bytes);
    }
    hasher.finalize().into()
}

pub fn canonical_direct_message_digest(message: &[M31], domain_log_size: u32) -> [u8; 32] {
    digest_m31(
        b"aspis:teeth:direct-message",
        &circle::encode_circle(message, domain_log_size),
    )
}

pub fn weakened_air_ifft_digest(message: &[M31], domain_log_size: u32) -> [u8; 32] {
    let air_coefficients = inverse_circle_codeword(message, message.len().ilog2());
    digest_m31(
        b"aspis:teeth:direct-message",
        &circle::encode_circle(&air_coefficients, domain_log_size),
    )
}

pub fn canonical_direct_message_accepts(
    message: &[M31],
    domain_log_size: u32,
    candidate: [u8; 32],
) -> bool {
    canonical_direct_message_digest(message, domain_log_size) == candidate
}

pub fn weakened_air_ifft_accepts(
    message: &[M31],
    domain_log_size: u32,
    candidate: [u8; 32],
) -> bool {
    weakened_air_ifft_digest(message, domain_log_size) == candidate
}

pub fn bit_reversed_message(message: &[M31]) -> Vec<M31> {
    let mut reversed = message.to_vec();
    line_fri::bit_reverse(&mut reversed);
    reversed
}

pub fn canonical_mle_accepts(message: &[M31], point: &[QM31], candidate: QM31) -> bool {
    multilinear_eval(message, point) == candidate
}

pub fn weakened_reversed_mle_accepts(message: &[M31], point: &[QM31], candidate: QM31) -> bool {
    multilinear_eval(&bit_reversed_message(message), point) == candidate
}

pub fn canonical_circle_slots(codeword: &[M31], fiber: usize) -> [M31; 4] {
    codeword[fiber * 4..fiber * 4 + 4].try_into().unwrap()
}

pub fn weakened_strided_circle_slots(codeword: &[M31], fiber: usize) -> [M31; 4] {
    let fiber_count = codeword.len() / 4;
    core::array::from_fn(|slot| codeword[fiber + slot * fiber_count])
}

/// Deliberate middle-slot swap used as an additional permutation proxy. This
/// is not claimed to be Stwo's exact internal twiddle-coset accessor; the
/// separate strided accessor above is the exact legacy shape named by the
/// production plan.
pub fn weakened_middle_slot_swap(codeword: &[M31], fiber: usize) -> [M31; 4] {
    let canonical = canonical_circle_slots(codeword, fiber);
    [canonical[0], canonical[2], canonical[1], canonical[3]]
}

pub fn canonical_circle_slots_accepts(codeword: &[M31], fiber: usize, candidate: [M31; 4]) -> bool {
    canonical_circle_slots(codeword, fiber) == candidate
}

pub fn weakened_strided_circle_slots_accepts(
    codeword: &[M31],
    fiber: usize,
    candidate: [M31; 4],
) -> bool {
    weakened_strided_circle_slots(codeword, fiber) == candidate
}

pub fn weakened_middle_slot_swap_accepts(
    codeword: &[M31],
    fiber: usize,
    candidate: [M31; 4],
) -> bool {
    weakened_middle_slot_swap(codeword, fiber) == candidate
}

pub fn fold_circle_with_second_challenge(
    values: [QM31; 4],
    alpha: QM31,
    second_challenge: QM31,
    x: M31,
    y: M31,
) -> QM31 {
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
        .add(second_challenge.mul(positive.sub(negative).mul_m31(inv_2x)))
}

pub fn canonical_circle_alpha2_accepts(
    values: [QM31; 4],
    alpha: QM31,
    x: M31,
    y: M31,
    candidate: QM31,
) -> bool {
    circle::normalized_fold4(values, alpha, x, y) == candidate
}

pub fn weakened_circle_alpha_reuse_accepts(
    values: [QM31; 4],
    alpha: QM31,
    x: M31,
    y: M31,
    candidate: QM31,
) -> bool {
    fold_circle_with_second_challenge(values, alpha, alpha, x, y) == candidate
}

pub fn weakened_line_alpha_reuse(
    evaluations: &[QM31],
    domain: line_fri::LineDomain,
    alpha: QM31,
) -> (line_fri::LineDomain, Vec<QM31>) {
    let (domain, first) = line_fri::fold_line(evaluations, domain, alpha);
    line_fri::fold_line(&first, domain, alpha)
}

pub fn canonical_line_alpha2_accepts(
    evaluations: &[QM31],
    domain: line_fri::LineDomain,
    alpha: QM31,
    candidate: &[QM31],
) -> bool {
    line_fri::fold_line_arity4(evaluations, domain, alpha).1 == candidate
}

pub fn weakened_line_alpha_reuse_accepts(
    evaluations: &[QM31],
    domain: line_fri::LineDomain,
    alpha: QM31,
    candidate: &[QM31],
) -> bool {
    weakened_line_alpha_reuse(evaluations, domain, alpha).1 == candidate
}

pub fn normalized_line_fold(
    evaluations: &[QM31],
    domain: line_fri::LineDomain,
    alpha: QM31,
) -> Vec<QM31> {
    line_fri::scale(
        &line_fri::fold_line_arity4(evaluations, domain, alpha).1,
        M31_QUARTER,
    )
}

pub fn canonical_normalized_line_accepts(
    evaluations: &[QM31],
    domain: line_fri::LineDomain,
    alpha: QM31,
    candidate: &[QM31],
) -> bool {
    normalized_line_fold(evaluations, domain, alpha) == candidate
}

pub fn weakened_raw_line_accepts(
    evaluations: &[QM31],
    domain: line_fri::LineDomain,
    alpha: QM31,
    candidate: &[QM31],
) -> bool {
    line_fri::fold_line_arity4(evaluations, domain, alpha).1 == candidate
}

pub fn canonical_circle_ood(coefficients: &[QM31], point: circle::SecureCirclePoint) -> QM31 {
    circle::evaluate_circle_secure(coefficients, point)
}

pub fn weakened_swapped_ood_factors(
    coefficients: &[QM31],
    point: circle::SecureCirclePoint,
) -> QM31 {
    let folded = circle::fold_first_two_coefficients(coefficients, point.x, point.y);
    circle::evaluate_line_secure(&folded, circle::double_x_secure(point.x))
}

pub fn weakened_retained_y_ood(coefficients: &[QM31], point: circle::SecureCirclePoint) -> QM31 {
    let folded = circle::fold_first_two_coefficients(coefficients, point.y, point.x);
    circle::evaluate_line_secure(&folded, point.y)
}

pub fn canonical_circle_ood_accepts(
    coefficients: &[QM31],
    point: circle::SecureCirclePoint,
    candidate: QM31,
) -> bool {
    canonical_circle_ood(coefficients, point) == candidate
}

pub fn weakened_swapped_ood_accepts(
    coefficients: &[QM31],
    point: circle::SecureCirclePoint,
    candidate: QM31,
) -> bool {
    weakened_swapped_ood_factors(coefficients, point) == candidate
}

pub fn weakened_retained_y_ood_accepts(
    coefficients: &[QM31],
    point: circle::SecureCirclePoint,
    candidate: QM31,
) -> bool {
    weakened_retained_y_ood(coefficients, point) == candidate
}

pub fn canonical_next_storage_codeword(
    natural: &[QM31],
    domain: line_fri::LineDomain,
    alpha: QM31,
) -> Vec<QM31> {
    let mut next = line_fri::fold_adjacent_natural_arity4(natural, alpha);
    line_fri::bit_reverse(&mut next);
    line_fri::evaluate_on_domain(&next, domain.repeated_double(2))
}

pub fn weakened_unbridged_next_codeword(
    natural: &[QM31],
    domain: line_fri::LineDomain,
    alpha: QM31,
) -> Vec<QM31> {
    let next = line_fri::fold_adjacent_natural_arity4(natural, alpha);
    line_fri::evaluate_on_domain(&next, domain.repeated_double(2))
}

pub fn canonical_storage_bridge_accepts(
    natural: &[QM31],
    domain: line_fri::LineDomain,
    alpha: QM31,
    candidate: &[QM31],
) -> bool {
    canonical_next_storage_codeword(natural, domain, alpha) == candidate
}

pub fn weakened_unbridged_storage_accepts(
    natural: &[QM31],
    domain: line_fri::LineDomain,
    alpha: QM31,
    candidate: &[QM31],
) -> bool {
    weakened_unbridged_next_codeword(natural, domain, alpha) == candidate
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalCandidate {
    pub serialized: Vec<u8>,
    pub query_value: QM31,
    pub relation_value: QM31,
}

fn serialize_qm31(values: &[QM31]) -> Vec<u8> {
    let mut bytes = vec![0u8; values.len() * 16];
    for (value, chunk) in values.iter().zip(bytes.chunks_exact_mut(16)) {
        value.write_le_bytes(chunk);
    }
    bytes
}

fn dot(left: &[QM31], right: &[QM31]) -> QM31 {
    left.iter()
        .zip(right)
        .fold(QM31::ZERO, |sum, (left, right)| sum.add(left.mul(*right)))
}

pub fn canonical_final_candidate(
    natural: &[QM31],
    relation_weights: &[QM31],
    query_x: QM31,
) -> FinalCandidate {
    let mut storage = natural.to_vec();
    line_fri::bit_reverse(&mut storage);
    FinalCandidate {
        serialized: serialize_qm31(natural),
        query_value: line_fri::evaluate_line_poly(&storage, query_x),
        relation_value: dot(natural, relation_weights),
    }
}

pub fn weakened_storage_final_candidate(
    natural: &[QM31],
    relation_weights: &[QM31],
    query_x: QM31,
) -> FinalCandidate {
    let mut storage = natural.to_vec();
    line_fri::bit_reverse(&mut storage);
    FinalCandidate {
        serialized: serialize_qm31(&storage),
        query_value: line_fri::evaluate_line_poly(natural, query_x),
        relation_value: dot(&storage, relation_weights),
    }
}

pub fn canonical_final_accepts(
    natural: &[QM31],
    relation_weights: &[QM31],
    query_x: QM31,
    candidate: &FinalCandidate,
) -> bool {
    canonical_final_candidate(natural, relation_weights, query_x) == *candidate
}

pub fn weakened_storage_final_accepts(
    natural: &[QM31],
    relation_weights: &[QM31],
    query_x: QM31,
    candidate: &FinalCandidate,
) -> bool {
    weakened_storage_final_candidate(natural, relation_weights, query_x) == *candidate
}

#[derive(Clone, Copy)]
pub struct Rng(pub u64);

impl Rng {
    pub fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0 = self.0.wrapping_mul(0x2545_f491_4f6c_dd1d);
        self.0
    }

    pub fn m31(&mut self) -> M31 {
        M31((self.next() as u32) % P)
    }

    pub fn qm31(&mut self) -> QM31 {
        QM31 {
            c0: CM31::new(self.m31(), self.m31()),
            c1: CM31::new(self.m31(), self.m31()),
        }
    }
}

pub fn q(values: [u32; 4]) -> QM31 {
    QM31 {
        c0: CM31::new(M31(values[0]), M31(values[1])),
        c1: CM31::new(M31(values[2]), M31(values[3])),
    }
}
