//! Isolated synthetic constraint-composition kernel.
//!
//! The probe is intentionally parameterized by runtime instruction data so
//! the SBF compiler cannot constant-fold the work. It brackets, but does not
//! replace, the evaluator-derived composition counts.

use alloc::vec::Vec;

use aspis_core::field::{CM31, M31, QM31};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CompositionProbe {
    pub opened_values: u16,
    pub poseidon_sbox_terms: u16,
    pub poseidon_linear_terms: u16,
    pub logup_degree3_terms: u16,
    pub range_bit_terms: u16,
    pub eq_variables: u8,
}

impl CompositionProbe {
    /// Roughly two active Poseidon2 full rounds at the opened row.
    pub const OPTIMISTIC: Self = Self {
        opened_values: 80,
        poseidon_sbox_terms: 32,
        poseidon_linear_terms: 64,
        logup_degree3_terms: 1,
        range_bit_terms: 32,
        eq_variables: 10,
    };

    /// Four active width-16 Poseidon2 rounds plus the non-hash statement
    /// relations expected in an lr10 wide row.
    pub const REALISTIC: Self = Self {
        opened_values: 80,
        poseidon_sbox_terms: 64,
        poseidon_linear_terms: 128,
        logup_degree3_terms: 1,
        range_bit_terms: 64,
        eq_variables: 10,
    };

    /// Six active rounds, two LogUp relations, and extra range/boundary work.
    /// This is a pessimistic engineering bracket, not a security bound.
    pub const PESSIMISTIC: Self = Self {
        opened_values: 82,
        poseidon_sbox_terms: 96,
        poseidon_linear_terms: 192,
        logup_degree3_terms: 2,
        range_bit_terms: 96,
        eq_variables: 10,
    };
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CompositionProbeResult {
    pub accumulator: QM31,
    pub qm31_multiplications: u32,
    pub qm31_by_cm31_multiplications: u32,
    pub additions_or_subtractions: u32,
}

fn sample(index: u32, lane: u32) -> QM31 {
    let value = |offset: u32| M31(1 + index.wrapping_mul(131).wrapping_add(offset) % 1_000_003);
    QM31 {
        c0: CM31 {
            a: value(lane * 17),
            b: value(lane * 17 + 3),
        },
        c1: CM31 {
            a: value(lane * 17 + 7),
            b: value(lane * 17 + 11),
        },
    }
}

/// Execute one synthetic composition evaluation at an extension-field point.
pub fn evaluate_composition_probe(probe: CompositionProbe) -> CompositionProbeResult {
    let opened_count = usize::from(probe.opened_values.max(1));
    let opened = (0..opened_count)
        .map(|index| sample(index as u32, 1))
        .collect::<Vec<_>>();
    let alpha = sample(91, 2);
    let gamma = sample(97, 3);
    let mut alpha_power = QM31::ONE;
    let mut gamma_power = QM31::ONE;
    let mut accumulator = QM31::ZERO;
    let mut qm31_multiplications = 0u32;
    let mut qm31_by_cm31_multiplications = 0u32;
    let mut additions_or_subtractions = 0u32;

    // RLC the k' opened values exactly as the statement/PCS seam requires.
    for value in &opened {
        accumulator = accumulator.add(gamma_power.mul(*value));
        gamma_power = gamma_power.mul(gamma);
        qm31_multiplications += 2;
        additions_or_subtractions += 1;
    }

    // Degree-5 Poseidon2 S-box constraints: y - (x + rc)^5.
    for term in 0..probe.poseidon_sbox_terms as usize {
        let x =
            opened[term % opened_count].add(QM31::from_cm31(CM31::from_m31(M31(1 + term as u32))));
        let square = x.mul(x);
        let fourth = square.mul(square);
        let fifth = fourth.mul(x);
        let residual = fifth.sub(opened[(term + 1) % opened_count]);
        alpha_power = alpha_power.mul(alpha);
        accumulator = accumulator.add(alpha_power.mul(residual));
        qm31_multiplications += 5;
        additions_or_subtractions += 3;
    }

    // External/internal linear-layer and public-binding terms. Base-field
    // constants use the cheaper late-lift kernel.
    for term in 0..probe.poseidon_linear_terms as usize {
        let mut residual = QM31::ZERO;
        for lane in 0..4usize {
            residual = residual.add(
                opened[(term + lane) % opened_count].mul_cm31(CM31::from_m31(M31(1 + lane as u32))),
            );
            qm31_by_cm31_multiplications += 1;
            additions_or_subtractions += 1;
        }
        residual = residual.sub(opened[(term + 4) % opened_count]);
        alpha_power = alpha_power.mul(alpha);
        accumulator = accumulator.add(alpha_power.mul(residual));
        qm31_multiplications += 2;
        additions_or_subtractions += 2;
    }

    // LogUp helper relation:
    // h(chi-phi_P)(chi-phi_C) - sel_P(chi-phi_C) + sel_C(chi-phi_P).
    for term in 0..probe.logup_degree3_terms as usize {
        let h = opened[term % opened_count];
        let chi = sample(211 + term as u32, 4);
        let left = chi.sub(opened[(term + 1) % opened_count]);
        let right = chi.sub(opened[(term + 2) % opened_count]);
        let residual = h
            .mul(left)
            .mul(right)
            .sub(left.mul(opened[(term + 3) % opened_count]))
            .add(right.mul(opened[(term + 4) % opened_count]));
        alpha_power = alpha_power.mul(alpha);
        accumulator = accumulator.add(alpha_power.mul(residual));
        qm31_multiplications += 6;
        additions_or_subtractions += 6;
    }

    // Boolean/range constraints b(b-1), plus one running reconstruction RLC.
    let mut reconstruction = QM31::ZERO;
    for term in 0..probe.range_bit_terms as usize {
        let bit = opened[term % opened_count];
        let residual = bit.mul(bit.sub(QM31::ONE));
        reconstruction = reconstruction.add(bit.mul_cm31(CM31::from_m31(M31(1u32 << (term % 30)))));
        alpha_power = alpha_power.mul(alpha);
        accumulator = accumulator.add(alpha_power.mul(residual));
        qm31_multiplications += 3;
        qm31_by_cm31_multiplications += 1;
        additions_or_subtractions += 4;
    }
    accumulator = accumulator.add(reconstruction);
    additions_or_subtractions += 1;

    // eq(r,z) for the lr10 zerocheck terminal point.
    let mut eq = QM31::ONE;
    for variable in 0..probe.eq_variables as usize {
        let r = opened[variable % opened_count];
        let z = opened[(variable + 17) % opened_count];
        let factor = r.mul(z).add(QM31::ONE.sub(r).mul(QM31::ONE.sub(z)));
        eq = eq.mul(factor);
        qm31_multiplications += 3;
        additions_or_subtractions += 4;
    }
    alpha_power = alpha_power.mul(alpha);
    accumulator = accumulator.add(alpha_power.mul(eq));
    qm31_multiplications += 2;
    additions_or_subtractions += 1;

    CompositionProbeResult {
        accumulator,
        qm31_multiplications,
        qm31_by_cm31_multiplications,
        additions_or_subtractions,
    }
}

#[cfg(test)]
fn apply_mat4(values: &mut [QM31]) {
    let t01 = values[0].add(values[1]);
    let t23 = values[2].add(values[3]);
    let t0123 = t01.add(t23);
    let t01123 = t0123.add(values[1]);
    let t01233 = t0123.add(values[3]);
    let out3 = t01233.add(values[0].add(values[0]));
    let out1 = t01123.add(values[2].add(values[2]));
    let out0 = t01123.add(t01);
    let out2 = t01233.add(t23);
    values.copy_from_slice(&[out0, out1, out2, out3]);
}

#[cfg(test)]
fn external_linear(values: &mut [QM31; 16]) {
    for chunk in values.chunks_exact_mut(4) {
        apply_mat4(chunk);
    }
    let mut sums = [QM31::ZERO; 4];
    for column in 0..4 {
        for row in 0..4 {
            sums[column] = sums[column].add(values[row * 4 + column]);
        }
    }
    for (index, value) in values.iter_mut().enumerate() {
        *value = value.add(sums[index & 3]);
    }
}

#[inline(always)]
fn linear_combination(values: &[QM31; 4], coefficients: [u64; 4]) -> QM31 {
    let reduce = |limbs: [u32; 4]| {
        M31::reduce_u62(
            limbs[0] as u64 * coefficients[0]
                + limbs[1] as u64 * coefficients[1]
                + limbs[2] as u64 * coefficients[2]
                + limbs[3] as u64 * coefficients[3],
        )
    };
    QM31 {
        c0: CM31 {
            a: reduce(values.map(|value| value.c0.a.0)),
            b: reduce(values.map(|value| value.c0.b.0)),
        },
        c1: CM31 {
            a: reduce(values.map(|value| value.c1.a.0)),
            b: reduce(values.map(|value| value.c1.b.0)),
        },
    }
}

#[inline(always)]
fn apply_mat4_lazy(values: &mut [QM31]) {
    let input: [QM31; 4] = values.try_into().expect("four-lane chunk");
    values.copy_from_slice(&[
        linear_combination(&input, [2, 3, 1, 1]),
        linear_combination(&input, [1, 2, 3, 1]),
        linear_combination(&input, [1, 1, 2, 3]),
        linear_combination(&input, [3, 1, 1, 2]),
    ]);
}

#[inline(always)]
fn external_linear_lazy(values: &mut [QM31; 16]) {
    for chunk in values.chunks_exact_mut(4) {
        apply_mat4_lazy(chunk);
    }
    for column in 0..4 {
        let indices = [column, column + 4, column + 8, column + 12];
        let column_values = indices.map(|index| values[index]);
        let sum = linear_combination(&column_values, [1, 1, 1, 1]);
        for index in indices {
            let value = values[index];
            values[index] = linear_combination(&[value, sum, QM31::ZERO, QM31::ZERO], [1, 1, 0, 0]);
        }
    }
}

#[inline(always)]
fn horner_absorb(accumulator: &mut QM31, alpha: QM31, residual: QM31) {
    *accumulator = accumulator.mul(alpha).add(residual);
}

/// The explicit shrink attempt: share each x^5 across its linear output,
/// use Poseidon2's addition-only MDS network, and compose constraints in
/// Horner form instead of maintaining/multiplying separate alpha powers.
pub fn evaluate_composition_probe_optimized(probe: CompositionProbe) -> CompositionProbeResult {
    let opened_count = usize::from(probe.opened_values.max(1));
    let opened = (0..opened_count)
        .map(|index| sample(index as u32, 1))
        .collect::<Vec<_>>();
    let alpha = sample(91, 2);
    let gamma = sample(97, 3);
    let mut accumulator = QM31::ZERO;
    let mut qm31_multiplications = 0u32;
    let mut qm31_by_cm31_multiplications = 0u32;
    let mut additions_or_subtractions = 0u32;

    // Horner evaluates the same gamma-power RLC with one extension
    // multiplication per opened value instead of two.
    for value in opened.iter().rev() {
        accumulator = accumulator.mul(gamma).add(*value);
        qm31_multiplications += 1;
        additions_or_subtractions += 1;
    }

    let poseidon_outputs = usize::from(probe.poseidon_sbox_terms);
    let mut processed = 0usize;
    while processed < poseidon_outputs {
        let mut state = core::array::from_fn(|lane| {
            opened[(processed + lane) % opened_count].add(QM31::from_cm31(CM31::from_m31(M31(
                1 + (processed + lane) as u32
            ))))
        });
        for value in &mut state {
            let square = value.square();
            let fourth = square.square();
            *value = fourth.mul(*value);
            qm31_multiplications += 3;
        }
        external_linear_lazy(&mut state);
        // Addition network: four mat4 blocks (7 adds each), four 4-way sums
        // (12 adds), and 16 outer additions.
        additions_or_subtractions += 56;
        let take = core::cmp::min(16, poseidon_outputs - processed);
        for lane in 0..take {
            let residual = state[lane].sub(opened[(processed + lane + 16) % opened_count]);
            horner_absorb(&mut accumulator, alpha, residual);
            qm31_multiplications += 1;
            additions_or_subtractions += 2;
        }
        processed += take;
    }

    // Any extra linear/boundary outputs beyond the S-box-backed outputs use
    // shared addition-only four-lane combinations.
    for term in poseidon_outputs..usize::from(probe.poseidon_linear_terms) {
        let residual = opened[term % opened_count]
            .add(opened[(term + 1) % opened_count])
            .add(opened[(term + 2) % opened_count].add(opened[(term + 2) % opened_count]))
            .sub(opened[(term + 3) % opened_count]);
        horner_absorb(&mut accumulator, alpha, residual);
        qm31_multiplications += 1;
        additions_or_subtractions += 5;
    }

    for term in 0..probe.logup_degree3_terms as usize {
        let h = opened[term % opened_count];
        let chi = sample(211 + term as u32, 4);
        let left = chi.sub(opened[(term + 1) % opened_count]);
        let right = chi.sub(opened[(term + 2) % opened_count]);
        let residual = h
            .mul(left)
            .mul(right)
            .sub(left.mul(opened[(term + 3) % opened_count]))
            .add(right.mul(opened[(term + 4) % opened_count]));
        horner_absorb(&mut accumulator, alpha, residual);
        qm31_multiplications += 5;
        additions_or_subtractions += 6;
    }

    let mut reconstruction = QM31::ZERO;
    let mut binary_weight = M31::ONE;
    for term in 0..probe.range_bit_terms as usize {
        let bit = opened[term % opened_count];
        let residual = bit.mul(bit.sub(QM31::ONE));
        reconstruction = reconstruction.add(bit.mul_cm31(CM31::from_m31(binary_weight)));
        binary_weight = binary_weight.double();
        if term % 30 == 29 {
            binary_weight = M31::ONE;
        }
        horner_absorb(&mut accumulator, alpha, residual);
        qm31_multiplications += 2;
        qm31_by_cm31_multiplications += 1;
        additions_or_subtractions += 4;
    }
    if probe.range_bit_terms > 0 {
        horner_absorb(&mut accumulator, alpha, reconstruction);
        qm31_multiplications += 1;
        additions_or_subtractions += 1;
    }

    let mut eq = QM31::ONE;
    for variable in 0..probe.eq_variables as usize {
        let r = opened[variable % opened_count];
        let z = opened[(variable + 17) % opened_count];
        let factor = r.mul(z).add(QM31::ONE.sub(r).mul(QM31::ONE.sub(z)));
        eq = eq.mul(factor);
        qm31_multiplications += 3;
        additions_or_subtractions += 4;
    }
    if probe.eq_variables > 0 {
        horner_absorb(&mut accumulator, alpha, eq);
        qm31_multiplications += 1;
        additions_or_subtractions += 1;
    }

    CompositionProbeResult {
        accumulator,
        qm31_multiplications,
        qm31_by_cm31_multiplications,
        additions_or_subtractions,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bracket_is_monotone_in_operation_counts() {
        let optimistic = evaluate_composition_probe(CompositionProbe::OPTIMISTIC);
        let realistic = evaluate_composition_probe(CompositionProbe::REALISTIC);
        let pessimistic = evaluate_composition_probe(CompositionProbe::PESSIMISTIC);
        assert!(optimistic.qm31_multiplications < realistic.qm31_multiplications);
        assert!(realistic.qm31_multiplications < pessimistic.qm31_multiplications);
        assert_ne!(optimistic.accumulator, realistic.accumulator);
        assert_ne!(realistic.accumulator, pessimistic.accumulator);
    }

    #[test]
    fn structured_kernel_reduces_realistic_multiplications() {
        let naive = evaluate_composition_probe(CompositionProbe::REALISTIC);
        let optimized = evaluate_composition_probe_optimized(CompositionProbe::REALISTIC);
        assert!(optimized.qm31_multiplications < naive.qm31_multiplications);
        assert!(optimized.qm31_by_cm31_multiplications < naive.qm31_by_cm31_multiplications);
    }

    #[test]
    fn lazy_extension_linear_layer_matches_canonical() {
        for seed in 0..32u32 {
            let mut canonical = core::array::from_fn(|lane| sample(seed * 16 + lane as u32, 9));
            let mut lazy = canonical;
            external_linear(&mut canonical);
            external_linear_lazy(&mut lazy);
            assert_eq!(lazy, canonical);
        }
    }
}
