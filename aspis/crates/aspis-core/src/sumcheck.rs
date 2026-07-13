//! Interleaved linear-relation sumcheck for the arity-4 coefficient fold.
//!
//! For each four-coefficient chunk, let
//! `A(X) = a0 + a1 X + a2 X^2 + a3 X^3`. The PCS fold stores `A(alpha)`.
//! Given linear weights `(b0..b3)`, define the dual polynomial
//! `B(X) = (b0 + b3 X + b2 X^2 + b1 X^3) / 4`. Summing `A(X)B(X)` over the
//! four fourth roots of unity returns `sum_t a_t b_t`; evaluating it at the
//! transcript challenge returns the same relation on the folded vector.
//! Thus one degree-6 polynomial per committed layer carries an arbitrary
//! batched linear claim down to the explicit final coefficients.

use alloc::vec::Vec;

use crate::circle::{double_x, SecureCirclePoint};
use crate::field::{qm31_sum_products2_prepared, PreparedQm31Multiplier, M31_QUARTER, QM31};
use crate::verify::EvaluationClaim;

pub const SUMCHECK_COEFFICIENTS: usize = 7;
pub const SUMCHECK_BYTES: usize = SUMCHECK_COEFFICIENTS * 16;
pub type SumcheckPolynomial = [QM31; SUMCHECK_COEFFICIENTS];

#[derive(Clone, Debug)]
enum WeightComponent {
    /// scale * base^index (univariate evaluation at `base`).
    Geometric { scale: QM31, base: QM31 },
    /// scale * eq(point, index_bits), with big-endian coordinate order.
    Multilinear { scale: QM31, point: Vec<QM31> },
    /// `scale * product(factor_j^bit_j)` with factors stored in big-endian
    /// coefficient-index order. The tail contains the low index bits: a
    /// circle point is `[..., pi(x), x, y]`; a line point is
    /// `[..., pi(x), x]`.
    Tensor { scale: QM31, factors: Vec<QM31> },
    /// `scale * product(pair_j[index_bit_j])`. This represents sparse
    /// subcube indicators without materializing a full covector; unlike the
    /// Tensor variant, either zero-bit weight may itself be zero.
    Product { scale: QM31, pairs: Vec<[QM31; 2]> },
    /// An exact arbitrary public covector. This is intended for small
    /// coefficient domains (the state-only relation has 1024 entries) whose
    /// selector is not a short union of Boolean subcubes. After the first
    /// dual fold it shrinks to 256 QM31 values.
    Dense { values: Vec<QM31> },
    /// A 64-by-16 binary matrix whose rows draw from a small set of distinct
    /// low masks. The first two arity-four dual folds are shared per distinct
    /// mask; after the low dimension disappears this becomes an ordinary
    /// 64-value Dense component.
    Grouped64x16 {
        row_groups: Vec<u8>,
        group_values: Vec<QM31>,
        low_width: u8,
    },
    /// The same 64-by-16 binary matrix as `Grouped64x16`, but retain the
    /// eight-or-fewer distinct masks through the first dual fold.  The next
    /// fold evaluates the complete 16-entry low mask from nine cross-products
    /// of the two rounds' challenge powers, then expands directly to the
    /// 64-entry high covector.  No verifier code observes the intermediate
    /// covector between relation folds, but `weight_at` still implements it
    /// exactly so random-point identity tests can compare both paths after
    /// every round.
    Grouped64x16BinaryDeferred {
        row_groups: Vec<u8>,
        group_masks: Vec<u16>,
        first_alpha: Option<QM31>,
    },
    /// Log-11 analogue of `Grouped64x16`. The lower 1024 entries use the
    /// generated inactive masks and the upper 1024 entries may share the
    /// all-zero group. After two dual folds it becomes a 128-value Dense
    /// component, avoiding a 2048-value SBF allocation and walk.
    Grouped128x16 {
        row_groups: Vec<u8>,
        group_values: Vec<QM31>,
        low_width: u8,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TensorWeightError {
    /// A multilinear point must have exactly one coordinate per live bit.
    MultilinearPointLength,
    /// A generic factor vector must have exactly one factor per live bit.
    FactorCount,
    /// Circle coefficients require at least the low `y` and `x` factors.
    CircleLogLength,
    /// Sparse interval must satisfy `start < end <= 2^log_len`.
    IndexInterval,
    /// A dense covector must have exactly `2^log_len` entries.
    DenseLength,
    /// Grouped 64-by-16 masks are defined only at log length ten.
    Grouped64x16LogLength,
    /// The 128-by-16 grouped form is defined only at log length eleven.
    Grouped128x16LogLength,
}

/// Compact sum of structured linear forms. It avoids materializing a full
/// QM31 weight vector in the SBF verifier (which would exceed the heap for
/// the lr14 diagnostic).
#[derive(Clone, Debug)]
pub struct WeightAccumulator {
    log_len: u32,
    components: Vec<WeightComponent>,
}

impl WeightAccumulator {
    pub fn empty(log_len: u32) -> Self {
        Self {
            log_len,
            components: Vec::new(),
        }
    }

    pub fn from_claim(log_len: u32, claim: Option<&EvaluationClaim>) -> Self {
        let mut out = Self::empty(log_len);
        if let Some(claim) = claim {
            debug_assert_eq!(claim.z.len(), log_len as usize);
            out.components.push(WeightComponent::Multilinear {
                scale: QM31::ONE,
                point: claim.z.clone(),
            });
        }
        out
    }

    /// Add `scale * [1, base, base^2, ...]`, the coefficient-linear form for
    /// a univariate evaluation at `base`.
    pub fn add_geometric(&mut self, scale: QM31, base: QM31) {
        self.components
            .push(WeightComponent::Geometric { scale, base });
    }

    /// Add `scale * eq(point, index_bits)` in the same big-endian coordinate
    /// order used by [`EvaluationClaim`]. This is the scaled, shape-checked
    /// form needed when more than one MLE evaluation is carried in one
    /// relation accumulator.
    pub fn add_multilinear(
        &mut self,
        scale: QM31,
        point: Vec<QM31>,
    ) -> Result<(), TensorWeightError> {
        if point.len() != self.log_len as usize {
            return Err(TensorWeightError::MultilinearPointLength);
        }
        self.components
            .push(WeightComponent::Multilinear { scale, point });
        Ok(())
    }

    /// Add generic tensor-product coefficient weights. `factors` are in
    /// big-endian index-bit order, so the last factor is selected by bit 0.
    pub fn add_tensor_factors(
        &mut self,
        scale: QM31,
        factors: Vec<QM31>,
    ) -> Result<(), TensorWeightError> {
        if factors.len() != self.log_len as usize {
            return Err(TensorWeightError::FactorCount);
        }
        self.components
            .push(WeightComponent::Tensor { scale, factors });
        Ok(())
    }

    pub fn add_product_pairs(
        &mut self,
        scale: QM31,
        pairs: Vec<[QM31; 2]>,
    ) -> Result<(), TensorWeightError> {
        if pairs.len() != self.log_len as usize {
            return Err(TensorWeightError::FactorCount);
        }
        self.components
            .push(WeightComponent::Product { scale, pairs });
        Ok(())
    }

    /// Add a half-open coefficient-index interval as a short union of aligned
    /// Boolean subcubes. Each dyadic block becomes one Product component.
    pub fn add_index_interval(
        &mut self,
        scale: QM31,
        start: usize,
        end: usize,
    ) -> Result<(), TensorWeightError> {
        let size = 1usize << self.log_len;
        if start >= end || end > size {
            return Err(TensorWeightError::IndexInterval);
        }
        let mut cursor = start;
        while cursor < end {
            let remaining = end - cursor;
            let mut block = if cursor == 0 {
                1usize << (usize::BITS - 1 - remaining.leading_zeros())
            } else {
                cursor & cursor.wrapping_neg()
            };
            while block > remaining {
                block >>= 1;
            }
            let free_bits = block.trailing_zeros() as usize;
            let fixed_bits = self.log_len as usize - free_bits;
            let mut pairs = Vec::with_capacity(self.log_len as usize);
            for coordinate in 0..fixed_bits {
                let bit = (cursor >> (self.log_len as usize - 1 - coordinate)) & 1;
                pairs.push(if bit == 0 {
                    [QM31::ONE, QM31::ZERO]
                } else {
                    [QM31::ZERO, QM31::ONE]
                });
            }
            pairs.extend((0..free_bits).map(|_| [QM31::ONE, QM31::ONE]));
            self.add_product_pairs(scale, pairs)?;
            cursor += block;
        }
        Ok(())
    }

    /// Add an arbitrary exact public covector. The values are coefficient
    /// weights in natural index order and are dual-folded in place with the
    /// same arity-4 normalization as every structured component.
    pub fn add_dense(&mut self, values: Vec<QM31>) -> Result<(), TensorWeightError> {
        if values.len() != 1usize << self.log_len {
            return Err(TensorWeightError::DenseLength);
        }
        self.components.push(WeightComponent::Dense { values });
        Ok(())
    }

    /// Add an exact 64-by-16 binary covector, deduplicating identical low
    /// masks. This is useful for fixed layouts with many repeated row shapes;
    /// it is algebraically identical to adding the corresponding 1024-value
    /// Dense component.
    pub fn add_grouped_64x16_binary_masks(
        &mut self,
        row_masks: [u16; 64],
    ) -> Result<(), TensorWeightError> {
        if self.log_len != 10 {
            return Err(TensorWeightError::Grouped64x16LogLength);
        }
        let mut unique_masks = Vec::<u16>::new();
        let mut row_groups = Vec::with_capacity(64);
        for mask in row_masks {
            let group = unique_masks
                .iter()
                .position(|&candidate| candidate == mask)
                .unwrap_or_else(|| {
                    unique_masks.push(mask);
                    unique_masks.len() - 1
                });
            row_groups.push(group as u8);
        }
        let mut group_values = Vec::with_capacity(unique_masks.len() * 16);
        for mask in unique_masks {
            group_values.extend((0..16).map(|low| {
                if mask & (1 << low) == 0 {
                    QM31::ZERO
                } else {
                    QM31::ONE
                }
            }));
        }
        self.components.push(WeightComponent::Grouped64x16 {
            row_groups,
            group_values,
            low_width: 16,
        });
        Ok(())
    }

    /// Exact binary specialization of [`Self::add_grouped_64x16_binary_masks`].
    ///
    /// This changes only how the fixed public covector is evaluated.  Its
    /// value before folding, after either of the first two folds, and after
    /// all later folds is identical to the legacy grouped component.
    pub fn add_grouped_64x16_binary_masks_deferred(
        &mut self,
        row_masks: [u16; 64],
    ) -> Result<(), TensorWeightError> {
        if self.log_len != 10 {
            return Err(TensorWeightError::Grouped64x16LogLength);
        }
        let mut group_masks = Vec::<u16>::new();
        let mut row_groups = Vec::with_capacity(64);
        for mask in row_masks {
            let group = group_masks
                .iter()
                .position(|&candidate| candidate == mask)
                .unwrap_or_else(|| {
                    group_masks.push(mask);
                    group_masks.len() - 1
                });
            row_groups.push(group as u8);
        }
        self.components
            .push(WeightComponent::Grouped64x16BinaryDeferred {
                row_groups,
                group_masks,
                first_alpha: None,
            });
        Ok(())
    }

    pub fn add_grouped_128x16_binary_masks(
        &mut self,
        row_masks: [u16; 128],
    ) -> Result<(), TensorWeightError> {
        if self.log_len != 11 {
            return Err(TensorWeightError::Grouped128x16LogLength);
        }
        let mut unique_masks = Vec::<u16>::new();
        let mut row_groups = Vec::with_capacity(128);
        for mask in row_masks {
            let group = unique_masks
                .iter()
                .position(|&candidate| candidate == mask)
                .unwrap_or_else(|| {
                    unique_masks.push(mask);
                    unique_masks.len() - 1
                });
            row_groups.push(group as u8);
        }
        let mut group_values = Vec::with_capacity(unique_masks.len() * 16);
        for mask in unique_masks {
            group_values.extend((0..16).map(|low| {
                if mask & (1 << low) == 0 {
                    QM31::ZERO
                } else {
                    QM31::ONE
                }
            }));
        }
        self.components.push(WeightComponent::Grouped128x16 {
            row_groups,
            group_values,
            low_width: 16,
        });
        Ok(())
    }

    /// Add circle-polynomial evaluation weights in stored order
    /// `[..., pi(x), x, y]`. The coefficient-index low bits therefore
    /// evaluate `y` first and `x` second, matching the circle FFT basis.
    pub fn add_circle_tensor(
        &mut self,
        scale: QM31,
        point: SecureCirclePoint,
    ) -> Result<(), TensorWeightError> {
        if self.log_len < 2 {
            return Err(TensorWeightError::CircleLogLength);
        }
        let mut factors = Vec::with_capacity(self.log_len as usize);
        factors.push(point.y);
        factors.push(point.x);
        let mut x = point.x;
        for _ in 2..self.log_len {
            x = double_x(x);
            factors.push(x);
        }
        factors.reverse();
        self.add_tensor_factors(scale, factors)
    }

    /// Add line-polynomial evaluation weights in stored order
    /// `[..., pi(x), x]`. Later PCS layers use this constructor with their
    /// direct exact-uniform QM31 line sample; they do not reuse the rational
    /// circle sampler's nonuniform x marginal.
    pub fn add_line_tensor(&mut self, scale: QM31, mut x: QM31) -> Result<(), TensorWeightError> {
        let mut factors = Vec::with_capacity(self.log_len as usize);
        for coordinate in 0..self.log_len {
            factors.push(x);
            if coordinate + 1 < self.log_len {
                x = double_x(x);
            }
        }
        factors.reverse();
        self.add_tensor_factors(scale, factors)
    }

    pub fn weight_at(&self, index: u32) -> QM31 {
        debug_assert!(index < (1u32 << self.log_len));
        let mut total = QM31::ZERO;
        for component in &self.components {
            let value = match component {
                WeightComponent::Geometric { scale, base } => scale.mul(base.pow(index as u64)),
                WeightComponent::Multilinear { scale, point } => {
                    let mut value = *scale;
                    for (coordinate, z) in point.iter().enumerate() {
                        let bit = (index >> (point.len() - 1 - coordinate)) & 1;
                        value = if bit == 0 {
                            value.mul(QM31::ONE.sub(*z))
                        } else {
                            value.mul(*z)
                        };
                    }
                    value
                }
                WeightComponent::Tensor { scale, factors } => {
                    let mut value = *scale;
                    for (coordinate, factor) in factors.iter().enumerate() {
                        let bit = (index >> (factors.len() - 1 - coordinate)) & 1;
                        if bit != 0 {
                            value = value.mul(*factor);
                        }
                    }
                    value
                }
                WeightComponent::Product { scale, pairs } => {
                    let mut value = *scale;
                    for (coordinate, pair) in pairs.iter().enumerate() {
                        let bit = ((index >> (pairs.len() - 1 - coordinate)) & 1) as usize;
                        value = value.mul(pair[bit]);
                    }
                    value
                }
                WeightComponent::Dense { values } => values[index as usize],
                WeightComponent::Grouped64x16 {
                    row_groups,
                    group_values,
                    low_width,
                } => {
                    let low_width = usize::from(*low_width);
                    let high = index as usize / low_width;
                    let low = index as usize & (low_width - 1);
                    let group = usize::from(row_groups[high]);
                    group_values[group * low_width + low]
                }
                WeightComponent::Grouped64x16BinaryDeferred {
                    row_groups,
                    group_masks,
                    first_alpha,
                } => {
                    if let Some(alpha) = first_alpha {
                        debug_assert_eq!(self.log_len, 8);
                        let high = index as usize / 4;
                        let low_chunk = index as usize & 3;
                        let mask = group_masks[usize::from(row_groups[high])];
                        let bits = (mask >> (4 * low_chunk)) & 0x0f;
                        let alpha2 = alpha.square();
                        let alpha3 = alpha2.mul(*alpha);
                        let powers = [QM31::ONE, alpha3, alpha2, *alpha];
                        powers
                            .iter()
                            .enumerate()
                            .filter(|(slot, _)| bits & (1 << slot) != 0)
                            .fold(QM31::ZERO, |sum, (_, power)| sum.add(*power))
                            .half()
                            .half()
                    } else {
                        debug_assert_eq!(self.log_len, 10);
                        let high = index as usize / 16;
                        let low = index as usize & 15;
                        let mask = group_masks[usize::from(row_groups[high])];
                        if mask & (1 << low) == 0 {
                            QM31::ZERO
                        } else {
                            QM31::ONE
                        }
                    }
                }
                WeightComponent::Grouped128x16 {
                    row_groups,
                    group_values,
                    low_width,
                } => {
                    let low_width = usize::from(*low_width);
                    let high = index as usize / low_width;
                    let low = index as usize & (low_width - 1);
                    let group = usize::from(row_groups[high]);
                    group_values[group * low_width + low]
                }
            };
            total = total.add(value);
        }
        total
    }

    /// Materialize a short natural-order prefix of the current covector in
    /// one traversal per structured component. This is exact
    /// `core::array::from_fn(|i| self.weight_at(i))`, but avoids replaying all
    /// tensor factors independently for every index. Profile 21 needs only
    /// indices `0..35` immediately after round zero.
    pub fn weight_prefix<const N: usize>(&self) -> [QM31; N] {
        debug_assert!(N <= 1usize << self.log_len);

        fn add_product_prefix<const N: usize>(
            output: &mut [QM31; N],
            pairs: &[[QM31; 2]],
            coordinate: usize,
            index: usize,
            value: QM31,
        ) {
            if coordinate == pairs.len() {
                output[index] = output[index].add(value);
                return;
            }
            let bit = pairs.len() - 1 - coordinate;
            add_product_prefix(
                output,
                pairs,
                coordinate + 1,
                index,
                value.mul(pairs[coordinate][0]),
            );
            let one_index = index | (1usize << bit);
            if one_index < N {
                add_product_prefix(
                    output,
                    pairs,
                    coordinate + 1,
                    one_index,
                    value.mul(pairs[coordinate][1]),
                );
            }
        }

        let mut output = [QM31::ZERO; N];
        for component in &self.components {
            match component {
                WeightComponent::Geometric { scale, base } => {
                    let mut value = *scale;
                    for item in &mut output {
                        *item = item.add(value);
                        value = value.mul(*base);
                    }
                }
                WeightComponent::Multilinear { scale, point } => {
                    let pairs = point
                        .iter()
                        .map(|&value| [QM31::ONE.sub(value), value])
                        .collect::<Vec<_>>();
                    add_product_prefix(&mut output, &pairs, 0, 0, *scale);
                }
                WeightComponent::Tensor { scale, factors } => {
                    let mut values = [QM31::ZERO; N];
                    if N != 0 {
                        values[0] = *scale;
                    }
                    for index in 1..N {
                        let bit = index.trailing_zeros() as usize;
                        let prefix = index ^ (1usize << bit);
                        values[index] = values[prefix].mul(factors[factors.len() - 1 - bit]);
                    }
                    for (item, value) in output.iter_mut().zip(values) {
                        *item = item.add(value);
                    }
                }
                WeightComponent::Product { scale, pairs } => {
                    add_product_prefix(&mut output, pairs, 0, 0, *scale);
                }
                WeightComponent::Dense { values } => {
                    for (item, &value) in output.iter_mut().zip(values) {
                        *item = item.add(value);
                    }
                }
                WeightComponent::Grouped64x16 {
                    row_groups,
                    group_values,
                    low_width,
                } => {
                    let width = usize::from(*low_width);
                    for (index, item) in output.iter_mut().enumerate() {
                        let group = usize::from(row_groups[index / width]);
                        *item = item.add(group_values[group * width + index % width]);
                    }
                }
                WeightComponent::Grouped64x16BinaryDeferred {
                    row_groups,
                    group_masks,
                    first_alpha,
                } => {
                    if let Some(alpha) = first_alpha {
                        debug_assert_eq!(self.log_len, 8);
                        let alpha2 = alpha.square();
                        let powers = [QM31::ONE, alpha2.mul(*alpha), alpha2, *alpha];
                        for (index, item) in output.iter_mut().enumerate() {
                            let high = index / 4;
                            let low_chunk = index & 3;
                            let mask = group_masks[usize::from(row_groups[high])];
                            let bits = (mask >> (4 * low_chunk)) & 0x0f;
                            let value = powers
                                .iter()
                                .enumerate()
                                .filter(|(slot, _)| bits & (1 << slot) != 0)
                                .fold(QM31::ZERO, |sum, (_, power)| sum.add(*power))
                                .half()
                                .half();
                            *item = item.add(value);
                        }
                    } else {
                        debug_assert_eq!(self.log_len, 10);
                        for (index, item) in output.iter_mut().enumerate() {
                            let high = index / 16;
                            let low = index & 15;
                            let mask = group_masks[usize::from(row_groups[high])];
                            if mask & (1 << low) != 0 {
                                *item = item.add(QM31::ONE);
                            }
                        }
                    }
                }
                WeightComponent::Grouped128x16 {
                    row_groups,
                    group_values,
                    low_width,
                } => {
                    let width = usize::from(*low_width);
                    for (index, item) in output.iter_mut().enumerate() {
                        let group = usize::from(row_groups[index / width]);
                        *item = item.add(group_values[group * width + index % width]);
                    }
                }
            }
        }
        output
    }

    /// Apply the dual of the arity-4 monomial coefficient fold.
    pub fn fold(&mut self, alpha: QM31) {
        debug_assert!(self.log_len >= 2);
        let current_log_len = self.log_len;
        let alpha2 = alpha.square();
        let prepared_alpha = PreparedQm31Multiplier::new(alpha);
        let prepared_alpha2 = PreparedQm31Multiplier::new(alpha2);
        let alpha3 = prepared_alpha.mul(alpha2);
        for component in &mut self.components {
            match component {
                WeightComponent::Geometric { scale, base } => {
                    let base2 = base.square();
                    let base3 = base2.mul(*base);
                    let factor = QM31::ONE
                        .add(alpha3.mul(*base))
                        .add(alpha2.mul(base2))
                        .add(alpha.mul(base3))
                        .half()
                        .half();
                    *scale = scale.mul(factor);
                    *base = base2.square();
                }
                WeightComponent::Multilinear { scale, point } => {
                    let split = point.len() - 2;
                    let z0 = point[split];
                    let z1 = point[split + 1];
                    // Interpolate first in z1 and then z0. This is exactly
                    // b0 + alpha^3*b1 + alpha^2*b2 + alpha*b3, but avoids
                    // materializing all four multilinear basis weights.
                    let low = QM31::ONE.add(alpha3.sub(QM31::ONE).mul(z1));
                    let high = alpha2.add(alpha.sub(alpha2).mul(z1));
                    let factor = low.add(z0.mul(high.sub(low))).half().half();
                    *scale = scale.mul(factor);
                    point.truncate(split);
                }
                WeightComponent::Tensor { scale, factors } => {
                    let split = factors.len() - 2;
                    let high = factors[split];
                    let low = factors[split + 1];
                    // For weights [b0,b1,b2,b3] =
                    // scale*[1,low,high,high*low], the arity-4 dual is
                    // (b0 + alpha^3*b1 + alpha^2*b2 + alpha*b3) / 4.
                    // 1 + alpha^3*low + alpha^2*high + alpha*high*low,
                    // grouped to reuse the high product.
                    let prepared = [prepared_alpha2, PreparedQm31Multiplier::new(low)];
                    let products = qm31_sum_products2_prepared(
                        &prepared,
                        &[high, alpha3.add(prepared_alpha.mul(high))],
                    );
                    let factor = QM31::ONE.add(products).half().half();
                    *scale = scale.mul(factor);
                    factors.truncate(split);
                }
                WeightComponent::Product { scale, pairs } => {
                    let split = pairs.len() - 2;
                    let high = pairs[split];
                    let low = pairs[split + 1];
                    let factor = high[0]
                        .mul(low[0])
                        .add(alpha3.mul(high[0].mul(low[1])))
                        .add(alpha2.mul(high[1].mul(low[0])))
                        .add(alpha.mul(high[1].mul(low[1])))
                        .half()
                        .half();
                    *scale = scale.mul(factor);
                    pairs.truncate(split);
                }
                WeightComponent::Dense { values } => {
                    let folded = values
                        .chunks_exact(4)
                        .map(|chunk| {
                            chunk[0]
                                .add(alpha3.mul(chunk[1]))
                                .add(alpha2.mul(chunk[2]))
                                .add(alpha.mul(chunk[3]))
                                .half()
                                .half()
                        })
                        .collect();
                    *values = folded;
                }
                WeightComponent::Grouped64x16 {
                    row_groups,
                    group_values,
                    low_width,
                } => {
                    debug_assert!(matches!(self.log_len, 10 | 8));
                    let folded = group_values
                        .chunks_exact(4)
                        .map(|chunk| {
                            chunk[0]
                                .add(alpha3.mul(chunk[1]))
                                .add(alpha2.mul(chunk[2]))
                                .add(alpha.mul(chunk[3]))
                                .half()
                                .half()
                        })
                        .collect::<Vec<_>>();
                    if *low_width == 16 {
                        *group_values = folded;
                        *low_width = 4;
                    } else {
                        debug_assert_eq!(*low_width, 4);
                        let values = row_groups
                            .iter()
                            .map(|&group| folded[usize::from(group)])
                            .collect();
                        *component = WeightComponent::Dense { values };
                    }
                }
                WeightComponent::Grouped64x16BinaryDeferred {
                    row_groups,
                    group_masks,
                    first_alpha,
                } => {
                    if let Some(alpha0) = *first_alpha {
                        debug_assert_eq!(current_log_len, 8);
                        let alpha0_2 = alpha0.square();
                        let alpha0_powers = [QM31::ONE, alpha0_2.mul(alpha0), alpha0_2, alpha0];
                        let alpha1_2 = alpha2;
                        let alpha1_powers = [QM31::ONE, alpha3, alpha1_2, alpha];
                        let low_basis: [QM31; 16] = core::array::from_fn(|low| {
                            let high_slot = low >> 2;
                            let low_slot = low & 3;
                            let product = if high_slot == 0 {
                                alpha0_powers[low_slot]
                            } else if low_slot == 0 {
                                alpha1_powers[high_slot]
                            } else {
                                alpha1_powers[high_slot].mul(alpha0_powers[low_slot])
                            };
                            product.half().half().half().half()
                        });
                        let group_values = group_masks
                            .iter()
                            .map(|mask| {
                                low_basis
                                    .iter()
                                    .enumerate()
                                    .filter(|(low, _)| mask & (1 << low) != 0)
                                    .fold(QM31::ZERO, |sum, (_, value)| sum.add(*value))
                            })
                            .collect::<Vec<_>>();
                        let values = row_groups
                            .iter()
                            .map(|&group| group_values[usize::from(group)])
                            .collect();
                        *component = WeightComponent::Dense { values };
                    } else {
                        debug_assert_eq!(current_log_len, 10);
                        *first_alpha = Some(alpha);
                    }
                }
                WeightComponent::Grouped128x16 {
                    row_groups,
                    group_values,
                    low_width,
                } => {
                    debug_assert!(matches!(self.log_len, 11 | 9));
                    let folded = group_values
                        .chunks_exact(4)
                        .map(|chunk| {
                            chunk[0]
                                .add(alpha3.mul(chunk[1]))
                                .add(alpha2.mul(chunk[2]))
                                .add(alpha.mul(chunk[3]))
                                .half()
                                .half()
                        })
                        .collect::<Vec<_>>();
                    if *low_width == 16 {
                        *group_values = folded;
                        *low_width = 4;
                    } else {
                        debug_assert_eq!(*low_width, 4);
                        let values = row_groups
                            .iter()
                            .map(|&group| folded[usize::from(group)])
                            .collect();
                        *component = WeightComponent::Dense { values };
                    }
                }
            }
        }
        self.log_len -= 2;
    }

    /// Host-probe implementation of the dual of an arity-8 monomial fold.
    ///
    /// For coefficient chunks `A(X)=sum_{i=0}^7 a_i X^i`, the primal fold
    /// stores `A(alpha)`.  The corresponding dual chunk is
    /// `(b_0 + alpha^7 b_1 + ... + alpha b_7) / 8`.  This deliberately
    /// materializes the current covector and replaces it by one dense
    /// component; it exists for structural rank experiments and is not an
    /// SBF optimization primitive.
    pub fn fold_arity8_materialized_for_probe(&mut self, alpha: QM31) {
        debug_assert!(self.log_len >= 3);
        let inverse_eight = crate::field::M31(8).inv();
        let powers: [QM31; 8] = core::array::from_fn(|exponent| alpha.pow(exponent as u64));
        let size = 1usize << self.log_len;
        let folded = (0..size / 8)
            .map(|chunk| {
                (0..8)
                    .fold(QM31::ZERO, |sum, slot| {
                        let exponent = if slot == 0 { 0 } else { 8 - slot };
                        sum.add(
                            self.weight_at((8 * chunk + slot) as u32)
                                .mul(powers[exponent]),
                        )
                    })
                    .mul_m31(inverse_eight)
            })
            .collect();
        self.components = alloc::vec![WeightComponent::Dense { values: folded }];
        self.log_len -= 3;
    }

    pub fn dot(&self, values: &[QM31]) -> QM31 {
        debug_assert_eq!(values.len(), 1usize << self.log_len);
        if self.log_len == 2 && values.len() == 4 {
            let mut total = QM31::ZERO;
            for component in &self.components {
                let contribution = match component {
                    WeightComponent::Geometric { scale, base } => {
                        let base2 = base.square();
                        let evaluation = values[0]
                            .add(base.mul(values[1]))
                            .add(base2.mul(values[2]))
                            .add(base2.mul(*base).mul(values[3]));
                        scale.mul(evaluation)
                    }
                    WeightComponent::Multilinear { scale, point } => {
                        debug_assert_eq!(point.len(), 2);
                        let low = values[0].add(point[1].mul(values[1].sub(values[0])));
                        let high = values[2].add(point[1].mul(values[3].sub(values[2])));
                        scale.mul(low.add(point[0].mul(high.sub(low))))
                    }
                    WeightComponent::Tensor { scale, factors } => {
                        debug_assert_eq!(factors.len(), 2);
                        let low = values[0].add(factors[1].mul(values[1]));
                        let high = values[2].add(factors[1].mul(values[3]));
                        scale.mul(low.add(factors[0].mul(high)))
                    }
                    WeightComponent::Product { scale, pairs } => {
                        debug_assert_eq!(pairs.len(), 2);
                        let evaluation = values[0]
                            .mul(pairs[0][0].mul(pairs[1][0]))
                            .add(values[1].mul(pairs[0][0].mul(pairs[1][1])))
                            .add(values[2].mul(pairs[0][1].mul(pairs[1][0])))
                            .add(values[3].mul(pairs[0][1].mul(pairs[1][1])));
                        scale.mul(evaluation)
                    }
                    WeightComponent::Dense { values: weights } => values
                        .iter()
                        .zip(weights)
                        .fold(QM31::ZERO, |sum, (value, weight)| {
                            sum.add(value.mul(*weight))
                        }),
                    WeightComponent::Grouped64x16 { .. } => {
                        unreachable!("grouped component becomes dense before log length two")
                    }
                    WeightComponent::Grouped64x16BinaryDeferred { .. } => {
                        unreachable!(
                            "deferred binary component becomes dense before log length two"
                        )
                    }
                    WeightComponent::Grouped128x16 { .. } => {
                        unreachable!("grouped component becomes dense before log length two")
                    }
                };
                total = total.add(contribution);
            }
            return total;
        }
        values
            .iter()
            .enumerate()
            .fold(QM31::ZERO, |sum, (index, value)| {
                sum.add(value.mul(self.weight_at(index as u32)))
            })
    }
}

fn accumulate_chunk(output: &mut SumcheckPolynomial, values: [QM31; 4], weights: [QM31; 4]) {
    // B coefficients are [b0, b3, b2, b1] / 4.
    let dual = [weights[0], weights[3], weights[2], weights[1]];
    for (a_degree, value) in values.iter().enumerate() {
        for (b_degree, weight) in dual.iter().enumerate() {
            output[a_degree + b_degree] =
                output[a_degree + b_degree].add(value.mul(*weight).mul_m31(M31_QUARTER));
        }
    }
}

pub fn polynomial_for_base(
    coefficients: &[crate::field::M31],
    weights: &WeightAccumulator,
) -> SumcheckPolynomial {
    debug_assert_eq!(coefficients.len(), 1usize << weights.log_len);
    let mut output = [QM31::ZERO; SUMCHECK_COEFFICIENTS];
    for (chunk_index, chunk) in coefficients.chunks_exact(4).enumerate() {
        let base = (chunk_index * 4) as u32;
        accumulate_chunk(
            &mut output,
            [
                QM31::from_cm31(crate::field::CM31::from_m31(chunk[0])),
                QM31::from_cm31(crate::field::CM31::from_m31(chunk[1])),
                QM31::from_cm31(crate::field::CM31::from_m31(chunk[2])),
                QM31::from_cm31(crate::field::CM31::from_m31(chunk[3])),
            ],
            [
                weights.weight_at(base),
                weights.weight_at(base + 1),
                weights.weight_at(base + 2),
                weights.weight_at(base + 3),
            ],
        );
    }
    output
}

pub fn polynomial_for_extension(
    coefficients: &[QM31],
    weights: &WeightAccumulator,
) -> SumcheckPolynomial {
    debug_assert_eq!(coefficients.len(), 1usize << weights.log_len);
    let mut output = [QM31::ZERO; SUMCHECK_COEFFICIENTS];
    for (chunk_index, chunk) in coefficients.chunks_exact(4).enumerate() {
        let base = (chunk_index * 4) as u32;
        accumulate_chunk(
            &mut output,
            [chunk[0], chunk[1], chunk[2], chunk[3]],
            [
                weights.weight_at(base),
                weights.weight_at(base + 1),
                weights.weight_at(base + 2),
                weights.weight_at(base + 3),
            ],
        );
    }
    output
}

/// Sum over the four fourth roots of unity. For degree <= 6, only
/// coefficients 0 and 4 survive the root-of-unity filter.
pub fn boundary_sum(polynomial: &SumcheckPolynomial) -> QM31 {
    polynomial[0]
        .add(polynomial[4])
        .mul_m31(crate::field::M31(4))
}

pub fn evaluate(polynomial: &SumcheckPolynomial, point: QM31) -> QM31 {
    polynomial
        .iter()
        .rev()
        .fold(QM31::ZERO, |acc, coefficient| {
            acc.mul(point).add(*coefficient)
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circle::secure_circle_point_from_parameter;
    use crate::field::{CM31, M31};
    use alloc::vec;

    fn q(value: u32) -> QM31 {
        QM31::from_cm31(CM31::from_m31(M31(value)))
    }

    fn fold_values(values: &[QM31], alpha: QM31) -> Vec<QM31> {
        let alpha2 = alpha.mul(alpha);
        let alpha3 = alpha2.mul(alpha);
        values
            .chunks_exact(4)
            .map(|chunk| {
                chunk[0]
                    .add(alpha.mul(chunk[1]))
                    .add(alpha2.mul(chunk[2]))
                    .add(alpha3.mul(chunk[3]))
            })
            .collect()
    }

    fn next(state: &mut u64) -> M31 {
        *state ^= *state >> 12;
        *state ^= *state << 25;
        *state ^= *state >> 27;
        M31((state.wrapping_mul(0x2545_f491_4f6c_dd1d) as u32) % crate::field::P)
    }

    fn random_q(state: &mut u64) -> QM31 {
        QM31 {
            c0: CM31::new(next(state), next(state)),
            c1: CM31::new(next(state), next(state)),
        }
    }

    #[test]
    fn short_prefix_dp_matches_independent_weight_at_after_profile21_round_zero() {
        let mut state = 0x21c0_35aa_17ef_0042u64;
        for _ in 0..32 {
            let mut weights = WeightAccumulator::empty(10);
            for _ in 0..3 {
                let scale = random_q(&mut state);
                let point = (0..10).map(|_| random_q(&mut state)).collect();
                weights.add_multilinear(scale, point).unwrap();
            }
            let masks = core::array::from_fn(|row| {
                let value = next(&mut state).0 as u16;
                value ^ (row as u16).wrapping_mul(0x421)
            });
            weights
                .add_grouped_64x16_binary_masks_deferred(masks)
                .unwrap();
            for _ in 0..2 {
                weights
                    .add_circle_tensor(
                        random_q(&mut state),
                        SecureCirclePoint {
                            x: random_q(&mut state),
                            y: random_q(&mut state),
                        },
                    )
                    .unwrap();
            }
            weights.fold(random_q(&mut state));
            let prefix = weights.weight_prefix::<35>();
            assert_eq!(
                prefix,
                core::array::from_fn(|index| weights.weight_at(index as u32)),
            );
        }
    }

    fn explicit_tensor_weights(scale: QM31, factors: &[QM31]) -> Vec<QM31> {
        (0..1u32 << factors.len())
            .map(|index| {
                factors
                    .iter()
                    .enumerate()
                    .fold(scale, |value, (coordinate, factor)| {
                        let bit = (index >> (factors.len() - 1 - coordinate)) & 1;
                        if bit == 0 {
                            value
                        } else {
                            value.mul(*factor)
                        }
                    })
            })
            .collect()
    }

    fn explicit_product_weights(scale: QM31, pairs: &[[QM31; 2]]) -> Vec<QM31> {
        (0..1u32 << pairs.len())
            .map(|index| {
                pairs
                    .iter()
                    .enumerate()
                    .fold(scale, |value, (coordinate, pair)| {
                        let bit = ((index >> (pairs.len() - 1 - coordinate)) & 1) as usize;
                        value.mul(pair[bit])
                    })
            })
            .collect()
    }

    fn explicit_multilinear_weights(scale: QM31, point: &[QM31]) -> Vec<QM31> {
        (0..1u32 << point.len())
            .map(|index| {
                point
                    .iter()
                    .enumerate()
                    .fold(scale, |value, (coordinate, point_coordinate)| {
                        let bit = (index >> (point.len() - 1 - coordinate)) & 1;
                        value.mul(if bit == 0 {
                            QM31::ONE.sub(*point_coordinate)
                        } else {
                            *point_coordinate
                        })
                    })
            })
            .collect()
    }

    fn explicit_dual_fold(weights: &[QM31], alpha: QM31) -> Vec<QM31> {
        let alpha2 = alpha.square();
        let alpha3 = alpha2.mul(alpha);
        weights
            .chunks_exact(4)
            .map(|chunk| {
                chunk[0]
                    .add(alpha3.mul(chunk[1]))
                    .add(alpha2.mul(chunk[2]))
                    .add(alpha.mul(chunk[3]))
                    .mul_m31(M31_QUARTER)
            })
            .collect()
    }

    #[test]
    fn materialized_arity8_dual_preserves_the_folded_dot() {
        let mut state = 0x7a13_4d29_610c_b83fu64;
        for _ in 0..16 {
            let values = (0..32).map(|_| random_q(&mut state)).collect::<Vec<_>>();
            let weights = (0..32).map(|_| random_q(&mut state)).collect::<Vec<_>>();
            let alpha = random_q(&mut state);
            let mut accumulator = WeightAccumulator::empty(5);
            accumulator.add_dense(weights.clone()).unwrap();
            let powers: [QM31; 8] = core::array::from_fn(|exponent| alpha.pow(exponent as u64));
            let folded = values
                .chunks_exact(8)
                .map(|chunk| {
                    chunk
                        .iter()
                        .zip(powers)
                        .fold(QM31::ZERO, |sum, (value, power)| sum.add(value.mul(power)))
                })
                .collect::<Vec<_>>();
            let inverse_eight = M31(8).inv();
            let expected = values.chunks_exact(8).zip(weights.chunks_exact(8)).fold(
                QM31::ZERO,
                |sum, (values, weights)| {
                    let primal = values
                        .iter()
                        .zip(powers)
                        .fold(QM31::ZERO, |sum, (value, power)| sum.add(value.mul(power)));
                    let dual = (0..8).fold(QM31::ZERO, |sum, slot| {
                        let exponent = if slot == 0 { 0 } else { 8 - slot };
                        sum.add(weights[slot].mul(powers[exponent]))
                    });
                    sum.add(primal.mul(dual).mul_m31(inverse_eight))
                },
            );
            accumulator.fold_arity8_materialized_for_probe(alpha);
            assert_eq!(accumulator.dot(&folded), expected);
        }
    }

    fn circle_factors(log_len: u32, point: SecureCirclePoint) -> Vec<QM31> {
        let mut factors = vec![point.y, point.x];
        let mut x = point.x;
        for _ in 2..log_len {
            x = double_x(x);
            factors.push(x);
        }
        factors.reverse();
        factors
    }

    fn line_factors(log_len: u32, mut x: QM31) -> Vec<QM31> {
        let mut factors = Vec::with_capacity(log_len as usize);
        for _ in 0..log_len {
            factors.push(x);
            x = double_x(x);
        }
        factors.reverse();
        factors
    }

    fn assert_materialized_at_every_fold(
        mut accumulator: WeightAccumulator,
        mut explicit: Vec<QM31>,
        state: &mut u64,
    ) {
        loop {
            assert_eq!(explicit.len(), 1usize << accumulator.log_len);
            for (index, expected) in explicit.iter().enumerate() {
                assert_eq!(accumulator.weight_at(index as u32), *expected);
            }
            let values = (0..explicit.len())
                .map(|_| random_q(state))
                .collect::<Vec<_>>();
            let explicit_dot = values
                .iter()
                .zip(&explicit)
                .fold(QM31::ZERO, |sum, (value, weight)| {
                    sum.add(value.mul(*weight))
                });
            assert_eq!(accumulator.dot(&values), explicit_dot);

            if accumulator.log_len == 0 {
                break;
            }
            let alpha = random_q(state);
            explicit = explicit_dual_fold(&explicit, alpha);
            accumulator.fold(alpha);
        }
    }

    #[test]
    fn boundary_and_fold_invariants_hold_for_mixed_weights() {
        let values = (1..=16).map(q).collect::<Vec<_>>();
        let claim = EvaluationClaim {
            z: vec![q(2), q(3), q(4), q(5)],
            v: QM31::ZERO,
        };
        let mut weights = WeightAccumulator::from_claim(4, Some(&claim));
        weights.add_geometric(q(7), q(9));

        let polynomial = polynomial_for_extension(&values, &weights);
        assert_eq!(boundary_sum(&polynomial), weights.dot(&values));

        let alpha = q(11);
        let folded = fold_values(&values, alpha);
        weights.fold(alpha);
        assert_eq!(evaluate(&polynomial, alpha), weights.dot(&folded));

        let polynomial = polynomial_for_extension(&folded, &weights);
        assert_eq!(boundary_sum(&polynomial), weights.dot(&folded));
        let alpha = q(13);
        let folded = fold_values(&folded, alpha);
        weights.fold(alpha);
        assert_eq!(evaluate(&polynomial, alpha), weights.dot(&folded));
    }

    #[test]
    fn circle_tensor_matches_materialized_weights_through_terminal() {
        for seed in 1..=24u64 {
            let mut state = seed.wrapping_mul(0x9e37_79b9_7f4a_7c15);
            let point = secure_circle_point_from_parameter(random_q(&mut state)).unwrap();
            let scale = random_q(&mut state);
            let factors = circle_factors(10, point);
            let explicit = explicit_tensor_weights(scale, &factors);
            let mut accumulator = WeightAccumulator::empty(10);
            accumulator.add_circle_tensor(scale, point).unwrap();
            assert_materialized_at_every_fold(accumulator, explicit, &mut state);
        }
    }

    #[test]
    fn prepared_tensor_folds_match_payment_component_counts_at_every_depth() {
        for seed in 1..=16u64 {
            let mut state = seed.wrapping_mul(0xd134_2543_de82_ef95);
            let mut accumulator = WeightAccumulator::empty(10);
            let mut explicit = vec![QM31::ZERO; 1 << 10];

            // The payment relation starts with two multilinear statement
            // claims, then introduces two OOD tensor components before each
            // of its four folds.  Thus the exact live component counts are
            // 4, 6, 8, and 10, with 2, 4, 6, and 8 Tensor branches.
            for _ in 0..2 {
                let scale = random_q(&mut state);
                let point = (0..10).map(|_| random_q(&mut state)).collect::<Vec<_>>();
                let materialized = explicit_multilinear_weights(scale, &point);
                for (weight, contribution) in explicit.iter_mut().zip(materialized) {
                    *weight = weight.add(contribution);
                }
                accumulator.add_multilinear(scale, point).unwrap();
            }

            for round in 0..4usize {
                let log_len = 10 - 2 * round as u32;
                assert_eq!(accumulator.log_len, log_len);
                for _ in 0..2 {
                    let scale = random_q(&mut state);
                    let factors = (0..log_len)
                        .map(|_| random_q(&mut state))
                        .collect::<Vec<_>>();
                    let materialized = explicit_tensor_weights(scale, &factors);
                    for (weight, contribution) in explicit.iter_mut().zip(materialized) {
                        *weight = weight.add(contribution);
                    }
                    accumulator.add_tensor_factors(scale, factors).unwrap();
                }
                assert_eq!(accumulator.components.len(), 4 + 2 * round);
                for (index, expected) in explicit.iter().enumerate() {
                    assert_eq!(
                        accumulator.weight_at(index as u32),
                        *expected,
                        "seed={seed}, round={round}, index={index}"
                    );
                }
                let values = (0..explicit.len())
                    .map(|_| random_q(&mut state))
                    .collect::<Vec<_>>();
                let expected_dot = values
                    .iter()
                    .zip(&explicit)
                    .fold(QM31::ZERO, |sum, (value, weight)| {
                        sum.add(value.mul(*weight))
                    });
                assert_eq!(accumulator.dot(&values), expected_dot);

                let alpha = match round {
                    0 => QM31::ZERO,
                    1 => QM31::ONE,
                    2 => QM31::ONE.neg(),
                    _ => random_q(&mut state),
                };
                explicit = explicit_dual_fold(&explicit, alpha);
                accumulator.fold(alpha);
            }

            assert_eq!(accumulator.log_len, 2);
            assert_eq!(accumulator.components.len(), 10);
            for (index, expected) in explicit.iter().enumerate() {
                assert_eq!(accumulator.weight_at(index as u32), *expected);
            }
        }
    }

    #[test]
    fn product_pairs_match_sparse_subcube_weights_through_terminal() {
        for seed in 1..=24u64 {
            let mut state = seed.wrapping_mul(0x94d0_49bb_1331_11eb);
            let scale = random_q(&mut state);
            let pairs = vec![
                [QM31::ZERO, QM31::ONE],
                [QM31::ONE, QM31::ONE],
                [QM31::ONE, QM31::ZERO],
                [random_q(&mut state), random_q(&mut state)],
                [QM31::ONE, QM31::ONE],
                [random_q(&mut state), random_q(&mut state)],
            ];
            let explicit = explicit_product_weights(scale, &pairs);
            let mut accumulator = WeightAccumulator::empty(pairs.len() as u32);
            accumulator
                .add_product_pairs(scale, pairs)
                .expect("pair count matches");
            assert_materialized_at_every_fold(accumulator, explicit, &mut state);
        }
    }

    #[test]
    fn index_interval_matches_the_154_row_helper_padding_indicator() {
        let mut state = 0x494e_5445_5256_414cu64;
        let scale = random_q(&mut state);
        let explicit = (0..1024)
            .map(|index| {
                if (870..1024).contains(&index) {
                    scale
                } else {
                    QM31::ZERO
                }
            })
            .collect::<Vec<_>>();
        let mut accumulator = WeightAccumulator::empty(10);
        accumulator
            .add_index_interval(scale, 870, 1024)
            .expect("valid padding interval");
        assert_materialized_at_every_fold(accumulator, explicit, &mut state);
    }

    #[test]
    fn dense_public_covector_matches_explicit_dual_folds() {
        let mut state = 0x4445_4e53_455f_5a4bu64;
        let explicit = (0..1024)
            .map(|index| {
                if index % 7 == 0 || (868..1024).contains(&index) {
                    random_q(&mut state)
                } else {
                    QM31::ZERO
                }
            })
            .collect::<Vec<_>>();
        let mut accumulator = WeightAccumulator::empty(10);
        accumulator
            .add_dense(explicit.clone())
            .expect("exact dense length");
        assert_materialized_at_every_fold(accumulator, explicit, &mut state);

        let mut wrong = WeightAccumulator::empty(10);
        assert_eq!(
            wrong.add_dense(vec![QM31::ZERO; 1023]),
            Err(TensorWeightError::DenseLength)
        );
    }

    #[test]
    fn grouped_64x16_binary_masks_match_dense_at_every_dual_fold() {
        let masks = [
            0xffff, 0xfffa, 0xff00, 0xfd00, 0xeffe, 0xe7ff, 0x4000, 0x0000,
        ];
        let row_masks: [u16; 64] = core::array::from_fn(|high| masks[(high * 5 + 3) & 7]);
        let explicit = row_masks
            .iter()
            .flat_map(|&mask| {
                (0..16).map(move |low| {
                    if mask & (1 << low) == 0 {
                        QM31::ZERO
                    } else {
                        QM31::ONE
                    }
                })
            })
            .collect::<Vec<_>>();
        for seed in 1..=24u64 {
            let mut state = seed.wrapping_mul(0x4752_4f55_5036_3416);
            let mut grouped = WeightAccumulator::empty(10);
            grouped.add_grouped_64x16_binary_masks(row_masks).unwrap();
            let mut dense = WeightAccumulator::empty(10);
            dense.add_dense(explicit.clone()).unwrap();
            while grouped.log_len >= 2 {
                let values = (0..1usize << grouped.log_len)
                    .map(|_| random_q(&mut state))
                    .collect::<Vec<_>>();
                assert_eq!(
                    polynomial_for_extension(&values, &grouped),
                    polynomial_for_extension(&values, &dense)
                );
                for index in 0..values.len() {
                    assert_eq!(
                        grouped.weight_at(index as u32),
                        dense.weight_at(index as u32)
                    );
                }
                let alpha = random_q(&mut state);
                grouped.fold(alpha);
                dense.fold(alpha);
            }
        }

        let mut wrong = WeightAccumulator::empty(8);
        assert_eq!(
            wrong.add_grouped_64x16_binary_masks(row_masks),
            Err(TensorWeightError::Grouped64x16LogLength)
        );
    }

    #[test]
    fn grouped_128x16_lower_masks_upper_zero_match_dense_at_every_dual_fold() {
        let masks = [
            0xffff, 0xfffa, 0xff00, 0xfd00, 0xeffe, 0xe7ff, 0x4000, 0x0000,
        ];
        let row_masks: [u16; 128] = core::array::from_fn(|high| {
            if high < 64 {
                masks[(high * 5 + 3) & 7]
            } else {
                0
            }
        });
        let explicit = row_masks
            .iter()
            .flat_map(|&mask| {
                (0..16).map(move |low| {
                    if mask & (1 << low) == 0 {
                        QM31::ZERO
                    } else {
                        QM31::ONE
                    }
                })
            })
            .collect::<Vec<_>>();
        for seed in 1..=12u64 {
            let mut state = seed.wrapping_mul(0x4752_4f55_5031_2816);
            let mut grouped = WeightAccumulator::empty(11);
            grouped.add_grouped_128x16_binary_masks(row_masks).unwrap();
            let mut dense = WeightAccumulator::empty(11);
            dense.add_dense(explicit.clone()).unwrap();
            while grouped.log_len >= 3 {
                let values = (0..1usize << grouped.log_len)
                    .map(|_| random_q(&mut state))
                    .collect::<Vec<_>>();
                assert_eq!(
                    polynomial_for_extension(&values, &grouped),
                    polynomial_for_extension(&values, &dense)
                );
                for index in 0..values.len() {
                    assert_eq!(
                        grouped.weight_at(index as u32),
                        dense.weight_at(index as u32)
                    );
                }
                let alpha = random_q(&mut state);
                grouped.fold(alpha);
                dense.fold(alpha);
            }
        }

        let mut wrong = WeightAccumulator::empty(10);
        assert_eq!(
            wrong.add_grouped_128x16_binary_masks(row_masks),
            Err(TensorWeightError::Grouped128x16LogLength)
        );
    }

    #[test]
    fn deferred_binary_64x16_matches_legacy_at_64_random_off_domain_fold_points() {
        let masks = [
            0xe7ff, 0xe7fe, 0xeffe, 0x4000, 0xfd00, 0xff00, 0xfffa, 0xffff,
        ];
        let row_masks: [u16; 64] =
            core::array::from_fn(|high| masks[(high * 5 + high / 7 + 3) & 7]);

        for seed in 1..=64u64 {
            let mut state = seed.wrapping_mul(0x4445_4645_5236_3416);
            let mut legacy = WeightAccumulator::empty(10);
            legacy.add_grouped_64x16_binary_masks(row_masks).unwrap();
            let mut deferred = WeightAccumulator::empty(10);
            deferred
                .add_grouped_64x16_binary_masks_deferred(row_masks)
                .unwrap();

            while legacy.log_len >= 2 {
                for index in 0..1u32 << legacy.log_len {
                    assert_eq!(
                        deferred.weight_at(index),
                        legacy.weight_at(index),
                        "seed={seed} log_len={} index={index}",
                        legacy.log_len
                    );
                }
                let terminal_values = (0..1usize << legacy.log_len)
                    .map(|_| random_q(&mut state))
                    .collect::<Vec<_>>();
                assert_eq!(deferred.dot(&terminal_values), legacy.dot(&terminal_values));
                if legacy.log_len == 2 {
                    break;
                }
                let alpha = random_q(&mut state);
                legacy.fold(alpha);
                deferred.fold(alpha);
            }
        }

        let mut wrong = WeightAccumulator::empty(8);
        assert_eq!(
            wrong.add_grouped_64x16_binary_masks_deferred(row_masks),
            Err(TensorWeightError::Grouped64x16LogLength)
        );
    }

    #[test]
    fn first_circle_fold_leaves_the_expected_line_tail() {
        for seed in 1..=24u64 {
            let mut state = seed.wrapping_mul(0xd1b5_4a32_d192_ed03);
            let point = secure_circle_point_from_parameter(random_q(&mut state)).unwrap();
            let scale = random_q(&mut state);
            let alpha = random_q(&mut state);

            let initial = explicit_tensor_weights(scale, &circle_factors(10, point));
            let expected = explicit_dual_fold(&initial, alpha);
            let mut circle = WeightAccumulator::empty(10);
            circle.add_circle_tensor(scale, point).unwrap();
            circle.fold(alpha);

            let mut line = WeightAccumulator::empty(8);
            line.add_line_tensor(expected[0], double_x(point.x))
                .unwrap();
            for (index, expected_weight) in expected.iter().enumerate() {
                assert_eq!(circle.weight_at(index as u32), *expected_weight);
                assert_eq!(line.weight_at(index as u32), *expected_weight);
            }
        }
    }

    #[test]
    fn random_line_tensors_match_materialized_weights_across_later_folds() {
        for log_len in [2u32, 4, 6, 8] {
            for seed in 1..=16u64 {
                let mut state = seed
                    .wrapping_mul(0xa076_1d64_78bd_642f)
                    .wrapping_add(u64::from(log_len));
                let x = random_q(&mut state);
                let scale = random_q(&mut state);
                let explicit = explicit_tensor_weights(scale, &line_factors(log_len, x));
                let mut accumulator = WeightAccumulator::empty(log_len);
                accumulator.add_line_tensor(scale, x).unwrap();
                assert_materialized_at_every_fold(accumulator, explicit, &mut state);
            }
        }
    }

    #[test]
    fn scaled_multilinear_components_match_materialization_through_terminal() {
        for seed in 1..=24u64 {
            let mut state = seed.wrapping_mul(0xe703_7ed1_a0b4_28db);
            let point_0 = (0..10).map(|_| random_q(&mut state)).collect::<Vec<_>>();
            let point_1 = (0..10).map(|_| random_q(&mut state)).collect::<Vec<_>>();
            let scale_0 = random_q(&mut state);
            let scale_1 = random_q(&mut state);
            let weights_0 = explicit_multilinear_weights(scale_0, &point_0);
            let weights_1 = explicit_multilinear_weights(scale_1, &point_1);
            let explicit = weights_0
                .iter()
                .zip(weights_1)
                .map(|(left, right)| left.add(right))
                .collect::<Vec<_>>();

            let mut accumulator = WeightAccumulator::empty(10);
            accumulator.add_multilinear(scale_0, point_0).unwrap();
            accumulator.add_multilinear(scale_1, point_1).unwrap();
            assert_materialized_at_every_fold(accumulator, explicit, &mut state);
        }
    }

    #[test]
    fn tensor_constructor_shapes_are_explicit_errors() {
        let mut accumulator = WeightAccumulator::empty(4);
        assert_eq!(
            accumulator.add_multilinear(QM31::ONE, vec![QM31::ONE; 3]),
            Err(TensorWeightError::MultilinearPointLength)
        );
        assert_eq!(
            accumulator.add_tensor_factors(QM31::ONE, vec![QM31::ONE; 3]),
            Err(TensorWeightError::FactorCount)
        );
        let mut too_short = WeightAccumulator::empty(1);
        assert_eq!(
            too_short.add_circle_tensor(QM31::ONE, SecureCirclePoint { x: q(3), y: q(5) },),
            Err(TensorWeightError::CircleLogLength)
        );
    }
}
