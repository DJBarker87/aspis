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
use crate::field::{
    qm31_m31_sum_products3, qm31_sum_products2_prepared, qm31_sum_products4,
    PreparedQm31Multiplier, CM31, M31, M31_QUARTER, QM31,
};
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
    /// Line-tensor evaluation whose low coordinate and every iterated
    /// `pi(x) = 2x^2 - 1` remain in M31.  Keeping the aligned base-field
    /// coordinate instead of eight lifted QM31 factors removes repeated
    /// extension-field squaring and enables mixed-width fold kernels.
    LineM31Tensor { scale: QM31, x: M31 },
    /// Several line tensors sharing one live log length. V6 installs all
    /// sixteen query-evaluation covectors together, avoiding sixteen enum
    /// dispatches per relation round while preserving each independent scale
    /// and base-field line coordinate exactly.
    LineM31Batch {
        scales: Vec<QM31>,
        xs: Vec<M31>,
        deferred_halvings: u8,
    },
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
    /// distinct masks through the first two dual folds. The high-row group
    /// schedule then remains grouped through both later folds: each distinct
    /// four-tuple is evaluated once and equal entries within a tuple share one
    /// multiplication. No verifier code observes an intermediate covector,
    /// but `weight_at` still implements every fold depth exactly so off-domain
    /// differential tests can compare both paths after every round.
    Grouped64x16BinaryDeferred {
        row_groups: Vec<u8>,
        group_masks: Vec<u16>,
        first_alpha: Option<QM31>,
        group_values: Vec<QM31>,
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

/// Read one coefficient from the unfurled log-10 representation of a
/// deferred 64-by-16 binary mask component.
///
/// The high six index bits select the row and its mask group. The low four
/// bits select a bit within that `u16`, with the least-significant bit first.
fn grouped_64x16_binary_deferred_weight_at_log10(
    row_groups: &[u8],
    group_masks: &[u16],
    index: u32,
) -> QM31 {
    let high = (index / 16) as usize;
    let low = index & 15;
    let group = usize::from(row_groups[high]);
    let mask = group_masks[group];
    if mask & (1u16 << low) == 0 {
        QM31::ZERO
    } else {
        QM31::ONE
    }
}

/// Evaluate every distinct 16-bit mask after the two low arity-four dual
/// folds.  Dense masks use the exact total-minus-complement identity, while
/// sparse masks sum their set positions.  Only basis entries selected by one
/// of those two representations are formed, and cross-products are shared by
/// every mask.
fn sum_selected_binary_basis(selected_positions: u16, basis: &[QM31; 16]) -> QM31 {
    let mut partial = QM31::ZERO;
    let mut low = 0usize;
    while low < 16 {
        if selected_positions & (1 << low) != 0 {
            partial = partial.add(basis[low]);
        }
        low += 1;
    }
    partial
}

#[inline(never)]
fn fold_binary_low_masks(group_masks: &[u16], alpha0: QM31, alpha1: QM31) -> Vec<QM31> {
    let alpha0_2 = alpha0.square();
    let alpha1_2 = alpha1.square();
    let alpha0_powers = [QM31::ONE, alpha0_2.mul(alpha0), alpha0_2, alpha0];
    let alpha1_powers = [QM31::ONE, alpha1_2.mul(alpha1), alpha1_2, alpha1];

    let mut selected = 0u16;
    let mut needs_total = false;
    let mut mask_index = 0usize;
    while mask_index < group_masks.len() {
        let mask = group_masks[mask_index];
        if mask.count_ones() > 8 {
            needs_total = true;
            selected |= !mask;
        } else {
            selected |= mask;
        }
        mask_index += 1;
    }

    // If every cross term is needed, materializing the complete basis also
    // gives the total by addition and avoids buying a tenth multiplication.
    const CROSS_POSITIONS: u16 = 0xeee0;
    let materialize_all = needs_total && (selected & CROSS_POSITIONS) == CROSS_POSITIONS;
    if materialize_all {
        selected = u16::MAX;
    }

    let mut basis = [QM31::ZERO; 16];
    let mut low = 0usize;
    while low < 16 {
        if selected & (1 << low) != 0 {
            let high_slot = low >> 2;
            let low_slot = low & 3;
            basis[low] = if high_slot == 0 {
                alpha0_powers[low_slot]
            } else if low_slot == 0 {
                alpha1_powers[high_slot]
            } else {
                alpha1_powers[high_slot].mul(alpha0_powers[low_slot])
            };
        }
        low += 1;
    }

    let total = if needs_total {
        if materialize_all {
            let mut total = QM31::ZERO;
            let mut low = 0usize;
            while low < 16 {
                total = total.add(basis[low]);
                low += 1;
            }
            total
        } else {
            let mut alpha0_total = QM31::ZERO;
            let mut alpha1_total = QM31::ZERO;
            let mut slot = 0usize;
            while slot < 4 {
                alpha0_total = alpha0_total.add(alpha0_powers[slot]);
                alpha1_total = alpha1_total.add(alpha1_powers[slot]);
                slot += 1;
            }
            alpha0_total.mul(alpha1_total)
        }
    } else {
        QM31::ZERO
    };

    let mut values = Vec::with_capacity(group_masks.len());
    let mut mask_index = 0usize;
    while mask_index < group_masks.len() {
        let mask = group_masks[mask_index];
        let dense = mask.count_ones() > 8;
        let selected_positions = if dense { !mask } else { mask };
        let partial = sum_selected_binary_basis(selected_positions, &basis);
        let raw = if dense { total.sub(partial) } else { partial };
        values.push(raw.half().half().half().half());
        mask_index += 1;
    }
    values
}

/// Fold one four-row group tuple. Equal group identifiers are collected
/// before multiplying, so the frozen high-row schedule pays once per distinct
/// value in a tuple rather than once per nonconstant slot.
#[inline(never)]
fn fold_group_tuple(
    groups: [u8; 4],
    group_values: &[QM31],
    alpha: QM31,
    alpha2: QM31,
    alpha3: QM31,
) -> QM31 {
    let powers = [QM31::ONE, alpha3, alpha2, alpha];
    let mut unique_groups = [0u8; 4];
    let mut coefficients = [QM31::ZERO; 4];
    let mut counts = [0u8; 4];
    let mut first_slots = [0u8; 4];
    let mut unique_len = 0usize;

    for slot in 0..4 {
        let group = groups[slot];
        let mut position = 0usize;
        while position < unique_len && unique_groups[position] != group {
            position += 1;
        }
        if position < unique_len {
            coefficients[position] = coefficients[position].add(powers[slot]);
            counts[position] += 1;
        } else {
            unique_groups[unique_len] = group;
            coefficients[unique_len] = powers[slot];
            counts[unique_len] = 1;
            first_slots[unique_len] = slot as u8;
            unique_len += 1;
        }
    }

    let mut folded = QM31::ZERO;
    for position in 0..unique_len {
        let value = group_values[usize::from(unique_groups[position])];
        let contribution = if first_slots[position] == 0 && counts[position] == 1 {
            value
        } else {
            value.mul(coefficients[position])
        };
        folded = folded.add(contribution);
    }
    folded.half().half()
}

/// Deduplicate the consecutive four-tuples of a grouped high-row schedule and
/// evaluate each distinct tuple once. The returned group schedule represents
/// the exact folded covector without expanding it to one QM31 per row.
#[inline(never)]
fn fold_grouped_rows(
    row_groups: &[u8],
    group_values: &[QM31],
    alpha: QM31,
    alpha2: QM31,
    alpha3: QM31,
) -> (Vec<u8>, Vec<QM31>) {
    debug_assert_eq!(row_groups.len() % 4, 0);
    let folded_len = row_groups.len() / 4;
    let mut tuples = Vec::<[u8; 4]>::with_capacity(folded_len);
    let mut folded_groups = Vec::<u8>::with_capacity(folded_len);
    let mut folded_values = Vec::<QM31>::with_capacity(folded_len);

    for chunk in row_groups.chunks_exact(4) {
        let tuple = [chunk[0], chunk[1], chunk[2], chunk[3]];
        let mut group = 0usize;
        while group < tuples.len() && tuples[group] != tuple {
            group += 1;
        }
        if group == tuples.len() {
            tuples.push(tuple);
            folded_values.push(fold_group_tuple(tuple, group_values, alpha, alpha2, alpha3));
        }
        folded_groups.push(group as u8);
    }
    (folded_groups, folded_values)
}

/// Compose the two high-row arity-four folds of a deferred 64-by-16 mask.
///
/// After the two low-mask folds have produced one value per mask group, the
/// remaining 64 rows are folded first to 16 and then to four.  Tensoring the
/// two dual coefficient vectors gives the identical arity-16 linear map.  A
/// group identifier is accumulated once per final 16-row chunk, avoiding the
/// intermediate tuple registry and allocation without changing any weight.
#[inline(never)]
fn fold_grouped_rows_twice(
    row_groups: &[u8],
    group_values: &[QM31],
    first_alpha: QM31,
    second_alpha: QM31,
) -> (Vec<u8>, Vec<QM31>) {
    debug_assert_eq!(row_groups.len(), 64);
    let first2 = first_alpha.square();
    let second2 = second_alpha.square();
    let first = [QM31::ONE, first2.mul(first_alpha), first2, first_alpha];
    let second = [QM31::ONE, second2.mul(second_alpha), second2, second_alpha];
    let basis: [QM31; 16] = core::array::from_fn(|slot| {
        let high = slot >> 2;
        let low = slot & 3;
        if high == 0 {
            first[low]
        } else if low == 0 {
            second[high]
        } else {
            second[high].mul(first[low])
        }
    });

    let mut folded_values = Vec::with_capacity(4);
    for chunk in row_groups.chunks_exact(16) {
        let mut unique_groups = [0u8; 16];
        let mut coefficients = [QM31::ZERO; 16];
        let mut counts = [0u8; 16];
        let mut first_slots = [0u8; 16];
        let mut unique_len = 0usize;
        let mut slot = 0usize;
        while slot < 16 {
            let group = chunk[slot];
            let mut position = 0usize;
            while position < unique_len && unique_groups[position] != group {
                position += 1;
            }
            if position == unique_len {
                unique_groups[unique_len] = group;
                coefficients[unique_len] = basis[slot];
                counts[unique_len] = 1;
                first_slots[unique_len] = slot as u8;
                unique_len += 1;
            } else {
                coefficients[position] = coefficients[position].add(basis[slot]);
                counts[position] += 1;
            }
            slot += 1;
        }

        let mut value = QM31::ZERO;
        let mut position = 0usize;
        while position < unique_len {
            let group_value = group_values[usize::from(unique_groups[position])];
            let contribution = if first_slots[position] == 0 && counts[position] == 1 {
                group_value
            } else {
                group_value.mul(coefficients[position])
            };
            value = value.add(contribution);
            position += 1;
        }
        folded_values.push(value.half().half().half().half());
    }
    (alloc::vec![0, 1, 2, 3], folded_values)
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
    /// A pre-grouped 64-by-16 mask schedule must reference a nonempty group table.
    Grouped64x16PreparedShape,
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
    /// Append one validated, already-deduplicated deferred binary schedule.
    /// Callers retain responsibility for log length and schedule-shape checks.
    fn install_grouped_64x16_binary_masks_deferred_prepared(
        &mut self,
        row_groups: Vec<u8>,
        group_masks: Vec<u16>,
    ) {
        self.components
            .push(WeightComponent::Grouped64x16BinaryDeferred {
                row_groups,
                group_masks,
                first_alpha: None,
                group_values: Vec::new(),
            });
    }

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
        let mut high = 0usize;
        while high < row_masks.len() {
            let mask = row_masks[high];
            let mut group = 0usize;
            while group < group_masks.len() && group_masks[group] != mask {
                group += 1;
            }
            if group == group_masks.len() {
                group_masks.push(mask);
            }
            row_groups.push(group as u8);
            high += 1;
        }
        self.install_grouped_64x16_binary_masks_deferred_prepared(row_groups, group_masks);
        Ok(())
    }

    /// Install an already deduplicated 64-by-16 binary mask schedule.
    ///
    /// This is algebraically identical to
    /// [`Self::add_grouped_64x16_binary_masks_deferred`]. It lets callers with
    /// a frozen public layout move the row-mask construction and deduplication
    /// off chain while retaining the same fold implementation.
    pub fn add_grouped_64x16_binary_masks_deferred_prepared(
        &mut self,
        row_groups: &[u8; 64],
        group_masks: &[u16],
    ) -> Result<(), TensorWeightError> {
        if self.log_len != 10 {
            return Err(TensorWeightError::Grouped64x16LogLength);
        }
        if group_masks.is_empty() {
            return Err(TensorWeightError::Grouped64x16PreparedShape);
        }
        let mut high = 0usize;
        while high < row_groups.len() {
            if usize::from(row_groups[high]) >= group_masks.len() {
                return Err(TensorWeightError::Grouped64x16PreparedShape);
            }
            high += 1;
        }
        self.install_grouped_64x16_binary_masks_deferred_prepared(
            row_groups.to_vec(),
            group_masks.to_vec(),
        );
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
        let mut high = 0usize;
        while high < row_masks.len() {
            let mask = row_masks[high];
            let mut group = 0usize;
            while group < unique_masks.len() && unique_masks[group] != mask {
                group += 1;
            }
            if group == unique_masks.len() {
                unique_masks.push(mask);
            }
            row_groups.push(group as u8);
            high += 1;
        }
        let mut group_values = Vec::with_capacity(unique_masks.len() * 16);
        let mut group = 0usize;
        while group < unique_masks.len() {
            let mask = unique_masks[group];
            let mut low = 0u32;
            while low < 16 {
                group_values.push(if mask & (1u16 << low) == 0 {
                    QM31::ZERO
                } else {
                    QM31::ONE
                });
                low += 1;
            }
            group += 1;
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

    /// Add the same line-evaluation covector while retaining its coordinate
    /// in the M31 subfield.  The component is exact, not an approximation:
    /// its unfurled weights and every dual-folded weight equal those produced
    /// by `add_line_tensor(scale, QM31::from_cm31(CM31::from_m31(x)))`.
    pub fn add_line_m31_tensor(&mut self, scale: QM31, x: M31) -> Result<(), TensorWeightError> {
        if self.log_len == 0 {
            return Err(TensorWeightError::FactorCount);
        }
        self.components
            .push(WeightComponent::LineM31Tensor { scale, x });
        Ok(())
    }

    /// Install multiple exact M31-aligned line tensors as one component.
    pub fn add_line_m31_batch(
        &mut self,
        scales: &[QM31],
        xs: &[M31],
    ) -> Result<(), TensorWeightError> {
        if self.log_len == 0 || scales.is_empty() || scales.len() != xs.len() {
            return Err(TensorWeightError::FactorCount);
        }
        self.components.push(WeightComponent::LineM31Batch {
            scales: scales.to_vec(),
            xs: xs.to_vec(),
            deferred_halvings: 0,
        });
        Ok(())
    }

    /// Merge two multilinear components once their remaining points are
    /// identical. Linearity makes
    /// `a * eq(z, ·) + b * eq(z, ·) = (a + b) * eq(z, ·)` exactly, so this
    /// changes only the representation of the public relation covector.
    ///
    /// V6 uses this after folding away the two coordinates complemented by
    /// its XOR-12 statement point. Keeping the shape check here makes the
    /// protocol-specific caller fail closed if that public relationship ever
    /// changes.
    pub fn merge_equal_multilinear_components(&mut self, first: usize, second: usize) -> bool {
        if first >= second || second >= self.components.len() {
            return false;
        }
        let (left, right) = self.components.split_at_mut(second);
        let WeightComponent::Multilinear {
            scale: first_scale,
            point: first_point,
        } = &mut left[first]
        else {
            return false;
        };
        let WeightComponent::Multilinear {
            scale: second_scale,
            point: second_point,
        } = &right[0]
        else {
            return false;
        };
        if first_point != second_point {
            return false;
        }
        *first_scale = first_scale.add(*second_scale);
        self.components.remove(second);
        true
    }

    pub fn weight_at(&self, index: u32) -> QM31 {
        debug_assert!(index < (1u32 << self.log_len));
        let mut total = QM31::ZERO;
        let mut component_index = 0usize;
        while component_index < self.components.len() {
            let component = &self.components[component_index];
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
                WeightComponent::LineM31Tensor { scale, x } => {
                    let mut value = *scale;
                    let mut factor = *x;
                    let mut bit = 0u32;
                    while bit < self.log_len {
                        if index & (1u32 << bit) != 0 {
                            value = value.mul_m31(factor);
                        }
                        factor = Self::double_x_m31(factor);
                        bit += 1;
                    }
                    value
                }
                WeightComponent::LineM31Batch {
                    scales,
                    xs,
                    deferred_halvings,
                } => {
                    let mut sum = QM31::ZERO;
                    for (&scale, &x) in scales.iter().zip(xs) {
                        let mut value = scale;
                        let mut factor = x;
                        let mut bit = 0u32;
                        while bit < self.log_len {
                            if index & (1u32 << bit) != 0 {
                                value = value.mul_m31(factor);
                            }
                            factor = Self::double_x_m31(factor);
                            bit += 1;
                        }
                        sum = sum.add(value);
                    }
                    Self::halve_qm31(sum, *deferred_halvings)
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
                    group_values,
                } => match self.log_len {
                    10 => {
                        debug_assert!(first_alpha.is_none());
                        grouped_64x16_binary_deferred_weight_at_log10(
                            row_groups,
                            group_masks,
                            index,
                        )
                    }
                    8 => {
                        let alpha = first_alpha
                            .as_ref()
                            .expect("the first deferred fold stores its challenge");
                        let high = index as usize / 4;
                        let low_chunk = index as usize & 3;
                        let mask = group_masks[usize::from(row_groups[high])];
                        let bits = (mask >> (4 * low_chunk)) & 0x0f;
                        let alpha2 = alpha.square();
                        let alpha3 = alpha2.mul(*alpha);
                        let powers = [QM31::ONE, alpha3, alpha2, *alpha];
                        let mut sum = QM31::ZERO;
                        let mut slot = 0u32;
                        while slot < 4 {
                            if bits & (1u16 << slot) != 0 {
                                sum = sum.add(powers[slot as usize]);
                            }
                            slot += 1;
                        }
                        sum.half().half()
                    }
                    2 | 4 | 6 => {
                        debug_assert!(first_alpha.is_none());
                        group_values[usize::from(row_groups[index as usize])]
                    }
                    _ => unreachable!("invalid deferred binary fold depth"),
                },
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
            component_index += 1;
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
        let mut component_index = 0usize;
        while component_index < self.components.len() {
            let component = &self.components[component_index];
            match component {
                WeightComponent::Geometric { scale, base } => {
                    let mut value = *scale;
                    let mut index = 0usize;
                    while index < N {
                        output[index] = output[index].add(value);
                        value = value.mul(*base);
                        index += 1;
                    }
                }
                WeightComponent::Multilinear { scale, point } => {
                    let mut pairs = Vec::with_capacity(point.len());
                    let mut coordinate = 0usize;
                    while coordinate < point.len() {
                        let value = point[coordinate];
                        pairs.push([QM31::ONE.sub(value), value]);
                        coordinate += 1;
                    }
                    add_product_prefix(&mut output, &pairs, 0, 0, *scale);
                }
                WeightComponent::Tensor { scale, factors } => {
                    let mut values = [QM31::ZERO; N];
                    if N != 0 {
                        values[0] = *scale;
                    }
                    let mut index = 1usize;
                    while index < N {
                        let bit = index.trailing_zeros() as usize;
                        let prefix = index ^ (1usize << bit);
                        values[index] = values[prefix].mul(factors[factors.len() - 1 - bit]);
                        index += 1;
                    }
                    let mut index = 0usize;
                    while index < N {
                        output[index] = output[index].add(values[index]);
                        index += 1;
                    }
                }
                WeightComponent::LineM31Tensor { scale, x } => {
                    let mut factors = Vec::with_capacity(self.log_len as usize);
                    let mut factor = *x;
                    for _ in 0..self.log_len {
                        factors.push(factor);
                        factor = Self::double_x_m31(factor);
                    }
                    let mut values = [QM31::ZERO; N];
                    if N != 0 {
                        values[0] = *scale;
                    }
                    let mut index = 1usize;
                    while index < N {
                        let bit = index.trailing_zeros() as usize;
                        values[index] = values[index ^ (1usize << bit)].mul_m31(factors[bit]);
                        index += 1;
                    }
                    let mut index = 0usize;
                    while index < N {
                        output[index] = output[index].add(values[index]);
                        index += 1;
                    }
                }
                WeightComponent::LineM31Batch {
                    scales,
                    xs,
                    deferred_halvings,
                } => {
                    let mut component_values = [QM31::ZERO; N];
                    for (&scale, &x) in scales.iter().zip(xs) {
                        let mut factors = Vec::with_capacity(self.log_len as usize);
                        let mut factor = x;
                        for _ in 0..self.log_len {
                            factors.push(factor);
                            factor = Self::double_x_m31(factor);
                        }
                        let mut values = [QM31::ZERO; N];
                        if N != 0 {
                            values[0] = scale;
                        }
                        let mut index = 1usize;
                        while index < N {
                            let bit = index.trailing_zeros() as usize;
                            values[index] = values[index ^ (1usize << bit)].mul_m31(factors[bit]);
                            index += 1;
                        }
                        let mut index = 0usize;
                        while index < N {
                            component_values[index] = component_values[index].add(values[index]);
                            index += 1;
                        }
                    }
                    let mut index = 0usize;
                    while index < N {
                        output[index] = output[index].add(Self::halve_qm31(
                            component_values[index],
                            *deferred_halvings,
                        ));
                        index += 1;
                    }
                }
                WeightComponent::Product { scale, pairs } => {
                    add_product_prefix(&mut output, pairs, 0, 0, *scale);
                }
                WeightComponent::Dense { values } => {
                    let mut index = 0usize;
                    while index < N && index < values.len() {
                        output[index] = output[index].add(values[index]);
                        index += 1;
                    }
                }
                WeightComponent::Grouped64x16 {
                    row_groups,
                    group_values,
                    low_width,
                } => {
                    let width = usize::from(*low_width);
                    let mut index = 0usize;
                    while index < N {
                        let group = usize::from(row_groups[index / width]);
                        output[index] =
                            output[index].add(group_values[group * width + index % width]);
                        index += 1;
                    }
                }
                WeightComponent::Grouped64x16BinaryDeferred {
                    row_groups,
                    group_masks,
                    first_alpha,
                    group_values,
                } => match self.log_len {
                    10 => {
                        debug_assert!(first_alpha.is_none());
                        let mut index = 0usize;
                        while index < N {
                            let high = index / 16;
                            let low = index & 15;
                            let mask = group_masks[usize::from(row_groups[high])];
                            if mask & (1 << low) != 0 {
                                output[index] = output[index].add(QM31::ONE);
                            }
                            index += 1;
                        }
                    }
                    8 => {
                        let alpha = first_alpha
                            .as_ref()
                            .expect("the first deferred fold stores its challenge");
                        let alpha2 = alpha.square();
                        let powers = [QM31::ONE, alpha2.mul(*alpha), alpha2, *alpha];
                        let mut index = 0usize;
                        while index < N {
                            let high = index / 4;
                            let low_chunk = index & 3;
                            let mask = group_masks[usize::from(row_groups[high])];
                            let bits = (mask >> (4 * low_chunk)) & 0x0f;
                            let mut value = QM31::ZERO;
                            let mut slot = 0u32;
                            while slot < 4 {
                                if bits & (1u16 << slot) != 0 {
                                    value = value.add(powers[slot as usize]);
                                }
                                slot += 1;
                            }
                            value = value.half().half();
                            output[index] = output[index].add(value);
                            index += 1;
                        }
                    }
                    2 | 4 | 6 => {
                        debug_assert!(first_alpha.is_none());
                        let mut index = 0usize;
                        while index < N {
                            output[index] =
                                output[index].add(group_values[usize::from(row_groups[index])]);
                            index += 1;
                        }
                    }
                    _ => unreachable!("invalid deferred binary fold depth"),
                },
                WeightComponent::Grouped128x16 {
                    row_groups,
                    group_values,
                    low_width,
                } => {
                    let width = usize::from(*low_width);
                    let mut index = 0usize;
                    while index < N {
                        let group = usize::from(row_groups[index / width]);
                        output[index] =
                            output[index].add(group_values[group * width + index % width]);
                        index += 1;
                    }
                }
            }
            component_index += 1;
        }
        output
    }

    fn fold_multilinear_arity4(
        scale: &mut QM31,
        point: &mut Vec<QM31>,
        alpha: QM31,
        alpha2: QM31,
        alpha3: QM31,
    ) {
        let split = point.len() - 2;
        let z0 = point[split];
        let z1 = point[split + 1];
        let low = QM31::ONE.add(alpha3.sub(QM31::ONE).mul(z1));
        let high = alpha2.add(alpha.sub(alpha2).mul(z1));
        let factor = low.add(z0.mul(high.sub(low))).half().half();
        *scale = scale.mul(factor);
        point.truncate(split);
    }

    fn fold_tensor_arity4(
        scale: &mut QM31,
        factors: &mut Vec<QM31>,
        alpha3: QM31,
        prepared_alpha: PreparedQm31Multiplier,
        prepared_alpha2: PreparedQm31Multiplier,
    ) {
        let split = factors.len() - 2;
        let high = factors[split];
        let low = factors[split + 1];
        let prepared = [prepared_alpha2, PreparedQm31Multiplier::new(low)];
        let products =
            qm31_sum_products2_prepared(&prepared, &[high, alpha3.add(prepared_alpha.mul(high))]);
        let factor = QM31::ONE.add(products).half().half();
        *scale = scale.mul(factor);
        factors.truncate(split);
    }

    #[inline(always)]
    fn double_x_m31(x: M31) -> M31 {
        x.mul(x).double().sub(M31::ONE)
    }

    #[inline(always)]
    fn halve_qm31(mut value: QM31, count: u8) -> QM31 {
        let mut index = 0u8;
        while index < count {
            value = value.half();
            index += 1;
        }
        value
    }

    fn fold_line_m31_tensor_arity4(
        scale: &mut QM31,
        x: &mut M31,
        alpha: QM31,
        alpha2: QM31,
        alpha3: QM31,
    ) {
        let low = *x;
        let high = Self::double_x_m31(low);
        let cross = high.mul(low);
        let mixed = qm31_m31_sum_products3([alpha3, alpha2, alpha], [low, high, cross]);
        *scale = scale.mul(QM31::ONE.add(mixed).half().half());
        *x = Self::double_x_m31(high);
    }

    fn fold_line_m31_batch_arity4(
        scales: &mut [QM31],
        xs: &mut [M31],
        deferred_halvings: &mut u8,
        alpha: QM31,
        alpha2: QM31,
        alpha3: QM31,
    ) {
        debug_assert_eq!(scales.len(), xs.len());
        let mut index = 0usize;
        while index < scales.len() {
            let low = xs[index];
            let high = Self::double_x_m31(low);
            let cross = high.mul(low);
            let mixed = qm31_m31_sum_products3([alpha3, alpha2, alpha], [low, high, cross]);
            scales[index] = scales[index].mul(QM31::ONE.add(mixed));
            xs[index] = Self::double_x_m31(high);
            index += 1;
        }
        *deferred_halvings += 2;
    }

    fn fold_dense_arity4(values: &mut Vec<QM31>, alpha: QM31, alpha2: QM31, alpha3: QM31) {
        let chunk_count = values.len() / 4;
        let mut folded = Vec::with_capacity(chunk_count);
        let mut chunk_index = 0usize;
        while chunk_index < chunk_count {
            let offset = chunk_index * 4;
            folded.push(
                values[offset]
                    .add(alpha3.mul(values[offset + 1]))
                    .add(alpha2.mul(values[offset + 2]))
                    .add(alpha.mul(values[offset + 3]))
                    .half()
                    .half(),
            );
            chunk_index += 1;
        }
        *values = folded;
    }

    fn fold_grouped64_binary_deferred_arity4(
        row_groups: &mut Vec<u8>,
        group_masks: &mut Vec<u16>,
        first_alpha: &mut Option<QM31>,
        group_values: &mut Vec<QM31>,
        current_log_len: u32,
        alpha: QM31,
        alpha2: QM31,
        alpha3: QM31,
    ) {
        match current_log_len {
            10 => {
                debug_assert!(first_alpha.is_none());
                *first_alpha = Some(alpha);
            }
            8 => {
                let alpha0 = first_alpha
                    .take()
                    .expect("the first deferred fold stores its challenge");
                *group_values = fold_binary_low_masks(group_masks, alpha0, alpha);
                group_masks.clear();
            }
            6 | 4 => {
                debug_assert!(first_alpha.is_none());
                let (folded_groups, folded_values) =
                    fold_grouped_rows(row_groups, group_values, alpha, alpha2, alpha3);
                *row_groups = folded_groups;
                *group_values = folded_values;
            }
            _ => unreachable!("invalid deferred binary fold depth"),
        }
    }

    fn fold_component_arity4(
        component: &mut WeightComponent,
        current_log_len: u32,
        alpha: QM31,
        alpha2: QM31,
        alpha3: QM31,
        prepared_alpha: PreparedQm31Multiplier,
        prepared_alpha2: PreparedQm31Multiplier,
    ) -> Option<WeightComponent> {
        let mut replacement = None;
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
                Self::fold_multilinear_arity4(scale, point, alpha, alpha2, alpha3);
            }
            WeightComponent::Tensor { scale, factors } => {
                Self::fold_tensor_arity4(scale, factors, alpha3, prepared_alpha, prepared_alpha2)
            }
            WeightComponent::LineM31Tensor { scale, x } => {
                Self::fold_line_m31_tensor_arity4(scale, x, alpha, alpha2, alpha3)
            }
            WeightComponent::LineM31Batch {
                scales,
                xs,
                deferred_halvings,
            } => Self::fold_line_m31_batch_arity4(
                scales,
                xs,
                deferred_halvings,
                alpha,
                alpha2,
                alpha3,
            ),
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
                Self::fold_dense_arity4(values, alpha, alpha2, alpha3);
            }
            WeightComponent::Grouped64x16 {
                row_groups,
                group_values,
                low_width,
            } => {
                replacement = Self::fold_grouped64_arity4(
                    row_groups,
                    group_values,
                    low_width,
                    current_log_len,
                    alpha,
                    alpha2,
                    alpha3,
                );
            }
            WeightComponent::Grouped64x16BinaryDeferred {
                row_groups,
                group_masks,
                first_alpha,
                group_values,
            } => Self::fold_grouped64_binary_deferred_arity4(
                row_groups,
                group_masks,
                first_alpha,
                group_values,
                current_log_len,
                alpha,
                alpha2,
                alpha3,
            ),
            WeightComponent::Grouped128x16 {
                row_groups,
                group_values,
                low_width,
            } => {
                debug_assert!(matches!(current_log_len, 11 | 9));
                let chunk_count = group_values.len() / 4;
                let mut folded = Vec::with_capacity(chunk_count);
                let mut chunk_index = 0usize;
                while chunk_index < chunk_count {
                    let offset = chunk_index * 4;
                    folded.push(
                        group_values[offset]
                            .add(alpha3.mul(group_values[offset + 1]))
                            .add(alpha2.mul(group_values[offset + 2]))
                            .add(alpha.mul(group_values[offset + 3]))
                            .half()
                            .half(),
                    );
                    chunk_index += 1;
                }
                if *low_width == 16 {
                    *group_values = folded;
                    *low_width = 4;
                } else {
                    debug_assert_eq!(*low_width, 4);
                    let mut values = Vec::with_capacity(row_groups.len());
                    let mut row = 0usize;
                    while row < row_groups.len() {
                        values.push(folded[usize::from(row_groups[row])]);
                        row += 1;
                    }
                    replacement = Some(WeightComponent::Dense { values });
                }
            }
        }
        replacement
    }

    /// The ordinary grouped-64 arm of [`Self::fold_component_arity4`].
    ///
    /// This helper is deliberately kept separate from the other component
    /// variants so source-correspondence extraction can authenticate the
    /// deployed grouped traversal without importing unreachable enum arms.
    fn fold_grouped64_arity4(
        row_groups: &Vec<u8>,
        group_values: &mut Vec<QM31>,
        low_width: &mut u8,
        current_log_len: u32,
        alpha: QM31,
        alpha2: QM31,
        alpha3: QM31,
    ) -> Option<WeightComponent> {
        debug_assert!(matches!(current_log_len, 10 | 8));
        // This indexed loop has exactly the former `chunks_exact(4)`
        // traversal: incomplete trailing values are deliberately ignored.
        let chunk_count = group_values.len() / 4;
        let mut folded = Vec::with_capacity(chunk_count);
        let mut chunk_index = 0usize;
        while chunk_index < chunk_count {
            let offset = chunk_index * 4;
            folded.push(
                group_values[offset]
                    .add(alpha3.mul(group_values[offset + 1]))
                    .add(alpha2.mul(group_values[offset + 2]))
                    .add(alpha.mul(group_values[offset + 3]))
                    .half()
                    .half(),
            );
            chunk_index += 1;
        }
        if *low_width == 16 {
            *group_values = folded;
            *low_width = 4;
            None
        } else {
            debug_assert_eq!(*low_width, 4);
            let mut values = Vec::with_capacity(row_groups.len());
            let mut row = 0usize;
            while row < row_groups.len() {
                values.push(folded[usize::from(row_groups[row])]);
                row += 1;
            }
            Some(WeightComponent::Dense { values })
        }
    }

    /// Arity-four fold for the exact component family used by the v5
    /// incremental relation.  That relation contains only multilinear,
    /// tensor, dense and deferred grouped-binary components, so no component
    /// changes enum variant during its four folds.
    pub fn fold_deferred_relation_arity4(&mut self, alpha: QM31) {
        debug_assert!(self.log_len >= 2);
        let current_log_len = self.log_len;
        let alpha2 = alpha.square();
        let prepared_alpha = PreparedQm31Multiplier::new(alpha);
        let prepared_alpha2 = PreparedQm31Multiplier::new(alpha2);
        let alpha3 = prepared_alpha.mul(alpha2);
        let mut component_index = 0usize;
        while component_index < self.components.len() {
            match &mut self.components[component_index] {
                WeightComponent::Multilinear { scale, point } => {
                    Self::fold_multilinear_arity4(scale, point, alpha, alpha2, alpha3);
                }
                WeightComponent::Tensor { scale, factors } => Self::fold_tensor_arity4(
                    scale,
                    factors,
                    alpha3,
                    prepared_alpha,
                    prepared_alpha2,
                ),
                WeightComponent::LineM31Tensor { scale, x } => {
                    Self::fold_line_m31_tensor_arity4(scale, x, alpha, alpha2, alpha3)
                }
                WeightComponent::LineM31Batch {
                    scales,
                    xs,
                    deferred_halvings,
                } => Self::fold_line_m31_batch_arity4(
                    scales,
                    xs,
                    deferred_halvings,
                    alpha,
                    alpha2,
                    alpha3,
                ),
                WeightComponent::Dense { values } => {
                    Self::fold_dense_arity4(values, alpha, alpha2, alpha3);
                }
                WeightComponent::Grouped64x16BinaryDeferred {
                    row_groups,
                    group_masks,
                    first_alpha,
                    group_values,
                } => Self::fold_grouped64_binary_deferred_arity4(
                    row_groups,
                    group_masks,
                    first_alpha,
                    group_values,
                    current_log_len,
                    alpha,
                    alpha2,
                    alpha3,
                ),
                _ => unreachable!("unsupported deferred-relation component"),
            }
            component_index += 1;
        }
        self.log_len -= 2;
    }

    /// Apply the exact three-round Tag-73 relation-weight tail.
    ///
    /// Round one remains an ordinary dual arity-four fold and is followed at
    /// the same semantic point by the checked merge of multilinear
    /// components zero and two. The last two folds are then traversed once
    /// per remaining component. Only the deferred 64-row schedule changes
    /// representation: its two dual maps are tensored into one arity-16 map.
    /// No transcript challenge, running claim, or terminal weight changes.
    #[inline(never)]
    pub fn fold_tag73_relation_tail_arity4(&mut self, alphas: [QM31; 3]) -> bool {
        if self.log_len != 8 {
            return false;
        }

        self.fold_deferred_relation_arity4(alphas[0]);
        if !self.merge_equal_multilinear_components(0, 2) {
            return false;
        }

        let alpha2 = [alphas[1].square(), alphas[2].square()];
        let prepared_alpha = [
            PreparedQm31Multiplier::new(alphas[1]),
            PreparedQm31Multiplier::new(alphas[2]),
        ];
        let prepared_alpha2 = [
            PreparedQm31Multiplier::new(alpha2[0]),
            PreparedQm31Multiplier::new(alpha2[1]),
        ];
        let alpha3 = [
            prepared_alpha[0].mul(alpha2[0]),
            prepared_alpha[1].mul(alpha2[1]),
        ];

        let mut component_index = 0usize;
        while component_index < self.components.len() {
            match &mut self.components[component_index] {
                WeightComponent::Multilinear { scale, point } => {
                    Self::fold_multilinear_arity4(scale, point, alphas[1], alpha2[0], alpha3[0]);
                    Self::fold_multilinear_arity4(scale, point, alphas[2], alpha2[1], alpha3[1]);
                }
                WeightComponent::Tensor { scale, factors } => {
                    Self::fold_tensor_arity4(
                        scale,
                        factors,
                        alpha3[0],
                        prepared_alpha[0],
                        prepared_alpha2[0],
                    );
                    Self::fold_tensor_arity4(
                        scale,
                        factors,
                        alpha3[1],
                        prepared_alpha[1],
                        prepared_alpha2[1],
                    );
                }
                WeightComponent::LineM31Tensor { scale, x } => {
                    Self::fold_line_m31_tensor_arity4(scale, x, alphas[1], alpha2[0], alpha3[0]);
                    Self::fold_line_m31_tensor_arity4(scale, x, alphas[2], alpha2[1], alpha3[1]);
                }
                WeightComponent::LineM31Batch {
                    scales,
                    xs,
                    deferred_halvings,
                } => {
                    Self::fold_line_m31_batch_arity4(
                        scales,
                        xs,
                        deferred_halvings,
                        alphas[1],
                        alpha2[0],
                        alpha3[0],
                    );
                    Self::fold_line_m31_batch_arity4(
                        scales,
                        xs,
                        deferred_halvings,
                        alphas[2],
                        alpha2[1],
                        alpha3[1],
                    );
                }
                WeightComponent::Dense { values } => {
                    Self::fold_dense_arity4(values, alphas[1], alpha2[0], alpha3[0]);
                    Self::fold_dense_arity4(values, alphas[2], alpha2[1], alpha3[1]);
                }
                WeightComponent::Grouped64x16BinaryDeferred {
                    row_groups,
                    group_masks,
                    first_alpha,
                    group_values,
                } => {
                    if !group_masks.is_empty() || first_alpha.is_some() || row_groups.len() != 64 {
                        return false;
                    }
                    let (folded_groups, folded_values) =
                        fold_grouped_rows_twice(row_groups, group_values, alphas[1], alphas[2]);
                    *row_groups = folded_groups;
                    *group_values = folded_values;
                }
                _ => return false,
            }
            component_index += 1;
        }
        self.log_len = 2;
        true
    }

    /// Apply the dual of the arity-4 monomial coefficient fold.
    pub fn fold(&mut self, alpha: QM31) {
        debug_assert!(self.log_len >= 2);
        let current_log_len = self.log_len;
        let alpha2 = alpha.square();
        let prepared_alpha = PreparedQm31Multiplier::new(alpha);
        let prepared_alpha2 = PreparedQm31Multiplier::new(alpha2);
        let alpha3 = prepared_alpha.mul(alpha2);
        self.fold_all_components_arity4(
            current_log_len,
            alpha,
            alpha2,
            alpha3,
            prepared_alpha,
            prepared_alpha2,
        );
        self.log_len -= 2;
    }

    /// Indexed spelling of the public fold dispatcher. This preserves the
    /// former mutable-iterator order while exposing the exact call graph to
    /// source-correspondence extraction.
    fn fold_all_components_arity4(
        &mut self,
        current_log_len: u32,
        alpha: QM31,
        alpha2: QM31,
        alpha3: QM31,
        prepared_alpha: PreparedQm31Multiplier,
        prepared_alpha2: PreparedQm31Multiplier,
    ) {
        let mut component_index = 0usize;
        while component_index < self.components.len() {
            let component = &mut self.components[component_index];
            let replacement = Self::fold_component_arity4(
                component,
                current_log_len,
                alpha,
                alpha2,
                alpha3,
                prepared_alpha,
                prepared_alpha2,
            );
            if let Some(replacement) = replacement {
                *component = replacement;
            }
            component_index += 1;
        }
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
            // All V6 query checks arrive here as line tensors over the same
            // four final coefficients.  Linearity lets us sum their four
            // covector coordinates first, then perform one four-product
            // extension-field dot.  The former spelling performed one full
            // QM31 multiplication per query after independently evaluating
            // the same coefficient tuple.
            let line_deferred_halvings = self
                .components
                .iter()
                .filter_map(|component| match component {
                    WeightComponent::LineM31Batch {
                        deferred_halvings, ..
                    } => Some(*deferred_halvings),
                    _ => None,
                })
                .max()
                .unwrap_or(0);
            let mut line_count = 0usize;
            let mut line_constant_limbs = [M31::ZERO; 4];
            let mut line_raw = [[0u64; 4]; 3];
            let mut line_sums = [[M31::ZERO; 4]; 3];
            for component in &self.components {
                let mut accumulate_line = |mut scale: QM31, x: M31, mut halvings: u8| {
                    while halvings < line_deferred_halvings {
                        scale = scale.add(scale);
                        halvings += 1;
                    }
                    let high = Self::double_x_m31(x);
                    let factors = [x, high, x.mul(high)];
                    let limbs = [scale.c0.a.0, scale.c0.b.0, scale.c1.a.0, scale.c1.b.0];
                    for limb in 0..4 {
                        line_constant_limbs[limb] = line_constant_limbs[limb].add(M31(limbs[limb]));
                        for slot in 0..3 {
                            line_raw[slot][limb] +=
                                u64::from(limbs[limb]) * u64::from(factors[slot].0);
                        }
                    }
                    line_count += 1;
                    if line_count % 4 == 0 {
                        for slot in 0..3 {
                            for limb in 0..4 {
                                line_sums[slot][limb] = line_sums[slot][limb]
                                    .add(M31::reduce_u64(line_raw[slot][limb]));
                                line_raw[slot][limb] = 0;
                            }
                        }
                    }
                };
                match component {
                    WeightComponent::LineM31Tensor { scale, x } => accumulate_line(*scale, *x, 0),
                    WeightComponent::LineM31Batch {
                        scales,
                        xs,
                        deferred_halvings,
                    } => {
                        for (&scale, &x) in scales.iter().zip(xs) {
                            accumulate_line(scale, x, *deferred_halvings);
                        }
                    }
                    _ => {}
                }
            }
            if line_count % 4 != 0 {
                for slot in 0..3 {
                    for limb in 0..4 {
                        line_sums[slot][limb] =
                            line_sums[slot][limb].add(M31::reduce_u64(line_raw[slot][limb]));
                    }
                }
            }
            let from_limbs = |limbs: [M31; 4]| QM31 {
                c0: CM31::new(limbs[0], limbs[1]),
                c1: CM31::new(limbs[2], limbs[3]),
            };
            let mut total = if line_count == 0 {
                QM31::ZERO
            } else {
                Self::halve_qm31(
                    qm31_sum_products4(
                        [
                            from_limbs(line_constant_limbs),
                            from_limbs(line_sums[0]),
                            from_limbs(line_sums[1]),
                            from_limbs(line_sums[2]),
                        ],
                        [values[0], values[1], values[2], values[3]],
                    ),
                    line_deferred_halvings,
                )
            };
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
                    WeightComponent::LineM31Tensor { .. } => QM31::ZERO,
                    WeightComponent::LineM31Batch { .. } => QM31::ZERO,
                    WeightComponent::Product { scale, pairs } => {
                        debug_assert_eq!(pairs.len(), 2);
                        let evaluation = values[0]
                            .mul(pairs[0][0].mul(pairs[1][0]))
                            .add(values[1].mul(pairs[0][0].mul(pairs[1][1])))
                            .add(values[2].mul(pairs[0][1].mul(pairs[1][0])))
                            .add(values[3].mul(pairs[0][1].mul(pairs[1][1])));
                        scale.mul(evaluation)
                    }
                    WeightComponent::Dense { values: weights } => {
                        let mut sum = QM31::ZERO;
                        let mut index = 0usize;
                        while index < values.len() {
                            sum = sum.add(values[index].mul(weights[index]));
                            index += 1;
                        }
                        sum
                    }
                    WeightComponent::Grouped64x16 { .. } => {
                        unreachable!("grouped component becomes dense before log length two")
                    }
                    WeightComponent::Grouped64x16BinaryDeferred {
                        row_groups,
                        group_values,
                        ..
                    } => {
                        let mut sum = QM31::ZERO;
                        let mut index = 0usize;
                        while index < values.len() {
                            sum = sum.add(
                                values[index].mul(group_values[usize::from(row_groups[index])]),
                            );
                            index += 1;
                        }
                        sum
                    }
                    WeightComponent::Grouped128x16 { .. } => {
                        unreachable!("grouped component becomes dense before log length two")
                    }
                };
                total = total.add(contribution);
            }
            return total;
        }
        let mut sum = QM31::ZERO;
        let mut index = 0usize;
        while index < values.len() {
            sum = sum.add(values[index].mul(self.weight_at(index as u32)));
            index += 1;
        }
        sum
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
    let mut acc = polynomial[SUMCHECK_COEFFICIENTS - 1];
    let mut degree = SUMCHECK_COEFFICIENTS - 1;
    while degree > 0 {
        degree -= 1;
        acc = acc.mul(point).add(polynomial[degree]);
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circle::secure_circle_point_from_parameter;
    use crate::field::{CM31, M31};
    use alloc::vec;

    extern crate std;

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

    /// The exact former iterator spelling of the legacy grouped dual fold,
    /// materialized as a dense covector for differential testing.
    fn grouped_64x16_fold_reference(
        row_groups: &[u8],
        group_values: &[QM31],
        low_width: u8,
        alpha: QM31,
    ) -> Vec<QM31> {
        let alpha2 = alpha.square();
        let alpha3 = alpha2.mul(alpha);
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
        if low_width == 16 {
            row_groups
                .iter()
                .flat_map(|&group| {
                    let start = usize::from(group) * 4;
                    folded[start..start + 4].iter().copied()
                })
                .collect()
        } else {
            debug_assert_eq!(low_width, 4);
            row_groups
                .iter()
                .map(|&group| folded[usize::from(group)])
                .collect()
        }
    }

    /// The complete pre-helper branch state, kept test-only as a differential
    /// oracle for mutation, replacement, and malformed-tail behavior.
    fn grouped_64x16_branch_reference(
        row_groups: &[u8],
        group_values: &[QM31],
        low_width: u8,
        alpha: QM31,
    ) -> (Vec<QM31>, u8, Option<Vec<QM31>>) {
        let alpha2 = alpha.square();
        let alpha3 = alpha2.mul(alpha);
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
        if low_width == 16 {
            (folded, 4, None)
        } else {
            debug_assert_eq!(low_width, 4);
            let values = row_groups
                .iter()
                .map(|&group| folded[usize::from(group)])
                .collect();
            (group_values.to_vec(), low_width, Some(values))
        }
    }

    fn run_grouped64_helper(
        row_groups: Vec<u8>,
        mut group_values: Vec<QM31>,
        mut low_width: u8,
        alpha: QM31,
    ) -> (Vec<QM31>, u8, Option<Vec<QM31>>) {
        let alpha2 = alpha.square();
        let prepared_alpha = PreparedQm31Multiplier::new(alpha);
        let alpha3 = prepared_alpha.mul(alpha2);
        let current_log_len = if low_width == 16 { 10 } else { 8 };
        let replacement = WeightAccumulator::fold_grouped64_arity4(
            &row_groups,
            &mut group_values,
            &mut low_width,
            current_log_len,
            alpha,
            alpha2,
            alpha3,
        );
        let dense = replacement.map(|component| match component {
            WeightComponent::Dense { values } => values,
            _ => panic!("ordinary grouped fold returned a non-dense replacement"),
        });
        (group_values, low_width, dense)
    }

    fn run_grouped64_component_wrapper(
        row_groups: Vec<u8>,
        group_values: Vec<QM31>,
        low_width: u8,
        alpha: QM31,
    ) -> (Vec<QM31>, u8, Option<Vec<QM31>>) {
        let alpha2 = alpha.square();
        let prepared_alpha = PreparedQm31Multiplier::new(alpha);
        let prepared_alpha2 = PreparedQm31Multiplier::new(alpha2);
        let alpha3 = prepared_alpha.mul(alpha2);
        let mut component = WeightComponent::Grouped64x16 {
            row_groups,
            group_values,
            low_width,
        };
        let replacement = WeightAccumulator::fold_component_arity4(
            &mut component,
            if low_width == 16 { 10 } else { 8 },
            alpha,
            alpha2,
            alpha3,
            prepared_alpha,
            prepared_alpha2,
        );
        let (group_values, low_width) = match component {
            WeightComponent::Grouped64x16 {
                group_values,
                low_width,
                ..
            } => (group_values, low_width),
            _ => panic!("component wrapper changed the input before replacement"),
        };
        let dense = replacement.map(|component| match component {
            WeightComponent::Dense { values } => values,
            _ => panic!("ordinary grouped fold returned a non-dense replacement"),
        });
        (group_values, low_width, dense)
    }

    /// The exact pre-refactor spelling of the log-10 deferred lookup. This is
    /// test-only differential evidence; production `weight_at` calls the
    /// extracted helper above.
    fn grouped_64x16_binary_deferred_weight_at_log10_reference(
        row_groups: &[u8],
        group_masks: &[u16],
        index: u32,
    ) -> QM31 {
        let high = index as usize / 16;
        let low = index as usize & 15;
        let mask = group_masks[usize::from(row_groups[high])];
        if mask & (1 << low) == 0 {
            QM31::ZERO
        } else {
            QM31::ONE
        }
    }

    #[test]
    fn log10_deferred_lookup_helper_matches_reference_for_every_row_and_bounds() {
        let fixed_masks = [0x0000, 0x0002, 0x4000, 0xe7ff, 0xeffe, 0xfd00, 0xffff];
        let fixed_groups: [u8; 64] =
            core::array::from_fn(|high| ((high * 5 + high / 7 + 3) % fixed_masks.len()) as u8);

        for index in 0..1024u32 {
            let expected = grouped_64x16_binary_deferred_weight_at_log10_reference(
                &fixed_groups,
                &fixed_masks,
                index,
            );
            assert_eq!(
                grouped_64x16_binary_deferred_weight_at_log10(&fixed_groups, &fixed_masks, index,),
                expected,
                "fixed index={index}"
            );
        }

        let mut state = 0x5745_4947_4854_3130u64;
        for case in 1..=64usize {
            let group_len = 1 + case % 23;
            let group_masks = (0..group_len)
                .map(|_| next(&mut state).0 as u16)
                .collect::<Vec<_>>();
            let row_groups: [u8; 64] =
                core::array::from_fn(|_| (next(&mut state).0 as usize % group_len) as u8);
            let mut accumulator = WeightAccumulator::empty(10);
            accumulator
                .add_grouped_64x16_binary_masks_deferred_prepared(&row_groups, &group_masks)
                .unwrap();

            for index in 0..1024u32 {
                let expected = grouped_64x16_binary_deferred_weight_at_log10_reference(
                    &row_groups,
                    &group_masks,
                    index,
                );
                assert_eq!(
                    grouped_64x16_binary_deferred_weight_at_log10(&row_groups, &group_masks, index,),
                    expected,
                    "case={case} index={index}"
                );
                assert_eq!(
                    accumulator.weight_at(index),
                    expected,
                    "production caller case={case} index={index}"
                );
            }
        }

        let short_groups = [0u8; 63];
        assert!(std::panic::catch_unwind(|| {
            grouped_64x16_binary_deferred_weight_at_log10_reference(
                &short_groups,
                &fixed_masks,
                1023,
            )
        })
        .is_err());
        assert!(std::panic::catch_unwind(|| {
            grouped_64x16_binary_deferred_weight_at_log10(&short_groups, &fixed_masks, 1023)
        })
        .is_err());

        let mut out_of_range_group = [0u8; 64];
        out_of_range_group[62] = 1;
        assert!(std::panic::catch_unwind(|| {
            grouped_64x16_binary_deferred_weight_at_log10_reference(
                &out_of_range_group,
                &[0u16],
                993,
            )
        })
        .is_err());
        assert!(std::panic::catch_unwind(|| {
            grouped_64x16_binary_deferred_weight_at_log10(&out_of_range_group, &[0u16], 993)
        })
        .is_err());
    }

    #[test]
    fn log10_deferred_lookup_row993_and_mutation_teeth() {
        let mut row_groups = [0u8; 64];
        row_groups[62] = 6;
        let mut group_masks = [0u16; 7];
        group_masks[6] = 0xffff;

        assert_eq!(
            grouped_64x16_binary_deferred_weight_at_log10(&row_groups, &group_masks, 993),
            QM31::ONE
        );

        let mut wrong_group = row_groups;
        wrong_group[62] = 0;
        assert_eq!(
            grouped_64x16_binary_deferred_weight_at_log10(&wrong_group, &group_masks, 993),
            QM31::ZERO
        );

        let mut flipped_bit = group_masks;
        flipped_bit[6] ^= 1u16 << 1;
        assert_eq!(
            grouped_64x16_binary_deferred_weight_at_log10(&row_groups, &flipped_bit, 993),
            QM31::ZERO
        );

        let mut reversed_bit = group_masks;
        reversed_bit[6] = 1u16 << 14;
        assert_eq!(
            grouped_64x16_binary_deferred_weight_at_log10(&row_groups, &reversed_bit, 993),
            QM31::ZERO
        );
    }

    #[test]
    fn deferred_relation_fold_matches_generic_fold_after_every_round() {
        let mut state = 0x4445_4645_5252_4544u64;
        let mut accumulator = WeightAccumulator::empty(10);
        accumulator
            .add_multilinear(q(3), (0..10).map(|_| random_q(&mut state)).collect())
            .unwrap();
        accumulator
            .add_tensor_factors(q(5), (0..10).map(|_| random_q(&mut state)).collect())
            .unwrap();
        accumulator
            .add_dense((0..1024).map(|_| random_q(&mut state)).collect())
            .unwrap();
        let masks = core::array::from_fn(|row| {
            let rotate = (row % 16) as u32;
            (0xa53cu16).rotate_left(rotate) ^ ((row as u16).wrapping_mul(0x0101))
        });
        accumulator
            .add_grouped_64x16_binary_masks_deferred(masks)
            .unwrap();

        let mut generic = accumulator.clone();
        let mut specialized = accumulator;
        for round in 0..4 {
            let alpha = random_q(&mut state);
            generic.fold(alpha);
            specialized.fold_deferred_relation_arity4(alpha);
            assert_eq!(generic.log_len, specialized.log_len, "round={round}");
            let size = 1u32 << generic.log_len;
            for index in 0..size {
                assert_eq!(
                    generic.weight_at(index),
                    specialized.weight_at(index),
                    "round={round} index={index}"
                );
            }
        }
    }

    #[test]
    fn composed_grouped_high_rows_match_two_sequential_folds() {
        let mut state = 0x434f_4d50_4f53_4544u64;
        for case in 0..64usize {
            let group_count = 1 + case % 23;
            let row_groups = (0..64)
                .map(|row| ((next(&mut state).0 as usize + row * 7 + row / 9) % group_count) as u8)
                .collect::<Vec<_>>();
            let group_values = (0..group_count)
                .map(|_| random_q(&mut state))
                .collect::<Vec<_>>();
            let alpha1 = random_q(&mut state);
            let alpha2 = random_q(&mut state);

            let alpha1_2 = alpha1.square();
            let alpha2_2 = alpha2.square();
            let (once_groups, once_values) = fold_grouped_rows(
                &row_groups,
                &group_values,
                alpha1,
                alpha1_2,
                alpha1_2.mul(alpha1),
            );
            let (sequential_groups, sequential_values) = fold_grouped_rows(
                &once_groups,
                &once_values,
                alpha2,
                alpha2_2,
                alpha2_2.mul(alpha2),
            );
            let (composed_groups, composed_values) =
                fold_grouped_rows_twice(&row_groups, &group_values, alpha1, alpha2);

            for index in 0..4usize {
                assert_eq!(
                    sequential_values[usize::from(sequential_groups[index])],
                    composed_values[usize::from(composed_groups[index])],
                    "case={case} index={index}",
                );
            }
        }
    }

    #[test]
    fn tag73_composed_weight_tail_matches_sequential_rounds() {
        let mut state = 0x5441_4737_3354_4149u64;
        for case in 0..32usize {
            let shared_prefix = (0..6).map(|_| random_q(&mut state)).collect::<Vec<_>>();
            let mut point_zero = shared_prefix.clone();
            point_zero.extend((0..4).map(|_| random_q(&mut state)));
            let point_one = (0..10).map(|_| random_q(&mut state)).collect::<Vec<_>>();
            let mut point_two = shared_prefix;
            point_two.extend((0..4).map(|_| random_q(&mut state)));

            let mut base = WeightAccumulator::empty(10);
            base.add_multilinear(random_q(&mut state), point_zero)
                .unwrap();
            base.add_multilinear(random_q(&mut state), point_one)
                .unwrap();
            base.add_multilinear(random_q(&mut state), point_two)
                .unwrap();
            let masks = core::array::from_fn(|row| {
                let rotation = ((row * 5 + row / 7 + case) & 15) as u32;
                (next(&mut state).0 as u16).rotate_left(rotation)
            });
            base.add_grouped_64x16_binary_masks_deferred(masks).unwrap();
            for _ in 0..2 {
                base.add_circle_tensor(
                    random_q(&mut state),
                    SecureCirclePoint {
                        x: random_q(&mut state),
                        y: random_q(&mut state),
                    },
                )
                .unwrap();
            }

            let alpha0 = random_q(&mut state);
            base.fold_deferred_relation_arity4(alpha0);
            let scales = core::array::from_fn::<_, 16, _>(|_| random_q(&mut state));
            let xs = core::array::from_fn::<_, 16, _>(|_| next(&mut state));
            base.add_line_m31_batch(&scales, &xs).unwrap();

            let alphas = core::array::from_fn(|_| random_q(&mut state));
            let mut sequential = base.clone();
            sequential.fold_deferred_relation_arity4(alphas[0]);
            assert!(sequential.merge_equal_multilinear_components(0, 2));
            sequential.fold_deferred_relation_arity4(alphas[1]);
            sequential.fold_deferred_relation_arity4(alphas[2]);

            let mut composed = base;
            assert!(composed.fold_tag73_relation_tail_arity4(alphas));
            assert_eq!(sequential.log_len, composed.log_len, "case={case}");
            for index in 0..4u32 {
                assert_eq!(
                    sequential.weight_at(index),
                    composed.weight_at(index),
                    "case={case} index={index}",
                );
            }
            let terminal = core::array::from_fn::<_, 4, _>(|_| random_q(&mut state));
            assert_eq!(sequential.dot(&terminal), composed.dot(&terminal));
        }
    }

    /// The exact former iterator spelling of the grouped-128 constructor.
    /// Production uses indexed loops; this remains test-only differential
    /// evidence for first-occurrence grouping and low-bit table order.
    fn grouped_128x16_builder_reference(row_masks: &[u16; 128]) -> (Vec<u8>, Vec<QM31>) {
        let mut unique_masks = Vec::<u16>::new();
        let row_groups = row_masks
            .iter()
            .map(|&mask| {
                let group = unique_masks
                    .iter()
                    .position(|&candidate| candidate == mask)
                    .unwrap_or_else(|| {
                        unique_masks.push(mask);
                        unique_masks.len() - 1
                    });
                group as u8
            })
            .collect::<Vec<_>>();
        let group_values = unique_masks
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
        (row_groups, group_values)
    }

    fn assert_weight_prefix_matches_weight_at<const N: usize>(weights: &WeightAccumulator) {
        assert_eq!(
            weights.weight_prefix::<N>(),
            core::array::from_fn(|index| weights.weight_at(index as u32))
        );
    }

    #[test]
    fn indexed_grouped_64x16_fold_matches_former_iterator_spelling() {
        let mut state = 0x4752_4f55_5046_4f4cu64;
        for low_width in [16u8, 4u8] {
            for case in 0..32usize {
                let group_count = 1 + case % 13;
                let row_groups = (0..64)
                    .map(|_| (next(&mut state).0 as usize % group_count) as u8)
                    .collect::<Vec<_>>();
                let group_values = (0..group_count * usize::from(low_width))
                    .map(|_| random_q(&mut state))
                    .collect::<Vec<_>>();
                let alpha = random_q(&mut state);
                let branch_expected =
                    grouped_64x16_branch_reference(&row_groups, &group_values, low_width, alpha);
                assert_eq!(
                    run_grouped64_helper(
                        row_groups.clone(),
                        group_values.clone(),
                        low_width,
                        alpha,
                    ),
                    branch_expected,
                );
                assert_eq!(
                    run_grouped64_component_wrapper(
                        row_groups.clone(),
                        group_values.clone(),
                        low_width,
                        alpha,
                    ),
                    branch_expected,
                );
                let expected =
                    grouped_64x16_fold_reference(&row_groups, &group_values, low_width, alpha);
                let mut actual = WeightAccumulator {
                    log_len: if low_width == 16 { 10 } else { 8 },
                    components: vec![WeightComponent::Grouped64x16 {
                        row_groups,
                        group_values,
                        low_width,
                    }],
                };
                actual.fold(alpha);
                assert_eq!(1usize << actual.log_len, expected.len());
                for (index, expected_value) in expected.into_iter().enumerate() {
                    assert_eq!(
                        actual.weight_at(index as u32),
                        expected_value,
                        "low_width={low_width} case={case} index={index}",
                    );
                }
            }
        }
    }

    #[test]
    fn grouped_64x16_helper_preserves_malformed_tail_and_table_boundaries() {
        let alpha = q(7);
        for (row_groups, group_values, low_width) in [
            (Vec::new(), Vec::new(), 16),
            (Vec::new(), Vec::new(), 4),
            (vec![0], vec![q(1), q(2), q(3), q(4), q(99)], 16),
            (vec![0], vec![q(1), q(2), q(3), q(4), q(99)], 4),
            (
                (0..64).map(|row| (row % 256) as u8).collect(),
                (0..256 * 16).map(|index| q((index + 1) as u32)).collect(),
                16,
            ),
            (
                (0..64).map(|row| (row % 256) as u8).collect(),
                (0..256 * 4).map(|index| q((index + 1) as u32)).collect(),
                4,
            ),
        ] {
            let expected =
                grouped_64x16_branch_reference(&row_groups, &group_values, low_width, alpha);
            assert_eq!(
                run_grouped64_helper(row_groups.clone(), group_values.clone(), low_width, alpha,),
                expected,
            );
            assert_eq!(
                run_grouped64_component_wrapper(row_groups, group_values, low_width, alpha),
                expected,
            );
        }
    }

    #[test]
    fn grouped_64x16_helper_preserves_invalid_group_failure() {
        use std::panic::{catch_unwind, AssertUnwindSafe};

        let rows = vec![1];
        let values = vec![q(1), q(2), q(3), q(4)];
        let alpha = q(3);
        assert!(catch_unwind(AssertUnwindSafe(|| {
            grouped_64x16_branch_reference(&rows, &values, 4, alpha)
        }))
        .is_err());
        assert!(catch_unwind(AssertUnwindSafe(|| {
            run_grouped64_helper(rows.clone(), values.clone(), 4, alpha)
        }))
        .is_err());
        assert!(catch_unwind(AssertUnwindSafe(|| {
            run_grouped64_component_wrapper(rows, values, 4, alpha)
        }))
        .is_err());
    }

    #[test]
    fn grouped_64x16_fold_order_and_all_four_terms_are_observable() {
        let alpha = q(2);
        let values = vec![q(1), q(2), q(4), q(8)];
        let correct = grouped_64x16_branch_reference(&[], &values, 16, alpha).0[0];
        let alpha2 = alpha.square();
        let alpha3 = alpha2.mul(alpha);
        let reversed = values[3]
            .add(alpha3.mul(values[2]))
            .add(alpha2.mul(values[1]))
            .add(alpha.mul(values[0]))
            .half()
            .half();
        let omitted = values[0]
            .add(alpha3.mul(values[1]))
            .add(alpha2.mul(values[2]))
            .half()
            .half();
        assert_ne!(correct, reversed);
        assert_ne!(correct, omitted);
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

    #[test]
    fn indexed_weight_prefix_preserves_product_order_and_dense_shortest_input() {
        let mut product = WeightAccumulator::empty(2);
        product
            .add_product_pairs(q(1), vec![[q(1), q(2)], [q(3), q(4)]])
            .unwrap();
        assert_eq!(product.weight_prefix::<4>(), [q(3), q(4), q(6), q(8)]);

        let malformed_dense = WeightAccumulator {
            log_len: 2,
            components: vec![WeightComponent::Dense {
                values: vec![q(7), q(8)],
            }],
        };
        assert_eq!(
            malformed_dense.weight_prefix::<4>(),
            [q(7), q(8), QM31::ZERO, QM31::ZERO]
        );
    }

    #[test]
    fn indexed_weight_prefix_matches_weight_at_for_every_component_branch() {
        let empty = WeightAccumulator::empty(0);
        assert_weight_prefix_matches_weight_at::<0>(&empty);

        let mut structured = WeightAccumulator::empty(2);
        structured.add_geometric(q(2), q(3));
        structured.add_multilinear(q(5), vec![q(7), q(11)]).unwrap();
        structured
            .add_tensor_factors(q(13), vec![q(17), q(19)])
            .unwrap();
        structured
            .add_product_pairs(q(23), vec![[q(29), q(31)], [q(37), q(41)]])
            .unwrap();
        structured
            .add_dense(vec![q(43), q(47), q(53), q(59)])
            .unwrap();
        assert_weight_prefix_matches_weight_at::<4>(&structured);

        let masks64 = core::array::from_fn(|high| {
            [0x0001, 0x8000, 0xa55a, 0x5aa5][(high * 3 + high / 7) & 3]
        });
        let mut grouped64 = WeightAccumulator::empty(10);
        grouped64.add_grouped_64x16_binary_masks(masks64).unwrap();
        assert_weight_prefix_matches_weight_at::<1024>(&grouped64);

        let mut deferred10 = WeightAccumulator::empty(10);
        deferred10
            .add_grouped_64x16_binary_masks_deferred(masks64)
            .unwrap();
        assert_weight_prefix_matches_weight_at::<1024>(&deferred10);

        let deferred8 = WeightAccumulator {
            log_len: 8,
            components: vec![WeightComponent::Grouped64x16BinaryDeferred {
                row_groups: (0..64).map(|high| (high & 1) as u8).collect(),
                group_masks: vec![0xa55a, 0x5aa5],
                first_alpha: Some(q(2)),
                group_values: Vec::new(),
            }],
        };
        assert_weight_prefix_matches_weight_at::<256>(&deferred8);

        let deferred6 = WeightAccumulator {
            log_len: 6,
            components: vec![WeightComponent::Grouped64x16BinaryDeferred {
                row_groups: (0..64).map(|high| (high & 1) as u8).collect(),
                group_masks: Vec::new(),
                first_alpha: None,
                group_values: vec![q(61), q(67)],
            }],
        };
        assert_weight_prefix_matches_weight_at::<64>(&deferred6);

        let masks128 = core::array::from_fn(|high| {
            [0x0001, 0x8000, 0xa55a, 0x5aa5][(high * 3 + high / 11) & 3]
        });
        let mut grouped128 = WeightAccumulator::empty(11);
        grouped128
            .add_grouped_128x16_binary_masks(masks128)
            .unwrap();
        assert_weight_prefix_matches_weight_at::<2048>(&grouped128);
    }

    #[test]
    #[should_panic]
    fn zero_length_product_prefix_preserves_bounds_failure() {
        let accumulator = WeightAccumulator {
            log_len: 0,
            components: vec![WeightComponent::Product {
                scale: QM31::ONE,
                pairs: Vec::new(),
            }],
        };
        let _ = accumulator.weight_prefix::<0>();
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
    fn indexed_grouped_128x16_builder_matches_former_iterator_spelling() {
        let masks = [0x0001, 0x8000, 0x0001, 0xa55a, 0xffff, 0x0000];
        let row_masks: [u16; 128] = core::array::from_fn(|high| {
            if high < 3 {
                [0x0001, 0x8000, 0x0001][high]
            } else {
                masks[(high * 5 + high / 9) % masks.len()]
            }
        });
        let (expected_groups, expected_values) = grouped_128x16_builder_reference(&row_masks);

        let mut actual = WeightAccumulator::empty(11);
        actual.add_grouped_128x16_binary_masks(row_masks).unwrap();
        match actual.components.as_slice() {
            [WeightComponent::Grouped128x16 {
                row_groups,
                group_values,
                low_width,
            }] => {
                assert_eq!(row_groups, &expected_groups);
                assert_eq!(group_values, &expected_values);
                assert_eq!(*low_width, 16);
                assert_eq!(&row_groups[..3], &[0, 1, 0]);
                assert_eq!(group_values[0], QM31::ONE);
                assert_eq!(group_values[15], QM31::ZERO);
                assert_eq!(group_values[16], QM31::ZERO);
                assert_eq!(group_values[31], QM31::ONE);
                assert!(row_groups
                    .iter()
                    .all(|&group| { usize::from(group) * 16 + 15 < group_values.len() }));
            }
            other => panic!("unexpected grouped-128 layout: {other:?}"),
        }

        let mut wrong_log = WeightAccumulator::empty(10);
        assert_eq!(
            wrong_log.add_grouped_128x16_binary_masks(row_masks),
            Err(TensorWeightError::Grouped128x16LogLength)
        );
        assert!(wrong_log.components.is_empty());

        let mut state = 0x4752_4f55_5031_2816u64;
        for _ in 0..16 {
            let row_masks = core::array::from_fn(|high| {
                let choice = (next(&mut state).0 as usize + high / 11) & 15;
                (0x9e37u16).rotate_left(choice as u32)
            });
            let expected = grouped_128x16_builder_reference(&row_masks);
            let mut actual = WeightAccumulator::empty(11);
            actual.add_grouped_128x16_binary_masks(row_masks).unwrap();
            match actual.components.as_slice() {
                [WeightComponent::Grouped128x16 {
                    row_groups,
                    group_values,
                    low_width: 16,
                }] => {
                    assert_eq!(row_groups, &expected.0);
                    assert_eq!(group_values, &expected.1);
                }
                other => panic!("unexpected grouped-128 layout: {other:?}"),
            }
        }
    }

    #[test]
    #[should_panic]
    fn manually_malformed_grouped_128x16_reference_preserves_bounds_failure() {
        let accumulator = WeightAccumulator {
            log_len: 11,
            components: vec![WeightComponent::Grouped128x16 {
                row_groups: vec![1; 128],
                group_values: vec![QM31::ZERO; 16],
                low_width: 16,
            }],
        };
        let _ = accumulator.weight_prefix::<1>();
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
                assert_eq!(
                    polynomial_for_extension(&terminal_values, &deferred),
                    polynomial_for_extension(&terminal_values, &legacy),
                    "seed={seed} log_len={} polynomial",
                    legacy.log_len
                );
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
    fn deferred_wrapper_and_prepared_installer_install_the_identical_schedule() {
        let masks = [
            0xe7ff, 0xe7fe, 0xeffe, 0x4000, 0xfd00, 0xff00, 0xfffa, 0xffff,
        ];
        let row_masks: [u16; 64] =
            core::array::from_fn(|high| masks[(high * 5 + high / 7 + 3) & 7]);

        let mut expected_masks = Vec::<u16>::new();
        let mut expected_groups = [0u8; 64];
        for (high, mask) in row_masks.into_iter().enumerate() {
            let mut group = 0usize;
            while group < expected_masks.len() && expected_masks[group] != mask {
                group += 1;
            }
            if group == expected_masks.len() {
                expected_masks.push(mask);
            }
            expected_groups[high] = group as u8;
        }

        let mut from_masks = WeightAccumulator::empty(10);
        from_masks
            .add_grouped_64x16_binary_masks_deferred(row_masks)
            .unwrap();
        let mut from_prepared = WeightAccumulator::empty(10);
        from_prepared
            .add_grouped_64x16_binary_masks_deferred_prepared(&expected_groups, &expected_masks)
            .unwrap();

        let [WeightComponent::Grouped64x16BinaryDeferred {
            row_groups: mask_groups,
            group_masks: mask_values,
            first_alpha: mask_alpha,
            group_values: mask_folded,
        }] = from_masks.components.as_slice()
        else {
            panic!("mask wrapper must install one deferred component")
        };
        let [WeightComponent::Grouped64x16BinaryDeferred {
            row_groups: prepared_groups,
            group_masks: prepared_values,
            first_alpha: prepared_alpha,
            group_values: prepared_folded,
        }] = from_prepared.components.as_slice()
        else {
            panic!("prepared wrapper must install one deferred component")
        };

        assert_eq!(mask_groups, prepared_groups);
        assert_eq!(mask_values, prepared_values);
        assert_eq!(mask_alpha, prepared_alpha);
        assert_eq!(mask_folded, prepared_folded);
        assert_eq!(mask_groups, &expected_groups);
        assert_eq!(mask_values, &expected_masks);
        assert!(mask_alpha.is_none());
        assert!(mask_folded.is_empty());
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
