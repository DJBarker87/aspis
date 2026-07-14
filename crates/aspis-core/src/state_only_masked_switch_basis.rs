//! Frozen universal-MDS basis for the profile-21 masked switch.
//!
//! Logical coordinates are split into a 19-dimensional message complement
//! and a 16-dimensional encoding-randomness space inside `M31[x]_{<35}`:
//!
//! ```text
//! M = span{x, 1, x^18, ..., x^34}
//! R = (x^2 + 1) * M31[x]_{<16}.
//! ```
//!
//! Since `2^31 - 1 == 3 (mod 4)`, `x^2 + 1` has no M31 roots.  Evaluation
//! of R at any 16 distinct M31 points is therefore a non-singular diagonal
//! matrix times a Vandermonde matrix.  The generated matrix below converts
//! those logical ordinary-polynomial coordinates into the natural line
//! tensor basis used by the circle encoder.  It is generated at compile time
//! and bound by a pinned fingerprint; prover, rank gate, and verifier must all
//! use this one object.

use crate::field::{M31, P, QM31};

pub const MASKED_SWITCH_UNIVERSAL_DIMENSION: usize = 35;
pub const MASKED_SWITCH_UNIVERSAL_MESSAGE_DIMENSION: usize = 19;
pub const MASKED_SWITCH_UNIVERSAL_RANDOMNESS_DIMENSION: usize = 16;

const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

const fn add_raw(left: u32, right: u32) -> u32 {
    let sum = left + right;
    if sum >= P {
        sum - P
    } else {
        sum
    }
}

const fn sub_raw(left: u32, right: u32) -> u32 {
    let difference = left + P - right;
    if difference >= P {
        difference - P
    } else {
        difference
    }
}

const fn mul_raw(left: u32, right: u32) -> u32 {
    ((left as u64 * right as u64) % P as u64) as u32
}

const fn pow_raw(mut base: u32, mut exponent: u64) -> u32 {
    let mut result = 1u32;
    while exponent != 0 {
        if exponent & 1 == 1 {
            result = mul_raw(result, base);
        }
        base = mul_raw(base, base);
        exponent >>= 1;
    }
    result
}

const fn inverse_raw(value: u32) -> u32 {
    assert!(value != 0);
    pow_raw(value, P as u64 - 2)
}

const fn trailing_bit(mut value: usize) -> usize {
    let mut bit = 0usize;
    while value & 1 == 0 {
        value >>= 1;
        bit += 1;
    }
    bit
}

/// Ordinary-polynomial coefficients of the natural tensor basis
/// `B_i(x)=prod_{b in bits(i)} T_{2^b}(x)`.
const fn natural_basis_polynomials(
) -> [[u32; MASKED_SWITCH_UNIVERSAL_DIMENSION]; MASKED_SWITCH_UNIVERSAL_DIMENSION] {
    const N: usize = MASKED_SWITCH_UNIVERSAL_DIMENSION;
    // Six factors cover natural indices below 35.
    let mut factors = [[0u32; N]; 6];
    let mut factor_lengths = [0usize; 6];
    factors[0][1] = 1;
    factor_lengths[0] = 2;
    let mut bit = 1usize;
    while bit < 6 {
        let previous_length = factor_lengths[bit - 1];
        let mut left = 0usize;
        while left < previous_length {
            let mut right = 0usize;
            while right < previous_length {
                let degree = left + right;
                factors[bit][degree] = add_raw(
                    factors[bit][degree],
                    mul_raw(factors[bit - 1][left], factors[bit - 1][right]),
                );
                right += 1;
            }
            left += 1;
        }
        let length = 2 * previous_length - 1;
        let mut degree = 0usize;
        while degree < length {
            factors[bit][degree] = add_raw(factors[bit][degree], factors[bit][degree]);
            degree += 1;
        }
        factors[bit][0] = sub_raw(factors[bit][0], 1);
        factor_lengths[bit] = length;
        bit += 1;
    }

    let mut basis = [[0u32; N]; N];
    let mut basis_lengths = [0usize; N];
    basis[0][0] = 1;
    basis_lengths[0] = 1;
    let mut index = 1usize;
    while index < N {
        let bit = trailing_bit(index);
        let prefix = index ^ (1usize << bit);
        let mut left = 0usize;
        while left < basis_lengths[prefix] {
            let mut right = 0usize;
            while right < factor_lengths[bit] {
                let degree = left + right;
                if degree < N {
                    basis[index][degree] = add_raw(
                        basis[index][degree],
                        mul_raw(basis[prefix][left], factors[bit][right]),
                    );
                }
                right += 1;
            }
            left += 1;
        }
        basis_lengths[index] = basis_lengths[prefix] + factor_lengths[bit] - 1;
        index += 1;
    }
    basis
}

/// Natural-tensor coordinates of every ordinary monomial `x^degree`.
const fn ordinary_monomials_in_natural_basis(
) -> [[u32; MASKED_SWITCH_UNIVERSAL_DIMENSION]; MASKED_SWITCH_UNIVERSAL_DIMENSION] {
    const N: usize = MASKED_SWITCH_UNIVERSAL_DIMENSION;
    let natural = natural_basis_polynomials();
    let mut result = [[0u32; N]; N];
    let mut degree = 0usize;
    while degree < N {
        let mut residual = [0u32; N];
        residual[degree] = 1;
        let mut pivot = degree + 1;
        while pivot != 0 {
            pivot -= 1;
            let scale = mul_raw(residual[pivot], inverse_raw(natural[pivot][pivot]));
            result[degree][pivot] = scale;
            let mut monomial = 0usize;
            while monomial <= pivot {
                residual[monomial] =
                    sub_raw(residual[monomial], mul_raw(scale, natural[pivot][monomial]));
                monomial += 1;
            }
        }
        degree += 1;
    }
    result
}

const fn generate_code_basis(
) -> [[M31; MASKED_SWITCH_UNIVERSAL_DIMENSION]; MASKED_SWITCH_UNIVERSAL_DIMENSION] {
    const N: usize = MASKED_SWITCH_UNIVERSAL_DIMENSION;
    const M: usize = MASKED_SWITCH_UNIVERSAL_MESSAGE_DIMENSION;
    const R: usize = MASKED_SWITCH_UNIVERSAL_RANDOMNESS_DIMENSION;
    let monomials = ordinary_monomials_in_natural_basis();
    let mut result = [[M31::ZERO; N]; N];

    // Logical message order keeps the genuine slot-zero `x` direction first,
    // followed by the constant and the high-degree complement.
    let mut natural = 0usize;
    while natural < N {
        result[0][natural] = M31(monomials[1][natural]);
        result[1][natural] = M31(monomials[0][natural]);
        natural += 1;
    }
    let mut logical = 2usize;
    while logical < M {
        let degree = R + logical;
        natural = 0;
        while natural < N {
            result[logical][natural] = M31(monomials[degree][natural]);
            natural += 1;
        }
        logical += 1;
    }

    // R_j=(x^2+1)x^j, j=0..15.
    let mut randomness = 0usize;
    while randomness < R {
        natural = 0;
        while natural < N {
            result[M + randomness][natural] = M31(add_raw(
                monomials[randomness][natural],
                monomials[randomness + 2][natural],
            ));
            natural += 1;
        }
        randomness += 1;
    }
    result
}

pub const MASKED_SWITCH_UNIVERSAL_CODE_BASIS: [[M31; MASKED_SWITCH_UNIVERSAL_DIMENSION];
    MASKED_SWITCH_UNIVERSAL_DIMENSION] = generate_code_basis();

const fn invert_code_basis(
) -> [[M31; MASKED_SWITCH_UNIVERSAL_DIMENSION]; MASKED_SWITCH_UNIVERSAL_DIMENSION] {
    const N: usize = MASKED_SWITCH_UNIVERSAL_DIMENSION;
    // Rows are natural coordinates; columns are logical coordinates.
    let mut left = [[0u32; N]; N];
    let mut right = [[0u32; N]; N];
    let mut row = 0usize;
    while row < N {
        let mut column = 0usize;
        while column < N {
            left[row][column] = MASKED_SWITCH_UNIVERSAL_CODE_BASIS[column][row].0;
            column += 1;
        }
        right[row][row] = 1;
        row += 1;
    }

    let mut pivot = 0usize;
    while pivot < N {
        let mut selected = pivot;
        while selected < N && left[selected][pivot] == 0 {
            selected += 1;
        }
        assert!(selected < N);
        if selected != pivot {
            let temporary_left = left[pivot];
            left[pivot] = left[selected];
            left[selected] = temporary_left;
            let temporary_right = right[pivot];
            right[pivot] = right[selected];
            right[selected] = temporary_right;
        }
        let inverse = inverse_raw(left[pivot][pivot]);
        let mut column = 0usize;
        while column < N {
            left[pivot][column] = mul_raw(left[pivot][column], inverse);
            right[pivot][column] = mul_raw(right[pivot][column], inverse);
            column += 1;
        }
        row = 0;
        while row < N {
            if row != pivot {
                let scale = left[row][pivot];
                if scale != 0 {
                    column = 0;
                    while column < N {
                        left[row][column] =
                            sub_raw(left[row][column], mul_raw(scale, left[pivot][column]));
                        right[row][column] =
                            sub_raw(right[row][column], mul_raw(scale, right[pivot][column]));
                        column += 1;
                    }
                }
            }
            row += 1;
        }
        pivot += 1;
    }

    let mut result = [[M31::ZERO; N]; N];
    let mut logical = 0usize;
    while logical < N {
        let mut natural = 0usize;
        while natural < N {
            // A^-1 has logical rows and natural columns.
            result[logical][natural] = M31(right[logical][natural]);
            natural += 1;
        }
        logical += 1;
    }
    result
}

pub const MASKED_SWITCH_UNIVERSAL_NATURAL_TO_LOGICAL: [[M31; MASKED_SWITCH_UNIVERSAL_DIMENSION];
    MASKED_SWITCH_UNIVERSAL_DIMENSION] = invert_code_basis();

const fn fingerprint_byte(hash: u64, byte: u8) -> u64 {
    (hash ^ byte as u64).wrapping_mul(FNV_PRIME)
}

const fn generated_basis_fingerprint() -> u64 {
    let mut hash = FNV_OFFSET;
    let domain = b"aspis/profile21/universal-mds-basis/v1";
    let mut index = 0usize;
    while index < domain.len() {
        hash = fingerprint_byte(hash, domain[index]);
        index += 1;
    }
    let dimensions = [
        MASKED_SWITCH_UNIVERSAL_DIMENSION as u16,
        MASKED_SWITCH_UNIVERSAL_MESSAGE_DIMENSION as u16,
        MASKED_SWITCH_UNIVERSAL_RANDOMNESS_DIMENSION as u16,
    ];
    let mut dimension_index = 0usize;
    while dimension_index < dimensions.len() {
        let dimension = dimensions[dimension_index];
        let bytes = dimension.to_le_bytes();
        hash = fingerprint_byte(hash, bytes[0]);
        hash = fingerprint_byte(hash, bytes[1]);
        dimension_index += 1;
    }
    let mut column = 0usize;
    while column < MASKED_SWITCH_UNIVERSAL_DIMENSION {
        let mut row = 0usize;
        while row < MASKED_SWITCH_UNIVERSAL_DIMENSION {
            let bytes = MASKED_SWITCH_UNIVERSAL_CODE_BASIS[column][row]
                .0
                .to_le_bytes();
            let mut byte = 0usize;
            while byte < bytes.len() {
                hash = fingerprint_byte(hash, bytes[byte]);
                byte += 1;
            }
            row += 1;
        }
        column += 1;
    }
    hash
}

pub const MASKED_SWITCH_UNIVERSAL_CODE_BASIS_FINGERPRINT: u64 = generated_basis_fingerprint();
pub const PINNED_MASKED_SWITCH_UNIVERSAL_CODE_BASIS_FINGERPRINT: u64 = 0xceb3_5dd3_ee50_e051;

/// Matrix reference for the frozen logical-to-natural change of basis.
/// Production uses the multiplication-free Horner recurrence below; this
/// form remains an independent identity guard for every generated column.
#[doc(hidden)]
pub fn masked_switch_logical_to_natural_matrix_reference(
    logical: &[QM31; MASKED_SWITCH_UNIVERSAL_DIMENSION],
) -> [QM31; MASKED_SWITCH_UNIVERSAL_DIMENSION] {
    let mut natural = [QM31::ZERO; MASKED_SWITCH_UNIVERSAL_DIMENSION];
    // Index the static matrix by reference. Iterating the array by value made
    // LLVM materialize the complete 35x35 M31 table in the SBF frame, which
    // exceeds Solana's 4 KiB stack limit even though only one row is live.
    for logical_index in 0..MASKED_SWITCH_UNIVERSAL_DIMENSION {
        let logical_value = logical[logical_index];
        let column = &MASKED_SWITCH_UNIVERSAL_CODE_BASIS[logical_index];
        for (output, &scale) in natural.iter_mut().zip(column.iter()) {
            if scale != M31::ZERO {
                *output = output.add(logical_value.mul_m31(scale));
            }
        }
    }
    natural
}

/// Multiply a natural line-tensor coefficient prefix by the ordinary
/// variable `x`. If the low bit of index `i` is clear, `x B_i = B_{i|1}`.
/// For a run of `r` low one-bits, repeated use of
/// `T_a*T_a=(T_{2a}+1)/2` gives at most `r+1` outputs, all scaled only by
/// powers of two. Thus this exact basis conversion needs additions and
/// canonical halves but no M31 multiplications.
fn masked_switch_natural_mul_x(
    values: &[QM31; MASKED_SWITCH_UNIVERSAL_DIMENSION],
) -> [QM31; MASKED_SWITCH_UNIVERSAL_DIMENSION] {
    let mut output = [QM31::ZERO; MASKED_SWITCH_UNIVERSAL_DIMENSION];
    for (index, &value) in values.iter().enumerate() {
        if index & 1 == 0 {
            if index + 1 < MASKED_SWITCH_UNIVERSAL_DIMENSION {
                output[index + 1] = output[index + 1].add(value);
            }
            continue;
        }
        let run = index.trailing_ones() as usize;
        let mut scaled = value;
        let mut cleared = index;
        for bit in 0..run {
            scaled = scaled.half();
            cleared &= !(1usize << bit);
            output[cleared] = output[cleared].add(scaled);
        }
        let raised = cleared | (1usize << run);
        if raised < MASKED_SWITCH_UNIVERSAL_DIMENSION {
            output[raised] = output[raised].add(scaled);
        }
    }
    output
}

/// Apply the frozen logical-to-natural change of basis. The logical input is
/// `(message[19], randomness[16])`; the output is the exact 35-coordinate
/// natural line tensor vector committed by the PCS.
///
/// The logical polynomial is assembled in the ordinary monomial basis and
/// converted by Horner using [`masked_switch_natural_mul_x`]. This is exactly
/// the generated matrix but removes its 324 QM31-by-M31 products from the
/// SBF relation seam.
pub fn masked_switch_logical_to_natural(
    logical: &[QM31; MASKED_SWITCH_UNIVERSAL_DIMENSION],
) -> [QM31; MASKED_SWITCH_UNIVERSAL_DIMENSION] {
    let mut ordinary = [QM31::ZERO; MASKED_SWITCH_UNIVERSAL_DIMENSION];
    ordinary[1] = logical[0];
    ordinary[0] = logical[1];
    for logical_index in 2..MASKED_SWITCH_UNIVERSAL_MESSAGE_DIMENSION {
        ordinary[MASKED_SWITCH_UNIVERSAL_RANDOMNESS_DIMENSION + logical_index] = ordinary
            [MASKED_SWITCH_UNIVERSAL_RANDOMNESS_DIMENSION + logical_index]
            .add(logical[logical_index]);
    }
    for randomness in 0..MASKED_SWITCH_UNIVERSAL_RANDOMNESS_DIMENSION {
        let value = logical[MASKED_SWITCH_UNIVERSAL_MESSAGE_DIMENSION + randomness];
        ordinary[randomness] = ordinary[randomness].add(value);
        ordinary[randomness + 2] = ordinary[randomness + 2].add(value);
    }

    let mut natural = [QM31::ZERO; MASKED_SWITCH_UNIVERSAL_DIMENSION];
    for degree in (0..MASKED_SWITCH_UNIVERSAL_DIMENSION).rev() {
        natural = masked_switch_natural_mul_x(&natural);
        natural[0] = natural[0].add(ordinary[degree]);
    }
    natural
}

/// Inverse of [`masked_switch_logical_to_natural`]. This generated matrix is
/// used by the verifier to recover the logical message coordinates from the
/// disclosed natural U coefficients before checking the post-delta target
/// identity.
pub fn masked_switch_natural_to_logical(
    natural: &[QM31; MASKED_SWITCH_UNIVERSAL_DIMENSION],
) -> [QM31; MASKED_SWITCH_UNIVERSAL_DIMENSION] {
    core::array::from_fn(|logical| {
        natural
            .iter()
            .copied()
            .zip(MASKED_SWITCH_UNIVERSAL_NATURAL_TO_LOGICAL[logical])
            .filter(|(_, scale)| *scale != M31::ZERO)
            .fold(QM31::ZERO, |sum, (value, scale)| {
                sum.add(value.mul_m31(scale))
            })
    })
}

/// Evaluate the production old-view target on the disclosed natural U
/// coefficients. `message_covector` is the exact 19-coordinate covector
/// derived after round-zero OOD mixing and alpha folding. Randomness
/// coordinates are deliberately absent from this target.
pub fn masked_switch_natural_message_target(
    natural: &[QM31; MASKED_SWITCH_UNIVERSAL_DIMENSION],
    message_covector: &[QM31; MASKED_SWITCH_UNIVERSAL_MESSAGE_DIMENSION],
) -> QM31 {
    (0..MASKED_SWITCH_UNIVERSAL_MESSAGE_DIMENSION).fold(QM31::ZERO, |target, logical| {
        let value = natural
            .iter()
            .copied()
            .zip(MASKED_SWITCH_UNIVERSAL_NATURAL_TO_LOGICAL[logical])
            .filter(|(_, scale)| *scale != M31::ZERO)
            .fold(QM31::ZERO, |sum, (value, scale)| {
                sum.add(value.mul_m31(scale))
            });
        target.add(message_covector[logical].mul(value))
    })
}

/// Evaluate the old-view message target directly on the disclosed logical
/// profile-21 coordinates.  Production serialization uses logical `U`, so
/// the verifier need not apply the 19-by-35 inverse basis merely to check the
/// post-delta identity.  The natural-basis path remains an independent
/// differential reference.
pub fn masked_switch_logical_message_target(
    logical: &[QM31; MASKED_SWITCH_UNIVERSAL_DIMENSION],
    message_covector: &[QM31; MASKED_SWITCH_UNIVERSAL_MESSAGE_DIMENSION],
) -> QM31 {
    logical[..MASKED_SWITCH_UNIVERSAL_MESSAGE_DIMENSION]
        .iter()
        .copied()
        .zip(message_covector.iter().copied())
        .fold(QM31::ZERO, |target, (value, weight)| {
            target.add(weight.mul(value))
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::CM31;
    use crate::sumcheck::WeightAccumulator;

    fn q(seed: u32) -> QM31 {
        QM31 {
            c0: CM31::new(M31(seed), M31(seed + 1)),
            c1: CM31::new(M31(seed + 2), M31(seed + 3)),
        }
    }

    #[test]
    fn generated_basis_fingerprint_is_pinned() {
        // Update only through an explicit profile/version change.
        assert_eq!(
            MASKED_SWITCH_UNIVERSAL_CODE_BASIS_FINGERPRINT,
            PINNED_MASKED_SWITCH_UNIVERSAL_CODE_BASIS_FINGERPRINT,
        );
    }

    #[test]
    fn inverse_roundtrip_and_ordinary_polynomial_reference_are_exact() {
        let logical = core::array::from_fn(|index| q(101 + 7 * index as u32));
        let natural = masked_switch_logical_to_natural(&logical);
        assert_eq!(masked_switch_natural_to_logical(&natural), logical);

        for sample in 0..32u32 {
            let x = q(10_003 + 97 * sample);
            let mut ordinary = logical[0].mul(x).add(logical[1]);
            for logical_index in 2..MASKED_SWITCH_UNIVERSAL_MESSAGE_DIMENSION {
                ordinary = ordinary.add(logical[logical_index].mul(
                    x.pow((MASKED_SWITCH_UNIVERSAL_RANDOMNESS_DIMENSION + logical_index) as u64),
                ));
            }
            let x2_plus_one = x.square().add(QM31::ONE);
            for randomness in 0..MASKED_SWITCH_UNIVERSAL_RANDOMNESS_DIMENSION {
                ordinary = ordinary.add(
                    logical[MASKED_SWITCH_UNIVERSAL_MESSAGE_DIMENSION + randomness]
                        .mul(x2_plus_one)
                        .mul(x.pow(randomness as u64)),
                );
            }
            let mut weights = WeightAccumulator::empty(8);
            weights.add_line_tensor(QM31::ONE, x).unwrap();
            let mut padded = [QM31::ZERO; 256];
            padded[..MASKED_SWITCH_UNIVERSAL_DIMENSION].copy_from_slice(&natural);
            assert_eq!(weights.dot(&padded), ordinary, "sample={sample}");
        }
    }

    #[test]
    fn multiplication_free_horner_matches_every_generated_basis_column() {
        for logical_index in 0..MASKED_SWITCH_UNIVERSAL_DIMENSION {
            let mut logical = [QM31::ZERO; MASKED_SWITCH_UNIVERSAL_DIMENSION];
            logical[logical_index] = q(101 + 17 * logical_index as u32);
            assert_eq!(
                masked_switch_logical_to_natural(&logical),
                masked_switch_logical_to_natural_matrix_reference(&logical),
                "logical_index={logical_index}",
            );
        }
    }

    #[test]
    fn optimized_message_target_matches_full_inverse_reference() {
        let logical = core::array::from_fn(|index| q(20_003 + 11 * index as u32));
        let natural = masked_switch_logical_to_natural(&logical);
        let covector = core::array::from_fn(|index| q(30_011 + 13 * index as u32));
        let reference = logical[..MASKED_SWITCH_UNIVERSAL_MESSAGE_DIMENSION]
            .iter()
            .copied()
            .zip(covector)
            .fold(QM31::ZERO, |sum, (value, weight)| {
                sum.add(weight.mul(value))
            });
        assert_eq!(
            masked_switch_natural_message_target(&natural, &covector),
            reference,
        );
        assert_eq!(
            masked_switch_logical_message_target(&logical, &covector),
            reference,
        );
    }
}
