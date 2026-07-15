//! Production-neutral masking algebra for the 16-column state-only candidate.
//!
//! This module defines only the public factor schedule and exact terminal
//! evaluation.  It does not sample masks, alter the production transcript, or
//! claim Fiat--Shamir zero knowledge.  The host rank gate lives beside the
//! prover because it also needs the circle encoder and the statement crate's
//! final relation-free-cell inventory.

use crate::field::{CM31, M31, QM31};
use crate::transcript::{label, ChallengeSampleExhausted, Transcript};

pub const STATE_ONLY_HIDING_C1_COLUMNS: usize = 16;
pub const STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS: usize = 10;
/// Frozen production width until the selected hiding profile is integrated
/// across prefix/query/relation/terminal together.
pub const STATE_ONLY_HIDING_TOTAL_C1_COLUMNS: usize = STATE_ONLY_HIDING_C1_COLUMNS;
pub const STATE_ONLY_HIDING_C2_COLUMNS: usize = 2;
pub const STATE_ONLY_HIDING_TOTAL_GENERATOR_WIDTH: usize =
    STATE_ONLY_HIDING_TOTAL_C1_COLUMNS + STATE_ONLY_HIDING_C2_COLUMNS;
pub const STATE_ONLY_HIDING_SELECTED_TOTAL_C1_COLUMNS: usize =
    STATE_ONLY_HIDING_C1_COLUMNS + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS;
pub const STATE_ONLY_HIDING_SELECTED_TOTAL_GENERATOR_WIDTH: usize =
    STATE_ONLY_HIDING_SELECTED_TOTAL_C1_COLUMNS + STATE_ONLY_HIDING_C2_COLUMNS;
pub const STATE_ONLY_HIDING_SEMANTIC_C1_START: usize = 0;
pub const STATE_ONLY_HIDING_MASK_ONLY_C1_START: usize = STATE_ONLY_HIDING_C1_COLUMNS;
pub const STATE_ONLY_HIDING_H1_GENERATOR_INDEX: usize = STATE_ONLY_HIDING_SELECTED_TOTAL_C1_COLUMNS;
pub const STATE_ONLY_HIDING_G_GENERATOR_INDEX: usize = STATE_ONLY_HIDING_H1_GENERATOR_INDEX + 1;
pub const STATE_ONLY_HIDING_SUMCHECK_ROUNDS: usize = 10;
pub const STATE_ONLY_HIDING_FACTOR_DEGREE: usize = 26;
pub const STATE_ONLY_HIDING_MASKED_ORACLE_DEGREE: usize = 27;
pub const STATE_ONLY_HIDING_QUERY_COUNT: usize = 36;
pub const STATE_ONLY_HIDING_FIBER_SLOTS: usize = 4;
pub const STATE_ONLY_HIDING_TERMINAL_POINTS: usize = 3;
pub const STATE_ONLY_H1_PADDING_MASK_START: usize = 868;
pub const STATE_ONLY_H1_PADDING_MASK_END: usize = 1024;
pub const STATE_ONLY_COPY_ACTIVE_ROW_COUNT: usize = 170;
pub const STATE_ONLY_COPY_INACTIVE_ROW_COUNT: usize =
    STATE_ONLY_H1_PADDING_MASK_END - STATE_ONLY_COPY_ACTIVE_ROW_COUNT;
pub const STATE_ONLY_H1_PADDING_MASK_FREE_QM31: usize = STATE_ONLY_COPY_INACTIVE_ROW_COUNT - 1;
pub const PINNED_STATE_ONLY_COPY_ACTIVE_ROWS_FINGERPRINT: u64 = 0xdfba_37ae_14a1_a2cc;
pub const STATE_ONLY_HIDING_C1_RAW_M31_OBSERVATIONS: usize = STATE_ONLY_HIDING_QUERY_COUNT
    * STATE_ONLY_HIDING_FIBER_SLOTS
    + 4 * STATE_ONLY_HIDING_TERMINAL_POINTS;
pub const STATE_ONLY_HIDING_G_RAW_QM31_OBSERVATIONS: usize = STATE_ONLY_HIDING_QUERY_COUNT
    * STATE_ONLY_HIDING_FIBER_SLOTS
    + STATE_ONLY_HIDING_TERMINAL_POINTS;
/// One initial claim and 27 independent coefficients in each of ten rounds.
/// A complete degree-27 round has 28 coefficients, but its `c1` coefficient
/// is fixed by `p(0)+p(1)=claim` and contributes no additional view dimension.
pub const STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS: usize =
    1 + STATE_ONLY_HIDING_SUMCHECK_ROUNDS * STATE_ONLY_HIDING_FACTOR_DEGREE.saturating_add(1);
pub const STATE_ONLY_HIDING_SUMCHECK_M31_OBSERVATIONS: usize =
    4 * STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS;
/// Binds semantic mask layout `0x1420cb9210f52636` to this exact factor and
/// tower-basis schedule. Either side changing must deliberately repin the
/// complete-rank artifact.
pub const PINNED_STATE_ONLY_HIDING_LAYOUT_FACTOR_FINGERPRINT: u64 = 0xcd10_90cd_cb5f_3718;
pub const PINNED_STATE_ONLY_RELATION_FREE_MASK_FINGERPRINT: u64 = 0x1420_cb92_10f5_2636;
pub const PINNED_ATOMIC_STATE_ONLY_COPY_ACTIVE_ROWS_FINGERPRINT_V3: u64 = 0xfc90_f89b_e110_b6f5;
pub const PINNED_ATOMIC_STATE_ONLY_RELATION_FREE_MASK_FINGERPRINT_V3: u64 = 0x0fda_bd40_1816_cc99;
pub const PINNED_ATOMIC_STATE_ONLY_HIDING_LAYOUT_FACTOR_FINGERPRINT_V3: u64 = 0x9e4d_2fcd_4cf9_fe01;
/// Spend preserves the atomic-v3 semantic mask-cell registry but binds
/// the appended third C2 lane, its zero mask factor, and the three-candidate
/// post-nonce query selector into a distinct precommit context.
pub const PINNED_ATOMIC_STATE_ONLY_SPEND_LAYOUT_FACTOR_FINGERPRINT_V3: u64 = 0x233b_a2ca_68f9_4148;
pub const STATE_ONLY_SPEND_TOTAL_GENERATOR_WIDTH: usize = 29;
pub const STATE_ONLY_SPEND_C2_COLUMNS: usize = 3;
pub const STATE_ONLY_SPEND_H_GENERATOR_INDEX: usize = 26;
pub const STATE_ONLY_SPEND_G_GENERATOR_INDEX: usize = 27;
pub const STATE_ONLY_SPEND_D_GENERATOR_INDEX: usize = 28;
pub const STATE_ONLY_SPEND_D_FACTOR_IDENTIFIER: u8 = 0;
pub const STATE_ONLY_SPEND_QUERY_CANDIDATES: usize = 3;
pub const STATE_ONLY_HIDING_CONTEXT_VERSION: u8 = 1;
pub const STATE_ONLY_HIDING_CONTEXT_BYTES: usize = 1 + 32 + 32 + 8 + 8;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StateOnlyHidingContext {
    pub statement_digest: [u8; 32],
    /// Public, proof-instance-unique nonce. This is not mask entropy.
    pub mask_nonce: [u8; 32],
    pub mask_layout_fingerprint: u64,
    pub layout_factor_fingerprint: u64,
}

impl StateOnlyHidingContext {
    pub const fn pinned(statement_digest: [u8; 32], mask_nonce: [u8; 32]) -> Self {
        Self {
            statement_digest,
            mask_nonce,
            mask_layout_fingerprint: PINNED_STATE_ONLY_RELATION_FREE_MASK_FINGERPRINT,
            layout_factor_fingerprint: PINNED_STATE_ONLY_HIDING_LAYOUT_FACTOR_FINGERPRINT,
        }
    }

    pub const fn atomic_v3(statement_digest: [u8; 32], mask_nonce: [u8; 32]) -> Self {
        Self {
            statement_digest,
            mask_nonce,
            mask_layout_fingerprint: PINNED_ATOMIC_STATE_ONLY_RELATION_FREE_MASK_FINGERPRINT_V3,
            layout_factor_fingerprint: PINNED_ATOMIC_STATE_ONLY_HIDING_LAYOUT_FACTOR_FINGERPRINT_V3,
        }
    }

    /// Nondefault spend context.  The semantic masks and H oracle remain
    /// atomic-v3; only the committed zero-factor D tail and query-selection
    /// envelope are new.
    pub const fn atomic_spend_v3(statement_digest: [u8; 32], mask_nonce: [u8; 32]) -> Self {
        Self {
            statement_digest,
            mask_nonce,
            mask_layout_fingerprint: PINNED_ATOMIC_STATE_ONLY_RELATION_FREE_MASK_FINGERPRINT_V3,
            layout_factor_fingerprint: PINNED_ATOMIC_STATE_ONLY_SPEND_LAYOUT_FACTOR_FINGERPRINT_V3,
        }
    }

    pub fn encode(self) -> [u8; STATE_ONLY_HIDING_CONTEXT_BYTES] {
        let mut encoded = [0u8; STATE_ONLY_HIDING_CONTEXT_BYTES];
        encoded[0] = STATE_ONLY_HIDING_CONTEXT_VERSION;
        encoded[1..33].copy_from_slice(&self.statement_digest);
        encoded[33..65].copy_from_slice(&self.mask_nonce);
        encoded[65..73].copy_from_slice(&self.mask_layout_fingerprint.to_le_bytes());
        encoded[73..81].copy_from_slice(&self.layout_factor_fingerprint.to_le_bytes());
        encoded
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateOnlyHidingScheduleError {
    ZeroMaskNonce,
    MaskLayoutFingerprint,
    LayoutFactorFingerprint,
    ChallengeSampleExhausted,
}

impl From<ChallengeSampleExhausted> for StateOnlyHidingScheduleError {
    fn from(_: ChallengeSampleExhausted) -> Self {
        Self::ChallengeSampleExhausted
    }
}

/// Bind the public mask instance before any masked commitment is formed.
///
/// The returned state is a derivation salt for the host prover's *private*
/// entropy. It is not sufficient mask randomness by itself and may be public.
pub fn begin_state_only_hiding_precommit(
    transcript: &mut Transcript,
    context: StateOnlyHidingContext,
) -> Result<[u8; 32], StateOnlyHidingScheduleError> {
    if context.mask_nonce == [0u8; 32] {
        return Err(StateOnlyHidingScheduleError::ZeroMaskNonce);
    }
    let copy_active_rows_fingerprint =
        if context.mask_layout_fingerprint == PINNED_STATE_ONLY_RELATION_FREE_MASK_FINGERPRINT {
            PINNED_STATE_ONLY_COPY_ACTIVE_ROWS_FINGERPRINT
        } else if context.mask_layout_fingerprint
            == PINNED_ATOMIC_STATE_ONLY_RELATION_FREE_MASK_FINGERPRINT_V3
        {
            PINNED_ATOMIC_STATE_ONLY_COPY_ACTIVE_ROWS_FINGERPRINT_V3
        } else {
            return Err(StateOnlyHidingScheduleError::MaskLayoutFingerprint);
        };
    let ordinary_factor = state_only_hiding_layout_factor_fingerprint_for_registry(
        context.mask_layout_fingerprint,
        copy_active_rows_fingerprint,
        true,
    );
    let spend_factor = context.mask_layout_fingerprint
        == PINNED_ATOMIC_STATE_ONLY_RELATION_FREE_MASK_FINGERPRINT_V3
        && context.layout_factor_fingerprint
            == state_only_spend_hiding_layout_factor_fingerprint_v3();
    if (context.layout_factor_fingerprint != ordinary_factor && !spend_factor)
        || (context.mask_layout_fingerprint == PINNED_STATE_ONLY_RELATION_FREE_MASK_FINGERPRINT
            && context.layout_factor_fingerprint
                != PINNED_STATE_ONLY_HIDING_LAYOUT_FACTOR_FINGERPRINT)
        || (context.mask_layout_fingerprint
            == PINNED_ATOMIC_STATE_ONLY_RELATION_FREE_MASK_FINGERPRINT_V3
            && context.layout_factor_fingerprint
                != PINNED_ATOMIC_STATE_ONLY_HIDING_LAYOUT_FACTOR_FINGERPRINT_V3
            && !spend_factor)
    {
        return Err(StateOnlyHidingScheduleError::LayoutFactorFingerprint);
    }
    transcript.absorb(label::M31_STATE_ONLY_HIDING_PRECOMMIT, &context.encode());
    Ok(transcript.diagnostic_state())
}

/// Fingerprint the spend-only commitment/generator extension without
/// pretending that D participates in the H mask oracle.  The final byte is
/// the exact candidate count, so q3 and the retired q4 draft cannot collide.
pub fn state_only_spend_hiding_layout_factor_fingerprint_v3() -> u64 {
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    let mut absorb = |byte: u8| {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    };
    // Frozen consensus bytes: this domain separator keeps the release's
    // original working-name spelling because it feeds the pinned layout
    // factor fingerprint checked fail-closed by the verifying schedule; the
    // frozen release proof must keep verifying without a re-grind.
    for byte in b"aspis-state-only-profile23-zero-factor-d-v1" {
        absorb(*byte);
    }
    for value in [
        PINNED_ATOMIC_STATE_ONLY_RELATION_FREE_MASK_FINGERPRINT_V3,
        PINNED_ATOMIC_STATE_ONLY_COPY_ACTIVE_ROWS_FINGERPRINT_V3,
        PINNED_ATOMIC_STATE_ONLY_HIDING_LAYOUT_FACTOR_FINGERPRINT_V3,
    ] {
        for byte in value.to_le_bytes() {
            absorb(byte);
        }
    }
    for byte in [
        STATE_ONLY_SPEND_TOTAL_GENERATOR_WIDTH as u8,
        STATE_ONLY_SPEND_C2_COLUMNS as u8,
        STATE_ONLY_SPEND_H_GENERATOR_INDEX as u8,
        STATE_ONLY_SPEND_G_GENERATOR_INDEX as u8,
        STATE_ONLY_SPEND_D_GENERATOR_INDEX as u8,
        STATE_ONLY_SPEND_D_FACTOR_IDENTIFIER,
        STATE_ONLY_SPEND_QUERY_CANDIDATES as u8,
    ] {
        absorb(byte);
    }
    hash
}

/// Bind the initial mask claim after all masked roots and sample the nonzero
/// affine-combination challenge for `H + eta*F`.
pub fn begin_state_only_masked_sumcheck(
    transcript: &mut Transcript,
    initial_mask_claim: QM31,
) -> Result<QM31, StateOnlyHidingScheduleError> {
    let mut record = [0u8; 18];
    record[0] = STATE_ONLY_HIDING_MASKED_ORACLE_DEGREE as u8;
    record[1] = STATE_ONLY_HIDING_SUMCHECK_ROUNDS as u8;
    initial_mask_claim.write_le_bytes(&mut record[2..]);
    transcript.absorb(label::M31_STATE_ONLY_HIDING_MASK_CLAIM, &record);
    transcript
        .challenge_nonzero_qm31()
        .map_err(StateOnlyHidingScheduleError::from)
}

const FACTOR_FAMILIES: [u8; STATE_ONLY_HIDING_C1_COLUMNS] = [0; 16];
const FACTOR_EXPONENTS: [u8; STATE_ONLY_HIDING_C1_COLUMNS] =
    [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 13, 25];
const MASK_ONLY_FACTOR_EXPONENTS: [u8; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS] =
    [1, 3, 5, 7, 9, 11, 15, 17, 19, 21];
const EXPLICIT_FACTOR_EXPONENT: usize = STATE_ONLY_HIDING_FACTOR_DEGREE;
const EXPLICIT_FACTOR_FAMILY: usize = 16;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StateOnlyMaskFactors {
    pub c1: [QM31; STATE_ONLY_HIDING_C1_COLUMNS],
    pub mask_only_c1: [QM31; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
    pub explicit_g: QM31,
}

#[inline(always)]
fn cm31_mul_i(value: CM31) -> CM31 {
    CM31::new(value.b.neg(), value.a)
}

#[inline(always)]
fn cm31_mul_r(value: CM31) -> CM31 {
    CM31::new(value.a.double().sub(value.b), value.a.add(value.b.double()))
}

/// Multiply by one of `(1,i,u,iu)` without a generic QM31 product.
#[inline(always)]
fn mul_tower_basis(value: QM31, coordinate: usize) -> QM31 {
    match coordinate {
        0 => value,
        1 => QM31 {
            c0: cm31_mul_i(value.c0),
            c1: cm31_mul_i(value.c1),
        },
        2 => QM31 {
            c0: cm31_mul_r(value.c1),
            c1: value.c0,
        },
        3 => QM31 {
            c0: cm31_mul_i(cm31_mul_r(value.c1)),
            c1: cm31_mul_i(value.c0),
        },
        _ => panic!("state-only hiding tower coordinate out of range"),
    }
}

/// Cache the shared dense linear form's complete power table once. The exact
/// exponent/tower schedule is pinned by the complete-view rank gate: using
/// the same factor for explicit G drops four required M31 directions, so G
/// deliberately remains on its independent family below.
#[inline(never)]
fn state_only_shared_factor_powers(
    point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
) -> [QM31; STATE_ONLY_HIDING_FACTOR_DEGREE + 1] {
    let linear = mask_linear(0, point);
    let mut powers = [QM31::ONE; STATE_ONLY_HIDING_FACTOR_DEGREE + 1];
    powers[1] = linear;
    for exponent in 2..=STATE_ONLY_HIDING_FACTOR_DEGREE {
        powers[exponent] = powers[exponent - 1].mul(linear);
    }
    powers
}

fn mask_linear(family: usize, point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS]) -> QM31 {
    point
        .iter()
        .enumerate()
        .fold(QM31::ZERO, |sum, (variable, value)| {
            let scalar = 3 + 22 * variable + family * (17 + 8 * variable);
            sum.add(value.mul_m31(M31(scalar as u32)))
        })
}

fn mask_power(value: QM31, exponent: usize) -> QM31 {
    (0..exponent).fold(QM31::ONE, |power, _| power.mul(value))
}

fn explicit_mask_factor(point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS]) -> QM31 {
    QM31::ONE.add(mask_power(
        mask_linear(EXPLICIT_FACTOR_FAMILY, point),
        EXPLICIT_FACTOR_EXPONENT,
    ))
}

pub fn state_only_mask_tower_basis(coordinate: usize) -> QM31 {
    match coordinate {
        0 => QM31::ONE,
        1 => QM31 {
            c0: CM31::new(M31::ZERO, M31::ONE),
            c1: CM31::ZERO,
        },
        2 => QM31 {
            c0: CM31::ZERO,
            c1: CM31::ONE,
        },
        3 => QM31 {
            c0: CM31::ZERO,
            c1: CM31::new(M31::ZERO, M31::ONE),
        },
        _ => panic!("state-only hiding tower coordinate out of range"),
    }
}

/// Public degree-26-or-less factors for the state-only masking candidate.
///
/// The semantic and mask-only columns share one dense linear form and one
/// cached `L^0..L^26` table. Their disjoint even/odd exponent schedules expose
/// all 1080 terminal-quotient directions in the q29 rank gate. The explicit
/// QM31 mask deliberately keeps an independent `1 + L_16^26` factor; sharing
/// it drops the rank to 1076.
pub fn state_only_mask_factors(
    point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
) -> StateOnlyMaskFactors {
    let powers = state_only_shared_factor_powers(point);
    let c1 = core::array::from_fn(|column| {
        let exponent = usize::from(FACTOR_EXPONENTS[column]);
        mul_tower_basis(powers[exponent], column & 3)
    });
    StateOnlyMaskFactors {
        c1,
        mask_only_c1: core::array::from_fn(|column| {
            mul_tower_basis(
                powers[usize::from(MASK_ONLY_FACTOR_EXPONENTS[column])],
                column & 3,
            )
        }),
        explicit_g: QM31::ONE
            .add(mask_linear(EXPLICIT_FACTOR_FAMILY, point).pow(EXPLICIT_FACTOR_EXPONENT as u64)),
    }
}

pub fn state_only_c1_mask_factor(
    column: usize,
    point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
) -> QM31 {
    assert!(column < STATE_ONLY_HIDING_C1_COLUMNS);
    let family = usize::from(FACTOR_FAMILIES[column]);
    let exponent = usize::from(FACTOR_EXPONENTS[column]);
    state_only_mask_tower_basis(column & 3).mul(mask_power(mask_linear(family, point), exponent))
}

pub fn state_only_explicit_g_mask_factor(
    point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
) -> QM31 {
    explicit_mask_factor(point)
}

/// Degree-at-most-26 factors for the ten selected full-domain M31 mask-only
/// columns. They use the rank-pinned unused odd powers of the same dense
/// linear form as the semantic columns, with distinct tower rotations.
pub fn state_only_mask_only_c1_factor(
    mask_column: usize,
    point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
) -> QM31 {
    assert!(mask_column < STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS);
    let exponent = usize::from(MASK_ONLY_FACTOR_EXPONENTS[mask_column]);
    mul_tower_basis(mask_power(mask_linear(0, point), exponent), mask_column & 3)
}

/// Evaluate the exact degree-at-most-27 mask polynomial terminal from the 16
/// already PCS-bound base-column evaluations and one explicit QM31 mask.
pub fn state_only_mask_value_with_factors(
    c1: &[QM31; STATE_ONLY_HIDING_C1_COLUMNS],
    explicit_g: QM31,
    factors: &StateOnlyMaskFactors,
) -> QM31 {
    c1.iter()
        .copied()
        .zip(factors.c1)
        .fold(QM31::ZERO, |sum, (value, factor)| {
            sum.add(factor.mul(value))
        })
        .add(factors.explicit_g.mul(explicit_g))
}

pub fn state_only_mask_value(
    c1: &[QM31; STATE_ONLY_HIDING_C1_COLUMNS],
    explicit_g: QM31,
    point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
) -> QM31 {
    state_only_mask_value_with_factors(c1, explicit_g, &state_only_mask_factors(point))
}

pub fn state_only_selected_mask_value_with_factors(
    c1: &[QM31; STATE_ONLY_HIDING_C1_COLUMNS],
    mask_only_c1: &[QM31; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
    explicit_g: QM31,
    factors: &StateOnlyMaskFactors,
) -> QM31 {
    mask_only_c1.iter().copied().zip(factors.mask_only_c1).fold(
        state_only_mask_value_with_factors(c1, explicit_g, factors),
        |sum, (value, factor)| sum.add(factor.mul(value)),
    )
}

pub fn state_only_selected_mask_value(
    c1: &[QM31; STATE_ONLY_HIDING_C1_COLUMNS],
    mask_only_c1: &[QM31; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
    explicit_g: QM31,
    point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
) -> QM31 {
    state_only_selected_mask_value_with_factors(
        c1,
        mask_only_c1,
        explicit_g,
        &state_only_mask_factors(point),
    )
}

/// Bind the final semantic mask-cell inventory and every algebraic factor
/// choice.  The statement crate owns `mask_layout_fingerprint`; changing the
/// layout, tower order, family, exponent, explicit-mask identifier, or degree
/// produces a distinct profile fingerprint.
pub fn state_only_hiding_layout_factor_fingerprint(mask_layout_fingerprint: u64) -> u64 {
    state_only_hiding_layout_factor_fingerprint_for_registry(
        mask_layout_fingerprint,
        PINNED_STATE_ONLY_COPY_ACTIVE_ROWS_FINGERPRINT,
        true,
    )
}

/// Bind one concrete relation-free mask layout to its copy-active registry
/// while retaining the frozen width-28 factor schedule.  Alternate statement
/// profiles must pin the output before using it in a transcript context.
pub fn state_only_hiding_layout_factor_fingerprint_for_registry(
    mask_layout_fingerprint: u64,
    copy_active_rows_fingerprint: u64,
    has_copy_inactive_zero_claim: bool,
) -> u64 {
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    let mut absorb = |byte: u8| {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    };
    for byte in b"aspis-state-only-hiding-v2-shared-powers" {
        absorb(*byte);
    }
    for byte in mask_layout_fingerprint.to_le_bytes() {
        absorb(byte);
    }
    for byte in b"copy-inactive-dense-zero-claim-v1" {
        absorb(*byte);
    }
    for byte in copy_active_rows_fingerprint.to_le_bytes() {
        absorb(byte);
    }
    absorb(u8::from(has_copy_inactive_zero_claim));
    for value in [
        STATE_ONLY_HIDING_C1_COLUMNS as u16,
        STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS as u16,
        STATE_ONLY_HIDING_SELECTED_TOTAL_GENERATOR_WIDTH as u16,
        STATE_ONLY_HIDING_SUMCHECK_ROUNDS as u16,
        STATE_ONLY_HIDING_FACTOR_DEGREE as u16,
        STATE_ONLY_HIDING_QUERY_COUNT as u16,
        STATE_ONLY_HIDING_FIBER_SLOTS as u16,
        STATE_ONLY_HIDING_TERMINAL_POINTS as u16,
    ] {
        for byte in value.to_le_bytes() {
            absorb(byte);
        }
    }
    for column in 0..STATE_ONLY_HIDING_C1_COLUMNS {
        absorb(column as u8);
        absorb((column & 3) as u8);
        absorb(FACTOR_FAMILIES[column]);
        absorb(FACTOR_EXPONENTS[column]);
    }
    for column in 0..STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS {
        absorb(0xfe); // Full-domain shared-power mask-only C1 namespace.
        absorb(column as u8);
        absorb(MASK_ONLY_FACTOR_EXPONENTS[column]);
        absorb((column & 3) as u8);
    }
    absorb(0xff); // Explicit G is not one of the sixteen C1 columns.
    absorb(0x45); // Even-coefficient-interval schedule marker.
    absorb(EXPLICIT_FACTOR_EXPONENT as u8);
    absorb(EXPLICIT_FACTOR_FAMILY as u8);
    hash
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::P;
    use sha2::{Digest, Sha256};

    fn host_hash(inputs: &[&[u8]]) -> [u8; 32] {
        let mut hash = Sha256::new();
        for input in inputs {
            hash.update(input);
        }
        hash.finalize().into()
    }

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
            M31((self.next() % u64::from(P)) as u32)
        }

        fn qm31(&mut self) -> QM31 {
            QM31 {
                c0: CM31::new(self.m31(), self.m31()),
                c1: CM31::new(self.m31(), self.m31()),
            }
        }
    }

    fn reference_factor(column: usize, point: &[QM31; 10]) -> QM31 {
        let family = usize::from(FACTOR_FAMILIES[column]);
        let exponent = usize::from(FACTOR_EXPONENTS[column]);
        state_only_mask_tower_basis(column & 3)
            .mul(mask_power(mask_linear(family, point), exponent))
    }

    fn finite_difference(mut values: alloc::vec::Vec<QM31>, order: usize) -> QM31 {
        for _ in 0..order {
            values = values.windows(2).map(|pair| pair[1].sub(pair[0])).collect();
        }
        assert_eq!(values.len(), 1);
        values[0]
    }

    #[test]
    fn factors_and_terminal_match_an_independent_column_walk() {
        let mut rng = Rng(0x5354_4f4e_4c59_5a4b);
        for point_index in 0..50 {
            let point = core::array::from_fn(|_| loop {
                let value = rng.qm31();
                if value != QM31::ZERO && value != QM31::ONE {
                    break value;
                }
            });
            let factors = state_only_mask_factors(&point);
            let c1 = core::array::from_fn(|_| rng.qm31());
            let mask_only_c1 = core::array::from_fn(|_| rng.qm31());
            let explicit_g = rng.qm31();
            let mut expected = QM31::ZERO;
            for column in 0..STATE_ONLY_HIDING_C1_COLUMNS {
                let factor = reference_factor(column, &point);
                assert_eq!(
                    factors.c1[column], factor,
                    "point={point_index}, column={column}"
                );
                expected = expected.add(factor.mul(c1[column]));
            }
            for column in 0..STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS {
                let factor = state_only_mask_only_c1_factor(column, &point);
                assert_eq!(
                    factors.mask_only_c1[column], factor,
                    "point={point_index}, mask-only column={column}"
                );
                expected = expected.add(factor.mul(mask_only_c1[column]));
            }
            let explicit_factor = QM31::ONE.add(mask_power(
                mask_linear(EXPLICIT_FACTOR_FAMILY, &point),
                EXPLICIT_FACTOR_EXPONENT,
            ));
            assert_eq!(factors.explicit_g, explicit_factor);
            expected = expected.add(explicit_factor.mul(explicit_g));
            assert_eq!(
                state_only_selected_mask_value(&c1, &mask_only_c1, explicit_g, &point),
                expected,
                "point={point_index}"
            );
        }
    }

    #[test]
    fn factor_degree_is_26_and_masked_oracle_degree_is_27() {
        let scalar = |value: usize| QM31::from_cm31(CM31::from_m31(M31(value as u32)));
        let factor_values = (0..=27)
            .map(|value| {
                let mut point = [QM31::ZERO; STATE_ONLY_HIDING_SUMCHECK_ROUNDS];
                point[0] = scalar(value);
                state_only_explicit_g_mask_factor(&point)
            })
            .collect();
        assert_eq!(finite_difference(factor_values, 27), QM31::ZERO);
        for mask_column in 0..STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS {
            let values = (0..=27)
                .map(|value| {
                    let mut point = [QM31::ZERO; STATE_ONLY_HIDING_SUMCHECK_ROUNDS];
                    point[mask_column % STATE_ONLY_HIDING_SUMCHECK_ROUNDS] = scalar(value);
                    state_only_mask_only_c1_factor(mask_column, &point)
                })
                .collect();
            assert_eq!(finite_difference(values, 27), QM31::ZERO);
        }

        let masked_values = (0..=28)
            .map(|value| {
                let mut point = [QM31::ZERO; STATE_ONLY_HIDING_SUMCHECK_ROUNDS];
                point[0] = scalar(value);
                scalar(value + 1).mul(state_only_explicit_g_mask_factor(&point))
            })
            .collect::<alloc::vec::Vec<_>>();
        assert_ne!(
            finite_difference(masked_values[..28].to_vec(), 27),
            QM31::ZERO
        );
        assert_eq!(finite_difference(masked_values, 28), QM31::ZERO);
    }

    #[test]
    fn fingerprint_has_layout_factor_and_basis_teeth() {
        let base = state_only_hiding_layout_factor_fingerprint(0x0123_4567_89ab_cdef);
        assert_ne!(
            base,
            state_only_hiding_layout_factor_fingerprint(0x0123_4567_89ab_cdee)
        );

        // Independently reproduce a one-byte factor mutation at the end of
        // the canonical stream. This is a negative/reuse guard: constants
        // compiled for one layout/factor profile cannot be silently reused.
        let other_layout = state_only_hiding_layout_factor_fingerprint(0xfedc_ba98_7654_3210);
        assert_ne!(base, other_layout);
        assert_ne!(
            base,
            state_only_hiding_layout_factor_fingerprint_for_registry(
                0x0123_4567_89ab_cdef,
                PINNED_STATE_ONLY_COPY_ACTIVE_ROWS_FINGERPRINT,
                false,
            )
        );
        assert_ne!(
            base,
            state_only_hiding_layout_factor_fingerprint_for_registry(
                0x0123_4567_89ab_cdef,
                PINNED_STATE_ONLY_COPY_ACTIVE_ROWS_FINGERPRINT ^ 1,
                true,
            )
        );
        assert_eq!(
            PINNED_STATE_ONLY_HIDING_LAYOUT_FACTOR_FINGERPRINT,
            state_only_hiding_layout_factor_fingerprint(
                PINNED_STATE_ONLY_RELATION_FREE_MASK_FINGERPRINT
            )
        );
        assert_eq!(STATE_ONLY_HIDING_C1_RAW_M31_OBSERVATIONS, 156);
        assert_eq!(STATE_ONLY_HIDING_G_RAW_QM31_OBSERVATIONS, 147);
        assert_eq!(STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS, 271);
        assert_eq!(STATE_ONLY_HIDING_SUMCHECK_M31_OBSERVATIONS, 1_084);
        assert_eq!(STATE_ONLY_HIDING_TOTAL_C1_COLUMNS, 16);
        assert_eq!(STATE_ONLY_HIDING_TOTAL_GENERATOR_WIDTH, 18);
        assert_eq!(STATE_ONLY_HIDING_SELECTED_TOTAL_C1_COLUMNS, 26);
        assert_eq!(STATE_ONLY_HIDING_SELECTED_TOTAL_GENERATOR_WIDTH, 28);
        assert_eq!(STATE_ONLY_HIDING_SEMANTIC_C1_START, 0);
        assert_eq!(STATE_ONLY_HIDING_MASK_ONLY_C1_START, 16);
        assert_eq!(STATE_ONLY_HIDING_H1_GENERATOR_INDEX, 26);
        assert_eq!(STATE_ONLY_HIDING_G_GENERATOR_INDEX, 27);
        assert_eq!(STATE_ONLY_COPY_ACTIVE_ROW_COUNT, 170);
        assert_eq!(STATE_ONLY_COPY_INACTIVE_ROW_COUNT, 854);
        assert_eq!(STATE_ONLY_H1_PADDING_MASK_FREE_QM31, 853);
    }

    #[test]
    fn spend_zero_factor_fingerprint_is_hard_pinned() {
        assert_eq!(
            state_only_spend_hiding_layout_factor_fingerprint_v3(),
            PINNED_ATOMIC_STATE_ONLY_SPEND_LAYOUT_FACTOR_FINGERPRINT_V3,
        );
        let context = StateOnlyHidingContext::atomic_spend_v3([0x23; 32], [0x42; 32]);
        let mut transcript = Transcript::new(host_hash);
        assert!(begin_state_only_hiding_precommit(&mut transcript, context).is_ok());
    }

    #[test]
    fn hiding_context_precedes_roots_and_rejects_stale_or_zero_instances() {
        let context = StateOnlyHidingContext::pinned([0x51; 32], [0xa7; 32]);
        let mut canonical = Transcript::new(host_hash);
        let precommit = begin_state_only_hiding_precommit(&mut canonical, context).unwrap();
        assert_eq!(precommit, canonical.diagnostic_state());
        canonical.absorb(label::M31_CIRCLE_ROUND_ROOT, &[0x11; 33]);
        canonical.absorb(label::M31_CIRCLE_C2_ROOT, &[0x22; 32]);
        let eta = begin_state_only_masked_sumcheck(&mut canonical, QM31::ONE).unwrap();
        assert_ne!(eta, QM31::ZERO);

        let mut roots_first = Transcript::new(host_hash);
        roots_first.absorb(label::M31_CIRCLE_ROUND_ROOT, &[0x11; 33]);
        roots_first.absorb(label::M31_CIRCLE_C2_ROOT, &[0x22; 32]);
        begin_state_only_hiding_precommit(&mut roots_first, context).unwrap();
        let early_eta = begin_state_only_masked_sumcheck(&mut roots_first, QM31::ONE).unwrap();
        assert_ne!(canonical.diagnostic_state(), roots_first.diagnostic_state());
        assert_ne!(eta, early_eta);

        let mut zero = Transcript::new(host_hash);
        assert_eq!(
            begin_state_only_hiding_precommit(
                &mut zero,
                StateOnlyHidingContext::pinned([0x51; 32], [0; 32])
            ),
            Err(StateOnlyHidingScheduleError::ZeroMaskNonce)
        );
        let mut stale = Transcript::new(host_hash);
        let mut stale_context = context;
        stale_context.mask_layout_fingerprint ^= 1;
        assert_eq!(
            begin_state_only_hiding_precommit(&mut stale, stale_context),
            Err(StateOnlyHidingScheduleError::MaskLayoutFingerprint)
        );
        let mut wrong_factor = Transcript::new(host_hash);
        let mut wrong_context = context;
        wrong_context.layout_factor_fingerprint ^= 1;
        assert_eq!(
            begin_state_only_hiding_precommit(&mut wrong_factor, wrong_context),
            Err(StateOnlyHidingScheduleError::LayoutFactorFingerprint)
        );
    }
}
