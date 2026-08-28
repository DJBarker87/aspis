//! Production-neutral masking algebra for the 16-column state-only candidate.
//!
//! This module defines only the public factor schedule and exact terminal
//! evaluation.  It does not sample masks, alter the production transcript, or
//! claim Fiat--Shamir zero knowledge.  The host rank gate lives beside the
//! prover because it also needs the circle encoder and the statement crate's
//! final relation-free-cell inventory.

use crate::field::{PreparedQm31Multiplier, CM31, M31, QM31};
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
pub const PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT: u64 = 0xfceb_68f3_197c_3351;
pub const PINNED_POOL_V1_PRIVATE_TRANSFER_COPY_ACTIVE_ROWS_FINGERPRINT: u64 = 0xe858_c4c0_d4e2_2b94;
pub const PINNED_POOL_V1_WITHDRAWAL_COPY_ACTIVE_ROWS_FINGERPRINT: u64 = 0xe9de_6f8f_ae7f_1793;
pub const PINNED_POOL_V1_PRIVATE_TRANSFER_ORDINARY_HG_LAYOUT_FACTOR_FINGERPRINT: u64 =
    0x2b36_45e9_342e_ad8d;
pub const PINNED_POOL_V1_WITHDRAWAL_ORDINARY_HG_LAYOUT_FACTOR_FINGERPRINT: u64 =
    0xc1ac_0561_7df0_0b70;
pub const PINNED_POOL_V1_PRIVATE_TRANSFER_HIDING_LAYOUT_FACTOR_FINGERPRINT: u64 =
    0x2945_d091_b802_310b;
pub const PINNED_POOL_V1_WITHDRAWAL_HIDING_LAYOUT_FACTOR_FINGERPRINT: u64 = 0x1805_e618_9f33_8346;
pub const PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1: u64 = 0xf9da_f3d5_4f42_85d1;
pub const PINNED_POOL_V1_PAIR_FOREST_COPY_ACTIVE_ROWS_FINGERPRINT_V1: u64 = 0xdf39_4a5a_8554_d09c;
pub const PINNED_POOL_V1_PAIR_FOREST_ORDINARY_HG_LAYOUT_FACTOR_FINGERPRINT_V1: u64 =
    0x74d8_a1f8_9edd_5006;
pub const PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1: u64 =
    0x698b_cded_ff44_a4db;
pub const POOL_V1_TAG73_TOTAL_GENERATOR_WIDTH: usize = 29;
pub const POOL_V1_TAG73_C2_COLUMNS: usize = 3;
pub const POOL_V1_TAG73_H_GENERATOR_INDEX: usize = 26;
pub const POOL_V1_TAG73_G_GENERATOR_INDEX: usize = 27;
pub const POOL_V1_TAG73_D_GENERATOR_INDEX: usize = 28;
pub const POOL_V1_TAG73_D_FACTOR_IDENTIFIER: u8 = 0;
pub const POOL_V1_TAG73_QUERY_COUNT: usize = 16;
pub const POOL_V1_TAG73_FIRST_QUERY_CAP: usize = 203;
/// Spend preserves the atomic-v3 semantic mask-cell registry but binds
/// the appended third C2 lane, its zero mask factor, and the three-candidate
/// post-nonce query selector into a distinct precommit context.
pub const PINNED_ATOMIC_STATE_ONLY_SPEND_LAYOUT_FACTOR_FINGERPRINT_V3: u64 = 0x10fe_8a50_2c4c_dd02;
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

    pub const fn pool_v1_private_transfer(
        statement_digest: [u8; 32],
        mask_nonce: [u8; 32],
    ) -> Self {
        Self {
            statement_digest,
            mask_nonce,
            mask_layout_fingerprint: PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT,
            layout_factor_fingerprint:
                PINNED_POOL_V1_PRIVATE_TRANSFER_HIDING_LAYOUT_FACTOR_FINGERPRINT,
        }
    }

    pub const fn pool_v1_withdrawal(statement_digest: [u8; 32], mask_nonce: [u8; 32]) -> Self {
        Self {
            statement_digest,
            mask_nonce,
            mask_layout_fingerprint: PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT,
            layout_factor_fingerprint: PINNED_POOL_V1_WITHDRAWAL_HIDING_LAYOUT_FACTOR_FINGERPRINT,
        }
    }

    /// Inactive eight-lane pair-forest profile. Transfer and withdrawal use
    /// the same merged-C1 mask/copy registry; the statement digest binds the
    /// payment variant and exact public statement separately.
    pub const fn pool_v1_pair_forest_v1(statement_digest: [u8; 32], mask_nonce: [u8; 32]) -> Self {
        Self {
            statement_digest,
            mask_nonce,
            mask_layout_fingerprint: PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1,
            layout_factor_fingerprint:
                PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1,
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
        } else if context.mask_layout_fingerprint
            == PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT
        {
            if context.layout_factor_fingerprint
                == PINNED_POOL_V1_PRIVATE_TRANSFER_HIDING_LAYOUT_FACTOR_FINGERPRINT
            {
                PINNED_POOL_V1_PRIVATE_TRANSFER_COPY_ACTIVE_ROWS_FINGERPRINT
            } else if context.layout_factor_fingerprint
                == PINNED_POOL_V1_WITHDRAWAL_HIDING_LAYOUT_FACTOR_FINGERPRINT
            {
                PINNED_POOL_V1_WITHDRAWAL_COPY_ACTIVE_ROWS_FINGERPRINT
            } else {
                return Err(StateOnlyHidingScheduleError::LayoutFactorFingerprint);
            }
        } else if context.mask_layout_fingerprint
            == PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1
        {
            if context.layout_factor_fingerprint
                != PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1
            {
                return Err(StateOnlyHidingScheduleError::LayoutFactorFingerprint);
            }
            PINNED_POOL_V1_PAIR_FOREST_COPY_ACTIVE_ROWS_FINGERPRINT_V1
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
    let pool_factor = (context.mask_layout_fingerprint
        == PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT
        || context.mask_layout_fingerprint
            == PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1)
        && context.layout_factor_fingerprint
            == state_only_pool_v1_tag73_hiding_layout_factor_fingerprint(
                context.mask_layout_fingerprint,
                copy_active_rows_fingerprint,
            );
    if (context.layout_factor_fingerprint != ordinary_factor && !spend_factor && !pool_factor)
        || (context.mask_layout_fingerprint == PINNED_STATE_ONLY_RELATION_FREE_MASK_FINGERPRINT
            && context.layout_factor_fingerprint
                != PINNED_STATE_ONLY_HIDING_LAYOUT_FACTOR_FINGERPRINT)
        || (context.mask_layout_fingerprint
            == PINNED_ATOMIC_STATE_ONLY_RELATION_FREE_MASK_FINGERPRINT_V3
            && context.layout_factor_fingerprint
                != PINNED_ATOMIC_STATE_ONLY_HIDING_LAYOUT_FACTOR_FINGERPRINT_V3
            && !spend_factor)
        || (context.mask_layout_fingerprint
            == PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT
            && context.layout_factor_fingerprint
                != PINNED_POOL_V1_PRIVATE_TRANSFER_HIDING_LAYOUT_FACTOR_FINGERPRINT
            && context.layout_factor_fingerprint
                != PINNED_POOL_V1_WITHDRAWAL_HIDING_LAYOUT_FACTOR_FINGERPRINT)
        || (context.mask_layout_fingerprint
            == PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1
            && context.layout_factor_fingerprint
                != PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1)
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
    // Frozen consensus bytes: this domain separator feeds the pinned layout
    // factor fingerprint checked fail-closed by the verifying schedule. The
    // aspis-spend release proofs are ground against exactly these bytes.
    for byte in b"aspis-state-only-spend-zero-factor-d-v1" {
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

/// Bind the complete Pool Tag-73 committed generator/query profile. D is a
/// zero-factor C2 lane outside the H oracle, but its commitment position and
/// q16/first-cap203 query envelope are public precommit inputs.
pub fn state_only_pool_v1_tag73_hiding_layout_factor_fingerprint(
    mask_layout_fingerprint: u64,
    copy_active_rows_fingerprint: u64,
) -> u64 {
    let ordinary = state_only_hiding_layout_factor_fingerprint_for_registry(
        mask_layout_fingerprint,
        copy_active_rows_fingerprint,
        true,
    );
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    let mut absorb = |byte: u8| {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    };
    for byte in b"aspis-state-only-pool-v1-tag73-zero-factor-d-v1" {
        absorb(*byte);
    }
    for value in [
        mask_layout_fingerprint,
        copy_active_rows_fingerprint,
        ordinary,
    ] {
        for byte in value.to_le_bytes() {
            absorb(byte);
        }
    }
    for byte in b"tag73-q16-first-cap203-v1" {
        absorb(*byte);
    }
    for byte in [
        POOL_V1_TAG73_TOTAL_GENERATOR_WIDTH as u8,
        POOL_V1_TAG73_C2_COLUMNS as u8,
        POOL_V1_TAG73_H_GENERATOR_INDEX as u8,
        POOL_V1_TAG73_G_GENERATOR_INDEX as u8,
        POOL_V1_TAG73_D_GENERATOR_INDEX as u8,
        POOL_V1_TAG73_D_FACTOR_IDENTIFIER,
        POOL_V1_TAG73_QUERY_COUNT as u8,
    ] {
        absorb(byte);
    }
    for byte in (POOL_V1_TAG73_FIRST_QUERY_CAP as u16).to_le_bytes() {
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

// The selected terminal can be evaluated as one dense degree-26 polynomial
// in the shared linear form only because these two frozen schedules form a
// duplicate-free cover of every exponent except 23. Keep that fact at the
// compiler boundary: a schedule change must fail here rather than silently
// changing the selected evaluator's algebra.
const _: () = {
    let mut seen = [false; STATE_ONLY_HIDING_FACTOR_DEGREE + 1];
    let mut column = 0;
    while column < STATE_ONLY_HIDING_C1_COLUMNS {
        let exponent = FACTOR_EXPONENTS[column] as usize;
        assert!(exponent <= STATE_ONLY_HIDING_FACTOR_DEGREE);
        assert!(!seen[exponent]);
        seen[exponent] = true;
        column += 1;
    }
    column = 0;
    while column < STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS {
        let exponent = MASK_ONLY_FACTOR_EXPONENTS[column] as usize;
        assert!(exponent <= STATE_ONLY_HIDING_FACTOR_DEGREE);
        assert!(!seen[exponent]);
        seen[exponent] = true;
        column += 1;
    }
    let mut exponent = 0;
    while exponent <= STATE_ONLY_HIDING_FACTOR_DEGREE {
        assert!(seen[exponent] == (exponent != 23));
        exponent += 1;
    }
};

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

/// Evaluate the two linear forms used by the selected terminal from the same
/// add-only sufficient statistics. With `S0 = sum z_i` and
/// `S1 = sum i*z_i`, the frozen forms are exactly
/// `L0 = 3*S0 + 22*S1` and `L16 = 275*S0 + 150*S1`.
#[inline(always)]
fn selected_mask_linears(point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS]) -> (QM31, QM31) {
    let mut suffix = QM31::ZERO;
    let mut weighted = QM31::ZERO;
    for variable in (0..STATE_ONLY_HIDING_SUMCHECK_ROUNDS).rev() {
        suffix = suffix.add(point[variable]);
        if variable != 0 {
            weighted = weighted.add(suffix);
        }
    }
    (
        suffix.mul_m31(M31(3)).add(weighted.mul_m31(M31(22))),
        suffix.mul_m31(M31(275)).add(weighted.mul_m31(M31(150))),
    )
}

fn mask_power(value: QM31, exponent: usize) -> QM31 {
    (0..exponent).fold(QM31::ONE, |power, _| power.mul(value))
}

/// Exact fixed addition chain for the explicit degree-26 factor.
#[inline(always)]
fn mask_power_26(value: QM31) -> QM31 {
    let x2 = value.square();
    let x4 = x2.square();
    let x8 = x4.square();
    let x16 = x8.square();
    x16.mul(x8).mul(x2)
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

#[inline(never)]
pub fn state_only_selected_mask_value(
    c1: &[QM31; STATE_ONLY_HIDING_C1_COLUMNS],
    mask_only_c1: &[QM31; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
    explicit_g: QM31,
    point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
) -> QM31 {
    let (linear, explicit_linear) = selected_mask_linears(point);
    let mut coefficients = [QM31::ZERO; STATE_ONLY_HIDING_FACTOR_DEGREE + 1];
    for column in 0..STATE_ONLY_HIDING_C1_COLUMNS {
        coefficients[usize::from(FACTOR_EXPONENTS[column])] =
            mul_tower_basis(c1[column], column & 3);
    }
    for column in 0..STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS {
        coefficients[usize::from(MASK_ONLY_FACTOR_EXPONENTS[column])] =
            mul_tower_basis(mask_only_c1[column], column & 3);
    }

    let prepared_linear = PreparedQm31Multiplier::new(linear);
    let mut shared = coefficients[STATE_ONLY_HIDING_FACTOR_DEGREE];
    for exponent in (0..STATE_ONLY_HIDING_FACTOR_DEGREE).rev() {
        shared = prepared_linear.mul(shared).add(coefficients[exponent]);
    }

    shared.add(
        QM31::ONE
            .add(mask_power_26(explicit_linear))
            .mul(explicit_g),
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

    fn legacy_selected_mask_value(
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

    #[test]
    fn selected_horner_matches_the_frozen_factor_evaluator() {
        let maximal = QM31 {
            c0: CM31::new(M31(P - 1), M31(P - 1)),
            c1: CM31::new(M31(P - 1), M31(P - 1)),
        };
        let alternating = QM31 {
            c0: CM31::new(M31::ZERO, M31::ONE),
            c1: CM31::new(M31(P - 1), M31(P - 2)),
        };
        let check = |c1: [QM31; STATE_ONLY_HIDING_C1_COLUMNS],
                     mask_only_c1: [QM31; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
                     explicit_g: QM31,
                     point: [QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS]| {
            assert_eq!(
                state_only_selected_mask_value(&c1, &mask_only_c1, explicit_g, &point),
                legacy_selected_mask_value(&c1, &mask_only_c1, explicit_g, &point),
            );
        };

        check(
            [QM31::ZERO; STATE_ONLY_HIDING_C1_COLUMNS],
            [QM31::ZERO; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
            QM31::ZERO,
            [QM31::ZERO; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
        );
        check(
            [QM31::ONE; STATE_ONLY_HIDING_C1_COLUMNS],
            [QM31::ONE; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
            QM31::ONE,
            [QM31::ONE; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
        );
        check(
            [maximal; STATE_ONLY_HIDING_C1_COLUMNS],
            [maximal; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
            maximal,
            [maximal; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
        );
        check(
            core::array::from_fn(|index| if index & 1 == 0 { alternating } else { maximal }),
            core::array::from_fn(|index| if index & 1 == 0 { maximal } else { alternating }),
            alternating,
            core::array::from_fn(|index| if index & 1 == 0 { QM31::ONE } else { maximal }),
        );

        let mut rng = Rng(0x484f_524e_4552_5633);
        for _ in 0..256 {
            check(
                core::array::from_fn(|_| rng.qm31()),
                core::array::from_fn(|_| rng.qm31()),
                rng.qm31(),
                core::array::from_fn(|_| rng.qm31()),
            );
        }
    }

    #[test]
    fn selected_linear_statistics_and_power_26_are_exact() {
        let maximal = QM31 {
            c0: CM31::new(M31(P - 1), M31(P - 1)),
            c1: CM31::new(M31(P - 1), M31(P - 1)),
        };
        let check_point = |point: [QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS]| {
            let (linear, explicit_linear) = selected_mask_linears(&point);
            assert_eq!(linear, mask_linear(0, &point));
            assert_eq!(explicit_linear, mask_linear(EXPLICIT_FACTOR_FAMILY, &point));
            assert_eq!(mask_power_26(explicit_linear), explicit_linear.pow(26));
        };
        check_point([QM31::ZERO; STATE_ONLY_HIDING_SUMCHECK_ROUNDS]);
        check_point([QM31::ONE; STATE_ONLY_HIDING_SUMCHECK_ROUNDS]);
        check_point([maximal; STATE_ONLY_HIDING_SUMCHECK_ROUNDS]);
        check_point(core::array::from_fn(|index| {
            if index & 1 == 0 {
                QM31::ONE
            } else {
                maximal
            }
        }));

        let mut rng = Rng(0x504f_5732_365f_4449);
        for _ in 0..256 {
            let value = rng.qm31();
            assert_eq!(mask_power_26(value), value.pow(26));
            check_point(core::array::from_fn(|_| rng.qm31()));
        }
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
        assert_eq!(
            PINNED_POOL_V1_PRIVATE_TRANSFER_ORDINARY_HG_LAYOUT_FACTOR_FINGERPRINT,
            state_only_hiding_layout_factor_fingerprint_for_registry(
                PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT,
                PINNED_POOL_V1_PRIVATE_TRANSFER_COPY_ACTIVE_ROWS_FINGERPRINT,
                true,
            ),
        );
        assert_eq!(
            PINNED_POOL_V1_WITHDRAWAL_ORDINARY_HG_LAYOUT_FACTOR_FINGERPRINT,
            state_only_hiding_layout_factor_fingerprint_for_registry(
                PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT,
                PINNED_POOL_V1_WITHDRAWAL_COPY_ACTIVE_ROWS_FINGERPRINT,
                true,
            ),
        );
        assert_eq!(
            PINNED_POOL_V1_PRIVATE_TRANSFER_HIDING_LAYOUT_FACTOR_FINGERPRINT,
            state_only_pool_v1_tag73_hiding_layout_factor_fingerprint(
                PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT,
                PINNED_POOL_V1_PRIVATE_TRANSFER_COPY_ACTIVE_ROWS_FINGERPRINT,
            ),
        );
        assert_eq!(
            PINNED_POOL_V1_WITHDRAWAL_HIDING_LAYOUT_FACTOR_FINGERPRINT,
            state_only_pool_v1_tag73_hiding_layout_factor_fingerprint(
                PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT,
                PINNED_POOL_V1_WITHDRAWAL_COPY_ACTIVE_ROWS_FINGERPRINT,
            ),
        );
        assert_eq!(
            PINNED_POOL_V1_PAIR_FOREST_ORDINARY_HG_LAYOUT_FACTOR_FINGERPRINT_V1,
            state_only_hiding_layout_factor_fingerprint_for_registry(
                PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1,
                PINNED_POOL_V1_PAIR_FOREST_COPY_ACTIVE_ROWS_FINGERPRINT_V1,
                true,
            ),
        );
        assert_eq!(
            PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1,
            state_only_pool_v1_tag73_hiding_layout_factor_fingerprint(
                PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1,
                PINNED_POOL_V1_PAIR_FOREST_COPY_ACTIVE_ROWS_FINGERPRINT_V1,
            ),
        );
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

    #[test]
    fn pool_contexts_bind_distinct_copy_active_registries() {
        let transfer = StateOnlyHidingContext::pool_v1_private_transfer([0x73; 32], [0x41; 32]);
        let withdrawal = StateOnlyHidingContext::pool_v1_withdrawal([0x73; 32], [0x41; 32]);
        assert_eq!(
            transfer.mask_layout_fingerprint,
            withdrawal.mask_layout_fingerprint
        );
        assert_ne!(
            transfer.layout_factor_fingerprint,
            withdrawal.layout_factor_fingerprint
        );
        for context in [transfer, withdrawal] {
            let mut transcript = Transcript::new(host_hash);
            assert!(begin_state_only_hiding_precommit(&mut transcript, context).is_ok());
        }

        let mut crossed = transfer;
        crossed.layout_factor_fingerprint = withdrawal.layout_factor_fingerprint ^ 1;
        let mut transcript = Transcript::new(host_hash);
        assert_eq!(
            begin_state_only_hiding_precommit(&mut transcript, crossed),
            Err(StateOnlyHidingScheduleError::LayoutFactorFingerprint),
        );
    }

    #[test]
    fn pair_forest_context_binds_exact_mask_copy_and_tag73_profile() {
        let context = StateOnlyHidingContext::pool_v1_pair_forest_v1([0x73; 32], [0x48; 32]);
        assert_eq!(
            context.mask_layout_fingerprint,
            PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1
        );
        assert_eq!(
            context.layout_factor_fingerprint,
            PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1
        );
        let mut transcript = Transcript::new(host_hash);
        assert!(begin_state_only_hiding_precommit(&mut transcript, context).is_ok());

        let mut crossed = context;
        crossed.mask_layout_fingerprint = PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT;
        let mut transcript = Transcript::new(host_hash);
        assert_eq!(
            begin_state_only_hiding_precommit(&mut transcript, crossed),
            Err(StateOnlyHidingScheduleError::LayoutFactorFingerprint)
        );
    }
}
