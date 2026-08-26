//! Host-only state-only masking helper and complete public-view inventory.
//!
//! This remains production-neutral: it does not choose the PCS envelope or
//! mutate Solana accounts. It does freeze mask seed derivation, one-time nonce
//! handling, the exact affine mask oracle, and the byte inventory which a
//! complete HVZK argument must cover.

use std::collections::BTreeSet;

use aspis_core::field::{CM31, M31, P, QM31};
#[cfg(test)]
use aspis_core::state_only_hiding::{
    begin_state_only_hiding_precommit, STATE_ONLY_H1_PADDING_MASK_FREE_QM31,
};
use aspis_core::state_only_hiding::{
    begin_state_only_masked_sumcheck, state_only_selected_mask_value, StateOnlyHidingContext,
    StateOnlyHidingScheduleError, PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT,
    PINNED_POOL_V1_PRIVATE_TRANSFER_HIDING_LAYOUT_FACTOR_FINGERPRINT,
    PINNED_POOL_V1_WITHDRAWAL_HIDING_LAYOUT_FACTOR_FINGERPRINT, STATE_ONLY_H1_PADDING_MASK_END,
    STATE_ONLY_H1_PADDING_MASK_START, STATE_ONLY_HIDING_C1_COLUMNS,
    STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS, STATE_ONLY_HIDING_SUMCHECK_ROUNDS,
};
use aspis_core::transcript::Transcript;
use aspis_core::HashFn;
use aspis_statement::{
    atomic_state_only_registry::atomic_state_only_relation_free_mask_cells_v3,
    atomic_state_only_terminal::atomic_state_only_copy_active_rows_v3,
    pool_v1::{
        pool_v1_payment_relation_free_mask_cells_v1,
        pool_v1_private_transfer_copy_active_row_masks_compiled_v1,
        pool_v1_withdrawal_copy_active_row_masks_compiled_v1,
    },
    state_only_copy_active_rows_v4, state_only_relation_free_mask_cells_v4,
    StateOnlyTraceFoundation, STATE_ONLY_POSEIDON_TRACE_ROWS,
};
use zeroize::Zeroize;

use crate::state_only_zerocheck::{
    prove_state_only_sumcheck_from_claim, StateOnlyZerocheckProveError, StateOnlyZerocheckTrace,
};

const MASK_SEED_DOMAIN: &[u8] = b"aspis:state-only:private-mask-seed:v1";
const MASK_EXPAND_DOMAIN: &[u8] = b"aspis:state-only:private-mask-expand:v1";
const VIEW_DOMAIN: &[u8] = b"aspis:state-only:complete-public-view:v1";
const MASK_SAMPLE_RETRY_LIMIT: usize = 16;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateOnlyMaskBuildError {
    ZeroPrivateEntropy,
    ReusedMaskNonce,
    MaskSampleExhausted,
    TraceShape,
    Layout,
}

/// The caller must back this with storage whose lifetime covers every proof
/// made under the same key. The in-memory implementation below is a test and
/// single-process helper, not a durable wallet database.
pub trait StateOnlyMaskNonceStore {
    fn reserve(&mut self, statement_digest: [u8; 32], mask_nonce: [u8; 32]) -> bool;
}

#[derive(Default)]
pub struct InMemoryStateOnlyMaskNonceStore {
    seen: BTreeSet<([u8; 32], [u8; 32])>,
}

impl StateOnlyMaskNonceStore for InMemoryStateOnlyMaskNonceStore {
    fn reserve(&mut self, statement_digest: [u8; 32], mask_nonce: [u8; 32]) -> bool {
        self.seen.insert((statement_digest, mask_nonce))
    }
}

pub struct StateOnlyMaskMaterial {
    c1: Vec<M31>,
    mask_only_c1: [Vec<M31>; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
    g: Vec<QM31>,
    h1_padding: Vec<QM31>,
    pub mask_nonce: [u8; 32],
}

fn volatile_clear<T: Copy>(values: &mut [T], zero: T) {
    for value in values {
        // SAFETY: callers pass uniquely borrowed attempt-owned storage.
        unsafe { core::ptr::write_volatile(value, zero) };
    }
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}

impl Drop for StateOnlyMaskMaterial {
    fn drop(&mut self) {
        volatile_clear(&mut self.c1, M31::ZERO);
        for column in &mut self.mask_only_c1 {
            volatile_clear(column, M31::ZERO);
        }
        volatile_clear(&mut self.g, QM31::ZERO);
        volatile_clear(&mut self.h1_padding, QM31::ZERO);
        self.mask_nonce.zeroize();
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct AppliedStateOnlyMasks {
    /// Ten full-domain M31 columns committed after semantic C1 columns 0..15.
    pub mask_only_c1: [Vec<M31>; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
    pub g: Vec<QM31>,
    /// Random only on rows absent from every copy endpoint. Its inactive
    /// sum is zero. The caller adds it to the uniquely determined copy helper
    /// after `lambda,chi`.
    pub h1_padding: Vec<QM31>,
    pub mask_nonce: [u8; 32],
}

impl Drop for AppliedStateOnlyMasks {
    fn drop(&mut self) {
        for column in &mut self.mask_only_c1 {
            volatile_clear(column, M31::ZERO);
        }
        volatile_clear(&mut self.g, QM31::ZERO);
        volatile_clear(&mut self.h1_padding, QM31::ZERO);
        self.mask_nonce.zeroize();
    }
}

fn copy_active_rows() -> [bool; STATE_ONLY_POSEIDON_TRACE_ROWS] {
    active_rows(state_only_copy_active_rows_v4())
}

fn active_rows(rows: &[u16]) -> [bool; STATE_ONLY_POSEIDON_TRACE_ROWS] {
    let mut active = [false; STATE_ONLY_POSEIDON_TRACE_ROWS];
    for &row in rows {
        active[usize::from(row)] = true;
    }
    active
}

fn atomic_copy_active_rows() -> [bool; STATE_ONLY_POSEIDON_TRACE_ROWS] {
    active_rows(atomic_state_only_copy_active_rows_v3())
}

fn active_rows_from_masks(masks: &[u16; 64]) -> [bool; STATE_ONLY_POSEIDON_TRACE_ROWS] {
    core::array::from_fn(|row| masks[row >> 4] & (1 << (row & 15)) != 0)
}

fn pool_v1_private_transfer_copy_active_rows() -> [bool; STATE_ONLY_POSEIDON_TRACE_ROWS] {
    active_rows_from_masks(pool_v1_private_transfer_copy_active_row_masks_compiled_v1())
}

fn pool_v1_withdrawal_copy_active_rows() -> [bool; STATE_ONLY_POSEIDON_TRACE_ROWS] {
    active_rows_from_masks(pool_v1_withdrawal_copy_active_row_masks_compiled_v1())
}

fn first_inactive_row(active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS]) -> usize {
    (0..STATE_ONLY_POSEIDON_TRACE_ROWS)
        .find(|row| !active[*row])
        .expect("generated layout has an inactive row")
}

fn balance_m31_copy_inactive(
    table: &mut [M31],
    dependent: usize,
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
) -> Result<(), StateOnlyMaskBuildError> {
    if table.len() != STATE_ONLY_POSEIDON_TRACE_ROWS || active[dependent] {
        return Err(StateOnlyMaskBuildError::TraceShape);
    }
    let sum = (0..STATE_ONLY_POSEIDON_TRACE_ROWS)
        .filter(|row| !active[*row] && *row != dependent)
        .fold(M31::ZERO, |sum, row| sum.add(table[row]));
    table[dependent] = M31::ZERO.sub(sum);
    Ok(())
}

fn balance_qm31_copy_inactive(
    table: &mut [QM31],
    dependent: usize,
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
) -> Result<(), StateOnlyMaskBuildError> {
    if table.len() != STATE_ONLY_POSEIDON_TRACE_ROWS || active[dependent] {
        return Err(StateOnlyMaskBuildError::TraceShape);
    }
    let sum = (0..STATE_ONLY_POSEIDON_TRACE_ROWS)
        .filter(|row| !active[*row] && *row != dependent)
        .fold(QM31::ZERO, |sum, row| sum.add(table[row]));
    table[dependent] = QM31::ZERO.sub(sum);
    Ok(())
}

pub fn state_only_copy_inactive_sum_qm31(table: &[QM31]) -> Option<QM31> {
    (table.len() == STATE_ONLY_POSEIDON_TRACE_ROWS).then(|| {
        let active = copy_active_rows();
        table
            .iter()
            .copied()
            .enumerate()
            .filter(|(row, _)| !active[*row])
            .fold(QM31::ZERO, |sum, (_, value)| sum.add(value))
    })
}

pub fn state_only_copy_inactive_sum_m31(table: &[M31]) -> Option<M31> {
    (table.len() == STATE_ONLY_POSEIDON_TRACE_ROWS).then(|| {
        let active = copy_active_rows();
        table
            .iter()
            .copied()
            .enumerate()
            .filter(|(row, _)| !active[*row])
            .fold(M31::ZERO, |sum, (_, value)| sum.add(value))
    })
}

pub fn state_only_padding_sum_m31(table: &[M31]) -> Option<M31> {
    (table.len() == STATE_ONLY_POSEIDON_TRACE_ROWS).then(|| {
        table[STATE_ONLY_H1_PADDING_MASK_START..STATE_ONLY_H1_PADDING_MASK_END]
            .iter()
            .copied()
            .fold(M31::ZERO, M31::add)
    })
}

pub fn state_only_padding_sum_qm31(table: &[QM31]) -> Option<QM31> {
    (table.len() == STATE_ONLY_POSEIDON_TRACE_ROWS).then(|| {
        table[STATE_ONLY_H1_PADDING_MASK_START..STATE_ONLY_H1_PADDING_MASK_END]
            .iter()
            .copied()
            .fold(QM31::ZERO, QM31::add)
    })
}

pub fn apply_state_only_h1_padding_mask(
    h1: &mut [QM31],
    padding: &[QM31],
) -> Result<(), StateOnlyMaskBuildError> {
    apply_h1_padding_mask_for_active(h1, padding, &copy_active_rows())
}

fn apply_h1_padding_mask_for_active(
    h1: &mut [QM31],
    padding: &[QM31],
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
) -> Result<(), StateOnlyMaskBuildError> {
    if h1.len() != STATE_ONLY_POSEIDON_TRACE_ROWS
        || padding.len() != STATE_ONLY_POSEIDON_TRACE_ROWS
        || active
            .iter()
            .copied()
            .zip(padding)
            .any(|(active, value)| active && *value != QM31::ZERO)
        || padding
            .iter()
            .copied()
            .enumerate()
            .filter(|(row, _)| !active[*row])
            .fold(QM31::ZERO, |sum, (_, value)| sum.add(value))
            != QM31::ZERO
    {
        return Err(StateOnlyMaskBuildError::TraceShape);
    }
    for (value, mask) in h1.iter_mut().zip(padding) {
        *value = value.add(*mask);
    }
    Ok(())
}

pub fn apply_atomic_state_only_h1_padding_mask_v3(
    h1: &mut [QM31],
    padding: &[QM31],
) -> Result<(), StateOnlyMaskBuildError> {
    apply_h1_padding_mask_for_active(h1, padding, &atomic_copy_active_rows())
}

pub fn apply_pool_v1_private_transfer_h1_padding_mask_v1(
    h1: &mut [QM31],
    padding: &[QM31],
) -> Result<(), StateOnlyMaskBuildError> {
    apply_h1_padding_mask_for_active(h1, padding, &pool_v1_private_transfer_copy_active_rows())
}

pub fn apply_pool_v1_withdrawal_h1_padding_mask_v1(
    h1: &mut [QM31],
    padding: &[QM31],
) -> Result<(), StateOnlyMaskBuildError> {
    apply_h1_padding_mask_for_active(h1, padding, &pool_v1_withdrawal_copy_active_rows())
}

struct SeedExpander {
    hash: HashFn,
    seed: [u8; 32],
    counter: u64,
    block: [u8; 32],
    word: usize,
}

impl Drop for SeedExpander {
    fn drop(&mut self) {
        self.seed.zeroize();
        self.block.zeroize();
        self.counter.zeroize();
        self.word.zeroize();
    }
}

impl SeedExpander {
    fn new(hash: HashFn, seed: [u8; 32]) -> Self {
        Self {
            hash,
            seed,
            counter: 0,
            block: [0; 32],
            word: 8,
        }
    }

    fn next_word(&mut self) -> u32 {
        if self.word == 8 {
            self.block =
                (self.hash)(&[MASK_EXPAND_DOMAIN, &self.seed, &self.counter.to_le_bytes()]);
            self.counter = self.counter.wrapping_add(1);
            self.word = 0;
        }
        let start = 4 * self.word;
        self.word += 1;
        u32::from_le_bytes(self.block[start..start + 4].try_into().unwrap())
    }

    fn m31(&mut self) -> Result<M31, StateOnlyMaskBuildError> {
        for _ in 0..MASK_SAMPLE_RETRY_LIMIT {
            let candidate = self.next_word() & 0x7fff_ffff;
            if candidate < P {
                return Ok(M31(candidate));
            }
        }
        Err(StateOnlyMaskBuildError::MaskSampleExhausted)
    }

    fn qm31(&mut self) -> Result<QM31, StateOnlyMaskBuildError> {
        Ok(QM31 {
            c0: CM31::new(self.m31()?, self.m31()?),
            c1: CM31::new(self.m31()?, self.m31()?),
        })
    }
}

/// Derive a private one-time seed. `precommit_binding` is public transcript
/// state; secrecy comes exclusively from `private_entropy`.
pub fn derive_state_only_mask_seed(
    hash: HashFn,
    precommit_binding: [u8; 32],
    context: StateOnlyHidingContext,
    mut private_entropy: [u8; 32],
) -> Result<[u8; 32], StateOnlyMaskBuildError> {
    let result = derive_state_only_mask_seed_from_entropy_ref(
        hash,
        precommit_binding,
        context,
        &private_entropy,
    );
    private_entropy.zeroize();
    result
}

fn derive_state_only_mask_seed_from_entropy_ref(
    hash: HashFn,
    precommit_binding: [u8; 32],
    context: StateOnlyHidingContext,
    private_entropy: &[u8; 32],
) -> Result<[u8; 32], StateOnlyMaskBuildError> {
    if *private_entropy == [0; 32] {
        return Err(StateOnlyMaskBuildError::ZeroPrivateEntropy);
    }
    Ok(hash(&[
        MASK_SEED_DOMAIN,
        &precommit_binding,
        &context.encode(),
        private_entropy,
    ]))
}

pub fn build_state_only_mask_material(
    hash: HashFn,
    precommit_binding: [u8; 32],
    context: StateOnlyHidingContext,
    mut private_entropy: [u8; 32],
    nonce_store: &mut impl StateOnlyMaskNonceStore,
) -> Result<StateOnlyMaskMaterial, StateOnlyMaskBuildError> {
    let result = state_only_relation_free_mask_cells_v4()
        .map_err(|_| StateOnlyMaskBuildError::Layout)
        .and_then(|cells| {
            build_mask_material_for_layout(
                hash,
                precommit_binding,
                context,
                &private_entropy,
                nonce_store,
                &cells,
                &copy_active_rows(),
            )
        });
    private_entropy.zeroize();
    result
}

fn build_mask_material_for_layout(
    hash: HashFn,
    precommit_binding: [u8; 32],
    context: StateOnlyHidingContext,
    private_entropy: &[u8; 32],
    nonce_store: &mut impl StateOnlyMaskNonceStore,
    cells: &[aspis_statement::TraceCell],
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
) -> Result<StateOnlyMaskMaterial, StateOnlyMaskBuildError> {
    if !nonce_store.reserve(context.statement_digest, context.mask_nonce) {
        return Err(StateOnlyMaskBuildError::ReusedMaskNonce);
    }
    let seed = derive_state_only_mask_seed_from_entropy_ref(
        hash,
        precommit_binding,
        context,
        private_entropy,
    )?;
    let mut expander = SeedExpander::new(hash, seed);
    let inactive_dependent = first_inactive_row(active);
    let mut c1 = Vec::with_capacity(cells.len());
    for _ in 0..cells.len() {
        c1.push(expander.m31()?);
    }
    let mut mask_only_c1: [Vec<M31>; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS] =
        core::array::from_fn(|_| Vec::with_capacity(STATE_ONLY_POSEIDON_TRACE_ROWS));
    for column in &mut mask_only_c1 {
        for _ in 0..STATE_ONLY_POSEIDON_TRACE_ROWS {
            column.push(expander.m31()?);
        }
        balance_m31_copy_inactive(column, inactive_dependent, active)?;
    }
    let mut g = Vec::with_capacity(STATE_ONLY_POSEIDON_TRACE_ROWS);
    for _ in 0..STATE_ONLY_POSEIDON_TRACE_ROWS {
        g.push(expander.qm31()?);
    }
    balance_qm31_copy_inactive(&mut g, inactive_dependent, active)?;
    let mut h1_padding = vec![QM31::ZERO; STATE_ONLY_POSEIDON_TRACE_ROWS];
    for row in 0..STATE_ONLY_POSEIDON_TRACE_ROWS {
        if !active[row] && row != inactive_dependent {
            h1_padding[row] = expander.qm31()?;
        }
    }
    balance_qm31_copy_inactive(&mut h1_padding, inactive_dependent, active)?;
    Ok(StateOnlyMaskMaterial {
        c1,
        mask_only_c1,
        g,
        h1_padding,
        mask_nonce: context.mask_nonce,
    })
}

pub fn build_atomic_state_only_mask_material_v3(
    hash: HashFn,
    precommit_binding: [u8; 32],
    context: StateOnlyHidingContext,
    mut private_entropy: [u8; 32],
    nonce_store: &mut impl StateOnlyMaskNonceStore,
) -> Result<StateOnlyMaskMaterial, StateOnlyMaskBuildError> {
    let result = build_atomic_state_only_mask_material_v3_from_entropy_ref(
        hash,
        precommit_binding,
        context,
        &private_entropy,
        nonce_store,
    );
    private_entropy.zeroize();
    result
}

pub(crate) fn build_atomic_state_only_mask_material_v3_from_entropy_ref(
    hash: HashFn,
    precommit_binding: [u8; 32],
    context: StateOnlyHidingContext,
    private_entropy: &[u8; 32],
    nonce_store: &mut impl StateOnlyMaskNonceStore,
) -> Result<StateOnlyMaskMaterial, StateOnlyMaskBuildError> {
    let cells = atomic_state_only_relation_free_mask_cells_v3()
        .map_err(|_| StateOnlyMaskBuildError::Layout)?;
    build_mask_material_for_layout(
        hash,
        precommit_binding,
        context,
        private_entropy,
        nonce_store,
        &cells,
        &atomic_copy_active_rows(),
    )
}

fn build_pool_v1_payment_mask_material_v1(
    hash: HashFn,
    precommit_binding: [u8; 32],
    context: StateOnlyHidingContext,
    private_entropy: &[u8; 32],
    nonce_store: &mut impl StateOnlyMaskNonceStore,
    expected_factor_fingerprint: u64,
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
) -> Result<StateOnlyMaskMaterial, StateOnlyMaskBuildError> {
    if context.mask_layout_fingerprint != PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT
        || context.layout_factor_fingerprint != expected_factor_fingerprint
    {
        return Err(StateOnlyMaskBuildError::Layout);
    }
    let cells = pool_v1_payment_relation_free_mask_cells_v1()
        .map_err(|_| StateOnlyMaskBuildError::Layout)?;
    build_mask_material_for_layout(
        hash,
        precommit_binding,
        context,
        private_entropy,
        nonce_store,
        &cells,
        active,
    )
}

pub(crate) fn build_pool_v1_private_transfer_mask_material_v1_from_entropy_ref(
    hash: HashFn,
    precommit_binding: [u8; 32],
    context: StateOnlyHidingContext,
    private_entropy: &[u8; 32],
    nonce_store: &mut impl StateOnlyMaskNonceStore,
) -> Result<StateOnlyMaskMaterial, StateOnlyMaskBuildError> {
    build_pool_v1_payment_mask_material_v1(
        hash,
        precommit_binding,
        context,
        private_entropy,
        nonce_store,
        PINNED_POOL_V1_PRIVATE_TRANSFER_HIDING_LAYOUT_FACTOR_FINGERPRINT,
        &pool_v1_private_transfer_copy_active_rows(),
    )
}

pub(crate) fn build_pool_v1_withdrawal_mask_material_v1_from_entropy_ref(
    hash: HashFn,
    precommit_binding: [u8; 32],
    context: StateOnlyHidingContext,
    private_entropy: &[u8; 32],
    nonce_store: &mut impl StateOnlyMaskNonceStore,
) -> Result<StateOnlyMaskMaterial, StateOnlyMaskBuildError> {
    build_pool_v1_payment_mask_material_v1(
        hash,
        precommit_binding,
        context,
        private_entropy,
        nonce_store,
        PINNED_POOL_V1_WITHDRAWAL_HIDING_LAYOUT_FACTOR_FINGERPRINT,
        &pool_v1_withdrawal_copy_active_rows(),
    )
}

pub fn build_pool_v1_private_transfer_mask_material_v1(
    hash: HashFn,
    precommit_binding: [u8; 32],
    context: StateOnlyHidingContext,
    mut private_entropy: [u8; 32],
    nonce_store: &mut impl StateOnlyMaskNonceStore,
) -> Result<StateOnlyMaskMaterial, StateOnlyMaskBuildError> {
    let result = build_pool_v1_private_transfer_mask_material_v1_from_entropy_ref(
        hash,
        precommit_binding,
        context,
        &private_entropy,
        nonce_store,
    );
    private_entropy.zeroize();
    result
}

pub fn build_pool_v1_withdrawal_mask_material_v1(
    hash: HashFn,
    precommit_binding: [u8; 32],
    context: StateOnlyHidingContext,
    mut private_entropy: [u8; 32],
    nonce_store: &mut impl StateOnlyMaskNonceStore,
) -> Result<StateOnlyMaskMaterial, StateOnlyMaskBuildError> {
    let result = build_pool_v1_withdrawal_mask_material_v1_from_entropy_ref(
        hash,
        precommit_binding,
        context,
        &private_entropy,
        nonce_store,
    );
    private_entropy.zeroize();
    result
}

/// Consume the one-time material while applying it, making accidental reuse
/// through this API impossible without reconstructing material from a reused
/// nonce (which the nonce store rejects).
pub fn apply_state_only_mask_material(
    trace: &mut StateOnlyTraceFoundation,
    material: StateOnlyMaskMaterial,
) -> Result<AppliedStateOnlyMasks, StateOnlyMaskBuildError> {
    let cells =
        state_only_relation_free_mask_cells_v4().map_err(|_| StateOnlyMaskBuildError::Layout)?;
    apply_mask_material_for_layout(trace, material, &cells, &copy_active_rows())
}

fn apply_mask_material_for_layout(
    trace: &mut StateOnlyTraceFoundation,
    mut material: StateOnlyMaskMaterial,
    cells: &[aspis_statement::TraceCell],
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
) -> Result<AppliedStateOnlyMasks, StateOnlyMaskBuildError> {
    if trace
        .c1
        .iter()
        .any(|column| column.len() != STATE_ONLY_POSEIDON_TRACE_ROWS)
    {
        return Err(StateOnlyMaskBuildError::TraceShape);
    }
    if material.c1.len() != cells.len()
        || material
            .mask_only_c1
            .iter()
            .any(|column| column.len() != STATE_ONLY_POSEIDON_TRACE_ROWS)
        || material.g.len() != STATE_ONLY_POSEIDON_TRACE_ROWS
        || material.h1_padding.len() != STATE_ONLY_POSEIDON_TRACE_ROWS
    {
        return Err(StateOnlyMaskBuildError::TraceShape);
    }
    let mut inactive_dependents = [None; STATE_ONLY_HIDING_C1_COLUMNS];
    for cell in cells {
        let row = usize::from(cell.row);
        let column = usize::from(cell.column);
        if !active[row] {
            inactive_dependents[column] = Some(row);
        }
    }
    if inactive_dependents.iter().any(Option::is_none) {
        return Err(StateOnlyMaskBuildError::Layout);
    }
    for (cell, mask) in cells.iter().copied().zip(core::mem::take(&mut material.c1)) {
        let value = &mut trace.c1[usize::from(cell.column)][usize::from(cell.row)];
        *value = value.add(mask);
    }
    for (column, dependent) in trace.c1.iter_mut().zip(inactive_dependents) {
        balance_m31_copy_inactive(column, dependent.unwrap(), active)?;
    }
    Ok(AppliedStateOnlyMasks {
        mask_only_c1: core::mem::take(&mut material.mask_only_c1),
        g: core::mem::take(&mut material.g),
        h1_padding: core::mem::take(&mut material.h1_padding),
        mask_nonce: material.mask_nonce,
    })
}

pub fn apply_atomic_state_only_mask_material_v3(
    trace: &mut StateOnlyTraceFoundation,
    material: StateOnlyMaskMaterial,
) -> Result<AppliedStateOnlyMasks, StateOnlyMaskBuildError> {
    let cells = atomic_state_only_relation_free_mask_cells_v3()
        .map_err(|_| StateOnlyMaskBuildError::Layout)?;
    apply_mask_material_for_layout(trace, material, &cells, &atomic_copy_active_rows())
}

pub fn apply_pool_v1_private_transfer_mask_material_v1(
    trace: &mut StateOnlyTraceFoundation,
    material: StateOnlyMaskMaterial,
) -> Result<AppliedStateOnlyMasks, StateOnlyMaskBuildError> {
    let cells = pool_v1_payment_relation_free_mask_cells_v1()
        .map_err(|_| StateOnlyMaskBuildError::Layout)?;
    apply_mask_material_for_layout(
        trace,
        material,
        &cells,
        &pool_v1_private_transfer_copy_active_rows(),
    )
}

pub fn apply_pool_v1_withdrawal_mask_material_v1(
    trace: &mut StateOnlyTraceFoundation,
    material: StateOnlyMaskMaterial,
) -> Result<AppliedStateOnlyMasks, StateOnlyMaskBuildError> {
    let cells = pool_v1_payment_relation_free_mask_cells_v1()
        .map_err(|_| StateOnlyMaskBuildError::Layout)?;
    apply_mask_material_for_layout(
        trace,
        material,
        &cells,
        &pool_v1_withdrawal_copy_active_rows(),
    )
}

fn evaluate_m31_table(
    table: &[M31],
    point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
) -> Result<QM31, StateOnlyMaskBuildError> {
    if table.len() != STATE_ONLY_POSEIDON_TRACE_ROWS {
        return Err(StateOnlyMaskBuildError::TraceShape);
    }
    let mut layer = table
        .iter()
        .copied()
        .map(|value| QM31::from_cm31(CM31::from_m31(value)))
        .collect::<Vec<_>>();
    for coordinate in point.iter().rev() {
        let mut next = Vec::with_capacity(layer.len() / 2);
        for pair in layer.chunks_exact(2) {
            next.push(pair[0].add(coordinate.mul(pair[1].sub(pair[0]))));
        }
        layer = next;
    }
    Ok(layer[0])
}

fn evaluate_qm31_table(
    table: &[QM31],
    point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
) -> Result<QM31, StateOnlyMaskBuildError> {
    if table.len() != STATE_ONLY_POSEIDON_TRACE_ROWS {
        return Err(StateOnlyMaskBuildError::TraceShape);
    }
    let mut layer = table.to_vec();
    for coordinate in point.iter().rev() {
        let mut next = Vec::with_capacity(layer.len() / 2);
        for pair in layer.chunks_exact(2) {
            next.push(pair[0].add(coordinate.mul(pair[1].sub(pair[0]))));
        }
        layer = next;
    }
    Ok(layer[0])
}

pub fn state_only_mask_oracle_value(
    trace: &StateOnlyTraceFoundation,
    mask_only_c1: &[Vec<M31>; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
    g: &[QM31],
    point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
) -> Result<QM31, StateOnlyMaskBuildError> {
    if trace.c1.len() != STATE_ONLY_HIDING_C1_COLUMNS
        || trace
            .c1
            .iter()
            .any(|column| column.len() != STATE_ONLY_POSEIDON_TRACE_ROWS)
        || mask_only_c1
            .iter()
            .any(|column| column.len() != STATE_ONLY_POSEIDON_TRACE_ROWS)
    {
        return Err(StateOnlyMaskBuildError::TraceShape);
    }
    let c1: [QM31; STATE_ONLY_HIDING_C1_COLUMNS] =
        core::array::from_fn(|column| evaluate_m31_table(&trace.c1[column], point).unwrap());
    let mask_only_c1 =
        core::array::from_fn(|column| evaluate_m31_table(&mask_only_c1[column], point).unwrap());
    Ok(state_only_selected_mask_value(
        &c1,
        &mask_only_c1,
        evaluate_qm31_table(g, point)?,
        point,
    ))
}

pub fn state_only_initial_mask_claim(
    trace: &StateOnlyTraceFoundation,
    mask_only_c1: &[Vec<M31>; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
    g: &[QM31],
) -> Result<QM31, StateOnlyMaskBuildError> {
    if trace
        .c1
        .iter()
        .any(|column| column.len() != STATE_ONLY_POSEIDON_TRACE_ROWS)
        || mask_only_c1
            .iter()
            .any(|column| column.len() != STATE_ONLY_POSEIDON_TRACE_ROWS)
        || g.len() != STATE_ONLY_POSEIDON_TRACE_ROWS
    {
        return Err(StateOnlyMaskBuildError::TraceShape);
    }
    let mut claim = QM31::ZERO;
    for row in 0..STATE_ONLY_POSEIDON_TRACE_ROWS {
        let point = core::array::from_fn(|coordinate| {
            if (row >> (STATE_ONLY_HIDING_SUMCHECK_ROUNDS - 1 - coordinate)) & 1 == 0 {
                QM31::ZERO
            } else {
                QM31::ONE
            }
        });
        let c1 =
            core::array::from_fn(|column| QM31::from_cm31(CM31::from_m31(trace.c1[column][row])));
        let mask_only_c1 = core::array::from_fn(|column| {
            QM31::from_cm31(CM31::from_m31(mask_only_c1[column][row]))
        });
        claim = claim.add(state_only_selected_mask_value(
            &c1,
            &mask_only_c1,
            g[row],
            &point,
        ));
    }
    Ok(claim)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MaskedStateOnlyZerocheckTrace {
    pub initial_mask_claim: QM31,
    pub eta: QM31,
    pub sumcheck: StateOnlyZerocheckTrace,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MaskedStateOnlyZerocheckError<E> {
    RootsNotBound,
    Mask(StateOnlyMaskBuildError),
    Schedule(StateOnlyHidingScheduleError),
    Sumcheck(StateOnlyZerocheckProveError<E>),
}

/// Prove `H + eta*F`, where the caller has already absorbed every masked root
/// after `precommit_binding`. The honest unmasked zerocheck claim is zero, so
/// the combined initial claim is exactly `sum(H)`.
pub fn prove_masked_state_only_zerocheck<F, E>(
    transcript: &mut Transcript,
    precommit_binding: [u8; 32],
    trace: &StateOnlyTraceFoundation,
    mask_only_c1: &[Vec<M31>; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
    g: &[QM31],
    mut original_oracle: F,
) -> Result<MaskedStateOnlyZerocheckTrace, MaskedStateOnlyZerocheckError<E>>
where
    F: FnMut(&[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS]) -> Result<QM31, E>,
{
    if transcript.diagnostic_state() == precommit_binding {
        return Err(MaskedStateOnlyZerocheckError::RootsNotBound);
    }
    let initial_mask_claim = state_only_initial_mask_claim(trace, mask_only_c1, g)
        .map_err(MaskedStateOnlyZerocheckError::Mask)?;
    let eta = begin_state_only_masked_sumcheck(transcript, initial_mask_claim)
        .map_err(MaskedStateOnlyZerocheckError::Schedule)?;
    let sumcheck = prove_state_only_sumcheck_from_claim(
        transcript,
        |point| {
            let mask = state_only_mask_oracle_value(trace, mask_only_c1, g, point)
                .map_err(MaskedStateOnlyZerocheckError::Mask)?;
            let original = original_oracle(point).map_err(|error| {
                MaskedStateOnlyZerocheckError::Sumcheck(StateOnlyZerocheckProveError::Oracle(error))
            })?;
            Ok::<_, MaskedStateOnlyZerocheckError<E>>(mask.add(eta.mul(original)))
        },
        initial_mask_claim,
    )
    .map_err(|error| match error {
        StateOnlyZerocheckProveError::Oracle(error) => error,
        other => MaskedStateOnlyZerocheckError::Sumcheck(match other {
            StateOnlyZerocheckProveError::BoundaryMismatch { round } => {
                StateOnlyZerocheckProveError::BoundaryMismatch { round }
            }
            StateOnlyZerocheckProveError::TerminalMismatch => {
                StateOnlyZerocheckProveError::TerminalMismatch
            }
            StateOnlyZerocheckProveError::ChallengeSampleExhausted => {
                StateOnlyZerocheckProveError::ChallengeSampleExhausted
            }
            StateOnlyZerocheckProveError::Oracle(_) => unreachable!(),
        }),
    })?;
    Ok(MaskedStateOnlyZerocheckTrace {
        initial_mask_claim,
        eta,
        sumcheck,
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicAccountSnapshot {
    pub key: [u8; 32],
    pub owner: [u8; 32],
    pub lamports: u64,
    pub executable: bool,
    pub rent_epoch: u64,
    pub data: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicAccountDelta {
    pub before: Option<PublicAccountSnapshot>,
    pub after: Option<PublicAccountSnapshot>,
}

/// Complete public surface for the candidate transaction. Parsed roots and
/// openings are kept even though they also occur in `proof_bytes`: the
/// explicit duplication makes omissions in distinguisher tests visible.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateOnlyCompletePublicView {
    pub proof_bytes: Vec<u8>,
    pub roots: Vec<[u8; 32]>,
    pub openings: Vec<Vec<u8>>,
    pub statement_values: Vec<[u8; 16]>,
    pub program_logs: Vec<Vec<u8>>,
    pub state_delta: PublicAccountDelta,
    pub nullifier_delta: PublicAccountDelta,
    pub output_delta: PublicAccountDelta,
}

fn append_bytes(output: &mut Vec<u8>, bytes: &[u8]) {
    output.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
    output.extend_from_slice(bytes);
}

fn append_snapshot(output: &mut Vec<u8>, snapshot: &Option<PublicAccountSnapshot>) {
    match snapshot {
        None => output.push(0),
        Some(snapshot) => {
            output.push(1);
            output.extend_from_slice(&snapshot.key);
            output.extend_from_slice(&snapshot.owner);
            output.extend_from_slice(&snapshot.lamports.to_le_bytes());
            output.push(u8::from(snapshot.executable));
            output.extend_from_slice(&snapshot.rent_epoch.to_le_bytes());
            append_bytes(output, &snapshot.data);
        }
    }
}

fn append_delta(output: &mut Vec<u8>, delta: &PublicAccountDelta) {
    append_snapshot(output, &delta.before);
    append_snapshot(output, &delta.after);
}

impl StateOnlyCompletePublicView {
    pub fn canonical_bytes(&self) -> Vec<u8> {
        let mut output = Vec::new();
        append_bytes(&mut output, VIEW_DOMAIN);
        append_bytes(&mut output, &self.proof_bytes);
        output.extend_from_slice(&(self.roots.len() as u64).to_le_bytes());
        for root in &self.roots {
            output.extend_from_slice(root);
        }
        output.extend_from_slice(&(self.openings.len() as u64).to_le_bytes());
        for opening in &self.openings {
            append_bytes(&mut output, opening);
        }
        output.extend_from_slice(&(self.statement_values.len() as u64).to_le_bytes());
        for value in &self.statement_values {
            output.extend_from_slice(value);
        }
        output.extend_from_slice(&(self.program_logs.len() as u64).to_le_bytes());
        for log in &self.program_logs {
            append_bytes(&mut output, log);
        }
        append_delta(&mut output, &self.state_delta);
        append_delta(&mut output, &self.nullifier_delta);
        append_delta(&mut output, &self.output_delta);
        output
    }

    pub fn digest(&self, hash: HashFn) -> [u8; 32] {
        hash(&[VIEW_DOMAIN, &self.canonical_bytes()])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::HOST_HASH;
    use aspis_core::transcript::label;

    fn zero_trace() -> StateOnlyTraceFoundation {
        StateOnlyTraceFoundation {
            c1: core::array::from_fn(|_| vec![M31::ZERO; STATE_ONLY_POSEIDON_TRACE_ROWS]),
        }
    }

    fn mask_context(nonce: u8) -> StateOnlyHidingContext {
        StateOnlyHidingContext::pinned([0x51; 32], [nonce; 32])
    }

    fn precommit(context: StateOnlyHidingContext) -> ([u8; 32], Transcript) {
        let mut transcript = Transcript::new(HOST_HASH);
        transcript.absorb(label::STATEMENT, &context.statement_digest);
        let binding = begin_state_only_hiding_precommit(&mut transcript, context).unwrap();
        (binding, transcript)
    }

    fn inactive_m31_sum(table: &[M31], active: &[bool; 1024]) -> M31 {
        table
            .iter()
            .copied()
            .enumerate()
            .filter(|(row, _)| !active[*row])
            .fold(M31::ZERO, |sum, (_, value)| sum.add(value))
    }

    #[test]
    fn pool_material_and_h1_helpers_use_the_exact_variant_contexts() {
        let transfer_context =
            StateOnlyHidingContext::pool_v1_private_transfer([0x73; 32], [0x41; 32]);
        let (transfer_binding, _) = precommit(transfer_context);
        let mut transfer_store = InMemoryStateOnlyMaskNonceStore::default();
        let transfer_material = build_pool_v1_private_transfer_mask_material_v1(
            HOST_HASH,
            transfer_binding,
            transfer_context,
            [0x31; 32],
            &mut transfer_store,
        )
        .unwrap();
        assert_eq!(transfer_material.c1.len(), 5_428);
        let mut transfer_trace = zero_trace();
        let transfer_applied =
            apply_pool_v1_private_transfer_mask_material_v1(&mut transfer_trace, transfer_material)
                .unwrap();
        let transfer_active = pool_v1_private_transfer_copy_active_rows();
        assert!(transfer_trace
            .c1
            .iter()
            .all(|column| inactive_m31_sum(column, &transfer_active) == M31::ZERO));
        let mut transfer_h1 = vec![QM31::ZERO; STATE_ONLY_POSEIDON_TRACE_ROWS];
        apply_pool_v1_private_transfer_h1_padding_mask_v1(
            &mut transfer_h1,
            &transfer_applied.h1_padding,
        )
        .unwrap();
        assert_eq!(transfer_h1, transfer_applied.h1_padding);

        let withdrawal_context = StateOnlyHidingContext::pool_v1_withdrawal([0x73; 32], [0x42; 32]);
        let (withdrawal_binding, _) = precommit(withdrawal_context);
        let mut withdrawal_store = InMemoryStateOnlyMaskNonceStore::default();
        let withdrawal_material = build_pool_v1_withdrawal_mask_material_v1(
            HOST_HASH,
            withdrawal_binding,
            withdrawal_context,
            [0x32; 32],
            &mut withdrawal_store,
        )
        .unwrap();
        assert_eq!(withdrawal_material.c1.len(), 5_428);
        let mut withdrawal_trace = zero_trace();
        let withdrawal_applied =
            apply_pool_v1_withdrawal_mask_material_v1(&mut withdrawal_trace, withdrawal_material)
                .unwrap();
        let withdrawal_active = pool_v1_withdrawal_copy_active_rows();
        assert!(withdrawal_trace
            .c1
            .iter()
            .all(|column| inactive_m31_sum(column, &withdrawal_active) == M31::ZERO));
        let mut withdrawal_h1 = vec![QM31::ZERO; STATE_ONLY_POSEIDON_TRACE_ROWS];
        apply_pool_v1_withdrawal_h1_padding_mask_v1(
            &mut withdrawal_h1,
            &withdrawal_applied.h1_padding,
        )
        .unwrap();
        assert_eq!(withdrawal_h1, withdrawal_applied.h1_padding);

        let mut wrong_store = InMemoryStateOnlyMaskNonceStore::default();
        assert_eq!(
            build_pool_v1_private_transfer_mask_material_v1(
                HOST_HASH,
                withdrawal_binding,
                withdrawal_context,
                [0x33; 32],
                &mut wrong_store,
            )
            .err(),
            Some(StateOnlyMaskBuildError::Layout),
        );
    }

    #[test]
    fn private_seed_material_is_exact_fresh_and_consumed_once() {
        let context = mask_context(0xa7);
        let (binding, _) = precommit(context);
        let mut first_store = InMemoryStateOnlyMaskNonceStore::default();
        let material = build_state_only_mask_material(
            HOST_HASH,
            binding,
            context,
            [0x31; 32],
            &mut first_store,
        )
        .unwrap();
        assert_eq!(material.c1.len(), 5_374);
        assert!(material
            .mask_only_c1
            .iter()
            .all(|column| column.len() == STATE_ONLY_POSEIDON_TRACE_ROWS));
        assert_eq!(material.g.len(), STATE_ONLY_POSEIDON_TRACE_ROWS);
        assert_eq!(material.h1_padding.len(), STATE_ONLY_POSEIDON_TRACE_ROWS);
        let expected_c1 = material.c1.clone();
        let expected_mask_only_c1 = material.mask_only_c1.clone();
        let expected_g = material.g.clone();
        let expected_h1_padding = material.h1_padding.clone();
        assert!(expected_mask_only_c1
            .iter()
            .all(|column| state_only_copy_inactive_sum_m31(column) == Some(M31::ZERO)));
        assert_eq!(
            state_only_copy_inactive_sum_qm31(&expected_g),
            Some(QM31::ZERO)
        );
        assert_eq!(
            state_only_copy_inactive_sum_qm31(&expected_h1_padding),
            Some(QM31::ZERO)
        );
        assert!(state_only_copy_active_rows_v4()
            .iter()
            .all(|row| expected_h1_padding[usize::from(*row)] == QM31::ZERO));
        assert_eq!(
            STATE_ONLY_POSEIDON_TRACE_ROWS - state_only_copy_active_rows_v4().len() - 1,
            STATE_ONLY_H1_PADDING_MASK_FREE_QM31
        );

        assert_eq!(
            build_state_only_mask_material(
                HOST_HASH,
                binding,
                context,
                [0x41; 32],
                &mut first_store,
            )
            .err(),
            Some(StateOnlyMaskBuildError::ReusedMaskNonce)
        );

        let mut deterministic_store = InMemoryStateOnlyMaskNonceStore::default();
        let deterministic = build_state_only_mask_material(
            HOST_HASH,
            binding,
            context,
            [0x31; 32],
            &mut deterministic_store,
        )
        .unwrap();
        assert_eq!(deterministic.c1, expected_c1);
        assert_eq!(deterministic.mask_only_c1, expected_mask_only_c1);
        assert_eq!(deterministic.g, expected_g);
        assert_eq!(deterministic.h1_padding, expected_h1_padding);

        let fresh_context = mask_context(0xb3);
        let (fresh_binding, _) = precommit(fresh_context);
        let mut fresh_store = InMemoryStateOnlyMaskNonceStore::default();
        let fresh = build_state_only_mask_material(
            HOST_HASH,
            fresh_binding,
            fresh_context,
            [0x32; 32],
            &mut fresh_store,
        )
        .unwrap();
        assert_ne!(fresh.c1, expected_c1);
        assert_ne!(fresh.mask_only_c1, expected_mask_only_c1);
        assert_ne!(fresh.g, expected_g);
        assert_ne!(fresh.h1_padding, expected_h1_padding);

        let mut trace = zero_trace();
        let applied = apply_state_only_mask_material(&mut trace, material).unwrap();
        assert_eq!(applied.mask_only_c1, expected_mask_only_c1);
        assert_eq!(applied.g, expected_g);
        assert_eq!(applied.h1_padding, expected_h1_padding);
        let cells = state_only_relation_free_mask_cells_v4().unwrap();
        let active = copy_active_rows();
        let mut dependent = [None; STATE_ONLY_HIDING_C1_COLUMNS];
        for cell in &cells {
            let row = usize::from(cell.row);
            if !active[row] {
                dependent[usize::from(cell.column)] = Some(row);
            }
        }
        for (cell, expected) in cells.into_iter().zip(expected_c1) {
            let row = usize::from(cell.row);
            if dependent[usize::from(cell.column)] == Some(row) {
                continue;
            }
            assert_eq!(
                trace.c1[usize::from(cell.column)][usize::from(cell.row)],
                expected
            );
        }
        assert!(trace
            .c1
            .iter()
            .all(|column| state_only_copy_inactive_sum_m31(column) == Some(M31::ZERO)));
        let mut h1 = vec![QM31::ZERO; STATE_ONLY_POSEIDON_TRACE_ROWS];
        apply_state_only_h1_padding_mask(&mut h1, &applied.h1_padding).unwrap();
        assert_eq!(h1, applied.h1_padding);
        assert_eq!(state_only_copy_inactive_sum_qm31(&h1), Some(QM31::ZERO));
        assert_eq!(trace.c1[0][0], M31::ZERO);
    }

    #[test]
    fn zero_entropy_and_missing_root_binding_fail_closed() {
        let context = mask_context(0xc1);
        let (binding, mut transcript) = precommit(context);
        let mut store = InMemoryStateOnlyMaskNonceStore::default();
        assert_eq!(
            build_state_only_mask_material(HOST_HASH, binding, context, [0; 32], &mut store).err(),
            Some(StateOnlyMaskBuildError::ZeroPrivateEntropy)
        );

        let trace = zero_trace();
        let mask_only_c1 =
            core::array::from_fn(|_| vec![M31::ZERO; STATE_ONLY_POSEIDON_TRACE_ROWS]);
        let g = vec![QM31::ZERO; STATE_ONLY_POSEIDON_TRACE_ROWS];
        assert_eq!(
            prove_masked_state_only_zerocheck(
                &mut transcript,
                binding,
                &trace,
                &mask_only_c1,
                &g,
                |_| Ok::<_, ()>(QM31::ZERO),
            ),
            Err(MaskedStateOnlyZerocheckError::RootsNotBound)
        );
    }

    fn snapshot(seed: u8) -> PublicAccountSnapshot {
        PublicAccountSnapshot {
            key: [seed; 32],
            owner: [seed.wrapping_add(1); 32],
            lamports: u64::from(seed) * 1_003,
            executable: seed & 1 == 1,
            rent_epoch: u64::from(seed) * 17,
            data: vec![seed; usize::from(seed % 7 + 1)],
        }
    }

    fn view() -> StateOnlyCompletePublicView {
        StateOnlyCompletePublicView {
            proof_bytes: (0..96u8).collect(),
            roots: vec![[0x11; 32], [0x22; 32]],
            openings: vec![vec![0x31; 64], vec![0x41; 16]],
            statement_values: vec![[0x51; 16], [0x61; 16]],
            program_logs: vec![b"verify-start".to_vec(), b"verify-ok".to_vec()],
            state_delta: PublicAccountDelta {
                before: Some(snapshot(1)),
                after: Some(snapshot(2)),
            },
            nullifier_delta: PublicAccountDelta {
                before: None,
                after: Some(snapshot(3)),
            },
            output_delta: PublicAccountDelta {
                before: None,
                after: Some(snapshot(4)),
            },
        }
    }

    #[test]
    fn complete_public_view_digest_has_per_category_and_position_teeth() {
        let baseline = view();
        let digest = baseline.digest(HOST_HASH);
        let encoded = baseline.canonical_bytes();
        for position in 0..encoded.len() {
            let mut mutated = encoded.clone();
            mutated[position] ^= 1;
            assert_ne!(
                HOST_HASH(&[VIEW_DOMAIN, &mutated]),
                digest,
                "position={position}"
            );
        }

        let mut proof = baseline.clone();
        proof.proof_bytes[0] ^= 1;
        assert_ne!(proof.digest(HOST_HASH), digest);
        let mut root = baseline.clone();
        root.roots[0][0] ^= 1;
        assert_ne!(root.digest(HOST_HASH), digest);
        let mut opening = baseline.clone();
        opening.openings[0][0] ^= 1;
        assert_ne!(opening.digest(HOST_HASH), digest);
        let mut statement = baseline.clone();
        statement.statement_values[0][0] ^= 1;
        assert_ne!(statement.digest(HOST_HASH), digest);
        let mut log = baseline.clone();
        log.program_logs[0][0] ^= 1;
        assert_ne!(log.digest(HOST_HASH), digest);
        let mut state = baseline.clone();
        state.state_delta.after.as_mut().unwrap().data[0] ^= 1;
        assert_ne!(state.digest(HOST_HASH), digest);
        let mut nullifier = baseline.clone();
        nullifier.nullifier_delta.after.as_mut().unwrap().lamports ^= 1;
        assert_ne!(nullifier.digest(HOST_HASH), digest);
        let mut output = baseline;
        output.output_delta.after.as_mut().unwrap().owner[0] ^= 1;
        assert_ne!(output.digest(HOST_HASH), digest);
    }
}
