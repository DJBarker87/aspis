//! Proof-facing control-flow boundary for the six tag-67 work checks.
//!
//! The deployed helpers remain in `v5_cu_probe.rs`: `require_real_v5_work`
//! and `check_and_absorb_real_v5_{batch,fold,final}_nonce`.  Pinned Aeneas
//! cannot translate their `Transcript` argument because it contains a
//! `HashFn` function pointer.  This helper therefore receives only the six
//! booleans already computed by those grinding calls.  It preserves the
//! deployed `?` ordering: a failed check returns `None` before its event is
//! emitted; a successful check emits exactly one event with the deployed
//! difficulty, label, payload discriminator, nonce, and next action.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Tag67ProofWorkStep {
    /// 0=batch, 1..=4=fold rounds 0..=3, 5=final.
    pub position: u8,
    pub bits: u8,
    pub label: u8,
    /// Fold payload prefix, or 255 for the two bare-LE64 payloads.
    pub fold_round: u8,
    pub nonce: u64,
    /// 0=gamma, 1..=4=the corresponding alpha, 5=selector then q18.
    pub next_action: u8,
}

#[inline(always)]
pub fn tag67_proof_require_real_v5_work(computed_ok: bool) -> Option<()> {
    if !computed_ok {
        return None;
    }
    Some(())
}

#[inline(always)]
pub fn tag67_proof_check_and_absorb_batch(
    computed_ok: bool,
    nonce: u64,
) -> Option<Tag67ProofWorkStep> {
    tag67_proof_require_real_v5_work(computed_ok)?;
    Some(Tag67ProofWorkStep {
        position: 0,
        bits: 37,
        label: 28,
        fold_round: 255,
        nonce,
        next_action: 0,
    })
}

#[inline(always)]
pub fn tag67_proof_check_and_absorb_fold(
    computed_ok: bool,
    round: usize,
    nonce: u64,
) -> Option<Tag67ProofWorkStep> {
    let (position, bits, next_action) = match round {
        0 => (1, 34, 1),
        1 => (2, 33, 2),
        2 => (3, 30, 3),
        3 => (4, 25, 4),
        _ => return None,
    };
    tag67_proof_require_real_v5_work(computed_ok)?;
    Some(Tag67ProofWorkStep {
        position,
        bits,
        label: 20,
        fold_round: round as u8,
        nonce,
        next_action,
    })
}

#[inline(always)]
pub fn tag67_proof_check_and_absorb_final(
    computed_ok: bool,
    nonce: u64,
) -> Option<Tag67ProofWorkStep> {
    tag67_proof_require_real_v5_work(computed_ok)?;
    Some(Tag67ProofWorkStep {
        position: 5,
        bits: 32,
        label: 5,
        fold_round: 255,
        nonce,
        next_action: 5,
    })
}

/// Exact six-position `?` chain.  Boolean and nonce order is batch, folds
/// 0--3, final, matching the deployed challenge schedule.
#[inline(always)]
pub fn tag67_proof_six_actual_steps(
    batch_ok: bool,
    fold0_ok: bool,
    fold1_ok: bool,
    fold2_ok: bool,
    fold3_ok: bool,
    final_ok: bool,
    batch_nonce: u64,
    fold0_nonce: u64,
    fold1_nonce: u64,
    fold2_nonce: u64,
    fold3_nonce: u64,
    final_nonce: u64,
) -> Option<[Tag67ProofWorkStep; 6]> {
    let batch = tag67_proof_check_and_absorb_batch(batch_ok, batch_nonce)?;
    let fold0 = tag67_proof_check_and_absorb_fold(fold0_ok, 0, fold0_nonce)?;
    let fold1 = tag67_proof_check_and_absorb_fold(fold1_ok, 1, fold1_nonce)?;
    let fold2 = tag67_proof_check_and_absorb_fold(fold2_ok, 2, fold2_nonce)?;
    let fold3 = tag67_proof_check_and_absorb_fold(fold3_ok, 3, fold3_nonce)?;
    let final_query = tag67_proof_check_and_absorb_final(final_ok, final_nonce)?;
    Some([batch, fold0, fold1, fold2, fold3, final_query])
}
