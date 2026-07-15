//! Isolated atomic payment-state transition candidate.
//!
//! This module deliberately separates economic mutation from proof selection.
//! The default instruction table remains fail-closed until profile-21 hiding
//! is complete; nondefault candidate/diagnostic builds inject the exact
//! profile-20 verifier to measure the closure. Tests pin the required ordering:
//! every account/public-input check and complete proof verification happen
//! before the first CPI or data write.

use solana_program::{
    account_info::AccountInfo,
    entrypoint::ProgramResult,
    program::{invoke, invoke_signed},
    program_error::ProgramError,
    pubkey::Pubkey,
    system_instruction, system_program,
    sysvar::{rent::Rent, Sysvar},
};

use aspis_statement::{
    atomic_payment_statement_digest_v3, decode_asset_id_canonical, decode_digest_canonical,
    AtomicPaymentStatementV3, AtomicStatementError, SpendPublic,
};

pub const ATOMIC_POOL_STATE_MAGIC: [u8; 4] = *b"ASPS";
pub const ATOMIC_POOL_STATE_VERSION: u8 = 1;
pub const ATOMIC_POOL_STATE_LEN: usize = 48;

pub const ATOMIC_NULLIFIER_MAGIC: [u8; 4] = *b"ASPN";
pub const ATOMIC_NULLIFIER_VERSION: u8 = 1;
pub const ATOMIC_NULLIFIER_MARKER_LEN: usize = 72;
pub const ATOMIC_NULLIFIER_SEED: &[u8] = b"aspis-nullifier-v1";
pub const PROOF_ACCOUNT_CLOSED_MAGIC: [u8; 4] = *b"ASPC";

pub const ATOMIC_ERROR_ANCHOR_MISMATCH: u32 = 0x4153_1001;
pub const ATOMIC_ERROR_NULLIFIER_ALREADY_SPENT: u32 = 0x4153_1002;
pub const ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED: u32 = 0x4153_1003;
pub const ATOMIC_ERROR_OUTPUT_INSERTION_MISMATCH: u32 = 0x4153_1004;

const POOL_SEQUENCE_OFFSET: usize = 8;
const POOL_ANCHOR_OFFSET: usize = 16;
const NULLIFIER_POOL_OFFSET: usize = 8;
const NULLIFIER_VALUE_OFFSET: usize = 40;

/// The exact public state transition that the future state-only proof must
/// bind. `current_anchor` is checked against the writable pool account and
/// `output_anchor` becomes its next root only after proof verification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AtomicPaymentPublicInputs {
    pub current_anchor: [u8; 32],
    pub nullifier: [u8; 32],
    pub output_commitment: [u8; 32],
    pub output_anchor: [u8; 32],
    pub asset_id: u32,
    pub fee: u32,
}

fn sbf_sha256(inputs: &[&[u8]]) -> [u8; 32] {
    solana_program::hash::hashv(inputs).to_bytes()
}

fn map_statement_error(error: AtomicStatementError) -> ProgramError {
    match error {
        AtomicStatementError::CurrentAnchorMismatch
        | AtomicStatementError::OutputAnchorMismatch
        | AtomicStatementError::PathDepthMismatch
        | AtomicStatementError::InsertionIndexOutOfRange => {
            ProgramError::Custom(ATOMIC_ERROR_OUTPUT_INSERTION_MISMATCH)
        }
        AtomicStatementError::NonCanonicalDigest
        | AtomicStatementError::NonCanonicalAssetId
        | AtomicStatementError::FeeOutOfRange => ProgramError::InvalidInstructionData,
    }
}

fn checked_statement(
    pool_key: &Pubkey,
    sequence: u64,
    public: &AtomicPaymentPublicInputs,
) -> Result<(AtomicPaymentStatementV3, [u8; 32]), ProgramError> {
    let current_anchor =
        decode_digest_canonical(&public.current_anchor).map_err(map_statement_error)?;
    let nullifier = decode_digest_canonical(&public.nullifier).map_err(map_statement_error)?;
    let output_commitment =
        decode_digest_canonical(&public.output_commitment).map_err(map_statement_error)?;
    let output_anchor =
        decode_digest_canonical(&public.output_anchor).map_err(map_statement_error)?;
    let asset_id = decode_asset_id_canonical(public.asset_id).map_err(map_statement_error)?;
    let statement = AtomicPaymentStatementV3 {
        pool: pool_key.to_bytes(),
        sequence,
        spend: SpendPublic {
            anchor: current_anchor,
            nullifier,
            output_commitment,
            asset_id,
            fee: public.fee,
        },
        output_anchor,
    };
    let digest =
        atomic_payment_statement_digest_v3(&statement, sbf_sha256).map_err(map_statement_error)?;
    Ok((statement, digest))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AtomicPoolStateV1 {
    pub sequence: u64,
    pub anchor: [u8; 32],
}

impl AtomicPoolStateV1 {
    pub fn decode(data: &[u8]) -> Result<Self, ProgramError> {
        if data.len() != ATOMIC_POOL_STATE_LEN
            || data[0..4] != ATOMIC_POOL_STATE_MAGIC
            || data[4] != ATOMIC_POOL_STATE_VERSION
            || data[5..8] != [0u8; 3]
        {
            return Err(ProgramError::InvalidAccountData);
        }
        Ok(Self {
            sequence: u64::from_le_bytes(
                data[POOL_SEQUENCE_OFFSET..POOL_ANCHOR_OFFSET]
                    .try_into()
                    .unwrap(),
            ),
            anchor: data[POOL_ANCHOR_OFFSET..ATOMIC_POOL_STATE_LEN]
                .try_into()
                .unwrap(),
        })
    }

    pub fn encode(self, data: &mut [u8]) -> ProgramResult {
        if data.len() != ATOMIC_POOL_STATE_LEN {
            return Err(ProgramError::InvalidAccountData);
        }
        data.fill(0);
        data[0..4].copy_from_slice(&ATOMIC_POOL_STATE_MAGIC);
        data[4] = ATOMIC_POOL_STATE_VERSION;
        data[POOL_SEQUENCE_OFFSET..POOL_ANCHOR_OFFSET]
            .copy_from_slice(&self.sequence.to_le_bytes());
        data[POOL_ANCHOR_OFFSET..ATOMIC_POOL_STATE_LEN].copy_from_slice(&self.anchor);
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct NullifierMarkerV1 {
    pool: Pubkey,
    nullifier: [u8; 32],
}

impl NullifierMarkerV1 {
    fn decode(data: &[u8]) -> Result<Option<Self>, ProgramError> {
        if data.len() != ATOMIC_NULLIFIER_MARKER_LEN {
            return Err(ProgramError::InvalidAccountData);
        }
        if data.iter().all(|byte| *byte == 0) {
            return Ok(None);
        }
        if data[0..4] != ATOMIC_NULLIFIER_MAGIC
            || data[4] != ATOMIC_NULLIFIER_VERSION
            || data[5..8] != [0u8; 3]
        {
            return Err(ProgramError::InvalidAccountData);
        }
        Ok(Some(Self {
            pool: Pubkey::new_from_array(
                data[NULLIFIER_POOL_OFFSET..NULLIFIER_VALUE_OFFSET]
                    .try_into()
                    .unwrap(),
            ),
            nullifier: data[NULLIFIER_VALUE_OFFSET..ATOMIC_NULLIFIER_MARKER_LEN]
                .try_into()
                .unwrap(),
        }))
    }

    fn encode(self, data: &mut [u8]) -> ProgramResult {
        if data.len() != ATOMIC_NULLIFIER_MARKER_LEN {
            return Err(ProgramError::InvalidAccountData);
        }
        data.fill(0);
        data[0..4].copy_from_slice(&ATOMIC_NULLIFIER_MAGIC);
        data[4] = ATOMIC_NULLIFIER_VERSION;
        data[NULLIFIER_POOL_OFFSET..NULLIFIER_VALUE_OFFSET].copy_from_slice(self.pool.as_ref());
        data[NULLIFIER_VALUE_OFFSET..ATOMIC_NULLIFIER_MARKER_LEN].copy_from_slice(&self.nullifier);
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MarkerPreparation {
    ProgramOwnedZeroed,
    CreateSystemOwned,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ProofAccountDisposition {
    Retain,
    RefundToPayer,
}

/// CU/account-transition boundaries for the exact atomic mutation kernel.
/// The production wrapper supplies a no-op callback; the callback is exposed
/// so a feature-gated diagnostic SBF build can price the same ordering without
/// adding logging syscalls to the production instruction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AtomicPaymentTransitionTraceEvent {
    AccountsValidatedProgramOwned,
    AccountsValidatedSystemOwned,
    StatementDigestDone,
    ProofVerified,
    ProgramOwnedMarkerReady,
    SystemOwnedMarkerCreated,
    MutableStateRechecked,
    StateApplied,
}

pub fn atomic_nullifier_address(program_id: &Pubkey, nullifier: &[u8; 32]) -> (Pubkey, u8) {
    Pubkey::find_program_address(&[ATOMIC_NULLIFIER_SEED, nullifier], program_id)
}

fn validate_accounts_and_state(
    program_id: &Pubkey,
    proof_account: &AccountInfo,
    pool_account: &AccountInfo,
    nullifier_account: &AccountInfo,
    payer: &AccountInfo,
    system_program_account: &AccountInfo,
    public: &AtomicPaymentPublicInputs,
    proof_disposition: ProofAccountDisposition,
) -> Result<(AtomicPoolStateV1, u8, MarkerPreparation), ProgramError> {
    if proof_account.owner != program_id || pool_account.owner != program_id {
        return Err(ProgramError::IncorrectProgramId);
    }
    if proof_disposition == ProofAccountDisposition::RefundToPayer && !proof_account.is_signer {
        return Err(ProgramError::MissingRequiredSignature);
    }
    let proof_access_invalid = match proof_disposition {
        ProofAccountDisposition::Retain => proof_account.is_writable,
        ProofAccountDisposition::RefundToPayer => !proof_account.is_writable,
    };
    if proof_access_invalid
        || !pool_account.is_writable
        || !nullifier_account.is_writable
        || !payer.is_writable
    {
        return Err(ProgramError::InvalidAccountData);
    }
    if !payer.is_signer {
        return Err(ProgramError::MissingRequiredSignature);
    }
    if payer.owner != &system_program::id()
        || system_program_account.key != &system_program::id()
        || !system_program_account.executable
    {
        return Err(ProgramError::IncorrectProgramId);
    }
    if proof_account.key == pool_account.key
        || proof_account.key == nullifier_account.key
        || proof_account.key == payer.key
        || pool_account.key == nullifier_account.key
        || payer.key == pool_account.key
        || payer.key == nullifier_account.key
    {
        return Err(ProgramError::InvalidArgument);
    }

    let (expected_nullifier, bump) = atomic_nullifier_address(program_id, &public.nullifier);
    if nullifier_account.key != &expected_nullifier {
        return Err(ProgramError::InvalidSeeds);
    }

    let pool = AtomicPoolStateV1::decode(&pool_account.try_borrow_data()?)?;
    if pool.anchor != public.current_anchor {
        return Err(ProgramError::Custom(ATOMIC_ERROR_ANCHOR_MISMATCH));
    }
    pool.sequence
        .checked_add(1)
        .ok_or(ProgramError::ArithmeticOverflow)?;

    let preparation = if nullifier_account.owner == program_id {
        match NullifierMarkerV1::decode(&nullifier_account.try_borrow_data()?)? {
            None => MarkerPreparation::ProgramOwnedZeroed,
            Some(marker) if marker.nullifier == public.nullifier => {
                return Err(ProgramError::Custom(ATOMIC_ERROR_NULLIFIER_ALREADY_SPENT));
            }
            Some(_) => return Err(ProgramError::InvalidAccountData),
        }
    } else if nullifier_account.owner == &system_program::id() && nullifier_account.data_is_empty()
    {
        MarkerPreparation::CreateSystemOwned
    } else {
        return Err(ProgramError::IncorrectProgramId);
    };

    Ok((pool, bump, preparation))
}

/// Drain a program-owned proof account into its signer-selected System
/// account. A zero-lamport account is purged by the runtime at transaction
/// commit. Requiring the proof account itself to sign prevents a third party
/// from stealing the refundable rent after the upload authority is erased.
pub fn refund_program_owned_proof_account(
    program_id: &Pubkey,
    proof_account: &AccountInfo,
    refund_account: &AccountInfo,
) -> ProgramResult {
    if proof_account.owner != program_id {
        return Err(ProgramError::IncorrectProgramId);
    }
    if !proof_account.is_signer || !refund_account.is_signer {
        return Err(ProgramError::MissingRequiredSignature);
    }
    if !proof_account.is_writable || !refund_account.is_writable {
        return Err(ProgramError::InvalidAccountData);
    }
    if proof_account.key == refund_account.key {
        return Err(ProgramError::InvalidArgument);
    }
    if refund_account.owner != &system_program::id() {
        return Err(ProgramError::IncorrectProgramId);
    }

    let refundable = proof_account.lamports();
    if refundable == 0 {
        return Err(ProgramError::InvalidAccountData);
    }
    let refunded_balance = refund_account
        .lamports()
        .checked_add(refundable)
        .ok_or(ProgramError::ArithmeticOverflow)?;
    let mut proof_data = proof_account.try_borrow_mut_data()?;
    if proof_data.len() < 4 {
        return Err(ProgramError::InvalidAccountData);
    }
    let mut proof_lamports = proof_account.try_borrow_mut_lamports()?;
    let mut refund_lamports = refund_account.try_borrow_mut_lamports()?;
    // Invalidate the account before draining it so a later instruction in the
    // same transaction cannot revive a valid sealed proof merely by crediting
    // lamports back to this address.
    proof_data[..4].copy_from_slice(&PROOF_ACCOUNT_CLOSED_MAGIC);
    **refund_lamports = refunded_balance;
    **proof_lamports = 0;
    Ok(())
}

fn create_nullifier_marker<'a>(
    program_id: &Pubkey,
    pool_account: &AccountInfo<'a>,
    nullifier_account: &AccountInfo<'a>,
    payer: &AccountInfo<'a>,
    system_program_account: &AccountInfo<'a>,
    public: &AtomicPaymentPublicInputs,
    bump: u8,
) -> ProgramResult {
    let rent = Rent::get()?;
    let required_lamports = rent.minimum_balance(ATOMIC_NULLIFIER_MARKER_LEN).max(1);
    let bump_seed = [bump];
    let nullifier_seeds: &[&[u8]] = &[ATOMIC_NULLIFIER_SEED, public.nullifier.as_ref(), &bump_seed];
    let signer_seeds = &[nullifier_seeds];
    let account_infos = [
        payer.clone(),
        nullifier_account.clone(),
        system_program_account.clone(),
    ];

    if nullifier_account.lamports() == 0 {
        invoke_signed(
            &system_instruction::create_account(
                payer.key,
                nullifier_account.key,
                required_lamports,
                ATOMIC_NULLIFIER_MARKER_LEN as u64,
                program_id,
            ),
            &account_infos,
            signer_seeds,
        )?;
    } else {
        let deficit = required_lamports.saturating_sub(nullifier_account.lamports());
        if deficit != 0 {
            invoke(
                &system_instruction::transfer(payer.key, nullifier_account.key, deficit),
                &account_infos,
            )?;
        }
        invoke_signed(
            &system_instruction::allocate(
                nullifier_account.key,
                ATOMIC_NULLIFIER_MARKER_LEN as u64,
            ),
            &account_infos,
            signer_seeds,
        )?;
        invoke_signed(
            &system_instruction::assign(nullifier_account.key, program_id),
            &account_infos,
            signer_seeds,
        )?;
    }

    // `pool_account` is intentionally included in the transition API but is
    // not an account meta of the System Program CPI. Keeping this explicit
    // prevents a future refactor from treating the pool as a CPI authority.
    let _ = pool_account;
    Ok(())
}

/// Validate exact accounts/public inputs, run the complete supplied verifier,
/// and atomically consume the nullifier and advance the pool root.
///
/// Account order is fixed:
///
/// 0. read-only proof account, owned by this program;
/// 1. writable v1 pool-state account, owned by this program;
/// 2. writable canonical nullifier PDA;
/// 3. writable signer funding a missing marker PDA;
/// 4. canonical System Program.
///
/// The verifier closure must bind `public` into the proof transcript. No CPI
/// or account write occurs before it returns success. Solana writable locking
/// on both the pool and canonical nullifier PDA serializes concurrent spends;
/// after the first transaction commits, a duplicate observes the marker and
/// rejects.
pub fn verify_and_apply_atomic_payment_state<'a, F>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'a>],
    public: &AtomicPaymentPublicInputs,
    verify_complete_proof: F,
) -> ProgramResult
where
    F: FnOnce(&AccountInfo<'a>, &AtomicPaymentStatementV3, &[u8; 32]) -> ProgramResult,
{
    verify_and_apply_atomic_payment_state_traced(
        program_id,
        accounts,
        public,
        verify_complete_proof,
        |_| {},
    )
}

/// Profile23 production form of [`verify_and_apply_atomic_payment_state`].
/// Account 0 must additionally be writable and sign the transaction. After
/// proof verification and every mutable-state recheck succeed, its complete
/// lamport balance is atomically refunded to account 3.
pub fn verify_and_apply_atomic_payment_state_with_proof_refund<'a, F>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'a>],
    public: &AtomicPaymentPublicInputs,
    verify_complete_proof: F,
) -> ProgramResult
where
    F: FnOnce(&AccountInfo<'a>, &AtomicPaymentStatementV3, &[u8; 32]) -> ProgramResult,
{
    verify_and_apply_atomic_payment_state_traced_inner(
        program_id,
        accounts,
        public,
        verify_complete_proof,
        ProofAccountDisposition::RefundToPayer,
        |_| {},
    )
}

/// The traced form of [`verify_and_apply_atomic_payment_state`].  It executes
/// the identical validation, statement, proof, CPI, recheck, and final-copy
/// path. Trace callbacks are observational only and return no error.
pub fn verify_and_apply_atomic_payment_state_traced<'a, F, T>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'a>],
    public: &AtomicPaymentPublicInputs,
    verify_complete_proof: F,
    trace: T,
) -> ProgramResult
where
    F: FnOnce(&AccountInfo<'a>, &AtomicPaymentStatementV3, &[u8; 32]) -> ProgramResult,
    T: FnMut(AtomicPaymentTransitionTraceEvent),
{
    verify_and_apply_atomic_payment_state_traced_inner(
        program_id,
        accounts,
        public,
        verify_complete_proof,
        ProofAccountDisposition::Retain,
        trace,
    )
}

/// Traced counterpart of
/// [`verify_and_apply_atomic_payment_state_with_proof_refund`].
pub fn verify_and_apply_atomic_payment_state_traced_with_proof_refund<'a, F, T>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'a>],
    public: &AtomicPaymentPublicInputs,
    verify_complete_proof: F,
    trace: T,
) -> ProgramResult
where
    F: FnOnce(&AccountInfo<'a>, &AtomicPaymentStatementV3, &[u8; 32]) -> ProgramResult,
    T: FnMut(AtomicPaymentTransitionTraceEvent),
{
    verify_and_apply_atomic_payment_state_traced_inner(
        program_id,
        accounts,
        public,
        verify_complete_proof,
        ProofAccountDisposition::RefundToPayer,
        trace,
    )
}

fn verify_and_apply_atomic_payment_state_traced_inner<'a, F, T>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'a>],
    public: &AtomicPaymentPublicInputs,
    verify_complete_proof: F,
    proof_disposition: ProofAccountDisposition,
    mut trace: T,
) -> ProgramResult
where
    F: FnOnce(&AccountInfo<'a>, &AtomicPaymentStatementV3, &[u8; 32]) -> ProgramResult,
    T: FnMut(AtomicPaymentTransitionTraceEvent),
{
    if accounts.len() != 5 {
        return Err(ProgramError::NotEnoughAccountKeys);
    }
    let proof_account = &accounts[0];
    let pool_account = &accounts[1];
    let nullifier_account = &accounts[2];
    let payer = &accounts[3];
    let system_program_account = &accounts[4];

    let (pool, bump, preparation) = validate_accounts_and_state(
        program_id,
        proof_account,
        pool_account,
        nullifier_account,
        payer,
        system_program_account,
        public,
        proof_disposition,
    )?;
    trace(match preparation {
        MarkerPreparation::ProgramOwnedZeroed => {
            AtomicPaymentTransitionTraceEvent::AccountsValidatedProgramOwned
        }
        MarkerPreparation::CreateSystemOwned => {
            AtomicPaymentTransitionTraceEvent::AccountsValidatedSystemOwned
        }
    });

    // Sequence is replay/concurrency metadata, not a public leaf index. The
    // v3 proof must show that the input and output roots use the same private
    // path and index under the fixed node compression.
    let (statement, statement_digest) = checked_statement(pool_account.key, pool.sequence, public)?;
    trace(AtomicPaymentTransitionTraceEvent::StatementDigestDone);

    // Load-bearing ordering rule: this must remain before marker creation and
    // before either mutable borrow below.
    // The proof verifier must evaluate the exact `statement.spend`, constrain
    // `statement.output_anchor` by the same-path replacement relation, and
    // absorb exactly `statement_digest`; the digest alone is insufficient.
    verify_complete_proof(proof_account, &statement, &statement_digest)?;
    trace(AtomicPaymentTransitionTraceEvent::ProofVerified);

    if preparation == MarkerPreparation::CreateSystemOwned {
        create_nullifier_marker(
            program_id,
            pool_account,
            nullifier_account,
            payer,
            system_program_account,
            public,
            bump,
        )?;
        trace(AtomicPaymentTransitionTraceEvent::SystemOwnedMarkerCreated);
    } else {
        trace(AtomicPaymentTransitionTraceEvent::ProgramOwnedMarkerReady);
    }

    // Acquire every fallible mutable borrow and recheck the preconditions
    // before copying either final image. After the first copy, no operation
    // can fail, which also keeps direct host tests mutation-atomic.
    let mut pool_data = pool_account.try_borrow_mut_data()?;
    let mut nullifier_data = nullifier_account.try_borrow_mut_data()?;
    let observed_pool = AtomicPoolStateV1::decode(&pool_data)?;
    if observed_pool != pool || observed_pool.anchor != public.current_anchor {
        return Err(ProgramError::Custom(ATOMIC_ERROR_ANCHOR_MISMATCH));
    }
    if NullifierMarkerV1::decode(&nullifier_data)?.is_some() {
        return Err(ProgramError::Custom(ATOMIC_ERROR_NULLIFIER_ALREADY_SPENT));
    }
    trace(AtomicPaymentTransitionTraceEvent::MutableStateRechecked);

    let next_pool = AtomicPoolStateV1 {
        sequence: pool.sequence + 1,
        anchor: public.output_anchor,
    };
    let marker = NullifierMarkerV1 {
        pool: *pool_account.key,
        nullifier: public.nullifier,
    };
    let mut next_pool_bytes = [0u8; ATOMIC_POOL_STATE_LEN];
    let mut marker_bytes = [0u8; ATOMIC_NULLIFIER_MARKER_LEN];
    next_pool.encode(&mut next_pool_bytes)?;
    marker.encode(&mut marker_bytes)?;

    if proof_disposition == ProofAccountDisposition::RefundToPayer {
        // This is the final fallible operation. Once the refund succeeds, the
        // two fixed-size state copies below cannot fail, preserving direct-test
        // and transaction-level atomicity.
        refund_program_owned_proof_account(program_id, proof_account, payer)?;
    }
    nullifier_data.copy_from_slice(&marker_bytes);
    pool_data.copy_from_slice(&next_pool_bytes);
    trace(AtomicPaymentTransitionTraceEvent::StateApplied);
    Ok(())
}

/// Safe placeholder retained by append-only tag 38. Final profile-21
/// integration uses the real closure above through a new append-only tag.
pub fn verifier_not_integrated(
    _proof_account: &AccountInfo,
    _statement: &AtomicPaymentStatementV3,
    _statement_digest: &[u8; 32],
) -> ProgramResult {
    Err(ProgramError::Custom(ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED))
}

#[cfg(test)]
mod tests {
    use core::cell::{Cell, RefCell};

    use solana_program::{account_info::AccountInfo, clock::Epoch};

    use super::*;

    fn make_account<'a>(
        key: &'a Pubkey,
        owner: &'a Pubkey,
        lamports: &'a mut u64,
        data: &'a mut [u8],
        is_signer: bool,
        is_writable: bool,
        executable: bool,
    ) -> AccountInfo<'a> {
        AccountInfo::new(
            key,
            is_signer,
            is_writable,
            lamports,
            data,
            owner,
            executable,
            Epoch::default(),
        )
    }

    fn digest(seed: u32) -> aspis_statement::Digest {
        core::array::from_fn(|index| aspis_core::field::M31(seed + index as u32 * 17))
    }

    fn valid_public(nullifier_seed: u32, output_seed: u32) -> AtomicPaymentPublicInputs {
        let siblings: [aspis_statement::Digest; aspis_statement::ATOMIC_PAYMENT_TREE_DEPTH] =
            core::array::from_fn(|index| digest(1_000 + index as u32 * 37));
        let index = 0x5a5a5u32;
        let output_commitment = digest(output_seed);
        let root = |mut leaf: aspis_statement::Digest| {
            for (level, sibling) in siblings.iter().enumerate() {
                leaf = if (index >> level) & 1 == 0 {
                    aspis_statement::merkle_node_compress_v3(&leaf, sibling)
                } else {
                    aspis_statement::merkle_node_compress_v3(sibling, &leaf)
                };
            }
            leaf
        };
        let current_anchor = root(digest(output_seed + 10_000));
        let output_anchor = root(output_commitment);
        AtomicPaymentPublicInputs {
            current_anchor: aspis_statement::encode_digest_canonical(&current_anchor),
            nullifier: aspis_statement::encode_digest_canonical(&digest(nullifier_seed)),
            output_commitment: aspis_statement::encode_digest_canonical(&output_commitment),
            output_anchor: aspis_statement::encode_digest_canonical(&output_anchor),
            asset_id: 17,
            fee: 1,
        }
    }

    struct Fixture {
        program_id: Pubkey,
        proof_key: Pubkey,
        pool_key: Pubkey,
        nullifier_key: Pubkey,
        payer_key: Pubkey,
        system_key: Pubkey,
        system_owner: Pubkey,
        proof_lamports: u64,
        pool_lamports: u64,
        nullifier_lamports: u64,
        payer_lamports: u64,
        system_lamports: u64,
        proof_data: [u8; 8],
        pool_data: [u8; ATOMIC_POOL_STATE_LEN],
        nullifier_data: [u8; ATOMIC_NULLIFIER_MARKER_LEN],
        payer_data: [u8; 0],
        system_data: [u8; 0],
    }

    impl Fixture {
        fn new(public: &AtomicPaymentPublicInputs, stored_anchor: [u8; 32]) -> Self {
            let program_id = crate::id();
            let (nullifier_key, _) = atomic_nullifier_address(&program_id, &public.nullifier);
            let mut pool_data = [0u8; ATOMIC_POOL_STATE_LEN];
            AtomicPoolStateV1 {
                sequence: 0,
                anchor: stored_anchor,
            }
            .encode(&mut pool_data)
            .unwrap();
            Self {
                program_id,
                proof_key: Pubkey::new_unique(),
                pool_key: Pubkey::new_unique(),
                nullifier_key,
                payer_key: Pubkey::new_unique(),
                system_key: system_program::id(),
                system_owner: Pubkey::new_unique(),
                proof_lamports: 1,
                pool_lamports: 1,
                nullifier_lamports: 1,
                payer_lamports: 1,
                system_lamports: 1,
                proof_data: [0x55; 8],
                pool_data,
                nullifier_data: [0u8; ATOMIC_NULLIFIER_MARKER_LEN],
                payer_data: [],
                system_data: [],
            }
        }

        fn accounts(&mut self) -> Vec<AccountInfo<'_>> {
            self.accounts_with_proof_access(false, false)
        }

        fn refund_accounts(&mut self) -> Vec<AccountInfo<'_>> {
            self.accounts_with_proof_access(true, true)
        }

        fn accounts_with_proof_access(
            &mut self,
            proof_is_signer: bool,
            proof_is_writable: bool,
        ) -> Vec<AccountInfo<'_>> {
            vec![
                make_account(
                    &self.proof_key,
                    &self.program_id,
                    &mut self.proof_lamports,
                    &mut self.proof_data,
                    proof_is_signer,
                    proof_is_writable,
                    false,
                ),
                make_account(
                    &self.pool_key,
                    &self.program_id,
                    &mut self.pool_lamports,
                    &mut self.pool_data,
                    false,
                    true,
                    false,
                ),
                make_account(
                    &self.nullifier_key,
                    &self.program_id,
                    &mut self.nullifier_lamports,
                    &mut self.nullifier_data,
                    false,
                    true,
                    false,
                ),
                make_account(
                    &self.payer_key,
                    &self.system_key,
                    &mut self.payer_lamports,
                    &mut self.payer_data,
                    true,
                    true,
                    false,
                ),
                make_account(
                    &self.system_key,
                    &self.system_owner,
                    &mut self.system_lamports,
                    &mut self.system_data,
                    false,
                    false,
                    true,
                ),
            ]
        }

        fn apply<F>(&mut self, public: &AtomicPaymentPublicInputs, verify: F) -> ProgramResult
        where
            F: FnOnce(&AccountInfo, &AtomicPaymentStatementV3, &[u8; 32]) -> ProgramResult,
        {
            let program_id = self.program_id;
            let accounts = self.accounts();
            verify_and_apply_atomic_payment_state(&program_id, &accounts, public, verify)
        }

        fn apply_with_refund<F>(
            &mut self,
            public: &AtomicPaymentPublicInputs,
            verify: F,
        ) -> ProgramResult
        where
            F: FnOnce(&AccountInfo, &AtomicPaymentStatementV3, &[u8; 32]) -> ProgramResult,
        {
            let program_id = self.program_id;
            let accounts = self.refund_accounts();
            verify_and_apply_atomic_payment_state_with_proof_refund(
                &program_id,
                &accounts,
                public,
                verify,
            )
        }
    }

    #[test]
    fn exact_v1_account_layouts_are_pinned() {
        let anchor = [7u8; 32];
        let mut pool = [0u8; ATOMIC_POOL_STATE_LEN];
        AtomicPoolStateV1 {
            sequence: 9,
            anchor,
        }
        .encode(&mut pool)
        .unwrap();
        assert_eq!(&pool[0..4], &ATOMIC_POOL_STATE_MAGIC);
        assert_eq!(pool[4], ATOMIC_POOL_STATE_VERSION);
        assert_eq!(&pool[5..8], &[0u8; 3]);
        assert_eq!(
            AtomicPoolStateV1::decode(&pool).unwrap(),
            AtomicPoolStateV1 {
                sequence: 9,
                anchor,
            }
        );

        let pool_key = Pubkey::new_unique();
        let nullifier = [9u8; 32];
        let mut marker = [0u8; ATOMIC_NULLIFIER_MARKER_LEN];
        let expected = NullifierMarkerV1 {
            pool: pool_key,
            nullifier,
        };
        expected.encode(&mut marker).unwrap();
        assert_eq!(&marker[0..4], &ATOMIC_NULLIFIER_MAGIC);
        assert_eq!(marker[4], ATOMIC_NULLIFIER_VERSION);
        assert_eq!(&marker[5..8], &[0u8; 3]);
        assert_eq!(NullifierMarkerV1::decode(&marker).unwrap(), Some(expected));
    }

    #[test]
    fn invalid_proof_leaves_pool_and_nullifier_unchanged() {
        let public = valid_public(200, 300);
        let mut fixture = Fixture::new(&public, public.current_anchor);
        let pool_before = fixture.pool_data;
        let marker_before = fixture.nullifier_data;
        let proof_lamports_before = fixture.proof_lamports;
        let payer_lamports_before = fixture.payer_lamports;
        let verifier_called = Cell::new(false);
        assert_eq!(
            fixture.apply(&public, |_, statement, digest| {
                verifier_called.set(true);
                assert_eq!(
                    statement.spend.anchor,
                    decode_digest_canonical(&public.current_anchor).unwrap()
                );
                assert_eq!(
                    statement.spend.nullifier,
                    decode_digest_canonical(&public.nullifier).unwrap()
                );
                assert_eq!(
                    statement.spend.output_commitment,
                    decode_digest_canonical(&public.output_commitment).unwrap()
                );
                assert_eq!(statement.spend.asset_id.0, public.asset_id);
                assert_eq!(statement.spend.fee, public.fee);
                assert_eq!(
                    atomic_payment_statement_digest_v3(statement, sbf_sha256).unwrap(),
                    *digest
                );
                Err(ProgramError::InvalidInstructionData)
            }),
            Err(ProgramError::InvalidInstructionData)
        );
        assert!(verifier_called.get());
        assert_eq!(fixture.pool_data, pool_before);
        assert_eq!(fixture.nullifier_data, marker_before);
        assert_eq!(fixture.proof_lamports, proof_lamports_before);
        assert_eq!(fixture.payer_lamports, payer_lamports_before);
    }

    #[test]
    fn successful_transition_consumes_once_and_duplicate_rejects_before_verifier() {
        let first = valid_public(400, 500);
        let mut fixture = Fixture::new(&first, first.current_anchor);
        let expected_pool = fixture.pool_key.to_bytes();
        assert_eq!(
            fixture.apply(&first, |_, statement, digest| {
                assert_eq!(statement.pool, expected_pool);
                assert_eq!(statement.sequence, 0);
                assert_eq!(
                    atomic_payment_statement_digest_v3(statement, sbf_sha256).unwrap(),
                    *digest
                );
                Ok(())
            }),
            Ok(())
        );
        assert_eq!(
            AtomicPoolStateV1::decode(&fixture.pool_data).unwrap(),
            AtomicPoolStateV1 {
                sequence: 1,
                anchor: first.output_anchor,
            }
        );
        assert_eq!(
            NullifierMarkerV1::decode(&fixture.nullifier_data).unwrap(),
            Some(NullifierMarkerV1 {
                pool: fixture.pool_key,
                nullifier: first.nullifier,
            })
        );
        let pool_after_first = fixture.pool_data;
        let marker_after_first = fixture.nullifier_data;

        let mut duplicate = first;
        duplicate.current_anchor = duplicate.output_anchor;
        let verifier_called = Cell::new(false);
        assert_eq!(
            fixture.apply(&duplicate, |_, _, _| {
                verifier_called.set(true);
                Ok(())
            }),
            Err(ProgramError::Custom(ATOMIC_ERROR_NULLIFIER_ALREADY_SPENT))
        );
        assert!(!verifier_called.get());
        assert_eq!(fixture.pool_data, pool_after_first);
        assert_eq!(fixture.nullifier_data, marker_after_first);
    }

    #[test]
    fn successful_profile23_transition_refunds_and_tombstones_proof() {
        let public = valid_public(425, 525);
        let mut fixture = Fixture::new(&public, public.current_anchor);
        fixture.proof_lamports = 463_083_600;
        fixture.payer_lamports = 10_000;
        let refundable = fixture.proof_lamports;
        let payer_before = fixture.payer_lamports;

        assert_eq!(fixture.apply_with_refund(&public, |_, _, _| Ok(())), Ok(()));
        assert_eq!(fixture.proof_lamports, 0);
        assert_eq!(fixture.payer_lamports, payer_before + refundable);
        assert_eq!(
            fixture.proof_data[..4],
            PROOF_ACCOUNT_CLOSED_MAGIC,
            "closed proof must retain a nonzero tombstone"
        );
        assert_eq!(
            AtomicPoolStateV1::decode(&fixture.pool_data)
                .unwrap()
                .sequence,
            1
        );
        assert!(NullifierMarkerV1::decode(&fixture.nullifier_data)
            .unwrap()
            .is_some());
    }

    #[test]
    fn failed_profile23_transition_preserves_proof_and_refund_balances() {
        let public = valid_public(430, 530);
        let mut fixture = Fixture::new(&public, public.current_anchor);
        let proof_before = fixture.proof_data;
        let pool_before = fixture.pool_data;
        let marker_before = fixture.nullifier_data;
        let proof_lamports_before = fixture.proof_lamports;
        let payer_lamports_before = fixture.payer_lamports;

        assert_eq!(
            fixture.apply_with_refund(&public, |_, _, _| {
                Err(ProgramError::InvalidInstructionData)
            }),
            Err(ProgramError::InvalidInstructionData)
        );
        assert_eq!(fixture.proof_data, proof_before);
        assert_eq!(fixture.pool_data, pool_before);
        assert_eq!(fixture.nullifier_data, marker_before);
        assert_eq!(fixture.proof_lamports, proof_lamports_before);
        assert_eq!(fixture.payer_lamports, payer_lamports_before);
    }

    #[test]
    fn profile23_refund_requires_writable_proof_signer_and_checked_balance() {
        let public = valid_public(435, 535);

        let mut unsigned = Fixture::new(&public, public.current_anchor);
        let unsigned_program = unsigned.program_id;
        let unsigned_accounts = unsigned.accounts_with_proof_access(false, true);
        assert_eq!(
            verify_and_apply_atomic_payment_state_with_proof_refund(
                &unsigned_program,
                &unsigned_accounts,
                &public,
                |_, _, _| Ok(())
            ),
            Err(ProgramError::MissingRequiredSignature)
        );

        let mut readonly = Fixture::new(&public, public.current_anchor);
        let readonly_program = readonly.program_id;
        let readonly_accounts = readonly.accounts_with_proof_access(true, false);
        assert_eq!(
            verify_and_apply_atomic_payment_state_with_proof_refund(
                &readonly_program,
                &readonly_accounts,
                &public,
                |_, _, _| Ok(())
            ),
            Err(ProgramError::InvalidAccountData)
        );

        let mut overflow = Fixture::new(&public, public.current_anchor);
        overflow.payer_lamports = u64::MAX;
        let proof_before = overflow.proof_data;
        let pool_before = overflow.pool_data;
        let marker_before = overflow.nullifier_data;
        let proof_lamports_before = overflow.proof_lamports;
        let overflow_program = overflow.program_id;
        let overflow_accounts = overflow.refund_accounts();
        assert_eq!(
            verify_and_apply_atomic_payment_state_with_proof_refund(
                &overflow_program,
                &overflow_accounts,
                &public,
                |_, _, _| Ok(())
            ),
            Err(ProgramError::ArithmeticOverflow)
        );
        drop(overflow_accounts);
        assert_eq!(overflow.proof_data, proof_before);
        assert_eq!(overflow.pool_data, pool_before);
        assert_eq!(overflow.nullifier_data, marker_before);
        assert_eq!(overflow.proof_lamports, proof_lamports_before);
        assert_eq!(overflow.payer_lamports, u64::MAX);
    }

    #[test]
    fn traced_program_owned_transition_pins_validation_digest_verify_and_write_order() {
        let public = valid_public(450, 550);
        let mut fixture = Fixture::new(&public, public.current_anchor);
        let program_id = fixture.program_id;
        let events = RefCell::new(Vec::new());
        let accounts = fixture.accounts();
        assert_eq!(
            verify_and_apply_atomic_payment_state_traced(
                &program_id,
                &accounts,
                &public,
                |_, _, _| Ok(()),
                |event| events.borrow_mut().push(event),
            ),
            Ok(())
        );
        assert_eq!(
            events.into_inner(),
            vec![
                AtomicPaymentTransitionTraceEvent::AccountsValidatedProgramOwned,
                AtomicPaymentTransitionTraceEvent::StatementDigestDone,
                AtomicPaymentTransitionTraceEvent::ProofVerified,
                AtomicPaymentTransitionTraceEvent::ProgramOwnedMarkerReady,
                AtomicPaymentTransitionTraceEvent::MutableStateRechecked,
                AtomicPaymentTransitionTraceEvent::StateApplied,
            ]
        );
    }

    #[test]
    fn anchor_mismatch_rejects_without_verification_or_mutation() {
        let public = valid_public(600, 700);
        let mut fixture = Fixture::new(&public, [99u8; 32]);
        let pool_before = fixture.pool_data;
        let marker_before = fixture.nullifier_data;
        let verifier_called = Cell::new(false);
        assert_eq!(
            fixture.apply(&public, |_, _, _| {
                verifier_called.set(true);
                Ok(())
            }),
            Err(ProgramError::Custom(ATOMIC_ERROR_ANCHOR_MISMATCH))
        );
        assert!(!verifier_called.get());
        assert_eq!(fixture.pool_data, pool_before);
        assert_eq!(fixture.nullifier_data, marker_before);
    }

    #[test]
    fn every_atomic_public_field_has_a_rejecting_no_mutation_tooth() {
        let original = valid_public(1_200, 1_400);
        let mut variants = Vec::new();

        let mut changed = original;
        changed.current_anchor[0] ^= 1;
        variants.push(("current_anchor", changed));
        let mut changed = original;
        changed.nullifier[0] ^= 1;
        variants.push(("nullifier", changed));
        let mut changed = original;
        changed.output_commitment[0] ^= 1;
        variants.push(("output_commitment", changed));
        let mut changed = original;
        changed.output_anchor[0] ^= 1;
        variants.push(("output_anchor", changed));
        let mut changed = original;
        changed.asset_id += 1;
        variants.push(("asset_id", changed));
        let mut changed = original;
        changed.fee += 1;
        variants.push(("fee", changed));

        for (field, changed) in variants {
            let mut fixture = Fixture::new(&original, original.current_anchor);
            let (_, expected_digest) = checked_statement(&fixture.pool_key, 0, &original).unwrap();
            let pool_before = fixture.pool_data;
            let marker_before = fixture.nullifier_data;
            let verifier_called = Cell::new(false);
            let result = fixture.apply(&changed, |_, _, digest| {
                verifier_called.set(true);
                assert_ne!(*digest, expected_digest, "field={field}");
                Err(ProgramError::InvalidInstructionData)
            });
            assert!(result.is_err(), "field={field}");
            assert_eq!(fixture.pool_data, pool_before, "field={field}");
            assert_eq!(fixture.nullifier_data, marker_before, "field={field}");
            if field == "asset_id" || field == "fee" {
                assert!(verifier_called.get(), "field={field}");
            }
        }
    }

    #[test]
    fn append_only_tag38_dispatch_is_fail_closed_and_does_not_mutate() {
        let public = valid_public(800, 900);
        let mut fixture = Fixture::new(&public, public.current_anchor);
        let pool_before = fixture.pool_data;
        let marker_before = fixture.nullifier_data;
        let instruction = crate::AspisInstruction::AtomicPaymentStateTransitionV1 {
            current_anchor: public.current_anchor,
            nullifier: public.nullifier,
            output_commitment: public.output_commitment,
            output_anchor: public.output_anchor,
            asset_id: public.asset_id,
            fee: public.fee,
        };
        let encoded = borsh::to_vec(&instruction).unwrap();
        assert_eq!(encoded[0], 38);
        let program_id = fixture.program_id;
        let accounts = fixture.accounts();
        assert_eq!(
            crate::process_instruction(&program_id, &accounts, &encoded),
            Err(ProgramError::Custom(ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED))
        );
        drop(accounts);
        assert_eq!(fixture.pool_data, pool_before);
        assert_eq!(fixture.nullifier_data, marker_before);
    }
}
