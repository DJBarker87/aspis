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
    atomic_payment_statement_digest_v4, decode_asset_id_canonical, decode_digest_canonical,
    AtomicPaymentStatementV4, AtomicStatementError, SpendPublic,
};

pub const ATOMIC_POOL_STATE_MAGIC: [u8; 4] = *b"ASPS";
pub const ATOMIC_POOL_STATE_VERSION: u8 = 2;
pub const ATOMIC_POOL_STATE_LEN: usize = 80;

pub const ATOMIC_NULLIFIER_MAGIC: [u8; 4] = *b"ASPN";
pub const ATOMIC_NULLIFIER_VERSION: u8 = 1;
pub const ATOMIC_NULLIFIER_MARKER_LEN: usize = 72;
pub const ATOMIC_NULLIFIER_SEED: &[u8] = b"aspis-nullifier-v1";
pub const PROOF_ACCOUNT_CLOSED_MAGIC: [u8; 4] = *b"ASPC";

pub const ATOMIC_ERROR_ANCHOR_MISMATCH: u32 = 0x4153_1001;
pub const ATOMIC_ERROR_NULLIFIER_ALREADY_SPENT: u32 = 0x4153_1002;
pub const ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED: u32 = 0x4153_1003;
pub const ATOMIC_ERROR_OUTPUT_INSERTION_MISMATCH: u32 = 0x4153_1004;
pub const ATOMIC_ERROR_DEPLOYMENT_DOMAIN_MISMATCH: u32 = 0x4153_1005;

const POOL_SEQUENCE_OFFSET: usize = 8;
const POOL_ANCHOR_OFFSET: usize = 16;
const POOL_DEPLOYMENT_DOMAIN_OFFSET: usize = 48;
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
    pub deployment_domain: [u8; 32],
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
) -> Result<(AtomicPaymentStatementV4, [u8; 32]), ProgramError> {
    let current_anchor =
        decode_digest_canonical(&public.current_anchor).map_err(map_statement_error)?;
    let nullifier = decode_digest_canonical(&public.nullifier).map_err(map_statement_error)?;
    let output_commitment =
        decode_digest_canonical(&public.output_commitment).map_err(map_statement_error)?;
    let output_anchor =
        decode_digest_canonical(&public.output_anchor).map_err(map_statement_error)?;
    let asset_id = decode_asset_id_canonical(public.asset_id).map_err(map_statement_error)?;
    let statement = AtomicPaymentStatementV4 {
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
        deployment_domain: public.deployment_domain,
    };
    let digest =
        atomic_payment_statement_digest_v4(&statement, sbf_sha256).map_err(map_statement_error)?;
    Ok((statement, digest))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AtomicPoolStateV2 {
    pub sequence: u64,
    pub anchor: [u8; 32],
    pub deployment_domain: [u8; 32],
}

impl AtomicPoolStateV2 {
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
            anchor: data[POOL_ANCHOR_OFFSET..POOL_DEPLOYMENT_DOMAIN_OFFSET]
                .try_into()
                .unwrap(),
            deployment_domain: data[POOL_DEPLOYMENT_DOMAIN_OFFSET..ATOMIC_POOL_STATE_LEN]
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
        data[POOL_ANCHOR_OFFSET..POOL_DEPLOYMENT_DOMAIN_OFFSET].copy_from_slice(&self.anchor);
        data[POOL_DEPLOYMENT_DOMAIN_OFFSET..ATOMIC_POOL_STATE_LEN]
            .copy_from_slice(&self.deployment_domain);
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
) -> Result<(AtomicPoolStateV2, u8, MarkerPreparation), ProgramError> {
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

    let pool = AtomicPoolStateV2::decode(&pool_account.try_borrow_data()?)?;
    // A proof/statement ground for another deployment domain must fail with
    // this exact error before any anchor comparison: a cross-deployment
    // replay is a domain error even when the tree states happen to align.
    if pool.deployment_domain != public.deployment_domain {
        return Err(ProgramError::Custom(
            ATOMIC_ERROR_DEPLOYMENT_DOMAIN_MISMATCH,
        ));
    }
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
    F: FnOnce(&AccountInfo<'a>, &AtomicPaymentStatementV4, &[u8; 32]) -> ProgramResult,
{
    verify_and_apply_atomic_payment_state_traced(
        program_id,
        accounts,
        public,
        verify_complete_proof,
        |_| {},
    )
}

/// Spend production form of [`verify_and_apply_atomic_payment_state`].
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
    F: FnOnce(&AccountInfo<'a>, &AtomicPaymentStatementV4, &[u8; 32]) -> ProgramResult,
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
    F: FnOnce(&AccountInfo<'a>, &AtomicPaymentStatementV4, &[u8; 32]) -> ProgramResult,
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
    F: FnOnce(&AccountInfo<'a>, &AtomicPaymentStatementV4, &[u8; 32]) -> ProgramResult,
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
    F: FnOnce(&AccountInfo<'a>, &AtomicPaymentStatementV4, &[u8; 32]) -> ProgramResult,
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
    let observed_pool = AtomicPoolStateV2::decode(&pool_data)?;
    if observed_pool != pool || observed_pool.anchor != public.current_anchor {
        return Err(ProgramError::Custom(ATOMIC_ERROR_ANCHOR_MISMATCH));
    }
    if NullifierMarkerV1::decode(&nullifier_data)?.is_some() {
        return Err(ProgramError::Custom(ATOMIC_ERROR_NULLIFIER_ALREADY_SPENT));
    }
    trace(AtomicPaymentTransitionTraceEvent::MutableStateRechecked);

    let next_pool = AtomicPoolStateV2 {
        sequence: pool.sequence + 1,
        anchor: public.output_anchor,
        deployment_domain: pool.deployment_domain,
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
    _statement: &AtomicPaymentStatementV4,
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
            deployment_domain: [0x0d; 32],
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
            AtomicPoolStateV2 {
                sequence: 0,
                anchor: stored_anchor,
                deployment_domain: public.deployment_domain,
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
            F: FnOnce(&AccountInfo, &AtomicPaymentStatementV4, &[u8; 32]) -> ProgramResult,
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
            F: FnOnce(&AccountInfo, &AtomicPaymentStatementV4, &[u8; 32]) -> ProgramResult,
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

        /// Build the five metas with the four caller-chosen keys placed at the
        /// proof/pool/nullifier/payer positions and run the transition. Only
        /// the keys move, so two positions can be aliased to the same account
        /// key to exercise the distinctness matrix; owners/flags stay canonical
        /// except the explicit proof access controls.
        #[allow(clippy::too_many_arguments)]
        fn apply_with_position_keys<F>(
            &mut self,
            positions: [Pubkey; 4],
            proof_is_signer: bool,
            proof_is_writable: bool,
            refund_path: bool,
            public: &AtomicPaymentPublicInputs,
            verify: F,
        ) -> ProgramResult
        where
            F: FnOnce(&AccountInfo, &AtomicPaymentStatementV4, &[u8; 32]) -> ProgramResult,
        {
            let program_id = self.program_id;
            let accounts = vec![
                make_account(
                    &positions[0],
                    &program_id,
                    &mut self.proof_lamports,
                    &mut self.proof_data,
                    proof_is_signer,
                    proof_is_writable,
                    false,
                ),
                make_account(
                    &positions[1],
                    &program_id,
                    &mut self.pool_lamports,
                    &mut self.pool_data,
                    false,
                    true,
                    false,
                ),
                make_account(
                    &positions[2],
                    &program_id,
                    &mut self.nullifier_lamports,
                    &mut self.nullifier_data,
                    false,
                    true,
                    false,
                ),
                make_account(
                    &positions[3],
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
            ];
            if refund_path {
                verify_and_apply_atomic_payment_state_with_proof_refund(
                    &program_id,
                    &accounts,
                    public,
                    verify,
                )
            } else {
                verify_and_apply_atomic_payment_state(&program_id, &accounts, public, verify)
            }
        }

        /// The canonical five metas but with the nullifier account owned by
        /// `nullifier_owner` instead of the program. Used to construct the
        /// wrong-owner / pre-created hostile nullifier shapes.
        fn accounts_with_nullifier_owner<'a>(
            &'a mut self,
            nullifier_owner: &'a Pubkey,
        ) -> Vec<AccountInfo<'a>> {
            vec![
                make_account(
                    &self.proof_key,
                    &self.program_id,
                    &mut self.proof_lamports,
                    &mut self.proof_data,
                    false,
                    false,
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
                    nullifier_owner,
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
    }

    #[test]
    fn exact_account_layouts_are_pinned() {
        let anchor = [7u8; 32];
        let deployment_domain = [11u8; 32];
        let mut pool = [0u8; ATOMIC_POOL_STATE_LEN];
        AtomicPoolStateV2 {
            sequence: 9,
            anchor,
            deployment_domain,
        }
        .encode(&mut pool)
        .unwrap();
        assert_eq!(&pool[0..4], &ATOMIC_POOL_STATE_MAGIC);
        assert_eq!(pool[4], ATOMIC_POOL_STATE_VERSION);
        assert_eq!(&pool[5..8], &[0u8; 3]);
        assert_eq!(&pool[16..48], &anchor);
        assert_eq!(&pool[48..80], &deployment_domain);
        assert_eq!(
            AtomicPoolStateV2::decode(&pool).unwrap(),
            AtomicPoolStateV2 {
                sequence: 9,
                anchor,
                deployment_domain,
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
                    atomic_payment_statement_digest_v4(statement, sbf_sha256).unwrap(),
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
                    atomic_payment_statement_digest_v4(statement, sbf_sha256).unwrap(),
                    *digest
                );
                Ok(())
            }),
            Ok(())
        );
        assert_eq!(
            AtomicPoolStateV2::decode(&fixture.pool_data).unwrap(),
            AtomicPoolStateV2 {
                sequence: 1,
                anchor: first.output_anchor,
                deployment_domain: first.deployment_domain,
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
    fn successful_spend_transition_refunds_and_tombstones_proof() {
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
            AtomicPoolStateV2::decode(&fixture.pool_data)
                .unwrap()
                .sequence,
            1
        );
        assert!(NullifierMarkerV1::decode(&fixture.nullifier_data)
            .unwrap()
            .is_some());
    }

    #[test]
    fn failed_spend_transition_preserves_proof_and_refund_balances() {
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
    fn spend_refund_requires_writable_proof_signer_and_checked_balance() {
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

    /// Host deployment-domain tooth: a proof/statement ground for domain A is
    /// rejected by a pool initialized with domain B, with the exact new error
    /// code, before the verifier runs and without any state change.
    #[test]
    fn cross_deployment_domain_rejects_without_verification_or_mutation() {
        let mut public_domain_a = valid_public(640, 740);
        public_domain_a.deployment_domain = aspis_statement::atomic_deployment_domain(
            sbf_sha256,
            &crate::id().to_bytes(),
            b"mainnet-beta",
        );
        // The pool below is initialized with domain B (same program id,
        // different domain tag), while the statement carries domain A.
        let mut fixture = Fixture::new(&public_domain_a, public_domain_a.current_anchor);
        let domain_b = aspis_statement::atomic_deployment_domain(
            sbf_sha256,
            &crate::id().to_bytes(),
            b"devnet",
        );
        assert_ne!(public_domain_a.deployment_domain, domain_b);
        AtomicPoolStateV2 {
            sequence: 0,
            anchor: public_domain_a.current_anchor,
            deployment_domain: domain_b,
        }
        .encode(&mut fixture.pool_data)
        .unwrap();

        let pool_before = fixture.pool_data;
        let marker_before = fixture.nullifier_data;
        let verifier_called = Cell::new(false);
        assert_eq!(
            fixture.apply(&public_domain_a, |_, _, _| {
                verifier_called.set(true);
                Ok(())
            }),
            Err(ProgramError::Custom(
                ATOMIC_ERROR_DEPLOYMENT_DOMAIN_MISMATCH
            ))
        );
        assert!(!verifier_called.get());
        assert_eq!(fixture.pool_data, pool_before);
        assert_eq!(fixture.nullifier_data, marker_before);

        // The refund path must reject identically without touching balances.
        let mut refund_fixture = Fixture::new(&public_domain_a, public_domain_a.current_anchor);
        AtomicPoolStateV2 {
            sequence: 0,
            anchor: public_domain_a.current_anchor,
            deployment_domain: domain_b,
        }
        .encode(&mut refund_fixture.pool_data)
        .unwrap();
        let proof_lamports_before = refund_fixture.proof_lamports;
        let payer_lamports_before = refund_fixture.payer_lamports;
        assert_eq!(
            refund_fixture.apply_with_refund(&public_domain_a, |_, _, _| Ok(())),
            Err(ProgramError::Custom(
                ATOMIC_ERROR_DEPLOYMENT_DOMAIN_MISMATCH
            ))
        );
        assert_eq!(refund_fixture.proof_lamports, proof_lamports_before);
        assert_eq!(refund_fixture.payer_lamports, payer_lamports_before);
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
        let mut changed = original;
        changed.deployment_domain[0] ^= 1;
        variants.push(("deployment_domain", changed));

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
            crate::dispatch::process_spend_production_instruction(&program_id, &accounts, &encoded),
            Err(ProgramError::InvalidInstructionData)
        );
        drop(accounts);
        assert_eq!(fixture.pool_data, pool_before);
        assert_eq!(fixture.nullifier_data, marker_before);
    }

    /// Adversarial account-aliasing / distinctness evidence for the atomic
    /// verifier. Each test constructs one hostile account arrangement and
    /// asserts the exact rejecting error together with an unchanged pool and
    /// nullifier (and, on the refund path, unchanged lamports). The full
    /// pairwise distinctness matrix over {proof, pool, nullifier, payer} is
    /// covered by the first six tests; the remainder cover wrong-owner,
    /// wrong-discriminator, pre-created/pre-seeded nullifier, sequence
    /// overflow, and mid-verification state mutation caught by the recheck.
    mod adversarial_account_aliasing {
        use super::*;

        // --- Pairwise distinctness matrix over the four mutable accounts. ---

        #[test]
        fn rejects_proof_account_aliased_to_pool_without_mutation() {
            let public = valid_public(2_100, 2_200);
            let mut fixture = Fixture::new(&public, public.current_anchor);
            let pool_before = fixture.pool_data;
            let marker_before = fixture.nullifier_data;
            let positions = [
                fixture.pool_key,
                fixture.pool_key,
                fixture.nullifier_key,
                fixture.payer_key,
            ];
            let verifier_called = Cell::new(false);
            let result = fixture.apply_with_position_keys(
                positions,
                false,
                false,
                false,
                &public,
                |_, _, _| {
                    verifier_called.set(true);
                    Ok(())
                },
            );
            assert_eq!(result, Err(ProgramError::InvalidArgument));
            assert!(!verifier_called.get());
            assert_eq!(fixture.pool_data, pool_before);
            assert_eq!(fixture.nullifier_data, marker_before);
        }

        #[test]
        fn rejects_proof_account_aliased_to_nullifier_pda_without_mutation() {
            let public = valid_public(2_110, 2_210);
            let mut fixture = Fixture::new(&public, public.current_anchor);
            let pool_before = fixture.pool_data;
            let marker_before = fixture.nullifier_data;
            let positions = [
                fixture.nullifier_key,
                fixture.pool_key,
                fixture.nullifier_key,
                fixture.payer_key,
            ];
            let verifier_called = Cell::new(false);
            let result = fixture.apply_with_position_keys(
                positions,
                false,
                false,
                false,
                &public,
                |_, _, _| {
                    verifier_called.set(true);
                    Ok(())
                },
            );
            assert_eq!(result, Err(ProgramError::InvalidArgument));
            assert!(!verifier_called.get());
            assert_eq!(fixture.pool_data, pool_before);
            assert_eq!(fixture.nullifier_data, marker_before);
        }

        #[test]
        fn rejects_proof_account_aliased_to_refund_destination_without_mutation() {
            // On the refund path account 3 (payer) is the rent-refund
            // recipient; aliasing the proof account to it must reject before
            // any drain.
            let public = valid_public(2_120, 2_220);
            let mut fixture = Fixture::new(&public, public.current_anchor);
            let pool_before = fixture.pool_data;
            let marker_before = fixture.nullifier_data;
            let proof_lamports_before = fixture.proof_lamports;
            let payer_lamports_before = fixture.payer_lamports;
            let positions = [
                fixture.payer_key,
                fixture.pool_key,
                fixture.nullifier_key,
                fixture.payer_key,
            ];
            let verifier_called = Cell::new(false);
            let result = fixture.apply_with_position_keys(
                positions,
                true,
                true,
                true,
                &public,
                |_, _, _| {
                    verifier_called.set(true);
                    Ok(())
                },
            );
            assert_eq!(result, Err(ProgramError::InvalidArgument));
            assert!(!verifier_called.get());
            assert_eq!(fixture.pool_data, pool_before);
            assert_eq!(fixture.nullifier_data, marker_before);
            assert_eq!(fixture.proof_lamports, proof_lamports_before);
            assert_eq!(fixture.payer_lamports, payer_lamports_before);
        }

        #[test]
        fn rejects_pool_state_aliased_to_nullifier_pda_without_mutation() {
            let public = valid_public(2_130, 2_230);
            let mut fixture = Fixture::new(&public, public.current_anchor);
            let pool_before = fixture.pool_data;
            let marker_before = fixture.nullifier_data;
            let positions = [
                fixture.proof_key,
                fixture.pool_key,
                fixture.pool_key,
                fixture.payer_key,
            ];
            let verifier_called = Cell::new(false);
            let result = fixture.apply_with_position_keys(
                positions,
                false,
                false,
                false,
                &public,
                |_, _, _| {
                    verifier_called.set(true);
                    Ok(())
                },
            );
            assert_eq!(result, Err(ProgramError::InvalidArgument));
            assert!(!verifier_called.get());
            assert_eq!(fixture.pool_data, pool_before);
            assert_eq!(fixture.nullifier_data, marker_before);
        }

        #[test]
        fn rejects_payer_aliased_to_pool_state_without_mutation() {
            // The payer is a writable signer; aliasing it onto the writable
            // pool-state account must reject.
            let public = valid_public(2_140, 2_240);
            let mut fixture = Fixture::new(&public, public.current_anchor);
            let pool_before = fixture.pool_data;
            let marker_before = fixture.nullifier_data;
            let positions = [
                fixture.proof_key,
                fixture.pool_key,
                fixture.nullifier_key,
                fixture.pool_key,
            ];
            let verifier_called = Cell::new(false);
            let result = fixture.apply_with_position_keys(
                positions,
                false,
                false,
                false,
                &public,
                |_, _, _| {
                    verifier_called.set(true);
                    Ok(())
                },
            );
            assert_eq!(result, Err(ProgramError::InvalidArgument));
            assert!(!verifier_called.get());
            assert_eq!(fixture.pool_data, pool_before);
            assert_eq!(fixture.nullifier_data, marker_before);
        }

        #[test]
        fn rejects_payer_aliased_to_nullifier_pda_without_mutation() {
            let public = valid_public(2_150, 2_250);
            let mut fixture = Fixture::new(&public, public.current_anchor);
            let pool_before = fixture.pool_data;
            let marker_before = fixture.nullifier_data;
            let positions = [
                fixture.proof_key,
                fixture.pool_key,
                fixture.nullifier_key,
                fixture.nullifier_key,
            ];
            let verifier_called = Cell::new(false);
            let result = fixture.apply_with_position_keys(
                positions,
                false,
                false,
                false,
                &public,
                |_, _, _| {
                    verifier_called.set(true);
                    Ok(())
                },
            );
            assert_eq!(result, Err(ProgramError::InvalidArgument));
            assert!(!verifier_called.get());
            assert_eq!(fixture.pool_data, pool_before);
            assert_eq!(fixture.nullifier_data, marker_before);
        }

        // --- Wrong owner / wrong discriminator / hostile pre-creation. ---

        #[test]
        fn rejects_nullifier_pda_with_correct_seeds_but_foreign_owner_without_mutation() {
            // The nullifier account key is the canonical PDA, but a third party
            // owns it (neither the program nor the System Program).
            let public = valid_public(2_300, 2_400);
            let mut fixture = Fixture::new(&public, public.current_anchor);
            let pool_before = fixture.pool_data;
            let marker_before = fixture.nullifier_data;
            let program_id = fixture.program_id;
            let foreign_owner = Pubkey::new_unique();
            assert_ne!(foreign_owner, program_id);
            assert_ne!(foreign_owner, system_program::id());
            let verifier_called = Cell::new(false);
            let accounts = fixture.accounts_with_nullifier_owner(&foreign_owner);
            let result = verify_and_apply_atomic_payment_state(
                &program_id,
                &accounts,
                &public,
                |_, _, _| {
                    verifier_called.set(true);
                    Ok(())
                },
            );
            assert_eq!(result, Err(ProgramError::IncorrectProgramId));
            drop(accounts);
            assert!(!verifier_called.get());
            assert_eq!(fixture.pool_data, pool_before);
            assert_eq!(fixture.nullifier_data, marker_before);
        }

        #[test]
        fn rejects_nullifier_pda_pre_created_system_owned_with_data_without_mutation() {
            // A griefer pre-creates the nullifier PDA System-owned but writes
            // data into it, so it is not the empty account the create path
            // accepts.
            let public = valid_public(2_310, 2_410);
            let mut fixture = Fixture::new(&public, public.current_anchor);
            fixture.nullifier_data[0] = 0x01;
            let pool_before = fixture.pool_data;
            let marker_before = fixture.nullifier_data;
            let program_id = fixture.program_id;
            let system_owner = system_program::id();
            let verifier_called = Cell::new(false);
            let accounts = fixture.accounts_with_nullifier_owner(&system_owner);
            let result = verify_and_apply_atomic_payment_state(
                &program_id,
                &accounts,
                &public,
                |_, _, _| {
                    verifier_called.set(true);
                    Ok(())
                },
            );
            assert_eq!(result, Err(ProgramError::IncorrectProgramId));
            drop(accounts);
            assert!(!verifier_called.get());
            assert_eq!(fixture.pool_data, pool_before);
            assert_eq!(fixture.nullifier_data, marker_before);
        }

        #[test]
        fn rejects_pool_state_with_correct_owner_but_wrong_discriminator_without_mutation() {
            // The pool account is program-owned and 80 bytes, but its magic is
            // corrupted, so decode must reject before verification.
            let public = valid_public(2_500, 2_600);
            let mut fixture = Fixture::new(&public, public.current_anchor);
            fixture.pool_data[0] ^= 0xff;
            let pool_before = fixture.pool_data;
            let marker_before = fixture.nullifier_data;
            let verifier_called = Cell::new(false);
            let result = fixture.apply(&public, |_, _, _| {
                verifier_called.set(true);
                Ok(())
            });
            assert_eq!(result, Err(ProgramError::InvalidAccountData));
            assert!(!verifier_called.get());
            assert_eq!(fixture.pool_data, pool_before);
            assert_eq!(fixture.nullifier_data, marker_before);
        }

        #[test]
        fn rejects_nullifier_marker_with_correct_owner_but_wrong_discriminator_without_mutation() {
            // The nullifier account is program-owned and correctly sized, but
            // holds non-zero data with the wrong magic.
            let public = valid_public(2_510, 2_610);
            let mut fixture = Fixture::new(&public, public.current_anchor);
            fixture.nullifier_data = [0xab; ATOMIC_NULLIFIER_MARKER_LEN];
            let pool_before = fixture.pool_data;
            let marker_before = fixture.nullifier_data;
            let verifier_called = Cell::new(false);
            let result = fixture.apply(&public, |_, _, _| {
                verifier_called.set(true);
                Ok(())
            });
            assert_eq!(result, Err(ProgramError::InvalidAccountData));
            assert!(!verifier_called.get());
            assert_eq!(fixture.pool_data, pool_before);
            assert_eq!(fixture.nullifier_data, marker_before);
        }

        #[test]
        fn rejects_nullifier_pda_pre_seeded_with_foreign_marker_without_mutation() {
            // The program-owned nullifier PDA already holds a valid marker for
            // a different nullifier value; this is an inconsistent PDA and must
            // reject rather than being overwritten.
            let public = valid_public(2_700, 2_800);
            let mut fixture = Fixture::new(&public, public.current_anchor);
            let mut foreign_nullifier = public.nullifier;
            foreign_nullifier[0] ^= 0xff;
            NullifierMarkerV1 {
                pool: fixture.pool_key,
                nullifier: foreign_nullifier,
            }
            .encode(&mut fixture.nullifier_data)
            .unwrap();
            let pool_before = fixture.pool_data;
            let marker_before = fixture.nullifier_data;
            let verifier_called = Cell::new(false);
            let result = fixture.apply(&public, |_, _, _| {
                verifier_called.set(true);
                Ok(())
            });
            assert_eq!(result, Err(ProgramError::InvalidAccountData));
            assert!(!verifier_called.get());
            assert_eq!(fixture.pool_data, pool_before);
            assert_eq!(fixture.nullifier_data, marker_before);
        }

        #[test]
        fn rejects_pool_sequence_overflow_before_verification_without_mutation() {
            // A pool already at u64::MAX cannot advance; the transition must
            // reject before running the verifier.
            let public = valid_public(2_900, 3_000);
            let mut fixture = Fixture::new(&public, public.current_anchor);
            AtomicPoolStateV2 {
                sequence: u64::MAX,
                anchor: public.current_anchor,
                deployment_domain: public.deployment_domain,
            }
            .encode(&mut fixture.pool_data)
            .unwrap();
            let pool_before = fixture.pool_data;
            let marker_before = fixture.nullifier_data;
            let verifier_called = Cell::new(false);
            let result = fixture.apply(&public, |_, _, _| {
                verifier_called.set(true);
                Ok(())
            });
            assert_eq!(result, Err(ProgramError::ArithmeticOverflow));
            assert!(!verifier_called.get());
            assert_eq!(fixture.pool_data, pool_before);
            assert_eq!(fixture.nullifier_data, marker_before);
        }

        // --- Mutable-state changed between snapshot and commit (recheck). ---

        #[test]
        fn rejects_pool_mutation_during_verification_via_recheck_without_commit() {
            // A shared handle to the pool account changes its anchor while the
            // verifier is running (modelling a concurrent/reentrant write
            // between the validation snapshot and the final commit). The
            // post-verification recheck must reject and the pool must not be
            // advanced to `output_anchor`.
            let public = valid_public(3_100, 3_200);
            let mut fixture = Fixture::new(&public, public.current_anchor);
            let program_id = fixture.program_id;
            let output_anchor = public.output_anchor;
            let accounts = fixture.accounts();
            let pool_handle = accounts[1].clone();
            let result = verify_and_apply_atomic_payment_state(
                &program_id,
                &accounts,
                &public,
                |_, _, _| {
                    let mut data = pool_handle.try_borrow_mut_data().unwrap();
                    data[POOL_ANCHOR_OFFSET..POOL_DEPLOYMENT_DOMAIN_OFFSET]
                        .copy_from_slice(&[0x5c; 32]);
                    Ok(())
                },
            );
            assert_eq!(
                result,
                Err(ProgramError::Custom(ATOMIC_ERROR_ANCHOR_MISMATCH))
            );
            drop(pool_handle);
            drop(accounts);
            let observed = AtomicPoolStateV2::decode(&fixture.pool_data).unwrap();
            assert_eq!(observed.sequence, 0, "pool sequence must not advance");
            assert_ne!(
                observed.anchor, output_anchor,
                "pool must not be advanced to output_anchor"
            );
            assert!(NullifierMarkerV1::decode(&fixture.nullifier_data)
                .unwrap()
                .is_none());
        }

        #[test]
        fn rejects_nullifier_marker_appearing_during_verification_via_recheck_without_commit() {
            // The nullifier marker for this exact spend appears while the
            // verifier runs (a concurrent spend of the same note). The recheck
            // must report the nullifier as already spent and not advance the
            // pool.
            let public = valid_public(3_110, 3_210);
            let mut fixture = Fixture::new(&public, public.current_anchor);
            let program_id = fixture.program_id;
            let pool_key = fixture.pool_key;
            let accounts = fixture.accounts();
            let nullifier_handle = accounts[2].clone();
            let result = verify_and_apply_atomic_payment_state(
                &program_id,
                &accounts,
                &public,
                |_, _, _| {
                    let mut marker_bytes = [0u8; ATOMIC_NULLIFIER_MARKER_LEN];
                    NullifierMarkerV1 {
                        pool: pool_key,
                        nullifier: public.nullifier,
                    }
                    .encode(&mut marker_bytes)
                    .unwrap();
                    nullifier_handle
                        .try_borrow_mut_data()
                        .unwrap()
                        .copy_from_slice(&marker_bytes);
                    Ok(())
                },
            );
            assert_eq!(
                result,
                Err(ProgramError::Custom(ATOMIC_ERROR_NULLIFIER_ALREADY_SPENT))
            );
            drop(nullifier_handle);
            drop(accounts);
            assert_eq!(
                AtomicPoolStateV2::decode(&fixture.pool_data)
                    .unwrap()
                    .sequence,
                0,
                "pool sequence must not advance"
            );
        }
    }
}
