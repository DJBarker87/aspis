//! Verifier-owned Pool V1 authorization-receipt (`ASRA`) lifecycle.
//!
//! These append-only handlers wrap the pure 720-byte account state machine in
//! exact Solana account, PDA, signer, rent, and close checks.  Initialization
//! binds a complete, still-unsealed `ASPU` upload to its upload authority;
//! finalization is the only pending-to-verified transition and occurs only
//! after the complete Tag-73 verifier accepts; close authenticates the
//! immutable refund authority and tombstones before draining.
//!
//! Dispatch integration is intentionally outside this module.  Numeric tags
//! 74, 75, and 76 are reserved here so the production dispatcher can append
//! them without changing any older wire ordinal.
//!
//! The lifecycle accepts either the legacy read-only compatibility profile or
//! the native Pool V1 private-transfer/withdrawal profile.  The selected
//! profile and release are immutable receipt bindings; finalization replays
//! the same request through the matching full verifier before writing.

use aspis_core::HashFn;
use aspis_statement::{
    pool_v1::{
        authorize_close_pool_v1_authorization_receipt_account_v1,
        decode_pool_v1_authorization_receipt_account_v1, decode_verifier_dispatch_request_v1,
        finalize_pool_v1_authorization_receipt_account_v1, historical_anchor_envelope_digest_v1,
        initialize_pool_v1_authorization_receipt_account_v1,
        pool_v1_authorization_receipt_binding_digest_v1,
        pool_v1_authorization_receipt_pda_inputs_for_binding_v1,
        validate_pool_v1_authorization_receipt_account_pda_inputs_v1,
        validate_pool_v1_authorization_receipt_account_request_v1, verifier_proof_body_digest_v1,
        HistoricalAnchorEnvelopeV1, PoolV1AuthorizationReceiptAccountStatusV1,
        PoolV1AuthorizationReceiptAccountV1, PoolV1AuthorizationReceiptPdaInputsV1,
        PoolV1AuthorizationReceiptV1, PoolV1TransitionKind, VerifierDispatchRequestV1,
        POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES, POOL_V1_AUTHORIZATION_RECEIPT_SEED,
    },
    AtomicPaymentStatementV4,
};
use solana_program::{
    account_info::AccountInfo,
    clock::Clock,
    entrypoint::ProgramResult,
    program::{invoke, invoke_signed},
    program_error::ProgramError,
    pubkey::Pubkey,
    rent::Rent,
    system_instruction, system_program,
    sysvar::Sysvar,
};

use crate::{
    lifecycle::{proof_account_finalized, uploaded_proof_bounds, AUTHORITY_OFFSET},
    v7_pool_dispatch::{
        decode_v7_pool_tag73_profile_payload_v1, verify_v7_pool_tag73_asvq_with_runtime,
        V7_POOL_TAG73_PROFILE_BINDING,
    },
    v7_pool_native_dispatch::{
        validate_v7_pool_native_tag73_request_v1, verify_v7_pool_native_tag73_asvq_with_runtime,
        V7_POOL_NATIVE_TAG73_REQUEST_BYTES,
    },
    v7_transaction::V7_RELEASE_BINDING,
};

pub const V7_POOL_RECEIPT_INITIALIZE_TAG: u8 = 74;
pub const V7_POOL_RECEIPT_FINALIZE_TAG: u8 = 75;
pub const V7_POOL_RECEIPT_CLOSE_TAG: u8 = 76;

pub const V7_POOL_RECEIPT_INITIALIZE_ACCOUNTS: usize = 4;
pub const V7_POOL_RECEIPT_FINALIZE_ACCOUNTS: usize = 2;
pub const V7_POOL_RECEIPT_CLOSE_ACCOUNTS: usize = 2;

/// A closed zero-lamport account must not become a valid receipt if another
/// instruction credits its address before transaction commit.
pub const V7_POOL_RECEIPT_CLOSED_MAGIC: [u8; 4] = *b"ASRC";

const NATIVE_LOADER_ID: Pubkey =
    solana_program::pubkey!("NativeLoader1111111111111111111111111111111");

const _: () = assert!(V7_POOL_RECEIPT_INITIALIZE_TAG == 74);
const _: () = assert!(V7_POOL_RECEIPT_FINALIZE_TAG == 75);
const _: () = assert!(V7_POOL_RECEIPT_CLOSE_TAG == 76);
const _: () = assert!(POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES == 720);
const _: () = assert!(POOL_V1_AUTHORIZATION_RECEIPT_SEED.len() <= 32);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ReceiptAccountPreparationV1 {
    Create { required_lamports: u64 },
    AllocateAssign { transfer_lamports: u64 },
}

fn exact_accounts<'a, 'info, const N: usize>(
    accounts: &'a [AccountInfo<'info>],
) -> Result<&'a [AccountInfo<'info>; N], ProgramError> {
    if accounts.len() < N {
        return Err(ProgramError::NotEnoughAccountKeys);
    }
    if accounts.len() > N {
        return Err(ProgramError::InvalidArgument);
    }
    accounts
        .try_into()
        .map_err(|_| ProgramError::InvalidArgument)
}

fn receipt_account_preparation_v1(
    current_lamports: u64,
    required_lamports: u64,
) -> ReceiptAccountPreparationV1 {
    if current_lamports == 0 {
        ReceiptAccountPreparationV1::Create { required_lamports }
    } else {
        ReceiptAccountPreparationV1::AllocateAssign {
            transfer_lamports: required_lamports.saturating_sub(current_lamports),
        }
    }
}

fn statement_matches_dispatch_binding(
    statement: &AtomicPaymentStatementV4,
    request: &VerifierDispatchRequestV1<'_>,
) -> bool {
    let binding = &request.binding;
    binding.transition_kind == PoolV1TransitionKind::PrivateTransfer
        && statement.pool == binding.pool
        && statement.sequence == binding.anchor_sequence
        && statement.spend.anchor == binding.anchor_root
        && statement.spend.nullifier == binding.nullifier
        && statement.deployment_domain == binding.deployment_domain
}

/// Validate the complete Tag-73 request without running the proof verifier.
/// The finalized handler deliberately reuses the canonical verifier helper;
/// initialization needs this metadata-only form because its proof upload must
/// still contain the nonzero authority that prevents PDA squatting.
fn validate_unsealed_legacy_tag73_request<'a>(
    program_id: &Pubkey,
    proof_account: &AccountInfo<'_>,
    instruction_data: &'a [u8],
    hash: HashFn,
) -> Result<VerifierDispatchRequestV1<'a>, ProgramError> {
    let request = decode_verifier_dispatch_request_v1(instruction_data, hash)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    if request.binding.verifier_program != program_id.to_bytes() {
        return Err(ProgramError::IncorrectProgramId);
    }
    if request.binding.profile_binding != V7_POOL_TAG73_PROFILE_BINDING
        || request.binding.release_binding != V7_RELEASE_BINDING
        || request.binding.transition_kind != PoolV1TransitionKind::PrivateTransfer
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    if request.binding.proof_account != proof_account.key.to_bytes() {
        return Err(ProgramError::InvalidArgument);
    }

    let payload = decode_v7_pool_tag73_profile_payload_v1(request.statement_payload, hash)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    if payload.verifier_program != request.binding.verifier_program
        || payload.release_binding != request.binding.release_binding
        || payload.attempt_id != request.binding.proof_account
        || payload.proof_body_length != request.binding.proof_body_length
        || payload.proof_body_digest != request.binding.proof_body_digest
        || !statement_matches_dispatch_binding(&payload.statement, &request)
    {
        return Err(ProgramError::InvalidInstructionData);
    }

    let envelope = HistoricalAnchorEnvelopeV1 {
        transition_kind: request.binding.transition_kind,
        pool: request.binding.pool,
        deployment_domain: request.binding.deployment_domain,
        anchor_sequence: request.binding.anchor_sequence,
        anchor_root: request.binding.anchor_root,
        nullifier: request.binding.nullifier,
        verifier_profile: request.binding.profile_binding,
        verifier_release: request.binding.release_binding,
    };
    let envelope_digest = historical_anchor_envelope_digest_v1(&envelope, hash)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    if envelope_digest != request.binding.envelope_digest {
        return Err(ProgramError::InvalidInstructionData);
    }
    Ok(request)
}

/// Metadata-only validation used before the upload authority is cleared.
/// Exact request length selects the native profile because its canonical
/// 216-byte Pool statement makes the complete ASVQ exactly 600 bytes; the
/// legacy A7P1 compatibility payload makes its ASVQ exactly 776 bytes.
fn validate_unsealed_selected_tag73_request<'a>(
    program_id: &Pubkey,
    proof_account: &AccountInfo<'_>,
    instruction_data: &'a [u8],
    hash: HashFn,
) -> Result<VerifierDispatchRequestV1<'a>, ProgramError> {
    if instruction_data.len() == V7_POOL_NATIVE_TAG73_REQUEST_BYTES {
        return Ok(validate_v7_pool_native_tag73_request_v1(
            program_id,
            proof_account,
            instruction_data,
            hash,
        )?
        .request);
    }
    validate_unsealed_legacy_tag73_request(program_id, proof_account, instruction_data, hash)
}

fn verify_selected_tag73_asvq_with_runtime(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
    hash: HashFn,
) -> Result<aspis_statement::pool_v1::VerifierDispatchBindingV1, ProgramError> {
    if instruction_data.len() == V7_POOL_NATIVE_TAG73_REQUEST_BYTES {
        return verify_v7_pool_native_tag73_asvq_with_runtime(
            program_id,
            accounts,
            instruction_data,
            hash,
        );
    }
    verify_v7_pool_tag73_asvq_with_runtime(
        program_id,
        accounts,
        instruction_data,
        hash,
        |proof,
         frontier_nodes,
         program_id,
         release_binding,
         attempt_id,
         statement,
         statement_digest,
         check_pow| {
            crate::v7_verifier::verify_v7_read_only_with_statement_digest(
                hash,
                proof,
                frontier_nodes,
                program_id,
                release_binding,
                attempt_id,
                statement,
                statement_digest,
                check_pow,
            )
            .map_err(|_| ProgramError::InvalidAccountData)?;
            Ok(())
        },
    )
}

fn canonical_receipt_pda_for_binding(
    program_id: &Pubkey,
    request: &VerifierDispatchRequestV1<'_>,
    hash: HashFn,
) -> Result<(Pubkey, PoolV1AuthorizationReceiptPdaInputsV1), ProgramError> {
    let binding_digest = pool_v1_authorization_receipt_binding_digest_v1(&request.binding, hash)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let (address, bump) = Pubkey::find_program_address(
        &[
            POOL_V1_AUTHORIZATION_RECEIPT_SEED,
            &request.binding.proof_account,
            &request.binding.statement_digest,
            &binding_digest,
        ],
        program_id,
    );
    let inputs =
        pool_v1_authorization_receipt_pda_inputs_for_binding_v1(&request.binding, bump, hash)
            .map_err(|_| ProgramError::InvalidInstructionData)?;
    Ok((address, inputs))
}

fn validate_stored_receipt_pda(
    program_id: &Pubkey,
    receipt_key: &Pubkey,
    receipt: &PoolV1AuthorizationReceiptAccountV1,
) -> ProgramResult {
    if receipt.verifier_program != program_id.to_bytes() {
        return Err(ProgramError::IncorrectProgramId);
    }
    let inputs = receipt.pda_inputs();
    let dynamic = inputs.dynamic_seeds();
    let (expected_address, canonical_bump) = Pubkey::find_program_address(
        &[
            POOL_V1_AUTHORIZATION_RECEIPT_SEED,
            &dynamic[0],
            &dynamic[1],
            &dynamic[2],
        ],
        program_id,
    );
    if receipt_key != &expected_address || inputs.bump != canonical_bump {
        return Err(ProgramError::InvalidSeeds);
    }
    let expected = PoolV1AuthorizationReceiptPdaInputsV1 {
        bump: canonical_bump,
        ..inputs
    };
    validate_pool_v1_authorization_receipt_account_pda_inputs_v1(receipt, &expected)
        .map_err(|_| ProgramError::InvalidSeeds)
}

fn create_or_allocate_receipt_account<'a>(
    program_id: &Pubkey,
    receipt_account: &AccountInfo<'a>,
    upload_authority: &AccountInfo<'a>,
    system_program_account: &AccountInfo<'a>,
    pda_inputs: &PoolV1AuthorizationReceiptPdaInputsV1,
    preparation: ReceiptAccountPreparationV1,
    pending_image: &[u8; POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES],
) -> ProgramResult {
    let bump_seed = [pda_inputs.bump];
    let signer_seed_values: &[&[u8]] = &[
        POOL_V1_AUTHORIZATION_RECEIPT_SEED,
        &pda_inputs.proof_account,
        &pda_inputs.statement_digest,
        &pda_inputs.binding_digest,
        &bump_seed,
    ];
    let signer_seeds = &[signer_seed_values];
    let account_infos = [
        upload_authority.clone(),
        receipt_account.clone(),
        system_program_account.clone(),
    ];

    match preparation {
        ReceiptAccountPreparationV1::Create { required_lamports } => {
            invoke_signed(
                &system_instruction::create_account(
                    upload_authority.key,
                    receipt_account.key,
                    required_lamports,
                    POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES as u64,
                    program_id,
                ),
                &account_infos,
                signer_seeds,
            )?;
        }
        ReceiptAccountPreparationV1::AllocateAssign { transfer_lamports } => {
            if transfer_lamports != 0 {
                invoke(
                    &system_instruction::transfer(
                        upload_authority.key,
                        receipt_account.key,
                        transfer_lamports,
                    ),
                    &account_infos,
                )?;
            }
            invoke_signed(
                &system_instruction::allocate(
                    receipt_account.key,
                    POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES as u64,
                ),
                &account_infos,
                signer_seeds,
            )?;
            invoke_signed(
                &system_instruction::assign(receipt_account.key, program_id),
                &account_infos,
                signer_seeds,
            )?;
        }
    }

    if receipt_account.owner != program_id {
        return Err(ProgramError::IncorrectProgramId);
    }
    let mut data = receipt_account.try_borrow_mut_data()?;
    if data.len() != POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES
        || data.iter().any(|byte| *byte != 0)
    {
        return Err(ProgramError::InvalidAccountData);
    }
    data.copy_from_slice(pending_image);
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn process_v7_pool_receipt_initialize_with_runtime<'a, R, C>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'a>],
    instruction_data: &[u8],
    hash: HashFn,
    minimum_balance: R,
    create_or_allocate: C,
) -> ProgramResult
where
    R: FnOnce(usize) -> Result<u64, ProgramError>,
    C: FnOnce(
        &Pubkey,
        &AccountInfo<'a>,
        &AccountInfo<'a>,
        &AccountInfo<'a>,
        &PoolV1AuthorizationReceiptPdaInputsV1,
        ReceiptAccountPreparationV1,
        &[u8; POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES],
    ) -> ProgramResult,
{
    let [proof_account, receipt_account, upload_authority, system_program_account] =
        exact_accounts::<V7_POOL_RECEIPT_INITIALIZE_ACCOUNTS>(accounts)?;

    if proof_account.owner != program_id {
        return Err(ProgramError::IncorrectProgramId);
    }
    if proof_account.is_signer || proof_account.is_writable || proof_account.executable {
        return Err(ProgramError::InvalidAccountData);
    }
    if receipt_account.owner != &system_program::id() {
        return Err(ProgramError::IncorrectProgramId);
    }
    if receipt_account.is_signer
        || !receipt_account.is_writable
        || receipt_account.executable
        || !receipt_account.data_is_empty()
    {
        return Err(ProgramError::InvalidAccountData);
    }
    if !upload_authority.is_signer {
        return Err(ProgramError::MissingRequiredSignature);
    }
    if !upload_authority.is_writable
        || upload_authority.executable
        || !upload_authority.data_is_empty()
    {
        return Err(ProgramError::InvalidAccountData);
    }
    if upload_authority.owner != &system_program::id()
        || system_program_account.key != &system_program::id()
        || system_program_account.owner != &NATIVE_LOADER_ID
    {
        return Err(ProgramError::IncorrectProgramId);
    }
    if system_program_account.is_signer
        || system_program_account.is_writable
        || !system_program_account.executable
    {
        return Err(ProgramError::InvalidAccountData);
    }
    if proof_account.key == receipt_account.key
        || proof_account.key == upload_authority.key
        || receipt_account.key == upload_authority.key
        || proof_account.key == system_program_account.key
        || receipt_account.key == system_program_account.key
        || upload_authority.key == system_program_account.key
    {
        return Err(ProgramError::InvalidArgument);
    }

    let request = validate_unsealed_selected_tag73_request(
        program_id,
        proof_account,
        instruction_data,
        hash,
    )?;
    let proof_header_upload_authority = {
        let data = proof_account.try_borrow_data()?;
        if proof_account_finalized(&data) {
            return Err(ProgramError::InvalidAccountData);
        }
        let (proof_start, proof_end) = uploaded_proof_bounds(&data)?;
        if proof_end != data.len()
            || proof_end - proof_start != request.binding.proof_body_length as usize
            || verifier_proof_body_digest_v1(&data[proof_start..proof_end], hash)
                != request.binding.proof_body_digest
        {
            return Err(ProgramError::InvalidAccountData);
        }
        let authority: [u8; 32] = data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32]
            .try_into()
            .map_err(|_| ProgramError::InvalidAccountData)?;
        if authority == [0u8; 32] || authority != upload_authority.key.to_bytes() {
            return Err(ProgramError::InvalidAccountData);
        }
        authority
    };

    let (expected_receipt, pda_inputs) =
        canonical_receipt_pda_for_binding(program_id, &request, hash)?;
    if receipt_account.key != &expected_receipt {
        return Err(ProgramError::InvalidSeeds);
    }
    let pending_image = initialize_pool_v1_authorization_receipt_account_v1(
        &request,
        proof_account.key.to_bytes(),
        proof_header_upload_authority,
        Some(upload_authority.key.to_bytes()),
        upload_authority.key.to_bytes(),
        pda_inputs.bump,
        hash,
    )
    .map_err(|_| ProgramError::InvalidInstructionData)?;
    let decoded_pending = decode_pool_v1_authorization_receipt_account_v1(&pending_image, hash)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    validate_pool_v1_authorization_receipt_account_pda_inputs_v1(&decoded_pending, &pda_inputs)
        .map_err(|_| ProgramError::InvalidSeeds)?;

    let required_lamports = minimum_balance(POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES)?.max(1);
    let preparation = receipt_account_preparation_v1(receipt_account.lamports(), required_lamports);
    create_or_allocate(
        program_id,
        receipt_account,
        upload_authority,
        system_program_account,
        &pda_inputs,
        preparation,
        &pending_image,
    )
}

/// Tag 74 body: one canonical Tag-73 `ASVQ` request (600-byte native Pool V1
/// or 776-byte legacy compatibility profile).
///
/// Accounts (exactly four): read-only unsealed verifier-owned `ASPU`, writable
/// canonical System-owned receipt PDA, writable upload-authority signer/payer,
/// and the read-only executable System Program.
pub fn process_v7_pool_receipt_initialize_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
) -> ProgramResult {
    process_v7_pool_receipt_initialize_with_runtime(
        program_id,
        accounts,
        instruction_data,
        crate::verify::sbf_hashv,
        |space| Ok(Rent::get()?.minimum_balance(space)),
        create_or_allocate_receipt_account,
    )
}

fn validate_pending_receipt_for_request(
    program_id: &Pubkey,
    receipt_key: &Pubkey,
    bytes: &[u8],
    request: &VerifierDispatchRequestV1<'_>,
    hash: HashFn,
) -> Result<PoolV1AuthorizationReceiptAccountV1, ProgramError> {
    let receipt = decode_pool_v1_authorization_receipt_account_v1(bytes, hash)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    if receipt.status != PoolV1AuthorizationReceiptAccountStatusV1::Pending {
        return Err(ProgramError::InvalidAccountData);
    }
    validate_pool_v1_authorization_receipt_account_request_v1(&receipt, request, hash)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let (_, expected_inputs) = canonical_receipt_pda_for_binding(program_id, request, hash)?;
    validate_pool_v1_authorization_receipt_account_pda_inputs_v1(&receipt, &expected_inputs)
        .map_err(|_| ProgramError::InvalidSeeds)?;
    validate_stored_receipt_pda(program_id, receipt_key, &receipt)?;
    Ok(receipt)
}

fn process_v7_pool_receipt_finalize_with_runtime<'a, V, S>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'a>],
    instruction_data: &[u8],
    hash: HashFn,
    verify: V,
    current_slot: S,
) -> ProgramResult
where
    V: FnOnce(
        &Pubkey,
        &[AccountInfo<'a>],
        &[u8],
        HashFn,
    ) -> Result<aspis_statement::pool_v1::VerifierDispatchBindingV1, ProgramError>,
    S: FnOnce() -> Result<u64, ProgramError>,
{
    let [proof_account, receipt_account] =
        exact_accounts::<V7_POOL_RECEIPT_FINALIZE_ACCOUNTS>(accounts)?;
    if receipt_account.owner != program_id {
        return Err(ProgramError::IncorrectProgramId);
    }
    if receipt_account.is_signer || !receipt_account.is_writable || receipt_account.executable {
        return Err(ProgramError::InvalidAccountData);
    }
    if receipt_account.data_len() != POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES {
        return Err(ProgramError::InvalidAccountData);
    }
    if proof_account.key == receipt_account.key {
        return Err(ProgramError::InvalidArgument);
    }

    let request = decode_verifier_dispatch_request_v1(instruction_data, hash)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    {
        let data = receipt_account.try_borrow_data()?;
        validate_pending_receipt_for_request(
            program_id,
            receipt_account.key,
            &data,
            &request,
            hash,
        )?;
    }

    let binding = verify(
        program_id,
        core::slice::from_ref(proof_account),
        instruction_data,
        hash,
    )?;
    if binding != request.binding {
        return Err(ProgramError::InvalidInstructionData);
    }
    let verified_slot = current_slot()?;

    // Re-decode immediately before the one write.  The production verifier
    // cannot mutate this account, and this recheck also makes injected-runtime
    // tests fail closed if a callback attempts to substitute pending state.
    let finalized_image = {
        let data = receipt_account.try_borrow_data()?;
        let pending = validate_pending_receipt_for_request(
            program_id,
            receipt_account.key,
            &data,
            &request,
            hash,
        )?;
        finalize_pool_v1_authorization_receipt_account_v1(
            &data,
            &request,
            &PoolV1AuthorizationReceiptV1 {
                pda_bump: pending.pda_bump,
                verified_slot,
                binding,
            },
            hash,
        )
        .map_err(|_| ProgramError::InvalidAccountData)?
    };
    let mut data = receipt_account.try_borrow_mut_data()?;
    data.copy_from_slice(&finalized_image);
    Ok(())
}

/// Tag 75 body: the same exact Tag-73 `ASVQ` committed at initialization.
/// Accounts are exactly the read-only sealed proof and writable canonical
/// verifier-owned receipt PDA.  The runtime Clock supplies `verified_slot`.
pub fn process_v7_pool_receipt_finalize_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
) -> ProgramResult {
    process_v7_pool_receipt_finalize_with_runtime(
        program_id,
        accounts,
        instruction_data,
        crate::verify::sbf_hashv,
        verify_selected_tag73_asvq_with_runtime,
        || Ok(Clock::get()?.slot),
    )
}

fn close_receipt_with_observer<O>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
    hash: HashFn,
    observe_tombstone_before_drain: O,
) -> ProgramResult
where
    O: FnOnce(&[u8]),
{
    if !instruction_data.is_empty() {
        return Err(ProgramError::InvalidInstructionData);
    }
    let [receipt_account, refund_authority] =
        exact_accounts::<V7_POOL_RECEIPT_CLOSE_ACCOUNTS>(accounts)?;
    if receipt_account.owner != program_id {
        return Err(ProgramError::IncorrectProgramId);
    }
    if receipt_account.is_signer || !receipt_account.is_writable || receipt_account.executable {
        return Err(ProgramError::InvalidAccountData);
    }
    if receipt_account.data_len() != POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES {
        return Err(ProgramError::InvalidAccountData);
    }
    if !refund_authority.is_signer {
        return Err(ProgramError::MissingRequiredSignature);
    }
    if !refund_authority.is_writable
        || refund_authority.executable
        || !refund_authority.data_is_empty()
    {
        return Err(ProgramError::InvalidAccountData);
    }
    if refund_authority.owner != &system_program::id() {
        return Err(ProgramError::IncorrectProgramId);
    }
    if receipt_account.key == refund_authority.key {
        return Err(ProgramError::InvalidArgument);
    }

    {
        let data = receipt_account.try_borrow_data()?;
        let receipt = decode_pool_v1_authorization_receipt_account_v1(&data, hash)
            .map_err(|_| ProgramError::InvalidAccountData)?;
        validate_stored_receipt_pda(program_id, receipt_account.key, &receipt)?;
        authorize_close_pool_v1_authorization_receipt_account_v1(
            &data,
            Some(refund_authority.key.to_bytes()),
            refund_authority.key.to_bytes(),
            hash,
        )
        .map_err(|_| ProgramError::InvalidArgument)?;
    }

    let refundable = receipt_account.lamports();
    if refundable == 0 {
        return Err(ProgramError::InvalidAccountData);
    }
    let refunded_balance = refund_authority
        .lamports()
        .checked_add(refundable)
        .ok_or(ProgramError::ArithmeticOverflow)?;

    // Acquire every fallible borrow before invalidating any byte.  There are
    // no fallible operations after the tombstone is installed.
    let mut receipt_data = receipt_account.try_borrow_mut_data()?;
    let mut receipt_lamports = receipt_account.try_borrow_mut_lamports()?;
    let mut refund_lamports = refund_authority.try_borrow_mut_lamports()?;
    receipt_data.fill(0);
    receipt_data[..4].copy_from_slice(&V7_POOL_RECEIPT_CLOSED_MAGIC);
    observe_tombstone_before_drain(&receipt_data);
    **refund_lamports = refunded_balance;
    **receipt_lamports = 0;
    Ok(())
}

/// Tag 76 has an empty body and exactly two writable accounts: the canonical
/// verifier-owned receipt followed by its embedded close/refund signer.
pub fn process_v7_pool_receipt_close_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
) -> ProgramResult {
    close_receipt_with_observer(
        program_id,
        accounts,
        instruction_data,
        crate::verify::sbf_hashv,
        |_| {},
    )
}

#[cfg(test)]
mod tests {
    use core::cell::Cell;
    use std::{cell::RefCell, vec, vec::Vec};

    use aspis_core::field::M31;
    use aspis_statement::{
        atomic_payment_statement_digest_v4,
        pool_v1::{
            encode_pool_v1_private_transfer_public_v1, encode_pool_v1_withdrawal_public_v1,
            encode_verifier_dispatch_request_v1, v7_pool_native_tag73_proof_body_bytes,
            verifier_dispatch_binding_from_envelope_v1, PoolV1AuthorizationReceiptAccountStatusV1,
            PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1, VerifierDispatchRequestV1,
            POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES, POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC,
            V7_POOL_NATIVE_TAG73_MIN_FRONTIER_NODES, V7_POOL_NATIVE_TAG73_PROFILE_BINDING,
            V7_POOL_NATIVE_TAG73_RELEASE_BINDING,
        },
        SpendPublic,
    };
    use solana_program::clock::Epoch;

    use crate::v7_pool_dispatch::{
        encode_v7_pool_tag73_profile_payload_v1, V7PoolTag73ProfilePayloadV1,
        V7_POOL_TAG73_FRONTIER_NODES, V7_POOL_TAG73_PROOF_BODY_BYTES,
    };

    use super::*;

    fn sha256(inputs: &[&[u8]]) -> [u8; 32] {
        solana_program::hash::hashv(inputs).to_bytes()
    }

    fn digest(seed: u32) -> aspis_statement::Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    struct Fixture {
        program_id: Pubkey,
        proof_key: Pubkey,
        upload_authority: Pubkey,
        statement: AtomicPaymentStatementV4,
        request: Vec<u8>,
        proof_body: Vec<u8>,
        unsealed_proof_data: Vec<u8>,
    }

    impl Fixture {
        fn new() -> Self {
            let program_id = crate::id();
            let proof_key = Pubkey::new_unique();
            let upload_authority = Pubkey::new_unique();
            let statement = AtomicPaymentStatementV4 {
                pool: Pubkey::new_unique().to_bytes(),
                sequence: 7,
                spend: SpendPublic {
                    anchor: digest(10),
                    nullifier: digest(100),
                    output_commitment: digest(200),
                    asset_id: M31(17),
                    fee: 1,
                },
                output_anchor: digest(300),
                deployment_domain: [0x44; 32],
            };
            let proof_body: Vec<u8> = (0..V7_POOL_TAG73_PROOF_BODY_BYTES as usize)
                .map(|index| (index as u8).wrapping_mul(29).wrapping_add(7))
                .collect();
            let proof_body_digest = verifier_proof_body_digest_v1(&proof_body, sha256);
            let statement_digest = atomic_payment_statement_digest_v4(&statement, sha256).unwrap();
            let envelope = HistoricalAnchorEnvelopeV1 {
                transition_kind: PoolV1TransitionKind::PrivateTransfer,
                pool: statement.pool,
                deployment_domain: statement.deployment_domain,
                anchor_sequence: statement.sequence,
                anchor_root: statement.spend.anchor,
                nullifier: statement.spend.nullifier,
                verifier_profile: V7_POOL_TAG73_PROFILE_BINDING,
                verifier_release: V7_RELEASE_BINDING,
            };
            let payload = encode_v7_pool_tag73_profile_payload_v1(
                &V7PoolTag73ProfilePayloadV1 {
                    frontier_nodes: V7_POOL_TAG73_FRONTIER_NODES,
                    proof_body_length: V7_POOL_TAG73_PROOF_BODY_BYTES,
                    proof_body_digest,
                    verifier_program: program_id.to_bytes(),
                    release_binding: V7_RELEASE_BINDING,
                    attempt_id: proof_key.to_bytes(),
                    statement_digest,
                    statement: statement.clone(),
                    check_pow: true,
                },
                sha256,
            )
            .unwrap();
            let binding = verifier_dispatch_binding_from_envelope_v1(
                program_id.to_bytes(),
                &envelope,
                &payload,
                proof_key.to_bytes(),
                proof_body_digest,
                V7_POOL_TAG73_PROOF_BODY_BYTES,
                sha256,
            )
            .unwrap();
            let request = encode_verifier_dispatch_request_v1(
                &VerifierDispatchRequestV1 {
                    binding,
                    statement_payload: &payload,
                },
                sha256,
            )
            .unwrap();
            let mut unsealed_proof_data = vec![
                0u8;
                POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES
                    + V7_POOL_TAG73_PROOF_BODY_BYTES as usize
            ];
            unsealed_proof_data[..4].copy_from_slice(&POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC);
            unsealed_proof_data[4..8]
                .copy_from_slice(&V7_POOL_TAG73_PROOF_BODY_BYTES.to_le_bytes());
            unsealed_proof_data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32]
                .copy_from_slice(upload_authority.as_ref());
            unsealed_proof_data[POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES..]
                .copy_from_slice(&proof_body);
            Self {
                program_id,
                proof_key,
                upload_authority,
                statement,
                request,
                proof_body,
                unsealed_proof_data,
            }
        }

        fn request(&self) -> VerifierDispatchRequestV1<'_> {
            decode_verifier_dispatch_request_v1(&self.request, sha256).unwrap()
        }

        fn receipt_address_and_inputs(&self) -> (Pubkey, PoolV1AuthorizationReceiptPdaInputsV1) {
            canonical_receipt_pda_for_binding(&self.program_id, &self.request(), sha256).unwrap()
        }

        fn pending_image(&self) -> [u8; POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES] {
            let request = self.request();
            let (_, inputs) = self.receipt_address_and_inputs();
            initialize_pool_v1_authorization_receipt_account_v1(
                &request,
                self.proof_key.to_bytes(),
                self.upload_authority.to_bytes(),
                Some(self.upload_authority.to_bytes()),
                self.upload_authority.to_bytes(),
                inputs.bump,
                sha256,
            )
            .unwrap()
        }

        fn finalized_image(&self, slot: u64) -> [u8; POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES] {
            let request = self.request();
            let pending = self.pending_image();
            let decoded =
                decode_pool_v1_authorization_receipt_account_v1(&pending, sha256).unwrap();
            finalize_pool_v1_authorization_receipt_account_v1(
                &pending,
                &request,
                &PoolV1AuthorizationReceiptV1 {
                    pda_bump: decoded.pda_bump,
                    verified_slot: slot,
                    binding: request.binding,
                },
                sha256,
            )
            .unwrap()
        }
    }

    struct NativeFixture {
        program_id: Pubkey,
        proof_key: Pubkey,
        upload_authority: Pubkey,
        pool: [u8; 32],
        deployment_domain: [u8; 32],
        anchor_sequence: u64,
        anchor_root: aspis_statement::Digest,
        nullifier: aspis_statement::Digest,
        destination_token_account: [u8; 32],
        proof_body: Vec<u8>,
        unsealed_proof_data: Vec<u8>,
    }

    impl NativeFixture {
        fn new() -> Self {
            let program_id = crate::id();
            let proof_key = Pubkey::new_unique();
            let upload_authority = Pubkey::new_unique();
            let proof_body_length =
                v7_pool_native_tag73_proof_body_bytes(V7_POOL_NATIVE_TAG73_MIN_FRONTIER_NODES)
                    .unwrap();
            let proof_body: Vec<u8> = (0..proof_body_length as usize)
                .map(|index| (index as u8).wrapping_mul(31).wrapping_add(11))
                .collect();
            let mut unsealed_proof_data =
                vec![0u8; POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES + proof_body.len()];
            unsealed_proof_data[..4].copy_from_slice(&POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC);
            unsealed_proof_data[4..8].copy_from_slice(&proof_body_length.to_le_bytes());
            unsealed_proof_data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32]
                .copy_from_slice(upload_authority.as_ref());
            unsealed_proof_data[POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES..]
                .copy_from_slice(&proof_body);
            Self {
                program_id,
                proof_key,
                upload_authority,
                pool: Pubkey::new_unique().to_bytes(),
                deployment_domain: [0x54; 32],
                anchor_sequence: 19,
                anchor_root: digest(410),
                nullifier: digest(510),
                destination_token_account: Pubkey::new_unique().to_bytes(),
                proof_body,
                unsealed_proof_data,
            }
        }

        fn statement_payload(&self, kind: PoolV1TransitionKind) -> Vec<u8> {
            match kind {
                PoolV1TransitionKind::PrivateTransfer => {
                    encode_pool_v1_private_transfer_public_v1(&PoolV1PrivateTransferPublicV1 {
                        pool: self.pool,
                        deployment_domain: self.deployment_domain,
                        anchor_sequence: self.anchor_sequence,
                        anchor_root: self.anchor_root,
                        nullifier: self.nullifier,
                        asset_id: M31(23),
                        recipient_commitment: digest(610),
                        change_commitment: digest(710),
                    })
                    .unwrap()
                    .to_vec()
                }
                PoolV1TransitionKind::Withdrawal => {
                    encode_pool_v1_withdrawal_public_v1(&PoolV1WithdrawalPublicV1 {
                        pool: self.pool,
                        deployment_domain: self.deployment_domain,
                        anchor_sequence: self.anchor_sequence,
                        anchor_root: self.anchor_root,
                        nullifier: self.nullifier,
                        asset_id: M31(23),
                        amount: 9,
                        destination_token_account: self.destination_token_account,
                        change_commitment: digest(710),
                    })
                    .unwrap()
                    .to_vec()
                }
            }
        }

        fn request_with_bindings(
            &self,
            kind: PoolV1TransitionKind,
            profile_binding: [u8; 32],
            release_binding: [u8; 32],
        ) -> Vec<u8> {
            let statement = self.statement_payload(kind);
            let envelope = HistoricalAnchorEnvelopeV1 {
                transition_kind: kind,
                pool: self.pool,
                deployment_domain: self.deployment_domain,
                anchor_sequence: self.anchor_sequence,
                anchor_root: self.anchor_root,
                nullifier: self.nullifier,
                verifier_profile: profile_binding,
                verifier_release: release_binding,
            };
            let binding = verifier_dispatch_binding_from_envelope_v1(
                self.program_id.to_bytes(),
                &envelope,
                &statement,
                self.proof_key.to_bytes(),
                verifier_proof_body_digest_v1(&self.proof_body, sha256),
                self.proof_body.len() as u32,
                sha256,
            )
            .unwrap();
            encode_verifier_dispatch_request_v1(
                &VerifierDispatchRequestV1 {
                    binding,
                    statement_payload: &statement,
                },
                sha256,
            )
            .unwrap()
        }

        fn request(&self, kind: PoolV1TransitionKind) -> Vec<u8> {
            self.request_with_bindings(
                kind,
                V7_POOL_NATIVE_TAG73_PROFILE_BINDING,
                V7_POOL_NATIVE_TAG73_RELEASE_BINDING,
            )
        }

        fn receipt_address_and_inputs(
            &self,
            request: &[u8],
        ) -> (Pubkey, PoolV1AuthorizationReceiptPdaInputsV1) {
            let request = decode_verifier_dispatch_request_v1(request, sha256).unwrap();
            canonical_receipt_pda_for_binding(&self.program_id, &request, sha256).unwrap()
        }
    }

    #[test]
    fn tags_layout_and_prefunded_plan_are_exact() {
        assert_eq!(
            [
                V7_POOL_RECEIPT_INITIALIZE_TAG,
                V7_POOL_RECEIPT_FINALIZE_TAG,
                V7_POOL_RECEIPT_CLOSE_TAG,
            ],
            [74, 75, 76]
        );
        assert_eq!(POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES, 720);
        assert_eq!(
            receipt_account_preparation_v1(0, 5_000),
            ReceiptAccountPreparationV1::Create {
                required_lamports: 5_000
            }
        );
        assert_eq!(
            receipt_account_preparation_v1(1_250, 5_000),
            ReceiptAccountPreparationV1::AllocateAssign {
                transfer_lamports: 3_750
            }
        );
        assert_eq!(
            receipt_account_preparation_v1(8_000, 5_000),
            ReceiptAccountPreparationV1::AllocateAssign {
                transfer_lamports: 0
            }
        );
    }

    fn run_initialize(
        fixture: &Fixture,
        proof_data: &mut [u8],
        receipt_key: Pubkey,
        authority_signer: bool,
        runtime_error: Option<ProgramError>,
    ) -> (ProgramResult, usize, Option<Vec<u8>>) {
        let system_id = system_program::id();
        let native_loader = NATIVE_LOADER_ID;
        let mut proof_lamports = 1;
        let mut receipt_lamports = 0;
        let mut authority_lamports = 50_000;
        let mut system_lamports = 1;
        let mut receipt_data = [];
        let mut authority_data = [];
        let mut system_data = [];
        let proof = AccountInfo::new(
            &fixture.proof_key,
            false,
            false,
            &mut proof_lamports,
            proof_data,
            &fixture.program_id,
            false,
            Epoch::default(),
        );
        let receipt = AccountInfo::new(
            &receipt_key,
            false,
            true,
            &mut receipt_lamports,
            &mut receipt_data,
            &system_id,
            false,
            Epoch::default(),
        );
        let authority = AccountInfo::new(
            &fixture.upload_authority,
            authority_signer,
            true,
            &mut authority_lamports,
            &mut authority_data,
            &system_id,
            false,
            Epoch::default(),
        );
        let system = AccountInfo::new(
            &system_id,
            false,
            false,
            &mut system_lamports,
            &mut system_data,
            &native_loader,
            true,
            Epoch::default(),
        );
        let calls = Cell::new(0);
        let captured = RefCell::new(None);
        let result = process_v7_pool_receipt_initialize_with_runtime(
            &fixture.program_id,
            &[proof, receipt, authority, system],
            &fixture.request,
            sha256,
            |space| {
                assert_eq!(space, 720);
                Ok(5_000)
            },
            |program_id, receipt, authority, system, inputs, plan, pending| {
                calls.set(calls.get() + 1);
                assert_eq!(program_id, &fixture.program_id);
                assert_eq!(receipt.key, &receipt_key);
                assert_eq!(authority.key, &fixture.upload_authority);
                assert_eq!(system.key, &system_id);
                assert_eq!(inputs, &fixture.receipt_address_and_inputs().1);
                assert_eq!(
                    plan,
                    ReceiptAccountPreparationV1::Create {
                        required_lamports: 5_000
                    }
                );
                *captured.borrow_mut() = Some(pending.to_vec());
                match runtime_error {
                    Some(error) => Err(error),
                    None => Ok(()),
                }
            },
        );
        (result, calls.get(), captured.into_inner())
    }

    #[test]
    fn initialize_binds_full_unsealed_upload_authority_pda_and_zero_pending_body() {
        let fixture = Fixture::new();
        let (receipt_key, inputs) = fixture.receipt_address_and_inputs();
        let mut proof_data = fixture.unsealed_proof_data.clone();
        let before = proof_data.clone();
        let (result, calls, captured) =
            run_initialize(&fixture, &mut proof_data, receipt_key, true, None);
        assert_eq!(result, Ok(()));
        assert_eq!(calls, 1);
        assert_eq!(proof_data, before);
        let pending = captured.unwrap();
        assert_eq!(pending.len(), 720);
        assert_eq!(&pending[..4], b"ASRA");
        assert!(pending[256..688].iter().all(|byte| *byte == 0));
        let decoded = decode_pool_v1_authorization_receipt_account_v1(&pending, sha256).unwrap();
        assert_eq!(
            decoded.status,
            PoolV1AuthorizationReceiptAccountStatusV1::Pending
        );
        assert_eq!(decoded.pda_inputs(), inputs);
        assert_eq!(
            decoded.proof_upload_authority,
            fixture.upload_authority.to_bytes()
        );
        assert_eq!(
            decoded.close_refund_authority,
            fixture.upload_authority.to_bytes()
        );
    }

    #[test]
    fn initialize_rejections_never_reach_system_runtime_or_mutate_upload() {
        let fixture = Fixture::new();
        let (receipt_key, _) = fixture.receipt_address_and_inputs();

        let mut proof_data = fixture.unsealed_proof_data.clone();
        let before = proof_data.clone();
        let (result, calls, _) =
            run_initialize(&fixture, &mut proof_data, receipt_key, false, None);
        assert_eq!(result, Err(ProgramError::MissingRequiredSignature));
        assert_eq!(calls, 0);
        assert_eq!(proof_data, before);

        let mut proof_data = fixture.unsealed_proof_data.clone();
        let before = proof_data.clone();
        let (result, calls, _) =
            run_initialize(&fixture, &mut proof_data, Pubkey::new_unique(), true, None);
        assert_eq!(result, Err(ProgramError::InvalidSeeds));
        assert_eq!(calls, 0);
        assert_eq!(proof_data, before);

        let mut proof_data = fixture.unsealed_proof_data.clone();
        proof_data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32].fill(0);
        let before = proof_data.clone();
        let (result, calls, _) = run_initialize(&fixture, &mut proof_data, receipt_key, true, None);
        assert_eq!(result, Err(ProgramError::InvalidAccountData));
        assert_eq!(calls, 0);
        assert_eq!(proof_data, before);

        let mut proof_data = fixture.unsealed_proof_data.clone();
        let last = proof_data.len() - 1;
        proof_data[last] ^= 1;
        let before = proof_data.clone();
        let (result, calls, _) = run_initialize(&fixture, &mut proof_data, receipt_key, true, None);
        assert_eq!(result, Err(ProgramError::InvalidAccountData));
        assert_eq!(calls, 0);
        assert_eq!(proof_data, before);

        // An injected System failure propagates without any handler write;
        // Solana transaction rollback covers partial CPI internals.
        let mut proof_data = fixture.unsealed_proof_data.clone();
        let before = proof_data.clone();
        let error = ProgramError::Custom(91);
        let (result, calls, captured) = run_initialize(
            &fixture,
            &mut proof_data,
            receipt_key,
            true,
            Some(error.clone()),
        );
        assert_eq!(result, Err(error));
        assert_eq!(calls, 1);
        assert!(captured.is_some());
        assert_eq!(proof_data, before);
    }

    fn initialize_native_receipt(
        fixture: &NativeFixture,
        request: &[u8],
    ) -> [u8; POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES] {
        assert_eq!(request.len(), V7_POOL_NATIVE_TAG73_REQUEST_BYTES);
        let system_id = system_program::id();
        let native_loader = NATIVE_LOADER_ID;
        let (receipt_key, expected_inputs) = fixture.receipt_address_and_inputs(request);
        let mut proof_data = fixture.unsealed_proof_data.clone();
        let proof_before = proof_data.clone();
        let mut proof_lamports = 1;
        let mut receipt_lamports = 0;
        let mut authority_lamports = 50_000;
        let mut system_lamports = 1;
        let mut receipt_data = [];
        let mut authority_data = [];
        let mut system_data = [];
        let proof = AccountInfo::new(
            &fixture.proof_key,
            false,
            false,
            &mut proof_lamports,
            &mut proof_data,
            &fixture.program_id,
            false,
            Epoch::default(),
        );
        let receipt = AccountInfo::new(
            &receipt_key,
            false,
            true,
            &mut receipt_lamports,
            &mut receipt_data,
            &system_id,
            false,
            Epoch::default(),
        );
        let authority = AccountInfo::new(
            &fixture.upload_authority,
            true,
            true,
            &mut authority_lamports,
            &mut authority_data,
            &system_id,
            false,
            Epoch::default(),
        );
        let system = AccountInfo::new(
            &system_id,
            false,
            false,
            &mut system_lamports,
            &mut system_data,
            &native_loader,
            true,
            Epoch::default(),
        );
        let captured = RefCell::new(None);
        let result = process_v7_pool_receipt_initialize_with_runtime(
            &fixture.program_id,
            &[proof, receipt, authority, system],
            request,
            sha256,
            |_| Ok(5_000),
            |program_id, receipt, authority, system, inputs, plan, pending| {
                assert_eq!(program_id, &fixture.program_id);
                assert_eq!(receipt.key, &receipt_key);
                assert_eq!(authority.key, &fixture.upload_authority);
                assert_eq!(system.key, &system_id);
                assert_eq!(inputs, &expected_inputs);
                assert_eq!(
                    plan,
                    ReceiptAccountPreparationV1::Create {
                        required_lamports: 5_000,
                    },
                );
                captured.replace(Some(*pending));
                Ok(())
            },
        );
        assert_eq!(result, Ok(()));
        assert_eq!(proof_data, proof_before);
        captured.into_inner().unwrap()
    }

    fn finalize_native_receipt(
        fixture: &NativeFixture,
        receipt_key: Pubkey,
        pending: [u8; POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES],
        request: &[u8],
        verified_slot: u64,
    ) -> (
        ProgramResult,
        [u8; POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES],
        usize,
    ) {
        let mut proof_data = fixture.unsealed_proof_data.clone();
        proof_data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32].fill(0);
        let mut receipt_data = pending;
        let mut proof_lamports = 1;
        let mut receipt_lamports = 5_000;
        let proof = AccountInfo::new(
            &fixture.proof_key,
            false,
            false,
            &mut proof_lamports,
            &mut proof_data,
            &fixture.program_id,
            false,
            Epoch::default(),
        );
        let receipt = AccountInfo::new(
            &receipt_key,
            false,
            true,
            &mut receipt_lamports,
            &mut receipt_data,
            &fixture.program_id,
            false,
            Epoch::default(),
        );
        let verify_calls = Cell::new(0);
        let result = process_v7_pool_receipt_finalize_with_runtime(
            &fixture.program_id,
            &[proof, receipt],
            request,
            sha256,
            |program_id, accounts, instruction_data, hash| {
                verify_calls.set(verify_calls.get() + 1);
                let [proof] = accounts else {
                    return Err(ProgramError::InvalidArgument);
                };
                assert!(proof_account_finalized(&proof.try_borrow_data()?));
                let validated = validate_v7_pool_native_tag73_request_v1(
                    program_id,
                    proof,
                    instruction_data,
                    hash,
                )?;
                Ok(validated.request.binding)
            },
            || Ok(verified_slot),
        );
        (result, receipt_data, verify_calls.get())
    }

    #[test]
    fn native_receipt_tag74_seal_tag75_lifecycle_accepts_ascp_and_aswp() {
        for (index, kind) in [
            PoolV1TransitionKind::PrivateTransfer,
            PoolV1TransitionKind::Withdrawal,
        ]
        .into_iter()
        .enumerate()
        {
            let fixture = NativeFixture::new();
            let request = fixture.request(kind);
            let (receipt_key, _) = fixture.receipt_address_and_inputs(&request);
            let pending = initialize_native_receipt(&fixture, &request);
            let decoded_pending =
                decode_pool_v1_authorization_receipt_account_v1(&pending, sha256).unwrap();
            assert_eq!(
                decoded_pending.status,
                PoolV1AuthorizationReceiptAccountStatusV1::Pending,
            );
            let slot = 12_000 + index as u64;
            let (result, finalized, verify_calls) =
                finalize_native_receipt(&fixture, receipt_key, pending, &request, slot);
            assert_eq!(result, Ok(()));
            assert_eq!(verify_calls, 1);
            let decoded =
                decode_pool_v1_authorization_receipt_account_v1(&finalized, sha256).unwrap();
            assert_eq!(
                decoded.status,
                PoolV1AuthorizationReceiptAccountStatusV1::Verified,
            );
            assert_eq!(decoded.verified_slot, slot);
            assert_eq!(
                decoded.receipt.unwrap().binding,
                decode_verifier_dispatch_request_v1(&request, sha256)
                    .unwrap()
                    .binding,
            );
        }
    }

    #[test]
    fn native_receipt_tag75_cross_kind_profile_release_and_length_fail_byte_exact() {
        for kind in [
            PoolV1TransitionKind::PrivateTransfer,
            PoolV1TransitionKind::Withdrawal,
        ] {
            let fixture = NativeFixture::new();
            let request = fixture.request(kind);
            let (receipt_key, _) = fixture.receipt_address_and_inputs(&request);
            let pending = initialize_native_receipt(&fixture, &request);
            let other_kind = match kind {
                PoolV1TransitionKind::PrivateTransfer => PoolV1TransitionKind::Withdrawal,
                PoolV1TransitionKind::Withdrawal => PoolV1TransitionKind::PrivateTransfer,
            };
            let mut short_request = request.clone();
            short_request.pop();
            let rejected_requests = [
                fixture.request(other_kind),
                fixture.request_with_bindings(
                    kind,
                    [0x91; 32],
                    V7_POOL_NATIVE_TAG73_RELEASE_BINDING,
                ),
                fixture.request_with_bindings(
                    kind,
                    V7_POOL_NATIVE_TAG73_PROFILE_BINDING,
                    [0x92; 32],
                ),
                short_request,
            ];
            for rejected in rejected_requests {
                let (result, after, verify_calls) =
                    finalize_native_receipt(&fixture, receipt_key, pending, &rejected, 12_100);
                assert!(result.is_err());
                assert_eq!(verify_calls, 0);
                assert_eq!(after, pending);
            }
        }
    }

    #[test]
    fn finalize_runs_full_tag73_helper_once_then_writes_current_slot_one_way() {
        let fixture = Fixture::new();
        let (receipt_key, _) = fixture.receipt_address_and_inputs();
        let mut proof_data = fixture.unsealed_proof_data.clone();
        proof_data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32].fill(0);
        let mut receipt_data = fixture.pending_image();
        let mut proof_lamports = 1;
        let mut receipt_lamports = 5_000;
        let proof = AccountInfo::new(
            &fixture.proof_key,
            false,
            false,
            &mut proof_lamports,
            &mut proof_data,
            &fixture.program_id,
            false,
            Epoch::default(),
        );
        let receipt = AccountInfo::new(
            &receipt_key,
            false,
            true,
            &mut receipt_lamports,
            &mut receipt_data,
            &fixture.program_id,
            false,
            Epoch::default(),
        );
        let verify_calls = Cell::new(0);
        let slot_calls = Cell::new(0);
        let result = process_v7_pool_receipt_finalize_with_runtime(
            &fixture.program_id,
            &[proof, receipt],
            &fixture.request,
            sha256,
            |program_id, accounts, instruction_data, hash| {
                verify_v7_pool_tag73_asvq_with_runtime(
                    program_id,
                    accounts,
                    instruction_data,
                    hash,
                    |proof,
                     frontier_nodes,
                     program_id,
                     release_binding,
                     attempt_id,
                     statement,
                     _,
                     check_pow| {
                        verify_calls.set(verify_calls.get() + 1);
                        assert_eq!(proof, fixture.proof_body);
                        assert_eq!(frontier_nodes, usize::from(V7_POOL_TAG73_FRONTIER_NODES));
                        assert_eq!(program_id, &fixture.program_id);
                        assert_eq!(release_binding, V7_RELEASE_BINDING);
                        assert_eq!(attempt_id, &fixture.proof_key);
                        assert_eq!(statement, &fixture.statement);
                        assert!(check_pow);
                        Ok(())
                    },
                )
            },
            || {
                slot_calls.set(slot_calls.get() + 1);
                Ok(9_001)
            },
        );
        assert_eq!(result, Ok(()));
        assert_eq!(verify_calls.get(), 1);
        assert_eq!(slot_calls.get(), 1);
        let finalized =
            decode_pool_v1_authorization_receipt_account_v1(&receipt_data, sha256).unwrap();
        assert_eq!(
            finalized.status,
            PoolV1AuthorizationReceiptAccountStatusV1::Verified
        );
        assert_eq!(finalized.verified_slot, 9_001);
        assert_eq!(
            finalized.receipt.unwrap().binding,
            fixture.request().binding
        );

        let before = receipt_data;
        let mut proof_data = fixture.unsealed_proof_data.clone();
        proof_data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32].fill(0);
        let mut receipt_data = before;
        let mut proof_lamports = 1;
        let mut receipt_lamports = 5_000;
        let proof = AccountInfo::new(
            &fixture.proof_key,
            false,
            false,
            &mut proof_lamports,
            &mut proof_data,
            &fixture.program_id,
            false,
            Epoch::default(),
        );
        let receipt = AccountInfo::new(
            &receipt_key,
            false,
            true,
            &mut receipt_lamports,
            &mut receipt_data,
            &fixture.program_id,
            false,
            Epoch::default(),
        );
        let called = Cell::new(false);
        let result = process_v7_pool_receipt_finalize_with_runtime(
            &fixture.program_id,
            &[proof, receipt],
            &fixture.request,
            sha256,
            |_, _, _, _| {
                called.set(true);
                Ok(fixture.request().binding)
            },
            || Ok(9_002),
        );
        assert_eq!(result, Err(ProgramError::InvalidAccountData));
        assert!(!called.get());
        assert_eq!(receipt_data, before);
    }

    #[test]
    fn verifier_failure_leaves_pending_receipt_byte_exact() {
        let fixture = Fixture::new();
        let (receipt_key, _) = fixture.receipt_address_and_inputs();
        let mut proof_data = fixture.unsealed_proof_data.clone();
        proof_data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32].fill(0);
        let mut receipt_data = fixture.pending_image();
        let before = receipt_data;
        let mut proof_lamports = 1;
        let mut receipt_lamports = 5_000;
        let proof = AccountInfo::new(
            &fixture.proof_key,
            false,
            false,
            &mut proof_lamports,
            &mut proof_data,
            &fixture.program_id,
            false,
            Epoch::default(),
        );
        let receipt = AccountInfo::new(
            &receipt_key,
            false,
            true,
            &mut receipt_lamports,
            &mut receipt_data,
            &fixture.program_id,
            false,
            Epoch::default(),
        );
        let slot_called = Cell::new(false);
        let result = process_v7_pool_receipt_finalize_with_runtime(
            &fixture.program_id,
            &[proof, receipt],
            &fixture.request,
            sha256,
            |_, _, _, _| Err(ProgramError::Custom(92)),
            || {
                slot_called.set(true);
                Ok(9_001)
            },
        );
        assert_eq!(result, Err(ProgramError::Custom(92)));
        assert!(!slot_called.get());
        assert_eq!(receipt_data, before);
    }

    fn run_close(
        fixture: &Fixture,
        receipt_key: Pubkey,
        authority_key: Pubkey,
        authority_signer: bool,
        mut receipt_data: [u8; POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES],
        receipt_balance: u64,
        refund_balance: u64,
    ) -> (ProgramResult, Vec<u8>, u64, u64, bool) {
        let system_id = system_program::id();
        let mut receipt_lamports = receipt_balance;
        let mut refund_lamports = refund_balance;
        let mut refund_data = [];
        let receipt = AccountInfo::new(
            &receipt_key,
            false,
            true,
            &mut receipt_lamports,
            &mut receipt_data,
            &fixture.program_id,
            false,
            Epoch::default(),
        );
        let refund = AccountInfo::new(
            &authority_key,
            authority_signer,
            true,
            &mut refund_lamports,
            &mut refund_data,
            &system_id,
            false,
            Epoch::default(),
        );
        let observed = Cell::new(false);
        let result = close_receipt_with_observer(
            &fixture.program_id,
            &[receipt, refund],
            &[],
            sha256,
            |data| {
                assert_eq!(&data[..4], &V7_POOL_RECEIPT_CLOSED_MAGIC);
                assert!(data[4..].iter().all(|byte| *byte == 0));
                observed.set(true);
            },
        );
        (
            result,
            receipt_data.to_vec(),
            receipt_lamports,
            refund_lamports,
            observed.get(),
        )
    }

    #[test]
    fn close_pending_or_verified_is_authority_exact_and_tombstones_before_drain() {
        let fixture = Fixture::new();
        let (receipt_key, _) = fixture.receipt_address_and_inputs();
        for image in [fixture.pending_image(), fixture.finalized_image(9_001)] {
            let (result, data, receipt_lamports, refund_lamports, observed) = run_close(
                &fixture,
                receipt_key,
                fixture.upload_authority,
                true,
                image,
                5_000,
                700,
            );
            assert_eq!(result, Ok(()));
            assert!(observed);
            assert_eq!(&data[..4], &V7_POOL_RECEIPT_CLOSED_MAGIC);
            assert!(data[4..].iter().all(|byte| *byte == 0));
            assert_eq!(receipt_lamports, 0);
            assert_eq!(refund_lamports, 5_700);
        }
    }

    #[test]
    fn close_rejections_preserve_exact_data_and_lamports() {
        let fixture = Fixture::new();
        let (receipt_key, _) = fixture.receipt_address_and_inputs();
        let original = fixture.pending_image();
        for (key, authority, signer, receipt_balance, refund_balance, expected) in [
            (
                Pubkey::new_unique(),
                fixture.upload_authority,
                true,
                5_000,
                700,
                ProgramError::InvalidSeeds,
            ),
            (
                receipt_key,
                Pubkey::new_unique(),
                true,
                5_000,
                700,
                ProgramError::InvalidArgument,
            ),
            (
                receipt_key,
                fixture.upload_authority,
                false,
                5_000,
                700,
                ProgramError::MissingRequiredSignature,
            ),
            (
                receipt_key,
                fixture.upload_authority,
                true,
                0,
                700,
                ProgramError::InvalidAccountData,
            ),
            (
                receipt_key,
                fixture.upload_authority,
                true,
                5_000,
                u64::MAX,
                ProgramError::ArithmeticOverflow,
            ),
        ] {
            let (result, data, after_receipt, after_refund, observed) = run_close(
                &fixture,
                key,
                authority,
                signer,
                original,
                receipt_balance,
                refund_balance,
            );
            assert_eq!(result, Err(expected));
            assert!(!observed);
            assert_eq!(data, original);
            assert_eq!(after_receipt, receipt_balance);
            assert_eq!(after_refund, refund_balance);
        }
    }
}
