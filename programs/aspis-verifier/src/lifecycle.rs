//! Proof-account and pool-account lifecycle (wire tags 0, 1, 62, 63, 64).
//!
//! Proof account layout:
//! [0..4] magic "ASPU", [4..8] proof_len u32 LE, [8..40] upload authority,
//! [40..40+proof_len] proof bytes.
//!
//! Finalization (tag 62) irreversibly zeroes the upload-authority field; the
//! production verification tags accept only sealed accounts. Closing
//! (tag 64) refunds every lamport of a sealed account and tombstones it.
//! Under the default-off authenticated-counter audit, a specialized seal keeps
//! that production header byte-exact, zeroes its authority normally, and fills
//! a reserved 36-byte `ASC || counter || statement_digest` trailer after the
//! declared proof body. The proof body and its offsets do not change. Only the
//! verifier program can perform either irreversible seal.

use solana_program::{
    account_info::{next_account_info, AccountInfo},
    entrypoint::ProgramResult,
    hash::hash,
    log::sol_log_data,
    program_error::ProgramError,
    pubkey::Pubkey,
};

use crate::atomic_payment;

pub(crate) const PROOF_ACCOUNT_MAGIC: [u8; 4] = *b"ASPU";
#[cfg(feature = "v7-pair-forest-authenticated-query-counter-audit")]
pub(crate) const PROOF_ACCOUNT_AUTHENTICATED_COUNTER_PREFIX: [u8; 3] = *b"ASC";
#[cfg(feature = "v7-pair-forest-authenticated-query-counter-audit")]
pub const PROOF_ACCOUNT_AUTHENTICATED_COUNTER_TRAILER_LEN: usize = 36;
pub const PROOF_ACCOUNT_HEADER_LEN: usize = 40;
pub(crate) const AUTHORITY_OFFSET: usize = 8;

pub(crate) fn proof_account_initialized(data: &[u8]) -> bool {
    data.len() >= PROOF_ACCOUNT_HEADER_LEN && data[0..4] == PROOF_ACCOUNT_MAGIC
}

pub(crate) fn proof_account_finalized(data: &[u8]) -> bool {
    let sealed = proof_account_initialized(data)
        && data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32]
            .iter()
            .all(|byte| *byte == 0);
    #[cfg(feature = "v7-pair-forest-authenticated-query-counter-audit")]
    {
        if !sealed {
            return false;
        }
        let declared = u32::from_le_bytes(data[4..8].try_into().unwrap()) as usize;
        PROOF_ACCOUNT_HEADER_LEN.checked_add(declared) == Some(data.len())
    }
    #[cfg(not(feature = "v7-pair-forest-authenticated-query-counter-audit"))]
    {
        sealed
    }
}

#[cfg(feature = "v7-pair-forest-authenticated-query-counter-audit")]
pub(crate) fn proof_account_has_authenticated_query_counter(data: &[u8]) -> bool {
    if !proof_account_initialized(data)
        || data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32]
            .iter()
            .any(|byte| *byte != 0)
    {
        return false;
    }
    let declared = u32::from_le_bytes(data[4..8].try_into().unwrap()) as usize;
    let Some(trailer_start) = PROOF_ACCOUNT_HEADER_LEN.checked_add(declared) else {
        return false;
    };
    let Some(expected_len) =
        trailer_start.checked_add(PROOF_ACCOUNT_AUTHENTICATED_COUNTER_TRAILER_LEN)
    else {
        return false;
    };
    data.len() == expected_len
        && data[trailer_start..trailer_start + 3] == PROOF_ACCOUNT_AUTHENTICATED_COUNTER_PREFIX
        && usize::from(data[trailer_start + 3])
            < aspis_core::v7_onefold::V7_COMPACT_QUERY_CANDIDATES
}

/// Return the exact counter only when the immutable proof-account seal binds
/// it to the caller's complete 256-bit statement digest.
#[cfg(feature = "v7-pair-forest-authenticated-query-counter-audit")]
pub(crate) fn authenticated_query_counter(
    data: &[u8],
    statement_digest: &[u8; 32],
) -> Result<u8, ProgramError> {
    if !proof_account_has_authenticated_query_counter(data) {
        return Err(ProgramError::InvalidAccountData);
    }
    let declared = u32::from_le_bytes(data[4..8].try_into().unwrap()) as usize;
    let trailer_start = PROOF_ACCOUNT_HEADER_LEN + declared;
    if data[trailer_start + 4..trailer_start + PROOF_ACCOUNT_AUTHENTICATED_COUNTER_TRAILER_LEN]
        != statement_digest[..]
    {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(data[trailer_start + 3])
}

/// Irreversibly replace an authorized upload header with the authenticated
/// counter seal. The caller must first run `require_upload_authority` and the
/// unchanged full verifier against the same account, statement, and digest.
#[cfg(feature = "v7-pair-forest-authenticated-query-counter-audit")]
pub(crate) fn write_authenticated_query_counter_seal(
    data: &mut [u8],
    counter: u8,
    statement_digest: &[u8; 32],
) -> ProgramResult {
    if !proof_account_initialized(data)
        || data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32]
            .iter()
            .all(|byte| *byte == 0)
        || usize::from(counter) >= aspis_core::v7_onefold::V7_COMPACT_QUERY_CANDIDATES
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let declared = u32::from_le_bytes(data[4..8].try_into().unwrap()) as usize;
    let trailer_start = PROOF_ACCOUNT_HEADER_LEN
        .checked_add(declared)
        .ok_or(ProgramError::InvalidAccountData)?;
    if trailer_start.checked_add(PROOF_ACCOUNT_AUTHENTICATED_COUNTER_TRAILER_LEN)
        != Some(data.len())
        || data[trailer_start..].iter().any(|byte| *byte != 0)
    {
        return Err(ProgramError::InvalidAccountData);
    }
    data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32].fill(0);
    data[trailer_start..trailer_start + 3]
        .copy_from_slice(&PROOF_ACCOUNT_AUTHENTICATED_COUNTER_PREFIX);
    data[trailer_start + 3] = counter;
    data[trailer_start + 4..].copy_from_slice(statement_digest);
    Ok(())
}

pub(crate) fn proof_len(data: &[u8]) -> Result<usize, ProgramError> {
    if !proof_account_initialized(data) {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(u32::from_le_bytes(data[4..8].try_into().unwrap()) as usize)
}

pub(crate) fn uploaded_proof_bounds(data: &[u8]) -> Result<(usize, usize), ProgramError> {
    let total_len = proof_len(data)?;
    let proof_end = PROOF_ACCOUNT_HEADER_LEN
        .checked_add(total_len)
        .ok_or(ProgramError::InvalidAccountData)?;
    if proof_end > data.len() {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok((PROOF_ACCOUNT_HEADER_LEN, proof_end))
}

pub(crate) fn require_upload_authority(data: &[u8], authority: &AccountInfo) -> ProgramResult {
    if !authority.is_signer {
        return Err(ProgramError::MissingRequiredSignature);
    }
    if data.len() < PROOF_ACCOUNT_HEADER_LEN || data[0..4] != PROOF_ACCOUNT_MAGIC {
        return Err(ProgramError::InvalidAccountData);
    }
    if data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32] != authority.key.to_bytes() {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}

pub(crate) fn log_uploaded_proof_sha256(proof_account: &AccountInfo) -> ProgramResult {
    let data = proof_account.try_borrow_data()?;
    let (start, end) = uploaded_proof_bounds(&data)?;
    let digest = hash(&data[start..end]);
    sol_log_data(&[b"aspis-proof-sha256-v1", digest.as_ref()]);
    Ok(())
}

/// Wire tag 0: initialize (or re-key under the same authority) a proof
/// account. The account must be pre-created with owner = this program and
/// space >= header + total_len.
pub(crate) fn init_proof(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    total_len: u32,
) -> ProgramResult {
    let account_iter = &mut accounts.iter();
    let proof_account = next_account_info(account_iter)?;
    let authority = next_account_info(account_iter)?;
    if proof_account.owner != program_id {
        return Err(ProgramError::IncorrectProgramId);
    }
    if !authority.is_signer {
        return Err(ProgramError::MissingRequiredSignature);
    }
    if !proof_account.is_writable {
        return Err(ProgramError::InvalidAccountData);
    }
    let mut data = proof_account.try_borrow_mut_data()?;
    let required_len = PROOF_ACCOUNT_HEADER_LEN
        .checked_add(total_len as usize)
        .ok_or(ProgramError::InvalidInstructionData)?;
    if data.len() < required_len {
        return Err(ProgramError::AccountDataTooSmall);
    }
    if proof_account_initialized(&data) {
        if data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32] != authority.key.to_bytes() {
            return Err(ProgramError::InvalidAccountData);
        }
    } else {
        if !proof_account.is_signer {
            return Err(ProgramError::MissingRequiredSignature);
        }
        if !data.iter().all(|byte| *byte == 0) {
            return Err(ProgramError::InvalidAccountData);
        }
    }
    data[0..4].copy_from_slice(&PROOF_ACCOUNT_MAGIC);
    data[4..8].copy_from_slice(&total_len.to_le_bytes());
    data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32].copy_from_slice(authority.key.as_ref());
    Ok(())
}

/// Wire tag 1: copy one chunk into the proof body at `offset`.
pub(crate) fn upload_chunk(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    offset: u32,
    chunk: &[u8],
) -> ProgramResult {
    let account_iter = &mut accounts.iter();
    let proof_account = next_account_info(account_iter)?;
    let authority = next_account_info(account_iter)?;
    if proof_account.owner != program_id {
        return Err(ProgramError::IncorrectProgramId);
    }
    if !proof_account.is_writable {
        return Err(ProgramError::InvalidAccountData);
    }
    let mut data = proof_account.try_borrow_mut_data()?;
    require_upload_authority(&data, authority)?;
    let total_len = proof_len(&data)?;
    let relative_end = (offset as usize)
        .checked_add(chunk.len())
        .ok_or(ProgramError::InvalidInstructionData)?;
    let start = PROOF_ACCOUNT_HEADER_LEN
        .checked_add(offset as usize)
        .ok_or(ProgramError::InvalidInstructionData)?;
    let end = start
        .checked_add(chunk.len())
        .ok_or(ProgramError::InvalidInstructionData)?;
    if relative_end > total_len || end > data.len() {
        return Err(ProgramError::InvalidInstructionData);
    }
    data[start..end].copy_from_slice(chunk);
    Ok(())
}

/// Wire tag 62: irreversibly seal an uploaded proof account by replacing its
/// upload-authority field with the all-zero sentinel.
pub(crate) fn finalize_proof(program_id: &Pubkey, accounts: &[AccountInfo]) -> ProgramResult {
    let account_iter = &mut accounts.iter();
    let proof_account = next_account_info(account_iter)?;
    let authority = next_account_info(account_iter)?;
    if proof_account.owner != program_id {
        return Err(ProgramError::IncorrectProgramId);
    }
    if !proof_account.is_writable {
        return Err(ProgramError::InvalidAccountData);
    }
    let mut data = proof_account.try_borrow_mut_data()?;
    require_upload_authority(&data, authority)?;
    #[cfg(feature = "v7-pair-forest-authenticated-query-counter-audit")]
    {
        let (proof_start, proof_end) = uploaded_proof_bounds(&data)?;
        debug_assert_eq!(proof_start, PROOF_ACCOUNT_HEADER_LEN);
        if proof_end != data.len() {
            return Err(ProgramError::InvalidAccountData);
        }
    }
    data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32].fill(0);
    Ok(())
}

/// The maximum accepted deployment-domain tag length. Tags are short cluster
/// names (`b"mainnet-beta"`, `b"devnet"`), never structured payloads.
pub const DEPLOYMENT_DOMAIN_TAG_MAX_LEN: usize = 64;

/// Wire tag 63: initialize a newly created, program-owned pool account. The
/// pool key must sign, the exact 80-byte account must still be all zero, and
/// the initial anchor must be canonically encoded. The pool's deployment
/// domain is derived on-chain from the runtime program id and the supplied
/// nonempty domain tag, so no client can bind a pool to a foreign deployment.
pub(crate) fn initialize_atomic_pool(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    sequence: u64,
    anchor: [u8; 32],
    domain_tag: &[u8],
) -> ProgramResult {
    let pool_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    if pool_account.owner != program_id {
        return Err(ProgramError::IncorrectProgramId);
    }
    if !pool_account.is_signer {
        return Err(ProgramError::MissingRequiredSignature);
    }
    if !pool_account.is_writable {
        return Err(ProgramError::InvalidAccountData);
    }
    if domain_tag.is_empty() || domain_tag.len() > DEPLOYMENT_DOMAIN_TAG_MAX_LEN {
        return Err(ProgramError::InvalidInstructionData);
    }
    aspis_statement::decode_digest_canonical(&anchor)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    sequence
        .checked_add(1)
        .ok_or(ProgramError::ArithmeticOverflow)?;
    let deployment_domain = aspis_statement::atomic_deployment_domain(
        crate::verify::sbf_hashv,
        &program_id.to_bytes(),
        domain_tag,
    );
    let mut data = pool_account.try_borrow_mut_data()?;
    if data.len() != atomic_payment::ATOMIC_POOL_STATE_LEN || !data.iter().all(|byte| *byte == 0) {
        return Err(ProgramError::InvalidAccountData);
    }
    atomic_payment::AtomicPoolStateV2 {
        sequence,
        anchor,
        deployment_domain,
    }
    .encode(&mut data)
}

/// Wire tag 64: close a sealed proof account and refund every lamport to a
/// writable System account. Both accounts must sign.
pub(crate) fn close_proof(program_id: &Pubkey, accounts: &[AccountInfo]) -> ProgramResult {
    let account_iter = &mut accounts.iter();
    let proof_account = next_account_info(account_iter)?;
    let refund_account = next_account_info(account_iter)?;
    close_finalized_proof_account(program_id, proof_account, refund_account)
}

pub(crate) fn close_finalized_proof_account(
    program_id: &Pubkey,
    proof_account: &AccountInfo,
    refund_account: &AccountInfo,
) -> ProgramResult {
    let data = proof_account.try_borrow_data()?;
    uploaded_proof_bounds(&data)?;
    #[cfg(feature = "v7-pair-forest-authenticated-query-counter-audit")]
    let sealed =
        proof_account_finalized(&data) || proof_account_has_authenticated_query_counter(&data);
    #[cfg(not(feature = "v7-pair-forest-authenticated-query-counter-audit"))]
    let sealed = proof_account_finalized(&data);
    if !sealed {
        return Err(ProgramError::InvalidAccountData);
    }
    drop(data);
    atomic_payment::refund_program_owned_proof_account(program_id, proof_account, refund_account)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::atomic_payment;
    use crate::dispatch::process_spend_production_instruction as process_instruction;
    use crate::id;
    use crate::test_support::make_account;
    use crate::wire::AspisInstruction;
    use solana_program::program_error::ProgramError;

    #[test]
    fn init_requires_authority_signature() {
        let program_id = id();
        let proof_key = Pubkey::new_unique();
        let authority_key = Pubkey::new_unique();
        let mut proof_lamports = 0;
        let mut authority_lamports = 0;
        let mut proof_data = [0u8; PROOF_ACCOUNT_HEADER_LEN + 8];
        let mut authority_data = [];
        let proof = make_account(
            &proof_key,
            &program_id,
            &mut proof_lamports,
            &mut proof_data,
            true,
            true,
        );
        let authority = make_account(
            &authority_key,
            &program_id,
            &mut authority_lamports,
            &mut authority_data,
            false,
            false,
        );
        let ix = borsh::to_vec(&AspisInstruction::InitProof { total_len: 8 }).unwrap();
        assert_eq!(
            process_instruction(&program_id, &[proof, authority], &ix),
            Err(ProgramError::MissingRequiredSignature)
        );

        let proof = make_account(
            &proof_key,
            &program_id,
            &mut proof_lamports,
            &mut proof_data,
            true,
            false,
        );
        let authority = make_account(
            &authority_key,
            &program_id,
            &mut authority_lamports,
            &mut authority_data,
            true,
            false,
        );
        assert_eq!(
            process_instruction(&program_id, &[proof, authority], &ix),
            Err(ProgramError::InvalidAccountData)
        );
    }

    #[test]
    fn upload_rejects_wrong_authority() {
        let program_id = id();
        let proof_key = Pubkey::new_unique();
        let authority_key = Pubkey::new_unique();
        let wrong_key = Pubkey::new_unique();
        let mut proof_lamports = 0;
        let mut authority_lamports = 0;
        let mut wrong_lamports = 0;
        let mut proof_data = [0u8; PROOF_ACCOUNT_HEADER_LEN + 8];
        let mut authority_data = [];
        let mut wrong_data = [];

        let init_ix = borsh::to_vec(&AspisInstruction::InitProof { total_len: 8 }).unwrap();
        {
            let proof = make_account(
                &proof_key,
                &program_id,
                &mut proof_lamports,
                &mut proof_data,
                true,
                true,
            );
            let authority = make_account(
                &authority_key,
                &program_id,
                &mut authority_lamports,
                &mut authority_data,
                true,
                false,
            );
            assert_eq!(
                process_instruction(&program_id, &[proof, authority], &init_ix),
                Ok(())
            );
        }

        let upload_ix = borsh::to_vec(&AspisInstruction::UploadChunk {
            offset: 0,
            chunk: vec![1, 2, 3, 4],
        })
        .unwrap();
        let proof = make_account(
            &proof_key,
            &program_id,
            &mut proof_lamports,
            &mut proof_data,
            false,
            true,
        );
        let wrong = make_account(
            &wrong_key,
            &program_id,
            &mut wrong_lamports,
            &mut wrong_data,
            true,
            false,
        );
        assert_eq!(
            process_instruction(&program_id, &[proof, wrong], &upload_ix),
            Err(ProgramError::InvalidAccountData)
        );

        let proof = make_account(
            &proof_key,
            &program_id,
            &mut proof_lamports,
            &mut proof_data,
            false,
            false,
        );
        let authority = make_account(
            &authority_key,
            &program_id,
            &mut authority_lamports,
            &mut authority_data,
            true,
            false,
        );
        assert_eq!(
            process_instruction(&program_id, &[proof, authority], &upload_ix),
            Err(ProgramError::InvalidAccountData)
        );
    }

    #[test]
    fn finalize_proof_is_authority_bound_and_irreversible() {
        let program_id = id();
        let proof_key = Pubkey::new_unique();
        let authority_key = Pubkey::new_unique();
        let wrong_authority_key = Pubkey::new_unique();
        let mut proof_lamports = 0;
        let mut authority_lamports = 0;
        let mut wrong_authority_lamports = 0;
        let mut proof_data = [0u8; PROOF_ACCOUNT_HEADER_LEN + 8];
        let mut authority_data = [];
        let mut wrong_authority_data = [];

        let init = borsh::to_vec(&AspisInstruction::InitProof { total_len: 8 }).unwrap();
        {
            let proof = make_account(
                &proof_key,
                &program_id,
                &mut proof_lamports,
                &mut proof_data,
                true,
                true,
            );
            let authority = make_account(
                &authority_key,
                &program_id,
                &mut authority_lamports,
                &mut authority_data,
                true,
                false,
            );
            assert_eq!(
                process_instruction(&program_id, &[proof, authority], &init),
                Ok(())
            );
        }

        let initialize_pool = borsh::to_vec(&AspisInstruction::InitializeAtomicPool {
            sequence: 0,
            anchor: [0u8; 32],
            domain_tag: b"devnet".to_vec(),
        })
        .unwrap();
        {
            let proof = make_account(
                &proof_key,
                &program_id,
                &mut proof_lamports,
                &mut proof_data,
                true,
                true,
            );
            assert_eq!(
                process_instruction(&program_id, &[proof], &initialize_pool),
                Err(ProgramError::InvalidAccountData),
                "an initialized proof must not be retyped as a pool"
            );
        }

        let finalize = borsh::to_vec(&AspisInstruction::FinalizeProof).unwrap();
        {
            let proof = make_account(
                &proof_key,
                &program_id,
                &mut proof_lamports,
                &mut proof_data,
                false,
                true,
            );
            let wrong_authority = make_account(
                &wrong_authority_key,
                &program_id,
                &mut wrong_authority_lamports,
                &mut wrong_authority_data,
                true,
                false,
            );
            assert_eq!(
                process_instruction(&program_id, &[proof, wrong_authority], &finalize),
                Err(ProgramError::InvalidAccountData)
            );
        }
        {
            let proof = make_account(
                &proof_key,
                &program_id,
                &mut proof_lamports,
                &mut proof_data,
                false,
                false,
            );
            let authority = make_account(
                &authority_key,
                &program_id,
                &mut authority_lamports,
                &mut authority_data,
                true,
                false,
            );
            assert_eq!(
                process_instruction(&program_id, &[proof, authority], &finalize),
                Err(ProgramError::InvalidAccountData)
            );
        }
        {
            let proof = make_account(
                &proof_key,
                &program_id,
                &mut proof_lamports,
                &mut proof_data,
                false,
                true,
            );
            let authority = make_account(
                &authority_key,
                &program_id,
                &mut authority_lamports,
                &mut authority_data,
                true,
                false,
            );
            assert_eq!(
                process_instruction(&program_id, &[proof, authority], &finalize),
                Ok(())
            );
        }
        assert!(proof_account_finalized(&proof_data));

        let upload = borsh::to_vec(&AspisInstruction::UploadChunk {
            offset: 0,
            chunk: vec![1],
        })
        .unwrap();
        let proof = make_account(
            &proof_key,
            &program_id,
            &mut proof_lamports,
            &mut proof_data,
            false,
            true,
        );
        let authority = make_account(
            &authority_key,
            &program_id,
            &mut authority_lamports,
            &mut authority_data,
            true,
            false,
        );
        assert_eq!(
            process_instruction(&program_id, &[proof, authority], &upload),
            Err(ProgramError::InvalidAccountData)
        );

        let reinitialize = borsh::to_vec(&AspisInstruction::InitProof { total_len: 8 }).unwrap();
        {
            let proof = make_account(
                &proof_key,
                &program_id,
                &mut proof_lamports,
                &mut proof_data,
                true,
                true,
            );
            let authority = make_account(
                &authority_key,
                &program_id,
                &mut authority_lamports,
                &mut authority_data,
                true,
                false,
            );
            assert_eq!(
                process_instruction(&program_id, &[proof, authority], &reinitialize),
                Err(ProgramError::InvalidAccountData)
            );
        }
        {
            let proof = make_account(
                &proof_key,
                &program_id,
                &mut proof_lamports,
                &mut proof_data,
                false,
                true,
            );
            let authority = make_account(
                &authority_key,
                &program_id,
                &mut authority_lamports,
                &mut authority_data,
                true,
                false,
            );
            assert_eq!(
                process_instruction(&program_id, &[proof, authority], &finalize),
                Err(ProgramError::InvalidAccountData)
            );
        }
    }

    #[test]
    fn close_finalized_proof_refunds_exact_balance_and_tombstones_overallocation() {
        let program_id = id();
        let proof_key = Pubkey::new_unique();
        let refund_key = Pubkey::new_unique();
        let refund_owner = solana_program::system_program::id();
        let mut proof_lamports = 463_083_600;
        let mut refund_lamports = 25_000;
        let mut proof_data = [0u8; PROOF_ACCOUNT_HEADER_LEN + 12];
        proof_data[..4].copy_from_slice(&PROOF_ACCOUNT_MAGIC);
        proof_data[4..8].copy_from_slice(&8u32.to_le_bytes());
        proof_data[PROOF_ACCOUNT_HEADER_LEN..PROOF_ACCOUNT_HEADER_LEN + 8].fill(0x5a);
        let mut refund_data = [];
        let close = borsh::to_vec(&AspisInstruction::CloseFinalizedProof).unwrap();

        {
            let proof = make_account(
                &proof_key,
                &program_id,
                &mut proof_lamports,
                &mut proof_data,
                true,
                true,
            );
            let refund = make_account(
                &refund_key,
                &refund_owner,
                &mut refund_lamports,
                &mut refund_data,
                true,
                true,
            );
            assert_eq!(
                process_instruction(&program_id, &[proof, refund], &close),
                Ok(())
            );
        }
        assert_eq!(proof_lamports, 0);
        assert_eq!(refund_lamports, 463_108_600);
        assert_eq!(proof_data[..4], atomic_payment::PROOF_ACCOUNT_CLOSED_MAGIC);
        assert!(!proof_account_finalized(&proof_data));
    }

    #[test]
    fn close_finalized_proof_rejects_unsealed_unsigned_and_overflow_without_mutation() {
        let program_id = id();
        let proof_key = Pubkey::new_unique();
        let refund_key = Pubkey::new_unique();
        let refund_owner = solana_program::system_program::id();
        let close = borsh::to_vec(&AspisInstruction::CloseFinalizedProof).unwrap();

        for (sealed, signed, refund_balance, expected) in [
            (false, true, 7u64, ProgramError::InvalidAccountData),
            (true, false, 7u64, ProgramError::MissingRequiredSignature),
            (true, true, u64::MAX, ProgramError::ArithmeticOverflow),
        ] {
            let mut proof_lamports = 11u64;
            let mut refund_lamports = refund_balance;
            let mut proof_data = [0u8; PROOF_ACCOUNT_HEADER_LEN + 8];
            proof_data[..4].copy_from_slice(&PROOF_ACCOUNT_MAGIC);
            proof_data[4..8].copy_from_slice(&8u32.to_le_bytes());
            if !sealed {
                proof_data[AUTHORITY_OFFSET] = 1;
            }
            let proof_before = proof_data;
            let mut refund_data = [];
            {
                let proof = make_account(
                    &proof_key,
                    &program_id,
                    &mut proof_lamports,
                    &mut proof_data,
                    signed,
                    true,
                );
                let refund = make_account(
                    &refund_key,
                    &refund_owner,
                    &mut refund_lamports,
                    &mut refund_data,
                    true,
                    true,
                );
                assert_eq!(
                    process_instruction(&program_id, &[proof, refund], &close),
                    Err(expected)
                );
            }
            assert_eq!(proof_lamports, 11);
            assert_eq!(refund_lamports, refund_balance);
            assert_eq!(proof_data, proof_before);
        }
    }

    #[test]
    fn close_finalized_proof_rejects_every_unsafe_account_shape_without_mutation() {
        let program_id = id();
        let system_id = solana_program::system_program::id();
        let proof_key = Pubkey::new_unique();
        let refund_key = Pubkey::new_unique();
        let close = borsh::to_vec(&AspisInstruction::CloseFinalizedProof).unwrap();

        // proof owner, proof signer, proof writable, refund owner, refund
        // signer, refund writable, aliased keys, proof lamports, declared
        // proof bytes, expected error
        for (
            proof_owner,
            proof_signer,
            proof_writable,
            refund_owner,
            refund_signer,
            refund_writable,
            aliased,
            initial_proof_lamports,
            declared_len,
            expected,
        ) in [
            (
                system_id,
                true,
                true,
                system_id,
                true,
                true,
                false,
                11,
                8,
                ProgramError::IncorrectProgramId,
            ),
            (
                program_id,
                true,
                true,
                program_id,
                true,
                true,
                false,
                11,
                8,
                ProgramError::IncorrectProgramId,
            ),
            (
                program_id,
                true,
                true,
                system_id,
                false,
                true,
                false,
                11,
                8,
                ProgramError::MissingRequiredSignature,
            ),
            (
                program_id,
                true,
                false,
                system_id,
                true,
                true,
                false,
                11,
                8,
                ProgramError::InvalidAccountData,
            ),
            (
                program_id,
                true,
                true,
                system_id,
                true,
                false,
                false,
                11,
                8,
                ProgramError::InvalidAccountData,
            ),
            (
                program_id,
                true,
                true,
                system_id,
                true,
                true,
                true,
                11,
                8,
                ProgramError::InvalidArgument,
            ),
            (
                program_id,
                true,
                true,
                system_id,
                true,
                true,
                false,
                0,
                8,
                ProgramError::InvalidAccountData,
            ),
            (
                program_id,
                true,
                true,
                system_id,
                true,
                true,
                false,
                11,
                100,
                ProgramError::InvalidAccountData,
            ),
        ] {
            let mut proof_lamports = initial_proof_lamports;
            let mut refund_lamports = 7u64;
            let mut proof_data = [0u8; PROOF_ACCOUNT_HEADER_LEN + 8];
            proof_data[..4].copy_from_slice(&PROOF_ACCOUNT_MAGIC);
            proof_data[4..8].copy_from_slice(&(declared_len as u32).to_le_bytes());
            let proof_before = proof_data;
            let mut refund_data = [];
            {
                let proof = make_account(
                    &proof_key,
                    &proof_owner,
                    &mut proof_lamports,
                    &mut proof_data,
                    proof_signer,
                    proof_writable,
                );
                let effective_refund_key = if aliased { &proof_key } else { &refund_key };
                let refund = make_account(
                    effective_refund_key,
                    &refund_owner,
                    &mut refund_lamports,
                    &mut refund_data,
                    refund_signer,
                    refund_writable,
                );
                assert_eq!(
                    process_instruction(&program_id, &[proof, refund], &close),
                    Err(expected)
                );
            }
            assert_eq!(proof_lamports, initial_proof_lamports);
            assert_eq!(refund_lamports, 7);
            assert_eq!(proof_data, proof_before);
        }
    }

    #[test]
    fn initialize_atomic_pool_is_signed_canonical_and_one_shot() {
        let program_id = id();
        let pool_key = Pubkey::new_unique();
        let authority_key = Pubkey::new_unique();
        let mut pool_lamports = 0;
        let mut authority_lamports = 0;
        let mut pool_data = [0u8; atomic_payment::ATOMIC_POOL_STATE_LEN];
        let mut authority_data = [];
        let anchor = [0u8; 32];
        let initialize = borsh::to_vec(&AspisInstruction::InitializeAtomicPool {
            sequence: 73,
            anchor,
            domain_tag: b"devnet".to_vec(),
        })
        .unwrap();

        {
            let unsigned_pool = make_account(
                &pool_key,
                &program_id,
                &mut pool_lamports,
                &mut pool_data,
                false,
                true,
            );
            assert_eq!(
                process_instruction(&program_id, &[unsigned_pool], &initialize),
                Err(ProgramError::MissingRequiredSignature)
            );
        }
        {
            let pool = make_account(
                &pool_key,
                &program_id,
                &mut pool_lamports,
                &mut pool_data,
                true,
                true,
            );
            assert_eq!(
                process_instruction(&program_id, &[pool], &initialize),
                Ok(())
            );
        }
        assert_eq!(
            atomic_payment::AtomicPoolStateV2::decode(&pool_data).unwrap(),
            atomic_payment::AtomicPoolStateV2 {
                sequence: 73,
                anchor,
                deployment_domain: aspis_statement::atomic_deployment_domain(
                    crate::verify::sbf_hashv,
                    &program_id.to_bytes(),
                    b"devnet",
                ),
            }
        );

        // Rejected domain tags: empty and oversized both fail before any
        // account write.
        for bad_tag in [Vec::new(), vec![0x61u8; DEPLOYMENT_DOMAIN_TAG_MAX_LEN + 1]] {
            let bad_pool_key = Pubkey::new_unique();
            let mut bad_pool_lamports = 0;
            let mut bad_pool_data = [0u8; atomic_payment::ATOMIC_POOL_STATE_LEN];
            let bad_initialize = borsh::to_vec(&AspisInstruction::InitializeAtomicPool {
                sequence: 0,
                anchor,
                domain_tag: bad_tag,
            })
            .unwrap();
            let bad_pool = make_account(
                &bad_pool_key,
                &program_id,
                &mut bad_pool_lamports,
                &mut bad_pool_data,
                true,
                true,
            );
            assert_eq!(
                process_instruction(&program_id, &[bad_pool], &bad_initialize),
                Err(ProgramError::InvalidInstructionData)
            );
            assert!(bad_pool_data.iter().all(|byte| *byte == 0));
        }

        let pool = make_account(
            &pool_key,
            &program_id,
            &mut pool_lamports,
            &mut pool_data,
            true,
            true,
        );
        assert_eq!(
            process_instruction(&program_id, &[pool], &initialize),
            Err(ProgramError::InvalidAccountData)
        );

        let pool_before = pool_data;
        let init_proof = borsh::to_vec(&AspisInstruction::InitProof { total_len: 8 }).unwrap();
        let pool = make_account(
            &pool_key,
            &program_id,
            &mut pool_lamports,
            &mut pool_data,
            true,
            true,
        );
        let authority = make_account(
            &authority_key,
            &program_id,
            &mut authority_lamports,
            &mut authority_data,
            true,
            false,
        );
        assert_eq!(
            process_instruction(&program_id, &[pool, authority], &init_proof),
            Err(ProgramError::InvalidAccountData),
            "an initialized pool must not be retyped as a proof account"
        );
        assert_eq!(pool_data, pool_before);

        let overflow_pool_key = Pubkey::new_unique();
        let mut overflow_pool_lamports = 0;
        let mut overflow_pool_data = [0u8; atomic_payment::ATOMIC_POOL_STATE_LEN];
        let overflow_initialize = borsh::to_vec(&AspisInstruction::InitializeAtomicPool {
            sequence: u64::MAX,
            anchor,
            domain_tag: b"devnet".to_vec(),
        })
        .unwrap();
        let overflow_pool = make_account(
            &overflow_pool_key,
            &program_id,
            &mut overflow_pool_lamports,
            &mut overflow_pool_data,
            true,
            true,
        );
        assert_eq!(
            process_instruction(&program_id, &[overflow_pool], &overflow_initialize),
            Err(ProgramError::ArithmeticOverflow)
        );
        assert!(overflow_pool_data.iter().all(|byte| *byte == 0));
    }

    #[cfg(feature = "v7-pair-forest-authenticated-query-counter-audit")]
    #[test]
    fn ordinary_seal_cannot_strand_authenticated_counter_account() {
        let program_id = id();
        let proof_key = Pubkey::new_unique();
        let authority_key = Pubkey::new_unique();
        let mut proof_lamports = 0;
        let mut authority_lamports = 0;
        let mut proof_data =
            vec![
                0u8;
                PROOF_ACCOUNT_HEADER_LEN + 8 + PROOF_ACCOUNT_AUTHENTICATED_COUNTER_TRAILER_LEN
            ];
        let mut authority_data = [];

        let initialize = borsh::to_vec(&AspisInstruction::InitProof { total_len: 8 }).unwrap();
        {
            let proof = make_account(
                &proof_key,
                &program_id,
                &mut proof_lamports,
                &mut proof_data,
                true,
                true,
            );
            let authority = make_account(
                &authority_key,
                &program_id,
                &mut authority_lamports,
                &mut authority_data,
                true,
                false,
            );
            assert_eq!(
                process_instruction(&program_id, &[proof, authority], &initialize),
                Ok(())
            );
        }
        let finalize = borsh::to_vec(&AspisInstruction::FinalizeProof).unwrap();
        {
            let proof = make_account(
                &proof_key,
                &program_id,
                &mut proof_lamports,
                &mut proof_data,
                false,
                true,
            );
            let authority = make_account(
                &authority_key,
                &program_id,
                &mut authority_lamports,
                &mut authority_data,
                true,
                false,
            );
            assert_eq!(
                process_instruction(&program_id, &[proof, authority], &finalize),
                Err(ProgramError::InvalidAccountData)
            );
        }
        assert_eq!(
            &proof_data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32],
            authority_key.as_ref(),
            "ordinary sealing must leave specialized account authority intact"
        );
        assert!(!proof_account_finalized(&proof_data));
        assert!(!proof_account_has_authenticated_query_counter(&proof_data));
    }

    #[cfg(feature = "v7-pair-forest-authenticated-query-counter-audit")]
    #[test]
    fn authenticated_counter_seal_is_statement_bound_immutable_and_body_preserving() {
        let authority = [0x61u8; 32];
        let statement_digest = [0x73u8; 32];
        let mut data =
            vec![
                0u8;
                PROOF_ACCOUNT_HEADER_LEN + 19 + PROOF_ACCOUNT_AUTHENTICATED_COUNTER_TRAILER_LEN
            ];
        data[..4].copy_from_slice(&PROOF_ACCOUNT_MAGIC);
        data[4..8].copy_from_slice(&19u32.to_le_bytes());
        data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32].copy_from_slice(&authority);
        data[PROOF_ACCOUNT_HEADER_LEN..PROOF_ACCOUNT_HEADER_LEN + 19].fill(0xa5);
        let body_before = data[PROOF_ACCOUNT_HEADER_LEN..PROOF_ACCOUNT_HEADER_LEN + 19].to_vec();

        write_authenticated_query_counter_seal(&mut data, 37, &statement_digest).unwrap();
        assert!(proof_account_has_authenticated_query_counter(&data));
        assert!(
            !proof_account_finalized(&data),
            "the specialized seal must not be accepted by unrelated verifier paths"
        );
        assert_eq!(
            authenticated_query_counter(&data, &statement_digest),
            Ok(37)
        );
        assert_eq!(
            authenticated_query_counter(&data, &[0x74; 32]),
            Err(ProgramError::InvalidAccountData)
        );
        assert_eq!(uploaded_proof_bounds(&data), Ok((40, 59)));
        assert_eq!(
            &data[PROOF_ACCOUNT_HEADER_LEN..PROOF_ACCOUNT_HEADER_LEN + 19],
            body_before.as_slice()
        );
        assert!(proof_account_initialized(&data));
        assert!(data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32]
            .iter()
            .all(|byte| *byte == 0));
        assert_eq!(
            write_authenticated_query_counter_seal(&mut data, 1, &statement_digest),
            Err(ProgramError::InvalidAccountData),
            "a certified account cannot be rewritten"
        );

        let mut bad_counter = data.clone();
        bad_counter[PROOF_ACCOUNT_HEADER_LEN + 19 + 3] =
            aspis_core::v7_onefold::V7_COMPACT_QUERY_CANDIDATES as u8;
        assert!(!proof_account_finalized(&bad_counter));
        assert!(!proof_account_has_authenticated_query_counter(&bad_counter));
        assert_eq!(
            uploaded_proof_bounds(&bad_counter),
            Ok((PROOF_ACCOUNT_HEADER_LEN, PROOF_ACCOUNT_HEADER_LEN + 19)),
            "declared proof-body bounds are independent of trailer validity"
        );
        assert_eq!(
            authenticated_query_counter(&bad_counter, &statement_digest),
            Err(ProgramError::InvalidAccountData)
        );

        let mut legacy = vec![0u8; PROOF_ACCOUNT_HEADER_LEN + 1];
        legacy[..4].copy_from_slice(&PROOF_ACCOUNT_MAGIC);
        legacy[4..8].copy_from_slice(&1u32.to_le_bytes());
        assert!(proof_account_finalized(&legacy));
        assert_eq!(
            authenticated_query_counter(&legacy, &[0u8; 32]),
            Err(ProgramError::InvalidAccountData),
            "the audit terminal must not silently accept an ordinary seal"
        );
    }
}
