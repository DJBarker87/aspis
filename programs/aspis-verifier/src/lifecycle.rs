//! Proof-account and pool-account lifecycle (wire tags 0, 1, 62, 63, 64).
//!
//! Proof account layout:
//! [0..4] magic "ASPU", [4..8] proof_len u32 LE, [8..40] upload authority,
//! [40..40+proof_len] proof bytes.
//!
//! Finalization (tag 62) irreversibly zeroes the upload-authority field; the
//! production verification tags accept only sealed accounts. Closing
//! (tag 64) refunds every lamport of a sealed account and tombstones it.
//!
//! The default-off `sealed-proof-digest-cache-v1` feature additionally
//! exposes an inactive versioned lifecycle API. Its sealed `ASD1` header keeps
//! the same 40-byte layout but replaces the former upload-authority bytes with
//! raw SHA-256 of the exact proof body. No verifier dispatch consumes this
//! format in this module.

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
pub const PROOF_ACCOUNT_HEADER_LEN: usize = 40;
pub(crate) const AUTHORITY_OFFSET: usize = 8;

#[cfg(feature = "sealed-proof-digest-cache-v1")]
pub(crate) const PROOF_ACCOUNT_SEALED_DIGEST_V1_MAGIC: [u8; 4] = *b"ASD1";
#[cfg(feature = "sealed-proof-digest-cache-v1")]
pub(crate) const PROOF_BODY_DIGEST_V1_OFFSET: usize = AUTHORITY_OFFSET;

/// Exact framing returned by the inactive versioned sealed-header validator.
///
/// The caller may borrow `body_start..body_end` only after the account has
/// passed the read-only, owner, length and expected-digest checks performed by
/// `validate_readonly_sealed_proof_body_digest_v1`.
#[cfg(feature = "sealed-proof-digest-cache-v1")]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct ValidatedSealedProofBodyDigestV1 {
    pub(crate) body_start: usize,
    pub(crate) body_end: usize,
    pub(crate) body_digest: [u8; 32],
}

pub(crate) fn proof_account_initialized(data: &[u8]) -> bool {
    data.len() >= PROOF_ACCOUNT_HEADER_LEN && data[0..4] == PROOF_ACCOUNT_MAGIC
}

pub(crate) fn proof_account_finalized(data: &[u8]) -> bool {
    proof_account_initialized(data)
        && data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32]
            .iter()
            .all(|byte| *byte == 0)
}

pub(crate) fn proof_len(data: &[u8]) -> Result<usize, ProgramError> {
    if data.len() < PROOF_ACCOUNT_HEADER_LEN || data[0..4] != PROOF_ACCOUNT_MAGIC {
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

#[cfg(feature = "sealed-proof-digest-cache-v1")]
fn exact_proof_body_bounds_for_magic(
    data: &[u8],
    magic: [u8; 4],
) -> Result<(usize, usize), ProgramError> {
    if data.len() < PROOF_ACCOUNT_HEADER_LEN || data[0..4] != magic {
        return Err(ProgramError::InvalidAccountData);
    }
    let body_len = u32::from_le_bytes(data[4..8].try_into().unwrap()) as usize;
    let body_end = PROOF_ACCOUNT_HEADER_LEN
        .checked_add(body_len)
        .ok_or(ProgramError::InvalidAccountData)?;
    if body_end != data.len() {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok((PROOF_ACCOUNT_HEADER_LEN, body_end))
}

/// Parse the exact versioned sealed image without rehashing its body.
///
/// This byte-level helper deliberately has no account-owner premise. Runtime
/// consumers must use `validate_readonly_sealed_proof_body_digest_v1` instead.
#[cfg(feature = "sealed-proof-digest-cache-v1")]
fn parse_sealed_proof_body_digest_v1(
    data: &[u8],
) -> Result<ValidatedSealedProofBodyDigestV1, ProgramError> {
    let (body_start, body_end) =
        exact_proof_body_bounds_for_magic(data, PROOF_ACCOUNT_SEALED_DIGEST_V1_MAGIC)?;
    Ok(ValidatedSealedProofBodyDigestV1 {
        body_start,
        body_end,
        body_digest: data[PROOF_BODY_DIGEST_V1_OFFSET..PROOF_BODY_DIGEST_V1_OFFSET + 32]
            .try_into()
            .unwrap(),
    })
}

/// Validate the read-only, verifier-owned framing and exact external binding
/// of a versioned sealed proof account without hashing the proof body again.
///
/// The no-rehash result is sound only together with the lifecycle invariant:
/// this program computed the cached digest while changing `ASPU` to `ASD1`,
/// and no program mutator accepts `ASD1`. Solana account ownership and
/// read-only enforcement remain explicit runtime boundaries.
#[cfg(feature = "sealed-proof-digest-cache-v1")]
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn validate_readonly_sealed_proof_body_digest_v1(
    program_id: &Pubkey,
    proof_account: &AccountInfo,
    expected_body_len: u32,
    expected_body_digest: &[u8; 32],
) -> Result<ValidatedSealedProofBodyDigestV1, ProgramError> {
    if proof_account.owner != program_id {
        return Err(ProgramError::IncorrectProgramId);
    }
    if proof_account.is_signer || proof_account.is_writable || proof_account.executable {
        return Err(ProgramError::InvalidAccountData);
    }
    let data = proof_account.try_borrow_data()?;
    let validated = parse_sealed_proof_body_digest_v1(&data)?;
    if validated.body_end - validated.body_start != expected_body_len as usize
        || validated.body_digest != *expected_body_digest
    {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(validated)
}

/// Recompute the versioned sealed header's body digest.
///
/// This audit helper detects stale body/header images in focused lifecycle and
/// replay checks. It is intentionally not the hot verifier path because that
/// would recreate the body-hash cost the cache is intended to move.
#[cfg(feature = "sealed-proof-digest-cache-v1")]
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn audit_sealed_proof_body_digest_v1(
    data: &[u8],
    hash: aspis_core::transcript::HashFn,
) -> Result<ValidatedSealedProofBodyDigestV1, ProgramError> {
    let validated = parse_sealed_proof_body_digest_v1(data)?;
    let recomputed = hash(&[&data[validated.body_start..validated.body_end]]);
    if recomputed != validated.body_digest {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(validated)
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
    data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32].fill(0);
    Ok(())
}

#[cfg(feature = "sealed-proof-digest-cache-v1")]
#[allow(dead_code)]
fn sbf_proof_body_hash_v1(inputs: &[&[u8]]) -> [u8; 32] {
    solana_program::hash::hashv(inputs).to_bytes()
}

/// Inactive versioned finalizer which seals an exact-size `ASPU` upload as an
/// `ASD1` account and caches raw SHA-256 of its proof body in the 32 bytes
/// formerly occupied by the upload authority.
///
/// No production wire tag calls this API. The explicit hash callback variant
/// is the source-verification seam; this wrapper fixes it to the Solana
/// SHA-256 syscall convention used by proof-body request bindings.
#[cfg(feature = "sealed-proof-digest-cache-v1")]
#[allow(dead_code)]
pub(crate) fn finalize_proof_with_body_digest_v1(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
) -> ProgramResult {
    finalize_proof_with_body_digest_v1_and_hash(program_id, accounts, sbf_proof_body_hash_v1)
}

/// Callback-explicit source kernel for `finalize_proof_with_body_digest_v1`.
///
/// All validation happens before the first write. After the digest is
/// computed, the only writes are the cached digest and, last, the versioned
/// magic. No later fallible operation can leave a partially sealed image.
#[cfg(feature = "sealed-proof-digest-cache-v1")]
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn finalize_proof_with_body_digest_v1_and_hash(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    hash: aspis_core::transcript::HashFn,
) -> ProgramResult {
    let account_iter = &mut accounts.iter();
    let proof_account = next_account_info(account_iter)?;
    let authority = next_account_info(account_iter)?;
    if proof_account.owner != program_id {
        return Err(ProgramError::IncorrectProgramId);
    }
    if !proof_account.is_writable || proof_account.executable {
        return Err(ProgramError::InvalidAccountData);
    }
    let mut data = proof_account.try_borrow_mut_data()?;
    require_upload_authority(&data, authority)?;
    let (body_start, body_end) = exact_proof_body_bounds_for_magic(&data, PROOF_ACCOUNT_MAGIC)?;
    let body_digest = hash(&[&data[body_start..body_end]]);
    data[PROOF_BODY_DIGEST_V1_OFFSET..PROOF_BODY_DIGEST_V1_OFFSET + 32]
        .copy_from_slice(&body_digest);
    data[0..4].copy_from_slice(&PROOF_ACCOUNT_SEALED_DIGEST_V1_MAGIC);
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
    if !proof_account_finalized(&data) {
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

    #[cfg(feature = "sealed-proof-digest-cache-v1")]
    fn host_hashv(inputs: &[&[u8]]) -> [u8; 32] {
        solana_program::hash::hashv(inputs).to_bytes()
    }

    #[cfg(feature = "sealed-proof-digest-cache-v1")]
    #[test]
    fn sealed_digest_cache_v1_is_exact_zero_byte_framing() {
        let program_id = id();
        let proof_key = Pubkey::new_unique();
        let authority_key = Pubkey::new_unique();
        let authority_owner = solana_program::system_program::id();
        let proof_body = *b"proof-v1";
        let expected_digest = host_hashv(&[&proof_body]);
        let mut proof_lamports = 1;
        let mut authority_lamports = 1;
        let mut proof_data = [0u8; PROOF_ACCOUNT_HEADER_LEN + 8];
        let mut authority_data = [];
        proof_data[..4].copy_from_slice(&PROOF_ACCOUNT_MAGIC);
        proof_data[4..8].copy_from_slice(&8u32.to_le_bytes());
        proof_data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32].copy_from_slice(authority_key.as_ref());
        proof_data[PROOF_ACCOUNT_HEADER_LEN..].copy_from_slice(&proof_body);

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
                &authority_owner,
                &mut authority_lamports,
                &mut authority_data,
                true,
                false,
            );
            assert_eq!(
                finalize_proof_with_body_digest_v1(&program_id, &[proof, authority]),
                Ok(())
            );
        }

        assert_eq!(
            proof_data.len(),
            PROOF_ACCOUNT_HEADER_LEN + proof_body.len()
        );
        assert_eq!(proof_data[..4], PROOF_ACCOUNT_SEALED_DIGEST_V1_MAGIC);
        assert_eq!(u32::from_le_bytes(proof_data[4..8].try_into().unwrap()), 8);
        assert_eq!(
            proof_data[PROOF_BODY_DIGEST_V1_OFFSET..PROOF_BODY_DIGEST_V1_OFFSET + 32],
            expected_digest
        );
        assert_eq!(proof_data[PROOF_ACCOUNT_HEADER_LEN..], proof_body);
        assert_eq!(
            audit_sealed_proof_body_digest_v1(&proof_data, host_hashv),
            Ok(ValidatedSealedProofBodyDigestV1 {
                body_start: PROOF_ACCOUNT_HEADER_LEN,
                body_end: proof_data.len(),
                body_digest: expected_digest,
            })
        );

        let proof = make_account(
            &proof_key,
            &program_id,
            &mut proof_lamports,
            &mut proof_data,
            false,
            false,
        );
        assert_eq!(
            validate_readonly_sealed_proof_body_digest_v1(
                &program_id,
                &proof,
                proof_body.len() as u32,
                &expected_digest,
            ),
            Ok(ValidatedSealedProofBodyDigestV1 {
                body_start: PROOF_ACCOUNT_HEADER_LEN,
                body_end: PROOF_ACCOUNT_HEADER_LEN + proof_body.len(),
                body_digest: expected_digest,
            })
        );
    }

    #[cfg(feature = "sealed-proof-digest-cache-v1")]
    #[test]
    fn sealed_digest_cache_v1_rejects_every_lifecycle_mutator() {
        let program_id = id();
        let proof_key = Pubkey::new_unique();
        let authority_key = Pubkey::new_unique();
        let authority_owner = solana_program::system_program::id();
        let mut proof_lamports = 1;
        let mut authority_lamports = 1;
        let mut proof_data = [0u8; PROOF_ACCOUNT_HEADER_LEN + 8];
        let mut authority_data = [];
        proof_data[..4].copy_from_slice(&PROOF_ACCOUNT_MAGIC);
        proof_data[4..8].copy_from_slice(&8u32.to_le_bytes());
        proof_data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32].copy_from_slice(authority_key.as_ref());
        proof_data[PROOF_ACCOUNT_HEADER_LEN..].copy_from_slice(b"proof-v1");

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
                &authority_owner,
                &mut authority_lamports,
                &mut authority_data,
                true,
                false,
            );
            assert_eq!(
                finalize_proof_with_body_digest_v1_and_hash(
                    &program_id,
                    &[proof, authority],
                    host_hashv,
                ),
                Ok(())
            );
        }
        let sealed = proof_data;

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
                &authority_owner,
                &mut authority_lamports,
                &mut authority_data,
                true,
                false,
            );
            assert_eq!(
                upload_chunk(&program_id, &[proof, authority], 0, &[0xff]),
                Err(ProgramError::InvalidAccountData)
            );
        }
        assert_eq!(proof_data, sealed);

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
                &authority_owner,
                &mut authority_lamports,
                &mut authority_data,
                true,
                false,
            );
            assert_eq!(
                init_proof(&program_id, &[proof, authority], 8),
                Err(ProgramError::InvalidAccountData)
            );
        }
        assert_eq!(proof_data, sealed);

        for versioned in [false, true] {
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
                &authority_owner,
                &mut authority_lamports,
                &mut authority_data,
                true,
                false,
            );
            let result = if versioned {
                finalize_proof_with_body_digest_v1_and_hash(
                    &program_id,
                    &[proof, authority],
                    host_hashv,
                )
            } else {
                finalize_proof(&program_id, &[proof, authority])
            };
            assert_eq!(result, Err(ProgramError::InvalidAccountData));
            assert_eq!(proof_data, sealed);
        }
    }

    #[cfg(feature = "sealed-proof-digest-cache-v1")]
    #[test]
    fn sealed_digest_cache_v1_rejects_malformed_stale_and_unsafe_framing() {
        let program_id = id();
        let proof_key = Pubkey::new_unique();
        let authority_key = Pubkey::new_unique();
        let authority_owner = solana_program::system_program::id();
        let proof_body = *b"proof-v1";
        let expected_digest = host_hashv(&[&proof_body]);
        let mut exact = [0u8; PROOF_ACCOUNT_HEADER_LEN + 8];
        exact[..4].copy_from_slice(&PROOF_ACCOUNT_MAGIC);
        exact[4..8].copy_from_slice(&8u32.to_le_bytes());
        exact[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32].copy_from_slice(authority_key.as_ref());
        exact[PROOF_ACCOUNT_HEADER_LEN..].copy_from_slice(&proof_body);

        for declared_len in [7u32, 9] {
            let mut proof_lamports = 1;
            let mut authority_lamports = 1;
            let mut authority_data = [];
            let mut malformed = exact;
            malformed[4..8].copy_from_slice(&declared_len.to_le_bytes());
            let before = malformed;
            {
                let proof = make_account(
                    &proof_key,
                    &program_id,
                    &mut proof_lamports,
                    &mut malformed,
                    false,
                    true,
                );
                let authority = make_account(
                    &authority_key,
                    &authority_owner,
                    &mut authority_lamports,
                    &mut authority_data,
                    true,
                    false,
                );
                assert_eq!(
                    finalize_proof_with_body_digest_v1_and_hash(
                        &program_id,
                        &[proof, authority],
                        host_hashv,
                    ),
                    Err(ProgramError::InvalidAccountData)
                );
            }
            assert_eq!(malformed, before);
        }

        let mut proof_lamports = 1;
        let mut authority_lamports = 1;
        let mut authority_data = [];
        {
            let proof = make_account(
                &proof_key,
                &program_id,
                &mut proof_lamports,
                &mut exact,
                false,
                true,
            );
            let authority = make_account(
                &authority_key,
                &authority_owner,
                &mut authority_lamports,
                &mut authority_data,
                true,
                false,
            );
            assert_eq!(
                finalize_proof_with_body_digest_v1_and_hash(
                    &program_id,
                    &[proof, authority],
                    host_hashv,
                ),
                Ok(())
            );
        }

        let sealed = exact;
        for (owner, signer, writable, expected_len, digest, expected_error) in [
            (
                program_id,
                false,
                false,
                7u32,
                expected_digest,
                ProgramError::InvalidAccountData,
            ),
            (
                program_id,
                false,
                false,
                8u32,
                [0x55; 32],
                ProgramError::InvalidAccountData,
            ),
            (
                authority_owner,
                false,
                false,
                8u32,
                expected_digest,
                ProgramError::IncorrectProgramId,
            ),
            (
                program_id,
                true,
                false,
                8u32,
                expected_digest,
                ProgramError::InvalidAccountData,
            ),
            (
                program_id,
                false,
                true,
                8u32,
                expected_digest,
                ProgramError::InvalidAccountData,
            ),
        ] {
            let proof = make_account(
                &proof_key,
                &owner,
                &mut proof_lamports,
                &mut exact,
                signer,
                writable,
            );
            assert_eq!(
                validate_readonly_sealed_proof_body_digest_v1(
                    &program_id,
                    &proof,
                    expected_len,
                    &digest,
                ),
                Err(expected_error)
            );
            assert_eq!(exact, sealed);
        }

        {
            let executable = AccountInfo::new(
                &proof_key,
                false,
                false,
                &mut proof_lamports,
                &mut exact,
                &program_id,
                true,
                solana_program::clock::Epoch::default(),
            );
            assert_eq!(
                validate_readonly_sealed_proof_body_digest_v1(
                    &program_id,
                    &executable,
                    8,
                    &expected_digest,
                ),
                Err(ProgramError::InvalidAccountData)
            );
        }
        assert_eq!(exact, sealed);

        let mut stale_body = sealed;
        stale_body[PROOF_ACCOUNT_HEADER_LEN] ^= 1;
        assert_eq!(
            audit_sealed_proof_body_digest_v1(&stale_body, host_hashv),
            Err(ProgramError::InvalidAccountData)
        );
        let mut stale_header = sealed;
        stale_header[PROOF_BODY_DIGEST_V1_OFFSET] ^= 1;
        assert_eq!(
            audit_sealed_proof_body_digest_v1(&stale_header, host_hashv),
            Err(ProgramError::InvalidAccountData)
        );
        let mut trailing = sealed.to_vec();
        trailing.push(0);
        assert_eq!(
            audit_sealed_proof_body_digest_v1(&trailing, host_hashv),
            Err(ProgramError::InvalidAccountData)
        );
        let mut wrong_magic = sealed;
        wrong_magic[..4].copy_from_slice(&PROOF_ACCOUNT_MAGIC);
        assert_eq!(
            audit_sealed_proof_body_digest_v1(&wrong_magic, host_hashv),
            Err(ProgramError::InvalidAccountData)
        );
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
}
