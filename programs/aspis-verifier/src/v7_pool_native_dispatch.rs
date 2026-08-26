//! Exact selected-verifier bridge for the native Pool V1 Tag-73 relations.
//!
//! The Pool supplies its canonical 216-byte `ASCP` or `ASWP` statement
//! directly.  The generic 384-byte `ASVQ` prefix already binds the selected
//! program/profile/release, proof account/body and statement digest, so this
//! profile introduces no duplicated statement envelope.

use aspis_core::{
    v7_onefold::{
        V7_COMPACT_BODY_WITHOUT_FRONTIERS, V7_COMPACT_DIGEST_BYTES,
        V7_COMPACT_FRONTIER_CAP_PER_TREE,
    },
    HashFn,
};
use aspis_statement::pool_v1::{
    decode_pool_v1_private_transfer_public_v1, decode_pool_v1_withdrawal_public_v1,
    decode_verifier_dispatch_request_v1, encode_verifier_dispatch_result_v1,
    historical_anchor_envelope_digest_v1, verifier_proof_body_digest_v1,
    HistoricalAnchorEnvelopeV1, PoolV1PrivateTransferPublicV1, PoolV1TransitionKind,
    PoolV1WithdrawalPublicV1, VerifierDispatchBindingV1, VerifierDispatchRequestV1,
    VerifierDispatchResultV1, POOL_V1_PAYMENT_STATEMENT_BYTES,
    POOL_V1_VERIFIER_DISPATCH_BINDING_PREFIX_BYTES, POOL_V1_VERIFIER_DISPATCH_RESULT_BYTES,
    POOL_V1_VERIFIER_DISPATCH_SUCCESS_CODE,
};
use solana_program::{
    account_info::AccountInfo, entrypoint::ProgramResult, program, program_error::ProgramError,
    pubkey::Pubkey,
};

use crate::lifecycle::{proof_account_finalized, uploaded_proof_bounds};

pub const V7_POOL_NATIVE_TAG73_PROFILE_BINDING_PREIMAGE: &[u8] =
    b"aspis:pool-v1:verifier-profile:tag73-native-payment-v1:asvq-v1";
pub const V7_POOL_NATIVE_TAG73_PROFILE_BINDING: [u8; 32] = [
    0x70, 0xa7, 0x85, 0xea, 0x72, 0x34, 0x69, 0xa1, 0x34, 0x97, 0x40, 0x71, 0x62, 0xff, 0x01, 0xb5,
    0x5b, 0x33, 0x26, 0x87, 0xfd, 0x9d, 0x0a, 0x8c, 0x89, 0xb8, 0x12, 0x59, 0xb2, 0xd1, 0x96, 0x3d,
];

pub const V7_POOL_NATIVE_TAG73_RELEASE_BINDING_PREIMAGE: &[u8] =
    b"aspis:v7:pool-v1-payment:26c1-3c2:b10:q16:digest208:cap203:full-c2:work35-31-34:release-v1";
pub const V7_POOL_NATIVE_TAG73_RELEASE_BINDING: [u8; 32] = [
    0x9a, 0x29, 0x16, 0xf7, 0x65, 0x7b, 0x7b, 0x85, 0xa3, 0x51, 0x2d, 0x85, 0xd5, 0xa0, 0x58, 0x9c,
    0x19, 0xe7, 0x55, 0xca, 0x5e, 0x60, 0xd9, 0x10, 0x71, 0xb8, 0x0c, 0x2a, 0xf6, 0x2d, 0x0d, 0xff,
];

pub const V7_POOL_NATIVE_TAG73_REQUEST_BYTES: usize =
    POOL_V1_VERIFIER_DISPATCH_BINDING_PREFIX_BYTES + POOL_V1_PAYMENT_STATEMENT_BYTES;
/// Smallest binary authentication frontier for 16 distinct leaves in a
/// depth-18 tree (the 16 leaves form one complete depth-four subtree).
pub const V7_POOL_NATIVE_TAG73_MIN_FRONTIER_NODES: usize = 14;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V7PoolNativeTag73StatementV1 {
    PrivateTransfer(PoolV1PrivateTransferPublicV1),
    Withdrawal(PoolV1WithdrawalPublicV1),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ValidatedV7PoolNativeTag73RequestV1<'a> {
    pub request: VerifierDispatchRequestV1<'a>,
    pub statement: V7PoolNativeTag73StatementV1,
    pub frontier_nodes: usize,
}

fn statement_matches_binding(
    statement: V7PoolNativeTag73StatementV1,
    binding: &VerifierDispatchBindingV1,
) -> bool {
    match statement {
        V7PoolNativeTag73StatementV1::PrivateTransfer(statement) => {
            binding.transition_kind == PoolV1TransitionKind::PrivateTransfer
                && statement.pool == binding.pool
                && statement.deployment_domain == binding.deployment_domain
                && statement.anchor_sequence == binding.anchor_sequence
                && statement.anchor_root == binding.anchor_root
                && statement.nullifier == binding.nullifier
        }
        V7PoolNativeTag73StatementV1::Withdrawal(statement) => {
            binding.transition_kind == PoolV1TransitionKind::Withdrawal
                && statement.pool == binding.pool
                && statement.deployment_domain == binding.deployment_domain
                && statement.anchor_sequence == binding.anchor_sequence
                && statement.anchor_root == binding.anchor_root
                && statement.nullifier == binding.nullifier
        }
    }
}

fn frontier_nodes_from_proof_length(length: u32) -> Option<usize> {
    let length = usize::try_from(length).ok()?;
    let frontier_bytes = length.checked_sub(V7_COMPACT_BODY_WITHOUT_FRONTIERS)?;
    let both_tree_node_bytes = 2usize.checked_mul(V7_COMPACT_DIGEST_BYTES)?;
    if frontier_bytes % both_tree_node_bytes != 0 {
        return None;
    }
    let nodes = frontier_bytes / both_tree_node_bytes;
    (nodes >= V7_POOL_NATIVE_TAG73_MIN_FRONTIER_NODES && nodes <= V7_COMPACT_FRONTIER_CAP_PER_TREE)
        .then_some(nodes)
}

pub fn validate_v7_pool_native_tag73_request_v1<'a>(
    program_id: &Pubkey,
    proof_account: &AccountInfo<'_>,
    instruction_data: &'a [u8],
    hash: HashFn,
) -> Result<ValidatedV7PoolNativeTag73RequestV1<'a>, ProgramError> {
    if instruction_data.len() != V7_POOL_NATIVE_TAG73_REQUEST_BYTES {
        return Err(ProgramError::InvalidInstructionData);
    }
    let request = decode_verifier_dispatch_request_v1(instruction_data, hash)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    if request.binding.verifier_program != program_id.to_bytes() {
        return Err(ProgramError::IncorrectProgramId);
    }
    if request.binding.profile_binding != V7_POOL_NATIVE_TAG73_PROFILE_BINDING
        || request.binding.release_binding != V7_POOL_NATIVE_TAG73_RELEASE_BINDING
        || request.binding.proof_account != proof_account.key.to_bytes()
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    let statement = match request.binding.transition_kind {
        PoolV1TransitionKind::PrivateTransfer => V7PoolNativeTag73StatementV1::PrivateTransfer(
            decode_pool_v1_private_transfer_public_v1(request.statement_payload)
                .map_err(|_| ProgramError::InvalidInstructionData)?,
        ),
        PoolV1TransitionKind::Withdrawal => V7PoolNativeTag73StatementV1::Withdrawal(
            decode_pool_v1_withdrawal_public_v1(request.statement_payload)
                .map_err(|_| ProgramError::InvalidInstructionData)?,
        ),
    };
    if !statement_matches_binding(statement, &request.binding) {
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
    let frontier_nodes = frontier_nodes_from_proof_length(request.binding.proof_body_length)
        .ok_or(ProgramError::InvalidInstructionData)?;
    Ok(ValidatedV7PoolNativeTag73RequestV1 {
        request,
        statement,
        frontier_nodes,
    })
}

pub(crate) fn verify_v7_pool_native_tag73_asvq_with_runtime(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
    hash: HashFn,
) -> Result<VerifierDispatchBindingV1, ProgramError> {
    let [proof_account] = accounts else {
        return Err(if accounts.is_empty() {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    };
    if proof_account.owner != program_id {
        return Err(ProgramError::IncorrectProgramId);
    }
    if proof_account.is_signer || proof_account.is_writable || proof_account.executable {
        return Err(ProgramError::InvalidAccountData);
    }
    let validated = validate_v7_pool_native_tag73_request_v1(
        program_id,
        proof_account,
        instruction_data,
        hash,
    )?;
    let data = proof_account.try_borrow_data()?;
    if !proof_account_finalized(&data) {
        return Err(ProgramError::InvalidAccountData);
    }
    let (proof_start, proof_end) = uploaded_proof_bounds(&data)?;
    if proof_end != data.len() {
        return Err(ProgramError::InvalidAccountData);
    }
    let proof = &data[proof_start..proof_end];
    if proof.len() != validated.request.binding.proof_body_length as usize
        || verifier_proof_body_digest_v1(proof, hash) != validated.request.binding.proof_body_digest
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let attempt_id = *proof_account.key;
    let statement_digest = validated.request.binding.statement_digest;
    let result = match validated.statement {
        V7PoolNativeTag73StatementV1::PrivateTransfer(statement) => {
            crate::v7_verifier::verify_v7_pool_private_transfer_with_statement_digest(
                hash,
                proof,
                validated.frontier_nodes,
                program_id,
                V7_POOL_NATIVE_TAG73_RELEASE_BINDING,
                &attempt_id,
                &statement,
                statement_digest,
                true,
            )
        }
        V7PoolNativeTag73StatementV1::Withdrawal(statement) => {
            crate::v7_verifier::verify_v7_pool_withdrawal_with_statement_digest(
                hash,
                proof,
                validated.frontier_nodes,
                program_id,
                V7_POOL_NATIVE_TAG73_RELEASE_BINDING,
                &attempt_id,
                &statement,
                statement_digest,
                true,
            )
        }
    };
    result.map_err(|_| ProgramError::InvalidAccountData)?;
    Ok(validated.request.binding)
}

pub fn process_v7_pool_native_tag73_asvq_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
) -> ProgramResult {
    let binding = verify_v7_pool_native_tag73_asvq_with_runtime(
        program_id,
        accounts,
        instruction_data,
        crate::verify::sbf_hashv,
    )?;
    let result = encode_verifier_dispatch_result_v1(&VerifierDispatchResultV1 {
        success_code: POOL_V1_VERIFIER_DISPATCH_SUCCESS_CODE,
        binding,
    })
    .map_err(|_| ProgramError::InvalidInstructionData)?;
    let _: &[u8; POOL_V1_VERIFIER_DISPATCH_RESULT_BYTES] = &result;
    program::set_return_data(&result);
    Ok(())
}

#[cfg(test)]
mod tests {
    use aspis_core::field::M31;
    use aspis_statement::pool_v1::{
        encode_pool_v1_private_transfer_public_v1, encode_pool_v1_withdrawal_public_v1,
        encode_verifier_dispatch_request_v1, verifier_dispatch_binding_from_envelope_v1,
        PoolV1WithdrawalPublicV1, VerifierDispatchRequestV1,
    };
    use solana_program::clock::Epoch;

    use super::*;

    fn sha256(inputs: &[&[u8]]) -> [u8; 32] {
        solana_program::hash::hashv(inputs).to_bytes()
    }

    fn digest(seed: u32) -> aspis_statement::Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn canonical_request(
        program_id: Pubkey,
        proof_key: Pubkey,
        kind: PoolV1TransitionKind,
    ) -> Vec<u8> {
        let pool = Pubkey::new_unique().to_bytes();
        let deployment_domain = [0x53; 32];
        let anchor_sequence = 41;
        let anchor_root = digest(10);
        let nullifier = digest(100);
        let statement = match kind {
            PoolV1TransitionKind::PrivateTransfer => {
                encode_pool_v1_private_transfer_public_v1(&PoolV1PrivateTransferPublicV1 {
                    pool,
                    deployment_domain,
                    anchor_sequence,
                    anchor_root,
                    nullifier,
                    asset_id: M31(17),
                    recipient_commitment: digest(200),
                    change_commitment: digest(300),
                })
                .unwrap()
            }
            PoolV1TransitionKind::Withdrawal => {
                encode_pool_v1_withdrawal_public_v1(&PoolV1WithdrawalPublicV1 {
                    pool,
                    deployment_domain,
                    anchor_sequence,
                    anchor_root,
                    nullifier,
                    asset_id: M31(17),
                    amount: 9,
                    destination_token_account: Pubkey::new_unique().to_bytes(),
                    change_commitment: digest(300),
                })
                .unwrap()
            }
        };
        let envelope = HistoricalAnchorEnvelopeV1 {
            transition_kind: kind,
            pool,
            deployment_domain,
            anchor_sequence,
            anchor_root,
            nullifier,
            verifier_profile: V7_POOL_NATIVE_TAG73_PROFILE_BINDING,
            verifier_release: V7_POOL_NATIVE_TAG73_RELEASE_BINDING,
        };
        let proof_body_length = (V7_COMPACT_BODY_WITHOUT_FRONTIERS
            + 2 * V7_POOL_NATIVE_TAG73_MIN_FRONTIER_NODES * V7_COMPACT_DIGEST_BYTES)
            as u32;
        let binding = verifier_dispatch_binding_from_envelope_v1(
            program_id.to_bytes(),
            &envelope,
            &statement,
            proof_key.to_bytes(),
            sha256(&[b"native-pool-proof-body"]),
            proof_body_length,
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

    #[test]
    fn profile_and_release_bindings_match_their_exact_preimages() {
        assert_eq!(
            solana_program::hash::hash(V7_POOL_NATIVE_TAG73_PROFILE_BINDING_PREIMAGE).to_bytes(),
            V7_POOL_NATIVE_TAG73_PROFILE_BINDING
        );
        assert_eq!(
            solana_program::hash::hash(V7_POOL_NATIVE_TAG73_RELEASE_BINDING_PREIMAGE).to_bytes(),
            V7_POOL_NATIVE_TAG73_RELEASE_BINDING
        );
    }

    #[test]
    fn proof_length_inversion_is_exact_and_bounded() {
        for nodes in [
            V7_POOL_NATIVE_TAG73_MIN_FRONTIER_NODES,
            99,
            V7_COMPACT_FRONTIER_CAP_PER_TREE,
        ] {
            let length = V7_COMPACT_BODY_WITHOUT_FRONTIERS + 2 * nodes * V7_COMPACT_DIGEST_BYTES;
            assert_eq!(frontier_nodes_from_proof_length(length as u32), Some(nodes));
        }
        assert_eq!(
            frontier_nodes_from_proof_length((V7_COMPACT_BODY_WITHOUT_FRONTIERS - 1) as u32),
            None
        );
        assert_eq!(
            frontier_nodes_from_proof_length((V7_COMPACT_BODY_WITHOUT_FRONTIERS + 1) as u32),
            None
        );
    }

    #[test]
    fn canonical_transfer_and_withdrawal_requests_bind_exact_native_statements() {
        let program_id = crate::id();
        for kind in [
            PoolV1TransitionKind::PrivateTransfer,
            PoolV1TransitionKind::Withdrawal,
        ] {
            let proof_key = Pubkey::new_unique();
            let request = canonical_request(program_id, proof_key, kind);
            assert_eq!(request.len(), V7_POOL_NATIVE_TAG73_REQUEST_BYTES);
            let mut lamports = 1;
            let mut data = [];
            let proof = AccountInfo::new(
                &proof_key,
                false,
                false,
                &mut lamports,
                &mut data,
                &program_id,
                false,
                Epoch::default(),
            );
            let validated =
                validate_v7_pool_native_tag73_request_v1(&program_id, &proof, &request, sha256)
                    .unwrap();
            assert_eq!(validated.request.binding.transition_kind, kind);
            assert_eq!(
                validated.frontier_nodes,
                V7_POOL_NATIVE_TAG73_MIN_FRONTIER_NODES
            );
            assert!(matches!(
                (kind, validated.statement),
                (
                    PoolV1TransitionKind::PrivateTransfer,
                    V7PoolNativeTag73StatementV1::PrivateTransfer(_)
                ) | (
                    PoolV1TransitionKind::Withdrawal,
                    V7PoolNativeTag73StatementV1::Withdrawal(_)
                )
            ));
        }
    }

    #[test]
    fn native_request_validation_rejects_wrong_account_and_statement_mutation() {
        let program_id = crate::id();
        let proof_key = Pubkey::new_unique();
        let mut request =
            canonical_request(program_id, proof_key, PoolV1TransitionKind::PrivateTransfer);
        let wrong_proof_key = Pubkey::new_unique();
        let mut lamports = 1;
        let mut data = [];
        let wrong_proof = AccountInfo::new(
            &wrong_proof_key,
            false,
            false,
            &mut lamports,
            &mut data,
            &program_id,
            false,
            Epoch::default(),
        );
        assert!(validate_v7_pool_native_tag73_request_v1(
            &program_id,
            &wrong_proof,
            &request,
            sha256,
        )
        .is_err());

        request[V7_POOL_NATIVE_TAG73_REQUEST_BYTES - 1] ^= 1;
        let mut lamports = 1;
        let mut data = [];
        let proof = AccountInfo::new(
            &proof_key,
            false,
            false,
            &mut lamports,
            &mut data,
            &program_id,
            false,
            Epoch::default(),
        );
        assert!(
            validate_v7_pool_native_tag73_request_v1(&program_id, &proof, &request, sha256,)
                .is_err()
        );
    }
}
