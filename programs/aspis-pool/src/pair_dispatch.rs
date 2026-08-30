//! Hash-free selected-verifier dispatch for the stable pair-Pool proof.
//!
//! The Pool validates the finalized verifier-owned proof account header,
//! exact body length and lack of trailing bytes. It intentionally does not
//! hash the 30,504-byte body: the same read-only account is passed to the
//! selected verifier, which reads and verifies those locked bytes directly.

extern crate alloc;

use alloc::{boxed::Box, vec, vec::Vec};

use aspis_core::transcript::HashFn;
use aspis_statement::pool_v1::{
    decode_pool_v1_pair_verified_afterstate_v1, decode_pool_v1_pair_verifier_result_v1,
    encode_pool_v1_pair_verifier_request_v1, pool_v1_pair_statement_digest_v1,
    HistoricalAnchorEnvelopeV1, PoolV1PairVerifiedAfterstateV1, PoolV1PairVerifierBindingV1,
    PoolV1PairVerifierRequestV1, PoolV1PairVerifierResultV1, VerifierPolicyV1,
    POOL_V1_HISTORICAL_ANCHOR_VERSION, POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
    POOL_V1_PAIR_VERIFIER_RESULT_BYTES, POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES,
    POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC,
};
use solana_program::{
    account_info::AccountInfo,
    instruction::{AccountMeta, Instruction},
    program,
    program_error::ProgramError,
    pubkey::Pubkey,
};
use solana_sdk_ids::{bpf_loader, bpf_loader_upgradeable, loader_v4};

use crate::{
    error::PoolV1ProgramError,
    registry::{authenticate_verifier_selection_v1, VerifierSelectionV1},
};

#[inline(always)]
fn pair_cu_checkpoint(label: &str) {
    #[cfg(feature = "pair-afterstate-profile")]
    {
        solana_program::log::sol_log(label);
        solana_program::log::sol_log_compute_units();
    }
    #[cfg(not(feature = "pair-afterstate-profile"))]
    let _ = label;
}

const PROOF_LENGTH_OFFSET: usize = 4;
const PROOF_AUTHORITY_OFFSET: usize = 8;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PairVerifierAccountClaimV1 {
    pub verifier_program: [u8; 32],
    pub proof_account: [u8; 32],
    pub proof_body_length: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlannedPairVerifierDispatchV1 {
    pub binding: PoolV1PairVerifierBindingV1,
    pub request_bytes: Vec<u8>,
}

/// Opaque proof-carried afterstate.  Its field is private so Pool state code
/// cannot manufacture an authorization without passing the immediate
/// selected-program return-data check in this module.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct AuthenticatedPairAfterstateV1(Box<PoolV1PairVerifiedAfterstateV1>);

impl AuthenticatedPairAfterstateV1 {
    pub(crate) fn value(&self) -> &PoolV1PairVerifiedAfterstateV1 {
        &self.0
    }
}

/// Authenticate and decode the minimal conservative proof-carried result.
/// The caller must pass the program id returned by Solana immediately after
/// the verifier CPI; a prior or unrelated program's bytes are rejected.
pub(crate) fn authenticate_pair_verified_afterstate_return_v1(
    selected_verifier: &Pubkey,
    returned_program: &Pubkey,
    returned_data: &[u8],
) -> Result<AuthenticatedPairAfterstateV1, ProgramError> {
    if returned_program != selected_verifier
        || returned_data.len() != POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
    {
        return Err(PoolV1ProgramError::InvalidVerifierReturnData.into());
    }
    let afterstate = decode_pool_v1_pair_verified_afterstate_v1(returned_data)
        .map_err(|_| PoolV1ProgramError::InvalidVerifierReturnData)?;
    Ok(AuthenticatedPairAfterstateV1(Box::new(afterstate)))
}

trait PairVerifierRuntimeV1 {
    fn clear_return_data(&mut self);
    fn invoke(
        &mut self,
        instruction: &Instruction,
        account_infos: &[AccountInfo<'_>],
    ) -> Result<(), ProgramError>;
    fn get_return_data(&mut self) -> Option<(Pubkey, Vec<u8>)>;
}

struct SolanaPairVerifierRuntimeV1;

impl PairVerifierRuntimeV1 for SolanaPairVerifierRuntimeV1 {
    fn clear_return_data(&mut self) {
        program::set_return_data(&[]);
    }

    fn invoke(
        &mut self,
        instruction: &Instruction,
        account_infos: &[AccountInfo<'_>],
    ) -> Result<(), ProgramError> {
        program::invoke(instruction, account_infos)
    }

    fn get_return_data(&mut self) -> Option<(Pubkey, Vec<u8>)> {
        program::get_return_data()
    }
}

fn supported_loader(owner: &Pubkey) -> bool {
    owner == &bpf_loader::id()
        || owner == &bpf_loader_upgradeable::id()
        || owner == &loader_v4::id()
}

fn require_verifier_program(
    account: &AccountInfo<'_>,
    selected: &Pubkey,
) -> Result<(), ProgramError> {
    if account.key != selected
        || !account.executable
        || account.is_signer
        || account.is_writable
        || !supported_loader(account.owner)
    {
        return Err(PoolV1ProgramError::InvalidVerifierProgramAccount.into());
    }
    Ok(())
}

/// Validate the sealed account framing without reading or hashing the body.
pub fn derive_pair_verifier_account_claim_v1(
    verifier_program: &AccountInfo<'_>,
    proof: &AccountInfo<'_>,
) -> Result<PairVerifierAccountClaimV1, ProgramError> {
    if proof.key == verifier_program.key
        || proof.owner != verifier_program.key
        || proof.executable
        || proof.is_signer
        || proof.is_writable
    {
        return Err(PoolV1ProgramError::InvalidVerifierProofAccount.into());
    }
    let data = proof.try_borrow_data()?;
    if data.len() < POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES
        || data[..4] != POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC
        || data[PROOF_AUTHORITY_OFFSET..POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES]
            .iter()
            .any(|byte| *byte != 0)
    {
        return Err(PoolV1ProgramError::InvalidVerifierProofAccount.into());
    }
    let proof_body_length = u32::from_le_bytes(
        data[PROOF_LENGTH_OFFSET..PROOF_AUTHORITY_OFFSET]
            .try_into()
            .map_err(|_| PoolV1ProgramError::InvalidVerifierProofAccount)?,
    );
    if proof_body_length == 0
        || POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES.checked_add(proof_body_length as usize)
            != Some(data.len())
    {
        return Err(PoolV1ProgramError::VerifierProofBindingMismatch.into());
    }
    Ok(PairVerifierAccountClaimV1 {
        verifier_program: verifier_program.key.to_bytes(),
        proof_account: proof.key.to_bytes(),
        proof_body_length,
    })
}

#[allow(clippy::too_many_arguments)]
pub fn plan_pair_verifier_dispatch_v1(
    pool: &Pubkey,
    expected_deployment_domain: &[u8; 32],
    policy: &VerifierPolicyV1,
    registry_accounts: &[AccountInfo<'_>],
    verifier_program: &AccountInfo<'_>,
    proof: &AccountInfo<'_>,
    envelope: &HistoricalAnchorEnvelopeV1,
    statement_payload: &[u8],
    current_slot: u64,
    hash: HashFn,
) -> Result<PlannedPairVerifierDispatchV1, ProgramError> {
    if envelope.pool != pool.to_bytes() || envelope.deployment_domain != *expected_deployment_domain
    {
        return Err(PoolV1ProgramError::VerifierDispatchIdentityMismatch.into());
    }
    let claim = derive_pair_verifier_account_claim_v1(verifier_program, proof)?;
    let selected = Pubkey::new_from_array(claim.verifier_program);
    require_verifier_program(verifier_program, &selected)?;
    let authenticated = authenticate_verifier_selection_v1(
        pool,
        policy,
        registry_accounts,
        VerifierSelectionV1 {
            verifier_program: claim.verifier_program,
            profile_binding: envelope.verifier_profile,
            release_binding: envelope.verifier_release,
            statement_version: POOL_V1_HISTORICAL_ANCHOR_VERSION,
        },
        current_slot,
    )?;
    if !authenticated.matches_verifier_owner(verifier_program.owner) {
        return Err(PoolV1ProgramError::InvalidVerifierProgramAccount.into());
    }
    if !authenticated.matches(
        pool.to_bytes(),
        claim.verifier_program,
        envelope.verifier_profile,
        envelope.verifier_release,
        POOL_V1_HISTORICAL_ANCHOR_VERSION,
    ) {
        return Err(PoolV1ProgramError::VerifierSelectionMismatch.into());
    }
    let binding = PoolV1PairVerifierBindingV1 {
        transition_kind: envelope.transition_kind,
        verifier_program: claim.verifier_program,
        profile_binding: envelope.verifier_profile,
        release_binding: envelope.verifier_release,
        pool: pool.to_bytes(),
        proof_account: claim.proof_account,
        proof_body_length: claim.proof_body_length,
        statement_digest: pool_v1_pair_statement_digest_v1(statement_payload, hash),
    };
    let request_bytes = encode_pool_v1_pair_verifier_request_v1(&PoolV1PairVerifierRequestV1 {
        binding,
        statement_payload,
    })
    .map_err(|_| PoolV1ProgramError::InvalidVerifierDispatchEnvelope)?;
    Ok(PlannedPairVerifierDispatchV1 {
        binding,
        request_bytes,
    })
}

fn invoke_pair_verifier_with_runtime_v1<'info, R: PairVerifierRuntimeV1>(
    plan: PlannedPairVerifierDispatchV1,
    verifier_program: &AccountInfo<'info>,
    proof: &AccountInfo<'info>,
    runtime: &mut R,
) -> Result<PoolV1PairVerifierResultV1, ProgramError> {
    let selected = Pubkey::new_from_array(plan.binding.verifier_program);
    require_verifier_program(verifier_program, &selected)?;
    if proof.key.to_bytes() != plan.binding.proof_account
        || proof.owner != &selected
        || proof.executable
        || proof.is_signer
        || proof.is_writable
    {
        return Err(PoolV1ProgramError::InvalidVerifierProofAccount.into());
    }
    let instruction = Instruction {
        program_id: selected,
        accounts: vec![AccountMeta::new_readonly(*proof.key, false)],
        data: plan.request_bytes,
    };
    let account_infos = [proof.clone(), verifier_program.clone()];
    runtime.clear_return_data();
    runtime.invoke(&instruction, &account_infos)?;
    let (returned_program, returned_data) = runtime
        .get_return_data()
        .ok_or(PoolV1ProgramError::MissingVerifierReturnData)?;
    if returned_program != selected {
        return Err(PoolV1ProgramError::InvalidVerifierReturnProgram.into());
    }
    if returned_data.len() != POOL_V1_PAIR_VERIFIER_RESULT_BYTES {
        return Err(PoolV1ProgramError::InvalidVerifierReturnData.into());
    }
    decode_pool_v1_pair_verifier_result_v1(&returned_data)
        .map_err(|_| PoolV1ProgramError::InvalidVerifierReturnData.into())
}

fn invoke_pair_afterstate_verifier_with_runtime_v1<'info, R: PairVerifierRuntimeV1>(
    plan: PlannedPairVerifierDispatchV1,
    verifier_program: &AccountInfo<'info>,
    proof: &AccountInfo<'info>,
    runtime: &mut R,
) -> Result<AuthenticatedPairAfterstateV1, ProgramError> {
    let selected = Pubkey::new_from_array(plan.binding.verifier_program);
    require_verifier_program(verifier_program, &selected)?;
    if proof.key.to_bytes() != plan.binding.proof_account
        || proof.owner != &selected
        || proof.executable
        || proof.is_signer
        || proof.is_writable
    {
        return Err(PoolV1ProgramError::InvalidVerifierProofAccount.into());
    }
    let instruction = Instruction {
        program_id: selected,
        accounts: vec![AccountMeta::new_readonly(*proof.key, false)],
        data: plan.request_bytes,
    };
    let account_infos = [proof.clone(), verifier_program.clone()];
    runtime.clear_return_data();
    pair_cu_checkpoint("aspis-pair-cu:verifier_cpi_start");
    runtime.invoke(&instruction, &account_infos)?;
    let (returned_program, returned_data) = runtime
        .get_return_data()
        .ok_or(PoolV1ProgramError::MissingVerifierReturnData)?;
    let authenticated = authenticate_pair_verified_afterstate_return_v1(
        &selected,
        &returned_program,
        &returned_data,
    )?;
    pair_cu_checkpoint("aspis-pair-cu:verifier_cpi_complete");
    Ok(authenticated)
}

#[allow(clippy::too_many_arguments)]
pub fn dispatch_pair_verifier_readonly_v1<'info>(
    pool: &Pubkey,
    expected_deployment_domain: &[u8; 32],
    policy: &VerifierPolicyV1,
    registry_accounts: &[AccountInfo<'info>],
    verifier_program: &AccountInfo<'info>,
    proof: &AccountInfo<'info>,
    envelope: &HistoricalAnchorEnvelopeV1,
    statement_payload: &[u8],
    current_slot: u64,
    hash: HashFn,
) -> Result<PoolV1PairVerifierResultV1, ProgramError> {
    let plan = plan_pair_verifier_dispatch_v1(
        pool,
        expected_deployment_domain,
        policy,
        registry_accounts,
        verifier_program,
        proof,
        envelope,
        statement_payload,
        current_slot,
        hash,
    )?;
    let mut runtime = SolanaPairVerifierRuntimeV1;
    invoke_pair_verifier_with_runtime_v1(plan, verifier_program, proof, &mut runtime)
}

/// Measurement-gated selected-verifier transport for the conservative ASJA
/// afterstate.  It performs the same registry/proof-account binding as the
/// stable pair dispatch, then accepts only the immediate selected program's
/// exact 688-byte typed result.
#[cfg(feature = "pair-afterstate-evidence")]
#[allow(clippy::too_many_arguments)]
pub(crate) fn dispatch_pair_verified_afterstate_readonly_v1<'info>(
    pool: &Pubkey,
    expected_deployment_domain: &[u8; 32],
    policy: &VerifierPolicyV1,
    registry_accounts: &[AccountInfo<'info>],
    verifier_program: &AccountInfo<'info>,
    proof: &AccountInfo<'info>,
    envelope: &HistoricalAnchorEnvelopeV1,
    statement_payload: &[u8],
    current_slot: u64,
    hash: HashFn,
) -> Result<AuthenticatedPairAfterstateV1, ProgramError> {
    pair_cu_checkpoint("aspis-pair-cu:verifier_plan_start");
    let plan = plan_pair_verifier_dispatch_v1(
        pool,
        expected_deployment_domain,
        policy,
        registry_accounts,
        verifier_program,
        proof,
        envelope,
        statement_payload,
        current_slot,
        hash,
    )?;
    pair_cu_checkpoint("aspis-pair-cu:verifier_plan_complete");
    let mut runtime = SolanaPairVerifierRuntimeV1;
    invoke_pair_afterstate_verifier_with_runtime_v1(plan, verifier_program, proof, &mut runtime)
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::M31;
    use aspis_statement::pool_v1::{
        decode_pool_v1_pair_verifier_request_v1, encode_pool_v1_pair_verifier_result_v1,
        encode_verifier_registry_entry_v1, encode_verifier_registry_v1, PoolV1TransitionKind,
        VerifierEntryStatusV1, VerifierRegistryEntryV1, VerifierRegistryV1,
        POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
    };
    use sha2::{Digest as _, Sha256};
    use solana_program::clock::Epoch;

    use crate::registry::{pool_v1_verifier_entry_address, pool_v1_verifier_registry_address};

    fn sha256(parts: &[&[u8]]) -> [u8; 32] {
        let mut hash = Sha256::new();
        for part in parts {
            hash.update(part);
        }
        hash.finalize().into()
    }

    fn account<'a>(
        key: &'a Pubkey,
        owner: &'a Pubkey,
        lamports: &'a mut u64,
        data: &'a mut [u8],
        writable: bool,
        executable: bool,
    ) -> AccountInfo<'a> {
        AccountInfo::new(
            key,
            false,
            writable,
            lamports,
            data,
            owner,
            executable,
            Epoch::default(),
        )
    }

    struct MockRuntime {
        return_data: Option<(Pubkey, Vec<u8>)>,
        invoked_request: Vec<u8>,
    }

    impl PairVerifierRuntimeV1 for MockRuntime {
        fn clear_return_data(&mut self) {
            self.return_data = None;
        }

        fn invoke(
            &mut self,
            instruction: &Instruction,
            _account_infos: &[AccountInfo<'_>],
        ) -> Result<(), ProgramError> {
            self.invoked_request = instruction.data.clone();
            let request = decode_pool_v1_pair_verifier_request_v1(&instruction.data)
                .map_err(|_| ProgramError::InvalidInstructionData)?;
            assert_eq!(request.binding.proof_body_length, 30_504);
            let result = encode_pool_v1_pair_verifier_result_v1(&PoolV1PairVerifierResultV1 {
                output_pair: core::array::from_fn(|lane| M31(100 + lane as u32)),
            })
            .unwrap();
            self.return_data = Some((instruction.program_id, result.to_vec()));
            Ok(())
        }

        fn get_return_data(&mut self) -> Option<(Pubkey, Vec<u8>)> {
            self.return_data.clone()
        }
    }

    #[test]
    fn exact_sealed_proof_is_not_hashed_and_selected_result_is_captured() {
        let pool = Pubkey::new_unique();
        let registry_program = Pubkey::new_unique();
        let verifier = Pubkey::new_unique();
        let proof_key = Pubkey::new_unique();
        let loader = bpf_loader::id();
        let policy = VerifierPolicyV1 {
            flags: 0,
            registry_program: registry_program.to_bytes(),
            registry_authority: [7u8; 32],
            policy_binding: [8u8; 32],
        };
        let profile = [9u8; 32];
        let release = [10u8; 32];
        let registry_key = pool_v1_verifier_registry_address(&registry_program, &pool).0;
        let entry_key =
            pool_v1_verifier_entry_address(&registry_program, &pool, &profile, &release).0;
        let mut registry_data = encode_verifier_registry_v1(&VerifierRegistryV1 {
            flags: 0,
            pool: pool.to_bytes(),
            authority: policy.registry_authority,
            policy_binding: policy.policy_binding,
            generation: 1,
            minimum_activation_delay_slots: 1,
        })
        .unwrap();
        let mut entry_data = encode_verifier_registry_entry_v1(&VerifierRegistryEntryV1 {
            status: VerifierEntryStatusV1::Active,
            statement_version: POOL_V1_HISTORICAL_ANCHOR_VERSION,
            pool: pool.to_bytes(),
            policy_binding: policy.policy_binding,
            verifier_program: verifier.to_bytes(),
            profile_binding: profile,
            release_binding: release,
            activation_slot: 0,
            retirement_slot: POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
        })
        .unwrap();
        let mut proof_data = vec![0u8; POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES + 30_504];
        proof_data[..4].copy_from_slice(&POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC);
        proof_data[4..8].copy_from_slice(&30_504u32.to_le_bytes());
        proof_data[POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES..].fill(0xa5);
        let mut zero_data = [];
        let mut registry_lamports = 1;
        let mut entry_lamports = 1;
        let mut verifier_lamports = 1;
        let mut proof_lamports = 1;
        let registry = account(
            &registry_key,
            &registry_program,
            &mut registry_lamports,
            &mut registry_data,
            false,
            false,
        );
        let entry = account(
            &entry_key,
            &registry_program,
            &mut entry_lamports,
            &mut entry_data,
            false,
            false,
        );
        let verifier_account = account(
            &verifier,
            &loader,
            &mut verifier_lamports,
            &mut zero_data,
            false,
            true,
        );
        let proof = account(
            &proof_key,
            &verifier,
            &mut proof_lamports,
            &mut proof_data,
            false,
            false,
        );
        let envelope = HistoricalAnchorEnvelopeV1 {
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            pool: pool.to_bytes(),
            deployment_domain: [11u8; 32],
            anchor_sequence: 0,
            anchor_root: [M31::ZERO; 8],
            nullifier: core::array::from_fn(|lane| M31(20 + lane as u32)),
            verifier_profile: profile,
            verifier_release: release,
        };
        let statement = [12u8; 216];
        let plan = plan_pair_verifier_dispatch_v1(
            &pool,
            &envelope.deployment_domain,
            &policy,
            &[registry, entry],
            &verifier_account,
            &proof,
            &envelope,
            &statement,
            10,
            sha256,
        )
        .unwrap();
        assert_eq!(plan.request_bytes.len(), 456);
        let mut runtime = MockRuntime {
            return_data: None,
            invoked_request: Vec::new(),
        };
        let result =
            invoke_pair_verifier_with_runtime_v1(plan, &verifier_account, &proof, &mut runtime)
                .unwrap();
        assert_eq!(result.output_pair[0], M31(100));
        assert_eq!(runtime.invoked_request.len(), 456);
    }

    #[test]
    fn trailing_proof_bytes_are_rejected_without_a_body_hash_pass() {
        let verifier = Pubkey::new_unique();
        let proof_key = Pubkey::new_unique();
        let loader = bpf_loader::id();
        let mut verifier_data = [];
        let mut proof_data = vec![0u8; POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES + 2];
        proof_data[..4].copy_from_slice(&POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC);
        proof_data[4..8].copy_from_slice(&1u32.to_le_bytes());
        let mut verifier_lamports = 1;
        let mut proof_lamports = 1;
        let verifier_account = account(
            &verifier,
            &loader,
            &mut verifier_lamports,
            &mut verifier_data,
            false,
            true,
        );
        let proof = account(
            &proof_key,
            &verifier,
            &mut proof_lamports,
            &mut proof_data,
            false,
            false,
        );
        assert_eq!(
            derive_pair_verifier_account_claim_v1(&verifier_account, &proof),
            Err(PoolV1ProgramError::VerifierProofBindingMismatch.into())
        );
    }
}
