//! Read-only Pool V1 authenticated-verifier dispatch and capture.
//!
//! This module composes the already-reviewed registry selection with the exact
//! P3a envelope, selected executable program account and sealed proof account.
//! P3d produces the exact request and sole acceptable fixed return-data result.
//! P3e can invoke that selected verifier through one exact read-only CPI and
//! authenticate the immediately captured return data. It writes no Pool,
//! marker, tree, vault, registry, proof, or verifier account. The Pool
//! entrypoint reaches it only from private-transfer and withdrawal processing
//! after all Pool-side preflight checks.

extern crate alloc;

use alloc::{vec, vec::Vec};
use aspis_core::transcript::HashFn;
use aspis_statement::pool_v1::{
    decode_historical_anchor_envelope_v1, decode_verifier_dispatch_result_v1,
    encode_verifier_dispatch_request_v1, encode_verifier_dispatch_result_v1,
    verifier_dispatch_binding_from_envelope_v1, verifier_proof_body_digest_v1,
    HistoricalAnchorEnvelopeV1, VerifierDispatchBindingV1, VerifierDispatchRequestV1,
    VerifierDispatchResultV1, VerifierPolicyV1, POOL_V1_HISTORICAL_ANCHOR_VERSION,
    POOL_V1_VERIFIER_DISPATCH_RESULT_BYTES, POOL_V1_VERIFIER_DISPATCH_SUCCESS_CODE,
    POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES, POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC,
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

const PROOF_LENGTH_OFFSET: usize = 4;
const PROOF_AUTHORITY_OFFSET: usize = 8;

/// Caller-supplied immutable identifiers that must match the actual accounts
/// and proof body before a request can be planned.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifierDispatchClaimV1 {
    pub verifier_program: [u8; 32],
    pub proof_account: [u8; 32],
    pub proof_body_digest: [u8; 32],
    pub proof_body_length: u32,
}

/// Derive the immutable claim from the exact accounts supplied to the Pool
/// instruction.  The full planner subsequently rechecks ownership, loader,
/// privileges, body bounds and digest; deriving here avoids a caller-provided
/// duplicate key/digest wire that could diverge from the account list.
pub(crate) fn derive_verifier_dispatch_claim_v1(
    verifier_program_account: &AccountInfo,
    proof_account: &AccountInfo,
    hash: HashFn,
) -> Result<VerifierDispatchClaimV1, ProgramError> {
    let data = proof_account.try_borrow_data()?;
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
    if proof_body_length == 0 {
        return Err(PoolV1ProgramError::VerifierProofBindingMismatch.into());
    }
    let body_end = POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES
        .checked_add(proof_body_length as usize)
        .ok_or(PoolV1ProgramError::VerifierProofBindingMismatch)?;
    if body_end > data.len() {
        return Err(PoolV1ProgramError::VerifierProofBindingMismatch.into());
    }
    let proof_body = &data[POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES..body_end];
    Ok(VerifierDispatchClaimV1 {
        verifier_program: verifier_program_account.key.to_bytes(),
        proof_account: proof_account.key.to_bytes(),
        proof_body_digest: verifier_proof_body_digest_v1(proof_body, hash),
        proof_body_length,
    })
}

/// Read-only output of complete pre-dispatch authentication.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlannedVerifierDispatchV1 {
    pub envelope: HistoricalAnchorEnvelopeV1,
    pub registry_generation: u64,
    pub request_binding: VerifierDispatchBindingV1,
    pub request_bytes: Vec<u8>,
    pub expected_result: VerifierDispatchResultV1,
    pub expected_result_bytes: [u8; POOL_V1_VERIFIER_DISPATCH_RESULT_BYTES],
}

/// Evidence available only after the freshly planned request has been invoked
/// and its exact selected-program return data has authenticated successfully.
/// The private field prevents external construction of accepted evidence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AuthenticatedVerifierDispatchV1 {
    plan: PlannedVerifierDispatchV1,
}

impl AuthenticatedVerifierDispatchV1 {
    pub fn plan(&self) -> &PlannedVerifierDispatchV1 {
        &self.plan
    }
}

trait VerifierDispatchRuntimeV1 {
    fn clear_return_data(&mut self);

    fn invoke(
        &mut self,
        instruction: &Instruction,
        account_infos: &[AccountInfo<'_>],
    ) -> Result<(), ProgramError>;

    fn get_return_data(&mut self) -> Option<(Pubkey, Vec<u8>)>;
}

struct SolanaVerifierDispatchRuntimeV1;

impl VerifierDispatchRuntimeV1 for SolanaVerifierDispatchRuntimeV1 {
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

fn supported_verifier_loader(owner: &Pubkey) -> bool {
    owner == &bpf_loader::id()
        || owner == &bpf_loader_upgradeable::id()
        || owner == &loader_v4::id()
}

fn require_selected_verifier_program_account(
    account: &AccountInfo,
    selected_program: &Pubkey,
) -> Result<(), ProgramError> {
    if account.key != selected_program
        || !account.executable
        || account.is_signer
        || account.is_writable
        || !supported_verifier_loader(account.owner)
    {
        return Err(PoolV1ProgramError::InvalidVerifierProgramAccount.into());
    }
    Ok(())
}

fn authenticate_proof_account_body_v1(
    account: &AccountInfo,
    selected_program: &Pubkey,
    pool: &Pubkey,
    claim: &VerifierDispatchClaimV1,
    hash: HashFn,
) -> Result<(), ProgramError> {
    if account.key.to_bytes() != claim.proof_account
        || account.key == selected_program
        || account.key == pool
        || account.owner != selected_program
        || account.executable
        || account.is_signer
        || account.is_writable
    {
        return Err(PoolV1ProgramError::InvalidVerifierProofAccount.into());
    }
    let data = account.try_borrow_data()?;
    if data.len() < POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES
        || data[..4] != POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC
        || data[PROOF_AUTHORITY_OFFSET..POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES]
            .iter()
            .any(|byte| *byte != 0)
    {
        return Err(PoolV1ProgramError::InvalidVerifierProofAccount.into());
    }
    let declared_length = u32::from_le_bytes([
        data[PROOF_LENGTH_OFFSET],
        data[PROOF_LENGTH_OFFSET + 1],
        data[PROOF_LENGTH_OFFSET + 2],
        data[PROOF_LENGTH_OFFSET + 3],
    ]);
    if declared_length == 0 || declared_length != claim.proof_body_length {
        return Err(PoolV1ProgramError::VerifierProofBindingMismatch.into());
    }
    let body_end = POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES
        .checked_add(declared_length as usize)
        .ok_or(PoolV1ProgramError::VerifierProofBindingMismatch)?;
    if body_end > data.len() {
        return Err(PoolV1ProgramError::VerifierProofBindingMismatch.into());
    }
    let body = &data[POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES..body_end];
    if verifier_proof_body_digest_v1(body, hash) != claim.proof_body_digest {
        return Err(PoolV1ProgramError::VerifierProofBindingMismatch.into());
    }
    Ok(())
}

/// Authenticate every immutable input needed by the selected-verifier CPI and
/// freeze both the exact request and the only acceptable success result.
///
/// The Pool derives `statement_digest` internally from the exact supplied
/// payload, selected profile/release, length and frozen digest domain. Payload
/// semantics remain profile-dispatched and are not interpreted by this layer.
#[allow(clippy::too_many_arguments)]
pub fn plan_authenticated_verifier_dispatch_v1(
    pool: &Pubkey,
    expected_deployment_domain: &[u8; 32],
    policy: &VerifierPolicyV1,
    registry_accounts: &[AccountInfo],
    verifier_program_account: &AccountInfo,
    proof_account: &AccountInfo,
    encoded_envelope: &[u8],
    statement_payload: &[u8],
    claim: VerifierDispatchClaimV1,
    current_slot: u64,
    hash: HashFn,
) -> Result<PlannedVerifierDispatchV1, ProgramError> {
    let envelope = decode_historical_anchor_envelope_v1(encoded_envelope)
        .map_err(|_| PoolV1ProgramError::InvalidVerifierDispatchEnvelope)?;
    if envelope.pool != pool.to_bytes() || envelope.deployment_domain != *expected_deployment_domain
    {
        return Err(PoolV1ProgramError::VerifierDispatchIdentityMismatch.into());
    }

    let selected_program = Pubkey::new_from_array(claim.verifier_program);
    let authenticated_selection = authenticate_verifier_selection_v1(
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
    require_selected_verifier_program_account(verifier_program_account, &selected_program)?;
    authenticate_proof_account_body_v1(proof_account, &selected_program, pool, &claim, hash)?;

    if !authenticated_selection.matches(
        envelope.pool,
        claim.verifier_program,
        envelope.verifier_profile,
        envelope.verifier_release,
        POOL_V1_HISTORICAL_ANCHOR_VERSION,
    ) {
        return Err(PoolV1ProgramError::VerifierDispatchIdentityMismatch.into());
    }

    let binding = verifier_dispatch_binding_from_envelope_v1(
        claim.verifier_program,
        &envelope,
        statement_payload,
        claim.proof_account,
        claim.proof_body_digest,
        claim.proof_body_length,
        hash,
    )
    .map_err(|_| PoolV1ProgramError::VerifierDispatchIdentityMismatch)?;
    let request = VerifierDispatchRequestV1 {
        binding,
        statement_payload,
    };
    let request_bytes = encode_verifier_dispatch_request_v1(&request, hash)
        .map_err(|_| PoolV1ProgramError::VerifierDispatchIdentityMismatch)?;
    let expected_result = VerifierDispatchResultV1 {
        success_code: POOL_V1_VERIFIER_DISPATCH_SUCCESS_CODE,
        binding,
    };
    let expected_result_bytes = encode_verifier_dispatch_result_v1(&expected_result)
        .map_err(|_| PoolV1ProgramError::VerifierDispatchIdentityMismatch)?;

    Ok(PlannedVerifierDispatchV1 {
        envelope,
        registry_generation: authenticated_selection.registry_generation(),
        request_binding: binding,
        request_bytes,
        expected_result,
        expected_result_bytes,
    })
}

/// Authenticate an already-snapshotted return-data pair without calling the
/// Solana runtime. Future composition must call `get_return_data` immediately
/// after the selected CPI and pass its `(program_id, bytes)` here unchanged.
pub fn authenticate_verifier_return_data_v1(
    expected: &PlannedVerifierDispatchV1,
    returned_program_id: &Pubkey,
    returned_data: &[u8],
) -> Result<(), ProgramError> {
    let selected_program = Pubkey::new_from_array(expected.request_binding.verifier_program);
    if returned_program_id != &selected_program {
        return Err(PoolV1ProgramError::InvalidVerifierReturnProgram.into());
    }
    if returned_data.len() != POOL_V1_VERIFIER_DISPATCH_RESULT_BYTES {
        return Err(PoolV1ProgramError::InvalidVerifierReturnData.into());
    }
    let returned = decode_verifier_dispatch_result_v1(returned_data)
        .map_err(|_| PoolV1ProgramError::InvalidVerifierReturnData)?;
    if returned != expected.expected_result || returned_data != expected.expected_result_bytes {
        return Err(PoolV1ProgramError::VerifierResultBindingMismatch.into());
    }
    Ok(())
}

fn require_exact_readonly_cpi_accounts_v1(
    plan: &PlannedVerifierDispatchV1,
    verifier_program_account: &AccountInfo<'_>,
    proof_account: &AccountInfo<'_>,
) -> Result<Pubkey, ProgramError> {
    let selected_program = Pubkey::new_from_array(plan.request_binding.verifier_program);
    require_selected_verifier_program_account(verifier_program_account, &selected_program)?;
    if proof_account.key.to_bytes() != plan.request_binding.proof_account
        || proof_account.owner != &selected_program
        || proof_account.executable
        || proof_account.is_signer
        || proof_account.is_writable
        || plan.expected_result.binding != plan.request_binding
    {
        return Err(PoolV1ProgramError::InvalidVerifierProofAccount.into());
    }
    Ok(selected_program)
}

/// Consume only a freshly constructed plan through one exact read-only CPI.
///
/// The invoking primitive is private, so an external caller cannot submit a
/// fabricated `PlannedVerifierDispatchV1`. It nevertheless rechecks the actual
/// verifier/proof identities and privileges against the plan before deriving
/// the instruction. The sole instruction meta is the nonsigning, read-only
/// sealed proof account; the executable verifier account is supplied to the
/// runtime only as the CPI program account.
fn invoke_freshly_planned_verifier_v1<'info, R: VerifierDispatchRuntimeV1>(
    plan: PlannedVerifierDispatchV1,
    verifier_program_account: &AccountInfo<'info>,
    proof_account: &AccountInfo<'info>,
    runtime: &mut R,
) -> Result<AuthenticatedVerifierDispatchV1, ProgramError> {
    let selected_program =
        require_exact_readonly_cpi_accounts_v1(&plan, verifier_program_account, proof_account)?;
    let instruction = Instruction {
        program_id: selected_program,
        accounts: vec![AccountMeta::new_readonly(*proof_account.key, false)],
        data: plan.request_bytes.clone(),
    };
    let account_infos = [proof_account.clone(), verifier_program_account.clone()];

    // This ordering is security-critical. Even though the current runtime also
    // clears return data on CPI entry, explicitly clear the Pool's buffer so a
    // successful callee that returns nothing cannot inherit an acceptable
    // stale image in either the production runtime or an equivalent harness.
    runtime.clear_return_data();
    runtime.invoke(&instruction, &account_infos)?;
    let returned = runtime
        .get_return_data()
        .ok_or(PoolV1ProgramError::MissingVerifierReturnData)?;

    authenticate_verifier_return_data_v1(&plan, &returned.0, &returned.1)?;
    Ok(AuthenticatedVerifierDispatchV1 { plan })
}

#[allow(clippy::too_many_arguments)]
fn dispatch_authenticated_verifier_readonly_with_runtime_v1<'info, R: VerifierDispatchRuntimeV1>(
    pool: &Pubkey,
    expected_deployment_domain: &[u8; 32],
    policy: &VerifierPolicyV1,
    registry_accounts: &[AccountInfo<'info>],
    verifier_program_account: &AccountInfo<'info>,
    proof_account: &AccountInfo<'info>,
    encoded_envelope: &[u8],
    statement_payload: &[u8],
    claim: VerifierDispatchClaimV1,
    current_slot: u64,
    hash: HashFn,
    runtime: &mut R,
) -> Result<AuthenticatedVerifierDispatchV1, ProgramError> {
    let plan = plan_authenticated_verifier_dispatch_v1(
        pool,
        expected_deployment_domain,
        policy,
        registry_accounts,
        verifier_program_account,
        proof_account,
        encoded_envelope,
        statement_payload,
        claim,
        current_slot,
        hash,
    )?;
    invoke_freshly_planned_verifier_v1(plan, verifier_program_account, proof_account, runtime)
}

/// Plan, invoke and authenticate one selected verifier without any Pool write.
///
/// This is a composition function rather than a standalone instruction
/// handler. The Pool entrypoint calls it with its runtime-derived identity and
/// exact top-level accounts. The selected verifier must implement the
/// separately reviewed profile-specific ASVQ handler before this path can be
/// exercised against a real proof.
#[allow(clippy::too_many_arguments)]
pub fn dispatch_authenticated_verifier_readonly_v1<'info>(
    pool: &Pubkey,
    expected_deployment_domain: &[u8; 32],
    policy: &VerifierPolicyV1,
    registry_accounts: &[AccountInfo<'info>],
    verifier_program_account: &AccountInfo<'info>,
    proof_account: &AccountInfo<'info>,
    encoded_envelope: &[u8],
    statement_payload: &[u8],
    claim: VerifierDispatchClaimV1,
    current_slot: u64,
    hash: HashFn,
) -> Result<AuthenticatedVerifierDispatchV1, ProgramError> {
    let mut runtime = SolanaVerifierDispatchRuntimeV1;
    dispatch_authenticated_verifier_readonly_with_runtime_v1(
        pool,
        expected_deployment_domain,
        policy,
        registry_accounts,
        verifier_program_account,
        proof_account,
        encoded_envelope,
        statement_payload,
        claim,
        current_slot,
        hash,
        &mut runtime,
    )
}

#[cfg(test)]
mod tests {
    use aspis_core::field::M31;
    use aspis_statement::{
        pool_v1::{
            decode_verifier_dispatch_request_v1, encode_historical_anchor_envelope_v1,
            encode_verifier_registry_entry_v1, encode_verifier_registry_v1,
            verifier_statement_payload_digest_v1, HistoricalAnchorEnvelopeV1, PoolV1TransitionKind,
            VerifierEntryStatusV1, VerifierRegistryEntryV1, VerifierRegistryV1,
            POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
        },
        poseidon2::Digest,
    };
    use sha2::{Digest as _, Sha256};
    use solana_program::clock::Epoch;
    use std::{vec, vec::Vec};

    use super::*;
    use crate::registry::{pool_v1_verifier_entry_address, pool_v1_verifier_registry_address};

    fn sha256(inputs: &[&[u8]]) -> [u8; 32] {
        let mut hash = Sha256::new();
        for input in inputs {
            hash.update(input);
        }
        hash.finalize().into()
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn account<'a>(
        key: &'a Pubkey,
        owner: &'a Pubkey,
        lamports: &'a mut u64,
        data: &'a mut [u8],
        signer: bool,
        writable: bool,
        executable: bool,
    ) -> AccountInfo<'a> {
        AccountInfo::new(
            key,
            signer,
            writable,
            lamports,
            data,
            owner,
            executable,
            Epoch::default(),
        )
    }

    #[derive(Clone, Copy)]
    struct Keys {
        pool: Pubkey,
        registry_program: Pubkey,
        verifier_program: Pubkey,
        proof: Pubkey,
        loader: Pubkey,
    }

    fn keys() -> Keys {
        Keys {
            pool: Pubkey::new_unique(),
            registry_program: Pubkey::new_unique(),
            verifier_program: Pubkey::new_unique(),
            proof: Pubkey::new_unique(),
            loader: bpf_loader_upgradeable::id(),
        }
    }

    fn policy(keys: Keys) -> VerifierPolicyV1 {
        VerifierPolicyV1 {
            flags: 0,
            registry_program: keys.registry_program.to_bytes(),
            registry_authority: [7u8; 32],
            policy_binding: [8u8; 32],
        }
    }

    fn envelope(keys: Keys) -> HistoricalAnchorEnvelopeV1 {
        HistoricalAnchorEnvelopeV1 {
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            pool: keys.pool.to_bytes(),
            deployment_domain: [2u8; 32],
            anchor_sequence: 44,
            anchor_root: digest(10),
            nullifier: digest(100),
            verifier_profile: [10u8; 32],
            verifier_release: [11u8; 32],
        }
    }

    fn registry(keys: Keys) -> VerifierRegistryV1 {
        VerifierRegistryV1 {
            flags: 0,
            pool: keys.pool.to_bytes(),
            authority: [7u8; 32],
            policy_binding: [8u8; 32],
            generation: 3,
            minimum_activation_delay_slots: 32,
        }
    }

    fn entry(keys: Keys) -> VerifierRegistryEntryV1 {
        VerifierRegistryEntryV1 {
            status: VerifierEntryStatusV1::Active,
            statement_version: POOL_V1_HISTORICAL_ANCHOR_VERSION,
            pool: keys.pool.to_bytes(),
            verifier_program: keys.verifier_program.to_bytes(),
            profile_binding: [10u8; 32],
            release_binding: [11u8; 32],
            activation_slot: 100,
            retirement_slot: POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
            policy_binding: [8u8; 32],
        }
    }

    fn proof_data(body: &[u8]) -> std::vec::Vec<u8> {
        let mut data = vec![0u8; POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES + body.len()];
        data[..4].copy_from_slice(&POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC);
        data[4..8].copy_from_slice(&(body.len() as u32).to_le_bytes());
        data[POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES..].copy_from_slice(body);
        data
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum RuntimeEvent {
        Clear,
        Invoke,
        Get,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum MockBehavior {
        Success,
        CalleeError,
        NoReturnData,
        WrongProgram,
        AlteredResult,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct ObservedInvoke {
        program_id: Pubkey,
        account_metas: Vec<AccountMeta>,
        account_infos: Vec<(Pubkey, bool, bool, bool)>,
        data: Vec<u8>,
    }

    struct MockDispatchRuntime {
        behavior: MockBehavior,
        events: Vec<RuntimeEvent>,
        invokes: Vec<ObservedInvoke>,
        return_data: Option<(Pubkey, Vec<u8>)>,
    }

    impl MockDispatchRuntime {
        fn new(behavior: MockBehavior) -> Self {
            Self {
                behavior,
                events: Vec::new(),
                invokes: Vec::new(),
                return_data: None,
            }
        }
    }

    impl VerifierDispatchRuntimeV1 for MockDispatchRuntime {
        fn clear_return_data(&mut self) {
            self.events.push(RuntimeEvent::Clear);
            self.return_data = None;
        }

        fn invoke(
            &mut self,
            instruction: &Instruction,
            account_infos: &[AccountInfo<'_>],
        ) -> Result<(), ProgramError> {
            self.events.push(RuntimeEvent::Invoke);
            self.invokes.push(ObservedInvoke {
                program_id: instruction.program_id,
                account_metas: instruction.accounts.clone(),
                account_infos: account_infos
                    .iter()
                    .map(|account| {
                        (
                            *account.key,
                            account.is_signer,
                            account.is_writable,
                            account.executable,
                        )
                    })
                    .collect(),
                data: instruction.data.clone(),
            });

            if self.behavior == MockBehavior::CalleeError {
                return Err(ProgramError::Custom(0x00CA_11EE));
            }
            if self.behavior == MockBehavior::NoReturnData {
                return Ok(());
            }

            let request = decode_verifier_dispatch_request_v1(&instruction.data, sha256)
                .map_err(|_| ProgramError::InvalidInstructionData)?;
            let mut result = encode_verifier_dispatch_result_v1(&VerifierDispatchResultV1 {
                success_code: POOL_V1_VERIFIER_DISPATCH_SUCCESS_CODE,
                binding: request.binding,
            })
            .map_err(|_| ProgramError::InvalidInstructionData)?
            .to_vec();
            let returning_program = if self.behavior == MockBehavior::WrongProgram {
                Pubkey::new_unique()
            } else {
                instruction.program_id
            };
            if self.behavior == MockBehavior::AlteredResult {
                result[248] ^= 1;
            }
            self.return_data = Some((returning_program, result));
            Ok(())
        }

        fn get_return_data(&mut self) -> Option<(Pubkey, Vec<u8>)> {
            self.events.push(RuntimeEvent::Get);
            self.return_data.clone()
        }
    }

    #[derive(Clone, Copy, Default)]
    struct DispatchAccountConfusion {
        verifier_signer: bool,
        verifier_writable: bool,
        proof_signer: bool,
        proof_writable: bool,
        extra_registry_account: bool,
    }

    fn run_injected_dispatch(
        keys: Keys,
        runtime: &mut MockDispatchRuntime,
        confusion: DispatchAccountConfusion,
    ) -> Result<AuthenticatedVerifierDispatchV1, ProgramError> {
        let envelope = envelope(keys);
        let encoded_envelope = encode_historical_anchor_envelope_v1(&envelope).unwrap();
        let body = b"sealed-proof-body";
        let statement_payload = b"canonical-profile-statement-v1";
        let claim = VerifierDispatchClaimV1 {
            verifier_program: keys.verifier_program.to_bytes(),
            proof_account: keys.proof.to_bytes(),
            proof_body_digest: verifier_proof_body_digest_v1(body, sha256),
            proof_body_length: body.len() as u32,
        };
        let registry_key = pool_v1_verifier_registry_address(&keys.registry_program, &keys.pool).0;
        let entry_key = pool_v1_verifier_entry_address(
            &keys.registry_program,
            &keys.pool,
            &envelope.verifier_profile,
            &envelope.verifier_release,
        )
        .0;
        let extra_key = Pubkey::new_unique();
        let mut registry_data = encode_verifier_registry_v1(&registry(keys)).unwrap();
        let mut entry_data = encode_verifier_registry_entry_v1(&entry(keys)).unwrap();
        let mut extra_data = [];
        let mut verifier_data = [];
        let mut proof_data = proof_data(body);
        let registry_before = registry_data;
        let entry_before = entry_data;
        let proof_before = proof_data.clone();
        let mut registry_lamports = 1;
        let mut entry_lamports = 1;
        let mut extra_lamports = 1;
        let mut verifier_lamports = 1;
        let mut proof_lamports = 1;
        let registry_account = account(
            &registry_key,
            &keys.registry_program,
            &mut registry_lamports,
            &mut registry_data,
            false,
            false,
            false,
        );
        let entry_account = account(
            &entry_key,
            &keys.registry_program,
            &mut entry_lamports,
            &mut entry_data,
            false,
            false,
            false,
        );
        let extra_account = account(
            &extra_key,
            &keys.registry_program,
            &mut extra_lamports,
            &mut extra_data,
            false,
            false,
            false,
        );
        let registry_accounts = if confusion.extra_registry_account {
            vec![registry_account, entry_account, extra_account]
        } else {
            vec![registry_account, entry_account]
        };
        let verifier_account = account(
            &keys.verifier_program,
            &keys.loader,
            &mut verifier_lamports,
            &mut verifier_data,
            confusion.verifier_signer,
            confusion.verifier_writable,
            true,
        );
        let proof_account = account(
            &keys.proof,
            &keys.verifier_program,
            &mut proof_lamports,
            &mut proof_data,
            confusion.proof_signer,
            confusion.proof_writable,
            false,
        );
        let result = dispatch_authenticated_verifier_readonly_with_runtime_v1(
            &keys.pool,
            &envelope.deployment_domain,
            &policy(keys),
            &registry_accounts,
            &verifier_account,
            &proof_account,
            &encoded_envelope,
            statement_payload,
            claim,
            200,
            sha256,
            runtime,
        );
        drop(registry_accounts);
        drop(verifier_account);
        drop(proof_account);
        assert_eq!(registry_data, registry_before);
        assert_eq!(entry_data, entry_before);
        assert_eq!(proof_data, proof_before);
        result
    }

    #[test]
    fn readonly_cpi_uses_exact_selected_program_proof_meta_and_clear_invoke_get_order() {
        let keys = keys();
        let mut runtime = MockDispatchRuntime::new(MockBehavior::Success);
        let authenticated =
            run_injected_dispatch(keys, &mut runtime, DispatchAccountConfusion::default()).unwrap();

        assert_eq!(
            runtime.events,
            vec![RuntimeEvent::Clear, RuntimeEvent::Invoke, RuntimeEvent::Get]
        );
        assert_eq!(runtime.invokes.len(), 1);
        let observed = &runtime.invokes[0];
        assert_eq!(observed.program_id, keys.verifier_program);
        assert_eq!(
            observed.account_metas,
            vec![AccountMeta::new_readonly(keys.proof, false)]
        );
        assert_eq!(
            observed.account_infos,
            vec![
                (keys.proof, false, false, false),
                (keys.verifier_program, false, false, true),
            ]
        );
        assert_eq!(observed.data, authenticated.plan().request_bytes);
    }

    #[test]
    fn cpi_error_missing_wrong_program_and_altered_result_fail_closed() {
        let cases = [
            (
                MockBehavior::CalleeError,
                ProgramError::Custom(0x00CA_11EE),
                vec![RuntimeEvent::Clear, RuntimeEvent::Invoke],
            ),
            (
                MockBehavior::NoReturnData,
                PoolV1ProgramError::MissingVerifierReturnData.into(),
                vec![RuntimeEvent::Clear, RuntimeEvent::Invoke, RuntimeEvent::Get],
            ),
            (
                MockBehavior::WrongProgram,
                PoolV1ProgramError::InvalidVerifierReturnProgram.into(),
                vec![RuntimeEvent::Clear, RuntimeEvent::Invoke, RuntimeEvent::Get],
            ),
            (
                MockBehavior::AlteredResult,
                PoolV1ProgramError::VerifierResultBindingMismatch.into(),
                vec![RuntimeEvent::Clear, RuntimeEvent::Invoke, RuntimeEvent::Get],
            ),
        ];
        for (behavior, expected_error, expected_events) in cases {
            let mut runtime = MockDispatchRuntime::new(behavior);
            let result =
                run_injected_dispatch(keys(), &mut runtime, DispatchAccountConfusion::default());
            assert_eq!(result, Err(expected_error));
            assert_eq!(runtime.events, expected_events);
        }
    }

    #[test]
    fn explicit_clear_prevents_acceptable_stale_result_reuse() {
        let keys = keys();
        let mut runtime = MockDispatchRuntime::new(MockBehavior::Success);
        let first =
            run_injected_dispatch(keys, &mut runtime, DispatchAccountConfusion::default()).unwrap();
        assert_eq!(
            runtime.return_data,
            Some((
                keys.verifier_program,
                first.plan().expected_result_bytes.to_vec(),
            ))
        );

        runtime.behavior = MockBehavior::NoReturnData;
        runtime.events.clear();
        runtime.invokes.clear();
        assert_eq!(
            run_injected_dispatch(keys, &mut runtime, DispatchAccountConfusion::default(),),
            Err(PoolV1ProgramError::MissingVerifierReturnData.into())
        );
        assert_eq!(
            runtime.events,
            vec![RuntimeEvent::Clear, RuntimeEvent::Invoke, RuntimeEvent::Get]
        );
        assert_eq!(runtime.return_data, None);
    }

    #[test]
    fn extra_writable_or_signer_account_confusion_never_reaches_runtime() {
        let cases = [
            (
                DispatchAccountConfusion {
                    extra_registry_account: true,
                    ..DispatchAccountConfusion::default()
                },
                ProgramError::InvalidArgument,
            ),
            (
                DispatchAccountConfusion {
                    verifier_signer: true,
                    ..DispatchAccountConfusion::default()
                },
                PoolV1ProgramError::InvalidVerifierProgramAccount.into(),
            ),
            (
                DispatchAccountConfusion {
                    verifier_writable: true,
                    ..DispatchAccountConfusion::default()
                },
                PoolV1ProgramError::InvalidVerifierProgramAccount.into(),
            ),
            (
                DispatchAccountConfusion {
                    proof_signer: true,
                    ..DispatchAccountConfusion::default()
                },
                PoolV1ProgramError::InvalidVerifierProofAccount.into(),
            ),
            (
                DispatchAccountConfusion {
                    proof_writable: true,
                    ..DispatchAccountConfusion::default()
                },
                PoolV1ProgramError::InvalidVerifierProofAccount.into(),
            ),
        ];
        for (confusion, expected_error) in cases {
            let mut runtime = MockDispatchRuntime::new(MockBehavior::Success);
            assert_eq!(
                run_injected_dispatch(keys(), &mut runtime, confusion),
                Err(expected_error)
            );
            assert!(runtime.events.is_empty());
            assert!(runtime.invokes.is_empty());
        }
    }

    #[test]
    fn exact_registry_envelope_program_and_sealed_proof_plan_one_result() {
        let keys = keys();
        let envelope = envelope(keys);
        let encoded_envelope = encode_historical_anchor_envelope_v1(&envelope).unwrap();
        let body = b"sealed-proof-body";
        let statement_payload = b"canonical-profile-statement-v1";
        let claim = VerifierDispatchClaimV1 {
            verifier_program: keys.verifier_program.to_bytes(),
            proof_account: keys.proof.to_bytes(),
            proof_body_digest: verifier_proof_body_digest_v1(body, sha256),
            proof_body_length: body.len() as u32,
        };
        let registry_key = pool_v1_verifier_registry_address(&keys.registry_program, &keys.pool).0;
        let entry_key = pool_v1_verifier_entry_address(
            &keys.registry_program,
            &keys.pool,
            &envelope.verifier_profile,
            &envelope.verifier_release,
        )
        .0;
        let mut registry_data = encode_verifier_registry_v1(&registry(keys)).unwrap();
        let mut entry_data = encode_verifier_registry_entry_v1(&entry(keys)).unwrap();
        let mut program_data = [];
        let mut proof_data = proof_data(body);
        let registry_before = registry_data;
        let entry_before = entry_data;
        let proof_before = proof_data.clone();
        let mut registry_lamports = 1;
        let mut entry_lamports = 1;
        let mut program_lamports = 1;
        let mut proof_lamports = 1;
        let registry_account = account(
            &registry_key,
            &keys.registry_program,
            &mut registry_lamports,
            &mut registry_data,
            false,
            false,
            false,
        );
        let entry_account = account(
            &entry_key,
            &keys.registry_program,
            &mut entry_lamports,
            &mut entry_data,
            false,
            false,
            false,
        );
        let verifier_account = account(
            &keys.verifier_program,
            &keys.loader,
            &mut program_lamports,
            &mut program_data,
            false,
            false,
            true,
        );
        let proof_account = account(
            &keys.proof,
            &keys.verifier_program,
            &mut proof_lamports,
            &mut proof_data,
            false,
            false,
            false,
        );
        let plan = plan_authenticated_verifier_dispatch_v1(
            &keys.pool,
            &envelope.deployment_domain,
            &policy(keys),
            &[registry_account, entry_account],
            &verifier_account,
            &proof_account,
            &encoded_envelope,
            statement_payload,
            claim,
            200,
            sha256,
        )
        .unwrap();
        assert_eq!(plan.registry_generation, 3);
        assert_eq!(plan.request_binding, plan.expected_result.binding);
        assert_eq!(plan.request_binding.proof_body_length, body.len() as u32);
        assert_eq!(
            plan.request_binding.proof_body_digest,
            claim.proof_body_digest
        );
        assert_eq!(
            plan.request_binding.statement_payload_length,
            statement_payload.len() as u32
        );
        assert_eq!(
            plan.request_binding.statement_digest,
            verifier_statement_payload_digest_v1(
                1,
                &envelope.verifier_profile,
                &envelope.verifier_release,
                statement_payload,
                sha256,
            )
            .unwrap()
        );
        assert_eq!(
            &plan.request_bytes
                [aspis_statement::pool_v1::POOL_V1_VERIFIER_DISPATCH_BINDING_PREFIX_BYTES..],
            statement_payload
        );
        assert_eq!(plan.request_bytes.len(), 384 + statement_payload.len());
        assert_eq!(plan.expected_result_bytes.len(), 384);
        assert_eq!(registry_data, registry_before);
        assert_eq!(entry_data, entry_before);
        assert_eq!(proof_data, proof_before);
        assert_eq!(
            authenticate_verifier_return_data_v1(
                &plan,
                &keys.verifier_program,
                &plan.expected_result_bytes,
            ),
            Ok(())
        );
    }

    #[test]
    fn return_data_rejects_wrong_program_size_code_or_any_binding_substitution() {
        let binding = verifier_dispatch_binding_from_envelope_v1(
            [5u8; 32],
            &HistoricalAnchorEnvelopeV1 {
                transition_kind: PoolV1TransitionKind::Withdrawal,
                pool: [1u8; 32],
                deployment_domain: [2u8; 32],
                anchor_sequence: 7,
                anchor_root: digest(10),
                nullifier: digest(100),
                verifier_profile: [3u8; 32],
                verifier_release: [4u8; 32],
            },
            b"canonical-profile-statement-v1",
            [8u8; 32],
            [9u8; 32],
            10,
            sha256,
        )
        .unwrap();
        let expected_result = VerifierDispatchResultV1 {
            success_code: POOL_V1_VERIFIER_DISPATCH_SUCCESS_CODE,
            binding,
        };
        let plan = PlannedVerifierDispatchV1 {
            envelope: HistoricalAnchorEnvelopeV1 {
                transition_kind: binding.transition_kind,
                pool: binding.pool,
                deployment_domain: binding.deployment_domain,
                anchor_sequence: binding.anchor_sequence,
                anchor_root: binding.anchor_root,
                nullifier: binding.nullifier,
                verifier_profile: binding.profile_binding,
                verifier_release: binding.release_binding,
            },
            registry_generation: 1,
            request_binding: binding,
            request_bytes: encode_verifier_dispatch_request_v1(
                &VerifierDispatchRequestV1 {
                    binding,
                    statement_payload: b"canonical-profile-statement-v1",
                },
                sha256,
            )
            .unwrap(),
            expected_result,
            expected_result_bytes: encode_verifier_dispatch_result_v1(&expected_result).unwrap(),
        };
        let expected_program = Pubkey::new_from_array(binding.verifier_program);
        assert_eq!(
            authenticate_verifier_return_data_v1(
                &plan,
                &Pubkey::new_unique(),
                &plan.expected_result_bytes,
            ),
            Err(PoolV1ProgramError::InvalidVerifierReturnProgram.into())
        );
        assert_eq!(
            authenticate_verifier_return_data_v1(
                &plan,
                &expected_program,
                &plan.expected_result_bytes[..383],
            ),
            Err(PoolV1ProgramError::InvalidVerifierReturnData.into())
        );
        let mut changed_code = plan.expected_result_bytes;
        changed_code[8..12].copy_from_slice(&0u32.to_le_bytes());
        assert_eq!(
            authenticate_verifier_return_data_v1(&plan, &expected_program, &changed_code),
            Err(PoolV1ProgramError::InvalidVerifierReturnData.into())
        );
        let mut changed_binding = plan.expected_result_bytes;
        changed_binding[248] ^= 1;
        assert_eq!(
            authenticate_verifier_return_data_v1(&plan, &expected_program, &changed_binding),
            Err(PoolV1ProgramError::VerifierResultBindingMismatch.into())
        );
    }

    #[test]
    fn proof_account_identity_privileges_header_length_and_digest_fail_closed() {
        let keys = keys();
        let body = b"proof";
        let claim = VerifierDispatchClaimV1 {
            verifier_program: keys.verifier_program.to_bytes(),
            proof_account: keys.proof.to_bytes(),
            proof_body_digest: verifier_proof_body_digest_v1(body, sha256),
            proof_body_length: body.len() as u32,
        };
        let mut lamports = 1;
        let mut data = proof_data(body);
        let wrong_key = Pubkey::new_unique();
        let wrong_address = account(
            &wrong_key,
            &keys.verifier_program,
            &mut lamports,
            &mut data,
            false,
            false,
            false,
        );
        assert_eq!(
            authenticate_proof_account_body_v1(
                &wrong_address,
                &keys.verifier_program,
                &keys.pool,
                &claim,
                sha256,
            ),
            Err(PoolV1ProgramError::InvalidVerifierProofAccount.into())
        );

        let mut data = proof_data(body);
        data[8] = 1;
        let occupied_authority = account(
            &keys.proof,
            &keys.verifier_program,
            &mut lamports,
            &mut data,
            false,
            false,
            false,
        );
        assert_eq!(
            authenticate_proof_account_body_v1(
                &occupied_authority,
                &keys.verifier_program,
                &keys.pool,
                &claim,
                sha256,
            ),
            Err(PoolV1ProgramError::InvalidVerifierProofAccount.into())
        );

        let mut data = proof_data(body);
        data[4..8].copy_from_slice(&4u32.to_le_bytes());
        let wrong_length = account(
            &keys.proof,
            &keys.verifier_program,
            &mut lamports,
            &mut data,
            false,
            false,
            false,
        );
        assert_eq!(
            authenticate_proof_account_body_v1(
                &wrong_length,
                &keys.verifier_program,
                &keys.pool,
                &claim,
                sha256,
            ),
            Err(PoolV1ProgramError::VerifierProofBindingMismatch.into())
        );

        let mut data = proof_data(b"other");
        let wrong_digest = account(
            &keys.proof,
            &keys.verifier_program,
            &mut lamports,
            &mut data,
            false,
            false,
            false,
        );
        assert_eq!(
            authenticate_proof_account_body_v1(
                &wrong_digest,
                &keys.verifier_program,
                &keys.pool,
                &claim,
                sha256,
            ),
            Err(PoolV1ProgramError::VerifierProofBindingMismatch.into())
        );
    }

    #[test]
    fn verifier_program_requires_exact_key_supported_loader_and_readonly_executable_privileges() {
        let selected = Pubkey::new_unique();
        let loader = bpf_loader_upgradeable::id();
        let mut lamports = 1;
        let mut data = [];
        let valid = account(
            &selected,
            &loader,
            &mut lamports,
            &mut data,
            false,
            false,
            true,
        );
        assert_eq!(
            require_selected_verifier_program_account(&valid, &selected),
            Ok(())
        );

        let foreign_loader = Pubkey::new_unique();
        let invalid = account(
            &selected,
            &foreign_loader,
            &mut lamports,
            &mut data,
            false,
            false,
            true,
        );
        assert_eq!(
            require_selected_verifier_program_account(&invalid, &selected),
            Err(PoolV1ProgramError::InvalidVerifierProgramAccount.into())
        );

        let invalid = account(
            &selected,
            &loader,
            &mut lamports,
            &mut data,
            false,
            true,
            true,
        );
        assert_eq!(
            require_selected_verifier_program_account(&invalid, &selected),
            Err(PoolV1ProgramError::InvalidVerifierProgramAccount.into())
        );
    }
}
