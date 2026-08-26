//! Composition of exact relayer RPC quorum receipts into coordinator inputs.
//!
//! This module performs no transport or signing. It consumes only typed RPC
//! requests and exact two-provider agreements, binds them to one successful
//! operator startup, and reconstructs the canonical relayer message before it
//! returns evidence accepted by the execution coordinator.

use bincode::Options as _;
use sha2::{Digest as _, Sha256};
use solana_transaction::versioned::VersionedTransaction;

use crate::{
    operator_execution::{
        RelayerNotFoundObservationV1, RelayerPendingObservationV1, RelayerSignatureObservationV1,
        RelayerSimulationArtifactV1,
    },
    operator_startup::{provider_set_digest_v1, OperatorStartupReceiptV1},
    relayer::RelayerPlanV1,
    relayer_execution_journal::{RelayerSimulationEvidenceV1, RelayerSubmissionEvidenceV1},
    relayer_rpc_json::{
        ExactRelayerSimulationRequestV1, ExactSendTransactionRequestV1,
        FinalizedAddressLookupTableBatchV1, FinalizedAddressLookupTablesRequestV1,
        FinalizedBlockHeightRequestV1, FinalizedFeeForMessageRequestV1, FinalizedFeeForMessageV1,
        FinalizedLatestBlockhashRequestV1, FinalizedLatestBlockhashV1, RelayerSignatureStatusRpcV1,
        SignatureStatusesRequestV1, SuccessfulRelayerSimulationRpcV1,
        RELAYER_RPC_MAX_TRANSACTION_WIRE_BYTES_V1,
    },
    relayer_rpc_quorum::{request_binding_digest_v1, RelayerRpcAgreementV1, RelayerRpcEndpointV1},
    relayer_transaction::{
        assemble_exact_unsigned_relayer_message_v1, relayer_simulation_accounts_sha256_v1,
        AuthenticatedAddressLookupTableV1, RelayerTransactionErrorV1,
    },
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelayerRpcCompositionErrorV1 {
    StartupReceiptMismatch,
    ProviderSetMismatch,
    WrongEndpoint,
    WrongRequestBinding,
    ContextOrderMismatch,
    MissingLookupAgreement,
    LookupAddressMismatch,
    LookupImageMismatch,
    InvalidUnsignedTransactionWire,
    CanonicalMessageMismatch,
    SignatureMismatch,
    MissingBlockHeightAgreement,
    UnexpectedBlockHeightAgreement,
    InvalidSignatureStatus,
    Transaction(RelayerTransactionErrorV1),
}

impl From<RelayerTransactionErrorV1> for RelayerRpcCompositionErrorV1 {
    fn from(error: RelayerTransactionErrorV1) -> Self {
        Self::Transaction(error)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct RelayerLookupQuorumInputsV1<'a> {
    request: &'a FinalizedAddressLookupTablesRequestV1,
    agreement: &'a RelayerRpcAgreementV1<FinalizedAddressLookupTableBatchV1>,
}

impl<'a> RelayerLookupQuorumInputsV1<'a> {
    pub fn new(
        request: &'a FinalizedAddressLookupTablesRequestV1,
        agreement: &'a RelayerRpcAgreementV1<FinalizedAddressLookupTableBatchV1>,
    ) -> Self {
        Self { request, agreement }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct RelayerSimulationQuorumInputsV1<'a> {
    latest_blockhash_request: &'a FinalizedLatestBlockhashRequestV1,
    latest_blockhash_agreement: &'a RelayerRpcAgreementV1<FinalizedLatestBlockhashV1>,
    lookup: Option<RelayerLookupQuorumInputsV1<'a>>,
    simulation_request: &'a ExactRelayerSimulationRequestV1,
    simulation_agreement: &'a RelayerRpcAgreementV1<SuccessfulRelayerSimulationRpcV1>,
    fee_request: &'a FinalizedFeeForMessageRequestV1,
    fee_agreement: &'a RelayerRpcAgreementV1<FinalizedFeeForMessageV1>,
}

impl<'a> RelayerSimulationQuorumInputsV1<'a> {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        latest_blockhash_request: &'a FinalizedLatestBlockhashRequestV1,
        latest_blockhash_agreement: &'a RelayerRpcAgreementV1<FinalizedLatestBlockhashV1>,
        lookup: Option<RelayerLookupQuorumInputsV1<'a>>,
        simulation_request: &'a ExactRelayerSimulationRequestV1,
        simulation_agreement: &'a RelayerRpcAgreementV1<SuccessfulRelayerSimulationRpcV1>,
        fee_request: &'a FinalizedFeeForMessageRequestV1,
        fee_agreement: &'a RelayerRpcAgreementV1<FinalizedFeeForMessageV1>,
    ) -> Self {
        Self {
            latest_blockhash_request,
            latest_blockhash_agreement,
            lookup,
            simulation_request,
            simulation_agreement,
            fee_request,
            fee_agreement,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct RelayerBlockHeightQuorumInputsV1<'a> {
    request: &'a FinalizedBlockHeightRequestV1,
    agreement: &'a RelayerRpcAgreementV1<u64>,
}

impl<'a> RelayerBlockHeightQuorumInputsV1<'a> {
    pub fn new(
        request: &'a FinalizedBlockHeightRequestV1,
        agreement: &'a RelayerRpcAgreementV1<u64>,
    ) -> Self {
        Self { request, agreement }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RelayerFinalizedStatusHintV1 {
    transaction_signature: [u8; 64],
    context_slot: u64,
    landed_slot: u64,
    succeeded: bool,
    execution_result_sha256: [u8; 32],
    provider_set_digest: [u8; 32],
    startup_receipt_digest: [u8; 32],
    status_request_id: u64,
    status_request_binding_sha256: [u8; 32],
}

impl RelayerFinalizedStatusHintV1 {
    pub fn transaction_signature(&self) -> &[u8; 64] {
        &self.transaction_signature
    }

    pub fn context_slot(&self) -> u64 {
        self.context_slot
    }

    pub fn landed_slot(&self) -> u64 {
        self.landed_slot
    }

    pub fn succeeded(&self) -> bool {
        self.succeeded
    }

    pub fn execution_result_sha256(&self) -> &[u8; 32] {
        &self.execution_result_sha256
    }

    pub fn provider_set_digest(&self) -> &[u8; 32] {
        &self.provider_set_digest
    }

    pub fn startup_receipt_digest(&self) -> &[u8; 32] {
        &self.startup_receipt_digest
    }

    pub fn status_request_id(&self) -> u64 {
        self.status_request_id
    }

    pub fn status_request_binding_sha256(&self) -> &[u8; 32] {
        &self.status_request_binding_sha256
    }

    #[cfg(test)]
    pub(crate) fn test_only_with_context_slot_v1(mut self, context_slot: u64) -> Self {
        self.context_slot = context_slot;
        self
    }
}

/// A finalized signature status is deliberately not coordinator-ready until
/// the separate two-provider finalized getBlock/root-page join is complete.
pub enum ComposedRelayerSignatureStatusV1 {
    CoordinatorReady(RelayerSignatureObservationV1),
    FinalizedBlockJoinRequired(RelayerFinalizedStatusHintV1),
    /// A finalized failed transaction must be journaled under a distinct
    /// failure ABI. It is not a blockhash-expiry observation.
    FinalizedFailureJoinRequired(RelayerFinalizedStatusHintV1),
}

/// Compose the exact blockhash, optional ALT, simulation and fee agreements
/// into the simulation artifact accepted by `RelayerExecutionPortV1`.
pub fn compose_relayer_simulation_artifact_v1(
    plan: &RelayerPlanV1,
    startup: &OperatorStartupReceiptV1,
    compute_unit_price_micro_lamports: u64,
    inputs: RelayerSimulationQuorumInputsV1<'_>,
) -> Result<RelayerSimulationArtifactV1, RelayerRpcCompositionErrorV1> {
    validate_agreement_v1(
        startup,
        RelayerRpcEndpointV1::FinalizedLatestBlockhash,
        inputs.latest_blockhash_request.request_id(),
        Some(inputs.latest_blockhash_request.min_context_slot()),
        &inputs.latest_blockhash_request.encode_json_v1(),
        inputs.latest_blockhash_agreement,
    )?;
    let latest = inputs.latest_blockhash_agreement.value();
    if latest.context_slot < plan.snapshot.observed_slot {
        return Err(RelayerRpcCompositionErrorV1::ContextOrderMismatch);
    }

    let mut predecessor_slot = latest.context_slot;
    let prefetched_lookup_tables = match inputs.lookup {
        Some(lookup) => {
            validate_agreement_v1(
                startup,
                RelayerRpcEndpointV1::FinalizedAddressLookupTables,
                lookup.request.request_id(),
                Some(lookup.request.min_context_slot()),
                &lookup.request.encode_json_v1(),
                lookup.agreement,
            )?;
            let batch = lookup.agreement.value();
            if lookup.request.min_context_slot() < predecessor_slot
                || batch.context_slot < predecessor_slot
            {
                return Err(RelayerRpcCompositionErrorV1::ContextOrderMismatch);
            }
            validate_lookup_addresses_v1(lookup.request.addresses(), &batch.lookup_tables)?;
            predecessor_slot = batch.context_slot;
            Some((lookup.request.addresses(), &batch.lookup_tables))
        }
        None => None,
    };

    validate_agreement_v1(
        startup,
        RelayerRpcEndpointV1::ExactSimulation,
        inputs.simulation_request.request_id(),
        Some(inputs.simulation_request.min_context_slot()),
        &inputs.simulation_request.encode_json_v1(),
        inputs.simulation_agreement,
    )?;
    let simulation = inputs.simulation_agreement.value();
    if inputs.simulation_request.min_context_slot() < predecessor_slot
        || simulation.simulated_at_slot < predecessor_slot
    {
        return Err(RelayerRpcCompositionErrorV1::ContextOrderMismatch);
    }
    match prefetched_lookup_tables {
        None => {
            if !inputs.simulation_request.lookup_addresses().is_empty()
                || !simulation.lookup_tables.is_empty()
            {
                return Err(RelayerRpcCompositionErrorV1::MissingLookupAgreement);
            }
        }
        Some((addresses, prefetched)) => {
            if addresses != inputs.simulation_request.lookup_addresses() {
                return Err(RelayerRpcCompositionErrorV1::LookupAddressMismatch);
            }
            validate_lookup_addresses_v1(addresses, &simulation.lookup_tables)?;
            if prefetched.len() != simulation.lookup_tables.len()
                || prefetched
                    .iter()
                    .zip(&simulation.lookup_tables)
                    .any(|(before, simulated)| !same_lookup_image_v1(before, simulated))
            {
                return Err(RelayerRpcCompositionErrorV1::LookupImageMismatch);
            }
        }
    }

    validate_agreement_v1(
        startup,
        RelayerRpcEndpointV1::FinalizedFeeForMessage,
        inputs.fee_request.request_id(),
        Some(inputs.fee_request.min_context_slot()),
        &inputs.fee_request.encode_json_v1(),
        inputs.fee_agreement,
    )?;
    let fee = inputs.fee_agreement.value();
    if inputs.fee_request.min_context_slot() < simulation.simulated_at_slot
        || fee.context_slot < simulation.simulated_at_slot
    {
        return Err(RelayerRpcCompositionErrorV1::ContextOrderMismatch);
    }

    let simulation_accounts_sha256 = relayer_simulation_accounts_sha256_v1(
        plan,
        simulation.simulated_at_slot,
        *startup.provider_set_digest(),
        &simulation.lookup_tables,
    )?;
    let evidence = RelayerSimulationEvidenceV1 {
        simulated_at_slot: simulation.simulated_at_slot,
        recent_blockhash: latest.blockhash,
        last_valid_block_height: latest.last_valid_block_height,
        fee_payer: plan.fee_payer.to_bytes(),
        unsigned_message_sha256: Sha256::digest(inputs.fee_request.serialized_message()).into(),
        simulation_result_sha256: simulation.simulation_result_sha256,
        simulation_accounts_sha256,
        startup_receipt_digest: *startup.receipt_digest(),
        compute_unit_limit: inputs.simulation_request.compute_unit_limit(),
        compute_unit_price_micro_lamports,
        compute_units_consumed: simulation.compute_units_consumed,
        estimated_fee_lamports: fee.fee_lamports,
    };
    let canonical = assemble_exact_unsigned_relayer_message_v1(
        plan,
        startup,
        evidence,
        &simulation.lookup_tables,
    )?;
    if canonical.serialized_message() != inputs.fee_request.serialized_message() {
        return Err(RelayerRpcCompositionErrorV1::CanonicalMessageMismatch);
    }
    let transaction: VersionedTransaction = bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .with_limit(RELAYER_RPC_MAX_TRANSACTION_WIRE_BYTES_V1 as u64)
        .reject_trailing_bytes()
        .deserialize(inputs.simulation_request.unsigned_transaction_wire())
        .map_err(|_| RelayerRpcCompositionErrorV1::InvalidUnsignedTransactionWire)?;
    transaction
        .sanitize()
        .map_err(|_| RelayerRpcCompositionErrorV1::InvalidUnsignedTransactionWire)?;
    if &transaction.message != canonical.message() {
        return Err(RelayerRpcCompositionErrorV1::CanonicalMessageMismatch);
    }

    Ok(RelayerSimulationArtifactV1::from_exact_rpc_composition_v1(
        evidence,
        simulation.lookup_tables.clone(),
    ))
}

/// Compose an exact two-provider send response into coordinator submission
/// evidence. `submitted_at_slot` is the request's authenticated
/// `minContextSlot` lower bound. It is not a provider-reported landing or send
/// slot; the sendTransaction result contains no such slot.
pub fn compose_relayer_submission_evidence_v1(
    startup: &OperatorStartupReceiptV1,
    expected_signature: [u8; 64],
    expected_signed_wire: &[u8],
    simulated_at_slot: u64,
    request: &ExactSendTransactionRequestV1,
    agreement: &RelayerRpcAgreementV1<[u8; 64]>,
) -> Result<RelayerSubmissionEvidenceV1, RelayerRpcCompositionErrorV1> {
    validate_agreement_v1(
        startup,
        RelayerRpcEndpointV1::ExactSendTransaction,
        request.request_id(),
        Some(request.min_context_slot()),
        &request.encode_json_v1(),
        agreement,
    )?;
    if expected_signature == [0u8; 64]
        || request.transaction_signature() != &expected_signature
        || agreement.value() != &expected_signature
        || request.signed_wire() != expected_signed_wire
    {
        return Err(RelayerRpcCompositionErrorV1::SignatureMismatch);
    }
    if request.min_context_slot() < simulated_at_slot {
        return Err(RelayerRpcCompositionErrorV1::ContextOrderMismatch);
    }
    Ok(RelayerSubmissionEvidenceV1 {
        submitted_at_slot: request.min_context_slot(),
        provider_set_digest: *agreement.provider_set_digest(),
    })
}

/// Compose an agreed signature status. Pending and sufficiently corroborated
/// not-found states are coordinator-ready. Finalized status remains only a
/// hint until the separate finalized getBlock/root-page quorum joins it to the
/// exact successful transaction and authenticated Pool lifecycle evidence.
pub fn compose_relayer_signature_status_v1(
    startup: &OperatorStartupReceiptV1,
    expected_signature: [u8; 64],
    status_request: &SignatureStatusesRequestV1,
    status_agreement: &RelayerRpcAgreementV1<RelayerSignatureStatusRpcV1>,
    block_height: Option<RelayerBlockHeightQuorumInputsV1<'_>>,
) -> Result<ComposedRelayerSignatureStatusV1, RelayerRpcCompositionErrorV1> {
    validate_agreement_v1(
        startup,
        RelayerRpcEndpointV1::SignatureStatuses,
        status_request.request_id(),
        None,
        &status_request.encode_json_v1(),
        status_agreement,
    )?;
    if expected_signature == [0u8; 64]
        || status_request.transaction_signature() != &expected_signature
    {
        return Err(RelayerRpcCompositionErrorV1::SignatureMismatch);
    }
    let provider_set_digest = *status_agreement.provider_set_digest();
    match *status_agreement.value() {
        RelayerSignatureStatusRpcV1::Pending { landed_slot, .. } => {
            if block_height.is_some() {
                return Err(RelayerRpcCompositionErrorV1::UnexpectedBlockHeightAgreement);
            }
            if landed_slot < status_agreement.startup_checkpoint_slot() {
                return Err(RelayerRpcCompositionErrorV1::InvalidSignatureStatus);
            }
            Ok(ComposedRelayerSignatureStatusV1::CoordinatorReady(
                RelayerSignatureObservationV1::Pending(
                    RelayerPendingObservationV1::from_agreed_status_v1(provider_set_digest),
                ),
            ))
        }
        RelayerSignatureStatusRpcV1::NotFound {
            context_slot,
            evidence_sha256,
        } => {
            let block_height =
                block_height.ok_or(RelayerRpcCompositionErrorV1::MissingBlockHeightAgreement)?;
            validate_agreement_v1(
                startup,
                RelayerRpcEndpointV1::FinalizedBlockHeight,
                block_height.request.request_id(),
                Some(block_height.request.min_context_slot()),
                &block_height.request.encode_json_v1(),
                block_height.agreement,
            )?;
            if block_height.request.min_context_slot() < context_slot {
                return Err(RelayerRpcCompositionErrorV1::ContextOrderMismatch);
            }
            Ok(ComposedRelayerSignatureStatusV1::CoordinatorReady(
                RelayerSignatureObservationV1::NotFound(
                    RelayerNotFoundObservationV1::from_agreed_status_v1(
                        *block_height.agreement.value(),
                        evidence_sha256,
                        provider_set_digest,
                    ),
                ),
            ))
        }
        RelayerSignatureStatusRpcV1::Finalized {
            context_slot,
            landed_slot,
            succeeded,
            execution_result_sha256,
        } => {
            if block_height.is_some() {
                return Err(RelayerRpcCompositionErrorV1::UnexpectedBlockHeightAgreement);
            }
            if landed_slot < status_agreement.startup_checkpoint_slot() {
                return Err(RelayerRpcCompositionErrorV1::InvalidSignatureStatus);
            }
            let hint = RelayerFinalizedStatusHintV1 {
                transaction_signature: expected_signature,
                context_slot,
                landed_slot,
                succeeded,
                execution_result_sha256,
                provider_set_digest,
                startup_receipt_digest: *status_agreement.startup_receipt_digest(),
                status_request_id: status_agreement.request_id(),
                status_request_binding_sha256: *status_agreement.request_binding_sha256(),
            };
            if succeeded {
                Ok(ComposedRelayerSignatureStatusV1::FinalizedBlockJoinRequired(hint))
            } else {
                Ok(ComposedRelayerSignatureStatusV1::FinalizedFailureJoinRequired(hint))
            }
        }
    }
}

fn validate_agreement_v1<T>(
    startup: &OperatorStartupReceiptV1,
    endpoint: RelayerRpcEndpointV1,
    request_id: u64,
    request_min_context_slot: Option<u64>,
    request_json: &[u8],
    agreement: &RelayerRpcAgreementV1<T>,
) -> Result<(), RelayerRpcCompositionErrorV1> {
    if startup.receipt_digest() == &[0u8; 32]
        || startup.receipt_digest() != agreement.startup_receipt_digest()
        || startup.checkpoint().point.slot() != agreement.startup_checkpoint_slot()
    {
        return Err(RelayerRpcCompositionErrorV1::StartupReceiptMismatch);
    }
    let provider_ids = agreement.provider_ids();
    if provider_ids[0] == [0u8; 32]
        || provider_ids[1] == [0u8; 32]
        || provider_ids[0] >= provider_ids[1]
        || provider_set_digest_v1(provider_ids) != *agreement.provider_set_digest()
        || agreement.provider_set_digest() != startup.provider_set_digest()
    {
        return Err(RelayerRpcCompositionErrorV1::ProviderSetMismatch);
    }
    if agreement.endpoint() != endpoint {
        return Err(RelayerRpcCompositionErrorV1::WrongEndpoint);
    }
    if agreement.request_id() != request_id
        || agreement.request_min_context_slot() != request_min_context_slot
        || agreement.request_binding_sha256()
            != &request_binding_digest_v1(
                endpoint,
                request_id,
                request_min_context_slot,
                request_json,
            )
    {
        return Err(RelayerRpcCompositionErrorV1::WrongRequestBinding);
    }
    Ok(())
}

fn validate_lookup_addresses_v1(
    addresses: &[solana_program::pubkey::Pubkey],
    tables: &[AuthenticatedAddressLookupTableV1],
) -> Result<(), RelayerRpcCompositionErrorV1> {
    if addresses.len() != tables.len()
        || addresses
            .iter()
            .zip(tables)
            .any(|(address, table)| *address != table.address())
    {
        return Err(RelayerRpcCompositionErrorV1::LookupAddressMismatch);
    }
    Ok(())
}

fn same_lookup_image_v1(
    before: &AuthenticatedAddressLookupTableV1,
    simulated: &AuthenticatedAddressLookupTableV1,
) -> bool {
    before.address() == simulated.address()
        && before.owner() == simulated.owner()
        && before.lamports() == simulated.lamports()
        && before.executable() == simulated.executable()
        && before.rent_epoch() == simulated.rent_epoch()
        && before.commitment() == simulated.commitment()
        && before.provider_set_digest() == simulated.provider_set_digest()
        && before.account_data() == simulated.account_data()
        && before.observed_slot() <= simulated.observed_slot()
}

#[cfg(test)]
mod tests {
    use std::borrow::Cow;

    use aspis_core::field::M31;
    use aspis_pool::{deposit::DepositRequestV1, pool_v1_state_address};
    use aspis_statement::poseidon2::Digest;
    use serde_json::{json, Value};
    use solana_address_lookup_table_interface::state::{AddressLookupTable, LookupTableMeta};
    use solana_compute_budget_interface::ComputeBudgetInstruction;
    use solana_keypair::Keypair;
    use solana_message::{legacy, v0, AddressLookupTableAccount, VersionedMessage};
    use solana_program::{hash::Hash, pubkey::Pubkey};
    use solana_signature::Signature;
    use solana_signer::Signer;

    use super::*;
    use crate::{
        operator_startup::{FinalizedReleaseCheckpointV1, OperatorStartupReceiptV1},
        relayer::{prepare_permissionless_relayer_plan_v1, RelayerSnapshotV1},
        relayer_rpc_quorum::{ExactProviderRpcExchangeV1, ExactTwoProviderRelayerRpcV1},
        scan_state::FinalizedChainPointV1,
        transaction_builder::build_deposit_instruction_v1,
    };

    const PROVIDERS: [[u8; 32]; 2] = [[1u8; 32], [2u8; 32]];
    const BLOCKHASH_SLOT: u64 = 100;
    const SIMULATION_SLOT: u64 = 101;
    const FEE_SLOT: u64 = 102;
    const COMPUTE_UNIT_LIMIT: u32 = 1_400_000;
    const COMPUTE_UNIT_PRICE: u64 = 7;
    const RECENT_BLOCKHASH: [u8; 32] = [0x39u8; 32];

    fn key(seed: u8) -> Pubkey {
        Pubkey::new_from_array([seed; 32])
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn fixture_v1() -> (
        Keypair,
        Keypair,
        RelayerPlanV1,
        OperatorStartupReceiptV1,
        ExactTwoProviderRelayerRpcV1,
    ) {
        let fee_payer = Keypair::new();
        let source_authority = Keypair::new();
        let program_id = key(1);
        let mint = key(2);
        let pool = pool_v1_state_address(&program_id, &mint).0;
        let request = DepositRequestV1 {
            owner_key: digest(10),
            amount: 77,
            salt: digest(20),
            encrypted_note_payload: &[],
        };
        let instruction = build_deposit_instruction_v1(
            program_id,
            pool,
            mint,
            7,
            key(3),
            source_authority.pubkey(),
            None,
            &request,
        )
        .unwrap();
        let snapshot = RelayerSnapshotV1 {
            pinned_program_id: program_id,
            registry_program: key(5),
            current_root_sequence: 7,
            observed_slot: 90,
            pool_state_sha256: [0x90u8; 32],
        };
        let plan =
            prepare_permissionless_relayer_plan_v1(snapshot, fee_payer.pubkey(), &instruction)
                .unwrap();
        let startup = OperatorStartupReceiptV1::test_only_v1(
            [0x93u8; 32],
            provider_set_digest_v1(&PROVIDERS),
            FinalizedReleaseCheckpointV1 {
                point: FinalizedChainPointV1::new(90, [0x91u8; 32]).unwrap(),
                pool_state_sha256: snapshot.pool_state_sha256,
                root_sequence: snapshot.current_root_sequence,
                root: [0x92u8; 32],
            },
        );
        let quorum = ExactTwoProviderRelayerRpcV1::new(PROVIDERS, &startup).unwrap();
        (fee_payer, source_authority, plan, startup, quorum)
    }

    fn canonical_message_v1(
        plan: &RelayerPlanV1,
        lookup: Option<AddressLookupTableAccount>,
    ) -> VersionedMessage {
        let instructions = vec![
            ComputeBudgetInstruction::set_compute_unit_limit(COMPUTE_UNIT_LIMIT),
            ComputeBudgetInstruction::set_compute_unit_price(COMPUTE_UNIT_PRICE),
            plan.instruction.clone(),
        ];
        let recent_blockhash = Hash::new_from_array(RECENT_BLOCKHASH);
        match lookup {
            None => VersionedMessage::Legacy(legacy::Message::new_with_blockhash(
                &instructions,
                Some(&plan.fee_payer),
                &recent_blockhash,
            )),
            Some(lookup) => VersionedMessage::V0(
                v0::Message::try_compile(
                    &plan.fee_payer,
                    &instructions,
                    &[lookup],
                    recent_blockhash,
                )
                .unwrap(),
            ),
        }
    }

    fn zero_signature_wire_v1(message: VersionedMessage) -> Vec<u8> {
        let signature_count = usize::from(message.header().num_required_signatures);
        bincode::serialize(&VersionedTransaction {
            signatures: vec![Signature::default(); signature_count],
            message,
        })
        .unwrap()
    }

    fn exchanges_v1<'a>(
        request: &'a [u8],
        first: &'a [u8],
        second: &'a [u8],
    ) -> [ExactProviderRpcExchangeV1<'a>; 2] {
        [
            ExactProviderRpcExchangeV1::new(PROVIDERS[0], request, first),
            ExactProviderRpcExchangeV1::new(PROVIDERS[1], request, second),
        ]
    }

    fn response_v1(id: u64, value: Value, context_slot: Option<u64>) -> Vec<u8> {
        let result = match context_slot {
            Some(slot) => json!({"context": {"slot": slot}, "value": value}),
            None => value,
        };
        serde_json::to_vec(&json!({"jsonrpc": "2.0", "id": id, "result": result})).unwrap()
    }

    fn latest_agreement_v1(
        quorum: &ExactTwoProviderRelayerRpcV1,
    ) -> (
        FinalizedLatestBlockhashRequestV1,
        RelayerRpcAgreementV1<FinalizedLatestBlockhashV1>,
    ) {
        let request = FinalizedLatestBlockhashRequestV1::new(1, 90).unwrap();
        let request_json = request.encode_json_v1();
        let response = response_v1(
            1,
            json!({
                "blockhash": Hash::new_from_array(RECENT_BLOCKHASH).to_string(),
                "lastValidBlockHeight": 500u64
            }),
            Some(BLOCKHASH_SLOT),
        );
        let agreement = quorum
            .agree_finalized_latest_blockhash_v1(
                &request,
                exchanges_v1(&request_json, &response, &response),
            )
            .unwrap();
        (request, agreement)
    }

    fn simulation_response_v1(id: u64, slot: u64, accounts: Vec<Value>) -> Vec<u8> {
        response_v1(
            id,
            json!({
                "err": null,
                "logs": ["Program log: exact"],
                "accounts": accounts,
                "unitsConsumed": 1_200_000u64,
                "returnData": null,
                "innerInstructions": null,
                "replacementBlockhash": null,
                "loadedAccountsDataSize": 88u64
            }),
            Some(slot),
        )
    }

    fn base64_standard_v1(bytes: &[u8]) -> String {
        const TABLE: &[u8; 64] =
            b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
        let mut output = String::with_capacity(bytes.len().div_ceil(3) * 4);
        for chunk in bytes.chunks(3) {
            let a = chunk[0];
            let b = chunk.get(1).copied().unwrap_or(0);
            let c = chunk.get(2).copied().unwrap_or(0);
            output.push(TABLE[(a >> 2) as usize] as char);
            output.push(TABLE[(((a & 3) << 4) | (b >> 4)) as usize] as char);
            output.push(if chunk.len() > 1 {
                TABLE[(((b & 15) << 2) | (c >> 6)) as usize] as char
            } else {
                '='
            });
            output.push(if chunk.len() > 2 {
                TABLE[(c & 63) as usize] as char
            } else {
                '='
            });
        }
        output
    }

    fn account_value_v1(data: &[u8]) -> Value {
        json!({
            "data": [base64_standard_v1(data), "base64"],
            "executable": false,
            "lamports": 1_000_000u64,
            "owner": solana_sdk_ids::address_lookup_table::id().to_string(),
            "rentEpoch": 7u64,
            "space": data.len() as u64
        })
    }

    fn lookup_data_v1(plan: &RelayerPlanV1, extra: Option<Pubkey>) -> Vec<u8> {
        let mut addresses = Vec::new();
        for account in &plan.instruction.accounts {
            if !account.is_signer && !addresses.contains(&account.pubkey) {
                addresses.push(account.pubkey);
            }
        }
        if let Some(extra) = extra {
            addresses.push(extra);
        }
        AddressLookupTable {
            meta: LookupTableMeta {
                last_extended_slot: 99,
                ..LookupTableMeta::default()
            },
            addresses: Cow::Owned(addresses),
        }
        .serialize_for_tests()
        .unwrap()
    }

    fn resolved_lookup_v1(table: Pubkey, data: &[u8]) -> AddressLookupTableAccount {
        AddressLookupTableAccount {
            key: table,
            addresses: AddressLookupTable::deserialize(data)
                .unwrap()
                .addresses
                .to_vec(),
        }
    }

    #[test]
    fn legacy_simulation_composition_binds_message_blockhash_fee_and_contexts() {
        let (_, _, plan, startup, quorum) = fixture_v1();
        let (latest_request, latest_agreement) = latest_agreement_v1(&quorum);
        let message = canonical_message_v1(&plan, None);
        let simulation_request = ExactRelayerSimulationRequestV1::new(
            2,
            BLOCKHASH_SLOT,
            COMPUTE_UNIT_LIMIT,
            zero_signature_wire_v1(message.clone()),
            vec![],
        )
        .unwrap();
        let simulation_json = simulation_request.encode_json_v1();
        let simulation_response = simulation_response_v1(2, SIMULATION_SLOT, vec![]);
        let simulation_agreement = quorum
            .agree_successful_simulation_v1(
                &simulation_request,
                exchanges_v1(&simulation_json, &simulation_response, &simulation_response),
            )
            .unwrap();
        let fee_request =
            FinalizedFeeForMessageRequestV1::new(3, SIMULATION_SLOT, 20_000, message.serialize())
                .unwrap();
        let fee_json = fee_request.encode_json_v1();
        let fee_response = response_v1(3, json!(10_000u64), Some(FEE_SLOT));
        let fee_agreement = quorum
            .agree_finalized_fee_v1(
                &fee_request,
                exchanges_v1(&fee_json, &fee_response, &fee_response),
            )
            .unwrap();

        let artifact = compose_relayer_simulation_artifact_v1(
            &plan,
            &startup,
            COMPUTE_UNIT_PRICE,
            RelayerSimulationQuorumInputsV1::new(
                &latest_request,
                &latest_agreement,
                None,
                &simulation_request,
                &simulation_agreement,
                &fee_request,
                &fee_agreement,
            ),
        )
        .unwrap();
        assert_eq!(artifact.evidence().recent_blockhash, RECENT_BLOCKHASH);
        assert_eq!(artifact.evidence().last_valid_block_height, 500);
        assert_eq!(artifact.evidence().simulated_at_slot, SIMULATION_SLOT);
        assert_eq!(artifact.evidence().estimated_fee_lamports, 10_000);
        assert_eq!(artifact.evidence().compute_units_consumed, 1_200_000);
        let message_sha256: [u8; 32] = Sha256::digest(message.serialize()).into();
        assert_eq!(artifact.evidence().unsigned_message_sha256, message_sha256);
        assert!(artifact.lookup_tables().is_empty());

        assert_eq!(
            compose_relayer_simulation_artifact_v1(
                &plan,
                &startup,
                COMPUTE_UNIT_PRICE + 1,
                RelayerSimulationQuorumInputsV1::new(
                    &latest_request,
                    &latest_agreement,
                    None,
                    &simulation_request,
                    &simulation_agreement,
                    &fee_request,
                    &fee_agreement,
                ),
            ),
            Err(RelayerRpcCompositionErrorV1::Transaction(
                RelayerTransactionErrorV1::SignedMessageMismatch
            ))
        );

        let wrong_latest_request = FinalizedLatestBlockhashRequestV1::new(99, 90).unwrap();
        assert_eq!(
            compose_relayer_simulation_artifact_v1(
                &plan,
                &startup,
                COMPUTE_UNIT_PRICE,
                RelayerSimulationQuorumInputsV1::new(
                    &wrong_latest_request,
                    &latest_agreement,
                    None,
                    &simulation_request,
                    &simulation_agreement,
                    &fee_request,
                    &fee_agreement,
                ),
            ),
            Err(RelayerRpcCompositionErrorV1::WrongRequestBinding)
        );

        let stale_fee_request =
            FinalizedFeeForMessageRequestV1::new(4, BLOCKHASH_SLOT, 20_000, message.serialize())
                .unwrap();
        let stale_json = stale_fee_request.encode_json_v1();
        let stale_response = response_v1(4, json!(10_000u64), Some(FEE_SLOT));
        let stale_agreement = quorum
            .agree_finalized_fee_v1(
                &stale_fee_request,
                exchanges_v1(&stale_json, &stale_response, &stale_response),
            )
            .unwrap();
        assert_eq!(
            compose_relayer_simulation_artifact_v1(
                &plan,
                &startup,
                COMPUTE_UNIT_PRICE,
                RelayerSimulationQuorumInputsV1::new(
                    &latest_request,
                    &latest_agreement,
                    None,
                    &simulation_request,
                    &simulation_agreement,
                    &stale_fee_request,
                    &stale_agreement,
                ),
            ),
            Err(RelayerRpcCompositionErrorV1::ContextOrderMismatch)
        );
    }

    #[test]
    fn v0_composition_requires_same_raw_alt_image_at_simulation() {
        let (_, _, plan, startup, quorum) = fixture_v1();
        let (latest_request, latest_agreement) = latest_agreement_v1(&quorum);
        let table = key(240);
        let data = lookup_data_v1(&plan, None);
        let lookup_request =
            FinalizedAddressLookupTablesRequestV1::new(2, BLOCKHASH_SLOT, vec![table]).unwrap();
        let lookup_json = lookup_request.encode_json_v1();
        let lookup_response =
            response_v1(2, json!([account_value_v1(&data)]), Some(BLOCKHASH_SLOT));
        let lookup_agreement = quorum
            .agree_finalized_lookup_tables_v1(
                &lookup_request,
                exchanges_v1(&lookup_json, &lookup_response, &lookup_response),
            )
            .unwrap();
        let message = canonical_message_v1(&plan, Some(resolved_lookup_v1(table, &data)));
        let simulation_request = ExactRelayerSimulationRequestV1::new(
            3,
            BLOCKHASH_SLOT,
            COMPUTE_UNIT_LIMIT,
            zero_signature_wire_v1(message.clone()),
            vec![table],
        )
        .unwrap();
        let simulation_json = simulation_request.encode_json_v1();
        let simulation_response =
            simulation_response_v1(3, SIMULATION_SLOT, vec![account_value_v1(&data)]);
        let simulation_agreement = quorum
            .agree_successful_simulation_v1(
                &simulation_request,
                exchanges_v1(&simulation_json, &simulation_response, &simulation_response),
            )
            .unwrap();
        let fee_request =
            FinalizedFeeForMessageRequestV1::new(4, SIMULATION_SLOT, 20_000, message.serialize())
                .unwrap();
        let fee_json = fee_request.encode_json_v1();
        let fee_response = response_v1(4, json!(10_000u64), Some(FEE_SLOT));
        let fee_agreement = quorum
            .agree_finalized_fee_v1(
                &fee_request,
                exchanges_v1(&fee_json, &fee_response, &fee_response),
            )
            .unwrap();
        let inputs = || {
            RelayerSimulationQuorumInputsV1::new(
                &latest_request,
                &latest_agreement,
                Some(RelayerLookupQuorumInputsV1::new(
                    &lookup_request,
                    &lookup_agreement,
                )),
                &simulation_request,
                &simulation_agreement,
                &fee_request,
                &fee_agreement,
            )
        };
        let artifact =
            compose_relayer_simulation_artifact_v1(&plan, &startup, COMPUTE_UNIT_PRICE, inputs())
                .unwrap();
        assert_eq!(artifact.lookup_tables().len(), 1);
        assert_eq!(artifact.lookup_tables()[0].account_data(), data);
        assert_eq!(artifact.lookup_tables()[0].observed_slot(), SIMULATION_SLOT);

        let changed_data = lookup_data_v1(&plan, Some(key(241)));
        let changed_response =
            simulation_response_v1(3, SIMULATION_SLOT, vec![account_value_v1(&changed_data)]);
        let changed_agreement = quorum
            .agree_successful_simulation_v1(
                &simulation_request,
                exchanges_v1(&simulation_json, &changed_response, &changed_response),
            )
            .unwrap();
        assert_eq!(
            compose_relayer_simulation_artifact_v1(
                &plan,
                &startup,
                COMPUTE_UNIT_PRICE,
                RelayerSimulationQuorumInputsV1::new(
                    &latest_request,
                    &latest_agreement,
                    Some(RelayerLookupQuorumInputsV1::new(
                        &lookup_request,
                        &lookup_agreement,
                    )),
                    &simulation_request,
                    &changed_agreement,
                    &fee_request,
                    &fee_agreement,
                ),
            ),
            Err(RelayerRpcCompositionErrorV1::LookupImageMismatch)
        );
    }

    #[test]
    fn submission_uses_authenticated_min_context_lower_bound_and_exact_wire() {
        let (fee_payer, source_authority, plan, startup, quorum) = fixture_v1();
        let message = canonical_message_v1(&plan, None);
        let signed =
            VersionedTransaction::try_new(message, &[&fee_payer, &source_authority]).unwrap();
        let signature = *signed.signatures[0].as_array();
        let signed_wire = bincode::serialize(&signed).unwrap();
        let request =
            ExactSendTransactionRequestV1::new(8, FEE_SLOT, signature, signed_wire.clone())
                .unwrap();
        let request_json = request.encode_json_v1();
        let response = response_v1(8, json!(Signature::from(signature).to_string()), None);
        let agreement = quorum
            .agree_exact_send_signature_v1(
                &request,
                exchanges_v1(&request_json, &response, &response),
            )
            .unwrap();
        let evidence = compose_relayer_submission_evidence_v1(
            &startup,
            signature,
            &signed_wire,
            SIMULATION_SLOT,
            &request,
            &agreement,
        )
        .unwrap();
        assert_eq!(evidence.submitted_at_slot, FEE_SLOT);
        assert_eq!(evidence.provider_set_digest, *startup.provider_set_digest());
        assert_eq!(
            compose_relayer_submission_evidence_v1(
                &startup,
                signature,
                &[0u8; 1],
                SIMULATION_SLOT,
                &request,
                &agreement,
            ),
            Err(RelayerRpcCompositionErrorV1::SignatureMismatch)
        );
    }

    #[test]
    fn status_composition_stops_finalized_at_block_join_boundary() {
        let (_, _, _, startup, quorum) = fixture_v1();
        let signature = [13u8; 64];

        let pending_request = SignatureStatusesRequestV1::new(9, signature).unwrap();
        let pending_json = pending_request.encode_json_v1();
        let pending_response = response_v1(
            9,
            json!([{
                "slot": 104,
                "confirmations": 2,
                "err": null,
                "confirmationStatus": "confirmed",
                "status": {"Ok": null}
            }]),
            Some(105),
        );
        let pending_agreement = quorum
            .agree_signature_status_v1(
                &pending_request,
                exchanges_v1(&pending_json, &pending_response, &pending_response),
            )
            .unwrap();
        assert!(matches!(
            compose_relayer_signature_status_v1(
                &startup,
                signature,
                &pending_request,
                &pending_agreement,
                None,
            )
            .unwrap(),
            ComposedRelayerSignatureStatusV1::CoordinatorReady(
                RelayerSignatureObservationV1::Pending(_)
            )
        ));

        let missing_request = SignatureStatusesRequestV1::new(10, signature).unwrap();
        let missing_json = missing_request.encode_json_v1();
        let missing_response = response_v1(10, json!([null]), Some(106));
        let missing_agreement = quorum
            .agree_signature_status_v1(
                &missing_request,
                exchanges_v1(&missing_json, &missing_response, &missing_response),
            )
            .unwrap();
        let height_request = FinalizedBlockHeightRequestV1::new(11, 106).unwrap();
        let height_json = height_request.encode_json_v1();
        let height_response = response_v1(11, json!(700u64), None);
        let height_agreement = quorum
            .agree_finalized_block_height_v1(
                &height_request,
                exchanges_v1(&height_json, &height_response, &height_response),
            )
            .unwrap();
        match compose_relayer_signature_status_v1(
            &startup,
            signature,
            &missing_request,
            &missing_agreement,
            Some(RelayerBlockHeightQuorumInputsV1::new(
                &height_request,
                &height_agreement,
            )),
        )
        .unwrap()
        {
            ComposedRelayerSignatureStatusV1::CoordinatorReady(
                RelayerSignatureObservationV1::NotFound(observation),
            ) => {
                assert_eq!(observation.observed_block_height(), 700);
                assert_eq!(
                    observation.provider_set_digest(),
                    startup.provider_set_digest()
                );
            }
            _ => panic!("not-found must be coordinator-ready"),
        }

        let finalized_request = SignatureStatusesRequestV1::new(12, signature).unwrap();
        let finalized_json = finalized_request.encode_json_v1();
        let finalized_response = response_v1(
            12,
            json!([{
                "slot": 104,
                "confirmations": null,
                "err": null,
                "confirmationStatus": "finalized",
                "status": {"Ok": null}
            }]),
            Some(107),
        );
        let finalized_agreement = quorum
            .agree_signature_status_v1(
                &finalized_request,
                exchanges_v1(&finalized_json, &finalized_response, &finalized_response),
            )
            .unwrap();
        match compose_relayer_signature_status_v1(
            &startup,
            signature,
            &finalized_request,
            &finalized_agreement,
            None,
        )
        .unwrap()
        {
            ComposedRelayerSignatureStatusV1::FinalizedBlockJoinRequired(hint) => {
                assert_eq!(hint.transaction_signature(), &signature);
                assert_eq!(hint.context_slot(), 107);
                assert_eq!(hint.landed_slot(), 104);
                assert!(hint.succeeded());
                assert_ne!(hint.execution_result_sha256(), &[0u8; 32]);
                assert_eq!(hint.provider_set_digest(), startup.provider_set_digest());
            }
            _ => panic!("finalized status must require the block/indexer join"),
        }

        let failed_request = SignatureStatusesRequestV1::new(13, signature).unwrap();
        let failed_json = failed_request.encode_json_v1();
        let failure = json!({"InstructionError": [0, "Custom"]});
        let failed_response = response_v1(
            13,
            json!([{
                "slot": 104,
                "confirmations": null,
                "err": failure,
                "confirmationStatus": "finalized",
                "status": {"Err": failure}
            }]),
            Some(107),
        );
        let failed_agreement = quorum
            .agree_signature_status_v1(
                &failed_request,
                exchanges_v1(&failed_json, &failed_response, &failed_response),
            )
            .unwrap();
        match compose_relayer_signature_status_v1(
            &startup,
            signature,
            &failed_request,
            &failed_agreement,
            None,
        )
        .unwrap()
        {
            ComposedRelayerSignatureStatusV1::FinalizedFailureJoinRequired(hint) => {
                assert!(!hint.succeeded());
                assert_eq!(hint.landed_slot(), 104);
                assert_ne!(hint.execution_result_sha256(), &[0u8; 32]);
            }
            _ => panic!("failed finality must require its distinct journal ABI"),
        }
    }
}
