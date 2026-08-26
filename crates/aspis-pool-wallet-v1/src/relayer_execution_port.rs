//! Concrete production relayer execution port.
//!
//! This module wires the restart-safe coordinator to the exact two-provider
//! HTTPS RPC client and an explicit external signer. Every RPC request id is
//! durably burned before transport. The signer receives only the canonical
//! public message and binding metadata; signer custody and secret key bytes do
//! not enter this crate.

use sha2::{Digest as _, Sha256};
use solana_program::pubkey::Pubkey;

use crate::{
    operator_execution::{
        RelayerExecutionPortV1, RelayerSignatureObservationV1, RelayerSimulationArtifactV1,
    },
    operator_startup::OperatorStartupReceiptV1,
    relayer::RelayerPlanV1,
    relayer_execution_journal::{RelayerSimulationEvidenceV1, RelayerSubmissionEvidenceV1},
    relayer_finality_join::{
        join_failed_relayer_finality_v1, join_successful_relayer_finality_v1,
        RelayerFinalityJoinErrorV1,
    },
    relayer_https_rpc::{ExactRelayerHttpsRpcV1, RelayerHttpsRpcErrorV1},
    relayer_rpc_composition::{
        compose_relayer_signature_status_v1, compose_relayer_simulation_artifact_v1,
        compose_relayer_submission_evidence_v1, ComposedRelayerSignatureStatusV1,
        RelayerBlockHeightQuorumInputsV1, RelayerFinalizedStatusHintV1,
        RelayerLookupQuorumInputsV1, RelayerRpcCompositionErrorV1, RelayerSimulationQuorumInputsV1,
    },
    relayer_rpc_json::{
        ExactRelayerSimulationRequestV1, ExactSendTransactionRequestV1,
        FinalizedAddressLookupTableBatchV1, FinalizedAddressLookupTablesRequestV1,
        FinalizedBlockHeightRequestV1, FinalizedFeeForMessageRequestV1, FinalizedFeeForMessageV1,
        FinalizedLatestBlockhashRequestV1, FinalizedLatestBlockhashV1, RelayerRpcJsonErrorV1,
        RelayerSignatureStatusRpcV1, SignatureStatusesRequestV1, SuccessfulRelayerSimulationRpcV1,
        RELAYER_RPC_MAX_LOOKUP_TABLES_V1,
    },
    relayer_rpc_quorum::RelayerRpcAgreementV1,
    relayer_rpc_request_id::RelayerRpcRequestIdSourceV1,
    relayer_transaction::{
        assemble_exact_pre_simulation_relayer_transaction_v1, RelayerTransactionErrorV1,
    },
    rpc_adapter::DepositRpcBindingV1,
    rpc_json::{FinalizedGetBlockRequestV1, RpcJsonErrorV1},
    rpc_json_quorum::{AgreedFinalizedBlockIngestV1, AgreedFinalizedRpcJsonPlanV1},
    scan_state::{LocalOwnerKeyStoreV1, ScanStateV1},
    ViewingSecretKeyV1,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelayerExecutionRpcPolicyV1 {
    compute_unit_limit: u32,
    compute_unit_price_micro_lamports: u64,
    max_fee_lamports: u64,
    lookup_table_addresses: Vec<Pubkey>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelayerExecutionRpcPolicyErrorV1 {
    InvalidComputeOrFeeLimit,
    TooManyLookupTables,
    NonCanonicalLookupTableOrder,
}

impl RelayerExecutionRpcPolicyV1 {
    pub fn new(
        compute_unit_limit: u32,
        compute_unit_price_micro_lamports: u64,
        max_fee_lamports: u64,
        lookup_table_addresses: Vec<Pubkey>,
    ) -> Result<Self, RelayerExecutionRpcPolicyErrorV1> {
        let minimum_priority_fee = u128::from(compute_unit_limit)
            .checked_mul(u128::from(compute_unit_price_micro_lamports))
            .ok_or(RelayerExecutionRpcPolicyErrorV1::InvalidComputeOrFeeLimit)?
            .div_ceil(1_000_000);
        if compute_unit_limit == 0
            || max_fee_lamports == 0
            || minimum_priority_fee > u128::from(max_fee_lamports)
        {
            return Err(RelayerExecutionRpcPolicyErrorV1::InvalidComputeOrFeeLimit);
        }
        if lookup_table_addresses.len() > RELAYER_RPC_MAX_LOOKUP_TABLES_V1 {
            return Err(RelayerExecutionRpcPolicyErrorV1::TooManyLookupTables);
        }
        if lookup_table_addresses
            .windows(2)
            .any(|pair| pair[0].to_bytes() >= pair[1].to_bytes())
        {
            return Err(RelayerExecutionRpcPolicyErrorV1::NonCanonicalLookupTableOrder);
        }
        Ok(Self {
            compute_unit_limit,
            compute_unit_price_micro_lamports,
            max_fee_lamports,
            lookup_table_addresses,
        })
    }

    pub fn compute_unit_limit(&self) -> u32 {
        self.compute_unit_limit
    }

    pub fn compute_unit_price_micro_lamports(&self) -> u64 {
        self.compute_unit_price_micro_lamports
    }

    pub fn max_fee_lamports(&self) -> u64 {
        self.max_fee_lamports
    }

    pub fn lookup_table_addresses(&self) -> &[Pubkey] {
        &self.lookup_table_addresses
    }
}

/// Public, immutable request passed across the HSM/remote-signer boundary.
pub struct ExactRelayerSigningRequestV1<'a> {
    request_id: [u8; 32],
    startup_receipt_digest: [u8; 32],
    fee_payer: [u8; 32],
    simulation: RelayerSimulationEvidenceV1,
    exact_unsigned_message: &'a [u8],
}

impl ExactRelayerSigningRequestV1<'_> {
    pub fn request_id(&self) -> &[u8; 32] {
        &self.request_id
    }

    pub fn startup_receipt_digest(&self) -> &[u8; 32] {
        &self.startup_receipt_digest
    }

    pub fn fee_payer(&self) -> &[u8; 32] {
        &self.fee_payer
    }

    pub fn simulation(&self) -> RelayerSimulationEvidenceV1 {
        self.simulation
    }

    pub fn exact_unsigned_message(&self) -> &[u8] {
        self.exact_unsigned_message
    }
}

pub trait ExternalRelayerSignerV1 {
    type Error;

    fn sign_exact_relayer_message_v1(
        &mut self,
        request: ExactRelayerSigningRequestV1<'_>,
    ) -> Result<Vec<u8>, Self::Error>;
}

#[derive(Debug, PartialEq, Eq)]
pub enum ExactRelayerExecutionPortErrorV1<I, S> {
    RequestId(I),
    Signer(S),
    Rpc(RelayerHttpsRpcErrorV1),
    RelayerCodec(RelayerRpcJsonErrorV1),
    FinalizedCodec(RpcJsonErrorV1),
    Composition(RelayerRpcCompositionErrorV1),
    Transaction(RelayerTransactionErrorV1),
    FinalityJoin(RelayerFinalityJoinErrorV1),
    SigningContextMismatch,
}

/// Exact RPC operations consumed by the production execution state machine.
///
/// The HTTPS implementation is the production implementation. Keeping this
/// boundary transport-free lets tests exercise the complete request and
/// evidence sequence without weakening or reconstructing sealed agreements.
pub trait ExactRelayerExecutionRpcV1 {
    fn startup_receipt_digest_v1(&self) -> &[u8; 32];

    fn finalized_latest_blockhash_v1(
        &self,
        request: &FinalizedLatestBlockhashRequestV1,
    ) -> Result<RelayerRpcAgreementV1<FinalizedLatestBlockhashV1>, RelayerHttpsRpcErrorV1>;

    fn finalized_lookup_tables_v1(
        &self,
        request: &FinalizedAddressLookupTablesRequestV1,
    ) -> Result<RelayerRpcAgreementV1<FinalizedAddressLookupTableBatchV1>, RelayerHttpsRpcErrorV1>;

    fn successful_simulation_v1(
        &self,
        request: &ExactRelayerSimulationRequestV1,
    ) -> Result<RelayerRpcAgreementV1<SuccessfulRelayerSimulationRpcV1>, RelayerHttpsRpcErrorV1>;

    fn finalized_fee_v1(
        &self,
        request: &FinalizedFeeForMessageRequestV1,
    ) -> Result<RelayerRpcAgreementV1<FinalizedFeeForMessageV1>, RelayerHttpsRpcErrorV1>;

    fn send_exact_transaction_v1(
        &self,
        request: &ExactSendTransactionRequestV1,
    ) -> Result<RelayerRpcAgreementV1<[u8; 64]>, RelayerHttpsRpcErrorV1>;

    fn signature_status_v1(
        &self,
        request: &SignatureStatusesRequestV1,
    ) -> Result<RelayerRpcAgreementV1<RelayerSignatureStatusRpcV1>, RelayerHttpsRpcErrorV1>;

    fn finalized_block_height_v1(
        &self,
        request: &FinalizedBlockHeightRequestV1,
    ) -> Result<RelayerRpcAgreementV1<u64>, RelayerHttpsRpcErrorV1>;

    fn agreed_finalized_block_plan_v1(
        &self,
        state: &ScanStateV1,
        binding: &DepositRpcBindingV1,
        request: FinalizedGetBlockRequestV1,
    ) -> Result<AgreedFinalizedRpcJsonPlanV1, RelayerHttpsRpcErrorV1>;

    #[allow(clippy::too_many_arguments)]
    fn ingest_agreed_finalized_block_v1<L: LocalOwnerKeyStoreV1>(
        &self,
        state: &mut ScanStateV1,
        binding: &DepositRpcBindingV1,
        agreed: &AgreedFinalizedRpcJsonPlanV1,
        root_request_id: u64,
        viewing_secret: &ViewingSecretKeyV1,
        local_keys: &L,
    ) -> Result<AgreedFinalizedBlockIngestV1, RelayerHttpsRpcErrorV1>;
}

impl ExactRelayerExecutionRpcV1 for ExactRelayerHttpsRpcV1 {
    fn startup_receipt_digest_v1(&self) -> &[u8; 32] {
        self.quorum().startup_receipt_digest()
    }

    fn finalized_latest_blockhash_v1(
        &self,
        request: &FinalizedLatestBlockhashRequestV1,
    ) -> Result<RelayerRpcAgreementV1<FinalizedLatestBlockhashV1>, RelayerHttpsRpcErrorV1> {
        ExactRelayerHttpsRpcV1::finalized_latest_blockhash_v1(self, request)
    }

    fn finalized_lookup_tables_v1(
        &self,
        request: &FinalizedAddressLookupTablesRequestV1,
    ) -> Result<RelayerRpcAgreementV1<FinalizedAddressLookupTableBatchV1>, RelayerHttpsRpcErrorV1>
    {
        ExactRelayerHttpsRpcV1::finalized_lookup_tables_v1(self, request)
    }

    fn successful_simulation_v1(
        &self,
        request: &ExactRelayerSimulationRequestV1,
    ) -> Result<RelayerRpcAgreementV1<SuccessfulRelayerSimulationRpcV1>, RelayerHttpsRpcErrorV1>
    {
        ExactRelayerHttpsRpcV1::successful_simulation_v1(self, request)
    }

    fn finalized_fee_v1(
        &self,
        request: &FinalizedFeeForMessageRequestV1,
    ) -> Result<RelayerRpcAgreementV1<FinalizedFeeForMessageV1>, RelayerHttpsRpcErrorV1> {
        ExactRelayerHttpsRpcV1::finalized_fee_v1(self, request)
    }

    fn send_exact_transaction_v1(
        &self,
        request: &ExactSendTransactionRequestV1,
    ) -> Result<RelayerRpcAgreementV1<[u8; 64]>, RelayerHttpsRpcErrorV1> {
        ExactRelayerHttpsRpcV1::send_exact_transaction_v1(self, request)
    }

    fn signature_status_v1(
        &self,
        request: &SignatureStatusesRequestV1,
    ) -> Result<RelayerRpcAgreementV1<RelayerSignatureStatusRpcV1>, RelayerHttpsRpcErrorV1> {
        ExactRelayerHttpsRpcV1::signature_status_v1(self, request)
    }

    fn finalized_block_height_v1(
        &self,
        request: &FinalizedBlockHeightRequestV1,
    ) -> Result<RelayerRpcAgreementV1<u64>, RelayerHttpsRpcErrorV1> {
        ExactRelayerHttpsRpcV1::finalized_block_height_v1(self, request)
    }

    fn agreed_finalized_block_plan_v1(
        &self,
        state: &ScanStateV1,
        binding: &DepositRpcBindingV1,
        request: FinalizedGetBlockRequestV1,
    ) -> Result<AgreedFinalizedRpcJsonPlanV1, RelayerHttpsRpcErrorV1> {
        ExactRelayerHttpsRpcV1::agreed_finalized_block_plan_v1(self, state, binding, request)
    }

    fn ingest_agreed_finalized_block_v1<L: LocalOwnerKeyStoreV1>(
        &self,
        state: &mut ScanStateV1,
        binding: &DepositRpcBindingV1,
        agreed: &AgreedFinalizedRpcJsonPlanV1,
        root_request_id: u64,
        viewing_secret: &ViewingSecretKeyV1,
        local_keys: &L,
    ) -> Result<AgreedFinalizedBlockIngestV1, RelayerHttpsRpcErrorV1> {
        ExactRelayerHttpsRpcV1::ingest_agreed_finalized_block_v1(
            self,
            state,
            binding,
            agreed,
            root_request_id,
            viewing_secret,
            local_keys,
        )
    }
}

pub struct ExactHttpsRelayerExecutionPortV1<'a, I, S, K, R = ExactRelayerHttpsRpcV1> {
    rpc: R,
    request_ids: I,
    signer: S,
    policy: RelayerExecutionRpcPolicyV1,
    scan_state: &'a mut ScanStateV1,
    pool_binding: &'a DepositRpcBindingV1,
    viewing_secret: &'a ViewingSecretKeyV1,
    local_keys: &'a K,
}

impl<'a, I, S, K> ExactHttpsRelayerExecutionPortV1<'a, I, S, K> {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        rpc: ExactRelayerHttpsRpcV1,
        request_ids: I,
        signer: S,
        policy: RelayerExecutionRpcPolicyV1,
        scan_state: &'a mut ScanStateV1,
        pool_binding: &'a DepositRpcBindingV1,
        viewing_secret: &'a ViewingSecretKeyV1,
        local_keys: &'a K,
    ) -> Self {
        Self {
            rpc,
            request_ids,
            signer,
            policy,
            scan_state,
            pool_binding,
            viewing_secret,
            local_keys,
        }
    }
}

#[cfg(test)]
impl<'a, I, S, K, R> ExactHttpsRelayerExecutionPortV1<'a, I, S, K, R> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn test_only_with_rpc_v1(
        rpc: R,
        request_ids: I,
        signer: S,
        policy: RelayerExecutionRpcPolicyV1,
        scan_state: &'a mut ScanStateV1,
        pool_binding: &'a DepositRpcBindingV1,
        viewing_secret: &'a ViewingSecretKeyV1,
        local_keys: &'a K,
    ) -> Self {
        Self {
            rpc,
            request_ids,
            signer,
            policy,
            scan_state,
            pool_binding,
            viewing_secret,
            local_keys,
        }
    }
}

impl<I, S, K, R> ExactHttpsRelayerExecutionPortV1<'_, I, S, K, R> {
    pub fn scan_state(&self) -> &ScanStateV1 {
        self.scan_state
    }
}

impl<I, S, K, R> RelayerExecutionPortV1 for ExactHttpsRelayerExecutionPortV1<'_, I, S, K, R>
where
    I: RelayerRpcRequestIdSourceV1,
    S: ExternalRelayerSignerV1,
    K: LocalOwnerKeyStoreV1,
    R: ExactRelayerExecutionRpcV1,
{
    type Error = ExactRelayerExecutionPortErrorV1<I::Error, S::Error>;

    fn simulate_exact_plan_v1(
        &mut self,
        plan: &RelayerPlanV1,
        startup: &OperatorStartupReceiptV1,
    ) -> Result<RelayerSimulationArtifactV1, Self::Error> {
        let latest_request =
            FinalizedLatestBlockhashRequestV1::new(self.next_id_v1()?, plan.snapshot.observed_slot)
                .map_err(ExactRelayerExecutionPortErrorV1::RelayerCodec)?;
        let latest_agreement = self
            .rpc
            .finalized_latest_blockhash_v1(&latest_request)
            .map_err(ExactRelayerExecutionPortErrorV1::Rpc)?;
        let latest = *latest_agreement.value();

        let lookup = if self.policy.lookup_table_addresses.is_empty() {
            None
        } else {
            let request = FinalizedAddressLookupTablesRequestV1::new(
                self.next_id_v1()?,
                latest.context_slot,
                self.policy.lookup_table_addresses.clone(),
            )
            .map_err(ExactRelayerExecutionPortErrorV1::RelayerCodec)?;
            let agreement = self
                .rpc
                .finalized_lookup_tables_v1(&request)
                .map_err(ExactRelayerExecutionPortErrorV1::Rpc)?;
            Some((request, agreement))
        };
        let (pre_simulation_slot, lookup_tables) = lookup.as_ref().map_or_else(
            || (latest.context_slot, Vec::new()),
            |(_, agreement)| {
                (
                    agreement.value().context_slot,
                    agreement.value().lookup_tables.clone(),
                )
            },
        );

        let exact = assemble_exact_pre_simulation_relayer_transaction_v1(
            plan,
            startup,
            pre_simulation_slot,
            latest.blockhash,
            latest.last_valid_block_height,
            self.policy.compute_unit_limit,
            self.policy.compute_unit_price_micro_lamports,
            &lookup_tables,
        )
        .map_err(ExactRelayerExecutionPortErrorV1::Transaction)?;
        let simulation_request = ExactRelayerSimulationRequestV1::new(
            self.next_id_v1()?,
            pre_simulation_slot,
            self.policy.compute_unit_limit,
            exact.unsigned_transaction_wire().to_vec(),
            self.policy.lookup_table_addresses.clone(),
        )
        .map_err(ExactRelayerExecutionPortErrorV1::RelayerCodec)?;
        let simulation_agreement = self
            .rpc
            .successful_simulation_v1(&simulation_request)
            .map_err(ExactRelayerExecutionPortErrorV1::Rpc)?;
        let fee_request = FinalizedFeeForMessageRequestV1::new(
            self.next_id_v1()?,
            simulation_agreement.value().simulated_at_slot,
            self.policy.max_fee_lamports,
            exact.exact_message().serialized_message().to_vec(),
        )
        .map_err(ExactRelayerExecutionPortErrorV1::RelayerCodec)?;
        let fee_agreement = self
            .rpc
            .finalized_fee_v1(&fee_request)
            .map_err(ExactRelayerExecutionPortErrorV1::Rpc)?;
        let lookup_inputs = lookup
            .as_ref()
            .map(|(request, agreement)| RelayerLookupQuorumInputsV1::new(request, agreement));
        compose_relayer_simulation_artifact_v1(
            plan,
            startup,
            self.policy.compute_unit_price_micro_lamports,
            RelayerSimulationQuorumInputsV1::new(
                &latest_request,
                &latest_agreement,
                lookup_inputs,
                &simulation_request,
                &simulation_agreement,
                &fee_request,
                &fee_agreement,
            ),
        )
        .map_err(ExactRelayerExecutionPortErrorV1::Composition)
    }

    fn sign_exact_unsigned_message_v1(
        &mut self,
        plan: &RelayerPlanV1,
        simulation: RelayerSimulationEvidenceV1,
        exact_unsigned_message: &[u8],
    ) -> Result<Vec<u8>, Self::Error> {
        let exact_message_sha256: [u8; 32] = Sha256::digest(exact_unsigned_message).into();
        if simulation.unsigned_message_sha256 != exact_message_sha256
            || simulation.fee_payer != plan.fee_payer.to_bytes()
            || simulation.startup_receipt_digest != *self.rpc.startup_receipt_digest_v1()
        {
            return Err(ExactRelayerExecutionPortErrorV1::SigningContextMismatch);
        }
        self.signer
            .sign_exact_relayer_message_v1(ExactRelayerSigningRequestV1 {
                request_id: plan.request_id,
                startup_receipt_digest: simulation.startup_receipt_digest,
                fee_payer: simulation.fee_payer,
                simulation,
                exact_unsigned_message,
            })
            .map_err(ExactRelayerExecutionPortErrorV1::Signer)
    }

    fn observe_signature_v1(
        &mut self,
        transaction_signature: [u8; 64],
        startup: &OperatorStartupReceiptV1,
    ) -> Result<RelayerSignatureObservationV1, Self::Error> {
        let status_request =
            SignatureStatusesRequestV1::new(self.next_id_v1()?, transaction_signature)
                .map_err(ExactRelayerExecutionPortErrorV1::RelayerCodec)?;
        let status_agreement = self
            .rpc
            .signature_status_v1(&status_request)
            .map_err(ExactRelayerExecutionPortErrorV1::Rpc)?;
        let block_height = match *status_agreement.value() {
            RelayerSignatureStatusRpcV1::NotFound { context_slot, .. } => {
                let request = FinalizedBlockHeightRequestV1::new(self.next_id_v1()?, context_slot)
                    .map_err(ExactRelayerExecutionPortErrorV1::RelayerCodec)?;
                let agreement = self
                    .rpc
                    .finalized_block_height_v1(&request)
                    .map_err(ExactRelayerExecutionPortErrorV1::Rpc)?;
                Some((request, agreement))
            }
            _ => None,
        };
        let block_height_inputs = block_height
            .as_ref()
            .map(|(request, agreement)| RelayerBlockHeightQuorumInputsV1::new(request, agreement));
        match compose_relayer_signature_status_v1(
            startup,
            transaction_signature,
            &status_request,
            &status_agreement,
            block_height_inputs,
        )
        .map_err(ExactRelayerExecutionPortErrorV1::Composition)?
        {
            ComposedRelayerSignatureStatusV1::CoordinatorReady(observation) => Ok(observation),
            ComposedRelayerSignatureStatusV1::FinalizedBlockJoinRequired(hint) => {
                self.join_finalized_hint_v1(startup, hint, true)
            }
            ComposedRelayerSignatureStatusV1::FinalizedFailureJoinRequired(hint) => {
                self.join_finalized_hint_v1(startup, hint, false)
            }
        }
    }

    fn submit_exact_signed_wire_v1(
        &mut self,
        transaction_signature: [u8; 64],
        signed_wire: &[u8],
        simulation: RelayerSimulationEvidenceV1,
        startup: &OperatorStartupReceiptV1,
    ) -> Result<RelayerSubmissionEvidenceV1, Self::Error> {
        let request = ExactSendTransactionRequestV1::new(
            self.next_id_v1()?,
            simulation.simulated_at_slot,
            transaction_signature,
            signed_wire.to_vec(),
        )
        .map_err(ExactRelayerExecutionPortErrorV1::RelayerCodec)?;
        let agreement = self
            .rpc
            .send_exact_transaction_v1(&request)
            .map_err(ExactRelayerExecutionPortErrorV1::Rpc)?;
        compose_relayer_submission_evidence_v1(
            startup,
            transaction_signature,
            signed_wire,
            simulation.simulated_at_slot,
            &request,
            &agreement,
        )
        .map_err(ExactRelayerExecutionPortErrorV1::Composition)
    }
}

impl<I, S, K, R> ExactHttpsRelayerExecutionPortV1<'_, I, S, K, R>
where
    I: RelayerRpcRequestIdSourceV1,
    S: ExternalRelayerSignerV1,
    K: LocalOwnerKeyStoreV1,
    R: ExactRelayerExecutionRpcV1,
{
    fn next_id_v1(&mut self) -> Result<u64, ExactRelayerExecutionPortErrorV1<I::Error, S::Error>> {
        self.request_ids
            .take_next_request_id_v1()
            .map_err(ExactRelayerExecutionPortErrorV1::RequestId)
    }

    fn join_finalized_hint_v1(
        &mut self,
        startup: &OperatorStartupReceiptV1,
        hint: RelayerFinalizedStatusHintV1,
        succeeded: bool,
    ) -> Result<RelayerSignatureObservationV1, ExactRelayerExecutionPortErrorV1<I::Error, S::Error>>
    {
        let block_request = FinalizedGetBlockRequestV1::new(self.next_id_v1()?, hint.landed_slot())
            .map_err(ExactRelayerExecutionPortErrorV1::FinalizedCodec)?;
        let agreed = self
            .rpc
            .agreed_finalized_block_plan_v1(self.scan_state, self.pool_binding, block_request)
            .map_err(ExactRelayerExecutionPortErrorV1::Rpc)?;
        let root_request_id = self.next_id_v1()?;
        let mut candidate = self.scan_state.clone();
        let ingest = self
            .rpc
            .ingest_agreed_finalized_block_v1(
                &mut candidate,
                self.pool_binding,
                &agreed,
                root_request_id,
                self.viewing_secret,
                self.local_keys,
            )
            .map_err(ExactRelayerExecutionPortErrorV1::Rpc)?;
        let observation = if succeeded {
            join_successful_relayer_finality_v1(startup, hint, &agreed, ingest)
        } else {
            join_failed_relayer_finality_v1(startup, hint, &agreed, ingest)
        }
        .map_err(ExactRelayerExecutionPortErrorV1::FinalityJoin)?;
        *self.scan_state = candidate;
        Ok(observation)
    }
}

#[cfg(test)]
mod tests {
    use std::{cell::RefCell, convert::Infallible};

    use aspis_core::field::M31;
    use aspis_pool::{deposit::DepositRequestV1, pool_v1_state_address};
    use aspis_statement::{encode_digest_canonical, poseidon2::Digest};
    use serde_json::json;
    use solana_keypair::Keypair;
    use solana_message::VersionedMessage;
    use solana_program::hash::Hash;
    use solana_signature::Signature;
    use solana_signer::Signer;
    use solana_transaction::versioned::VersionedTransaction;

    use super::*;
    use crate::{
        derive_viewing_keypair_v1,
        operator_startup::{
            provider_set_digest_v1, FinalizedReleaseCheckpointV1, OperatorStartupReceiptV1,
        },
        relayer::{prepare_permissionless_relayer_plan_v1, RelayerSnapshotV1},
        relayer_rpc_quorum::{ExactProviderRpcExchangeV1, ExactTwoProviderRelayerRpcV1},
        relayer_transaction::assemble_exact_unsigned_relayer_message_v1,
        scan_state::{DepositScanIdentityV1, FinalizedChainPointV1},
        transaction_builder::build_deposit_instruction_v1,
    };

    const PROVIDERS: [[u8; 32]; 2] = [[1u8; 32], [2u8; 32]];
    const STARTUP_SLOT: u64 = 90;
    const BLOCKHASH_SLOT: u64 = 100;
    const SIMULATION_SLOT: u64 = 101;
    const COMPUTE_UNIT_LIMIT: u32 = 1_400_000;
    const COMPUTE_UNIT_PRICE: u64 = 7;
    const MAX_FEE_LAMPORTS: u64 = 20_000;
    const RECENT_BLOCKHASH: [u8; 32] = [0x39u8; 32];

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum RpcCallV1 {
        Latest {
            request_id: u64,
            min_context_slot: u64,
        },
        Simulation {
            request_id: u64,
            min_context_slot: u64,
        },
        Fee {
            request_id: u64,
            min_context_slot: u64,
        },
        Send {
            request_id: u64,
            min_context_slot: u64,
        },
        Status {
            request_id: u64,
        },
        BlockHeight {
            request_id: u64,
            min_context_slot: u64,
        },
    }

    struct MockExactRpcV1 {
        quorum: ExactTwoProviderRelayerRpcV1,
        calls: RefCell<Vec<RpcCallV1>>,
    }

    impl MockExactRpcV1 {
        fn new(startup: &OperatorStartupReceiptV1) -> Self {
            Self {
                quorum: ExactTwoProviderRelayerRpcV1::new(PROVIDERS, startup).unwrap(),
                calls: RefCell::new(Vec::new()),
            }
        }
    }

    impl ExactRelayerExecutionRpcV1 for MockExactRpcV1 {
        fn startup_receipt_digest_v1(&self) -> &[u8; 32] {
            self.quorum.startup_receipt_digest()
        }

        fn finalized_latest_blockhash_v1(
            &self,
            request: &FinalizedLatestBlockhashRequestV1,
        ) -> Result<RelayerRpcAgreementV1<FinalizedLatestBlockhashV1>, RelayerHttpsRpcErrorV1>
        {
            self.calls.borrow_mut().push(RpcCallV1::Latest {
                request_id: request.request_id(),
                min_context_slot: request.min_context_slot(),
            });
            let request_json = request.encode_json_v1();
            let response = response_v1(
                request.request_id(),
                json!({
                    "blockhash": Hash::new_from_array(RECENT_BLOCKHASH).to_string(),
                    "lastValidBlockHeight": 500u64,
                }),
                Some(BLOCKHASH_SLOT),
            );
            Ok(self.quorum.agree_finalized_latest_blockhash_v1(
                request,
                exchanges_v1(&request_json, &response),
            )?)
        }

        fn finalized_lookup_tables_v1(
            &self,
            _request: &FinalizedAddressLookupTablesRequestV1,
        ) -> Result<RelayerRpcAgreementV1<FinalizedAddressLookupTableBatchV1>, RelayerHttpsRpcErrorV1>
        {
            panic!("the legacy test plan must not request lookup tables")
        }

        fn successful_simulation_v1(
            &self,
            request: &ExactRelayerSimulationRequestV1,
        ) -> Result<RelayerRpcAgreementV1<SuccessfulRelayerSimulationRpcV1>, RelayerHttpsRpcErrorV1>
        {
            self.calls.borrow_mut().push(RpcCallV1::Simulation {
                request_id: request.request_id(),
                min_context_slot: request.min_context_slot(),
            });
            let request_json = request.encode_json_v1();
            let response = response_v1(
                request.request_id(),
                json!({
                    "err": null,
                    "logs": ["Program log: exact"],
                    "accounts": [],
                    "unitsConsumed": 1_200_000u64,
                    "returnData": null,
                    "innerInstructions": null,
                    "replacementBlockhash": null,
                    "loadedAccountsDataSize": 88u64,
                }),
                Some(SIMULATION_SLOT),
            );
            Ok(self
                .quorum
                .agree_successful_simulation_v1(request, exchanges_v1(&request_json, &response))?)
        }

        fn finalized_fee_v1(
            &self,
            request: &FinalizedFeeForMessageRequestV1,
        ) -> Result<RelayerRpcAgreementV1<FinalizedFeeForMessageV1>, RelayerHttpsRpcErrorV1>
        {
            self.calls.borrow_mut().push(RpcCallV1::Fee {
                request_id: request.request_id(),
                min_context_slot: request.min_context_slot(),
            });
            let request_json = request.encode_json_v1();
            let response = response_v1(
                request.request_id(),
                json!(10_000u64),
                Some(request.min_context_slot()),
            );
            Ok(self
                .quorum
                .agree_finalized_fee_v1(request, exchanges_v1(&request_json, &response))?)
        }

        fn send_exact_transaction_v1(
            &self,
            request: &ExactSendTransactionRequestV1,
        ) -> Result<RelayerRpcAgreementV1<[u8; 64]>, RelayerHttpsRpcErrorV1> {
            self.calls.borrow_mut().push(RpcCallV1::Send {
                request_id: request.request_id(),
                min_context_slot: request.min_context_slot(),
            });
            let request_json = request.encode_json_v1();
            let response = response_v1(
                request.request_id(),
                json!(Signature::from(*request.transaction_signature()).to_string()),
                None,
            );
            Ok(self
                .quorum
                .agree_exact_send_signature_v1(request, exchanges_v1(&request_json, &response))?)
        }

        fn signature_status_v1(
            &self,
            request: &SignatureStatusesRequestV1,
        ) -> Result<RelayerRpcAgreementV1<RelayerSignatureStatusRpcV1>, RelayerHttpsRpcErrorV1>
        {
            self.calls.borrow_mut().push(RpcCallV1::Status {
                request_id: request.request_id(),
            });
            let request_json = request.encode_json_v1();
            let response = response_v1(request.request_id(), json!([null]), Some(110));
            Ok(self
                .quorum
                .agree_signature_status_v1(request, exchanges_v1(&request_json, &response))?)
        }

        fn finalized_block_height_v1(
            &self,
            request: &FinalizedBlockHeightRequestV1,
        ) -> Result<RelayerRpcAgreementV1<u64>, RelayerHttpsRpcErrorV1> {
            self.calls.borrow_mut().push(RpcCallV1::BlockHeight {
                request_id: request.request_id(),
                min_context_slot: request.min_context_slot(),
            });
            let request_json = request.encode_json_v1();
            let response = response_v1(request.request_id(), json!(499u64), None);
            Ok(self
                .quorum
                .agree_finalized_block_height_v1(request, exchanges_v1(&request_json, &response))?)
        }

        fn agreed_finalized_block_plan_v1(
            &self,
            _state: &ScanStateV1,
            _binding: &DepositRpcBindingV1,
            _request: FinalizedGetBlockRequestV1,
        ) -> Result<AgreedFinalizedRpcJsonPlanV1, RelayerHttpsRpcErrorV1> {
            panic!("not-found status must not request a finalized block")
        }

        fn ingest_agreed_finalized_block_v1<L: LocalOwnerKeyStoreV1>(
            &self,
            _state: &mut ScanStateV1,
            _binding: &DepositRpcBindingV1,
            _agreed: &AgreedFinalizedRpcJsonPlanV1,
            _root_request_id: u64,
            _viewing_secret: &ViewingSecretKeyV1,
            _local_keys: &L,
        ) -> Result<AgreedFinalizedBlockIngestV1, RelayerHttpsRpcErrorV1> {
            panic!("not-found status must not ingest a finalized block")
        }
    }

    struct SequentialRequestIdsV1(u64);

    impl RelayerRpcRequestIdSourceV1 for SequentialRequestIdsV1 {
        type Error = Infallible;

        fn take_next_request_id_v1(&mut self) -> Result<u64, Self::Error> {
            let current = self.0;
            self.0 += 1;
            Ok(current)
        }
    }

    struct RecordingSignerV1 {
        fee_payer: Keypair,
        source_authority: Keypair,
        calls: usize,
        last_request_id: Option<[u8; 32]>,
        last_startup_receipt_digest: Option<[u8; 32]>,
    }

    impl ExternalRelayerSignerV1 for RecordingSignerV1 {
        type Error = &'static str;

        fn sign_exact_relayer_message_v1(
            &mut self,
            request: ExactRelayerSigningRequestV1<'_>,
        ) -> Result<Vec<u8>, Self::Error> {
            self.calls += 1;
            self.last_request_id = Some(*request.request_id());
            self.last_startup_receipt_digest = Some(*request.startup_receipt_digest());
            let message: VersionedMessage = bincode::deserialize(request.exact_unsigned_message())
                .map_err(|_| "invalid exact unsigned message")?;
            let transaction =
                VersionedTransaction::try_new(message, &[&self.fee_payer, &self.source_authority])
                    .map_err(|_| "unable to sign exact message")?;
            bincode::serialize(&transaction).map_err(|_| "unable to serialize signed wire")
        }
    }

    struct NoLocalKeysV1;

    impl LocalOwnerKeyStoreV1 for NoLocalKeysV1 {
        fn contains_owner_key_v1(&self, _owner_key: &[u8; 32]) -> bool {
            false
        }
    }

    struct FixtureV1 {
        plan: RelayerPlanV1,
        startup: OperatorStartupReceiptV1,
        scan_state: ScanStateV1,
        binding: DepositRpcBindingV1,
        viewing_secret: ViewingSecretKeyV1,
        fee_payer: Keypair,
        source_authority: Keypair,
    }

    fn key(seed: u8) -> Pubkey {
        Pubkey::new_from_array([seed; 32])
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn fixture_v1(manifest_digest: [u8; 32]) -> FixtureV1 {
        let fee_payer = Keypair::new();
        let source_authority = Keypair::new();
        let program_id = key(11);
        let mint = key(12);
        let pool = pool_v1_state_address(&program_id, &mint).0;
        let vault = aspis_pool::pool_v1_vault_token_account_address(&program_id, &pool).0;
        let instruction = build_deposit_instruction_v1(
            program_id,
            pool,
            mint,
            7,
            key(13),
            source_authority.pubkey(),
            None,
            &DepositRequestV1 {
                owner_key: digest(10),
                amount: 77,
                salt: digest(20),
                encrypted_note_payload: &[],
            },
        )
        .unwrap();
        let snapshot = RelayerSnapshotV1 {
            pinned_program_id: program_id,
            registry_program: key(14),
            current_root_sequence: 7,
            observed_slot: STARTUP_SLOT,
            pool_state_sha256: [0x90u8; 32],
        };
        let plan =
            prepare_permissionless_relayer_plan_v1(snapshot, fee_payer.pubkey(), &instruction)
                .unwrap();
        let point = FinalizedChainPointV1::new(STARTUP_SLOT, [0x91u8; 32]).unwrap();
        let root = encode_digest_canonical(&digest(30));
        let startup = OperatorStartupReceiptV1::test_only_v1(
            manifest_digest,
            provider_set_digest_v1(&PROVIDERS),
            FinalizedReleaseCheckpointV1 {
                point,
                pool_state_sha256: snapshot.pool_state_sha256,
                root_sequence: snapshot.current_root_sequence,
                root,
            },
        );
        let identity = DepositScanIdentityV1::new(
            pool.to_bytes(),
            [0x92u8; 32],
            mint.to_bytes(),
            vault.to_bytes(),
            9,
        )
        .unwrap();
        FixtureV1 {
            plan,
            startup,
            scan_state: ScanStateV1::new(identity, point, 7, root).unwrap(),
            binding: DepositRpcBindingV1::new(program_id.to_bytes()).unwrap(),
            viewing_secret: derive_viewing_keypair_v1(&[0x51u8; 32]).unwrap().0,
            fee_payer,
            source_authority,
        }
    }

    fn policy_v1() -> RelayerExecutionRpcPolicyV1 {
        RelayerExecutionRpcPolicyV1::new(
            COMPUTE_UNIT_LIMIT,
            COMPUTE_UNIT_PRICE,
            MAX_FEE_LAMPORTS,
            Vec::new(),
        )
        .unwrap()
    }

    fn response_v1(
        request_id: u64,
        value: serde_json::Value,
        context_slot: Option<u64>,
    ) -> Vec<u8> {
        let result = match context_slot {
            Some(slot) => json!({"context": {"slot": slot}, "value": value}),
            None => value,
        };
        serde_json::to_vec(&json!({
            "jsonrpc": "2.0",
            "id": request_id,
            "result": result,
        }))
        .unwrap()
    }

    fn exchanges_v1<'a>(
        request_json: &'a [u8],
        response_json: &'a [u8],
    ) -> [ExactProviderRpcExchangeV1<'a>; 2] {
        [
            ExactProviderRpcExchangeV1::new(PROVIDERS[0], request_json, response_json),
            ExactProviderRpcExchangeV1::new(PROVIDERS[1], request_json, response_json),
        ]
    }

    #[test]
    fn rpc_policy_rejects_unsafe_limits_and_noncanonical_tables() {
        let a = Pubkey::new_from_array([1u8; 32]);
        let b = Pubkey::new_from_array([2u8; 32]);
        assert!(RelayerExecutionRpcPolicyV1::new(1_300_000, 10_000, 20_000, vec![a, b]).is_ok());
        assert_eq!(
            RelayerExecutionRpcPolicyV1::new(0, 0, 1, Vec::new()),
            Err(RelayerExecutionRpcPolicyErrorV1::InvalidComputeOrFeeLimit)
        );
        assert_eq!(
            RelayerExecutionRpcPolicyV1::new(1_300_000, 10_000, 1, Vec::new()),
            Err(RelayerExecutionRpcPolicyErrorV1::InvalidComputeOrFeeLimit)
        );
        assert_eq!(
            RelayerExecutionRpcPolicyV1::new(1, 0, 1, vec![b, a]),
            Err(RelayerExecutionRpcPolicyErrorV1::NonCanonicalLookupTableOrder)
        );
    }

    #[test]
    fn exact_port_sequences_bound_requests_signing_submission_and_not_found_observation() {
        let FixtureV1 {
            plan,
            startup,
            mut scan_state,
            binding,
            viewing_secret,
            fee_payer,
            source_authority,
        } = fixture_v1([0x93u8; 32]);
        let rpc = MockExactRpcV1::new(&startup);
        let signer = RecordingSignerV1 {
            fee_payer,
            source_authority,
            calls: 0,
            last_request_id: None,
            last_startup_receipt_digest: None,
        };
        let local_keys = NoLocalKeysV1;
        let mut port = ExactHttpsRelayerExecutionPortV1 {
            rpc,
            request_ids: SequentialRequestIdsV1(41),
            signer,
            policy: policy_v1(),
            scan_state: &mut scan_state,
            pool_binding: &binding,
            viewing_secret: &viewing_secret,
            local_keys: &local_keys,
        };

        let artifact = port.simulate_exact_plan_v1(&plan, &startup).unwrap();
        let simulation = artifact.evidence();
        assert_eq!(simulation.simulated_at_slot(), SIMULATION_SLOT);
        assert_eq!(simulation.estimated_fee_lamports(), 10_000);
        assert_eq!(artifact.lookup_tables(), []);
        let exact = assemble_exact_unsigned_relayer_message_v1(
            &plan,
            &startup,
            simulation,
            artifact.lookup_tables(),
        )
        .unwrap();
        let signed_wire = port
            .sign_exact_unsigned_message_v1(&plan, simulation, exact.serialized_message())
            .unwrap();
        let signed: VersionedTransaction = bincode::deserialize(&signed_wire).unwrap();
        let transaction_signature = *signed.signatures[0].as_array();
        let submission = port
            .submit_exact_signed_wire_v1(transaction_signature, &signed_wire, simulation, &startup)
            .unwrap();
        assert_eq!(submission.submitted_at_slot(), SIMULATION_SLOT);
        assert_eq!(
            submission.provider_set_digest(),
            startup.provider_set_digest()
        );
        let observation = port
            .observe_signature_v1(transaction_signature, &startup)
            .unwrap();
        let RelayerSignatureObservationV1::NotFound(not_found) = observation else {
            panic!("mock finalized status must remain not found")
        };
        assert_eq!(not_found.observed_block_height(), 499);
        assert_eq!(
            not_found.provider_set_digest(),
            startup.provider_set_digest()
        );
        assert_eq!(port.signer.calls, 1);
        assert_eq!(port.signer.last_request_id, Some(plan.request_id));
        assert_eq!(
            port.signer.last_startup_receipt_digest,
            Some(*startup.receipt_digest())
        );
        assert_eq!(
            *port.rpc.calls.borrow(),
            [
                RpcCallV1::Latest {
                    request_id: 41,
                    min_context_slot: STARTUP_SLOT,
                },
                RpcCallV1::Simulation {
                    request_id: 42,
                    min_context_slot: BLOCKHASH_SLOT,
                },
                RpcCallV1::Fee {
                    request_id: 43,
                    min_context_slot: SIMULATION_SLOT,
                },
                RpcCallV1::Send {
                    request_id: 44,
                    min_context_slot: SIMULATION_SLOT,
                },
                RpcCallV1::Status { request_id: 45 },
                RpcCallV1::BlockHeight {
                    request_id: 46,
                    min_context_slot: 110,
                },
            ]
        );
        assert_eq!(port.scan_state().head().slot(), STARTUP_SLOT);
    }

    #[test]
    fn rpc_pinned_to_different_startup_is_rejected_before_signer_call() {
        let FixtureV1 {
            plan,
            startup,
            mut scan_state,
            binding,
            viewing_secret,
            fee_payer,
            source_authority,
        } = fixture_v1([0x93u8; 32]);
        let first_rpc = MockExactRpcV1::new(&startup);
        let local_keys = NoLocalKeysV1;
        let mut first_port = ExactHttpsRelayerExecutionPortV1 {
            rpc: first_rpc,
            request_ids: SequentialRequestIdsV1(1),
            signer: RecordingSignerV1 {
                fee_payer,
                source_authority,
                calls: 0,
                last_request_id: None,
                last_startup_receipt_digest: None,
            },
            policy: policy_v1(),
            scan_state: &mut scan_state,
            pool_binding: &binding,
            viewing_secret: &viewing_secret,
            local_keys: &local_keys,
        };
        let artifact = first_port.simulate_exact_plan_v1(&plan, &startup).unwrap();
        let simulation = artifact.evidence();
        let exact = assemble_exact_unsigned_relayer_message_v1(
            &plan,
            &startup,
            simulation,
            artifact.lookup_tables(),
        )
        .unwrap();
        let ExactHttpsRelayerExecutionPortV1 {
            signer,
            request_ids,
            policy,
            ..
        } = first_port;

        let other_startup = OperatorStartupReceiptV1::test_only_v1(
            [0xa3u8; 32],
            provider_set_digest_v1(&PROVIDERS),
            startup.checkpoint(),
        );
        assert_ne!(other_startup.receipt_digest(), startup.receipt_digest());
        let mut second_port = ExactHttpsRelayerExecutionPortV1 {
            rpc: MockExactRpcV1::new(&other_startup),
            request_ids,
            signer,
            policy,
            scan_state: &mut scan_state,
            pool_binding: &binding,
            viewing_secret: &viewing_secret,
            local_keys: &local_keys,
        };
        assert_eq!(
            second_port.sign_exact_unsigned_message_v1(
                &plan,
                simulation,
                exact.serialized_message(),
            ),
            Err(ExactRelayerExecutionPortErrorV1::SigningContextMismatch)
        );
        assert_eq!(second_port.signer.calls, 0);
    }
}
