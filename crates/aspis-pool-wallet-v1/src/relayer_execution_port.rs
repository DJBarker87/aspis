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
        FinalizedAddressLookupTablesRequestV1, FinalizedBlockHeightRequestV1,
        FinalizedFeeForMessageRequestV1, FinalizedLatestBlockhashRequestV1, RelayerRpcJsonErrorV1,
        RelayerSignatureStatusRpcV1, SignatureStatusesRequestV1, RELAYER_RPC_MAX_LOOKUP_TABLES_V1,
    },
    relayer_rpc_request_id::RelayerRpcRequestIdSourceV1,
    relayer_transaction::{
        assemble_exact_pre_simulation_relayer_transaction_v1, RelayerTransactionErrorV1,
    },
    rpc_adapter::DepositRpcBindingV1,
    rpc_json::{FinalizedGetBlockRequestV1, RpcJsonErrorV1},
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

pub struct ExactHttpsRelayerExecutionPortV1<'a, I, S, K> {
    rpc: ExactRelayerHttpsRpcV1,
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

    pub fn scan_state(&self) -> &ScanStateV1 {
        self.scan_state
    }
}

impl<I, S, K> RelayerExecutionPortV1 for ExactHttpsRelayerExecutionPortV1<'_, I, S, K>
where
    I: RelayerRpcRequestIdSourceV1,
    S: ExternalRelayerSignerV1,
    K: LocalOwnerKeyStoreV1,
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
            || simulation.startup_receipt_digest == [0u8; 32]
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

impl<I, S, K> ExactHttpsRelayerExecutionPortV1<'_, I, S, K>
where
    I: RelayerRpcRequestIdSourceV1,
    S: ExternalRelayerSignerV1,
    K: LocalOwnerKeyStoreV1,
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
    use super::*;

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
}
