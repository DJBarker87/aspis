//! Production typed RPC calls over the exact startup-pinned HTTPS pair.
//!
//! Each method emits one codec-owned request image, submits those immutable
//! bytes to both providers, and immediately consumes the sealed responses in
//! the corresponding exact-agreement decoder. No raw single-provider result
//! is exposed as coordinator evidence.

use crate::{
    relayer_rpc_json::{
        ExactRelayerSimulationRequestV1, ExactSendTransactionRequestV1,
        FinalizedAddressLookupTableBatchV1, FinalizedAddressLookupTablesRequestV1,
        FinalizedBlockHeightRequestV1, FinalizedFeeForMessageRequestV1, FinalizedFeeForMessageV1,
        FinalizedLatestBlockhashRequestV1, FinalizedLatestBlockhashV1, RelayerSignatureStatusRpcV1,
        SignatureStatusesRequestV1, SuccessfulRelayerSimulationRpcV1,
    },
    relayer_rpc_quorum::{
        ExactTwoProviderRelayerRpcV1, RelayerRpcAgreementV1, RelayerRpcQuorumErrorV1,
    },
    rpc_adapter::DepositRpcBindingV1,
    rpc_https_transport::{ExactTwoProviderHttpsTransportV1, RpcHttpsQuorumTransportErrorV1},
    rpc_json::FinalizedGetBlockRequestV1,
    rpc_json_quorum::{
        agree_finalized_get_block_plan_v1, ingest_agreed_finalized_rpc_json_plan_v1,
        AgreedFinalizedBlockIngestV1, AgreedFinalizedRpcJsonPlanV1,
        FinalizedRootPagesQuorumInputV1, FinalizedRpcQuorumErrorV1,
    },
    scan_state::{LocalOwnerKeyStoreV1, ScanStateV1},
    ViewingSecretKeyV1,
};

const SMALL_RESPONSE_MAX_BYTES_V1: usize = 16 * 1024;
const LOOKUP_RESPONSE_BASE_MAX_BYTES_V1: usize = 16 * 1024;
const LOOKUP_RESPONSE_MAX_BYTES_PER_ACCOUNT_V1: usize = 16 * 1024;
const SIMULATION_RESPONSE_MAX_BYTES_V1: usize = 8 * 1024 * 1024;
const STATUS_RESPONSE_MAX_BYTES_V1: usize = 128 * 1024;
const FINALIZED_BLOCK_RESPONSE_MAX_BYTES_V1: usize = 64 * 1024 * 1024;
const ROOT_RESPONSE_BASE_MAX_BYTES_V1: usize = 16 * 1024;
const ROOT_RESPONSE_MAX_BYTES_PER_ACCOUNT_V1: usize = 16 * 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelayerHttpsRpcErrorV1 {
    Transport(RpcHttpsQuorumTransportErrorV1),
    RelayerQuorum(RelayerRpcQuorumErrorV1),
    FinalizedQuorum(FinalizedRpcQuorumErrorV1),
    ResponseLimitOverflow,
}

impl From<RpcHttpsQuorumTransportErrorV1> for RelayerHttpsRpcErrorV1 {
    fn from(error: RpcHttpsQuorumTransportErrorV1) -> Self {
        Self::Transport(error)
    }
}

impl From<RelayerRpcQuorumErrorV1> for RelayerHttpsRpcErrorV1 {
    fn from(error: RelayerRpcQuorumErrorV1) -> Self {
        Self::RelayerQuorum(error)
    }
}

impl From<FinalizedRpcQuorumErrorV1> for RelayerHttpsRpcErrorV1 {
    fn from(error: FinalizedRpcQuorumErrorV1) -> Self {
        Self::FinalizedQuorum(error)
    }
}

pub struct ExactRelayerHttpsRpcV1 {
    quorum: ExactTwoProviderRelayerRpcV1,
    transport: ExactTwoProviderHttpsTransportV1,
}

impl ExactRelayerHttpsRpcV1 {
    pub fn new(
        quorum: ExactTwoProviderRelayerRpcV1,
        transport: ExactTwoProviderHttpsTransportV1,
    ) -> Result<Self, RelayerHttpsRpcErrorV1> {
        if transport.provider_ids() != *quorum.provider_ids() {
            return Err(RelayerHttpsRpcErrorV1::Transport(
                RpcHttpsQuorumTransportErrorV1::ProviderOrderMismatch,
            ));
        }
        Ok(Self { quorum, transport })
    }

    pub fn quorum(&self) -> &ExactTwoProviderRelayerRpcV1 {
        &self.quorum
    }

    pub fn finalized_latest_blockhash_v1(
        &self,
        request: &FinalizedLatestBlockhashRequestV1,
    ) -> Result<RelayerRpcAgreementV1<FinalizedLatestBlockhashV1>, RelayerHttpsRpcErrorV1> {
        let responses = self
            .transport
            .post_both_exact_json_v1(&request.encode_json_v1(), SMALL_RESPONSE_MAX_BYTES_V1)?;
        Ok(self
            .quorum
            .agree_finalized_latest_blockhash_v1(request, responses.exchanges_v1())?)
    }

    pub fn finalized_lookup_tables_v1(
        &self,
        request: &FinalizedAddressLookupTablesRequestV1,
    ) -> Result<RelayerRpcAgreementV1<FinalizedAddressLookupTableBatchV1>, RelayerHttpsRpcErrorV1>
    {
        let maximum = bounded_batch_response_limit_v1(
            LOOKUP_RESPONSE_BASE_MAX_BYTES_V1,
            LOOKUP_RESPONSE_MAX_BYTES_PER_ACCOUNT_V1,
            request.addresses().len(),
        )?;
        let responses = self
            .transport
            .post_both_exact_json_v1(&request.encode_json_v1(), maximum)?;
        Ok(self
            .quorum
            .agree_finalized_lookup_tables_v1(request, responses.exchanges_v1())?)
    }

    pub fn successful_simulation_v1(
        &self,
        request: &ExactRelayerSimulationRequestV1,
    ) -> Result<RelayerRpcAgreementV1<SuccessfulRelayerSimulationRpcV1>, RelayerHttpsRpcErrorV1>
    {
        let responses = self
            .transport
            .post_both_exact_json_v1(&request.encode_json_v1(), SIMULATION_RESPONSE_MAX_BYTES_V1)?;
        Ok(self
            .quorum
            .agree_successful_simulation_v1(request, responses.exchanges_v1())?)
    }

    pub fn finalized_fee_v1(
        &self,
        request: &FinalizedFeeForMessageRequestV1,
    ) -> Result<RelayerRpcAgreementV1<FinalizedFeeForMessageV1>, RelayerHttpsRpcErrorV1> {
        let responses = self
            .transport
            .post_both_exact_json_v1(&request.encode_json_v1(), SMALL_RESPONSE_MAX_BYTES_V1)?;
        Ok(self
            .quorum
            .agree_finalized_fee_v1(request, responses.exchanges_v1())?)
    }

    pub fn send_exact_transaction_v1(
        &self,
        request: &ExactSendTransactionRequestV1,
    ) -> Result<RelayerRpcAgreementV1<[u8; 64]>, RelayerHttpsRpcErrorV1> {
        let responses = self
            .transport
            .post_both_exact_json_v1(&request.encode_json_v1(), SMALL_RESPONSE_MAX_BYTES_V1)?;
        Ok(self
            .quorum
            .agree_exact_send_signature_v1(request, responses.exchanges_v1())?)
    }

    pub fn signature_status_v1(
        &self,
        request: &SignatureStatusesRequestV1,
    ) -> Result<RelayerRpcAgreementV1<RelayerSignatureStatusRpcV1>, RelayerHttpsRpcErrorV1> {
        let responses = self
            .transport
            .post_both_exact_json_v1(&request.encode_json_v1(), STATUS_RESPONSE_MAX_BYTES_V1)?;
        Ok(self
            .quorum
            .agree_signature_status_v1(request, responses.exchanges_v1())?)
    }

    pub fn finalized_block_height_v1(
        &self,
        request: &FinalizedBlockHeightRequestV1,
    ) -> Result<RelayerRpcAgreementV1<u64>, RelayerHttpsRpcErrorV1> {
        let responses = self
            .transport
            .post_both_exact_json_v1(&request.encode_json_v1(), SMALL_RESPONSE_MAX_BYTES_V1)?;
        Ok(self
            .quorum
            .agree_finalized_block_height_v1(request, responses.exchanges_v1())?)
    }

    pub fn agreed_finalized_block_plan_v1(
        &self,
        state: &ScanStateV1,
        binding: &DepositRpcBindingV1,
        request: FinalizedGetBlockRequestV1,
    ) -> Result<AgreedFinalizedRpcJsonPlanV1, RelayerHttpsRpcErrorV1> {
        let responses = self.transport.post_both_exact_json_v1(
            &request.encode_json_v1(),
            FINALIZED_BLOCK_RESPONSE_MAX_BYTES_V1,
        )?;
        Ok(agree_finalized_get_block_plan_v1(
            &self.quorum,
            state,
            binding,
            request,
            responses.exchanges_v1(),
        )?)
    }

    #[allow(clippy::too_many_arguments)]
    pub fn ingest_agreed_finalized_block_v1(
        &self,
        state: &mut ScanStateV1,
        binding: &DepositRpcBindingV1,
        agreed: &AgreedFinalizedRpcJsonPlanV1,
        root_request_id: u64,
        viewing_secret: &ViewingSecretKeyV1,
        local_keys: &impl LocalOwnerKeyStoreV1,
    ) -> Result<AgreedFinalizedBlockIngestV1, RelayerHttpsRpcErrorV1> {
        let root_request = agreed
            .plan()
            .root_pages_request_v1(root_request_id)
            .map_err(FinalizedRpcQuorumErrorV1::Indexer)?;
        let responses = match root_request.as_ref() {
            None => None,
            Some(request) => {
                let maximum = bounded_batch_response_limit_v1(
                    ROOT_RESPONSE_BASE_MAX_BYTES_V1,
                    ROOT_RESPONSE_MAX_BYTES_PER_ACCOUNT_V1,
                    request.bindings().len(),
                )?;
                Some(
                    self.transport
                        .post_both_exact_json_v1(&request.encode_json_v1(), maximum)?,
                )
            }
        };
        let roots = match (root_request.as_ref(), responses.as_ref()) {
            (Some(request), Some(responses)) => Some(FinalizedRootPagesQuorumInputV1::new(
                request,
                responses.exchanges_v1(),
            )),
            (None, None) => None,
            _ => unreachable!("root request and response are constructed together"),
        };
        Ok(ingest_agreed_finalized_rpc_json_plan_v1(
            state,
            binding,
            agreed,
            roots,
            viewing_secret,
            local_keys,
        )?)
    }
}

fn bounded_batch_response_limit_v1(
    base: usize,
    per_account: usize,
    count: usize,
) -> Result<usize, RelayerHttpsRpcErrorV1> {
    base.checked_add(
        per_account
            .checked_mul(count)
            .ok_or(RelayerHttpsRpcErrorV1::ResponseLimitOverflow)?,
    )
    .ok_or(RelayerHttpsRpcErrorV1::ResponseLimitOverflow)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn batch_response_limit_is_checked() {
        assert_eq!(bounded_batch_response_limit_v1(16, 32, 2).unwrap(), 80);
        assert_eq!(
            bounded_batch_response_limit_v1(1, usize::MAX, 2),
            Err(RelayerHttpsRpcErrorV1::ResponseLimitOverflow)
        );
    }
}
