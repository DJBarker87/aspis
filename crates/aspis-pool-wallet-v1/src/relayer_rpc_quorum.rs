//! Exact two-provider agreement for Pool V1 relayer JSON-RPC exchanges.
//!
//! This layer is deliberately transport-free. Callers retain responsibility
//! for authenticating a response as coming from the named provider and for
//! performing network I/O. The types here bind those authenticated identities
//! to the exact codec-emitted request bytes and require strict agreement of the
//! decoded result before returning an execution input.

use sha2::{Digest as _, Sha256};

use crate::{
    operator_startup::{provider_set_digest_v1, OperatorStartupReceiptV1},
    relayer_rpc_json::{
        ExactRelayerSimulationRequestV1, ExactSendTransactionRequestV1,
        FinalizedAddressLookupTableBatchV1, FinalizedAddressLookupTablesRequestV1,
        FinalizedBlockHeightRequestV1, FinalizedFeeForMessageRequestV1, FinalizedFeeForMessageV1,
        FinalizedLatestBlockhashRequestV1, FinalizedLatestBlockhashV1, RelayerRpcJsonErrorV1,
        RelayerSignatureStatusRpcV1, SignatureStatusesRequestV1, SuccessfulRelayerSimulationRpcV1,
    },
};

pub const RELAYER_RPC_REQUEST_BINDING_DOMAIN_V1: &[u8] =
    b"aspis:pool-v1:relayer-rpc-two-provider-request:sha256:v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum RelayerRpcEndpointV1 {
    FinalizedLatestBlockhash = 1,
    FinalizedAddressLookupTables = 2,
    ExactSimulation = 3,
    FinalizedFeeForMessage = 4,
    ExactSendTransaction = 5,
    SignatureStatuses = 6,
    FinalizedBlockHeight = 7,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelayerRpcQuorumErrorV1 {
    NonCanonicalProviderIds,
    ProviderSetDigestMismatch,
    InvalidStartupCheckpoint,
    RequestBelowStartupCheckpoint,
    WrongProviderOrder {
        provider_index: u8,
    },
    WrongRequestBytes {
        provider_index: u8,
    },
    ProviderCodec {
        provider_index: u8,
        error: RelayerRpcJsonErrorV1,
    },
    ProviderDisagreement,
    ResponseBelowStartupCheckpoint,
}

/// One authenticated provider exchange supplied by a transport adapter.
///
/// `request_json` must be the exact byte slice submitted to this provider;
/// reconstructed or normalized JSON is intentionally rejected by the quorum.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExactProviderRpcExchangeV1<'a> {
    provider_id: [u8; 32],
    request_json: &'a [u8],
    response_json: &'a [u8],
}

impl<'a> ExactProviderRpcExchangeV1<'a> {
    pub fn new(provider_id: [u8; 32], request_json: &'a [u8], response_json: &'a [u8]) -> Self {
        Self {
            provider_id,
            request_json,
            response_json,
        }
    }

    pub fn provider_id(&self) -> &[u8; 32] {
        &self.provider_id
    }

    pub fn request_json(&self) -> &'a [u8] {
        self.request_json
    }

    pub fn response_json(&self) -> &'a [u8] {
        self.response_json
    }
}

/// Read-only receipt for one exact two-provider RPC agreement.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelayerRpcAgreementV1<T> {
    endpoint: RelayerRpcEndpointV1,
    provider_ids: [[u8; 32]; 2],
    provider_set_digest: [u8; 32],
    startup_receipt_digest: [u8; 32],
    startup_checkpoint_slot: u64,
    request_id: u64,
    request_min_context_slot: Option<u64>,
    request_binding_sha256: [u8; 32],
    value: T,
}

impl<T> RelayerRpcAgreementV1<T> {
    pub fn endpoint(&self) -> RelayerRpcEndpointV1 {
        self.endpoint
    }

    pub fn provider_ids(&self) -> &[[u8; 32]; 2] {
        &self.provider_ids
    }

    pub fn provider_set_digest(&self) -> &[u8; 32] {
        &self.provider_set_digest
    }

    pub fn startup_receipt_digest(&self) -> &[u8; 32] {
        &self.startup_receipt_digest
    }

    pub fn startup_checkpoint_slot(&self) -> u64 {
        self.startup_checkpoint_slot
    }

    pub fn request_id(&self) -> u64 {
        self.request_id
    }

    pub fn request_min_context_slot(&self) -> Option<u64> {
        self.request_min_context_slot
    }

    pub fn request_binding_sha256(&self) -> &[u8; 32] {
        &self.request_binding_sha256
    }

    pub fn value(&self) -> &T {
        &self.value
    }

    pub fn into_value(self) -> T {
        self.value
    }
}

/// Exact, ordered two-provider set pinned to one successful operator startup.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExactTwoProviderRelayerRpcV1 {
    provider_ids: [[u8; 32]; 2],
    provider_set_digest: [u8; 32],
    startup_receipt_digest: [u8; 32],
    startup_checkpoint_slot: u64,
}

impl ExactTwoProviderRelayerRpcV1 {
    pub fn new(
        provider_ids: [[u8; 32]; 2],
        startup: &OperatorStartupReceiptV1,
    ) -> Result<Self, RelayerRpcQuorumErrorV1> {
        if provider_ids[0] == [0u8; 32]
            || provider_ids[1] == [0u8; 32]
            || provider_ids[0] >= provider_ids[1]
        {
            return Err(RelayerRpcQuorumErrorV1::NonCanonicalProviderIds);
        }
        let provider_set_digest = provider_set_digest_v1(&provider_ids);
        if &provider_set_digest != startup.provider_set_digest() {
            return Err(RelayerRpcQuorumErrorV1::ProviderSetDigestMismatch);
        }
        let startup_checkpoint_slot = startup.checkpoint().point.slot();
        if startup_checkpoint_slot == 0 {
            return Err(RelayerRpcQuorumErrorV1::InvalidStartupCheckpoint);
        }
        Ok(Self {
            provider_ids,
            provider_set_digest,
            startup_receipt_digest: *startup.receipt_digest(),
            startup_checkpoint_slot,
        })
    }

    pub fn provider_ids(&self) -> &[[u8; 32]; 2] {
        &self.provider_ids
    }

    pub fn provider_set_digest(&self) -> &[u8; 32] {
        &self.provider_set_digest
    }

    pub fn startup_receipt_digest(&self) -> &[u8; 32] {
        &self.startup_receipt_digest
    }

    pub fn startup_checkpoint_slot(&self) -> u64 {
        self.startup_checkpoint_slot
    }

    pub fn agree_finalized_latest_blockhash_v1(
        &self,
        request: &FinalizedLatestBlockhashRequestV1,
        exchanges: [ExactProviderRpcExchangeV1<'_>; 2],
    ) -> Result<RelayerRpcAgreementV1<FinalizedLatestBlockhashV1>, RelayerRpcQuorumErrorV1> {
        self.agree_v1(
            RelayerRpcEndpointV1::FinalizedLatestBlockhash,
            request.request_id(),
            Some(request.min_context_slot()),
            request.encode_json_v1(),
            exchanges,
            |response| request.decode_response_v1(response),
        )
    }

    pub fn agree_finalized_lookup_tables_v1(
        &self,
        request: &FinalizedAddressLookupTablesRequestV1,
        exchanges: [ExactProviderRpcExchangeV1<'_>; 2],
    ) -> Result<RelayerRpcAgreementV1<FinalizedAddressLookupTableBatchV1>, RelayerRpcQuorumErrorV1>
    {
        self.agree_v1(
            RelayerRpcEndpointV1::FinalizedAddressLookupTables,
            request.request_id(),
            Some(request.min_context_slot()),
            request.encode_json_v1(),
            exchanges,
            |response| request.decode_response_v1(response, self.provider_set_digest),
        )
    }

    pub fn agree_successful_simulation_v1(
        &self,
        request: &ExactRelayerSimulationRequestV1,
        exchanges: [ExactProviderRpcExchangeV1<'_>; 2],
    ) -> Result<RelayerRpcAgreementV1<SuccessfulRelayerSimulationRpcV1>, RelayerRpcQuorumErrorV1>
    {
        self.agree_v1(
            RelayerRpcEndpointV1::ExactSimulation,
            request.request_id(),
            Some(request.min_context_slot()),
            request.encode_json_v1(),
            exchanges,
            |response| request.decode_success_response_v1(response, self.provider_set_digest),
        )
    }

    pub fn agree_finalized_fee_v1(
        &self,
        request: &FinalizedFeeForMessageRequestV1,
        exchanges: [ExactProviderRpcExchangeV1<'_>; 2],
    ) -> Result<RelayerRpcAgreementV1<FinalizedFeeForMessageV1>, RelayerRpcQuorumErrorV1> {
        self.agree_v1(
            RelayerRpcEndpointV1::FinalizedFeeForMessage,
            request.request_id(),
            Some(request.min_context_slot()),
            request.encode_json_v1(),
            exchanges,
            |response| request.decode_response_v1(response),
        )
    }

    pub fn agree_exact_send_signature_v1(
        &self,
        request: &ExactSendTransactionRequestV1,
        exchanges: [ExactProviderRpcExchangeV1<'_>; 2],
    ) -> Result<RelayerRpcAgreementV1<[u8; 64]>, RelayerRpcQuorumErrorV1> {
        self.agree_v1(
            RelayerRpcEndpointV1::ExactSendTransaction,
            request.request_id(),
            Some(request.min_context_slot()),
            request.encode_json_v1(),
            exchanges,
            |response| request.decode_response_v1(response),
        )
    }

    pub fn agree_signature_status_v1(
        &self,
        request: &SignatureStatusesRequestV1,
        exchanges: [ExactProviderRpcExchangeV1<'_>; 2],
    ) -> Result<RelayerRpcAgreementV1<RelayerSignatureStatusRpcV1>, RelayerRpcQuorumErrorV1> {
        let agreement = self.agree_v1(
            RelayerRpcEndpointV1::SignatureStatuses,
            request.request_id(),
            None,
            request.encode_json_v1(),
            exchanges,
            |response| request.decode_response_v1(response),
        )?;
        if signature_status_context_slot_v1(agreement.value()) < self.startup_checkpoint_slot {
            return Err(RelayerRpcQuorumErrorV1::ResponseBelowStartupCheckpoint);
        }
        Ok(agreement)
    }

    pub fn agree_finalized_block_height_v1(
        &self,
        request: &FinalizedBlockHeightRequestV1,
        exchanges: [ExactProviderRpcExchangeV1<'_>; 2],
    ) -> Result<RelayerRpcAgreementV1<u64>, RelayerRpcQuorumErrorV1> {
        self.agree_v1(
            RelayerRpcEndpointV1::FinalizedBlockHeight,
            request.request_id(),
            Some(request.min_context_slot()),
            request.encode_json_v1(),
            exchanges,
            |response| request.decode_response_v1(response),
        )
    }

    fn agree_v1<T, F>(
        &self,
        endpoint: RelayerRpcEndpointV1,
        request_id: u64,
        request_min_context_slot: Option<u64>,
        expected_request_json: Vec<u8>,
        exchanges: [ExactProviderRpcExchangeV1<'_>; 2],
        decode: F,
    ) -> Result<RelayerRpcAgreementV1<T>, RelayerRpcQuorumErrorV1>
    where
        T: PartialEq,
        F: Fn(&[u8]) -> Result<T, RelayerRpcJsonErrorV1>,
    {
        if request_min_context_slot.is_some_and(|slot| slot < self.startup_checkpoint_slot) {
            return Err(RelayerRpcQuorumErrorV1::RequestBelowStartupCheckpoint);
        }
        for (provider_index, exchange) in exchanges.iter().enumerate() {
            if exchange.provider_id != self.provider_ids[provider_index] {
                return Err(RelayerRpcQuorumErrorV1::WrongProviderOrder {
                    provider_index: provider_index as u8,
                });
            }
            if exchange.request_json != expected_request_json {
                return Err(RelayerRpcQuorumErrorV1::WrongRequestBytes {
                    provider_index: provider_index as u8,
                });
            }
        }

        let first = decode(exchanges[0].response_json).map_err(|error| {
            RelayerRpcQuorumErrorV1::ProviderCodec {
                provider_index: 0,
                error,
            }
        })?;
        let second = decode(exchanges[1].response_json).map_err(|error| {
            RelayerRpcQuorumErrorV1::ProviderCodec {
                provider_index: 1,
                error,
            }
        })?;
        if first != second {
            return Err(RelayerRpcQuorumErrorV1::ProviderDisagreement);
        }

        Ok(RelayerRpcAgreementV1 {
            endpoint,
            provider_ids: self.provider_ids,
            provider_set_digest: self.provider_set_digest,
            startup_receipt_digest: self.startup_receipt_digest,
            startup_checkpoint_slot: self.startup_checkpoint_slot,
            request_id,
            request_min_context_slot,
            request_binding_sha256: request_binding_digest_v1(
                endpoint,
                request_id,
                request_min_context_slot,
                &expected_request_json,
            ),
            value: first,
        })
    }
}

pub(crate) fn request_binding_digest_v1(
    endpoint: RelayerRpcEndpointV1,
    request_id: u64,
    request_min_context_slot: Option<u64>,
    request_json: &[u8],
) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(RELAYER_RPC_REQUEST_BINDING_DOMAIN_V1);
    hasher.update([endpoint as u8]);
    hasher.update(request_id.to_le_bytes());
    hasher.update([u8::from(request_min_context_slot.is_some())]);
    hasher.update(request_min_context_slot.unwrap_or(0).to_le_bytes());
    hasher.update((request_json.len() as u64).to_le_bytes());
    hasher.update(request_json);
    hasher.finalize().into()
}

fn signature_status_context_slot_v1(status: &RelayerSignatureStatusRpcV1) -> u64 {
    match status {
        RelayerSignatureStatusRpcV1::NotFound { context_slot, .. }
        | RelayerSignatureStatusRpcV1::Pending { context_slot, .. }
        | RelayerSignatureStatusRpcV1::Finalized { context_slot, .. } => *context_slot,
    }
}

#[cfg(test)]
mod tests {
    use std::borrow::Cow;

    use serde_json::{json, Value};
    use solana_address_lookup_table_interface::state::{AddressLookupTable, LookupTableMeta};
    use solana_keypair::Keypair;
    use solana_message::{legacy, VersionedMessage};
    use solana_program::hash::Hash;
    use solana_program::pubkey::Pubkey;
    use solana_signature::Signature;
    use solana_signer::Signer;
    use solana_transaction::versioned::VersionedTransaction;

    use super::*;
    use crate::{
        operator_startup::{provider_set_digest_v1, FinalizedReleaseCheckpointV1},
        scan_state::FinalizedChainPointV1,
    };

    const PROVIDERS: [[u8; 32]; 2] = [[1u8; 32], [2u8; 32]];
    const STARTUP_SLOT: u64 = 100;

    fn key(byte: u8) -> Pubkey {
        Pubkey::new_from_array([byte; 32])
    }

    fn startup_v1(provider_ids: [[u8; 32]; 2]) -> OperatorStartupReceiptV1 {
        OperatorStartupReceiptV1::test_only_v1(
            [3u8; 32],
            provider_set_digest_v1(&provider_ids),
            FinalizedReleaseCheckpointV1 {
                point: FinalizedChainPointV1::new(STARTUP_SLOT, [4u8; 32]).unwrap(),
                pool_state_sha256: [5u8; 32],
                root_sequence: 6,
                root: [7u8; 32],
            },
        )
    }

    fn quorum_v1() -> ExactTwoProviderRelayerRpcV1 {
        ExactTwoProviderRelayerRpcV1::new(PROVIDERS, &startup_v1(PROVIDERS)).unwrap()
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

    fn base64_standard_v1(bytes: &[u8]) -> String {
        const TABLE: &[u8; 64] =
            b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
        let mut output = String::with_capacity(bytes.len().div_ceil(3) * 4);
        for chunk in bytes.chunks(3) {
            let a = chunk[0];
            let b = chunk.get(1).copied().unwrap_or(0);
            let c = chunk.get(2).copied().unwrap_or(0);
            output.push(TABLE[(a >> 2) as usize] as char);
            output.push(TABLE[(((a & 0x03) << 4) | (b >> 4)) as usize] as char);
            output.push(if chunk.len() > 1 {
                TABLE[(((b & 0x0f) << 2) | (c >> 6)) as usize] as char
            } else {
                '='
            });
            output.push(if chunk.len() > 2 {
                TABLE[(c & 0x3f) as usize] as char
            } else {
                '='
            });
        }
        output
    }

    fn lookup_table_data_v1(address_byte: u8) -> Vec<u8> {
        AddressLookupTable {
            meta: LookupTableMeta {
                last_extended_slot: 99,
                ..LookupTableMeta::default()
            },
            addresses: Cow::Owned(vec![key(address_byte)]),
        }
        .serialize_for_tests()
        .unwrap()
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

    fn zero_signature_legacy_wire_v1() -> Vec<u8> {
        let message = VersionedMessage::Legacy(legacy::Message::new_with_blockhash(
            &[],
            Some(&key(1)),
            &Hash::new_from_array([2u8; 32]),
        ));
        bincode::serialize(&VersionedTransaction {
            signatures: vec![Signature::default()],
            message,
        })
        .unwrap()
    }

    fn signed_wire_v1() -> (Vec<u8>, [u8; 64]) {
        let payer = Keypair::new();
        let message = VersionedMessage::Legacy(legacy::Message::new_with_blockhash(
            &[],
            Some(&payer.pubkey()),
            &Hash::new_from_array([4u8; 32]),
        ));
        let transaction = VersionedTransaction::try_new(message, &[&payer]).unwrap();
        let signature = *transaction.signatures[0].as_array();
        (bincode::serialize(&transaction).unwrap(), signature)
    }

    #[test]
    fn constructor_binds_exact_ordered_provider_set_and_startup() {
        let startup = startup_v1(PROVIDERS);
        let quorum = ExactTwoProviderRelayerRpcV1::new(PROVIDERS, &startup).unwrap();
        assert_eq!(quorum.provider_ids(), &PROVIDERS);
        assert_eq!(quorum.provider_set_digest(), startup.provider_set_digest());
        assert_eq!(quorum.startup_receipt_digest(), startup.receipt_digest());
        assert_eq!(quorum.startup_checkpoint_slot(), STARTUP_SLOT);

        assert_eq!(
            ExactTwoProviderRelayerRpcV1::new([PROVIDERS[1], PROVIDERS[0]], &startup),
            Err(RelayerRpcQuorumErrorV1::NonCanonicalProviderIds)
        );
        assert_eq!(
            ExactTwoProviderRelayerRpcV1::new([[0u8; 32], PROVIDERS[1]], &startup),
            Err(RelayerRpcQuorumErrorV1::NonCanonicalProviderIds)
        );
        assert_eq!(
            ExactTwoProviderRelayerRpcV1::new(PROVIDERS, &startup_v1([[1u8; 32], [3u8; 32]])),
            Err(RelayerRpcQuorumErrorV1::ProviderSetDigestMismatch)
        );
    }

    #[test]
    fn latest_blockhash_agreement_binds_exact_request_and_semantics() {
        let quorum = quorum_v1();
        let request = FinalizedLatestBlockhashRequestV1::new(7, STARTUP_SLOT).unwrap();
        let request_json = request.encode_json_v1();
        let blockhash = key(9).to_string();
        let first = response_v1(
            7,
            json!({"blockhash": blockhash, "lastValidBlockHeight": 500}),
            Some(101),
        );
        let second = format!(
            "{{ \"result\": {{\"value\": {{\"lastValidBlockHeight\":500,\"blockhash\":\"{}\"}},\"context\":{{\"slot\":101}}}}, \"id\":7, \"jsonrpc\":\"2.0\" }}",
            key(9)
        )
        .into_bytes();
        let agreement = quorum
            .agree_finalized_latest_blockhash_v1(
                &request,
                exchanges_v1(&request_json, &first, &second),
            )
            .unwrap();
        assert_eq!(
            agreement.endpoint(),
            RelayerRpcEndpointV1::FinalizedLatestBlockhash
        );
        assert_eq!(agreement.request_id(), 7);
        assert_eq!(agreement.request_min_context_slot(), Some(STARTUP_SLOT));
        assert_eq!(agreement.value().context_slot, 101);
        assert_ne!(agreement.request_binding_sha256(), &[0u8; 32]);

        let wrong_order = [
            ExactProviderRpcExchangeV1::new(PROVIDERS[1], &request_json, &first),
            ExactProviderRpcExchangeV1::new(PROVIDERS[0], &request_json, &second),
        ];
        assert_eq!(
            quorum.agree_finalized_latest_blockhash_v1(&request, wrong_order),
            Err(RelayerRpcQuorumErrorV1::WrongProviderOrder { provider_index: 0 })
        );

        let altered_request = [request_json.as_slice(), b"{}"].map(|bytes| bytes as &[u8]);
        let wrong_request = [
            ExactProviderRpcExchangeV1::new(PROVIDERS[0], altered_request[0], &first),
            ExactProviderRpcExchangeV1::new(PROVIDERS[1], altered_request[1], &second),
        ];
        assert_eq!(
            quorum.agree_finalized_latest_blockhash_v1(&request, wrong_request),
            Err(RelayerRpcQuorumErrorV1::WrongRequestBytes { provider_index: 1 })
        );

        let disagreement = response_v1(
            7,
            json!({"blockhash": key(8).to_string(), "lastValidBlockHeight": 500}),
            Some(101),
        );
        assert_eq!(
            quorum.agree_finalized_latest_blockhash_v1(
                &request,
                exchanges_v1(&request_json, &first, &disagreement)
            ),
            Err(RelayerRpcQuorumErrorV1::ProviderDisagreement)
        );

        let wrong_id = response_v1(
            8,
            json!({"blockhash": key(9).to_string(), "lastValidBlockHeight": 500}),
            Some(101),
        );
        assert_eq!(
            quorum.agree_finalized_latest_blockhash_v1(
                &request,
                exchanges_v1(&request_json, &first, &wrong_id)
            ),
            Err(RelayerRpcQuorumErrorV1::ProviderCodec {
                provider_index: 1,
                error: RelayerRpcJsonErrorV1::WrongResponseId,
            })
        );

        let stale_request = FinalizedLatestBlockhashRequestV1::new(7, STARTUP_SLOT - 1).unwrap();
        let stale_json = stale_request.encode_json_v1();
        assert_eq!(
            quorum.agree_finalized_latest_blockhash_v1(
                &stale_request,
                exchanges_v1(&stale_json, &first, &second)
            ),
            Err(RelayerRpcQuorumErrorV1::RequestBelowStartupCheckpoint)
        );
    }

    #[test]
    fn raw_lookup_table_image_mismatch_has_no_quorum() {
        let quorum = quorum_v1();
        let request =
            FinalizedAddressLookupTablesRequestV1::new(8, STARTUP_SLOT, vec![key(10)]).unwrap();
        let request_json = request.encode_json_v1();
        let first = response_v1(
            8,
            Value::Array(vec![account_value_v1(&lookup_table_data_v1(11))]),
            Some(STARTUP_SLOT),
        );
        let second = response_v1(
            8,
            Value::Array(vec![account_value_v1(&lookup_table_data_v1(12))]),
            Some(STARTUP_SLOT),
        );
        assert_eq!(
            quorum.agree_finalized_lookup_tables_v1(
                &request,
                exchanges_v1(&request_json, &first, &second)
            ),
            Err(RelayerRpcQuorumErrorV1::ProviderDisagreement)
        );

        let agreement = quorum
            .agree_finalized_lookup_tables_v1(&request, exchanges_v1(&request_json, &first, &first))
            .unwrap();
        assert_eq!(
            agreement.value().lookup_tables[0].account_data(),
            lookup_table_data_v1(11)
        );
        assert_eq!(
            agreement.value().lookup_tables[0].provider_set_digest(),
            quorum.provider_set_digest()
        );
    }

    #[test]
    fn fee_status_and_block_height_require_strict_contextual_agreement() {
        let quorum = quorum_v1();
        let fee =
            FinalizedFeeForMessageRequestV1::new(9, STARTUP_SLOT, 10_000, vec![1, 2]).unwrap();
        let fee_json = fee.encode_json_v1();
        let fee_response = response_v1(9, json!(5_000u64), Some(STARTUP_SLOT));
        assert_eq!(
            quorum
                .agree_finalized_fee_v1(&fee, exchanges_v1(&fee_json, &fee_response, &fee_response))
                .unwrap()
                .value()
                .fee_lamports,
            5_000
        );

        let signature = [13u8; 64];
        let statuses = SignatureStatusesRequestV1::new(10, signature).unwrap();
        let status_json = statuses.encode_json_v1();
        let stale_status = response_v1(10, json!([null]), Some(STARTUP_SLOT - 1));
        assert_eq!(
            quorum.agree_signature_status_v1(
                &statuses,
                exchanges_v1(&status_json, &stale_status, &stale_status)
            ),
            Err(RelayerRpcQuorumErrorV1::ResponseBelowStartupCheckpoint)
        );
        let current_status = response_v1(10, json!([null]), Some(STARTUP_SLOT));
        let status_agreement = quorum
            .agree_signature_status_v1(
                &statuses,
                exchanges_v1(&status_json, &current_status, &current_status),
            )
            .unwrap();
        assert_eq!(status_agreement.request_min_context_slot(), None);

        let height = FinalizedBlockHeightRequestV1::new(11, STARTUP_SLOT).unwrap();
        let height_json = height.encode_json_v1();
        let first = response_v1(11, json!(700u64), None);
        let second = response_v1(11, json!(701u64), None);
        assert_eq!(
            quorum.agree_finalized_block_height_v1(
                &height,
                exchanges_v1(&height_json, &first, &second)
            ),
            Err(RelayerRpcQuorumErrorV1::ProviderDisagreement)
        );
    }

    #[test]
    fn simulation_and_send_require_exact_canonical_results() {
        let quorum = quorum_v1();
        let simulation = ExactRelayerSimulationRequestV1::new(
            12,
            STARTUP_SLOT,
            500,
            zero_signature_legacy_wire_v1(),
            vec![],
        )
        .unwrap();
        let simulation_json = simulation.encode_json_v1();
        let simulation_value = |log: &str| {
            json!({
                "err": null,
                "logs": [log],
                "unitsConsumed": 450,
                "returnData": null,
                "innerInstructions": null,
                "replacementBlockhash": null,
                "loadedAccountsDataSize": 88
            })
        };
        let first = response_v1(
            12,
            simulation_value("Program log: exact"),
            Some(STARTUP_SLOT),
        );
        let second = response_v1(
            12,
            simulation_value("Program log: changed"),
            Some(STARTUP_SLOT),
        );
        assert_eq!(
            quorum.agree_successful_simulation_v1(
                &simulation,
                exchanges_v1(&simulation_json, &first, &second)
            ),
            Err(RelayerRpcQuorumErrorV1::ProviderDisagreement)
        );
        assert_eq!(
            quorum
                .agree_successful_simulation_v1(
                    &simulation,
                    exchanges_v1(&simulation_json, &first, &first)
                )
                .unwrap()
                .value()
                .compute_units_consumed,
            450
        );

        let (signed_wire, signature) = signed_wire_v1();
        let send =
            ExactSendTransactionRequestV1::new(13, STARTUP_SLOT, signature, signed_wire).unwrap();
        let send_json = send.encode_json_v1();
        let send_response = response_v1(13, json!(Signature::from(signature).to_string()), None);
        assert_eq!(
            quorum
                .agree_exact_send_signature_v1(
                    &send,
                    exchanges_v1(&send_json, &send_response, &send_response)
                )
                .unwrap()
                .into_value(),
            signature
        );
    }

    #[test]
    fn endpoint_discriminator_changes_the_request_binding() {
        let request = br#"{\"jsonrpc\":\"2.0\",\"id\":7}"#;
        assert_ne!(
            request_binding_digest_v1(
                RelayerRpcEndpointV1::FinalizedLatestBlockhash,
                7,
                Some(100),
                request
            ),
            request_binding_digest_v1(
                RelayerRpcEndpointV1::FinalizedBlockHeight,
                7,
                Some(100),
                request
            )
        );
    }
}
