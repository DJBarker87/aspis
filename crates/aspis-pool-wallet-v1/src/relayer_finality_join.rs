//! Exact join from finalized status and block/indexer quorum receipts into the
//! coordinator's constructor-sealed finalized observation.
//!
//! This module performs no transport and does not infer finality. Both inputs
//! must already have been produced by their exact, startup-pinned two-provider
//! agreement layers. A finalized failed transaction remains a separate ABI
//! boundary and is never converted into a blockhash-expiry observation.

use crate::{
    operator_execution::{RelayerFinalizedObservationV1, RelayerSignatureObservationV1},
    operator_startup::{provider_set_digest_v1, OperatorStartupReceiptV1},
    relayer_rpc_composition::RelayerFinalizedStatusHintV1,
    rpc_json::RpcJsonErrorV1,
    rpc_json_quorum::{AgreedFinalizedBlockIngestV1, AgreedFinalizedRpcJsonPlanV1},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelayerFinalityJoinErrorV1 {
    StartupReceiptMismatch,
    ProviderSetMismatch,
    InvalidStatusEvidence,
    BlockRequestBindingMismatch,
    RootRequestBindingMismatch,
    RequestedLandedSlotMismatch,
    StatusContextBeforeLanded,
    FinalizedFailureJoinRequired,
    TransactionExecution(RpcJsonErrorV1),
    ExecutionPointMismatch,
}

impl From<RpcJsonErrorV1> for RelayerFinalityJoinErrorV1 {
    fn from(error: RpcJsonErrorV1) -> Self {
        Self::TransactionExecution(error)
    }
}

/// Join one successful finalized signature-status hint to the exact agreed
/// getBlock transaction and its authenticated Pool ingest result.
///
/// `ingest` is consumed because the coordinator observation owns the indexer
/// evidence. External callers cannot construct `RelayerFinalizedObservationV1`
/// directly; they can only inspect its read-only getters after this join.
pub fn join_successful_relayer_finality_v1(
    startup: &OperatorStartupReceiptV1,
    hint: RelayerFinalizedStatusHintV1,
    plan: &AgreedFinalizedRpcJsonPlanV1,
    ingest: AgreedFinalizedBlockIngestV1,
) -> Result<RelayerSignatureObservationV1, RelayerFinalityJoinErrorV1> {
    if startup.receipt_digest() == &[0u8; 32]
        || startup.receipt_digest() != hint.startup_receipt_digest()
        || startup.receipt_digest() != plan.startup_receipt_digest()
        || startup.receipt_digest() != ingest.startup_receipt_digest()
        || startup.checkpoint().point.slot() != plan.startup_checkpoint_slot()
    {
        return Err(RelayerFinalityJoinErrorV1::StartupReceiptMismatch);
    }

    let expected_provider_set_digest = provider_set_digest_v1(plan.provider_ids());
    if startup.provider_set_digest() == &[0u8; 32]
        || startup.provider_set_digest() != hint.provider_set_digest()
        || startup.provider_set_digest() != plan.provider_set_digest()
        || startup.provider_set_digest() != ingest.provider_set_digest()
        || startup.provider_set_digest() != &expected_provider_set_digest
    {
        return Err(RelayerFinalityJoinErrorV1::ProviderSetMismatch);
    }

    if hint.status_request_id() == 0
        || hint.status_request_binding_sha256() == &[0u8; 32]
        || hint.execution_result_sha256() == &[0u8; 32]
    {
        return Err(RelayerFinalityJoinErrorV1::InvalidStatusEvidence);
    }
    if plan.block_request_binding_sha256() == &[0u8; 32]
        || plan.block_request_binding_sha256() != ingest.block_request_binding_sha256()
    {
        return Err(RelayerFinalityJoinErrorV1::BlockRequestBindingMismatch);
    }

    let root_request_binding_sha256 = ingest.root_request_binding_sha256().copied();
    let root_request_required = !plan.plan().root_page_bindings().is_empty();
    if root_request_required != root_request_binding_sha256.is_some()
        || root_request_binding_sha256 == Some([0u8; 32])
    {
        return Err(RelayerFinalityJoinErrorV1::RootRequestBindingMismatch);
    }

    let block_request = plan.plan().block_request();
    if block_request.slot() != hint.landed_slot()
        || hint.landed_slot() < startup.checkpoint().point.slot()
    {
        return Err(RelayerFinalityJoinErrorV1::RequestedLandedSlotMismatch);
    }
    if hint.context_slot() < hint.landed_slot() {
        return Err(RelayerFinalityJoinErrorV1::StatusContextBeforeLanded);
    }
    if !hint.succeeded() {
        return Err(RelayerFinalityJoinErrorV1::FinalizedFailureJoinRequired);
    }

    let execution = plan
        .plan()
        .transaction_execution_v1(*hint.transaction_signature())?;
    if execution.point().slot() != hint.landed_slot()
        || execution.transaction_signature() != hint.transaction_signature()
    {
        return Err(RelayerFinalityJoinErrorV1::ExecutionPointMismatch);
    }

    Ok(RelayerSignatureObservationV1::Finalized(
        RelayerFinalizedObservationV1::from_agreed_finality_v1(
            execution,
            ingest.into_result(),
            expected_provider_set_digest,
            *hint.execution_result_sha256(),
            *plan.block_request_binding_sha256(),
            root_request_binding_sha256,
        ),
    ))
}

#[cfg(test)]
mod tests {
    use aspis_core::field::M31;
    use aspis_statement::{encode_digest_canonical, poseidon2::Digest};
    use serde_json::json;
    use solana_program::pubkey::Pubkey;

    use super::*;
    use crate::{
        derive_viewing_keypair_v1,
        operator_startup::{FinalizedReleaseCheckpointV1, OperatorStartupReceiptV1},
        relayer_rpc_composition::{
            compose_relayer_signature_status_v1, ComposedRelayerSignatureStatusV1,
        },
        relayer_rpc_json::SignatureStatusesRequestV1,
        relayer_rpc_quorum::{ExactProviderRpcExchangeV1, ExactTwoProviderRelayerRpcV1},
        rpc_adapter::DepositRpcBindingV1,
        rpc_json::FinalizedGetBlockRequestV1,
        rpc_json_quorum::{
            agree_finalized_get_block_plan_v1, ingest_agreed_finalized_rpc_json_plan_v1,
        },
        scan_state::{
            DepositScanIdentityV1, FinalizedBlockAdvanceV1, FinalizedChainPointV1,
            LocalOwnerKeyStoreV1, ScanStateV1,
        },
        ViewingSecretKeyV1,
    };

    const PROVIDERS: [[u8; 32]; 2] = [[1u8; 32], [2u8; 32]];
    const STARTUP_SLOT: u64 = 100;
    const LANDED_SLOT: u64 = 101;
    const SIGNATURE: [u8; 64] = [0x55; 64];

    struct EmptyKeys;

    impl LocalOwnerKeyStoreV1 for EmptyKeys {
        fn contains_owner_key_v1(&self, _: &[u8; 32]) -> bool {
            false
        }
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + index as u32))
    }

    fn encode_base58(bytes: &[u8]) -> String {
        const ALPHABET: &[u8; 58] = b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
        let leading_zeroes = bytes.iter().take_while(|byte| **byte == 0).count();
        let mut digits = Vec::<u8>::new();
        for byte in &bytes[leading_zeroes..] {
            let mut carry = u32::from(*byte);
            for digit in &mut digits {
                let value = u32::from(*digit) * 256 + carry;
                *digit = (value % 58) as u8;
                carry = value / 58;
            }
            while carry != 0 {
                digits.push((carry % 58) as u8);
                carry /= 58;
            }
        }
        let mut output = String::new();
        output.extend(core::iter::repeat_n('1', leading_zeroes));
        output.extend(
            digits
                .iter()
                .rev()
                .map(|digit| char::from(ALPHABET[usize::from(*digit)])),
        );
        output
    }

    fn fixture() -> (
        ScanStateV1,
        DepositRpcBindingV1,
        ViewingSecretKeyV1,
        OperatorStartupReceiptV1,
        ExactTwoProviderRelayerRpcV1,
    ) {
        let program = Pubkey::new_from_array([0x91; 32]);
        let mint = Pubkey::new_from_array([0x33; 32]);
        let pool = aspis_pool::pool_v1_state_address(&program, &mint).0;
        let vault = aspis_pool::pool_v1_vault_token_account_address(&program, &pool).0;
        let identity = DepositScanIdentityV1::new(
            pool.to_bytes(),
            [0x22; 32],
            mint.to_bytes(),
            vault.to_bytes(),
            9,
        )
        .unwrap();
        let point = FinalizedChainPointV1::new(STARTUP_SLOT, [0xa0; 32]).unwrap();
        let state =
            ScanStateV1::new(identity, point, 7, encode_digest_canonical(&digest(20))).unwrap();
        let binding = DepositRpcBindingV1::new(program.to_bytes()).unwrap();
        let viewing = derive_viewing_keypair_v1(&[0x51; 32]).unwrap().0;
        let startup = OperatorStartupReceiptV1::test_only_v1(
            [3u8; 32],
            provider_set_digest_v1(&PROVIDERS),
            FinalizedReleaseCheckpointV1 {
                point,
                pool_state_sha256: [5u8; 32],
                root_sequence: 7,
                root: encode_digest_canonical(&digest(20)),
            },
        );
        let quorum = ExactTwoProviderRelayerRpcV1::new(PROVIDERS, &startup).unwrap();
        (state, binding, viewing, startup, quorum)
    }

    fn response_v1(request_id: u64, result: serde_json::Value) -> Vec<u8> {
        serde_json::to_vec(&json!({
            "jsonrpc": "2.0",
            "id": request_id,
            "result": result,
        }))
        .unwrap()
    }

    fn block_response_v1(request_id: u64, signature: [u8; 64]) -> Vec<u8> {
        response_v1(
            request_id,
            json!({
                "blockhash": encode_base58(&[0xa1; 32]),
                "previousBlockhash": encode_base58(&[0xa0; 32]),
                "parentSlot": STARTUP_SLOT,
                "transactions": [{
                    "transaction": {
                        "signatures": [encode_base58(&signature)],
                        "message": {
                            "header": {
                                "numRequiredSignatures": 1,
                                "numReadonlySignedAccounts": 0,
                                "numReadonlyUnsignedAccounts": 0
                            },
                            "accountKeys": [encode_base58(&[0x71; 32])],
                            "recentBlockhash": encode_base58(&[0x72; 32]),
                            "instructions": [],
                            "addressTableLookups": []
                        }
                    },
                    "meta": {
                        "err": null,
                        "loadedAddresses": {"writable": [], "readonly": []},
                        "fee": 5_000,
                        "computeUnitsConsumed": 777
                    },
                    "version": 0
                }],
                "rewards": []
            }),
        )
    }

    fn exchanges<'a>(
        request_json: &'a [u8],
        response: &'a [u8],
    ) -> [ExactProviderRpcExchangeV1<'a>; 2] {
        [
            ExactProviderRpcExchangeV1::new(PROVIDERS[0], request_json, response),
            ExactProviderRpcExchangeV1::new(PROVIDERS[1], request_json, response),
        ]
    }

    fn agreed_block_v1(
        block_request_id: u64,
        block_slot: u64,
        block_signature: [u8; 64],
    ) -> (
        OperatorStartupReceiptV1,
        AgreedFinalizedRpcJsonPlanV1,
        AgreedFinalizedBlockIngestV1,
    ) {
        let (mut state, binding, viewing, startup, quorum) = fixture();
        let request = FinalizedGetBlockRequestV1::new(block_request_id, block_slot).unwrap();
        let request_json = request.encode_json_v1();
        let response = block_response_v1(block_request_id, block_signature);
        let agreed = agree_finalized_get_block_plan_v1(
            &quorum,
            &state,
            &binding,
            request,
            exchanges(&request_json, &response),
        )
        .unwrap();
        let ingested = ingest_agreed_finalized_rpc_json_plan_v1(
            &mut state, &binding, &agreed, None, &viewing, &EmptyKeys,
        )
        .unwrap();
        (startup, agreed, ingested)
    }

    fn finalized_hint_v1(
        startup: &OperatorStartupReceiptV1,
        signature: [u8; 64],
        landed_slot: u64,
        succeeded: bool,
    ) -> RelayerFinalizedStatusHintV1 {
        let quorum = ExactTwoProviderRelayerRpcV1::new(PROVIDERS, startup).unwrap();
        let request = SignatureStatusesRequestV1::new(91, signature).unwrap();
        let request_json = request.encode_json_v1();
        let error = if succeeded {
            serde_json::Value::Null
        } else {
            json!({"InstructionError": [0, "Custom"]})
        };
        let status = if succeeded {
            json!({"Ok": null})
        } else {
            json!({"Err": error.clone()})
        };
        let response = response_v1(
            request.request_id(),
            json!({
                "context": {"slot": landed_slot + 3},
                "value": [{
                    "slot": landed_slot,
                    "confirmations": null,
                    "err": error,
                    "confirmationStatus": "finalized",
                    "status": status
                }]
            }),
        );
        let agreement = quorum
            .agree_signature_status_v1(&request, exchanges(&request_json, &response))
            .unwrap();
        match compose_relayer_signature_status_v1(startup, signature, &request, &agreement, None)
            .unwrap()
        {
            ComposedRelayerSignatureStatusV1::FinalizedBlockJoinRequired(hint)
            | ComposedRelayerSignatureStatusV1::FinalizedFailureJoinRequired(hint) => hint,
            ComposedRelayerSignatureStatusV1::CoordinatorReady(_) => {
                panic!("finalized status cannot be coordinator-ready")
            }
        }
    }

    #[test]
    fn exact_successful_finality_join_returns_only_getter_visible_observation() {
        let (startup, plan, ingest) = agreed_block_v1(41, LANDED_SLOT, SIGNATURE);
        let hint = finalized_hint_v1(&startup, SIGNATURE, LANDED_SLOT, true);
        let status_evidence = *hint.execution_result_sha256();
        let block_binding = *plan.block_request_binding_sha256();
        match join_successful_relayer_finality_v1(&startup, hint, &plan, ingest).unwrap() {
            RelayerSignatureObservationV1::Finalized(observation) => {
                assert_eq!(observation.execution().point().slot(), LANDED_SLOT);
                assert_eq!(observation.execution().transaction_signature(), &SIGNATURE);
                assert_eq!(
                    observation.provider_set_digest(),
                    startup.provider_set_digest()
                );
                assert_eq!(observation.status_evidence_sha256(), &status_evidence);
                assert_eq!(observation.block_request_binding_sha256(), &block_binding);
                assert!(observation.root_request_binding_sha256().is_none());
                assert_eq!(
                    observation.indexed_pool().advance(),
                    FinalizedBlockAdvanceV1::Advanced
                );
            }
            _ => panic!("successful join must return a finalized observation"),
        }
    }

    #[test]
    fn finality_join_rejects_receipt_binding_slot_signature_and_failure_mismatches() {
        let (startup, plan, _) = agreed_block_v1(41, LANDED_SLOT, SIGNATURE);
        let (_, _, wrong_binding_ingest) = agreed_block_v1(42, LANDED_SLOT, SIGNATURE);
        let hint = finalized_hint_v1(&startup, SIGNATURE, LANDED_SLOT, true);
        assert_eq!(
            join_successful_relayer_finality_v1(&startup, hint, &plan, wrong_binding_ingest,).err(),
            Some(RelayerFinalityJoinErrorV1::BlockRequestBindingMismatch)
        );

        let (_, _, ingest) = agreed_block_v1(41, LANDED_SLOT, SIGNATURE);
        let wrong_startup = OperatorStartupReceiptV1::test_only_v1(
            [0x99; 32],
            *startup.provider_set_digest(),
            startup.checkpoint(),
        );
        assert_eq!(
            join_successful_relayer_finality_v1(&wrong_startup, hint, &plan, ingest).err(),
            Some(RelayerFinalityJoinErrorV1::StartupReceiptMismatch)
        );

        let (_, _, ingest) = agreed_block_v1(41, LANDED_SLOT, SIGNATURE);
        let wrong_slot_hint = finalized_hint_v1(&startup, SIGNATURE, LANDED_SLOT + 1, true);
        assert_eq!(
            join_successful_relayer_finality_v1(&startup, wrong_slot_hint, &plan, ingest).err(),
            Some(RelayerFinalityJoinErrorV1::RequestedLandedSlotMismatch)
        );

        let (_, _, ingest) = agreed_block_v1(41, LANDED_SLOT, SIGNATURE);
        let wrong_context_hint = finalized_hint_v1(&startup, SIGNATURE, LANDED_SLOT, true)
            .test_only_with_context_slot_v1(LANDED_SLOT - 1);
        assert_eq!(
            join_successful_relayer_finality_v1(&startup, wrong_context_hint, &plan, ingest).err(),
            Some(RelayerFinalityJoinErrorV1::StatusContextBeforeLanded)
        );

        let (_, _, ingest) = agreed_block_v1(41, LANDED_SLOT, SIGNATURE);
        let wrong_signature_hint = finalized_hint_v1(&startup, [0x56; 64], LANDED_SLOT, true);
        assert_eq!(
            join_successful_relayer_finality_v1(&startup, wrong_signature_hint, &plan, ingest,)
                .err(),
            Some(RelayerFinalityJoinErrorV1::TransactionExecution(
                RpcJsonErrorV1::TransactionNotFound
            ))
        );

        let (_, _, ingest) = agreed_block_v1(41, LANDED_SLOT, SIGNATURE);
        let failed_hint = finalized_hint_v1(&startup, SIGNATURE, LANDED_SLOT, false);
        assert_eq!(
            join_successful_relayer_finality_v1(&startup, failed_hint, &plan, ingest).err(),
            Some(RelayerFinalityJoinErrorV1::FinalizedFailureJoinRequired)
        );
    }
}
