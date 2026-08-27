//! Two-provider agreement for finalized Pool block and root-page ingestion.
//!
//! The caller must authenticate each transport response as coming from the
//! supplied provider identity. This module then binds the exact request bytes,
//! decodes both responses independently, requires equality of every field the
//! indexer consumes, and exposes only the agreed, constructor-sealed result.

use sha2::{Digest as _, Sha256};

use crate::{
    finalized_indexer::FinalizedBlockIngestResultV1,
    operator_startup::OperatorStartupReceiptV1,
    relayer_rpc_quorum::{ExactProviderRpcExchangeV1, ExactTwoProviderRelayerRpcV1},
    rpc_adapter::DepositRpcBindingV1,
    rpc_json::{
        ingest_finalized_rpc_json_plan_v1, plan_finalized_get_block_json_v1,
        root_page_responses_semantically_equal_v1, FinalizedGetBlockRequestV1,
        FinalizedRootPagesRequestV1, FinalizedRpcJsonPlanV1, RpcJsonErrorV1,
    },
    scan_state::{LocalOwnerKeyStoreV1, ScanStateV1},
    ViewingSecretKeyV1,
};

pub const FINALIZED_RPC_QUORUM_REQUEST_DOMAIN_V1: &[u8] =
    b"aspis:pool-v1:finalized-rpc-two-provider-request:sha256:v1";

const GET_BLOCK_ENDPOINT_V1: u8 = 1;
const ROOT_PAGES_ENDPOINT_V1: u8 = 2;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FinalizedRpcQuorumErrorV1 {
    BlockBeforeStartupCheckpoint,
    WrongProviderOrder {
        provider_index: u8,
    },
    WrongRequestBytes {
        provider_index: u8,
    },
    ProviderBlock {
        provider_index: u8,
        error: RpcJsonErrorV1,
    },
    ProviderDisagreement,
    RootRequestPresenceMismatch,
    RootRequestPlanMismatch,
    RootResponse(RpcJsonErrorV1),
    Indexer(RpcJsonErrorV1),
    LengthOverflow,
}

/// A block plan decoded independently and agreed by the exact startup-pinned
/// provider pair. Its fields are private, so callers cannot stamp an
/// arbitrary single-provider plan with a quorum identity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgreedFinalizedRpcJsonPlanV1 {
    provider_ids: [[u8; 32]; 2],
    provider_set_digest: [u8; 32],
    startup_receipt_digest: [u8; 32],
    startup_checkpoint_slot: u64,
    block_request_binding_sha256: [u8; 32],
    plan: FinalizedRpcJsonPlanV1,
}

impl AgreedFinalizedRpcJsonPlanV1 {
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

    pub fn block_request_binding_sha256(&self) -> &[u8; 32] {
        &self.block_request_binding_sha256
    }

    pub fn plan(&self) -> &FinalizedRpcJsonPlanV1 {
        &self.plan
    }
}

/// Two-provider evidence that one exact finalized `getBlock(slot)` request
/// returned JSON `result: null` at both providers. This authenticates the null
/// response, but does not by itself distinguish a skipped slot from temporary
/// or archival unavailability; retry/skip policy stays with the backfill
/// scheduler. The fields are private so callers cannot manufacture evidence or
/// associate it with different request bytes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgreedFinalizedNullSlotV1 {
    provider_ids: [[u8; 32]; 2],
    provider_set_digest: [u8; 32],
    startup_receipt_digest: [u8; 32],
    startup_checkpoint_slot: u64,
    request_id: u64,
    slot: u64,
    block_request_binding_sha256: [u8; 32],
}

impl AgreedFinalizedNullSlotV1 {
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

    pub fn slot(&self) -> u64 {
        self.slot
    }

    pub fn block_request_binding_sha256(&self) -> &[u8; 32] {
        &self.block_request_binding_sha256
    }
}

/// Complete authenticated outcome of one exact finalized block request.
/// `Null` is emitted only when both startup-pinned providers independently
/// decode the same request as JSON `result: null`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AgreedFinalizedSlotPlanV1 {
    Block(AgreedFinalizedRpcJsonPlanV1),
    Null(AgreedFinalizedNullSlotV1),
}

/// Optional exact two-provider root-page exchange for the bindings derived
/// from an agreed block plan.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FinalizedRootPagesQuorumInputV1<'a> {
    request: &'a FinalizedRootPagesRequestV1,
    exchanges: [ExactProviderRpcExchangeV1<'a>; 2],
}

impl<'a> FinalizedRootPagesQuorumInputV1<'a> {
    pub fn new(
        request: &'a FinalizedRootPagesRequestV1,
        exchanges: [ExactProviderRpcExchangeV1<'a>; 2],
    ) -> Self {
        Self { request, exchanges }
    }
}

/// Constructor-sealed result of one agreed block and, when required, one
/// agreed root-page batch. This is the only object a production finality join
/// needs to turn into a coordinator observation.
pub struct AgreedFinalizedBlockIngestV1 {
    provider_set_digest: [u8; 32],
    startup_receipt_digest: [u8; 32],
    block_request_binding_sha256: [u8; 32],
    root_request_binding_sha256: Option<[u8; 32]>,
    result: FinalizedBlockIngestResultV1,
}

impl AgreedFinalizedBlockIngestV1 {
    pub fn provider_set_digest(&self) -> &[u8; 32] {
        &self.provider_set_digest
    }

    pub fn startup_receipt_digest(&self) -> &[u8; 32] {
        &self.startup_receipt_digest
    }

    pub fn block_request_binding_sha256(&self) -> &[u8; 32] {
        &self.block_request_binding_sha256
    }

    pub fn root_request_binding_sha256(&self) -> Option<&[u8; 32]> {
        self.root_request_binding_sha256.as_ref()
    }

    pub fn result(&self) -> &FinalizedBlockIngestResultV1 {
        &self.result
    }

    pub fn into_result(self) -> FinalizedBlockIngestResultV1 {
        self.result
    }
}

pub fn agree_finalized_get_block_plan_v1(
    quorum: &ExactTwoProviderRelayerRpcV1,
    state: &ScanStateV1,
    binding: &DepositRpcBindingV1,
    request: FinalizedGetBlockRequestV1,
    exchanges: [ExactProviderRpcExchangeV1<'_>; 2],
) -> Result<AgreedFinalizedRpcJsonPlanV1, FinalizedRpcQuorumErrorV1> {
    match agree_finalized_get_block_outcome_v1(quorum, state, binding, request, exchanges)? {
        AgreedFinalizedSlotPlanV1::Block(plan) => Ok(plan),
        AgreedFinalizedSlotPlanV1::Null(_) => Err(FinalizedRpcQuorumErrorV1::ProviderBlock {
            provider_index: 0,
            error: RpcJsonErrorV1::SkippedBlock,
        }),
    }
}

/// Agree either a non-null finalized block plan or an authenticated null-slot
/// result.
/// A null/non-null split is provider disagreement, never permission to omit a
/// slot from backfill. Malformed responses remain attributed to the exact
/// provider index.
pub fn agree_finalized_get_block_outcome_v1(
    quorum: &ExactTwoProviderRelayerRpcV1,
    state: &ScanStateV1,
    binding: &DepositRpcBindingV1,
    request: FinalizedGetBlockRequestV1,
    exchanges: [ExactProviderRpcExchangeV1<'_>; 2],
) -> Result<AgreedFinalizedSlotPlanV1, FinalizedRpcQuorumErrorV1> {
    if request.slot() < quorum.startup_checkpoint_slot() {
        return Err(FinalizedRpcQuorumErrorV1::BlockBeforeStartupCheckpoint);
    }
    let request_json = request.encode_json_v1();
    validate_exchanges_v1(quorum.provider_ids(), &request_json, &exchanges)?;
    let first =
        plan_finalized_get_block_json_v1(state, binding, request, exchanges[0].response_json());
    let second =
        plan_finalized_get_block_json_v1(state, binding, request, exchanges[1].response_json());
    let block_request_binding_sha256 = request_binding_digest_v1(
        GET_BLOCK_ENDPOINT_V1,
        request.request_id(),
        request.slot(),
        &request_json,
    )?;

    match (first, second) {
        (Ok(first), Ok(second)) => {
            if first != second {
                return Err(FinalizedRpcQuorumErrorV1::ProviderDisagreement);
            }
            Ok(AgreedFinalizedSlotPlanV1::Block(
                AgreedFinalizedRpcJsonPlanV1 {
                    provider_ids: *quorum.provider_ids(),
                    provider_set_digest: *quorum.provider_set_digest(),
                    startup_receipt_digest: *quorum.startup_receipt_digest(),
                    startup_checkpoint_slot: quorum.startup_checkpoint_slot(),
                    block_request_binding_sha256,
                    plan: first,
                },
            ))
        }
        (Err(RpcJsonErrorV1::SkippedBlock), Err(RpcJsonErrorV1::SkippedBlock)) => {
            Ok(AgreedFinalizedSlotPlanV1::Null(AgreedFinalizedNullSlotV1 {
                provider_ids: *quorum.provider_ids(),
                provider_set_digest: *quorum.provider_set_digest(),
                startup_receipt_digest: *quorum.startup_receipt_digest(),
                startup_checkpoint_slot: quorum.startup_checkpoint_slot(),
                request_id: request.request_id(),
                slot: request.slot(),
                block_request_binding_sha256,
            }))
        }
        (Ok(_), Err(RpcJsonErrorV1::SkippedBlock)) | (Err(RpcJsonErrorV1::SkippedBlock), Ok(_)) => {
            Err(FinalizedRpcQuorumErrorV1::ProviderDisagreement)
        }
        (Err(error), _) => Err(FinalizedRpcQuorumErrorV1::ProviderBlock {
            provider_index: 0,
            error,
        }),
        (_, Err(error)) => Err(FinalizedRpcQuorumErrorV1::ProviderBlock {
            provider_index: 1,
            error,
        }),
    }
}

#[allow(clippy::too_many_arguments)]
pub fn ingest_agreed_finalized_rpc_json_plan_v1(
    state: &mut ScanStateV1,
    binding: &DepositRpcBindingV1,
    agreed: &AgreedFinalizedRpcJsonPlanV1,
    roots: Option<FinalizedRootPagesQuorumInputV1<'_>>,
    viewing_secret: &ViewingSecretKeyV1,
    local_keys: &impl LocalOwnerKeyStoreV1,
) -> Result<AgreedFinalizedBlockIngestV1, FinalizedRpcQuorumErrorV1> {
    let expected_roots = agreed
        .plan
        .root_pages_request_v1(roots.as_ref().map_or(1, |input| input.request.request_id()))
        .map_err(FinalizedRpcQuorumErrorV1::Indexer)?;
    if expected_roots.is_some() != roots.is_some() {
        return Err(FinalizedRpcQuorumErrorV1::RootRequestPresenceMismatch);
    }

    let (root_request, root_response, root_request_binding_sha256) =
        match (expected_roots.as_ref(), roots.as_ref()) {
            (None, None) => (None, None, None),
            (Some(expected), Some(input)) => {
                if expected != input.request {
                    return Err(FinalizedRpcQuorumErrorV1::RootRequestPlanMismatch);
                }
                let request_json = input.request.encode_json_v1();
                validate_exchanges_v1(&agreed.provider_ids, &request_json, &input.exchanges)?;
                let equal = root_page_responses_semantically_equal_v1(
                    input.request,
                    input.exchanges[0].response_json(),
                    input.exchanges[1].response_json(),
                )
                .map_err(FinalizedRpcQuorumErrorV1::RootResponse)?;
                if !equal {
                    return Err(FinalizedRpcQuorumErrorV1::ProviderDisagreement);
                }
                (
                    Some(input.request),
                    Some(input.exchanges[0].response_json()),
                    Some(request_binding_digest_v1(
                        ROOT_PAGES_ENDPOINT_V1,
                        input.request.request_id(),
                        input.request.min_context_slot(),
                        &request_json,
                    )?),
                )
            }
            _ => return Err(FinalizedRpcQuorumErrorV1::RootRequestPresenceMismatch),
        };

    let result = ingest_finalized_rpc_json_plan_v1(
        state,
        binding,
        &agreed.plan,
        root_request,
        root_response,
        viewing_secret,
        local_keys,
    )
    .map_err(FinalizedRpcQuorumErrorV1::Indexer)?;
    Ok(AgreedFinalizedBlockIngestV1 {
        provider_set_digest: agreed.provider_set_digest,
        startup_receipt_digest: agreed.startup_receipt_digest,
        block_request_binding_sha256: agreed.block_request_binding_sha256,
        root_request_binding_sha256,
        result,
    })
}

fn validate_exchanges_v1(
    provider_ids: &[[u8; 32]; 2],
    expected_request_json: &[u8],
    exchanges: &[ExactProviderRpcExchangeV1<'_>; 2],
) -> Result<(), FinalizedRpcQuorumErrorV1> {
    for (provider_index, exchange) in exchanges.iter().enumerate() {
        if exchange.provider_id() != &provider_ids[provider_index] {
            return Err(FinalizedRpcQuorumErrorV1::WrongProviderOrder {
                provider_index: provider_index as u8,
            });
        }
        if exchange.request_json() != expected_request_json {
            return Err(FinalizedRpcQuorumErrorV1::WrongRequestBytes {
                provider_index: provider_index as u8,
            });
        }
    }
    Ok(())
}

fn request_binding_digest_v1(
    endpoint: u8,
    request_id: u64,
    context_slot: u64,
    request_json: &[u8],
) -> Result<[u8; 32], FinalizedRpcQuorumErrorV1> {
    let length =
        u64::try_from(request_json.len()).map_err(|_| FinalizedRpcQuorumErrorV1::LengthOverflow)?;
    let mut hasher = Sha256::new();
    hasher.update(FINALIZED_RPC_QUORUM_REQUEST_DOMAIN_V1);
    hasher.update([endpoint]);
    hasher.update(request_id.to_le_bytes());
    hasher.update(context_slot.to_le_bytes());
    hasher.update(length.to_le_bytes());
    hasher.update(request_json);
    Ok(hasher.finalize().into())
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
        operator_startup::{provider_set_digest_v1, FinalizedReleaseCheckpointV1},
        scan_state::{DepositScanIdentityV1, FinalizedChainPointV1},
    };

    const PROVIDERS: [[u8; 32]; 2] = [[1u8; 32], [2u8; 32]];
    const STARTUP_SLOT: u64 = 100;

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
        (state, binding, viewing, startup)
    }

    fn empty_block_response(request_id: u64, blockhash: [u8; 32]) -> Vec<u8> {
        serde_json::to_vec(&json!({
            "jsonrpc": "2.0",
            "id": request_id,
            "result": {
                "blockhash": encode_base58(&blockhash),
                "previousBlockhash": encode_base58(&[0xa0; 32]),
                "parentSlot": STARTUP_SLOT,
                "transactions": []
            }
        }))
        .unwrap()
    }

    fn exchanges<'a>(
        request: &'a [u8],
        first: &'a [u8],
        second: &'a [u8],
    ) -> [ExactProviderRpcExchangeV1<'a>; 2] {
        [
            ExactProviderRpcExchangeV1::new(PROVIDERS[0], request, first),
            ExactProviderRpcExchangeV1::new(PROVIDERS[1], request, second),
        ]
    }

    #[test]
    fn finalized_block_requires_exact_provider_request_and_semantic_agreement() {
        let (state, binding, _, startup) = fixture();
        let quorum = ExactTwoProviderRelayerRpcV1::new(PROVIDERS, &startup).unwrap();
        let request = FinalizedGetBlockRequestV1::new(7, STARTUP_SLOT + 1).unwrap();
        let request_json = request.encode_json_v1();
        let first = empty_block_response(7, [0xa1; 32]);
        let second_value: serde_json::Value = serde_json::from_slice(&first).unwrap();
        let second = serde_json::to_vec_pretty(&second_value).unwrap();
        let agreed = agree_finalized_get_block_plan_v1(
            &quorum,
            &state,
            &binding,
            request,
            exchanges(&request_json, &first, &second),
        )
        .unwrap();
        assert_eq!(agreed.provider_set_digest(), startup.provider_set_digest());
        assert_ne!(agreed.block_request_binding_sha256(), &[0u8; 32]);

        let different = empty_block_response(7, [0xa2; 32]);
        assert_eq!(
            agree_finalized_get_block_plan_v1(
                &quorum,
                &state,
                &binding,
                request,
                exchanges(&request_json, &first, &different),
            ),
            Err(FinalizedRpcQuorumErrorV1::ProviderDisagreement)
        );
        let wrong_request = b"{}";
        assert_eq!(
            agree_finalized_get_block_plan_v1(
                &quorum,
                &state,
                &binding,
                request,
                exchanges(wrong_request, &first, &first),
            ),
            Err(FinalizedRpcQuorumErrorV1::WrongRequestBytes { provider_index: 0 })
        );
    }

    #[test]
    fn finalized_null_slot_requires_two_provider_agreement() {
        let (state, binding, _, startup) = fixture();
        let quorum = ExactTwoProviderRelayerRpcV1::new(PROVIDERS, &startup).unwrap();
        let request = FinalizedGetBlockRequestV1::new(9, STARTUP_SLOT + 3).unwrap();
        let request_json = request.encode_json_v1();
        let compact = br#"{"jsonrpc":"2.0","id":9,"result":null}"#;
        let pretty = br#"{
          "jsonrpc": "2.0",
          "id": 9,
          "result": null
        }"#;

        let agreed = agree_finalized_get_block_outcome_v1(
            &quorum,
            &state,
            &binding,
            request,
            exchanges(&request_json, compact, pretty),
        )
        .unwrap();
        let AgreedFinalizedSlotPlanV1::Null(null) = agreed else {
            panic!("two null finalized responses must produce a null-slot result")
        };
        assert_eq!(null.provider_ids(), &PROVIDERS);
        assert_eq!(null.provider_set_digest(), startup.provider_set_digest());
        assert_eq!(null.startup_receipt_digest(), startup.receipt_digest());
        assert_eq!(null.startup_checkpoint_slot(), STARTUP_SLOT);
        assert_eq!(null.request_id(), 9);
        assert_eq!(null.slot(), STARTUP_SLOT + 3);
        assert_ne!(null.block_request_binding_sha256(), &[0u8; 32]);

        assert_eq!(
            agree_finalized_get_block_plan_v1(
                &quorum,
                &state,
                &binding,
                request,
                exchanges(&request_json, compact, pretty),
            ),
            Err(FinalizedRpcQuorumErrorV1::ProviderBlock {
                provider_index: 0,
                error: RpcJsonErrorV1::SkippedBlock,
            })
        );
    }

    #[test]
    fn finalized_null_block_split_is_provider_disagreement() {
        let (state, binding, _, startup) = fixture();
        let quorum = ExactTwoProviderRelayerRpcV1::new(PROVIDERS, &startup).unwrap();
        let request = FinalizedGetBlockRequestV1::new(10, STARTUP_SLOT + 1).unwrap();
        let request_json = request.encode_json_v1();
        let skipped = br#"{"jsonrpc":"2.0","id":10,"result":null}"#;
        let block = empty_block_response(10, [0xa1; 32]);

        assert_eq!(
            agree_finalized_get_block_outcome_v1(
                &quorum,
                &state,
                &binding,
                request,
                exchanges(&request_json, skipped, &block),
            ),
            Err(FinalizedRpcQuorumErrorV1::ProviderDisagreement)
        );
        assert_eq!(
            agree_finalized_get_block_outcome_v1(
                &quorum,
                &state,
                &binding,
                request,
                exchanges(&request_json, &block, skipped),
            ),
            Err(FinalizedRpcQuorumErrorV1::ProviderDisagreement)
        );
    }

    #[test]
    fn agreed_empty_block_ingests_without_unrequested_root_pages() {
        let (mut state, binding, viewing, startup) = fixture();
        let quorum = ExactTwoProviderRelayerRpcV1::new(PROVIDERS, &startup).unwrap();
        let request = FinalizedGetBlockRequestV1::new(8, STARTUP_SLOT + 1).unwrap();
        let request_json = request.encode_json_v1();
        let response = empty_block_response(8, [0xa1; 32]);
        let agreed = agree_finalized_get_block_plan_v1(
            &quorum,
            &state,
            &binding,
            request,
            exchanges(&request_json, &response, &response),
        )
        .unwrap();
        let ingested = ingest_agreed_finalized_rpc_json_plan_v1(
            &mut state, &binding, &agreed, None, &viewing, &EmptyKeys,
        )
        .unwrap();
        assert_eq!(
            ingested.provider_set_digest(),
            startup.provider_set_digest()
        );
        assert_eq!(
            ingested.result().advance(),
            crate::scan_state::FinalizedBlockAdvanceV1::Advanced
        );
        assert!(ingested.root_request_binding_sha256().is_none());
    }
}
