//! Default-off Solana transaction-v1 plumbing for the eight-lane Pool.
//!
//! The 4,096-byte envelope is available only to transaction v1 (SIMD-0385).
//! Legacy and v0 remain limited to 1,232 bytes. V1 has no address lookup
//! tables and carries compute, loaded-account-data, heap and priority-fee
//! requests in `TransactionConfig`, not ComputeBudget instructions.
//!
//! This module constructs placeholder-signature wires for sizing, simulation
//! and wallet review only. It owns no keys and never signs or submits.

use std::{collections::BTreeSet, io::Read, time::Duration};

use aspis_pool::{
    pool_v1_nullifier_marker_address, pool_v1_pair_forest_checkpoint_address,
    pool_v1_pair_forest_lane_address, pool_v1_pair_forest_lane_root_page_address,
    pool_v1_pair_forest_master_address, pool_v1_vault_authority_address,
    pool_v1_vault_token_account_address, LEGACY_SPL_TOKEN_PROGRAM_ID,
};
use aspis_statement::{
    encode_digest_canonical,
    pool_v1::{
        encode_pool_v1_pair_forest_terminal_request_v1, pool_v1_pair_forest_output_lane_v1,
        root_history_location, PoolV1PairForestLaneStateV1, PoolV1PairForestMasterV1,
        PoolV1PairForestTerminalPaymentV1, PoolV1PairForestTerminalRequestV1,
        POOL_V1_PAIR_CAPACITY, POOL_V1_PAIR_FOREST_TERMINAL_VERSION,
    },
};
use base64::{engine::general_purpose::STANDARD as BASE64_STANDARD, Engine as _};
use solana_address_v1::Address;
use solana_hash_v1::Hash as V1Hash;
use solana_instruction_v1::{AccountMeta as V1AccountMeta, Instruction as V1Instruction};
use solana_message::{AddressLookupTableAccount, VersionedMessage as LegacyVersionedMessage};
use solana_message_v1::{v1, VersionedMessage as V1VersionedMessage};
use solana_program::{
    instruction::{AccountMeta, Instruction},
    pubkey::Pubkey,
};
use solana_signature_v1::Signature as V1Signature;
use solana_transaction::versioned::VersionedTransaction as LegacyVersionedTransaction;
use solana_transaction_v1::versioned::VersionedTransaction as V1VersionedTransaction;

use crate::lane_forest_client_v2::PairForestSpendProfileSelectionV2;

pub const SOLANA_LEGACY_V0_TRANSACTION_MAX_BYTES_V2: usize = 1_232;
pub const SOLANA_V1_TRANSACTION_MAX_BYTES_V2: usize = 4_096;
pub const SOLANA_V1_MAX_SIGNATURES_V2: usize = 12;
pub const SOLANA_V1_MAX_ADDRESSES_V2: usize = 64;
pub const SOLANA_V1_MAX_INSTRUCTIONS_V2: usize = 64;
pub const SOLANA_V1_VERSION_PREFIX_V2: u8 = 0x81;
pub const SOLANA_TX_V1_FEATURE_ID_V2: &str = "txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL";
pub const SOLANA_DEVNET_GENESIS_HASH_V2: &str = "EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG";
pub const SOLANA_PUBLIC_DEVNET_RPC_V2: &str = "https://api.devnet.solana.com";
const SOLANA_FEATURE_PROGRAM_ID_V2: &str = "Feature111111111111111111111111111111111111";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PairForestTransactionV1ErrorV2 {
    UnpinnedProgram,
    ZeroAccount,
    AccountAlias,
    WrongMaster,
    WrongLane,
    WrongProfile,
    WrongRequest,
    TreeFull,
    AddressLookupTableForbidden,
    ComputeBudgetInstructionForbidden,
    InvalidComputeLimit,
    InvalidLoadedAccountsLimit,
    InvalidHeapSize,
    TooManySignatures,
    TooManyAddresses,
    TooManyInstructions,
    InstructionDataTooLarge,
    CompileFailed,
    SanitizeFailed,
    SerializationFailed,
    TransactionTooLarge,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PairForestV1TransactionConfigV2 {
    /// Total priority fee in lamports, not micro-lamports per CU.
    pub priority_fee_lamports: u64,
    pub compute_unit_limit: u32,
    pub loaded_accounts_data_size_limit: u32,
    pub heap_size: u32,
}

impl PairForestV1TransactionConfigV2 {
    pub fn validate_v2(self) -> Result<(), PairForestTransactionV1ErrorV2> {
        if self.compute_unit_limit == 0 || self.compute_unit_limit > 1_400_000 {
            return Err(PairForestTransactionV1ErrorV2::InvalidComputeLimit);
        }
        if self.loaded_accounts_data_size_limit == 0
            || self.loaded_accounts_data_size_limit > 64 * 1024 * 1024
        {
            return Err(PairForestTransactionV1ErrorV2::InvalidLoadedAccountsLimit);
        }
        if !(32 * 1024..=256 * 1024).contains(&self.heap_size) || self.heap_size % 1024 != 0 {
            return Err(PairForestTransactionV1ErrorV2::InvalidHeapSize);
        }
        Ok(())
    }

    fn as_solana_v1(self) -> v1::TransactionConfig {
        v1::TransactionConfig::empty()
            .with_priority_fee(self.priority_fee_lamports)
            .with_compute_unit_limit(self.compute_unit_limit)
            .with_loaded_accounts_data_size_limit(self.loaded_accounts_data_size_limit)
            .with_heap_size(self.heap_size)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactUnsignedPairForestV1TransactionV2 {
    signable_message: Vec<u8>,
    placeholder_signature_wire: Vec<u8>,
    required_signatures: u8,
    inline_addresses: u8,
    instruction_count: u8,
    config: PairForestV1TransactionConfigV2,
}

impl ExactUnsignedPairForestV1TransactionV2 {
    pub fn signable_message_v2(&self) -> &[u8] {
        &self.signable_message
    }

    pub fn placeholder_signature_wire_v2(&self) -> &[u8] {
        &self.placeholder_signature_wire
    }

    pub fn serialized_wire_bytes_v2(&self) -> usize {
        self.placeholder_signature_wire.len()
    }

    pub fn required_signatures_v2(&self) -> u8 {
        self.required_signatures
    }

    pub fn inline_addresses_v2(&self) -> u8 {
        self.inline_addresses
    }

    pub fn instruction_count_v2(&self) -> u8 {
        self.instruction_count
    }

    pub fn config_v2(&self) -> PairForestV1TransactionConfigV2 {
        self.config
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LegacyV0SizeComparisonV2 {
    pub serialized_wire_bytes: usize,
    pub legacy_v0_limit_bytes: usize,
    pub eligible_for_four_kib: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TxV1CapabilityProbeErrorV2 {
    Http,
    ResponseTooLarge,
    Rpc,
    MalformedResponse,
    WrongGenesis,
    WrongFeatureOwner,
    WrongFeatureData,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicDevnetTxV1CapabilityV2 {
    pub genesis_hash: String,
    pub solana_core: String,
    pub feature_set: u64,
    pub finalized_slot: u64,
    pub feature_account_present: bool,
    pub activation_slot: Option<u64>,
    pub max_transaction_version_one_rpc_supported: bool,
}

impl PublicDevnetTxV1CapabilityV2 {
    /// A caller may simulate v1 only after all cluster-side gates are true.
    pub fn execution_activated_v2(&self) -> bool {
        self.genesis_hash == SOLANA_DEVNET_GENESIS_HASH_V2
            && self.activation_slot.is_some()
            && self.max_transaction_version_one_rpc_supported
    }
}

fn rpc_result_v2(
    client: &reqwest::blocking::Client,
    method: &str,
    params: serde_json::Value,
) -> Result<serde_json::Value, TxV1CapabilityProbeErrorV2> {
    let request = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 1,
        "method": method,
        "params": params,
    });
    let mut response = client
        .post(SOLANA_PUBLIC_DEVNET_RPC_V2)
        .header(reqwest::header::CONTENT_TYPE, "application/json")
        .body(request.to_string())
        .send()
        .map_err(|_| TxV1CapabilityProbeErrorV2::Http)?
        .error_for_status()
        .map_err(|_| TxV1CapabilityProbeErrorV2::Http)?;
    const MAX_RESPONSE_BYTES: u64 = 1024 * 1024;
    if response
        .content_length()
        .is_some_and(|length| length > MAX_RESPONSE_BYTES)
    {
        return Err(TxV1CapabilityProbeErrorV2::ResponseTooLarge);
    }
    let mut response_bytes = Vec::new();
    response
        .by_ref()
        .take(MAX_RESPONSE_BYTES + 1)
        .read_to_end(&mut response_bytes)
        .map_err(|_| TxV1CapabilityProbeErrorV2::Http)?;
    if response_bytes.len() as u64 > MAX_RESPONSE_BYTES {
        return Err(TxV1CapabilityProbeErrorV2::ResponseTooLarge);
    }
    let response = serde_json::from_slice::<serde_json::Value>(&response_bytes)
        .map_err(|_| TxV1CapabilityProbeErrorV2::MalformedResponse)?;
    if response.get("error").is_some() {
        return Err(TxV1CapabilityProbeErrorV2::Rpc);
    }
    response
        .get("result")
        .cloned()
        .ok_or(TxV1CapabilityProbeErrorV2::MalformedResponse)
}

fn feature_activation_v2(
    account: &serde_json::Value,
) -> Result<(bool, Option<u64>), TxV1CapabilityProbeErrorV2> {
    if account.is_null() {
        return Ok((false, None));
    }
    if account.get("owner").and_then(serde_json::Value::as_str)
        != Some(SOLANA_FEATURE_PROGRAM_ID_V2)
    {
        return Err(TxV1CapabilityProbeErrorV2::WrongFeatureOwner);
    }
    let data = account
        .get("data")
        .and_then(serde_json::Value::as_array)
        .ok_or(TxV1CapabilityProbeErrorV2::WrongFeatureData)?;
    if data.get(1).and_then(serde_json::Value::as_str) != Some("base64") {
        return Err(TxV1CapabilityProbeErrorV2::WrongFeatureData);
    }
    let bytes = BASE64_STANDARD
        .decode(
            data.first()
                .and_then(serde_json::Value::as_str)
                .ok_or(TxV1CapabilityProbeErrorV2::WrongFeatureData)?,
        )
        .map_err(|_| TxV1CapabilityProbeErrorV2::WrongFeatureData)?;
    match bytes.as_slice() {
        [0] => Ok((true, None)),
        [1, slot @ ..] if slot.len() == 8 => {
            let mut encoded = [0u8; 8];
            encoded.copy_from_slice(slot);
            Ok((true, Some(u64::from_le_bytes(encoded))))
        }
        _ => Err(TxV1CapabilityProbeErrorV2::WrongFeatureData),
    }
}

/// Probe the fixed public-devnet endpoint without signing, simulating or
/// submitting. The method allowlist is hard-coded to read-only JSON-RPC calls.
pub fn probe_public_devnet_tx_v1_capability_v2(
) -> Result<PublicDevnetTxV1CapabilityV2, TxV1CapabilityProbeErrorV2> {
    let client = reqwest::blocking::Client::builder()
        .timeout(Duration::from_secs(15))
        .build()
        .map_err(|_| TxV1CapabilityProbeErrorV2::Http)?;
    let genesis_hash = rpc_result_v2(&client, "getGenesisHash", serde_json::json!([]))?
        .as_str()
        .ok_or(TxV1CapabilityProbeErrorV2::MalformedResponse)?
        .to_owned();
    if genesis_hash != SOLANA_DEVNET_GENESIS_HASH_V2 {
        return Err(TxV1CapabilityProbeErrorV2::WrongGenesis);
    }
    let version = rpc_result_v2(&client, "getVersion", serde_json::json!([]))?;
    let solana_core = version
        .get("solana-core")
        .and_then(serde_json::Value::as_str)
        .ok_or(TxV1CapabilityProbeErrorV2::MalformedResponse)?
        .to_owned();
    let feature_set = version
        .get("feature-set")
        .and_then(serde_json::Value::as_u64)
        .ok_or(TxV1CapabilityProbeErrorV2::MalformedResponse)?;
    let finalized_slot = rpc_result_v2(
        &client,
        "getSlot",
        serde_json::json!([{ "commitment": "finalized" }]),
    )?
    .as_u64()
    .ok_or(TxV1CapabilityProbeErrorV2::MalformedResponse)?;
    let account_result = rpc_result_v2(
        &client,
        "getAccountInfo",
        serde_json::json!([
            SOLANA_TX_V1_FEATURE_ID_V2,
            { "commitment": "finalized", "encoding": "base64" }
        ]),
    )?;
    let account = account_result
        .get("value")
        .ok_or(TxV1CapabilityProbeErrorV2::MalformedResponse)?;
    let (feature_account_present, activation_slot) = feature_activation_v2(account)?;

    // `transactionDetails: none` avoids downloading transaction bodies. The
    // call still exercises the RPC parser's version-1 ceiling.
    let block_probe = rpc_result_v2(
        &client,
        "getBlock",
        serde_json::json!([
            finalized_slot.saturating_sub(32),
            {
                "commitment": "finalized",
                "transactionDetails": "none",
                "rewards": false,
                "maxSupportedTransactionVersion": 1
            }
        ]),
    );
    Ok(PublicDevnetTxV1CapabilityV2 {
        genesis_hash,
        solana_core,
        feature_set,
        finalized_slot,
        feature_account_present,
        activation_slot,
        max_transaction_version_one_rpc_supported: block_probe.is_ok(),
    })
}

fn require_unique_metas_v2(accounts: &[AccountMeta]) -> Result<(), PairForestTransactionV1ErrorV2> {
    let mut seen = BTreeSet::new();
    if accounts
        .iter()
        .all(|account| seen.insert(account.pubkey.to_bytes()))
    {
        Ok(())
    } else {
        Err(PairForestTransactionV1ErrorV2::AccountAlias)
    }
}

fn terminal_request_identity_v2(
    request: &PoolV1PairForestTerminalRequestV1,
) -> ([u8; 32], [u8; 32], u64, [u8; 32], bool) {
    match request.public {
        PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) => (
            public.pool,
            public.deployment_domain,
            public.anchor_sequence,
            [0u8; 32],
            false,
        ),
        PoolV1PairForestTerminalPaymentV1::Withdrawal(public) => (
            public.pool,
            public.deployment_domain,
            public.anchor_sequence,
            public.destination_token_account,
            true,
        ),
    }
}

/// Build the exact one-terminal `ASQ8` top-level Pool instruction.
///
/// Same-page/genesis transfer: 9 accounts. Rollover transfer: 10.
/// Withdrawal appends the exact five legacy SPL custody accounts: 14 or 15.
#[allow(clippy::too_many_arguments)]
pub fn build_pair_forest_terminal_instruction_v1_4k_v2(
    pool_program: Pubkey,
    master: &PoolV1PairForestMasterV1,
    lane: &PoolV1PairForestLaneStateV1,
    profile: PairForestSpendProfileSelectionV2,
    proof_account: Pubkey,
    request: &PoolV1PairForestTerminalRequestV1,
) -> Result<Instruction, PairForestTransactionV1ErrorV2> {
    if pool_program == Pubkey::default() {
        return Err(PairForestTransactionV1ErrorV2::UnpinnedProgram);
    }
    if proof_account == Pubkey::default() || profile.verifier_program == [0u8; 32] {
        return Err(PairForestTransactionV1ErrorV2::ZeroAccount);
    }
    let mint = Pubkey::new_from_array(master.identity.asset_mint);
    let master_address = pool_v1_pair_forest_master_address(&pool_program, &mint).0;
    if master.identity.pool != master_address.to_bytes()
        || master.identity.token_program != LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes()
    {
        return Err(PairForestTransactionV1ErrorV2::WrongMaster);
    }
    if lane.master != master.identity.pool
        || usize::from(lane.lane_id) >= 8
        || master.initialized_lane_mask & (1u8 << lane.lane_id) == 0
        || lane.tree.next_leaf_index >= POOL_V1_PAIR_CAPACITY
    {
        return Err(if lane.tree.next_leaf_index >= POOL_V1_PAIR_CAPACITY {
            PairForestTransactionV1ErrorV2::TreeFull
        } else {
            PairForestTransactionV1ErrorV2::WrongLane
        });
    }
    let expected_lane = pool_v1_pair_forest_output_lane_v1(request.public.nullifier())
        .map_err(|_| PairForestTransactionV1ErrorV2::WrongLane)?;
    if expected_lane != lane.lane_id {
        return Err(PairForestTransactionV1ErrorV2::WrongLane);
    }
    let (pool, deployment, checkpoint_sequence, destination, withdrawal) =
        terminal_request_identity_v2(request);
    let request_asset = match request.public {
        PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) => public.asset_id,
        PoolV1PairForestTerminalPaymentV1::Withdrawal(public) => public.asset_id,
    };
    if request.pool_program != pool_program.to_bytes()
        || pool != master.identity.pool
        || deployment != master.identity.deployment_domain
        || request_asset != master.identity.asset_id
        || (withdrawal && destination == [0u8; 32])
        || !master.has_checkpoint
        || checkpoint_sequence >= master.next_checkpoint_sequence
    {
        return Err(PairForestTransactionV1ErrorV2::WrongRequest);
    }
    if profile.registry_program != master.verifier_policy.registry_program
        || profile.profile_binding != request.verifier_profile
        || profile.release_binding != request.verifier_release
        || profile.statement_version != POOL_V1_PAIR_FOREST_TERMINAL_VERSION
    {
        return Err(PairForestTransactionV1ErrorV2::WrongProfile);
    }
    let registry_program = Pubkey::new_from_array(profile.registry_program);
    let registry_address =
        aspis_registry::pool_v1_verifier_registry_address(&registry_program, &master_address).0;
    let entry_address = aspis_registry::pool_v1_verifier_entry_address(
        &registry_program,
        &master_address,
        &request.verifier_profile,
        &request.verifier_release,
    )
    .0;
    if profile.registry_address != registry_address.to_bytes()
        || profile.entry_address != entry_address.to_bytes()
    {
        return Err(PairForestTransactionV1ErrorV2::WrongProfile);
    }

    let lane_address =
        pool_v1_pair_forest_lane_address(&pool_program, &master_address, lane.lane_id)
            .map_err(|_| PairForestTransactionV1ErrorV2::WrongLane)?
            .0;
    let checkpoint_address =
        pool_v1_pair_forest_checkpoint_address(&pool_program, &master_address, checkpoint_sequence)
            .0;
    let current_location = root_history_location(lane.tree.next_leaf_index);
    let next_location = root_history_location(lane.tree.next_leaf_index + 1);
    let current_page = pool_v1_pair_forest_lane_root_page_address(
        &pool_program,
        &master_address,
        lane.lane_id,
        current_location.page_number,
    )
    .map_err(|_| PairForestTransactionV1ErrorV2::WrongLane)?
    .0;
    let marker = pool_v1_nullifier_marker_address(
        &pool_program,
        &master_address,
        &encode_digest_canonical(request.public.nullifier()),
    )
    .map_err(|_| PairForestTransactionV1ErrorV2::WrongRequest)?
    .0;
    let mut accounts = vec![
        AccountMeta::new_readonly(master_address, false),
        AccountMeta::new_readonly(checkpoint_address, false),
        AccountMeta::new(lane_address, false),
    ];
    if current_location.page_number == next_location.page_number {
        accounts.push(AccountMeta::new(current_page, false));
    } else {
        let next_page = pool_v1_pair_forest_lane_root_page_address(
            &pool_program,
            &master_address,
            lane.lane_id,
            next_location.page_number,
        )
        .map_err(|_| PairForestTransactionV1ErrorV2::WrongLane)?
        .0;
        accounts.push(AccountMeta::new_readonly(current_page, false));
        accounts.push(AccountMeta::new(next_page, false));
    }
    accounts.extend([
        AccountMeta::new(marker, false),
        AccountMeta::new_readonly(registry_address, false),
        AccountMeta::new_readonly(entry_address, false),
        AccountMeta::new_readonly(Pubkey::new_from_array(profile.verifier_program), false),
        AccountMeta::new_readonly(proof_account, false),
    ]);
    if withdrawal {
        accounts.extend([
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new(
                pool_v1_vault_token_account_address(&pool_program, &master_address).0,
                false,
            ),
            AccountMeta::new(Pubkey::new_from_array(destination), false),
            AccountMeta::new_readonly(
                pool_v1_vault_authority_address(&pool_program, &master_address).0,
                false,
            ),
            AccountMeta::new_readonly(LEGACY_SPL_TOKEN_PROGRAM_ID, false),
        ]);
    }
    require_unique_metas_v2(&accounts)?;
    Ok(Instruction {
        program_id: pool_program,
        accounts,
        data: encode_pool_v1_pair_forest_terminal_request_v1(request)
            .map_err(|_| PairForestTransactionV1ErrorV2::WrongRequest)?
            .to_vec(),
    })
}

fn to_v1_instruction_v2(
    instruction: &Instruction,
) -> Result<V1Instruction, PairForestTransactionV1ErrorV2> {
    if instruction.data.len() > usize::from(u16::MAX) {
        return Err(PairForestTransactionV1ErrorV2::InstructionDataTooLarge);
    }
    Ok(V1Instruction {
        program_id: Address::from(instruction.program_id.to_bytes()),
        accounts: instruction
            .accounts
            .iter()
            .map(|meta| V1AccountMeta {
                pubkey: Address::from(meta.pubkey.to_bytes()),
                is_signer: meta.is_signer,
                is_writable: meta.is_writable,
            })
            .collect(),
        data: instruction.data.clone(),
    })
}

/// Compile one exact Pool instruction into a v1 placeholder-signature wire.
///
/// `lookup_tables` is accepted only to make accidental v0 reuse fail loudly;
/// it must be empty because transaction v1 has no ALT field.
pub fn build_exact_pair_forest_v1_transaction_v2(
    instruction: &Instruction,
    fee_payer: Pubkey,
    recent_blockhash: [u8; 32],
    config: PairForestV1TransactionConfigV2,
    lookup_tables: &[AddressLookupTableAccount],
) -> Result<ExactUnsignedPairForestV1TransactionV2, PairForestTransactionV1ErrorV2> {
    if instruction.program_id == Pubkey::default() || fee_payer == Pubkey::default() {
        return Err(PairForestTransactionV1ErrorV2::UnpinnedProgram);
    }
    if !lookup_tables.is_empty() {
        return Err(PairForestTransactionV1ErrorV2::AddressLookupTableForbidden);
    }
    if instruction.program_id == solana_sdk_ids::compute_budget::id() {
        return Err(PairForestTransactionV1ErrorV2::ComputeBudgetInstructionForbidden);
    }
    config.validate_v2()?;
    let instruction = to_v1_instruction_v2(instruction)?;
    let payer = Address::from(fee_payer.to_bytes());
    let message = v1::Message::try_compile_with_config(
        &payer,
        &[instruction],
        V1Hash::new_from_array(recent_blockhash),
        config.as_solana_v1(),
    )
    .map_err(|_| PairForestTransactionV1ErrorV2::CompileFailed)?;
    let signatures = usize::from(message.header.num_required_signatures);
    let addresses = message.account_keys.len();
    if signatures > SOLANA_V1_MAX_SIGNATURES_V2 {
        return Err(PairForestTransactionV1ErrorV2::TooManySignatures);
    }
    if addresses > SOLANA_V1_MAX_ADDRESSES_V2 {
        return Err(PairForestTransactionV1ErrorV2::TooManyAddresses);
    }
    if message.instructions.len() > SOLANA_V1_MAX_INSTRUCTIONS_V2 {
        return Err(PairForestTransactionV1ErrorV2::TooManyInstructions);
    }
    let versioned_message = V1VersionedMessage::V1(message);
    versioned_message
        .sanitize()
        .map_err(|_| PairForestTransactionV1ErrorV2::SanitizeFailed)?;
    let signable_message = versioned_message.serialize();
    if signable_message.first().copied() != Some(SOLANA_V1_VERSION_PREFIX_V2) {
        return Err(PairForestTransactionV1ErrorV2::SerializationFailed);
    }
    let transaction = V1VersionedTransaction {
        signatures: vec![V1Signature::default(); signatures],
        message: versioned_message,
    };
    transaction
        .sanitize()
        .map_err(|_| PairForestTransactionV1ErrorV2::SanitizeFailed)?;
    let placeholder_signature_wire = wincode::serialize(&transaction)
        .map_err(|_| PairForestTransactionV1ErrorV2::SerializationFailed)?;
    if placeholder_signature_wire.first().copied() != Some(SOLANA_V1_VERSION_PREFIX_V2) {
        return Err(PairForestTransactionV1ErrorV2::SerializationFailed);
    }
    if placeholder_signature_wire.len() > SOLANA_V1_TRANSACTION_MAX_BYTES_V2 {
        return Err(PairForestTransactionV1ErrorV2::TransactionTooLarge);
    }
    Ok(ExactUnsignedPairForestV1TransactionV2 {
        signable_message,
        placeholder_signature_wire,
        required_signatures: signatures as u8,
        inline_addresses: addresses as u8,
        instruction_count: 1,
        config,
    })
}

/// Size the same instruction under v0's real 1,232-byte envelope.
///
/// This is diagnostic only. It never authorizes v0 as a 4 KiB fallback.
pub fn compare_exact_pair_forest_v0_size_v2(
    instruction: &Instruction,
    fee_payer: Pubkey,
    recent_blockhash: [u8; 32],
    lookup_tables: &[AddressLookupTableAccount],
) -> Result<LegacyV0SizeComparisonV2, PairForestTransactionV1ErrorV2> {
    let message = solana_message::v0::Message::try_compile(
        &fee_payer,
        &[instruction.clone()],
        &lookup_tables,
        solana_program::hash::Hash::new_from_array(recent_blockhash),
    )
    .map_err(|_| PairForestTransactionV1ErrorV2::CompileFailed)?;
    let signature_count = usize::from(message.header.num_required_signatures);
    let wire = bincode::serialize(&LegacyVersionedTransaction {
        signatures: vec![solana_signature::Signature::default(); signature_count],
        message: LegacyVersionedMessage::V0(message),
    })
    .map_err(|_| PairForestTransactionV1ErrorV2::SerializationFailed)?;
    Ok(LegacyV0SizeComparisonV2 {
        serialized_wire_bytes: wire.len(),
        legacy_v0_limit_bytes: SOLANA_LEGACY_V0_TRANSACTION_MAX_BYTES_V2,
        eligible_for_four_kib: false,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::M31;
    use aspis_pool::{
        deposit::DepositRequestV1, pool_v1_pair_forest_master_address, PoolInitializationV1,
        POOL_V1_PAIR_EMPTY_ROOTS,
    };
    use aspis_statement::pool_v1::{
        IncrementalMerkleTreeV1, PoolIdentityV1, PoolV1PrivateTransferPublicV1,
        PoolV1WithdrawalPublicV1, VerifierPolicyV1, POOL_V1_ENCRYPTED_NOTE_PAYLOAD_MAX_BYTES,
        POOL_V1_PAIR_FOREST_ALL_LANES_MASK, POOL_V1_PAIR_TREE_DEPTH, POOL_V1_ROOT_HISTORY_CAPACITY,
    };

    use crate::{
        lane_forest_client_v2::{
            build_pair_forest_checkpoint_instruction_v2, build_pair_forest_deposit_instruction_v2,
            build_pair_forest_initialize_instruction_v2,
        },
        scan_state::FinalizedChainPointV1,
    };

    fn key(seed: u8) -> Pubkey {
        Pubkey::new_from_array([seed; 32])
    }

    fn digest(seed: u32) -> aspis_statement::Digest {
        core::array::from_fn(|index| M31(seed + index as u32))
    }

    fn initialization(mint: Pubkey, registry_program: Pubkey) -> PoolInitializationV1 {
        PoolInitializationV1 {
            asset_mint: mint.to_bytes(),
            token_program: LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes(),
            asset_id: M31(9),
            deployment_domain: [10; 32],
            verifier_policy: VerifierPolicyV1 {
                flags: 0,
                registry_program: registry_program.to_bytes(),
                registry_authority: [12; 32],
                policy_binding: [13; 32],
            },
        }
    }

    fn master(program: Pubkey, mint: Pubkey, registry_program: Pubkey) -> PoolV1PairForestMasterV1 {
        let initialization = initialization(mint, registry_program);
        PoolV1PairForestMasterV1 {
            identity: PoolIdentityV1 {
                pool: pool_v1_pair_forest_master_address(&program, &mint)
                    .0
                    .to_bytes(),
                asset_mint: initialization.asset_mint,
                token_program: initialization.token_program,
                asset_id: initialization.asset_id,
                deployment_domain: initialization.deployment_domain,
            },
            verifier_policy: initialization.verifier_policy,
            initialized_lane_mask: POOL_V1_PAIR_FOREST_ALL_LANES_MASK,
            has_checkpoint: true,
            next_checkpoint_sequence: 1,
            last_checkpoint_lane_sequences: [0; 8],
        }
    }

    fn lane(
        master: &PoolV1PairForestMasterV1,
        lane_id: u8,
        sequence: u64,
    ) -> PoolV1PairForestLaneStateV1 {
        PoolV1PairForestLaneStateV1 {
            master: master.identity.pool,
            lane_id,
            tree: IncrementalMerkleTreeV1 {
                next_leaf_index: sequence,
                root: POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH],
                frontier: core::array::from_fn(|level| POOL_V1_PAIR_EMPTY_ROOTS[level]),
            },
        }
    }

    fn profile(
        master: &PoolV1PairForestMasterV1,
        registry_program: Pubkey,
        profile_binding: [u8; 32],
        release_binding: [u8; 32],
    ) -> PairForestSpendProfileSelectionV2 {
        let pool = Pubkey::new_from_array(master.identity.pool);
        PairForestSpendProfileSelectionV2 {
            finalized_point: FinalizedChainPointV1::new(10, [11; 32]).unwrap(),
            provider_set_digest: [12; 32],
            registry_program: registry_program.to_bytes(),
            registry_address: aspis_registry::pool_v1_verifier_registry_address(
                &registry_program,
                &pool,
            )
            .0
            .to_bytes(),
            registry_generation: 1,
            entry_address: aspis_registry::pool_v1_verifier_entry_address(
                &registry_program,
                &pool,
                &profile_binding,
                &release_binding,
            )
            .0
            .to_bytes(),
            verifier_program: key(20).to_bytes(),
            profile_binding,
            release_binding,
            statement_version: POOL_V1_PAIR_FOREST_TERMINAL_VERSION,
        }
    }

    fn rollover_sequence() -> u64 {
        u64::try_from(POOL_V1_ROOT_HISTORY_CAPACITY).unwrap() - 1
    }

    fn config() -> PairForestV1TransactionConfigV2 {
        PairForestV1TransactionConfigV2 {
            priority_fee_lamports: 10_000,
            compute_unit_limit: 1_400_000,
            loaded_accounts_data_size_limit: 8 * 1024 * 1024,
            heap_size: 256 * 1024,
        }
    }

    fn terminal_fixture(
        withdrawal: bool,
    ) -> (
        Pubkey,
        PoolV1PairForestMasterV1,
        PoolV1PairForestLaneStateV1,
        PairForestSpendProfileSelectionV2,
        PoolV1PairForestTerminalRequestV1,
    ) {
        let program = key(1);
        let mint = key(2);
        let registry_program = key(3);
        let master = master(program, mint, registry_program);
        let profile_binding = [4; 32];
        let release_binding = [5; 32];
        let nullifier = digest(100);
        let public = if withdrawal {
            PoolV1PairForestTerminalPaymentV1::Withdrawal(PoolV1WithdrawalPublicV1 {
                pool: master.identity.pool,
                deployment_domain: master.identity.deployment_domain,
                anchor_sequence: 0,
                anchor_root: digest(200),
                nullifier,
                asset_id: master.identity.asset_id,
                amount: 7,
                destination_token_account: key(6).to_bytes(),
                change_commitment: digest(300),
            })
        } else {
            PoolV1PairForestTerminalPaymentV1::PrivateTransfer(PoolV1PrivateTransferPublicV1 {
                pool: master.identity.pool,
                deployment_domain: master.identity.deployment_domain,
                anchor_sequence: 0,
                anchor_root: digest(200),
                nullifier,
                asset_id: master.identity.asset_id,
                recipient_commitment: digest(300),
                change_commitment: digest(400),
            })
        };
        let lane_id = pool_v1_pair_forest_output_lane_v1(public.nullifier()).unwrap();
        (
            program,
            master,
            lane(&master, lane_id, rollover_sequence()),
            profile(&master, registry_program, profile_binding, release_binding),
            PoolV1PairForestTerminalRequestV1 {
                verifier_profile: profile_binding,
                verifier_release: release_binding,
                pool_program: program.to_bytes(),
                public,
            },
        )
    }

    #[test]
    fn max_shape_terminal_wires_are_tx_v1_and_never_embed_the_proof() {
        for (withdrawal, expected_accounts, expected_v1, expected_v0, expected_addresses) in
            [(false, 10, 844, 822, 12), (true, 15, 1_009, 987, 17)]
        {
            let (program, master, lane, profile, request) = terminal_fixture(withdrawal);
            let proof_account = key(21);
            let instruction = build_pair_forest_terminal_instruction_v1_4k_v2(
                program,
                &master,
                &lane,
                profile,
                proof_account,
                &request,
            )
            .unwrap();
            assert_eq!(instruction.accounts.len(), expected_accounts);
            assert_eq!(instruction.data.len(), 320);
            let transaction = build_exact_pair_forest_v1_transaction_v2(
                &instruction,
                key(22),
                [23; 32],
                config(),
                &[],
            )
            .unwrap();
            assert_eq!(transaction.placeholder_signature_wire_v2()[0], 0x81);
            assert_eq!(transaction.required_signatures_v2(), 1);
            assert_eq!(transaction.serialized_wire_bytes_v2(), expected_v1);
            assert_eq!(transaction.inline_addresses_v2(), expected_addresses);
            assert!(!transaction
                .placeholder_signature_wire_v2()
                .windows(64)
                .any(|window| window == [0x5a; 64]));
            let v0 =
                compare_exact_pair_forest_v0_size_v2(&instruction, key(22), [23; 32], &[]).unwrap();
            assert_eq!(v0.serialized_wire_bytes, expected_v0);
            assert!(!v0.eligible_for_four_kib);
        }
    }

    #[test]
    fn max_shape_init_checkpoint_and_deposit_fit_exact_v1_envelope() {
        let program = key(30);
        let mint = key(31);
        let registry_program = key(32);
        let initialization = initialization(mint, registry_program);
        let mut master = master(program, mint, registry_program);
        let init =
            build_pair_forest_initialize_instruction_v2(program, key(33), &initialization).unwrap();
        let checkpoint =
            build_pair_forest_checkpoint_instruction_v2(program, key(34), &master).unwrap();

        let payload = [0xa5; POOL_V1_ENCRYPTED_NOTE_PAYLOAD_MAX_BYTES];
        let deposit_request = DepositRequestV1 {
            owner_key: [M31(35); 8],
            amount: 9,
            salt: [M31(36); 8],
            encrypted_note_payload: &payload,
        };
        let commitment = aspis_statement::pool_v1::pool_v1_note_commitment(
            &deposit_request.owner_key,
            deposit_request.amount,
            master.identity.asset_id,
            &deposit_request.salt,
        );
        let lane_id =
            aspis_statement::pool_v1::pool_v1_pair_forest_deposit_lane_v1(&commitment).unwrap();
        master.has_checkpoint = true;
        let deposit = build_pair_forest_deposit_instruction_v2(
            program,
            &master,
            &lane(&master, lane_id, rollover_sequence()),
            key(37),
            key(38),
            Some(key(39)),
            &deposit_request,
        )
        .unwrap();

        for (instruction, fee_payer, expected_signatures, expected_wire, expected_addresses) in [
            (init, key(40), 2, 904, 16),
            (checkpoint, key(40), 2, 662, 14),
            (deposit, key(40), 3, 1_277, 13),
        ] {
            let transaction = build_exact_pair_forest_v1_transaction_v2(
                &instruction,
                fee_payer,
                [41; 32],
                config(),
                &[],
            )
            .unwrap();
            assert_eq!(transaction.placeholder_signature_wire_v2()[0], 0x81);
            assert_eq!(transaction.required_signatures_v2(), expected_signatures);
            assert_eq!(transaction.serialized_wire_bytes_v2(), expected_wire);
            assert_eq!(transaction.inline_addresses_v2(), expected_addresses);
        }
    }

    #[test]
    fn v1_rejects_alt_compute_budget_and_invalid_resource_config() {
        let compute_budget =
            solana_compute_budget_interface::ComputeBudgetInstruction::set_compute_unit_limit(
                1_000_000,
            );
        assert_eq!(
            build_exact_pair_forest_v1_transaction_v2(
                &compute_budget,
                key(50),
                [51; 32],
                config(),
                &[],
            ),
            Err(PairForestTransactionV1ErrorV2::ComputeBudgetInstructionForbidden)
        );

        let (program, master, lane, profile, request) = terminal_fixture(false);
        let instruction = build_pair_forest_terminal_instruction_v1_4k_v2(
            program,
            &master,
            &lane,
            profile,
            key(52),
            &request,
        )
        .unwrap();
        let lookup_table = AddressLookupTableAccount {
            key: key(53),
            addresses: vec![key(54)],
        };
        assert_eq!(
            build_exact_pair_forest_v1_transaction_v2(
                &instruction,
                key(55),
                [56; 32],
                config(),
                &[lookup_table],
            ),
            Err(PairForestTransactionV1ErrorV2::AddressLookupTableForbidden)
        );
        let mut invalid = config();
        invalid.compute_unit_limit = 0;
        assert_eq!(
            build_exact_pair_forest_v1_transaction_v2(
                &instruction,
                key(55),
                [56; 32],
                invalid,
                &[],
            ),
            Err(PairForestTransactionV1ErrorV2::InvalidComputeLimit)
        );

        let oversized = Instruction {
            program_id: key(57),
            accounts: vec![],
            data: vec![0u8; 4_000],
        };
        assert_eq!(
            build_exact_pair_forest_v1_transaction_v2(&oversized, key(58), [59; 32], config(), &[],),
            Err(PairForestTransactionV1ErrorV2::TransactionTooLarge)
        );
    }

    #[test]
    fn devnet_feature_account_parser_distinguishes_missing_pending_and_active() {
        assert_eq!(
            feature_activation_v2(&serde_json::Value::Null),
            Ok((false, None))
        );
        let pending = serde_json::json!({
            "owner": SOLANA_FEATURE_PROGRAM_ID_V2,
            "data": [BASE64_STANDARD.encode([0u8]), "base64"]
        });
        assert_eq!(feature_activation_v2(&pending), Ok((true, None)));
        let mut active = vec![1u8];
        active.extend_from_slice(&987_654u64.to_le_bytes());
        let active = serde_json::json!({
            "owner": SOLANA_FEATURE_PROGRAM_ID_V2,
            "data": [BASE64_STANDARD.encode(active), "base64"]
        });
        assert_eq!(feature_activation_v2(&active), Ok((true, Some(987_654))));
        let wrong_owner = serde_json::json!({
            "owner": "11111111111111111111111111111111",
            "data": [BASE64_STANDARD.encode([0u8]), "base64"]
        });
        assert_eq!(
            feature_activation_v2(&wrong_owner),
            Err(TxV1CapabilityProbeErrorV2::WrongFeatureOwner)
        );
    }
}
