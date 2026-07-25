//! One-shot mainnet sweep from the disposable V5 payer to a locally pinned
//! refund wallet.
//!
//! The recipient is read from an absolute, non-symlink, owner-only file outside
//! the workspace. The command builds one System Program transfer, signs and
//! simulates those exact bytes, submits them once, refetches the finalized
//! transaction, and records immutable before/after evidence.

#![allow(deprecated)]

use std::{
    collections::BTreeMap,
    fs::{self, OpenOptions},
    io::{Read, Write},
    os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt},
    path::{Path, PathBuf},
    str::FromStr,
    thread,
    time::{Duration, Instant},
};

use anyhow::{anyhow, bail, ensure, Context, Result};
use base64::{engine::general_purpose::STANDARD as BASE64, Engine};
use serde::Serialize;
use serde_json::{json, Map, Value};
use sha2::{Digest, Sha256};
use solana_sdk::{
    hash::Hash,
    instruction::CompiledInstruction,
    message::VersionedMessage,
    pubkey::Pubkey,
    signature::{read_keypair_file, Keypair, Signature, Signer},
    system_instruction, system_program,
    transaction::{Transaction, VersionedTransaction},
};

use crate::spend_mainnet_loader::{
    derive_programdata_address, validate_exact_program_account, LoaderAccountImage,
};

pub const EXECUTE_ACKNOWLEDGEMENT: &str =
    "I_ACKNOWLEDGE_V5_MAINNET_PAYER_SWEEP_SENDS_THE_SIGNED_SNAPSHOT_BALANCE_MINUS_FEE_TO_THE_LOCALLY_PINNED_REFUND_RECIPIENT";

const MAINNET_BETA_GENESIS_HASH: &str = "5eykt4UsFv8P8NJdTREpY1vzqKqZKvdpKuc147dw2N9d";
const READ_RETRIES: u8 = 12;
const FINALITY_TIMEOUT: Duration = Duration::from_secs(180);
const POLL_INTERVAL: Duration = Duration::from_secs(2);
const IN_PROGRESS_WARNING: &str =
    "The sweep did not reach its linked immutable finalized receipt. Inspect the pre-submit artifact and exact signed wire before any retry.";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SweepConfig {
    rpc_url: String,
    rpc_origin_redacted: String,
    payer_keypair: PathBuf,
    expected_payer_pubkey: Pubkey,
    expected_program_id: Pubkey,
    expected_proof_account: Pubkey,
    expected_tag67_signature: Signature,
    refund_recipient_pubkey_file: PathBuf,
    expected_refund_pin_sha256: String,
    fee_reserve_lamports: u64,
    evidence: PathBuf,
    expected_genesis_hash: String,
    acknowledgement: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct PinnedRecipient {
    pubkey: Pubkey,
    raw_bytes: Vec<u8>,
    raw_sha256: String,
    mode: u32,
    uid: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RpcAccount {
    lamports: u64,
    owner: Pubkey,
    executable: bool,
    data: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CoherentSnapshot {
    context_slot: u64,
    addresses: Vec<Pubkey>,
    accounts: Vec<Option<RpcAccount>>,
}

#[derive(Clone, Debug)]
struct Simulation {
    context_slot: u64,
    error: Option<Value>,
    units: u64,
    logs: Vec<String>,
}

#[derive(Clone, Debug)]
struct FinalizedTransaction {
    block_time: Option<i64>,
    fee_lamports: u64,
    pre_balances: Vec<u64>,
    post_balances: Vec<u64>,
    compute_units: u64,
    logs: Vec<String>,
    wire: Vec<u8>,
}

#[derive(Clone, Debug, Serialize)]
struct AccountEvidence {
    address: String,
    present: bool,
    lamports: Option<u64>,
    owner: Option<String>,
    executable: Option<bool>,
    data_len: Option<usize>,
    data_sha256: Option<String>,
}

#[derive(Clone, Debug, Serialize)]
struct SnapshotEvidence {
    context_slot: u64,
    accounts: Vec<AccountEvidence>,
}

#[derive(Clone, Debug, Serialize)]
struct SimulationEvidence {
    exact_signed_wire_simulated: bool,
    context_slot: u64,
    error: Option<Value>,
    compute_units_consumed: u64,
    logs_sha256: String,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
struct SweepBalanceEvidence {
    payer_account_index: usize,
    refund_recipient_account_index: usize,
    payer_pre_lamports: u64,
    payer_post_lamports: u64,
    refund_recipient_pre_lamports: u64,
    refund_recipient_post_lamports: u64,
    transfer_lamports: u64,
    fee_lamports: u64,
    payer_pre_matches_signed_snapshot: bool,
    payer_pre_at_least_signed_snapshot: bool,
    inbound_dust_after_signing_lamports: u64,
    payer_debit_equals_transfer_plus_fee: bool,
    recipient_credit_equals_transfer: bool,
    payer_post_is_zero: bool,
    payer_post_equals_inbound_dust_after_signing: bool,
    signed_snapshot_balance_fully_swept: bool,
    every_other_message_account_balance_unchanged: bool,
    landed_exact_zero_balance_result: bool,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
struct PostfinalityBalanceEvidence {
    landed_payer_residual_lamports: u64,
    current_payer_lamports: u64,
    payer_inbound_after_landing_lamports: u64,
    landed_refund_recipient_post_lamports: u64,
    current_refund_recipient_lamports: u64,
    refund_recipient_inbound_after_landing_lamports: u64,
    presubmit_program_lamports: u64,
    current_program_lamports: u64,
    program_inbound_after_submission_lamports: u64,
    presubmit_programdata_dust_lamports: u64,
    current_programdata_dust_lamports: u64,
    programdata_inbound_after_submission_lamports: u64,
    presubmit_proof_account_dust_lamports: u64,
    current_proof_account_dust_lamports: u64,
    proof_account_inbound_after_submission_lamports: u64,
}

#[derive(Clone, Debug, Serialize)]
struct PresubmitEvidence {
    artifact: &'static str,
    generated_at_utc: String,
    network_genesis_hash: String,
    rpc_origin_redacted: String,
    payer_pubkey: String,
    refund_recipient_pubkey: String,
    expected_program_id: String,
    expected_programdata_address: String,
    expected_proof_account: String,
    expected_tag67_signature: String,
    tag67_finalized_slot: u64,
    tag67_landed_wire_sha256: String,
    tag67_instruction_and_proof_role_validated: bool,
    refund_recipient_pin_sha256: String,
    expected_refund_recipient_pin_sha256: String,
    refund_recipient_pin_sha256_matches_expected: bool,
    refund_recipient_pin_mode: u32,
    refund_recipient_pin_owner_matches_payer_keypair: bool,
    refund_recipient_pin_outside_workspace: bool,
    prestate: SnapshotEvidence,
    before_submission: SnapshotEvidence,
    programdata_closed_or_system_dust_before_signing: bool,
    programdata_dust_lamports_before_signing: u64,
    proof_account_closed_or_system_dust_before_signing: bool,
    proof_account_dust_lamports_before_signing: u64,
    payer_inbound_lamports_before_submission: u64,
    recipient_inbound_lamports_before_submission: u64,
    program_inbound_lamports_before_submission: u64,
    programdata_dust_lamports_before_submission: u64,
    programdata_inbound_dust_before_submission_lamports: u64,
    proof_account_dust_lamports_before_submission: u64,
    proof_account_inbound_dust_before_submission_lamports: u64,
    fee_reserve_lamports: u64,
    quoted_fee_lamports: u64,
    transfer_lamports: u64,
    expected_payer_post_lamports_without_concurrent_inflow: u64,
    expected_signature: String,
    recent_blockhash: String,
    last_valid_block_height: u64,
    signed_wire_base64: String,
    signed_wire_bytes: usize,
    signed_wire_sha256: String,
    message_sha256: String,
    exact_single_system_transfer_validated: bool,
    pin_reread_before_signing_exact: bool,
    pin_reread_before_submission_exact: bool,
    prestate_reread_before_submission_donation_only: bool,
    simulation: SimulationEvidence,
    submission_performed_when_written: bool,
    postsubmit_evidence_path: String,
}

#[derive(Clone, Debug, Serialize)]
struct PostsubmitEvidence {
    artifact: &'static str,
    generated_at_utc: String,
    network_genesis_hash: String,
    rpc_origin_redacted: String,
    presubmit_evidence_path: String,
    presubmit_evidence_sha256: String,
    presubmit_evidence_bytes: usize,
    presubmit_evidence_mode: u32,
    signature: String,
    finalized_slot: u64,
    block_time: Option<i64>,
    landed_wire_sha256: String,
    landed_wire_identical_to_presubmit_artifact: bool,
    landed_message_identical_to_signed_message: bool,
    landed_compute_units_consumed: u64,
    landed_logs_sha256: String,
    quoted_fee_lamports: u64,
    landed_fee_lamports: u64,
    landed_fee_equals_quote: bool,
    balances: SweepBalanceEvidence,
    postfinality_snapshot: SnapshotEvidence,
    postfinality_balances: PostfinalityBalanceEvidence,
    post_landing_dust_does_not_change_landed_reconciliation: bool,
}

#[derive(Clone, Debug, Serialize)]
pub struct EvidenceReceipt {
    pub path: String,
    pub sha256: String,
    pub bytes: usize,
    pub mode: u32,
}

#[derive(Clone, Debug, Serialize)]
pub struct SweepOutcome {
    pub signature: String,
    pub finalized_slot: u64,
    pub payer_pubkey: String,
    pub refund_recipient_pubkey: String,
    pub transfer_lamports: u64,
    pub fee_lamports: u64,
    pub payer_post_lamports: u64,
    pub inbound_dust_after_signing_lamports: u64,
    pub signed_snapshot_balance_fully_swept: bool,
    pub landed_exact_zero_balance_result: bool,
    pub presubmit_evidence: EvidenceReceipt,
    pub postsubmit_evidence: EvidenceReceipt,
}

struct Rpc {
    endpoint: String,
    client: reqwest::blocking::Client,
}

impl Rpc {
    fn new(endpoint: String) -> Result<Self> {
        Ok(Self {
            endpoint,
            client: reqwest::blocking::Client::builder()
                .timeout(Duration::from_secs(60))
                .redirect(reqwest::redirect::Policy::none())
                .retry(reqwest::retry::never())
                .build()?,
        })
    }

    fn call(&self, method: &str, params: Value) -> Result<Value> {
        let response = self
            .client
            .post(&self.endpoint)
            .json(&json!({"jsonrpc":"2.0","id":1,"method":method,"params":params}))
            .send()
            .map_err(|_| anyhow!("RPC {method} transport failure (endpoint redacted)"))?;
        let status = response.status();
        let value: Value = response
            .json()
            .with_context(|| format!("RPC {method} returned non-JSON HTTP {}", status.as_u16()))?;
        ensure!(
            status.is_success(),
            "RPC {method} returned HTTP {}",
            status.as_u16()
        );
        if let Some(error) = value.get("error") {
            bail!("RPC {method} error: {error}");
        }
        value
            .get("result")
            .cloned()
            .ok_or_else(|| anyhow!("RPC {method} omitted result"))
    }

    fn read(&self, method: &str, params: Value) -> Result<Value> {
        let mut retries = 0u8;
        loop {
            match self.call(method, params.clone()) {
                Ok(value) => return Ok(value),
                Err(error) if retries < READ_RETRIES && rpc_read_retryable(&error) => {
                    retries += 1;
                    thread::sleep(POLL_INTERVAL);
                }
                Err(error) => return Err(error),
            }
        }
    }

    fn genesis_hash(&self) -> Result<String> {
        self.read("getGenesisHash", json!([]))?
            .as_str()
            .map(ToOwned::to_owned)
            .context("getGenesisHash result was not a string")
    }

    fn latest_blockhash(&self) -> Result<(Hash, u64, u64)> {
        let result = self.read("getLatestBlockhash", json!([{"commitment":"finalized"}]))?;
        let value = &result["value"];
        Ok((
            value["blockhash"]
                .as_str()
                .context("latest blockhash missing")?
                .parse()
                .context("latest blockhash invalid")?,
            value["lastValidBlockHeight"]
                .as_u64()
                .context("latest blockhash expiry missing")?,
            result["context"]["slot"]
                .as_u64()
                .context("latest blockhash context slot missing")?,
        ))
    }

    fn block_height(&self) -> Result<u64> {
        self.read("getBlockHeight", json!([{"commitment":"finalized"}]))?
            .as_u64()
            .context("getBlockHeight result was not u64")
    }

    fn snapshot(
        &self,
        addresses: &[Pubkey],
        min_context_slot: Option<u64>,
    ) -> Result<CoherentSnapshot> {
        let mut config = Map::new();
        config.insert("encoding".to_owned(), Value::String("base64".to_owned()));
        config.insert(
            "commitment".to_owned(),
            Value::String("finalized".to_owned()),
        );
        if let Some(slot) = min_context_slot {
            config.insert("minContextSlot".to_owned(), Value::from(slot));
        }
        let result = self.read(
            "getMultipleAccounts",
            json!([
                addresses
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>(),
                Value::Object(config)
            ]),
        )?;
        parse_coherent_snapshot(&result, addresses)
    }

    fn fee_for_transaction_message(&self, transaction: &Transaction) -> Result<u64> {
        let message = bincode::serialize(&transaction.message)?;
        self.read(
            "getFeeForMessage",
            json!([BASE64.encode(message), {"commitment":"finalized"}]),
        )?["value"]
            .as_u64()
            .context("getFeeForMessage returned no fee")
    }

    fn simulate_exact(&self, wire: &[u8], min_context_slot: u64) -> Result<Simulation> {
        let result = self.read(
            "simulateTransaction",
            json!([BASE64.encode(wire), {
                "encoding":"base64",
                "sigVerify":true,
                "replaceRecentBlockhash":false,
                "commitment":"finalized",
                "minContextSlot":min_context_slot
            }]),
        )?;
        parse_simulation(&result)
    }

    fn signature_status(
        &self,
        signature: &Signature,
    ) -> Result<Option<(u64, bool, Option<Value>)>> {
        let result = self.read(
            "getSignatureStatuses",
            json!([[signature.to_string()], {"searchTransactionHistory":true}]),
        )?;
        parse_signature_status(&result)
    }

    fn send_exact_once(&self, wire: &[u8], expected_signature: &Signature) -> Result<()> {
        match self.call(
            "sendTransaction",
            json!([BASE64.encode(wire), {
                "encoding":"base64",
                "skipPreflight":false,
                "preflightCommitment":"finalized",
                "maxRetries":0
            }]),
        ) {
            Ok(value) => ensure!(
                value.as_str() == Some(expected_signature.to_string().as_str()),
                "RPC returned a signature different from the immutable wire"
            ),
            Err(error) => ensure!(
                self.signature_status(expected_signature)?.is_some(),
                "single exact-wire submission failed and its signature is unseen: {error}"
            ),
        }
        Ok(())
    }

    fn wait_finalized(&self, signature: &Signature) -> Result<u64> {
        let started = Instant::now();
        loop {
            if let Some((slot, finalized, error)) = self.signature_status(signature)? {
                if let Some(error) = error {
                    bail!("payer sweep {signature} failed: {error}");
                }
                if finalized {
                    return Ok(slot);
                }
            }
            ensure!(
                started.elapsed() < FINALITY_TIMEOUT,
                "payer sweep {signature} did not finalize before timeout"
            );
            thread::sleep(POLL_INTERVAL);
        }
    }

    fn transaction_result(&self, signature: &Signature, encoding: &str) -> Result<Value> {
        let started = Instant::now();
        loop {
            let result = self.read(
                "getTransaction",
                json!([signature.to_string(), {
                    "encoding":encoding,
                    "commitment":"finalized",
                    "maxSupportedTransactionVersion":0
                }]),
            )?;
            if !result.is_null() {
                return Ok(result);
            }
            ensure!(
                started.elapsed() < FINALITY_TIMEOUT,
                "finalized payer sweep unavailable from getTransaction"
            );
            thread::sleep(POLL_INTERVAL);
        }
    }

    fn finalized_transaction(
        &self,
        signature: &Signature,
        expected_slot: u64,
    ) -> Result<FinalizedTransaction> {
        let json_result = self.transaction_result(signature, "json")?;
        let base64_result = self.transaction_result(signature, "base64")?;
        parse_finalized_transaction(&json_result, &base64_result, expected_slot)
    }

    fn existing_finalized_transaction(
        &self,
        signature: &Signature,
    ) -> Result<(u64, FinalizedTransaction)> {
        let (slot, finalized, error) = self
            .signature_status(signature)?
            .context("expected Tag-67 signature is not present on mainnet")?;
        ensure!(
            error.is_none(),
            "expected Tag-67 transaction failed: {error:?}"
        );
        ensure!(
            finalized,
            "expected Tag-67 transaction has not reached finalized commitment"
        );
        let transaction = self.finalized_transaction(signature, slot)?;
        Ok((slot, transaction))
    }
}

struct EvidenceReservation {
    path: PathBuf,
    file: fs::File,
}

impl EvidenceReservation {
    fn reserve(path: &Path) -> Result<Self> {
        prepare_evidence_parent(path)?;
        let mut file = OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(path)
            .with_context(|| format!("reserve payer-sweep evidence {}", path.display()))?;
        write_synced_json(
            &mut file,
            &json!({
                "artifact": "aspis_v5_mainnet_payer_sweep_postsubmit",
                "status": "in_progress_no_finalized_claim",
                "reserved_at_utc": chrono::Utc::now().to_rfc3339(),
                "warning": IN_PROGRESS_WARNING,
            }),
        )?;
        sync_parent(path)?;
        Ok(Self {
            path: path.to_path_buf(),
            file,
        })
    }

    fn commit(self, value: &impl Serialize) -> Result<EvidenceReceipt> {
        let bytes = serialized_json(value)?;
        let parent = self.path.parent().context("evidence path omitted parent")?;
        let filename = self
            .path
            .file_name()
            .and_then(|name| name.to_str())
            .context("evidence filename is not UTF-8")?;
        let temporary = parent.join(format!(".{filename}.complete-{}", std::process::id()));
        let mut completed = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&temporary)
            .with_context(|| format!("create completed evidence {}", temporary.display()))?;
        completed.write_all(&bytes)?;
        completed.sync_all()?;
        let mut permissions = completed.metadata()?.permissions();
        permissions.set_mode(0o444);
        fs::set_permissions(&temporary, permissions)?;
        completed.sync_all()?;

        drop(self.file);
        fs::rename(&temporary, &self.path)?;
        sync_parent(&self.path)?;
        immutable_receipt(&self.path)
    }
}

/// Parse the command without reading key or pin files and without network I/O.
pub fn parse_args(arguments: &[String]) -> Result<SweepConfig> {
    let mut values = BTreeMap::<String, String>::new();
    let mut execute_interlock = false;
    let mut index = 0usize;
    while index < arguments.len() {
        let key = &arguments[index];
        if key == "--execute-mainnet-payer-sweep" {
            ensure!(!execute_interlock, "duplicate payer-sweep interlock");
            execute_interlock = true;
            index += 1;
            continue;
        }
        ensure!(
            key.starts_with("--"),
            "unexpected positional argument {key}"
        );
        let value = arguments
            .get(index + 1)
            .ok_or_else(|| anyhow!("missing value for {key}"))?;
        ensure!(
            values.insert(key.clone(), value.clone()).is_none(),
            "duplicate argument {key}"
        );
        index += 2;
    }
    ensure!(execute_interlock, "missing payer-sweep execute interlock");
    let allowed = [
        "--rpc-url",
        "--payer-keypair",
        "--expected-payer-pubkey",
        "--expected-program-id",
        "--expected-proof-account",
        "--expected-tag67-signature",
        "--refund-recipient-pubkey-file",
        "--expected-refund-pin-sha256",
        "--fee-reserve-lamports",
        "--evidence",
        "--expected-genesis",
        "--acknowledgement",
    ];
    for key in values.keys() {
        ensure!(allowed.contains(&key.as_str()), "unknown argument {key}");
    }
    let required = |key: &str| {
        values
            .get(key)
            .cloned()
            .ok_or_else(|| anyhow!("missing required explicit argument {key}"))
    };
    let absolute = |key: &str| -> Result<PathBuf> {
        let path = PathBuf::from(required(key)?);
        ensure!(path.is_absolute(), "{key} must be an absolute path");
        Ok(path)
    };

    let acknowledgement = required("--acknowledgement")?;
    ensure!(
        acknowledgement == EXECUTE_ACKNOWLEDGEMENT,
        "payer-sweep acknowledgement mismatch"
    );
    let expected_genesis_hash = required("--expected-genesis")?;
    ensure!(
        expected_genesis_hash == MAINNET_BETA_GENESIS_HASH,
        "payer sweep is restricted to the canonical mainnet-beta genesis"
    );
    Hash::from_str(&expected_genesis_hash).context("--expected-genesis is not a hash")?;
    let rpc_url = required("--rpc-url")?;
    let rpc_origin_redacted = explicit_https_rpc(&rpc_url)?;
    let payer_keypair = absolute("--payer-keypair")?;
    let refund_recipient_pubkey_file = absolute("--refund-recipient-pubkey-file")?;
    let evidence = absolute("--evidence")?;
    ensure!(
        payer_keypair != refund_recipient_pubkey_file
            && payer_keypair != evidence
            && refund_recipient_pubkey_file != evidence,
        "payer keypair, refund pin, and evidence paths must differ"
    );
    let fee_reserve_lamports = required("--fee-reserve-lamports")?
        .parse::<u64>()
        .context("--fee-reserve-lamports is not u64")?;
    ensure!(
        fee_reserve_lamports > 0,
        "--fee-reserve-lamports must be nonzero"
    );
    let expected_refund_pin_sha256 = required("--expected-refund-pin-sha256")?;
    ensure!(
        expected_refund_pin_sha256.len() == 64
            && expected_refund_pin_sha256
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
        "--expected-refund-pin-sha256 must be 64 lowercase hexadecimal characters"
    );
    Ok(SweepConfig {
        rpc_url,
        rpc_origin_redacted,
        payer_keypair,
        expected_payer_pubkey: required("--expected-payer-pubkey")?
            .parse()
            .context("--expected-payer-pubkey is not a pubkey")?,
        expected_program_id: required("--expected-program-id")?
            .parse()
            .context("--expected-program-id is not a pubkey")?,
        expected_proof_account: required("--expected-proof-account")?
            .parse()
            .context("--expected-proof-account is not a pubkey")?,
        expected_tag67_signature: required("--expected-tag67-signature")?
            .parse()
            .context("--expected-tag67-signature is not a signature")?,
        refund_recipient_pubkey_file,
        expected_refund_pin_sha256,
        fee_reserve_lamports,
        evidence,
        expected_genesis_hash,
        acknowledgement,
    })
}

/// Execute one exact mainnet sweep. This is the only function in this module
/// that signs or submits a transaction.
pub fn execute(arguments: &[String]) -> Result<SweepOutcome> {
    let config = parse_args(arguments)?;
    ensure!(config.acknowledgement == EXECUTE_ACKNOWLEDGEMENT);
    let (presubmit_path, postsubmit_path) = evidence_paths(&config.evidence)?;
    ensure!(
        !presubmit_path.exists() && !postsubmit_path.exists(),
        "payer-sweep evidence path already exists"
    );
    let postsubmit_reservation = EvidenceReservation::reserve(&postsubmit_path)?;

    let payer = secure_keypair(&config.payer_keypair)?;
    ensure!(
        payer.pubkey() == config.expected_payer_pubkey,
        "payer keypair differs from --expected-payer-pubkey"
    );
    ensure!(
        config.expected_program_id == aspis_verifier::id(),
        "payer sweep is restricted to the canonical Aspis V5 program ID"
    );
    ensure!(
        config.expected_proof_account.is_on_curve(),
        "expected proof account must be an on-curve keypair address"
    );
    ensure!(
        payer.pubkey().is_on_curve(),
        "payer must be an on-curve System wallet"
    );
    let pinned = read_pinned_recipient(&config.refund_recipient_pubkey_file)?;
    let payer_metadata = fs::symlink_metadata(&config.payer_keypair)
        .context("stat payer keypair for refund-pin ownership check")?;
    ensure!(
        pinned.uid == payer_metadata.uid(),
        "refund-recipient pin and payer keypair must have the same file owner"
    );
    ensure!(
        pinned.raw_sha256 == config.expected_refund_pin_sha256,
        "refund-recipient pin SHA-256 differs from --expected-refund-pin-sha256"
    );
    ensure!(
        payer.pubkey() != pinned.pubkey,
        "refund recipient must differ from the disposable payer"
    );
    let programdata = derive_programdata_address(&config.expected_program_id);
    ensure!(
        config.expected_proof_account != payer.pubkey()
            && config.expected_proof_account != pinned.pubkey
            && config.expected_proof_account != config.expected_program_id
            && config.expected_proof_account != programdata,
        "proof, payer, recipient, Program, and ProgramData addresses must be distinct"
    );

    let rpc = Rpc::new(config.rpc_url.clone())?;
    let observed_genesis = rpc.genesis_hash()?;
    ensure!(
        observed_genesis == config.expected_genesis_hash,
        "RPC genesis differs from canonical mainnet-beta"
    );
    let (tag67_slot, tag67_finalized) =
        rpc.existing_finalized_transaction(&config.expected_tag67_signature)?;
    validate_landed_tag67(
        &tag67_finalized.wire,
        &config.expected_program_id,
        &config.expected_proof_account,
        &payer.pubkey(),
    )?;
    let (recent_blockhash, last_valid_block_height, blockhash_context_slot) =
        rpc.latest_blockhash()?;
    let addresses = [
        payer.pubkey(),
        pinned.pubkey,
        config.expected_program_id,
        programdata,
        config.expected_proof_account,
    ];
    let signed_snapshot = rpc.snapshot(&addresses, Some(blockhash_context_slot))?;
    let (programdata_dust_signed, proof_dust_signed) = validate_sweep_prestate(
        &signed_snapshot,
        &payer.pubkey(),
        &pinned.pubkey,
        &config.expected_program_id,
        &programdata,
        &config.expected_proof_account,
    )?;
    let payer_balance = signed_snapshot.required(&payer.pubkey(), "payer")?.lamports;

    // Fee calculation does not depend on the transfer amount, but the quote is
    // taken from the exact final message after the pin is re-read.
    let provisional = Transaction::new_unsigned(solana_sdk::message::Message::new_with_blockhash(
        &[system_instruction::transfer(
            &payer.pubkey(),
            &pinned.pubkey,
            1,
        )],
        Some(&payer.pubkey()),
        &recent_blockhash,
    ));
    let provisional_fee = rpc.fee_for_transaction_message(&provisional)?;
    ensure!(
        provisional_fee > 0 && provisional_fee <= config.fee_reserve_lamports,
        "quoted fee {provisional_fee} exceeds the explicit reserve {}",
        config.fee_reserve_lamports
    );
    let pin_before_signing = read_pinned_recipient(&config.refund_recipient_pubkey_file)?;
    ensure!(
        pin_before_signing == pinned,
        "refund-recipient pin changed before signing"
    );
    let transfer_lamports = payer_balance
        .checked_sub(provisional_fee)
        .context("payer balance does not cover the quoted sweep fee")?;
    ensure!(
        transfer_lamports > 0,
        "payer has no spendable sweep balance"
    );

    let instruction =
        system_instruction::transfer(&payer.pubkey(), &pinned.pubkey, transfer_lamports);
    let transaction = Transaction::new_signed_with_payer(
        std::slice::from_ref(&instruction),
        Some(&payer.pubkey()),
        &[&payer],
        recent_blockhash,
    );
    validate_exact_signed_sweep(
        &transaction,
        &payer.pubkey(),
        &pinned.pubkey,
        transfer_lamports,
        recent_blockhash,
    )?;
    let quoted_fee_lamports = rpc.fee_for_transaction_message(&transaction)?;
    ensure!(
        quoted_fee_lamports == provisional_fee,
        "final signed-message fee differs from the provisional exact-shape quote"
    );
    ensure!(
        quoted_fee_lamports <= config.fee_reserve_lamports,
        "final fee quote exceeds the explicit reserve"
    );
    let wire = bincode::serialize(&transaction)?;
    let expected_signature = transaction.signatures[0];
    let wire_sha256 = sha256(&wire);
    let message_sha256 = sha256(&bincode::serialize(&transaction.message)?);

    let simulation = rpc.simulate_exact(&wire, signed_snapshot.context_slot)?;
    ensure!(
        simulation.error.is_none(),
        "exact signed payer-sweep simulation rejected: {:?}",
        simulation.error
    );
    let before_submission = rpc.snapshot(
        &addresses,
        Some(simulation.context_slot.max(signed_snapshot.context_slot)),
    )?;
    let (programdata_dust_presubmit, proof_dust_presubmit) = validate_sweep_prestate(
        &before_submission,
        &payer.pubkey(),
        &pinned.pubkey,
        &config.expected_program_id,
        &programdata,
        &config.expected_proof_account,
    )?;
    let (
        payer_inbound_presubmit,
        recipient_inbound_presubmit,
        program_inbound_presubmit,
        programdata_inbound_presubmit,
        proof_inbound_presubmit,
    ) = validate_donation_only_snapshot_change(
        &signed_snapshot,
        &before_submission,
        &payer.pubkey(),
        &pinned.pubkey,
        &config.expected_program_id,
        &programdata,
        &config.expected_proof_account,
    )?;
    let pin_before_submission = read_pinned_recipient(&config.refund_recipient_pubkey_file)?;
    ensure!(
        pin_before_submission == pinned,
        "refund-recipient pin changed before submission"
    );
    ensure!(
        rpc.block_height()? <= last_valid_block_height,
        "signed payer sweep expired before submission"
    );

    let presubmit = PresubmitEvidence {
        artifact: "aspis_v5_mainnet_payer_sweep_presubmit",
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        network_genesis_hash: observed_genesis.clone(),
        rpc_origin_redacted: config.rpc_origin_redacted.clone(),
        payer_pubkey: payer.pubkey().to_string(),
        refund_recipient_pubkey: pinned.pubkey.to_string(),
        expected_program_id: config.expected_program_id.to_string(),
        expected_programdata_address: programdata.to_string(),
        expected_proof_account: config.expected_proof_account.to_string(),
        expected_tag67_signature: config.expected_tag67_signature.to_string(),
        tag67_finalized_slot: tag67_slot,
        tag67_landed_wire_sha256: sha256(&tag67_finalized.wire),
        tag67_instruction_and_proof_role_validated: true,
        refund_recipient_pin_sha256: pinned.raw_sha256.clone(),
        expected_refund_recipient_pin_sha256: config.expected_refund_pin_sha256,
        refund_recipient_pin_sha256_matches_expected: true,
        refund_recipient_pin_mode: pinned.mode,
        refund_recipient_pin_owner_matches_payer_keypair: true,
        refund_recipient_pin_outside_workspace: true,
        prestate: signed_snapshot.evidence(),
        before_submission: before_submission.evidence(),
        programdata_closed_or_system_dust_before_signing: true,
        programdata_dust_lamports_before_signing: programdata_dust_signed,
        proof_account_closed_or_system_dust_before_signing: true,
        proof_account_dust_lamports_before_signing: proof_dust_signed,
        payer_inbound_lamports_before_submission: payer_inbound_presubmit,
        recipient_inbound_lamports_before_submission: recipient_inbound_presubmit,
        program_inbound_lamports_before_submission: program_inbound_presubmit,
        programdata_dust_lamports_before_submission: programdata_dust_presubmit,
        programdata_inbound_dust_before_submission_lamports: programdata_inbound_presubmit,
        proof_account_dust_lamports_before_submission: proof_dust_presubmit,
        proof_account_inbound_dust_before_submission_lamports: proof_inbound_presubmit,
        fee_reserve_lamports: config.fee_reserve_lamports,
        quoted_fee_lamports,
        transfer_lamports,
        expected_payer_post_lamports_without_concurrent_inflow: 0,
        expected_signature: expected_signature.to_string(),
        recent_blockhash: recent_blockhash.to_string(),
        last_valid_block_height,
        signed_wire_base64: BASE64.encode(&wire),
        signed_wire_bytes: wire.len(),
        signed_wire_sha256: wire_sha256.clone(),
        message_sha256,
        exact_single_system_transfer_validated: true,
        pin_reread_before_signing_exact: true,
        pin_reread_before_submission_exact: true,
        prestate_reread_before_submission_donation_only: true,
        simulation: simulation.evidence(),
        submission_performed_when_written: false,
        postsubmit_evidence_path: postsubmit_path.display().to_string(),
    };
    let presubmit_receipt = commit_immutable_new(&presubmit_path, &presubmit)?;

    rpc.send_exact_once(&wire, &expected_signature)?;
    let finalized_slot = rpc.wait_finalized(&expected_signature)?;
    let finalized = rpc.finalized_transaction(&expected_signature, finalized_slot)?;
    ensure!(
        finalized.wire == wire,
        "landed payer-sweep wire differs from immutable presubmit artifact"
    );
    let landed: VersionedTransaction =
        bincode::deserialize(&finalized.wire).context("decode finalized payer sweep")?;
    let landed_message_identical_to_signed_message = landed.message
        == VersionedMessage::Legacy(transaction.message.clone())
        && landed.signatures == transaction.signatures;
    ensure!(
        landed_message_identical_to_signed_message,
        "landed payer-sweep signatures or message differ from signed bytes"
    );
    let balances = reconcile_sweep(
        &transaction.message.account_keys,
        &finalized.pre_balances,
        &finalized.post_balances,
        finalized.fee_lamports,
        &payer.pubkey(),
        &pinned.pubkey,
        payer_balance,
        transfer_lamports,
    )?;
    let landed_fee_equals_quote = finalized.fee_lamports == quoted_fee_lamports;
    let postfinality_snapshot = rpc.snapshot(&addresses, Some(finalized_slot))?;
    let postfinality_balances = validate_postfinality_state(
        &before_submission,
        &postfinality_snapshot,
        &balances,
        &payer.pubkey(),
        &pinned.pubkey,
        &config.expected_program_id,
        &programdata,
        &config.expected_proof_account,
    )?;
    let postsubmit = PostsubmitEvidence {
        artifact: "aspis_v5_mainnet_payer_sweep_postsubmit",
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        network_genesis_hash: observed_genesis,
        rpc_origin_redacted: config.rpc_origin_redacted,
        presubmit_evidence_path: presubmit_receipt.path.clone(),
        presubmit_evidence_sha256: presubmit_receipt.sha256.clone(),
        presubmit_evidence_bytes: presubmit_receipt.bytes,
        presubmit_evidence_mode: presubmit_receipt.mode,
        signature: expected_signature.to_string(),
        finalized_slot,
        block_time: finalized.block_time,
        landed_wire_sha256: sha256(&finalized.wire),
        landed_wire_identical_to_presubmit_artifact: true,
        landed_message_identical_to_signed_message,
        landed_compute_units_consumed: finalized.compute_units,
        landed_logs_sha256: joined_logs_sha256(&finalized.logs),
        quoted_fee_lamports,
        landed_fee_lamports: finalized.fee_lamports,
        landed_fee_equals_quote,
        balances: balances.clone(),
        postfinality_snapshot: postfinality_snapshot.evidence(),
        postfinality_balances,
        post_landing_dust_does_not_change_landed_reconciliation: true,
    };
    let postsubmit_receipt = postsubmit_reservation.commit(&postsubmit)?;
    ensure!(
        landed_fee_equals_quote && balances.signed_snapshot_balance_fully_swept,
        "payer sweep finalized but did not transfer the signed-snapshot balance net of the finalized fee to the pinned recipient; inspect immutable evidence before any retry"
    );
    Ok(SweepOutcome {
        signature: expected_signature.to_string(),
        finalized_slot,
        payer_pubkey: payer.pubkey().to_string(),
        refund_recipient_pubkey: pinned.pubkey.to_string(),
        transfer_lamports,
        fee_lamports: finalized.fee_lamports,
        payer_post_lamports: balances.payer_post_lamports,
        inbound_dust_after_signing_lamports: balances.inbound_dust_after_signing_lamports,
        signed_snapshot_balance_fully_swept: balances.signed_snapshot_balance_fully_swept,
        landed_exact_zero_balance_result: balances.landed_exact_zero_balance_result,
        presubmit_evidence: presubmit_receipt,
        postsubmit_evidence: postsubmit_receipt,
    })
}

fn validate_exact_signed_sweep(
    transaction: &Transaction,
    payer: &Pubkey,
    recipient: &Pubkey,
    transfer_lamports: u64,
    blockhash: Hash,
) -> Result<()> {
    ensure!(payer != recipient, "payer and refund recipient must differ");
    ensure!(transfer_lamports > 0, "sweep transfer must be nonzero");
    transaction
        .verify()
        .map_err(|error| anyhow!("verify signed payer sweep: {error}"))?;
    ensure!(
        transaction.signatures.len() == 1,
        "payer sweep must have exactly one signature"
    );
    let expected_instruction = system_instruction::transfer(payer, recipient, transfer_lamports);
    let expected_message = solana_sdk::message::Message::new_with_blockhash(
        &[expected_instruction],
        Some(payer),
        &blockhash,
    );
    ensure!(
        transaction.message == expected_message,
        "signed message is not the exact single pinned System transfer"
    );
    ensure!(
        transaction.message.account_keys.len() == 3
            && transaction.message.account_keys[0] == *payer
            && transaction.message.account_keys[1] == *recipient
            && transaction.message.account_keys[2] == system_program::id(),
        "signed payer-sweep account keys differ from payer, pin, System Program"
    );
    ensure!(
        transaction.message.header.num_required_signatures == 1
            && transaction.message.header.num_readonly_signed_accounts == 0
            && transaction.message.header.num_readonly_unsigned_accounts == 1,
        "signed payer-sweep account privileges differ from the exact policy"
    );
    ensure!(
        transaction.message.instructions.len() == 1,
        "payer sweep must contain exactly one instruction"
    );
    Ok(())
}

fn validate_landed_tag67(
    wire: &[u8],
    program: &Pubkey,
    proof: &Pubkey,
    payer: &Pubkey,
) -> Result<()> {
    let transaction: VersionedTransaction =
        bincode::deserialize(wire).context("decode finalized Tag-67 transaction")?;
    let message = match &transaction.message {
        VersionedMessage::Legacy(message) => message,
        VersionedMessage::V0(_) => {
            bail!("V5 Tag-67 transaction must use the pinned legacy message")
        }
    };
    ensure!(
        message.account_keys.first() == Some(payer),
        "Tag-67 transaction payer differs from the dedicated V5 payer"
    );
    let mut matches = message.instructions.iter().filter(|instruction| {
        message
            .account_keys
            .get(usize::from(instruction.program_id_index))
            == Some(program)
            && instruction.data.first() == Some(&67)
    });
    let instruction = matches
        .next()
        .context("finalized transaction contains no canonical Tag-67 instruction")?;
    ensure!(
        matches.next().is_none(),
        "finalized transaction contains more than one Tag-67 instruction"
    );
    validate_tag67_proof_role(message, instruction, proof, payer)
}

fn validate_tag67_proof_role(
    message: &solana_sdk::message::Message,
    instruction: &CompiledInstruction,
    proof: &Pubkey,
    payer: &Pubkey,
) -> Result<()> {
    ensure!(
        instruction.data.len() == 169,
        "Tag-67 instruction length differs from the frozen wire"
    );
    ensure!(
        instruction.accounts.len() == 5,
        "Tag-67 instruction account count differs from the frozen wire"
    );
    let account = |position: usize| -> Result<(usize, Pubkey)> {
        let index = usize::from(
            *instruction
                .accounts
                .get(position)
                .context("Tag-67 instruction account position missing")?,
        );
        let key = *message
            .account_keys
            .get(index)
            .context("Tag-67 instruction account index is out of range")?;
        Ok((index, key))
    };
    let (proof_index, landed_proof) = account(0)?;
    let (_, landed_payer) = account(3)?;
    let (_, landed_system_program) = account(4)?;
    ensure!(
        landed_proof == *proof && landed_payer == *payer,
        "Tag-67 transaction does not use the expected proof and payer roles"
    );
    ensure!(
        landed_system_program == system_program::id(),
        "Tag-67 transaction System Program role differs from the frozen instruction"
    );
    let required_signatures = usize::from(message.header.num_required_signatures);
    let readonly_unsigned = usize::from(message.header.num_readonly_unsigned_accounts);
    let readonly_unsigned_start = message
        .account_keys
        .len()
        .checked_sub(readonly_unsigned)
        .context("Tag-67 message readonly-account header is invalid")?;
    ensure!(
        proof_index >= required_signatures && proof_index >= readonly_unsigned_start,
        "Tag-67 proof role must be a readonly non-signer"
    );
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn reconcile_sweep(
    account_keys: &[Pubkey],
    pre_balances: &[u64],
    post_balances: &[u64],
    fee_lamports: u64,
    payer: &Pubkey,
    recipient: &Pubkey,
    signed_snapshot_payer_lamports: u64,
    transfer_lamports: u64,
) -> Result<SweepBalanceEvidence> {
    ensure!(
        account_keys.len() == pre_balances.len() && account_keys.len() == post_balances.len(),
        "finalized balance arrays do not match signed message accounts"
    );
    let index = |address: &Pubkey| {
        account_keys
            .iter()
            .position(|candidate| candidate == address)
            .with_context(|| format!("payer sweep omitted account {address}"))
    };
    let payer_index = index(payer)?;
    let recipient_index = index(recipient)?;
    ensure!(
        payer_index != recipient_index,
        "payer and recipient indices alias"
    );
    let payer_pre = pre_balances[payer_index];
    let payer_post = post_balances[payer_index];
    let recipient_pre = pre_balances[recipient_index];
    let recipient_post = post_balances[recipient_index];
    let payer_pre_matches_signed_snapshot = payer_pre == signed_snapshot_payer_lamports;
    let inbound_dust_after_signing_lamports = payer_pre
        .checked_sub(signed_snapshot_payer_lamports)
        .context("landed payer pre-balance fell below the signed snapshot")?;
    let payer_pre_at_least_signed_snapshot = true;
    let payer_debit_equals_transfer_plus_fee = payer_pre
        .checked_sub(payer_post)
        .and_then(|debit| {
            transfer_lamports
                .checked_add(fee_lamports)
                .map(|total| debit == total)
        })
        .unwrap_or(false);
    let recipient_credit_equals_transfer = recipient_post
        .checked_sub(recipient_pre)
        .is_some_and(|credit| credit == transfer_lamports);
    let payer_post_is_zero = payer_post == 0;
    let payer_post_equals_inbound_dust_after_signing =
        payer_post == inbound_dust_after_signing_lamports;
    let every_other_message_account_balance_unchanged = pre_balances
        .iter()
        .zip(post_balances)
        .enumerate()
        .all(|(index, (pre, post))| {
            index == payer_index || index == recipient_index || pre == post
        });
    let signed_snapshot_balance_fully_swept = payer_pre_at_least_signed_snapshot
        && payer_debit_equals_transfer_plus_fee
        && recipient_credit_equals_transfer
        && payer_post_equals_inbound_dust_after_signing
        && every_other_message_account_balance_unchanged;
    let landed_exact_zero_balance_result = signed_snapshot_balance_fully_swept
        && payer_pre_matches_signed_snapshot
        && payer_post_is_zero;
    Ok(SweepBalanceEvidence {
        payer_account_index: payer_index,
        refund_recipient_account_index: recipient_index,
        payer_pre_lamports: payer_pre,
        payer_post_lamports: payer_post,
        refund_recipient_pre_lamports: recipient_pre,
        refund_recipient_post_lamports: recipient_post,
        transfer_lamports,
        fee_lamports,
        payer_pre_matches_signed_snapshot,
        payer_pre_at_least_signed_snapshot,
        inbound_dust_after_signing_lamports,
        payer_debit_equals_transfer_plus_fee,
        recipient_credit_equals_transfer,
        payer_post_is_zero,
        payer_post_equals_inbound_dust_after_signing,
        signed_snapshot_balance_fully_swept,
        every_other_message_account_balance_unchanged,
        landed_exact_zero_balance_result,
    })
}

fn closed_or_system_dust_lamports(
    snapshot: &CoherentSnapshot,
    address: &Pubkey,
    label: &str,
) -> Result<u64> {
    match snapshot.account(address)? {
        None => Ok(0),
        Some(account)
            if account.owner == system_program::id()
                && !account.executable
                && account.data.is_empty() =>
        {
            Ok(account.lamports)
        }
        Some(_) => bail!(
            "{label} was not closed: only absence or a System-owned zero-data dust account is accepted"
        ),
    }
}

fn validate_sweep_prestate(
    snapshot: &CoherentSnapshot,
    payer: &Pubkey,
    recipient: &Pubkey,
    program: &Pubkey,
    programdata: &Pubkey,
    proof_account: &Pubkey,
) -> Result<(u64, u64)> {
    ensure!(
        payer != recipient
            && payer != program
            && payer != programdata
            && payer != proof_account
            && recipient != program
            && recipient != programdata
            && recipient != proof_account
            && program != programdata
            && program != proof_account
            && programdata != proof_account
    );
    ensure!(
        payer.is_on_curve() && recipient.is_on_curve(),
        "payer and refund recipient must be on-curve wallet addresses"
    );
    let payer_account = snapshot.required(payer, "payer")?;
    ensure!(
        payer_account.owner == system_program::id()
            && !payer_account.executable
            && payer_account.data.is_empty(),
        "payer is not a plain System Program wallet"
    );
    ensure!(payer_account.lamports > 0, "payer balance is zero");
    let recipient_account = snapshot.required(recipient, "refund recipient")?;
    ensure!(
        recipient_account.owner == system_program::id()
            && !recipient_account.executable
            && recipient_account.data.is_empty(),
        "refund recipient is not an existing plain System Program wallet"
    );
    let program_account = snapshot.required(program, "canonical V5 Program")?;
    validate_exact_program_account(
        &LoaderAccountImage {
            address: *program,
            owner: program_account.owner,
            executable: program_account.executable,
            data: &program_account.data,
        },
        program,
    )
    .context("canonical V5 Program account is not the retained loader-v3 Program image")?;
    let programdata_dust = closed_or_system_dust_lamports(snapshot, programdata, "ProgramData")?;
    let proof_dust =
        closed_or_system_dust_lamports(snapshot, proof_account, "sealed proof account")?;
    Ok((programdata_dust, proof_dust))
}

#[allow(clippy::too_many_arguments)]
fn validate_donation_only_snapshot_change(
    signed: &CoherentSnapshot,
    later: &CoherentSnapshot,
    payer: &Pubkey,
    recipient: &Pubkey,
    program: &Pubkey,
    programdata: &Pubkey,
    proof_account: &Pubkey,
) -> Result<(u64, u64, u64, u64, u64)> {
    ensure!(
        later.context_slot >= signed.context_slot,
        "pre-submission snapshot is older than the signed snapshot"
    );
    ensure!(
        later.addresses == signed.addresses,
        "pre-submission snapshot address order changed"
    );
    let donation_only = |address: &Pubkey, label: &str| -> Result<u64> {
        let before = signed.required(address, label)?;
        let after = later.required(address, label)?;
        ensure!(
            before.owner == after.owner
                && before.executable == after.executable
                && before.data == after.data,
            "{label} owner, executable flag, or data changed after signing"
        );
        after
            .lamports
            .checked_sub(before.lamports)
            .with_context(|| format!("{label} balance decreased after signing"))
    };
    let payer_inbound = donation_only(payer, "payer")?;
    let recipient_inbound = donation_only(recipient, "refund recipient")?;
    let program_inbound = donation_only(program, "canonical V5 Program")?;

    let signed_programdata = closed_or_system_dust_lamports(signed, programdata, "ProgramData")?;
    let later_programdata = closed_or_system_dust_lamports(later, programdata, "ProgramData")?;
    let programdata_inbound = later_programdata
        .checked_sub(signed_programdata)
        .context("ProgramData dust balance decreased after signing")?;
    let signed_proof =
        closed_or_system_dust_lamports(signed, proof_account, "sealed proof account")?;
    let later_proof = closed_or_system_dust_lamports(later, proof_account, "sealed proof account")?;
    let proof_inbound = later_proof
        .checked_sub(signed_proof)
        .context("proof-account dust balance decreased after signing")?;
    Ok((
        payer_inbound,
        recipient_inbound,
        program_inbound,
        programdata_inbound,
        proof_inbound,
    ))
}

#[allow(clippy::too_many_arguments)]
fn validate_postfinality_state(
    before_submission: &CoherentSnapshot,
    snapshot: &CoherentSnapshot,
    landed: &SweepBalanceEvidence,
    payer: &Pubkey,
    recipient: &Pubkey,
    program: &Pubkey,
    programdata: &Pubkey,
    proof_account: &Pubkey,
) -> Result<PostfinalityBalanceEvidence> {
    ensure!(
        snapshot.context_slot >= before_submission.context_slot,
        "post-finality snapshot is older than the pre-submission snapshot"
    );
    ensure!(
        snapshot.addresses == before_submission.addresses,
        "post-finality snapshot address order changed"
    );
    let payer_lamports = closed_or_system_dust_lamports(snapshot, payer, "swept payer")?;
    let payer_inbound_after_landing = payer_lamports
        .checked_sub(landed.payer_post_lamports)
        .context("current payer balance fell below the finalized transaction residual")?;
    let recipient_account = snapshot.required(recipient, "refund recipient")?;
    ensure!(
        recipient_account.owner == system_program::id()
            && !recipient_account.executable
            && recipient_account.data.is_empty(),
        "refund recipient is no longer a plain System Program wallet"
    );
    let recipient_inbound_after_landing = recipient_account
        .lamports
        .checked_sub(landed.refund_recipient_post_lamports)
        .context("refund-recipient balance fell below the finalized transaction post-balance")?;
    let program_before =
        before_submission.required(program, "pre-submission canonical V5 Program")?;
    let program_account = snapshot.required(program, "canonical V5 Program")?;
    ensure!(
        program_account.owner == program_before.owner
            && program_account.executable == program_before.executable
            && program_account.data == program_before.data,
        "canonical V5 Program owner, executable flag, or data changed after submission"
    );
    validate_exact_program_account(
        &LoaderAccountImage {
            address: *program,
            owner: program_account.owner,
            executable: program_account.executable,
            data: &program_account.data,
        },
        program,
    )
    .context("canonical V5 Program account changed after the payer sweep")?;
    let program_inbound_after_submission = program_account
        .lamports
        .checked_sub(program_before.lamports)
        .context("canonical V5 Program balance decreased after submission")?;
    let programdata_before =
        closed_or_system_dust_lamports(before_submission, programdata, "ProgramData")?;
    let programdata_dust = closed_or_system_dust_lamports(snapshot, programdata, "ProgramData")?;
    let programdata_inbound_after_submission = programdata_dust
        .checked_sub(programdata_before)
        .context("ProgramData dust balance decreased after submission")?;
    let proof_before =
        closed_or_system_dust_lamports(before_submission, proof_account, "sealed proof account")?;
    let proof_dust =
        closed_or_system_dust_lamports(snapshot, proof_account, "sealed proof account")?;
    let proof_inbound_after_submission = proof_dust
        .checked_sub(proof_before)
        .context("proof-account dust balance decreased after submission")?;
    Ok(PostfinalityBalanceEvidence {
        landed_payer_residual_lamports: landed.payer_post_lamports,
        current_payer_lamports: payer_lamports,
        payer_inbound_after_landing_lamports: payer_inbound_after_landing,
        landed_refund_recipient_post_lamports: landed.refund_recipient_post_lamports,
        current_refund_recipient_lamports: recipient_account.lamports,
        refund_recipient_inbound_after_landing_lamports: recipient_inbound_after_landing,
        presubmit_program_lamports: program_before.lamports,
        current_program_lamports: program_account.lamports,
        program_inbound_after_submission_lamports: program_inbound_after_submission,
        presubmit_programdata_dust_lamports: programdata_before,
        current_programdata_dust_lamports: programdata_dust,
        programdata_inbound_after_submission_lamports: programdata_inbound_after_submission,
        presubmit_proof_account_dust_lamports: proof_before,
        current_proof_account_dust_lamports: proof_dust,
        proof_account_inbound_after_submission_lamports: proof_inbound_after_submission,
    })
}

fn read_pinned_recipient(path: &Path) -> Result<PinnedRecipient> {
    ensure!(
        path.is_absolute(),
        "refund-recipient pin path must be absolute"
    );
    let workspace = workspace_root()?.canonicalize()?;
    let canonical = path
        .canonicalize()
        .with_context(|| format!("canonicalize refund-recipient pin {}", path.display()))?;
    ensure!(
        canonical == path,
        "refund-recipient pin path must contain no symlink or relative components"
    );
    ensure!(
        !canonical.starts_with(&workspace),
        "refund-recipient pin must live outside the workspace"
    );
    let metadata = fs::symlink_metadata(path)
        .with_context(|| format!("refund-recipient pin unavailable: {}", path.display()))?;
    ensure!(
        metadata.file_type().is_file() && !metadata.file_type().is_symlink(),
        "refund-recipient pin must be a regular non-symlink file"
    );
    let mode = metadata.permissions().mode() & 0o777;
    ensure!(
        mode == 0o400 || mode == 0o600,
        "refund-recipient pin mode must be exactly 0400 or 0600"
    );
    let mut file = fs::File::open(path)
        .with_context(|| format!("open refund-recipient pin {}", path.display()))?;
    let opened_metadata = file
        .metadata()
        .with_context(|| format!("stat opened refund-recipient pin {}", path.display()))?;
    ensure!(
        opened_metadata.file_type().is_file()
            && opened_metadata.dev() == metadata.dev()
            && opened_metadata.ino() == metadata.ino()
            && opened_metadata.permissions().mode() & 0o777 == mode,
        "refund-recipient pin changed while opening"
    );
    let mut raw_bytes = Vec::new();
    file.read_to_end(&mut raw_bytes)
        .with_context(|| format!("read refund-recipient pin {}", path.display()))?;
    ensure!(
        !raw_bytes.is_empty() && raw_bytes.len() <= 128,
        "refund-recipient pin has an invalid byte length"
    );
    let text = std::str::from_utf8(&raw_bytes).context("refund-recipient pin is not UTF-8")?;
    let body = text
        .strip_suffix("\r\n")
        .or_else(|| text.strip_suffix('\n'))
        .unwrap_or(text);
    ensure!(
        !body.is_empty()
            && body == body.trim()
            && !body.contains('\n')
            && !body.contains('\r')
            && !body.chars().any(char::is_whitespace),
        "refund-recipient pin must contain exactly one base58 pubkey"
    );
    let pubkey = body
        .parse::<Pubkey>()
        .context("refund-recipient pin is not a pubkey")?;
    ensure!(
        pubkey.is_on_curve(),
        "refund-recipient pin must be an on-curve wallet address"
    );
    ensure!(
        pubkey != system_program::id(),
        "System Program cannot be the refund recipient"
    );
    Ok(PinnedRecipient {
        pubkey,
        raw_sha256: sha256(&raw_bytes),
        raw_bytes,
        mode,
        uid: opened_metadata.uid(),
    })
}

fn workspace_root() -> Result<PathBuf> {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .map(Path::to_path_buf)
        .context("xtask manifest has no workspace parent")
}

fn parse_coherent_snapshot(result: &Value, addresses: &[Pubkey]) -> Result<CoherentSnapshot> {
    ensure!(!addresses.is_empty(), "snapshot address list is empty");
    let context_slot = result["context"]["slot"]
        .as_u64()
        .context("getMultipleAccounts omitted context.slot")?;
    let values = result["value"]
        .as_array()
        .context("getMultipleAccounts omitted value array")?;
    ensure!(
        values.len() == addresses.len(),
        "getMultipleAccounts result length mismatch"
    );
    let accounts = values
        .iter()
        .map(parse_optional_rpc_account)
        .collect::<Result<Vec<_>>>()?;
    Ok(CoherentSnapshot {
        context_slot,
        addresses: addresses.to_vec(),
        accounts,
    })
}

fn parse_optional_rpc_account(value: &Value) -> Result<Option<RpcAccount>> {
    if value.is_null() {
        return Ok(None);
    }
    let data = value["data"]
        .as_array()
        .context("account data was not an encoding tuple")?;
    ensure!(data.len() == 2 && data[1].as_str() == Some("base64"));
    Ok(Some(RpcAccount {
        lamports: value["lamports"]
            .as_u64()
            .context("account lamports missing")?,
        owner: value["owner"]
            .as_str()
            .context("account owner missing")?
            .parse()
            .context("account owner invalid")?,
        executable: value["executable"]
            .as_bool()
            .context("account executable flag missing")?,
        data: BASE64.decode(data[0].as_str().context("account base64 payload missing")?)?,
    }))
}

fn parse_simulation(result: &Value) -> Result<Simulation> {
    let value = result.get("value").context("simulation omitted value")?;
    let error = value.get("err").context("simulation omitted err")?;
    let logs = value["logs"]
        .as_array()
        .context("simulation omitted logs")?
        .iter()
        .map(|line| {
            line.as_str()
                .map(ToOwned::to_owned)
                .context("simulation log was not a string")
        })
        .collect::<Result<Vec<_>>>()?;
    Ok(Simulation {
        context_slot: result["context"]["slot"]
            .as_u64()
            .context("simulation omitted context slot")?,
        error: (!error.is_null()).then(|| error.clone()),
        units: value["unitsConsumed"]
            .as_u64()
            .context("simulation omitted unitsConsumed")?,
        logs,
    })
}

fn parse_signature_status(result: &Value) -> Result<Option<(u64, bool, Option<Value>)>> {
    let values = result
        .get("value")
        .context("signature statuses omitted value")?
        .as_array()
        .context("signature statuses omitted value array")?;
    ensure!(values.len() == 1, "signature status length mismatch");
    let value = &values[0];
    if value.is_null() {
        return Ok(None);
    }
    let confirmation_status = value
        .get("confirmationStatus")
        .context("signature status omitted confirmationStatus")?;
    ensure!(
        confirmation_status.is_null() || confirmation_status.is_string(),
        "signature confirmationStatus had an invalid type"
    );
    let error = value.get("err").context("signature status omitted err")?;
    Ok(Some((
        value["slot"]
            .as_u64()
            .context("signature status omitted slot")?,
        confirmation_status.as_str() == Some("finalized"),
        (!error.is_null()).then(|| error.clone()),
    )))
}

fn parse_finalized_transaction(
    json_result: &Value,
    base64_result: &Value,
    expected_slot: u64,
) -> Result<FinalizedTransaction> {
    let slot = json_result["slot"]
        .as_u64()
        .context("finalized transaction omitted slot")?;
    ensure!(slot == expected_slot, "finalized transaction slot drift");
    ensure!(
        base64_result["slot"].as_u64() == Some(slot),
        "base64 transaction slot drift"
    );
    let meta = json_result
        .get("meta")
        .context("finalized transaction omitted meta")?;
    let error = meta
        .get("err")
        .context("finalized transaction omitted meta.err")?;
    ensure!(error.is_null(), "finalized payer sweep failed: {error}");
    let balances = |field: &str| -> Result<Vec<u64>> {
        meta[field]
            .as_array()
            .with_context(|| format!("finalized transaction omitted {field}"))?
            .iter()
            .map(|value| {
                value
                    .as_u64()
                    .with_context(|| format!("{field} contained non-u64"))
            })
            .collect()
    };
    let logs = meta["logMessages"]
        .as_array()
        .context("finalized transaction omitted logs")?
        .iter()
        .map(|line| {
            line.as_str()
                .map(ToOwned::to_owned)
                .context("finalized log was not a string")
        })
        .collect::<Result<Vec<_>>>()?;
    let transaction = base64_result["transaction"]
        .as_array()
        .context("finalized base64 transaction was not an encoding tuple")?;
    ensure!(
        transaction.len() == 2 && transaction[1].as_str() == Some("base64"),
        "finalized transaction encoding drift"
    );
    let wire = BASE64.decode(
        transaction[0]
            .as_str()
            .context("finalized base64 wire missing")?,
    )?;
    let _: VersionedTransaction =
        bincode::deserialize(&wire).context("decode landed transaction wire")?;
    Ok(FinalizedTransaction {
        block_time: json_result["blockTime"].as_i64(),
        fee_lamports: meta["fee"].as_u64().context("finalized fee missing")?,
        pre_balances: balances("preBalances")?,
        post_balances: balances("postBalances")?,
        compute_units: meta["computeUnitsConsumed"]
            .as_u64()
            .context("finalized compute units missing")?,
        logs,
        wire,
    })
}

impl CoherentSnapshot {
    fn account(&self, address: &Pubkey) -> Result<Option<&RpcAccount>> {
        let index = self
            .addresses
            .iter()
            .position(|candidate| candidate == address)
            .with_context(|| format!("snapshot omitted requested address {address}"))?;
        Ok(self.accounts[index].as_ref())
    }

    fn required(&self, address: &Pubkey, label: &str) -> Result<&RpcAccount> {
        self.account(address)?
            .with_context(|| format!("{label} is absent"))
    }

    fn evidence(&self) -> SnapshotEvidence {
        SnapshotEvidence {
            context_slot: self.context_slot,
            accounts: self
                .addresses
                .iter()
                .zip(&self.accounts)
                .map(|(address, account)| {
                    let account = account.as_ref();
                    AccountEvidence {
                        address: address.to_string(),
                        present: account.is_some(),
                        lamports: account.map(|value| value.lamports),
                        owner: account.map(|value| value.owner.to_string()),
                        executable: account.map(|value| value.executable),
                        data_len: account.map(|value| value.data.len()),
                        data_sha256: account.map(|value| sha256(&value.data)),
                    }
                })
                .collect(),
        }
    }
}

impl Simulation {
    fn evidence(&self) -> SimulationEvidence {
        SimulationEvidence {
            exact_signed_wire_simulated: true,
            context_slot: self.context_slot,
            error: self.error.clone(),
            compute_units_consumed: self.units,
            logs_sha256: joined_logs_sha256(&self.logs),
        }
    }
}

fn secure_keypair(path: &Path) -> Result<Keypair> {
    ensure!(path.is_absolute(), "payer keypair path must be absolute");
    let metadata = fs::symlink_metadata(path)
        .with_context(|| format!("payer keypair unavailable: {}", path.display()))?;
    ensure!(
        metadata.file_type().is_file() && !metadata.file_type().is_symlink(),
        "payer keypair must be a regular non-symlink file"
    );
    let mode = metadata.permissions().mode() & 0o777;
    ensure!(
        mode == 0o400 || mode == 0o600,
        "payer keypair mode must be exactly 0400 or 0600"
    );
    read_keypair_file(path).map_err(|_| anyhow!("could not decode payer keypair"))
}

fn explicit_https_rpc(endpoint: &str) -> Result<String> {
    let url = reqwest::Url::parse(endpoint).context("RPC URL is invalid")?;
    ensure!(url.scheme() == "https", "payer-sweep RPC must use HTTPS");
    ensure!(
        url.username().is_empty() && url.password().is_none(),
        "RPC credentials must not use URL userinfo"
    );
    ensure!(
        url.fragment().is_none(),
        "RPC URL must not contain a fragment"
    );
    let host = url.host_str().context("RPC URL omitted host")?;
    Ok(match url.port() {
        Some(port) => format!("https://{host}:{port}"),
        None => format!("https://{host}"),
    })
}

fn rpc_read_retryable(error: &anyhow::Error) -> bool {
    let text = error.to_string();
    text.contains("transport failure")
        || text.contains("HTTP 429")
        || text.contains("HTTP 500")
        || text.contains("HTTP 502")
        || text.contains("HTTP 503")
        || text.contains("HTTP 504")
}

fn evidence_paths(postsubmit: &Path) -> Result<(PathBuf, PathBuf)> {
    ensure!(
        postsubmit.is_absolute(),
        "payer-sweep evidence path must be absolute"
    );
    let parent = postsubmit
        .parent()
        .context("evidence path omitted parent")?;
    let filename = postsubmit
        .file_name()
        .and_then(|name| name.to_str())
        .context("evidence filename is not UTF-8")?;
    let presubmit_name = match filename.strip_suffix(".json") {
        Some(stem) => format!("{stem}.pre.json"),
        None => format!("{filename}.pre.json"),
    };
    let presubmit = parent.join(presubmit_name);
    ensure!(
        presubmit != postsubmit,
        "pre/post payer-sweep evidence paths alias"
    );
    Ok((presubmit, postsubmit.to_path_buf()))
}

fn prepare_evidence_parent(path: &Path) -> Result<()> {
    let parent = path.parent().context("evidence path omitted parent")?;
    let metadata = fs::symlink_metadata(parent)
        .with_context(|| format!("evidence parent unavailable: {}", parent.display()))?;
    ensure!(
        metadata.file_type().is_dir() && !metadata.file_type().is_symlink(),
        "evidence parent must be an existing non-symlink directory"
    );
    Ok(())
}

fn serialized_json(value: &impl Serialize) -> Result<Vec<u8>> {
    let mut bytes = serde_json::to_vec_pretty(value)?;
    bytes.push(b'\n');
    Ok(bytes)
}

fn write_synced_json(file: &mut fs::File, value: &impl Serialize) -> Result<()> {
    file.write_all(&serialized_json(value)?)?;
    file.sync_all()?;
    Ok(())
}

fn sync_parent(path: &Path) -> Result<()> {
    fs::File::open(path.parent().context("path omitted parent")?)?.sync_all()?;
    Ok(())
}

fn commit_immutable_new(path: &Path, value: &impl Serialize) -> Result<EvidenceReceipt> {
    prepare_evidence_parent(path)?;
    let bytes = serialized_json(value)?;
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(path)
        .with_context(|| format!("create immutable evidence {}", path.display()))?;
    file.write_all(&bytes)?;
    file.sync_all()?;
    let mut permissions = file.metadata()?.permissions();
    permissions.set_mode(0o444);
    fs::set_permissions(path, permissions)?;
    file.sync_all()?;
    sync_parent(path)?;
    immutable_receipt(path)
}

fn immutable_receipt(path: &Path) -> Result<EvidenceReceipt> {
    let metadata = fs::symlink_metadata(path)?;
    ensure!(
        metadata.file_type().is_file()
            && !metadata.file_type().is_symlink()
            && metadata.permissions().mode() & 0o777 == 0o444,
        "evidence is not an immutable mode-0444 regular file"
    );
    let bytes = fs::read(path)?;
    Ok(EvidenceReceipt {
        path: path.display().to_string(),
        sha256: sha256(&bytes),
        bytes: bytes.len(),
        mode: 0o444,
    })
}

fn sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn joined_logs_sha256(logs: &[String]) -> String {
    sha256(logs.join("\n").as_bytes())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        os::unix::fs::{symlink, PermissionsExt},
        sync::atomic::{AtomicU64, Ordering},
    };

    static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

    struct TempDir(PathBuf);

    impl TempDir {
        fn new() -> Self {
            let suffix = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "aspis-v5-mainnet-refund-test-{}-{suffix}",
                std::process::id()
            ));
            fs::create_dir(&path).unwrap();
            Self(path.canonicalize().unwrap())
        }

        fn path(&self) -> &Path {
            &self.0
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn valid_args(root: &Path, payer: Pubkey) -> Vec<String> {
        let tag67_signature = Keypair::new().sign_message(b"test Tag-67 transaction");
        vec![
            "--execute-mainnet-payer-sweep".to_owned(),
            "--rpc-url".to_owned(),
            "https://rpc.example.invalid/?api-key=secret".to_owned(),
            "--payer-keypair".to_owned(),
            root.join("payer.json").display().to_string(),
            "--expected-payer-pubkey".to_owned(),
            payer.to_string(),
            "--expected-program-id".to_owned(),
            aspis_verifier::id().to_string(),
            "--expected-proof-account".to_owned(),
            Keypair::new().pubkey().to_string(),
            "--expected-tag67-signature".to_owned(),
            tag67_signature.to_string(),
            "--refund-recipient-pubkey-file".to_owned(),
            root.join("refund.pubkey").display().to_string(),
            "--expected-refund-pin-sha256".to_owned(),
            "0".repeat(64),
            "--fee-reserve-lamports".to_owned(),
            "100000".to_owned(),
            "--evidence".to_owned(),
            root.join("sweep.json").display().to_string(),
            "--expected-genesis".to_owned(),
            MAINNET_BETA_GENESIS_HASH.to_owned(),
            "--acknowledgement".to_owned(),
            EXECUTE_ACKNOWLEDGEMENT.to_owned(),
        ]
    }

    fn write_mode(path: &Path, bytes: &[u8], mode: u32) {
        fs::write(path, bytes).unwrap();
        fs::set_permissions(path, fs::Permissions::from_mode(mode)).unwrap();
    }

    #[test]
    fn parser_requires_exact_mainnet_interlock_paths_payer_and_fee_reserve() {
        let root = TempDir::new();
        let payer = Pubkey::new_unique();
        let args = valid_args(root.path(), payer);
        let parsed = parse_args(&args).unwrap();
        assert_eq!(parsed.expected_payer_pubkey, payer);
        assert_eq!(parsed.fee_reserve_lamports, 100_000);
        assert_eq!(parsed.rpc_origin_redacted, "https://rpc.example.invalid");

        let mut missing_interlock = args.clone();
        missing_interlock.remove(0);
        assert!(parse_args(&missing_interlock).is_err());
        let mut bad_ack = args.clone();
        let ack = bad_ack
            .iter()
            .position(|value| value == "--acknowledgement")
            .unwrap();
        bad_ack[ack + 1] = "no".to_owned();
        assert!(parse_args(&bad_ack).is_err());
        let mut bad_genesis = args.clone();
        let genesis = bad_genesis
            .iter()
            .position(|value| value == "--expected-genesis")
            .unwrap();
        bad_genesis[genesis + 1] = Hash::new_unique().to_string();
        assert!(parse_args(&bad_genesis).is_err());
        let mut no_reserve = args;
        let reserve = no_reserve
            .iter()
            .position(|value| value == "--fee-reserve-lamports")
            .unwrap();
        no_reserve[reserve + 1] = "0".to_owned();
        assert!(parse_args(&no_reserve).is_err());

        let mut malformed_pin_hash = valid_args(root.path(), payer);
        let pin_hash = malformed_pin_hash
            .iter()
            .position(|value| value == "--expected-refund-pin-sha256")
            .unwrap();
        malformed_pin_hash[pin_hash + 1] = "not-a-hash".to_owned();
        assert!(parse_args(&malformed_pin_hash).is_err());
    }

    #[test]
    fn local_pin_accepts_only_owner_only_regular_file_outside_workspace() {
        let root = TempDir::new();
        let recipient = Keypair::new().pubkey();
        let pin = root.path().join("refund.pubkey");
        write_mode(&pin, format!("{recipient}\n").as_bytes(), 0o400);
        let parsed = read_pinned_recipient(&pin).unwrap();
        assert_eq!(parsed.pubkey, recipient);
        assert_eq!(parsed.mode, 0o400);

        fs::set_permissions(&pin, fs::Permissions::from_mode(0o600)).unwrap();
        assert_eq!(read_pinned_recipient(&pin).unwrap().mode, 0o600);
        fs::set_permissions(&pin, fs::Permissions::from_mode(0o644)).unwrap();
        assert!(read_pinned_recipient(&pin).is_err());

        let target = root.path().join("target.pubkey");
        write_mode(&target, recipient.to_string().as_bytes(), 0o400);
        let link = root.path().join("link.pubkey");
        symlink(&target, &link).unwrap();
        assert!(read_pinned_recipient(&link).is_err());

        let workspace_path = workspace_root().unwrap().join("not-a-real-refund-pin");
        assert!(read_pinned_recipient(&workspace_path).is_err());
    }

    #[test]
    fn pin_parser_rejects_multiple_values_and_off_curve_addresses() {
        let root = TempDir::new();
        let first = Keypair::new().pubkey();
        let second = Keypair::new().pubkey();
        let pin = root.path().join("refund.pubkey");
        write_mode(&pin, format!("{first}\n{second}\n").as_bytes(), 0o400);
        assert!(read_pinned_recipient(&pin).is_err());

        // A PDA is deliberately off curve and cannot be a wallet destination.
        let off_curve = Pubkey::find_program_address(&[b"refund-test"], &Pubkey::new_unique()).0;
        fs::set_permissions(&pin, fs::Permissions::from_mode(0o600)).unwrap();
        write_mode(&pin, off_curve.to_string().as_bytes(), 0o400);
        assert!(read_pinned_recipient(&pin).is_err());
    }

    #[test]
    fn signed_sweep_is_exactly_one_system_transfer_to_pin() {
        let payer = Keypair::new();
        let recipient = Keypair::new().pubkey();
        let blockhash = Hash::new_unique();
        let transfer = 7_184_879_880;
        let transaction = Transaction::new_signed_with_payer(
            &[system_instruction::transfer(
                &payer.pubkey(),
                &recipient,
                transfer,
            )],
            Some(&payer.pubkey()),
            &[&payer],
            blockhash,
        );
        validate_exact_signed_sweep(
            &transaction,
            &payer.pubkey(),
            &recipient,
            transfer,
            blockhash,
        )
        .unwrap();

        let wrong = Keypair::new().pubkey();
        assert!(validate_exact_signed_sweep(
            &transaction,
            &payer.pubkey(),
            &wrong,
            transfer,
            blockhash
        )
        .is_err());
        assert!(validate_exact_signed_sweep(
            &transaction,
            &payer.pubkey(),
            &recipient,
            transfer - 1,
            blockhash
        )
        .is_err());
    }

    #[test]
    fn finalized_tag67_transaction_binds_the_expected_readonly_proof_and_payer() {
        use solana_sdk::instruction::{AccountMeta, Instruction};

        let payer = Keypair::new();
        let proof = Pubkey::new_unique();
        let pool = Pubkey::new_unique();
        let spent_marker = Pubkey::new_unique();
        let mut data = vec![0u8; 169];
        data[0] = 67;
        let instruction = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![
                AccountMeta::new_readonly(proof, false),
                AccountMeta::new(pool, false),
                AccountMeta::new(spent_marker, false),
                AccountMeta::new(payer.pubkey(), true),
                AccountMeta::new_readonly(system_program::id(), false),
            ],
            data,
        };
        let transaction = Transaction::new_signed_with_payer(
            &[instruction],
            Some(&payer.pubkey()),
            &[&payer],
            Hash::new_unique(),
        );
        let wire = bincode::serialize(&VersionedTransaction::from(transaction)).unwrap();
        validate_landed_tag67(&wire, &aspis_verifier::id(), &proof, &payer.pubkey()).unwrap();
        assert!(validate_landed_tag67(
            &wire,
            &aspis_verifier::id(),
            &Pubkey::new_unique(),
            &payer.pubkey(),
        )
        .is_err());
    }

    #[test]
    fn reconciliation_sweeps_signed_balance_and_classifies_concurrent_dust() {
        let payer = Keypair::new().pubkey();
        let recipient = Keypair::new().pubkey();
        let keys = [payer, recipient, system_program::id()];
        let exact = reconcile_sweep(
            &keys,
            &[7_184_884_880, 12, 1],
            &[0, 7_184_879_892, 1],
            5_000,
            &payer,
            &recipient,
            7_184_884_880,
            7_184_879_880,
        )
        .unwrap();
        assert!(exact.landed_exact_zero_balance_result);
        assert!(exact.signed_snapshot_balance_fully_swept);

        let dust_race = reconcile_sweep(
            &keys,
            &[7_184_894_880, 12, 1],
            &[10_000, 7_184_879_892, 1],
            5_000,
            &payer,
            &recipient,
            7_184_884_880,
            7_184_879_880,
        )
        .unwrap();
        assert!(!dust_race.payer_pre_matches_signed_snapshot);
        assert!(!dust_race.payer_post_is_zero);
        assert_eq!(dust_race.inbound_dust_after_signing_lamports, 10_000);
        assert!(dust_race.payer_post_equals_inbound_dust_after_signing);
        assert!(dust_race.signed_snapshot_balance_fully_swept);
        assert!(!dust_race.landed_exact_zero_balance_result);
    }

    #[test]
    fn sweep_prestate_requires_programdata_and_proof_rent_already_recovered() {
        use solana_sdk::bpf_loader_upgradeable::{self, UpgradeableLoaderState};

        let payer = Keypair::new().pubkey();
        let recipient = Keypair::new().pubkey();
        let program = aspis_verifier::id();
        let programdata = derive_programdata_address(&program);
        let proof = Keypair::new().pubkey();
        let wallet = |lamports| RpcAccount {
            lamports,
            owner: system_program::id(),
            executable: false,
            data: Vec::new(),
        };
        let program_account = RpcAccount {
            lamports: 1_141_440,
            owner: bpf_loader_upgradeable::id(),
            executable: true,
            data: bincode::serialize(&UpgradeableLoaderState::Program {
                programdata_address: programdata,
            })
            .unwrap(),
        };
        let addresses = vec![payer, recipient, program, programdata, proof];
        let clean = CoherentSnapshot {
            context_slot: 9,
            addresses: addresses.clone(),
            accounts: vec![
                Some(wallet(100_000)),
                Some(wallet(20_000)),
                Some(program_account.clone()),
                None,
                None,
            ],
        };
        validate_sweep_prestate(&clean, &payer, &recipient, &program, &programdata, &proof)
            .unwrap();

        let mut system_dust = clean.clone();
        system_dust.accounts[3] = Some(wallet(1));
        system_dust.accounts[4] = Some(wallet(2));
        assert_eq!(
            validate_sweep_prestate(
                &system_dust,
                &payer,
                &recipient,
                &program,
                &programdata,
                &proof,
            )
            .unwrap(),
            (1, 2)
        );

        let mut recipient_absent = clean.clone();
        recipient_absent.accounts[1] = None;
        assert!(validate_sweep_prestate(
            &recipient_absent,
            &payer,
            &recipient,
            &program,
            &programdata,
            &proof,
        )
        .is_err());

        let mut programdata_present = clean.clone();
        programdata_present.accounts[3] = Some(RpcAccount {
            lamports: 6_000_000_000,
            owner: bpf_loader_upgradeable::id(),
            executable: false,
            data: vec![0; 8],
        });
        assert!(validate_sweep_prestate(
            &programdata_present,
            &payer,
            &recipient,
            &program,
            &programdata,
            &proof,
        )
        .is_err());

        let mut proof_present = clean.clone();
        proof_present.accounts[4] = Some(RpcAccount {
            lamports: 500_000_000,
            owner: program,
            executable: false,
            data: vec![0; 8],
        });
        assert!(validate_sweep_prestate(
            &proof_present,
            &payer,
            &recipient,
            &program,
            &programdata,
            &proof,
        )
        .is_err());

        let mut proof_system_data = clean;
        proof_system_data.accounts[4] = Some(RpcAccount {
            lamports: 1,
            owner: system_program::id(),
            executable: false,
            data: vec![1],
        });
        assert!(validate_sweep_prestate(
            &proof_system_data,
            &payer,
            &recipient,
            &program,
            &programdata,
            &proof,
        )
        .is_err());
    }

    #[test]
    fn presubmit_snapshot_accepts_only_inbound_donations_and_closed_account_dust() {
        use solana_sdk::bpf_loader_upgradeable::{self, UpgradeableLoaderState};

        let payer = Keypair::new().pubkey();
        let recipient = Keypair::new().pubkey();
        let program = aspis_verifier::id();
        let programdata = derive_programdata_address(&program);
        let proof = Keypair::new().pubkey();
        let wallet = |lamports| RpcAccount {
            lamports,
            owner: system_program::id(),
            executable: false,
            data: Vec::new(),
        };
        let program_account = RpcAccount {
            lamports: 1_141_440,
            owner: bpf_loader_upgradeable::id(),
            executable: true,
            data: bincode::serialize(&UpgradeableLoaderState::Program {
                programdata_address: programdata,
            })
            .unwrap(),
        };
        let addresses = vec![payer, recipient, program, programdata, proof];
        let signed = CoherentSnapshot {
            context_slot: 10,
            addresses: addresses.clone(),
            accounts: vec![
                Some(wallet(100_000)),
                Some(wallet(20_000)),
                Some(program_account.clone()),
                None,
                None,
            ],
        };
        let later = CoherentSnapshot {
            context_slot: 11,
            addresses,
            accounts: vec![
                Some(wallet(100_001)),
                Some(wallet(20_002)),
                Some(RpcAccount {
                    lamports: program_account.lamports + 3,
                    ..program_account.clone()
                }),
                Some(wallet(4)),
                Some(wallet(5)),
            ],
        };
        assert_eq!(
            validate_donation_only_snapshot_change(
                &signed,
                &later,
                &payer,
                &recipient,
                &program,
                &programdata,
                &proof,
            )
            .unwrap(),
            (1, 2, 3, 4, 5)
        );

        let mut decreased = later.clone();
        decreased.accounts[0].as_mut().unwrap().lamports = 99_999;
        assert!(validate_donation_only_snapshot_change(
            &signed,
            &decreased,
            &payer,
            &recipient,
            &program,
            &programdata,
            &proof,
        )
        .is_err());

        let mut recipient_mutated = later.clone();
        recipient_mutated.accounts[1].as_mut().unwrap().data.push(1);
        assert!(validate_donation_only_snapshot_change(
            &signed,
            &recipient_mutated,
            &payer,
            &recipient,
            &program,
            &programdata,
            &proof,
        )
        .is_err());

        let mut program_decreased = later.clone();
        program_decreased.accounts[2].as_mut().unwrap().lamports = program_account.lamports - 1;
        assert!(validate_donation_only_snapshot_change(
            &signed,
            &program_decreased,
            &payer,
            &recipient,
            &program,
            &programdata,
            &proof,
        )
        .is_err());

        let mut program_mutated = later.clone();
        program_mutated.accounts[2].as_mut().unwrap().executable = false;
        assert!(validate_donation_only_snapshot_change(
            &signed,
            &program_mutated,
            &payer,
            &recipient,
            &program,
            &programdata,
            &proof,
        )
        .is_err());

        let mut signed_with_tombstone_dust = signed.clone();
        signed_with_tombstone_dust.accounts[3] = Some(wallet(5));
        signed_with_tombstone_dust.accounts[4] = Some(wallet(6));
        let mut tombstone_decreased = later;
        tombstone_decreased.accounts[3] = Some(wallet(4));
        tombstone_decreased.accounts[4] = Some(wallet(5));
        assert!(validate_donation_only_snapshot_change(
            &signed_with_tombstone_dust,
            &tombstone_decreased,
            &payer,
            &recipient,
            &program,
            &programdata,
            &proof,
        )
        .is_err());
    }

    #[test]
    fn postfinality_state_accepts_absent_or_redusted_closed_addresses() {
        use solana_sdk::bpf_loader_upgradeable::{self, UpgradeableLoaderState};

        let payer = Keypair::new().pubkey();
        let recipient = Keypair::new().pubkey();
        let program = aspis_verifier::id();
        let programdata = derive_programdata_address(&program);
        let proof = Keypair::new().pubkey();
        let wallet = |lamports| RpcAccount {
            lamports,
            owner: system_program::id(),
            executable: false,
            data: Vec::new(),
        };
        let program_account = RpcAccount {
            lamports: 1_141_440,
            owner: bpf_loader_upgradeable::id(),
            executable: true,
            data: bincode::serialize(&UpgradeableLoaderState::Program {
                programdata_address: programdata,
            })
            .unwrap(),
        };
        let addresses = vec![payer, recipient, program, programdata, proof];
        let before_submission = CoherentSnapshot {
            context_slot: 19,
            addresses: addresses.clone(),
            accounts: vec![
                Some(wallet(100_000)),
                Some(wallet(900_000)),
                Some(program_account.clone()),
                None,
                None,
            ],
        };
        let landed = reconcile_sweep(
            &[payer, recipient, system_program::id()],
            &[100_000, 900_000, 1],
            &[0, 995_000, 1],
            5_000,
            &payer,
            &recipient,
            100_000,
            95_000,
        )
        .unwrap();
        let mut snapshot = CoherentSnapshot {
            context_slot: 20,
            addresses,
            accounts: vec![
                None,
                Some(wallet(995_007)),
                Some(RpcAccount {
                    lamports: program_account.lamports + 3,
                    ..program_account
                }),
                Some(wallet(4)),
                Some(wallet(5)),
            ],
        };
        assert_eq!(
            validate_postfinality_state(
                &before_submission,
                &snapshot,
                &landed,
                &payer,
                &recipient,
                &program,
                &programdata,
                &proof,
            )
            .unwrap(),
            PostfinalityBalanceEvidence {
                landed_payer_residual_lamports: 0,
                current_payer_lamports: 0,
                payer_inbound_after_landing_lamports: 0,
                landed_refund_recipient_post_lamports: 995_000,
                current_refund_recipient_lamports: 995_007,
                refund_recipient_inbound_after_landing_lamports: 7,
                presubmit_program_lamports: 1_141_440,
                current_program_lamports: 1_141_443,
                program_inbound_after_submission_lamports: 3,
                presubmit_programdata_dust_lamports: 0,
                current_programdata_dust_lamports: 4,
                programdata_inbound_after_submission_lamports: 4,
                presubmit_proof_account_dust_lamports: 0,
                current_proof_account_dust_lamports: 5,
                proof_account_inbound_after_submission_lamports: 5,
            }
        );

        snapshot.accounts[0] = Some(wallet(6));
        let redusted = validate_postfinality_state(
            &before_submission,
            &snapshot,
            &landed,
            &payer,
            &recipient,
            &program,
            &programdata,
            &proof,
        )
        .unwrap();
        assert_eq!(redusted.current_payer_lamports, 6);
        assert_eq!(redusted.payer_inbound_after_landing_lamports, 6);
        snapshot.accounts[0] = Some(RpcAccount {
            lamports: 6,
            owner: program,
            executable: false,
            data: Vec::new(),
        });
        assert!(validate_postfinality_state(
            &before_submission,
            &snapshot,
            &landed,
            &payer,
            &recipient,
            &program,
            &programdata,
            &proof,
        )
        .is_err());

        let landed_with_inbound = reconcile_sweep(
            &[payer, recipient, system_program::id()],
            &[100_006, 900_000, 1],
            &[6, 995_000, 1],
            5_000,
            &payer,
            &recipient,
            100_000,
            95_000,
        )
        .unwrap();
        snapshot.accounts[0] = Some(wallet(5));
        assert!(validate_postfinality_state(
            &before_submission,
            &snapshot,
            &landed_with_inbound,
            &payer,
            &recipient,
            &program,
            &programdata,
            &proof,
        )
        .is_err());

        snapshot.accounts[0] = Some(wallet(6));
        snapshot.accounts[1] = Some(wallet(994_999));
        assert!(validate_postfinality_state(
            &before_submission,
            &snapshot,
            &landed_with_inbound,
            &payer,
            &recipient,
            &program,
            &programdata,
            &proof,
        )
        .is_err());

        snapshot.accounts[1] = Some(wallet(995_000));
        snapshot.accounts[2].as_mut().unwrap().lamports = 1_141_439;
        assert!(validate_postfinality_state(
            &before_submission,
            &snapshot,
            &landed_with_inbound,
            &payer,
            &recipient,
            &program,
            &programdata,
            &proof,
        )
        .is_err());

        let mut before_with_tombstone_dust = before_submission;
        before_with_tombstone_dust.accounts[3] = Some(wallet(10));
        before_with_tombstone_dust.accounts[4] = Some(wallet(11));
        snapshot.accounts[2].as_mut().unwrap().lamports = 1_141_440;
        snapshot.accounts[3] = Some(wallet(9));
        snapshot.accounts[4] = Some(wallet(10));
        assert!(validate_postfinality_state(
            &before_with_tombstone_dust,
            &snapshot,
            &landed_with_inbound,
            &payer,
            &recipient,
            &program,
            &programdata,
            &proof,
        )
        .is_err());
    }

    #[test]
    fn evidence_paths_are_distinct_and_presubmit_is_derived() {
        let root = TempDir::new();
        let post = root.path().join("payer-sweep.json");
        let (pre, derived_post) = evidence_paths(&post).unwrap();
        assert_eq!(pre, root.path().join("payer-sweep.pre.json"));
        assert_eq!(derived_post, post);
    }
}
