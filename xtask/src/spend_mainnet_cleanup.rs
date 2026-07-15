//! Explicit ProgramData recovery for a disposable Spend deployment.
//!
//! The command is intentionally not registered by this module. Calling
//! [`execute`] requires a pinned genesis hash and an exact destructive
//! acknowledgement. Unit tests exercise only pure parsing, construction,
//! reconciliation, and local evidence I/O; they make no network calls.

#![allow(deprecated)]

use std::{
    collections::BTreeMap,
    fs::{self, OpenOptions},
    io::Write,
    os::unix::fs::{OpenOptionsExt, PermissionsExt},
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
    bpf_loader_upgradeable,
    compute_budget::ComputeBudgetInstruction,
    hash::Hash,
    instruction::Instruction,
    pubkey::Pubkey,
    signature::{read_keypair_file, Keypair, Signature, Signer},
    system_instruction,
    transaction::{Transaction, VersionedTransaction},
};

use crate::spend_mainnet_loader::{
    build_close_programdata_to_payer, derive_programdata_address, validate_exact_program_account,
    validate_exact_programdata_account, LoaderAccountImage,
};

pub const EXECUTE_CLEANUP_ACKNOWLEDGEMENT: &str = "I_ACKNOWLEDGE_SPEND_PROGRAMDATA_CLEANUP_PERMANENTLY_CLOSES_THE_DISPOSABLE_PROGRAM_AND_REFUNDS_ITS_PROGRAMDATA_RENT";
pub const MAX_PROGRAMDATA_CLEANUP_FEE_LAMPORTS: u64 = 1_000_000;

const READ_RETRIES: u8 = 12;
const FINALITY_TIMEOUT: Duration = Duration::from_secs(180);
const POLL_INTERVAL: Duration = Duration::from_secs(2);
const IN_PROGRESS_WARNING: &str = "Cleanup did not reach the linked immutable post-close receipt. Inspect the pre-close artifact and its exact signed wire before any retry.";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CleanupConfig {
    pub rpc_url: String,
    pub rpc_origin_redacted: String,
    pub payer_keypair: PathBuf,
    pub program_keypair: PathBuf,
    pub upgrade_authority_keypair: PathBuf,
    pub sbf: PathBuf,
    pub evidence: PathBuf,
    pub expected_genesis_hash: String,
    pub execute_interlock: bool,
    pub acknowledgement: String,
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
    slot: u64,
    block_time: Option<i64>,
    fee_lamports: u64,
    pre_balances: Vec<u64>,
    post_balances: Vec<u64>,
    compute_units: u64,
    logs: Vec<String>,
    wire: Vec<u8>,
}

#[derive(Clone, Debug, Serialize)]
pub struct AccountEvidence {
    pub address: String,
    pub present: bool,
    pub lamports: Option<u64>,
    pub owner: Option<String>,
    pub executable: Option<bool>,
    pub data_len: Option<usize>,
    pub data_sha256: Option<String>,
    pub raw_account_image_sha256: Option<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct SnapshotEvidence {
    pub context_slot: u64,
    pub accounts: Vec<AccountEvidence>,
}

#[derive(Clone, Debug, Serialize)]
pub struct SimulationEvidence {
    pub exact_signed_wire_simulated: bool,
    pub context_slot: u64,
    pub error: Option<Value>,
    pub compute_units_consumed: u64,
    pub log_count: usize,
    pub logs_sha256: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct ProgramDataRefundEvidence {
    pub payer_account_index: usize,
    pub program_account_index: usize,
    pub programdata_account_index: usize,
    pub payer_pre_lamports: u64,
    pub payer_post_lamports: u64,
    pub program_pre_lamports: u64,
    pub program_post_lamports: u64,
    pub programdata_pre_lamports: u64,
    pub programdata_post_lamports: u64,
    pub transaction_fee_lamports: u64,
    pub refund_lamports: u64,
    pub payer_delta_plus_fee_lamports: i128,
    pub exact_refund_equation_reconciled: bool,
    pub program_balance_unchanged: bool,
    pub every_other_message_account_balance_unchanged: bool,
}

#[derive(Clone, Debug, Serialize)]
pub struct PrecloseEvidence {
    pub artifact: &'static str,
    pub generated_at_utc: String,
    pub network_genesis_hash: String,
    pub rpc_origin_redacted: String,
    pub payer_pubkey: String,
    pub disposable_program_id: String,
    pub programdata_address: String,
    pub upgrade_authority: String,
    pub sbf_path: String,
    pub sbf_bytes: usize,
    pub sbf_sha256: String,
    pub program_max_len: usize,
    pub exact_program_and_programdata_validated: bool,
    pub prestate: SnapshotEvidence,
    pub programdata_lamports: u64,
    pub compute_unit_price_micro_lamports: u64,
    pub top_level_instruction_count: usize,
    pub expected_signature: String,
    pub recent_blockhash: String,
    pub last_valid_block_height: u64,
    pub quoted_fee_lamports: u64,
    pub maximum_cleanup_fee_lamports: u64,
    pub signed_wire_base64: String,
    pub signed_wire_bytes: usize,
    pub signed_wire_sha256: String,
    pub message_sha256: String,
    pub simulation: SimulationEvidence,
    pub submission_performed_when_written: bool,
    pub postclose_evidence_path: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct PostcloseEvidence {
    pub artifact: &'static str,
    pub generated_at_utc: String,
    pub network_genesis_hash: String,
    pub rpc_origin_redacted: String,
    pub preclose_evidence_path: String,
    pub preclose_evidence_sha256: String,
    pub preclose_evidence_bytes: usize,
    pub preclose_evidence_mode: u32,
    pub signature: String,
    pub finalized_slot: u64,
    pub block_time: Option<i64>,
    pub landed_wire_sha256: String,
    pub landed_wire_identical_to_preclose_artifact: bool,
    pub landed_compute_units_consumed: u64,
    pub landed_log_count: usize,
    pub landed_logs_sha256: String,
    pub poststate: SnapshotEvidence,
    pub program_account_remains: bool,
    pub program_account_image_unchanged: bool,
    pub programdata_account_absent: bool,
    pub refund: ProgramDataRefundEvidence,
    pub sweep_remaining_to_refund_source_submitted: bool,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct ImmutableEvidenceReceipt {
    pub path: String,
    pub sha256: String,
    pub bytes: usize,
    pub mode: u32,
}

#[derive(Clone, Debug, Serialize)]
pub struct ProgramDataCleanupOutcome {
    pub signature: String,
    pub finalized_slot: u64,
    pub refund_lamports: u64,
    pub fee_lamports: u64,
    pub preclose_evidence: ImmutableEvidenceReceipt,
    pub postclose_evidence: ImmutableEvidenceReceipt,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RefundSweepPlan {
    pub instruction: Instruction,
    pub transfer_lamports: u64,
    pub reserved_fee_lamports: u64,
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

    fn latest_blockhash(&self) -> Result<(Hash, u64)> {
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
        ))
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

    fn fee_for_message(&self, transaction: &Transaction) -> Result<u64> {
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
                "RPC returned a signature different from the journaled wire"
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
                    bail!("cleanup transaction {signature} failed: {error}");
                }
                if finalized {
                    return Ok(slot);
                }
            }
            ensure!(
                started.elapsed() < FINALITY_TIMEOUT,
                "cleanup transaction {signature} did not finalize before timeout"
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
                "finalized cleanup transaction unavailable from getTransaction"
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
            .with_context(|| format!("reserve post-close evidence {}", path.display()))?;
        write_synced_json(
            &mut file,
            &json!({
                "artifact": "spend_programdata_cleanup_postclose",
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

    fn commit(self, value: &impl Serialize) -> Result<ImmutableEvidenceReceipt> {
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
        self.file.sync_all()?;
        fs::rename(&temporary, &self.path)?;
        sync_parent(&self.path)?;
        immutable_receipt(&self.path, &bytes)
    }
}

/// Parse a fully explicit cleanup command. No filesystem or network access is
/// performed by the parser.
pub fn parse_cleanup_args(arguments: &[String]) -> Result<CleanupConfig> {
    let mut values = BTreeMap::<String, String>::new();
    let mut execute_interlock = false;
    let mut index = 0usize;
    while index < arguments.len() {
        let key = &arguments[index];
        if key == "--execute-mainnet-programdata-cleanup" {
            ensure!(!execute_interlock, "duplicate cleanup execute interlock");
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
    let allowed = [
        "--rpc-url",
        "--payer-keypair",
        "--program-keypair",
        "--upgrade-authority-keypair",
        "--sbf",
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

    ensure!(execute_interlock, "missing cleanup execute interlock");
    let acknowledgement = required("--acknowledgement")?;
    ensure!(
        acknowledgement == EXECUTE_CLEANUP_ACKNOWLEDGEMENT,
        "cleanup acknowledgement mismatch"
    );
    let expected_genesis_hash = required("--expected-genesis")?;
    Hash::from_str(&expected_genesis_hash).context("--expected-genesis is not a hash")?;
    let rpc_url = required("--rpc-url")?;
    let rpc_origin_redacted = explicit_https_rpc(&rpc_url)?;
    let evidence = absolute("--evidence")?;
    evidence_paths(&evidence)?;
    Ok(CleanupConfig {
        rpc_url,
        rpc_origin_redacted,
        payer_keypair: absolute("--payer-keypair")?,
        program_keypair: absolute("--program-keypair")?,
        upgrade_authority_keypair: absolute("--upgrade-authority-keypair")?,
        sbf: absolute("--sbf")?,
        evidence,
        expected_genesis_hash,
        execute_interlock,
        acknowledgement,
    })
}

/// Build the explicit zero-priority ProgramData close sequence. No signing or
/// submission occurs here.
pub fn build_programdata_cleanup_instructions(
    runtime_program_id: &Pubkey,
    payer: &Pubkey,
    upgrade_authority: &Pubkey,
) -> Result<Vec<Instruction>> {
    Ok(vec![
        ComputeBudgetInstruction::set_compute_unit_price(0),
        build_close_programdata_to_payer(runtime_program_id, payer, upgrade_authority)?,
    ])
}

/// Build an instruction that sweeps every lamport except an explicit future
/// transaction-fee reserve back to the original refund source. This helper is
/// intentionally not called by [`execute`].
pub fn sweep_remaining_to_refund_source(
    payer: &Pubkey,
    refund_source: &Pubkey,
    payer_balance_lamports: u64,
    reserved_sweep_fee_lamports: u64,
) -> Result<RefundSweepPlan> {
    ensure!(
        payer != refund_source,
        "refund source must differ from payer"
    );
    ensure!(
        reserved_sweep_fee_lamports > 0,
        "sweep fee reserve must be nonzero"
    );
    let transfer_lamports = payer_balance_lamports
        .checked_sub(reserved_sweep_fee_lamports)
        .context("payer balance does not cover sweep fee reserve")?;
    ensure!(transfer_lamports > 0, "sweep transfer would be empty");
    let plan = RefundSweepPlan {
        instruction: system_instruction::transfer(payer, refund_source, transfer_lamports),
        transfer_lamports,
        reserved_fee_lamports: reserved_sweep_fee_lamports,
    };
    check_sweep_remaining_to_refund_source(&plan, payer, refund_source, payer_balance_lamports)?;
    Ok(plan)
}

pub fn check_sweep_remaining_to_refund_source(
    plan: &RefundSweepPlan,
    payer: &Pubkey,
    refund_source: &Pubkey,
    payer_balance_lamports: u64,
) -> Result<()> {
    ensure!(
        payer != refund_source,
        "refund source must differ from payer"
    );
    ensure!(plan.transfer_lamports > 0, "sweep transfer must be nonzero");
    ensure!(
        plan.reserved_fee_lamports > 0,
        "sweep fee reserve must be nonzero"
    );
    ensure!(plan.instruction.program_id == solana_sdk::system_program::id());
    ensure!(plan.instruction.accounts.len() == 2);
    ensure!(plan.instruction.accounts[0].pubkey == *payer);
    ensure!(plan.instruction.accounts[0].is_signer);
    ensure!(plan.instruction.accounts[0].is_writable);
    ensure!(plan.instruction.accounts[1].pubkey == *refund_source);
    ensure!(!plan.instruction.accounts[1].is_signer);
    ensure!(plan.instruction.accounts[1].is_writable);
    let decoded: solana_sdk::system_instruction::SystemInstruction =
        bincode::deserialize(&plan.instruction.data).context("decode sweep transfer")?;
    ensure!(
        decoded
            == solana_sdk::system_instruction::SystemInstruction::Transfer {
                lamports: plan.transfer_lamports,
            },
        "sweep instruction is not the declared System transfer"
    );
    ensure!(
        plan.transfer_lamports
            .checked_add(plan.reserved_fee_lamports)
            == Some(payer_balance_lamports),
        "sweep amount plus reserve does not equal payer balance"
    );
    Ok(())
}

/// Execute one permanent loader-v3 ProgramData close. This function is inert
/// unless called by a future command surface with the exact parsed interlocks.
#[allow(clippy::too_many_lines)]
pub fn execute(arguments: &[String]) -> Result<ProgramDataCleanupOutcome> {
    let config = parse_cleanup_args(arguments)?;
    ensure!(config.execute_interlock);
    ensure!(config.acknowledgement == EXECUTE_CLEANUP_ACKNOWLEDGEMENT);

    let payer = secure_keypair(&config.payer_keypair)?;
    let program = secure_keypair(&config.program_keypair)?;
    let upgrade_authority = secure_keypair(&config.upgrade_authority_keypair)?;
    ensure!(
        payer.pubkey() != program.pubkey()
            && payer.pubkey() != upgrade_authority.pubkey()
            && program.pubkey() != upgrade_authority.pubkey(),
        "payer, disposable program, and upgrade authority must be distinct"
    );
    let sbf = exact_regular_file(&config.sbf)?;
    ensure!(!sbf.is_empty(), "SBF image is empty");
    let sbf_sha256 = sha256(&sbf);
    let programdata = derive_programdata_address(&program.pubkey());
    let (preclose_path, postclose_path) = evidence_paths(&config.evidence)?;
    ensure!(
        !preclose_path.exists(),
        "pre-close evidence path already exists"
    );
    let postclose_reservation = EvidenceReservation::reserve(&postclose_path)?;

    let rpc = Rpc::new(config.rpc_url.clone())?;
    let observed_genesis = rpc.genesis_hash()?;
    ensure!(
        observed_genesis == config.expected_genesis_hash,
        "RPC genesis differs from the explicit expected genesis"
    );
    let addresses = [
        payer.pubkey(),
        program.pubkey(),
        programdata,
        upgrade_authority.pubkey(),
    ];
    let initial = rpc.snapshot(&addresses, None)?;
    validate_cleanup_prestate(
        &initial,
        &program.pubkey(),
        &programdata,
        &upgrade_authority.pubkey(),
        &sbf,
    )?;

    let (recent_blockhash, last_valid_block_height) = rpc.latest_blockhash()?;
    let instructions = build_programdata_cleanup_instructions(
        &program.pubkey(),
        &payer.pubkey(),
        &upgrade_authority.pubkey(),
    )?;
    let transaction = Transaction::new_signed_with_payer(
        &instructions,
        Some(&payer.pubkey()),
        &[&payer, &upgrade_authority],
        recent_blockhash,
    );
    transaction
        .verify()
        .map_err(|error| anyhow!("verify signed ProgramData close: {error}"))?;
    let wire = bincode::serialize(&transaction)?;
    let expected_signature = transaction.signatures[0];
    let wire_sha256 = sha256(&wire);
    let message_sha256 = sha256(&bincode::serialize(&transaction.message)?);
    let quoted_fee_lamports = rpc.fee_for_message(&transaction)?;
    ensure!(
        quoted_fee_lamports <= MAX_PROGRAMDATA_CLEANUP_FEE_LAMPORTS,
        "ProgramData cleanup fee quote exceeds its reserved envelope"
    );

    // Revalidate the complete executable and payer balance at one finalized
    // context immediately before exact signed simulation.
    let prestate = rpc.snapshot(&addresses, Some(initial.context_slot))?;
    let programdata_pre = validate_cleanup_prestate(
        &prestate,
        &program.pubkey(),
        &programdata,
        &upgrade_authority.pubkey(),
        &sbf,
    )?;
    ensure!(
        quoted_fee_lamports < programdata_pre.lamports,
        "cleanup fee is not strictly smaller than the expected refund"
    );
    let simulation = rpc.simulate_exact(&wire, prestate.context_slot)?;
    ensure!(
        simulation.context_slot >= prestate.context_slot,
        "exact signed simulation used state older than the coherent prestate"
    );
    ensure!(
        simulation.error.is_none(),
        "exact signed ProgramData close simulation rejected: {:?}",
        simulation.error
    );
    let preclose = PrecloseEvidence {
        artifact: "spend_programdata_cleanup_preclose",
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        network_genesis_hash: observed_genesis.clone(),
        rpc_origin_redacted: config.rpc_origin_redacted.clone(),
        payer_pubkey: payer.pubkey().to_string(),
        disposable_program_id: program.pubkey().to_string(),
        programdata_address: programdata.to_string(),
        upgrade_authority: upgrade_authority.pubkey().to_string(),
        sbf_path: config.sbf.display().to_string(),
        sbf_bytes: sbf.len(),
        sbf_sha256,
        program_max_len: sbf.len(),
        exact_program_and_programdata_validated: true,
        prestate: prestate.evidence(),
        programdata_lamports: programdata_pre.lamports,
        compute_unit_price_micro_lamports: 0,
        top_level_instruction_count: instructions.len(),
        expected_signature: expected_signature.to_string(),
        recent_blockhash: recent_blockhash.to_string(),
        last_valid_block_height,
        quoted_fee_lamports,
        maximum_cleanup_fee_lamports: MAX_PROGRAMDATA_CLEANUP_FEE_LAMPORTS,
        signed_wire_base64: BASE64.encode(&wire),
        signed_wire_bytes: wire.len(),
        signed_wire_sha256: wire_sha256.clone(),
        message_sha256,
        simulation: simulation.evidence(),
        submission_performed_when_written: false,
        postclose_evidence_path: postclose_path.display().to_string(),
    };
    let preclose_receipt = commit_immutable_new(&preclose_path, &preclose)?;

    // The immutable pre-close artifact now journals the only wire permitted to
    // be submitted. There is no reconstruction and no second send.
    rpc.send_exact_once(&wire, &expected_signature)?;
    let finalized_slot = rpc.wait_finalized(&expected_signature)?;
    let finalized = rpc.finalized_transaction(&expected_signature, finalized_slot)?;
    ensure!(
        finalized.wire == wire,
        "landed ProgramData close wire differs from immutable pre-close artifact"
    );
    let refund = check_programdata_refund_equation(
        &transaction.message.account_keys,
        &finalized.pre_balances,
        &finalized.post_balances,
        finalized.fee_lamports,
        &payer.pubkey(),
        &program.pubkey(),
        &programdata,
        programdata_pre.lamports,
    )?;
    ensure!(
        finalized.fee_lamports <= quoted_fee_lamports,
        "finalized cleanup fee exceeded its exact message quote"
    );

    let poststate = rpc.snapshot(&addresses, Some(finalized_slot))?;
    let pre_program = prestate.required(&program.pubkey(), "pre-close Program")?;
    let post_program = poststate.required(&program.pubkey(), "post-close Program")?;
    ensure!(
        post_program.owner == bpf_loader_upgradeable::id(),
        "remaining Program account changed owner"
    );
    ensure!(
        post_program.lamports == refund.program_post_lamports,
        "remaining Program account balance differs from finalized metadata"
    );
    ensure!(
        post_program == pre_program,
        "remaining Program account image changed during cleanup"
    );
    ensure!(
        poststate.account(&programdata)?.is_none(),
        "ProgramData account remains after finalized close"
    );

    let postclose = PostcloseEvidence {
        artifact: "spend_programdata_cleanup_postclose",
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        network_genesis_hash: observed_genesis,
        rpc_origin_redacted: config.rpc_origin_redacted,
        preclose_evidence_path: preclose_receipt.path.clone(),
        preclose_evidence_sha256: preclose_receipt.sha256.clone(),
        preclose_evidence_bytes: preclose_receipt.bytes,
        preclose_evidence_mode: preclose_receipt.mode,
        signature: expected_signature.to_string(),
        finalized_slot,
        block_time: finalized.block_time,
        landed_wire_sha256: sha256(&finalized.wire),
        landed_wire_identical_to_preclose_artifact: true,
        landed_compute_units_consumed: finalized.compute_units,
        landed_log_count: finalized.logs.len(),
        landed_logs_sha256: joined_logs_sha256(&finalized.logs),
        poststate: poststate.evidence(),
        program_account_remains: true,
        program_account_image_unchanged: true,
        programdata_account_absent: true,
        refund: refund.clone(),
        sweep_remaining_to_refund_source_submitted: false,
    };
    let postclose_receipt = postclose_reservation.commit(&postclose)?;
    Ok(ProgramDataCleanupOutcome {
        signature: expected_signature.to_string(),
        finalized_slot,
        refund_lamports: refund.refund_lamports,
        fee_lamports: refund.transaction_fee_lamports,
        preclose_evidence: preclose_receipt,
        postclose_evidence: postclose_receipt,
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
                .map(|(address, account)| account_evidence(*address, account.as_ref()))
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
            log_count: self.logs.len(),
            logs_sha256: joined_logs_sha256(&self.logs),
        }
    }
}

fn validate_cleanup_prestate<'a>(
    snapshot: &'a CoherentSnapshot,
    program: &Pubkey,
    programdata: &Pubkey,
    upgrade_authority: &Pubkey,
    sbf: &[u8],
) -> Result<&'a RpcAccount> {
    let program_account = snapshot.required(program, "disposable Program")?;
    let programdata_account = snapshot.required(programdata, "disposable ProgramData")?;
    validate_exact_program_account(
        &LoaderAccountImage {
            address: *program,
            owner: program_account.owner,
            executable: program_account.executable,
            data: &program_account.data,
        },
        program,
    )?;
    validate_exact_programdata_account(
        &LoaderAccountImage {
            address: *programdata,
            owner: programdata_account.owner,
            executable: programdata_account.executable,
            data: &programdata_account.data,
        },
        program,
        upgrade_authority,
        sbf,
        sbf.len(),
    )?;
    ensure!(
        programdata_account.lamports > MAX_PROGRAMDATA_CLEANUP_FEE_LAMPORTS,
        "ProgramData refund does not exceed cleanup fee envelope"
    );
    Ok(programdata_account)
}

#[allow(clippy::too_many_arguments)]
pub fn check_programdata_refund_equation(
    account_keys: &[Pubkey],
    pre_balances: &[u64],
    post_balances: &[u64],
    transaction_fee_lamports: u64,
    payer: &Pubkey,
    program: &Pubkey,
    programdata: &Pubkey,
    expected_programdata_lamports: u64,
) -> Result<ProgramDataRefundEvidence> {
    ensure!(
        pre_balances.len() == account_keys.len() && post_balances.len() == account_keys.len(),
        "finalized balance arrays do not match message account keys"
    );
    let index = |address: &Pubkey| {
        account_keys
            .iter()
            .position(|candidate| candidate == address)
            .with_context(|| format!("cleanup transaction omitted account {address}"))
    };
    let payer_index = index(payer)?;
    let program_index = index(program)?;
    let programdata_index = index(programdata)?;
    ensure!(
        payer_index != program_index
            && payer_index != programdata_index
            && program_index != programdata_index
    );
    let payer_pre = pre_balances[payer_index];
    let payer_post = post_balances[payer_index];
    let program_pre = pre_balances[program_index];
    let program_post = post_balances[program_index];
    let programdata_pre = pre_balances[programdata_index];
    let programdata_post = post_balances[programdata_index];
    ensure!(
        programdata_pre == expected_programdata_lamports,
        "transaction ProgramData pre-balance differs from validated prestate"
    );
    ensure!(programdata_post == 0, "ProgramData post-balance is nonzero");
    let refund_lamports = programdata_pre
        .checked_sub(programdata_post)
        .context("ProgramData balance increased")?;
    let payer_delta_plus_fee =
        i128::from(payer_post) - i128::from(payer_pre) + i128::from(transaction_fee_lamports);
    let exact_refund_equation_reconciled = payer_delta_plus_fee == i128::from(refund_lamports);
    ensure!(
        exact_refund_equation_reconciled,
        "payer delta plus fee does not equal ProgramData refund"
    );
    let program_balance_unchanged = program_pre == program_post;
    ensure!(program_balance_unchanged, "Program account balance changed");
    let every_other_message_account_balance_unchanged = pre_balances
        .iter()
        .zip(post_balances)
        .enumerate()
        .all(|(index, (pre, post))| {
            index == payer_index || index == programdata_index || pre == post
        });
    ensure!(
        every_other_message_account_balance_unchanged,
        "a non-payer/non-ProgramData message balance changed"
    );
    Ok(ProgramDataRefundEvidence {
        payer_account_index: payer_index,
        program_account_index: program_index,
        programdata_account_index: programdata_index,
        payer_pre_lamports: payer_pre,
        payer_post_lamports: payer_post,
        program_pre_lamports: program_pre,
        program_post_lamports: program_post,
        programdata_pre_lamports: programdata_pre,
        programdata_post_lamports: programdata_post,
        transaction_fee_lamports,
        refund_lamports,
        payer_delta_plus_fee_lamports: payer_delta_plus_fee,
        exact_refund_equation_reconciled,
        program_balance_unchanged,
        every_other_message_account_balance_unchanged,
    })
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
    let _confirmations = value
        .get("confirmations")
        .context("signature status omitted confirmations")?;
    let error = value.get("err").context("signature status omitted err")?;
    let finalized = confirmation_status.as_str() == Some("finalized");
    Ok(Some((
        value["slot"]
            .as_u64()
            .context("signature status omitted slot")?,
        finalized,
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
    ensure!(error.is_null(), "finalized transaction failed: {error}");
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
        slot,
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

fn secure_keypair(path: &Path) -> Result<Keypair> {
    let metadata = fs::symlink_metadata(path)
        .with_context(|| format!("keypair unavailable: {}", path.display()))?;
    ensure!(
        metadata.file_type().is_file() && !metadata.file_type().is_symlink(),
        "keypair must be a regular non-symlink file"
    );
    ensure!(
        metadata.permissions().mode() & 0o077 == 0,
        "keypair permissions must exclude group/other access"
    );
    read_keypair_file(path).map_err(|_| anyhow!("could not decode keypair {}", path.display()))
}

fn exact_regular_file(path: &Path) -> Result<Vec<u8>> {
    let metadata = fs::symlink_metadata(path)
        .with_context(|| format!("file unavailable: {}", path.display()))?;
    ensure!(
        metadata.file_type().is_file() && !metadata.file_type().is_symlink(),
        "input must be a regular non-symlink file"
    );
    fs::read(path).with_context(|| format!("read {}", path.display()))
}

fn explicit_https_rpc(endpoint: &str) -> Result<String> {
    let url = reqwest::Url::parse(endpoint).context("RPC URL is invalid")?;
    ensure!(url.scheme() == "https", "cleanup RPC must use HTTPS");
    ensure!(
        url.username().is_empty() && url.password().is_none(),
        "RPC credentials must not use URL userinfo"
    );
    ensure!(
        url.fragment().is_none(),
        "RPC URL must not contain a fragment"
    );
    let host = url.host_str().context("RPC URL omitted host")?;
    let port = url
        .port()
        .map(|port| format!(":{port}"))
        .unwrap_or_default();
    Ok(format!("https://{host}{port}/<redacted>"))
}

fn rpc_read_retryable(error: &anyhow::Error) -> bool {
    let rendered = format!("{error:#}");
    rendered.contains("HTTP 429")
        || rendered.contains("\"code\":429")
        || rendered.contains("Too Many Requests")
        || rendered.contains("transport failure")
        || rendered.contains("HTTP 502")
        || rendered.contains("HTTP 503")
        || rendered.contains("HTTP 504")
}

fn evidence_paths(postclose: &Path) -> Result<(PathBuf, PathBuf)> {
    ensure!(postclose.is_absolute(), "evidence path must be absolute");
    ensure!(
        postclose.extension().and_then(|value| value.to_str()) == Some("json"),
        "evidence path must end in .json"
    );
    let parent = postclose.parent().context("evidence path omitted parent")?;
    let stem = postclose
        .file_stem()
        .and_then(|value| value.to_str())
        .context("evidence filename is not UTF-8")?;
    ensure!(!stem.is_empty(), "evidence filename stem is empty");
    Ok((
        parent.join(format!("{stem}.preclose.json")),
        postclose.to_path_buf(),
    ))
}

fn commit_immutable_new(path: &Path, value: &impl Serialize) -> Result<ImmutableEvidenceReceipt> {
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
    immutable_receipt(path, &bytes)
}

fn prepare_evidence_parent(path: &Path) -> Result<()> {
    let parent = path.parent().context("evidence path omitted parent")?;
    fs::create_dir_all(parent)?;
    let metadata = fs::symlink_metadata(parent)?;
    ensure!(
        metadata.file_type().is_dir() && !metadata.file_type().is_symlink(),
        "evidence parent must be a non-symlink directory"
    );
    Ok(())
}

fn sync_parent(path: &Path) -> Result<()> {
    fs::File::open(path.parent().context("evidence path omitted parent")?)?.sync_all()?;
    Ok(())
}

fn write_synced_json(file: &mut fs::File, value: &impl Serialize) -> Result<()> {
    file.write_all(&serialized_json(value)?)?;
    file.sync_all()?;
    Ok(())
}

fn serialized_json(value: &impl Serialize) -> Result<Vec<u8>> {
    let mut bytes = serde_json::to_vec_pretty(value)?;
    bytes.push(b'\n');
    Ok(bytes)
}

fn immutable_receipt(path: &Path, expected_bytes: &[u8]) -> Result<ImmutableEvidenceReceipt> {
    let metadata = fs::metadata(path)?;
    let mode = metadata.permissions().mode() & 0o777;
    ensure!(mode == 0o444, "immutable evidence mode is not 0444");
    let actual = fs::read(path)?;
    ensure!(actual == expected_bytes, "immutable evidence bytes changed");
    Ok(ImmutableEvidenceReceipt {
        path: path.display().to_string(),
        sha256: sha256(&actual),
        bytes: actual.len(),
        mode,
    })
}

fn account_evidence(address: Pubkey, account: Option<&RpcAccount>) -> AccountEvidence {
    match account {
        None => AccountEvidence {
            address: address.to_string(),
            present: false,
            lamports: None,
            owner: None,
            executable: None,
            data_len: None,
            data_sha256: None,
            raw_account_image_sha256: None,
        },
        Some(account) => {
            let mut raw = Vec::with_capacity(8 + 32 + 1 + account.data.len());
            raw.extend_from_slice(&account.lamports.to_le_bytes());
            raw.extend_from_slice(account.owner.as_ref());
            raw.push(u8::from(account.executable));
            raw.extend_from_slice(&account.data);
            AccountEvidence {
                address: address.to_string(),
                present: true,
                lamports: Some(account.lamports),
                owner: Some(account.owner.to_string()),
                executable: Some(account.executable),
                data_len: Some(account.data.len()),
                data_sha256: Some(sha256(&account.data)),
                raw_account_image_sha256: Some(sha256(&raw)),
            }
        }
    }
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn joined_logs_sha256(logs: &[String]) -> String {
    sha256(logs.join("\n").as_bytes())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        sync::atomic::{AtomicU64, Ordering},
        time::{SystemTime, UNIX_EPOCH},
    };

    static NEXT_TEMP_DIR: AtomicU64 = AtomicU64::new(0);

    struct TempDir(PathBuf);

    impl TempDir {
        fn new() -> Self {
            let nonce = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos();
            loop {
                let serial = NEXT_TEMP_DIR.fetch_add(1, Ordering::Relaxed);
                let path = std::env::temp_dir().join(format!(
                    "spend-mainnet-cleanup-test-{}-{nonce}-{serial}",
                    std::process::id()
                ));
                match fs::create_dir(&path) {
                    Ok(()) => return Self(path),
                    Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                    Err(error) => panic!("create test temporary directory: {error}"),
                }
            }
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn valid_arguments(root: &Path) -> Vec<String> {
        vec![
            "--execute-mainnet-programdata-cleanup".to_owned(),
            "--rpc-url".to_owned(),
            "https://rpc.example.test/private?key=secret".to_owned(),
            "--payer-keypair".to_owned(),
            root.join("payer.json").display().to_string(),
            "--program-keypair".to_owned(),
            root.join("program.json").display().to_string(),
            "--upgrade-authority-keypair".to_owned(),
            root.join("authority.json").display().to_string(),
            "--sbf".to_owned(),
            root.join("program.so").display().to_string(),
            "--evidence".to_owned(),
            root.join("cleanup.json").display().to_string(),
            "--expected-genesis".to_owned(),
            Hash::new_unique().to_string(),
            "--acknowledgement".to_owned(),
            EXECUTE_CLEANUP_ACKNOWLEDGEMENT.to_owned(),
        ]
    }

    #[test]
    fn parser_requires_every_explicit_interlock_and_redacts_rpc_secrets() {
        let root = TempDir::new();
        let arguments = valid_arguments(&root.0);
        let config = parse_cleanup_args(&arguments).unwrap();
        assert!(config.execute_interlock);
        assert_eq!(
            config.rpc_origin_redacted,
            "https://rpc.example.test/<redacted>"
        );
        assert!(!config.rpc_origin_redacted.contains("secret"));

        let without_interlock = arguments[1..].to_vec();
        assert!(parse_cleanup_args(&without_interlock).is_err());
        let mut wrong_ack = arguments.clone();
        *wrong_ack.last_mut().unwrap() = "no".to_owned();
        assert!(parse_cleanup_args(&wrong_ack).is_err());
        let mut http = arguments;
        let index = http.iter().position(|value| value == "--rpc-url").unwrap();
        http[index + 1] = "http://rpc.example.test".to_owned();
        assert!(parse_cleanup_args(&http).is_err());
    }

    #[test]
    fn cleanup_builder_is_explicitly_zero_priority_and_links_programdata() {
        let payer = Pubkey::new_unique();
        let program = Pubkey::new_unique();
        let authority = Pubkey::new_unique();
        let instructions =
            build_programdata_cleanup_instructions(&program, &payer, &authority).unwrap();
        assert_eq!(instructions.len(), 2);
        assert_eq!(
            instructions[0],
            ComputeBudgetInstruction::set_compute_unit_price(0)
        );
        assert_eq!(instructions[1].program_id, bpf_loader_upgradeable::id());
        assert_eq!(
            instructions[1]
                .accounts
                .iter()
                .map(|meta| meta.pubkey)
                .collect::<Vec<_>>(),
            vec![
                derive_programdata_address(&program),
                payer,
                authority,
                program
            ]
        );
        assert!(instructions[1].accounts[2].is_signer);
    }

    #[test]
    fn coherent_snapshot_parser_preserves_absence_and_full_account_bytes() {
        let first = Pubkey::new_unique();
        let second = Pubkey::new_unique();
        let owner = Pubkey::new_unique();
        let result = json!({
            "context": {"slot": 77},
            "value": [
                {
                    "lamports": 123,
                    "owner": owner.to_string(),
                    "executable": false,
                    "data": [BASE64.encode([1u8, 2, 3]), "base64"]
                },
                null
            ]
        });
        let snapshot = parse_coherent_snapshot(&result, &[first, second]).unwrap();
        assert_eq!(snapshot.context_slot, 77);
        assert_eq!(snapshot.required(&first, "first").unwrap().data, [1, 2, 3]);
        assert!(snapshot.account(&second).unwrap().is_none());
        assert!(parse_coherent_snapshot(&result, &[first]).is_err());
    }

    #[test]
    fn refund_equation_requires_full_programdata_refund_and_program_retention() {
        let payer = Pubkey::new_unique();
        let program = Pubkey::new_unique();
        let programdata = derive_programdata_address(&program);
        let loader = bpf_loader_upgradeable::id();
        let keys = [payer, programdata, program, loader];
        let fee = 10_000u64;
        let refund = 6_417_266_160u64;
        let payer_pre = 1_000_000_000u64;
        let payer_post = payer_pre + refund - fee;
        let evidence = check_programdata_refund_equation(
            &keys,
            &[payer_pre, refund, 1_141_440, 1],
            &[payer_post, 0, 1_141_440, 1],
            fee,
            &payer,
            &program,
            &programdata,
            refund,
        )
        .unwrap();
        assert!(evidence.exact_refund_equation_reconciled);
        assert!(evidence.program_balance_unchanged);
        assert_eq!(evidence.refund_lamports, refund);

        assert!(check_programdata_refund_equation(
            &keys,
            &[payer_pre, refund, 1_141_440, 1],
            &[payer_post, 1, 1_141_440, 1],
            fee,
            &payer,
            &program,
            &programdata,
            refund,
        )
        .is_err());
    }

    #[test]
    fn immutable_pre_and_post_evidence_are_hash_linkable_and_mode_0444() {
        let root = TempDir::new();
        let post_path = root.0.join("cleanup.json");
        let (pre_path, derived_post) = evidence_paths(&post_path).unwrap();
        assert_eq!(derived_post, post_path);
        let pre = json!({"artifact":"pre", "value": 7});
        let pre_receipt = commit_immutable_new(&pre_path, &pre).unwrap();
        assert_eq!(pre_receipt.mode, 0o444);
        let reservation = EvidenceReservation::reserve(&post_path).unwrap();
        let post = json!({
            "artifact":"post",
            "preclose_evidence_sha256":pre_receipt.sha256,
        });
        let post_receipt = reservation.commit(&post).unwrap();
        assert_eq!(post_receipt.mode, 0o444);
        let post_value: Value = serde_json::from_slice(&fs::read(post_path).unwrap()).unwrap();
        assert_eq!(
            post_value["preclose_evidence_sha256"].as_str(),
            Some(pre_receipt.sha256.as_str())
        );
    }

    #[test]
    fn sweep_helper_returns_only_to_pinned_refund_source_and_preserves_fee() {
        let payer = Pubkey::new_unique();
        let refund_source = Pubkey::new_unique();
        let plan =
            sweep_remaining_to_refund_source(&payer, &refund_source, 9_000_000, 10_000).unwrap();
        assert_eq!(plan.transfer_lamports, 8_990_000);
        check_sweep_remaining_to_refund_source(&plan, &payer, &refund_source, 9_000_000).unwrap();
        assert!(sweep_remaining_to_refund_source(&payer, &payer, 9_000_000, 10_000).is_err());
        assert!(sweep_remaining_to_refund_source(&payer, &refund_source, 10_000, 10_000).is_err());
    }

    #[test]
    fn simulation_and_signature_status_parsers_fail_closed_on_shape_drift() {
        let simulation = parse_simulation(&json!({
            "context":{"slot":88},
            "value":{"err":null,"unitsConsumed":1234,"logs":["a","b"]}
        }))
        .unwrap();
        assert_eq!(simulation.context_slot, 88);
        assert_eq!(simulation.units, 1234);
        assert!(simulation.error.is_none());

        let status = parse_signature_status(&json!({
            "value":[{"slot":99,"confirmationStatus":"finalized","confirmations":null,"err":null}]
        }))
        .unwrap()
        .unwrap();
        assert_eq!(status, (99, true, None));
        assert!(parse_signature_status(&json!({"value":[]})).is_err());
        assert!(parse_simulation(&json!({
            "context":{"slot":88},
            "value":{"unitsConsumed":1234,"logs":[]}
        }))
        .is_err());
        assert!(parse_signature_status(&json!({
            "value":[{"slot":99,"confirmationStatus":"finalized","confirmations":null}]
        }))
        .is_err());
        assert!(parse_signature_status(&json!({
            "value":[{"slot":99,"confirmations":null,"err":null}]
        }))
        .is_err());
        assert!(parse_finalized_transaction(
            &json!({"slot":99,"meta":{}}),
            &json!({"slot":99}),
            99,
        )
        .is_err());
    }
}
