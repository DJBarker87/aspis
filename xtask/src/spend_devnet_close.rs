//! Destructive, devnet-only smoke test for the append-only Spend tag 64.
//!
//! This command is intentionally self-contained. It does not consult Solana
//! CLI configuration, does not infer a network, and will not sign unless both
//! destructive interlocks are present. The exact signed wire is simulated and
//! then submitted without reconstruction. Finalized transaction balances are
//! used to prove the refund.

use std::{
    collections::BTreeMap,
    fs::{self, OpenOptions},
    io::{Seek, SeekFrom, Write},
    os::unix::fs::{OpenOptionsExt, PermissionsExt},
    path::{Path, PathBuf},
    thread,
    time::{Duration, Instant},
};

use anyhow::{anyhow, bail, ensure, Context, Result};
use base64::{engine::general_purpose::STANDARD as BASE64, Engine};
use serde::Serialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use solana_sdk::{
    bpf_loader_upgradeable::{self, UpgradeableLoaderState},
    hash::Hash,
    instruction::{AccountMeta, Instruction},
    pubkey::Pubkey,
    signature::{read_keypair_file, Keypair, Signature, Signer},
    transaction::Transaction,
};

use aspis_verifier::PROOF_ACCOUNT_HEADER_LEN;

const DEVNET_GENESIS_HASH: &str = "EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG";
const EXECUTE_ACK: &str =
    "I_ACKNOWLEDGE_SPEND_DEVNET_TAG64_CLOSE_IRREVERSIBLY_DESTROYS_THE_PROOF_ACCOUNT_AND_REFUNDS_ITS_DEVNET_SOL";
const TAG_CLOSE_FINALIZED_PROOF: u8 = 64;
const PROOF_MAGIC: &[u8; 4] = b"ASPU";
const PROOF_AUTHORITY_OFFSET: usize = 8;
const PROGRAMDATA_METADATA_BYTES: usize = 45;
const READ_RETRIES: u8 = 12;
const FINALITY_TIMEOUT: Duration = Duration::from_secs(180);
const POLL_INTERVAL: Duration = Duration::from_secs(2);
const IN_PROGRESS_WARNING: &str = "Execution did not reach the immutable finalized evidence commit. The recorded expected signature and exact wire hash must be inspected on devnet before any retry.";

#[derive(Debug)]
struct Config {
    rpc_url: String,
    payer_keypair: PathBuf,
    proof_account_keypair: PathBuf,
    expected_proof_account: Pubkey,
    expected_proof_sha256: String,
    sbf: PathBuf,
    program_max_len: usize,
    evidence: PathBuf,
    execute_interlock: bool,
    acknowledgement: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RpcAccount {
    lamports: u64,
    owner: Pubkey,
    executable: bool,
    data: Vec<u8>,
}

#[derive(Clone, Debug)]
struct AccountRead {
    context_slot: u64,
    account: Option<RpcAccount>,
}

#[derive(Clone, Debug)]
struct ProgramSnapshot {
    program_context_slot: u64,
    program_id: Pubkey,
    program: RpcAccount,
    programdata_context_slot: u64,
    programdata_address: Pubkey,
    programdata: RpcAccount,
    programdata_deployment_slot: u64,
    upgrade_authority: Pubkey,
}

#[derive(Clone, Debug, Serialize)]
pub struct AccountEvidence {
    pub address: String,
    pub context_slot: u64,
    pub lamports: u64,
    pub owner: String,
    pub executable: bool,
    pub data_len: usize,
    pub data_sha256: String,
    pub raw_account_image_sha256: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct ProgramSnapshotEvidence {
    pub program_account: AccountEvidence,
    pub programdata_address: String,
    pub programdata_account: AccountEvidence,
    pub programdata_deployment_slot: u64,
    pub upgrade_authority: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct ProgramContinuityEvidence {
    pub programdata_address_unchanged: bool,
    pub program_raw_account_image_unchanged: bool,
    pub programdata_raw_account_image_unchanged: bool,
    pub programdata_deployment_slot_unchanged: bool,
    pub upgrade_authority_unchanged: bool,
}

impl ProgramContinuityEvidence {
    fn all_unchanged(&self) -> bool {
        self.programdata_address_unchanged
            && self.program_raw_account_image_unchanged
            && self.programdata_raw_account_image_unchanged
            && self.programdata_deployment_slot_unchanged
            && self.upgrade_authority_unchanged
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct SealedProofEvidence {
    pub account: AccountEvidence,
    pub magic_exact: bool,
    pub authority_erased: bool,
    pub stored_proof_bytes: usize,
    pub stored_proof_sha256: String,
    pub trailing_allocation_bytes: usize,
}

#[derive(Clone, Debug, Serialize)]
pub struct InstructionAccountEvidence {
    pub index: usize,
    pub address: String,
    pub writable: bool,
    pub signer: bool,
    pub role: &'static str,
}

#[derive(Clone, Debug, Serialize)]
pub struct SimulationEvidence {
    pub exact_signed_wire_simulated: bool,
    pub error: Option<Value>,
    pub compute_units_consumed: u64,
    pub log_count: usize,
    pub logs_sha256: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct RefundEvidence {
    pub fee_lamports: u64,
    pub payer_account_index: usize,
    pub proof_account_index: usize,
    pub payer_pre_lamports: u64,
    pub payer_post_lamports: u64,
    pub proof_pre_lamports: u64,
    pub proof_post_lamports: u64,
    pub refund_lamports: u64,
    pub payer_delta_plus_fee_lamports: i128,
    pub exact_refund_equation_reconciled: bool,
    pub every_other_message_account_balance_unchanged: bool,
}

#[derive(Clone, Debug, Serialize)]
pub struct SpendDevnetCloseEvidence {
    pub artifact: &'static str,
    pub generated_at_utc: String,
    pub network: &'static str,
    pub genesis_hash: String,
    pub rpc_origin_redacted: String,
    pub program_id: String,
    pub payer_pubkey: String,
    pub proof_account_pubkey: String,
    pub expected_proof_account_pubkey: String,
    pub expected_proof_payload_sha256: String,
    pub destructive_target_identity_exact: bool,
    pub destructive_execute_interlock_present: bool,
    pub destructive_acknowledgement_exact: bool,
    pub sbf_path: String,
    pub sbf_bytes: usize,
    pub sbf_sha256: String,
    pub program_max_len: usize,
    pub program_before: ProgramSnapshotEvidence,
    pub program_after: ProgramSnapshotEvidence,
    pub program_continuity: ProgramContinuityEvidence,
    pub exact_sbf_max_len_authority_before: bool,
    pub exact_sbf_max_len_authority_after: bool,
    pub proof_before: SealedProofEvidence,
    pub instruction_tag: u8,
    pub instruction_data_hex: String,
    pub instruction_accounts: Vec<InstructionAccountEvidence>,
    pub signature: String,
    pub finalized_slot: u64,
    pub signed_wire_bytes: usize,
    pub signed_wire_sha256: String,
    pub message_sha256: String,
    pub simulation: SimulationEvidence,
    pub submitted_identically_to_simulation: bool,
    pub landed_wire_sha256: String,
    pub landed_wire_identical_to_submitted: bool,
    pub landed_message_account_count: usize,
    pub landed_compute_units_consumed: u64,
    pub landed_log_count: usize,
    pub landed_logs_sha256: String,
    pub refund: RefundEvidence,
    pub refund_lamports: u64,
    pub proof_account_absent_after_finality: bool,
    pub evidence_path: String,
    pub evidence_file_mode: u32,
    pub explicit_scope: Vec<&'static str>,
}

impl RpcAccount {
    fn evidence(&self, address: Pubkey, context_slot: u64) -> AccountEvidence {
        let mut raw = Vec::with_capacity(8 + 32 + 1 + self.data.len());
        raw.extend_from_slice(&self.lamports.to_le_bytes());
        raw.extend_from_slice(self.owner.as_ref());
        raw.push(u8::from(self.executable));
        raw.extend_from_slice(&self.data);
        AccountEvidence {
            address: address.to_string(),
            context_slot,
            lamports: self.lamports,
            owner: self.owner.to_string(),
            executable: self.executable,
            data_len: self.data.len(),
            data_sha256: sha256(&self.data),
            raw_account_image_sha256: sha256(&raw),
        }
    }
}

impl ProgramSnapshot {
    fn evidence(&self) -> ProgramSnapshotEvidence {
        ProgramSnapshotEvidence {
            program_account: self
                .program
                .evidence(self.program_id, self.program_context_slot),
            programdata_address: self.programdata_address.to_string(),
            programdata_account: self
                .programdata
                .evidence(self.programdata_address, self.programdata_context_slot),
            programdata_deployment_slot: self.programdata_deployment_slot,
            upgrade_authority: self.upgrade_authority.to_string(),
        }
    }

    fn continuity_from(&self, before: &Self) -> ProgramContinuityEvidence {
        ProgramContinuityEvidence {
            programdata_address_unchanged: self.programdata_address == before.programdata_address,
            program_raw_account_image_unchanged: self.program == before.program,
            programdata_raw_account_image_unchanged: self.programdata == before.programdata,
            programdata_deployment_slot_unchanged: self.programdata_deployment_slot
                == before.programdata_deployment_slot,
            upgrade_authority_unchanged: self.upgrade_authority == before.upgrade_authority,
        }
    }
}

#[derive(Debug)]
struct Simulation {
    error: Option<Value>,
    units: u64,
    logs: Vec<String>,
}

#[derive(Debug)]
struct FinalizedTransaction {
    slot: u64,
    fee: u64,
    pre_balances: Vec<u64>,
    post_balances: Vec<u64>,
    compute_units: Option<u64>,
    logs: Vec<String>,
    wire: Vec<u8>,
}

struct Rpc {
    endpoint: String,
    client: reqwest::blocking::Client,
}

fn read_retryable(error: &anyhow::Error) -> bool {
    let rendered = format!("{error:#}");
    rendered.contains("HTTP 429")
        || rendered.contains("\"code\":429")
        || rendered.contains("Too Many Requests")
        || rendered.contains("transport failure")
        || rendered.contains("HTTP 502")
        || rendered.contains("HTTP 503")
        || rendered.contains("HTTP 504")
}

impl Rpc {
    fn new(endpoint: String) -> Result<Self> {
        Ok(Self {
            endpoint,
            client: reqwest::blocking::Client::builder()
                .timeout(Duration::from_secs(60))
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
                Err(error) if retries < READ_RETRIES && read_retryable(&error) => {
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

    fn latest_blockhash(&self) -> Result<Hash> {
        self.read("getLatestBlockhash", json!([{"commitment":"finalized"}]))?["value"]["blockhash"]
            .as_str()
            .context("getLatestBlockhash omitted blockhash")?
            .parse()
            .context("getLatestBlockhash returned invalid hash")
    }

    fn account(&self, address: &Pubkey) -> Result<AccountRead> {
        let result = self.read(
            "getAccountInfo",
            json!([address.to_string(), {"encoding":"base64","commitment":"finalized"}]),
        )?;
        let context_slot = result["context"]["slot"]
            .as_u64()
            .context("getAccountInfo omitted context slot")?;
        let value = &result["value"];
        if value.is_null() {
            return Ok(AccountRead {
                context_slot,
                account: None,
            });
        }
        let account = RpcAccount {
            lamports: value["lamports"]
                .as_u64()
                .context("account omitted lamports")?,
            owner: value["owner"]
                .as_str()
                .context("account omitted owner")?
                .parse()
                .context("account returned invalid owner")?,
            executable: value["executable"]
                .as_bool()
                .context("account omitted executable flag")?,
            data: BASE64.decode(
                value["data"][0]
                    .as_str()
                    .context("account omitted base64 data")?,
            )?,
        };
        Ok(AccountRead {
            context_slot,
            account: Some(account),
        })
    }

    fn simulate_exact(&self, wire: &[u8]) -> Result<Simulation> {
        let result = self.read(
            "simulateTransaction",
            json!([BASE64.encode(wire), {
                "encoding":"base64",
                "sigVerify":true,
                "replaceRecentBlockhash":false,
                "commitment":"finalized"
            }]),
        )?;
        let value = &result["value"];
        let error = (!value["err"].is_null()).then(|| value["err"].clone());
        let units = value["unitsConsumed"]
            .as_u64()
            .context("simulation omitted unitsConsumed")?;
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
        Ok(Simulation { error, units, logs })
    }

    fn signature_status(
        &self,
        signature: &Signature,
    ) -> Result<Option<(u64, bool, Option<Value>)>> {
        let result = self.read(
            "getSignatureStatuses",
            json!([[signature.to_string()], {"searchTransactionHistory":true}]),
        )?;
        let values = result["value"]
            .as_array()
            .context("getSignatureStatuses omitted value array")?;
        ensure!(values.len() == 1, "signature status response length drift");
        let value = &values[0];
        if value.is_null() {
            return Ok(None);
        }
        let finalized = value["confirmationStatus"].as_str() == Some("finalized")
            || (value["confirmationStatus"].is_null() && value["confirmations"].is_null());
        let error = (!value["err"].is_null()).then(|| value["err"].clone());
        Ok(Some((
            value["slot"]
                .as_u64()
                .context("signature status omitted slot")?,
            finalized,
            error,
        )))
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
                "RPC returned a signature different from the signed wire"
            ),
            Err(send_error) => {
                // Never reconstruct and never silently send a different wire.
                // If the response was ambiguous but the expected signature is
                // already visible, finality polling can safely continue.
                ensure!(
                    self.signature_status(expected_signature)?.is_some(),
                    "exact-wire submission failed and its expected signature was not observed: {send_error}"
                );
            }
        }
        Ok(())
    }

    fn wait_finalized(&self, signature: &Signature) -> Result<u64> {
        let started = Instant::now();
        loop {
            if let Some((slot, finalized, error)) = self.signature_status(signature)? {
                if let Some(error) = error {
                    bail!("transaction {signature} failed: {error}");
                }
                if finalized {
                    return Ok(slot);
                }
            }
            ensure!(
                started.elapsed() < FINALITY_TIMEOUT,
                "transaction {signature} did not finalize before timeout"
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
                "finalized transaction was not available from getTransaction before timeout"
            );
            thread::sleep(POLL_INTERVAL);
        }
    }

    fn finalized_transaction(
        &self,
        signature: &Signature,
        expected_slot: u64,
    ) -> Result<FinalizedTransaction> {
        let result = self.transaction_result(signature, "json")?;
        let slot = result["slot"]
            .as_u64()
            .context("finalized transaction omitted slot")?;
        ensure!(
            slot == expected_slot,
            "finalized slot differs across RPC methods"
        );
        let meta = &result["meta"];
        ensure!(
            meta["err"].is_null(),
            "finalized transaction meta reports failure"
        );
        let parse_balances = |field: &str| -> Result<Vec<u64>> {
            meta[field]
                .as_array()
                .with_context(|| format!("finalized transaction omitted {field}"))?
                .iter()
                .map(|value| {
                    value
                        .as_u64()
                        .with_context(|| format!("{field} contained a non-u64 balance"))
                })
                .collect()
        };
        let logs = meta["logMessages"]
            .as_array()
            .context("finalized transaction omitted logMessages")?
            .iter()
            .map(|line| {
                line.as_str()
                    .map(ToOwned::to_owned)
                    .context("finalized log was not a string")
            })
            .collect::<Result<Vec<_>>>()?;
        let encoded = self.transaction_result(signature, "base64")?;
        ensure!(
            encoded["slot"].as_u64() == Some(slot),
            "base64 transaction slot differs from JSON transaction slot"
        );
        let wire = BASE64.decode(
            encoded["transaction"][0]
                .as_str()
                .context("finalized transaction omitted base64 wire")?,
        )?;
        Ok(FinalizedTransaction {
            slot,
            fee: meta["fee"]
                .as_u64()
                .context("finalized transaction omitted fee")?,
            pre_balances: parse_balances("preBalances")?,
            post_balances: parse_balances("postBalances")?,
            compute_units: meta["computeUnitsConsumed"].as_u64(),
            logs,
            wire,
        })
    }
}

fn parse_args(arguments: &[String]) -> Result<Config> {
    let mut values = BTreeMap::<String, String>::new();
    let mut execute_interlock = false;
    let mut index = 0usize;
    while index < arguments.len() {
        let key = &arguments[index];
        if key == "--execute-devnet-tag64-close" {
            ensure!(!execute_interlock, "duplicate --execute-devnet-tag64-close");
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
        "--proof-account-keypair",
        "--expected-proof-account",
        "--expected-proof-sha256",
        "--sbf",
        "--program-max-len",
        "--evidence",
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
    let program_max_len = required("--program-max-len")?
        .parse::<usize>()
        .context("--program-max-len is not usize")?;
    ensure!(program_max_len > 0, "--program-max-len must be nonzero");
    let expected_proof_account = required("--expected-proof-account")?
        .parse::<Pubkey>()
        .context("--expected-proof-account is not a Solana pubkey")?;
    let expected_proof_sha256 = required("--expected-proof-sha256")?;
    ensure!(
        expected_proof_sha256.len() == 64
            && expected_proof_sha256
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
        "--expected-proof-sha256 must be exactly 64 lowercase hexadecimal characters"
    );
    Ok(Config {
        rpc_url: required("--rpc-url")?,
        payer_keypair: absolute("--payer-keypair")?,
        proof_account_keypair: absolute("--proof-account-keypair")?,
        expected_proof_account,
        expected_proof_sha256,
        sbf: absolute("--sbf")?,
        program_max_len,
        evidence: absolute("--evidence")?,
        execute_interlock,
        acknowledgement: values.get("--acknowledgement").cloned(),
    })
}

fn rpc_origin(endpoint: &str) -> Result<String> {
    let url = reqwest::Url::parse(endpoint).context("invalid RPC URL")?;
    ensure!(url.scheme() == "https", "devnet RPC must use HTTPS");
    ensure!(
        url.username().is_empty() && url.password().is_none(),
        "RPC credentials may not use URL userinfo"
    );
    ensure!(
        url.fragment().is_none(),
        "RPC URL must not contain a fragment"
    );
    let host = url.host_str().context("RPC URL omitted host")?;
    Ok(format!(
        "https://{}{}<redacted>",
        host,
        url.port()
            .map(|port| format!(":{port}/"))
            .unwrap_or_else(|| "/".to_owned())
    ))
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
        "input must be a regular non-symlink file: {}",
        path.display()
    );
    fs::read(path).with_context(|| format!("read {}", path.display()))
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

fn deployed_program_exact(
    rpc: &Rpc,
    expected_sbf: &[u8],
    expected_max_len: usize,
    expected_authority: Pubkey,
) -> Result<ProgramSnapshot> {
    ensure!(!expected_sbf.is_empty(), "SBF file must not be empty");
    ensure!(
        expected_sbf.len() <= expected_max_len,
        "SBF is longer than declared ProgramData maximum length"
    );
    let program_id = aspis_verifier::id();
    let program_read = rpc.account(&program_id)?;
    let program = program_read
        .account
        .context("Spend program account is absent")?;
    ensure!(
        program.owner == bpf_loader_upgradeable::id() && program.executable,
        "Spend program is not executable BPFLoaderUpgradeable"
    );
    let state: UpgradeableLoaderState =
        bincode::deserialize(&program.data).context("decode Spend Program state")?;
    let UpgradeableLoaderState::Program {
        programdata_address,
    } = state
    else {
        bail!("Spend address is not an upgradeable Program account")
    };
    let programdata_read = rpc.account(&programdata_address)?;
    let programdata = programdata_read
        .account
        .context("linked Spend ProgramData account is absent")?;
    ensure!(
        programdata.owner == bpf_loader_upgradeable::id() && !programdata.executable,
        "linked Spend account is not non-executable BPFLoaderUpgradeable ProgramData"
    );
    let state: UpgradeableLoaderState =
        bincode::deserialize(&programdata.data).context("decode Spend ProgramData state")?;
    let UpgradeableLoaderState::ProgramData {
        slot: programdata_deployment_slot,
        upgrade_authority_address,
    } = state
    else {
        bail!("linked Spend account is not ProgramData")
    };
    let upgrade_authority = upgrade_authority_address
        .context("Spend ProgramData is immutable; explicit authority continuity failed")?;
    ensure!(
        upgrade_authority == expected_authority,
        "Spend ProgramData upgrade authority does not equal explicit payer"
    );
    let code = programdata
        .data
        .get(PROGRAMDATA_METADATA_BYTES..)
        .context("Spend ProgramData is shorter than loader metadata")?;
    ensure!(
        code.len() == expected_max_len,
        "Spend ProgramData maximum length mismatch"
    );
    ensure!(
        code.get(..expected_sbf.len()) == Some(expected_sbf),
        "deployed Spend bytes differ from the explicit SBF"
    );
    ensure!(
        code[expected_sbf.len()..].iter().all(|byte| *byte == 0),
        "deployed Spend ProgramData padding is nonzero"
    );
    Ok(ProgramSnapshot {
        program_context_slot: program_read.context_slot,
        program_id,
        program,
        programdata_context_slot: programdata_read.context_slot,
        programdata_address,
        programdata,
        programdata_deployment_slot,
        upgrade_authority,
    })
}

fn sealed_proof_exact(
    read: AccountRead,
    proof_address: Pubkey,
) -> Result<(RpcAccount, SealedProofEvidence)> {
    let account = read.account.context("proof account is absent")?;
    ensure!(
        account.owner == aspis_verifier::id(),
        "proof account is not owned by the exact Spend program"
    );
    ensure!(!account.executable, "proof account must not be executable");
    ensure!(
        account.lamports > 0,
        "proof account has no refundable lamports"
    );
    ensure!(
        account.data.len() >= PROOF_ACCOUNT_HEADER_LEN,
        "proof account is shorter than the Spend header"
    );
    let magic_exact = account.data.get(..4) == Some(PROOF_MAGIC.as_slice());
    ensure!(magic_exact, "proof account magic is not ASPU");
    let stored_proof_bytes = u32::from_le_bytes(
        account.data[4..8]
            .try_into()
            .expect("four-byte proof length slice"),
    ) as usize;
    ensure!(
        stored_proof_bytes > 0,
        "sealed proof account stores an empty proof"
    );
    let proof_end = PROOF_ACCOUNT_HEADER_LEN
        .checked_add(stored_proof_bytes)
        .context("proof length overflow")?;
    ensure!(
        proof_end <= account.data.len(),
        "stored proof length exceeds account allocation"
    );
    let authority_erased = account.data[PROOF_AUTHORITY_OFFSET..PROOF_AUTHORITY_OFFSET + 32]
        .iter()
        .all(|byte| *byte == 0);
    ensure!(authority_erased, "proof account is not irreversibly sealed");
    let evidence = SealedProofEvidence {
        account: account.evidence(proof_address, read.context_slot),
        magic_exact,
        authority_erased,
        stored_proof_bytes,
        stored_proof_sha256: sha256(&account.data[PROOF_ACCOUNT_HEADER_LEN..proof_end]),
        trailing_allocation_bytes: account.data.len() - proof_end,
    };
    Ok((account, evidence))
}

struct EvidenceReservation {
    file: fs::File,
    path: PathBuf,
}

impl EvidenceReservation {
    fn reserve(path: &Path) -> Result<Self> {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)?;
        }
        let mut file = OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(path)
            .with_context(|| format!("reserve fresh evidence path {}", path.display()))?;
        let placeholder = json!({
            "artifact": "spend_devnet_tag64_close_refund_smoke",
            "status": "in_progress_no_finalized_claim",
            "reserved_at_utc": chrono::Utc::now().to_rfc3339(),
            "warning": IN_PROGRESS_WARNING
        });
        write_json(&mut file, &placeholder)?;
        Ok(Self {
            file,
            path: path.to_path_buf(),
        })
    }

    fn mark_prepared(&mut self, signature: Signature, wire_sha256: &str) -> Result<()> {
        let placeholder = json!({
            "artifact": "spend_devnet_tag64_close_refund_smoke",
            "status": "prepared_or_submitted_no_finalized_claim",
            "expected_signature": signature.to_string(),
            "exact_signed_wire_sha256": wire_sha256,
            "updated_at_utc": chrono::Utc::now().to_rfc3339(),
            "warning": IN_PROGRESS_WARNING
        });
        self.file.set_len(0)?;
        self.file.seek(SeekFrom::Start(0))?;
        write_json(&mut self.file, &placeholder)
    }

    fn commit(self, value: &impl Serialize) -> Result<()> {
        let parent = self.path.parent().context("evidence path omitted parent")?;
        let name = self
            .path
            .file_name()
            .and_then(|name| name.to_str())
            .context("evidence filename is not UTF-8")?;
        let temporary = parent.join(format!(".{name}.complete-{}", std::process::id()));
        let mut completed = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&temporary)
            .with_context(|| format!("create completed evidence {}", temporary.display()))?;
        write_json(&mut completed, value)?;
        let mut permissions = completed.metadata()?.permissions();
        permissions.set_mode(0o444);
        fs::set_permissions(&temporary, permissions)?;
        completed.sync_all()?;
        self.file.sync_all()?;
        fs::rename(&temporary, &self.path)?;
        fs::File::open(parent)?.sync_all()?;
        let mode = fs::metadata(&self.path)?.permissions().mode() & 0o777;
        ensure!(mode == 0o444, "final evidence mode is not 0444");
        Ok(())
    }
}

fn write_json(file: &mut fs::File, value: &impl Serialize) -> Result<()> {
    let mut bytes = serde_json::to_vec_pretty(value)?;
    bytes.push(b'\n');
    file.write_all(&bytes)?;
    file.sync_all()?;
    Ok(())
}

/// Execute the destructive devnet-only tag-64 close/refund smoke test.
#[allow(clippy::too_many_lines)]
pub fn execute(arguments: &[String]) -> Result<SpendDevnetCloseEvidence> {
    let config = parse_args(arguments)?;
    ensure!(
        config.execute_interlock,
        "tag64 close requires --execute-devnet-tag64-close"
    );
    ensure!(
        config.acknowledgement.as_deref() == Some(EXECUTE_ACK),
        "tag64 close acknowledgement mismatch; exact required value: {EXECUTE_ACK}"
    );

    let rpc_origin_redacted = rpc_origin(&config.rpc_url)?;
    let rpc = Rpc::new(config.rpc_url.clone())?;
    let genesis_hash = rpc.genesis_hash()?;
    ensure!(
        genesis_hash == DEVNET_GENESIS_HASH,
        "tag64 close requires the pinned Solana devnet genesis"
    );

    let payer = secure_keypair(&config.payer_keypair)?;
    let proof = secure_keypair(&config.proof_account_keypair)?;
    ensure!(
        payer.pubkey() != proof.pubkey(),
        "payer and proof-account keypairs must differ"
    );
    ensure!(
        proof.pubkey() != aspis_verifier::id(),
        "proof-account key must not equal the Spend program id"
    );
    ensure!(
        proof.pubkey() == config.expected_proof_account,
        "proof-account keypair does not match --expected-proof-account; refusing destructive close"
    );
    let sbf = exact_regular_file(&config.sbf)?;
    ensure!(!sbf.is_empty(), "SBF file must not be empty");
    ensure!(
        sbf.len() <= config.program_max_len,
        "SBF exceeds declared ProgramData maximum length"
    );

    // Acquire the blockhash first, then read the proof and finally the exact
    // executable image. No RPC call intervenes between the last executable
    // check and simulation of the signed wire.
    let blockhash = rpc.latest_blockhash()?;
    let (proof_before_account, proof_before) =
        sealed_proof_exact(rpc.account(&proof.pubkey())?, proof.pubkey())?;
    ensure!(
        proof_before.stored_proof_sha256 == config.expected_proof_sha256,
        "sealed proof payload does not match --expected-proof-sha256; refusing destructive close"
    );
    let program_before =
        deployed_program_exact(&rpc, &sbf, config.program_max_len, payer.pubkey())?;

    let instruction = Instruction {
        program_id: aspis_verifier::id(),
        accounts: vec![
            AccountMeta::new(proof.pubkey(), true),
            AccountMeta::new(payer.pubkey(), true),
        ],
        // The production minimal dispatcher is explicitly a one-byte tag.
        data: vec![TAG_CLOSE_FINALIZED_PROOF],
    };
    ensure!(instruction.data == [TAG_CLOSE_FINALIZED_PROOF]);
    ensure!(
        instruction.accounts[0].is_signer && instruction.accounts[0].is_writable,
        "proof account meta must be writable signer"
    );
    ensure!(
        instruction.accounts[1].is_signer && instruction.accounts[1].is_writable,
        "refund payer meta must be writable signer"
    );
    let transaction = Transaction::new_signed_with_payer(
        &[instruction],
        Some(&payer.pubkey()),
        &[&payer, &proof],
        blockhash,
    );
    transaction
        .verify()
        .map_err(|error| anyhow!("locally verify signed tag64 transaction: {error}"))?;
    ensure!(
        transaction.signatures.len() == 2,
        "tag64 wire must contain exactly payer and proof signatures"
    );
    ensure!(
        transaction.message.header.num_required_signatures == 2,
        "tag64 message requires an unexpected signer count"
    );
    let wire = bincode::serialize(&transaction)?;
    let wire_sha256 = sha256(&wire);
    let message_sha256 = sha256(&bincode::serialize(&transaction.message)?);
    let expected_signature = transaction.signatures[0];

    let mut reservation = EvidenceReservation::reserve(&config.evidence)?;
    reservation.mark_prepared(expected_signature, &wire_sha256)?;

    let simulation = rpc.simulate_exact(&wire)?;
    ensure!(
        simulation.error.is_none(),
        "exact signed tag64 simulation rejected: {:?}",
        simulation.error
    );
    let simulation_evidence = SimulationEvidence {
        exact_signed_wire_simulated: true,
        error: None,
        compute_units_consumed: simulation.units,
        log_count: simulation.logs.len(),
        logs_sha256: joined_logs_sha256(&simulation.logs),
    };

    // `wire` is deliberately not reconstructed after simulation.
    rpc.send_exact_once(&wire, &expected_signature)?;
    let finalized_slot = rpc.wait_finalized(&expected_signature)?;
    let finalized = rpc.finalized_transaction(&expected_signature, finalized_slot)?;
    ensure!(finalized.slot == finalized_slot);
    let landed_wire_sha256 = sha256(&finalized.wire);
    let landed_wire_identical = finalized.wire == wire;
    ensure!(
        landed_wire_identical,
        "finalized transaction wire differs from the simulated and submitted bytes"
    );

    let keys = &transaction.message.account_keys;
    ensure!(
        finalized.pre_balances.len() == keys.len() && finalized.post_balances.len() == keys.len(),
        "finalized balance arrays do not match the exact legacy message account count"
    );
    let account_index = |address: Pubkey| -> Result<usize> {
        keys.iter()
            .position(|key| *key == address)
            .with_context(|| format!("tag64 message omitted account {address}"))
    };
    let payer_index = account_index(payer.pubkey())?;
    let proof_index = account_index(proof.pubkey())?;
    let program_index = account_index(aspis_verifier::id())?;
    ensure!(payer_index != proof_index, "payer/proof indices alias");
    let payer_pre = finalized.pre_balances[payer_index];
    let payer_post = finalized.post_balances[payer_index];
    let proof_pre = finalized.pre_balances[proof_index];
    let proof_post = finalized.post_balances[proof_index];
    ensure!(
        proof_pre == proof_before_account.lamports,
        "transaction proof pre-balance differs from validated sealed account"
    );
    ensure!(proof_post == 0, "closed proof post-balance is not zero");
    let refund_lamports = proof_pre
        .checked_sub(proof_post)
        .context("closed proof balance increased")?;
    ensure!(
        refund_lamports == proof_before_account.lamports,
        "tag64 did not refund the full proof-account balance"
    );
    let payer_delta_plus_fee =
        i128::from(payer_post) - i128::from(payer_pre) + i128::from(finalized.fee);
    let exact_refund_equation_reconciled = payer_delta_plus_fee == i128::from(refund_lamports);
    ensure!(
        exact_refund_equation_reconciled,
        "payer delta plus fee does not equal the full proof refund"
    );
    let every_other_unchanged = finalized
        .pre_balances
        .iter()
        .zip(&finalized.post_balances)
        .enumerate()
        .all(|(index, (pre, post))| index == payer_index || index == proof_index || pre == post);
    ensure!(
        every_other_unchanged,
        "tag64 changed a message-account balance other than payer/proof"
    );
    ensure!(
        finalized.pre_balances[program_index] == program_before.program.lamports
            && finalized.post_balances[program_index] == program_before.program.lamports,
        "Spend Program account balance changed during tag64"
    );

    let proof_after = rpc.account(&proof.pubkey())?;
    ensure!(
        proof_after.account.is_none(),
        "proof account still exists after finalized tag64"
    );
    let program_after = deployed_program_exact(&rpc, &sbf, config.program_max_len, payer.pubkey())?;
    let program_continuity = program_after.continuity_from(&program_before);
    ensure!(
        program_continuity.all_unchanged(),
        "Spend program or ProgramData changed across tag64 finality"
    );
    let landed_compute_units = finalized
        .compute_units
        .context("finalized tag64 transaction omitted computeUnitsConsumed")?;

    let instruction_accounts = vec![
        InstructionAccountEvidence {
            index: 0,
            address: proof.pubkey().to_string(),
            writable: true,
            signer: true,
            role: "sealed_program_owned_proof_to_close",
        },
        InstructionAccountEvidence {
            index: 1,
            address: payer.pubkey().to_string(),
            writable: true,
            signer: true,
            role: "system_owned_refund_destination_and_fee_payer",
        },
    ];
    let refund = RefundEvidence {
        fee_lamports: finalized.fee,
        payer_account_index: payer_index,
        proof_account_index: proof_index,
        payer_pre_lamports: payer_pre,
        payer_post_lamports: payer_post,
        proof_pre_lamports: proof_pre,
        proof_post_lamports: proof_post,
        refund_lamports,
        payer_delta_plus_fee_lamports: payer_delta_plus_fee,
        exact_refund_equation_reconciled,
        every_other_message_account_balance_unchanged: every_other_unchanged,
    };
    let evidence_path = config.evidence.display().to_string();
    let evidence = SpendDevnetCloseEvidence {
        artifact: "spend_devnet_tag64_close_refund_smoke",
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        network: "solana-devnet",
        genesis_hash,
        rpc_origin_redacted,
        program_id: aspis_verifier::id().to_string(),
        payer_pubkey: payer.pubkey().to_string(),
        proof_account_pubkey: proof.pubkey().to_string(),
        expected_proof_account_pubkey: config.expected_proof_account.to_string(),
        expected_proof_payload_sha256: config.expected_proof_sha256.clone(),
        destructive_target_identity_exact: true,
        destructive_execute_interlock_present: true,
        destructive_acknowledgement_exact: true,
        sbf_path: config.sbf.display().to_string(),
        sbf_bytes: sbf.len(),
        sbf_sha256: sha256(&sbf),
        program_max_len: config.program_max_len,
        program_before: program_before.evidence(),
        program_after: program_after.evidence(),
        program_continuity,
        exact_sbf_max_len_authority_before: true,
        exact_sbf_max_len_authority_after: true,
        proof_before,
        instruction_tag: TAG_CLOSE_FINALIZED_PROOF,
        instruction_data_hex: format!("{TAG_CLOSE_FINALIZED_PROOF:02x}"),
        instruction_accounts,
        signature: expected_signature.to_string(),
        finalized_slot,
        signed_wire_bytes: wire.len(),
        signed_wire_sha256: wire_sha256,
        message_sha256,
        simulation: simulation_evidence,
        submitted_identically_to_simulation: true,
        landed_wire_sha256,
        landed_wire_identical_to_submitted: true,
        landed_message_account_count: keys.len(),
        landed_compute_units_consumed: landed_compute_units,
        landed_log_count: finalized.logs.len(),
        landed_logs_sha256: joined_logs_sha256(&finalized.logs),
        refund,
        refund_lamports,
        proof_account_absent_after_finality: true,
        evidence_path,
        evidence_file_mode: 0o444,
        explicit_scope: vec![
            "This artifact proves only one finalized tag64 close/refund on the pinned Solana devnet genesis.",
            "It is not mainnet-beta execution evidence and makes no mainnet deployment claim.",
            "The proof account is irreversibly destroyed; its complete pre-balance is refunded to the explicit payer apart from the separately reconciled transaction fee.",
            "The Spend Program and ProgramData raw account images are byte-for-byte unchanged across the transaction.",
        ],
    };
    reservation.commit(&evidence)?;
    Ok(evidence)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rpc_policy_requires_https_and_redacts_path() {
        assert!(rpc_origin("http://api.devnet.solana.com").is_err());
        assert_eq!(
            rpc_origin("https://rpc.example.test/private?token=secret").unwrap(),
            "https://rpc.example.test/<redacted>"
        );
    }

    #[test]
    fn parser_rejects_unknown_arguments() {
        assert!(parse_args(&["--wat".to_owned(), "x".to_owned()]).is_err());
    }
}
