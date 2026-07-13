//! Fail-closed Profile23 devnet rehearsal.
//!
//! `readiness` performs only filesystem and read-only RPC calls. `execute`
//! exists as a separate surface and requires two explicit interlocks. Every
//! path and RPC endpoint is supplied on the command line; Solana CLI ambient
//! configuration is never consulted.

use std::{
    collections::BTreeMap,
    fs::{self, OpenOptions},
    io::Write,
    os::unix::fs::PermissionsExt,
    path::{Path, PathBuf},
    process::Command,
    str::FromStr,
    thread,
    time::{Duration, Instant},
};

use anyhow::{anyhow, bail, ensure, Context, Result};
use base64::{engine::general_purpose::STANDARD as BASE64, Engine};
use borsh::to_vec;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
#[allow(deprecated)]
use solana_sdk::system_instruction;
use solana_sdk::{
    bpf_loader_upgradeable::{self, UpgradeableLoaderState},
    compute_budget::ComputeBudgetInstruction,
    hash::Hash,
    instruction::{AccountMeta, Instruction},
    pubkey::Pubkey,
    signature::{read_keypair_file, Keypair, Signature, Signer},
    system_program,
    transaction::{Transaction, VersionedTransaction},
};

use aspis_verifier::{
    atomic_payment::{
        atomic_nullifier_address, AtomicPaymentPublicInputs, AtomicPoolStateV1,
        ATOMIC_NULLIFIER_MAGIC, ATOMIC_NULLIFIER_MARKER_LEN, ATOMIC_NULLIFIER_VERSION,
        ATOMIC_POOL_STATE_LEN,
    },
    AspisInstruction, PROOF_ACCOUNT_HEADER_LEN,
};

const DEVNET_GENESIS_HASH: &str = "EtWTRABZaYq6iMfeYKouRu166VU2xqa1";
const EXECUTE_ACK: &str =
    "I_ACKNOWLEDGE_PROFILE23_DEVNET_REHEARSAL_MUTATES_DEVNET_AND_SPENDS_DEVNET_SOL";
const CU_LIMIT: u32 = 1_400_000;
const HEAP_FRAME_BYTES: u32 = 262_144;
const UPLOAD_CHUNK_BYTES: usize = 640;
const PROOF_MAGIC: &[u8; 4] = b"ASPU";
const PROOF_AUTHORITY_OFFSET: usize = 8;
const PROGRAMDATA_METADATA_BYTES: usize = 45;
const PROGRAM_ACCOUNT_BYTES: usize = 36;
const BUFFER_METADATA_BYTES: usize = 37;
const DEFAULT_CONFIRM_TIMEOUT: Duration = Duration::from_secs(180);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CommandMode {
    Readiness,
    Execute,
}

#[derive(Clone, Debug)]
struct DevnetConfig {
    rpc_url: String,
    payer_keypair: PathBuf,
    program_keypair: PathBuf,
    pool_keypair: PathBuf,
    proof_account_keypair: PathBuf,
    release: PathBuf,
    sbf: PathBuf,
    proof: PathBuf,
    statement: PathBuf,
    solana_cli: PathBuf,
    evidence: PathBuf,
    program_max_len: usize,
    fee_reserve_lamports: u64,
    execute_interlock: bool,
    acknowledgement: Option<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct DevnetGate {
    pub name: String,
    pub passed: bool,
    pub evidence: String,
}

#[derive(Clone, Debug, Default, Serialize)]
pub struct DevnetRentBudget {
    pub program_buffer_lamports: Option<u64>,
    pub programdata_lamports: Option<u64>,
    pub program_account_lamports: Option<u64>,
    pub pool_account_lamports: Option<u64>,
    pub proof_account_lamports: Option<u64>,
    pub nullifier_account_lamports: Option<u64>,
    pub fee_reserve_lamports: u64,
    pub conservative_required_lamports: Option<u64>,
    pub payer_balance_lamports: Option<u64>,
    pub surplus_lamports: Option<i128>,
}

#[derive(Clone, Debug, Serialize)]
pub struct Profile23DevnetReadiness {
    pub artifact: &'static str,
    pub generated_at_utc: String,
    pub mode: &'static str,
    pub mutations_performed: bool,
    pub ready: bool,
    pub expected_genesis_hash: &'static str,
    pub observed_genesis_hash: Option<String>,
    pub rpc_origin_redacted: Option<String>,
    pub program_id: String,
    pub payer_pubkey: Option<String>,
    pub pool_pubkey: Option<String>,
    pub proof_account_pubkey: Option<String>,
    pub proof_sha256: Option<String>,
    pub sbf_sha256: Option<String>,
    pub release_sha256: Option<String>,
    pub statement_sha256: Option<String>,
    pub nullifier_address: Option<String>,
    pub program_already_deployed: Option<bool>,
    pub rent_budget: DevnetRentBudget,
    pub gates: Vec<DevnetGate>,
    pub blockers: Vec<String>,
    pub explicit_nonclaims: Vec<&'static str>,
}

#[derive(Clone, Debug, Serialize)]
pub struct TransactionEvidence {
    pub label: String,
    pub signature: String,
    pub finalized_slot: u64,
    pub message_sha256: String,
    pub serialized_transaction_sha256: String,
    pub compute_units_consumed: Option<u64>,
    pub identical_wire_retries: u8,
}

#[derive(Clone, Debug, Serialize)]
pub struct AccountEvidence {
    pub address: String,
    pub lamports: u64,
    pub owner: String,
    pub executable: bool,
    pub data_len: usize,
    pub data_sha256: String,
    pub raw_account_image_sha256: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct Profile23DevnetEvidence {
    pub artifact: &'static str,
    pub generated_at_utc: String,
    pub network: &'static str,
    pub genesis_hash: String,
    pub program_id: String,
    pub release_certificate_path: String,
    pub release_certificate_sha256: String,
    pub release_gate_count: usize,
    pub sbf_path: String,
    pub sbf_bytes: usize,
    pub sbf_sha256: String,
    pub proof_path: String,
    pub proof_bytes: usize,
    pub proof_sha256: String,
    pub statement_path: String,
    pub statement_sha256: String,
    pub program_max_len: usize,
    pub deployment: Option<TransactionEvidence>,
    pub setup_transactions: Vec<TransactionEvidence>,
    pub final_transaction: TransactionEvidence,
    pub final_transaction_simulation_cu: u64,
    pub final_transaction_wire_sha256: String,
    pub final_transaction_message_sha256: String,
    pub final_transaction_submitted_identically_to_simulation: bool,
    pub proof_account: AccountEvidence,
    pub proof_account_finalized: bool,
    pub post_finalize_upload_rejected: bool,
    pub post_finalize_second_finalize_rejected: bool,
    pub pool_before: AccountEvidence,
    pub pool_after: AccountEvidence,
    pub sequence_before: u64,
    pub sequence_after: u64,
    pub nullifier_before: Option<AccountEvidence>,
    pub nullifier_after: AccountEvidence,
    pub duplicate_simulation_rejected: bool,
    pub evidence_path: String,
    pub evidence_file_mode: u32,
    pub explicit_scope: Vec<&'static str>,
}

#[derive(Clone, Debug, Deserialize)]
struct StatementSidecar {
    artifact: String,
    pool_hex: String,
    sequence: u64,
    current_anchor_hex: String,
    nullifier_hex: String,
    output_commitment_hex: String,
    output_anchor_hex: String,
    asset_id: u32,
    fee: u32,
    witness_independent_public_metadata: bool,
}

impl StatementSidecar {
    fn pool(&self) -> Result<Pubkey> {
        Ok(Pubkey::new_from_array(decode_hex_32(&self.pool_hex)?))
    }

    fn public(&self) -> Result<AtomicPaymentPublicInputs> {
        let public = AtomicPaymentPublicInputs {
            current_anchor: decode_hex_32(&self.current_anchor_hex)?,
            nullifier: decode_hex_32(&self.nullifier_hex)?,
            output_commitment: decode_hex_32(&self.output_commitment_hex)?,
            output_anchor: decode_hex_32(&self.output_anchor_hex)?,
            asset_id: self.asset_id,
            fee: self.fee,
        };
        aspis_statement::decode_digest_canonical(&public.current_anchor)
            .map_err(|_| anyhow!("sidecar current anchor is noncanonical"))?;
        aspis_statement::decode_digest_canonical(&public.nullifier)
            .map_err(|_| anyhow!("sidecar nullifier is noncanonical"))?;
        aspis_statement::decode_digest_canonical(&public.output_commitment)
            .map_err(|_| anyhow!("sidecar output commitment is noncanonical"))?;
        aspis_statement::decode_digest_canonical(&public.output_anchor)
            .map_err(|_| anyhow!("sidecar output anchor is noncanonical"))?;
        aspis_statement::decode_asset_id_canonical(public.asset_id)
            .map_err(|_| anyhow!("sidecar asset id is noncanonical"))?;
        Ok(public)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RpcAccount {
    lamports: u64,
    owner: Pubkey,
    executable: bool,
    data: Vec<u8>,
}

impl RpcAccount {
    fn evidence(&self, address: Pubkey) -> AccountEvidence {
        let mut raw = Vec::with_capacity(8 + 32 + 1 + self.data.len());
        raw.extend_from_slice(&self.lamports.to_le_bytes());
        raw.extend_from_slice(self.owner.as_ref());
        raw.push(u8::from(self.executable));
        raw.extend_from_slice(&self.data);
        AccountEvidence {
            address: address.to_string(),
            lamports: self.lamports,
            owner: self.owner.to_string(),
            executable: self.executable,
            data_len: self.data.len(),
            data_sha256: sha256(&self.data),
            raw_account_image_sha256: sha256(&raw),
        }
    }
}

struct Rpc {
    endpoint: String,
    client: reqwest::blocking::Client,
}

#[derive(Clone, Debug)]
struct Simulation {
    units: Option<u64>,
    error: Option<Value>,
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
        let value: Value = response
            .json()
            .with_context(|| format!("RPC {method} non-JSON response"))?;
        if let Some(error) = value.get("error") {
            bail!("RPC {method} error: {error}");
        }
        value
            .get("result")
            .cloned()
            .ok_or_else(|| anyhow!("RPC {method} omitted result"))
    }

    fn genesis_hash(&self) -> Result<String> {
        self.call("getGenesisHash", json!([]))?
            .as_str()
            .map(ToOwned::to_owned)
            .context("getGenesisHash result was not a string")
    }

    fn latest_blockhash(&self) -> Result<Hash> {
        self.call("getLatestBlockhash", json!([{"commitment":"finalized"}]))?["value"]["blockhash"]
            .as_str()
            .context("latest blockhash missing")?
            .parse()
            .context("latest blockhash invalid")
    }

    fn account(&self, address: &Pubkey) -> Result<Option<RpcAccount>> {
        let result = self.call(
            "getAccountInfo",
            json!([address.to_string(), {"encoding":"base64","commitment":"finalized"}]),
        )?;
        let value = &result["value"];
        if value.is_null() {
            return Ok(None);
        }
        Ok(Some(RpcAccount {
            lamports: value["lamports"]
                .as_u64()
                .context("account lamports missing")?,
            owner: value["owner"]
                .as_str()
                .context("account owner missing")?
                .parse()?,
            executable: value["executable"]
                .as_bool()
                .context("account executable flag missing")?,
            data: BASE64.decode(
                value["data"][0]
                    .as_str()
                    .context("account base64 data missing")?,
            )?,
        }))
    }

    fn rent(&self, bytes: usize) -> Result<u64> {
        self.call("getMinimumBalanceForRentExemption", json!([bytes]))?
            .as_u64()
            .context("rent result was not u64")
    }

    fn balance(&self, address: &Pubkey) -> Result<u64> {
        self.call(
            "getBalance",
            json!([address.to_string(), {"commitment":"finalized"}]),
        )?["value"]
            .as_u64()
            .context("balance result was not u64")
    }

    fn simulate_exact(&self, wire: &[u8]) -> Result<Simulation> {
        let result = self.call(
            "simulateTransaction",
            json!([BASE64.encode(wire), {
                "encoding":"base64",
                "sigVerify":true,
                "replaceRecentBlockhash":false,
                "commitment":"finalized"
            }]),
        )?;
        let error = if result["value"]["err"].is_null() {
            None
        } else {
            Some(result["value"]["err"].clone())
        };
        Ok(Simulation {
            units: result["value"]["unitsConsumed"].as_u64(),
            error,
        })
    }

    fn signature_status(
        &self,
        signature: &Signature,
    ) -> Result<Option<(u64, Option<Value>, String)>> {
        let result = self.call(
            "getSignatureStatuses",
            json!([[signature.to_string()], {"searchTransactionHistory":true}]),
        )?;
        let status = &result["value"][0];
        if status.is_null() {
            return Ok(None);
        }
        Ok(Some((
            status["slot"].as_u64().context("signature slot missing")?,
            if status["err"].is_null() {
                None
            } else {
                Some(status["err"].clone())
            },
            status["confirmationStatus"]
                .as_str()
                .unwrap_or("unknown")
                .to_owned(),
        )))
    }

    fn wait_finalized(&self, signature: &Signature) -> Result<u64> {
        let started = Instant::now();
        loop {
            if let Some((slot, error, confirmation)) = self.signature_status(signature)? {
                if let Some(error) = error {
                    bail!("transaction {signature} failed: {error}");
                }
                if confirmation == "finalized" {
                    return Ok(slot);
                }
            }
            ensure!(
                started.elapsed() < DEFAULT_CONFIRM_TIMEOUT,
                "transaction {signature} did not finalize before timeout"
            );
            thread::sleep(Duration::from_millis(500));
        }
    }

    fn transaction_cu(&self, signature: &Signature) -> Result<Option<u64>> {
        let result = self.call(
            "getTransaction",
            json!([signature.to_string(), {
                "encoding":"json",
                "commitment":"finalized",
                "maxSupportedTransactionVersion":0
            }]),
        )?;
        Ok(result["meta"]["computeUnitsConsumed"].as_u64())
    }

    fn transaction_wire_and_message_hash(&self, signature: &Signature) -> Result<(String, String)> {
        let result = self.call(
            "getTransaction",
            json!([signature.to_string(), {
                "encoding":"base64",
                "commitment":"finalized",
                "maxSupportedTransactionVersion":0
            }]),
        )?;
        let encoded = result["transaction"][0]
            .as_str()
            .context("finalized transaction base64 missing")?;
        let wire = BASE64.decode(encoded)?;
        let transaction: VersionedTransaction =
            bincode::deserialize(&wire).context("decode finalized versioned transaction")?;
        Ok((
            sha256(&wire),
            sha256(&bincode::serialize(&transaction.message)?),
        ))
    }

    fn submit_wire(
        &self,
        wire: &[u8],
        expected_signature: Signature,
        allow_one_identical_retry: bool,
        label: &str,
        message_sha256: String,
    ) -> Result<TransactionEvidence> {
        let encoded = BASE64.encode(wire);
        let send = || {
            self.call(
                "sendTransaction",
                json!([encoded, {
                    "encoding":"base64",
                    "skipPreflight":false,
                    "preflightCommitment":"finalized",
                    "maxRetries":0
                }]),
            )
        };
        let mut retries = 0u8;
        let first = send();
        match first {
            Ok(value) => {
                ensure!(
                    value.as_str() == Some(expected_signature.to_string().as_str()),
                    "RPC returned a different signature for {label}"
                );
            }
            Err(first_error) => {
                if self.signature_status(&expected_signature)?.is_none()
                    && allow_one_identical_retry
                {
                    retries = 1;
                    let value = send().with_context(|| {
                        format!(
                            "identical-wire retry failed after ambiguous first submit: {first_error}"
                        )
                    })?;
                    ensure!(
                        value.as_str() == Some(expected_signature.to_string().as_str()),
                        "RPC returned a different signature on identical retry"
                    );
                } else if self.signature_status(&expected_signature)?.is_none() {
                    return Err(first_error).with_context(|| format!("submit {label}"));
                }
            }
        }
        let slot = self.wait_finalized(&expected_signature)?;
        Ok(TransactionEvidence {
            label: label.to_owned(),
            signature: expected_signature.to_string(),
            finalized_slot: slot,
            message_sha256,
            serialized_transaction_sha256: sha256(wire),
            compute_units_consumed: self.transaction_cu(&expected_signature)?,
            identical_wire_retries: retries,
        })
    }

    fn submit_transaction(
        &self,
        transaction: &Transaction,
        label: &str,
    ) -> Result<TransactionEvidence> {
        let wire = bincode::serialize(transaction)?;
        self.submit_wire(
            &wire,
            transaction.signatures[0],
            false,
            label,
            sha256(&bincode::serialize(&transaction.message)?),
        )
    }
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn decode_hex_32(value: &str) -> Result<[u8; 32]> {
    ensure!(value.len() == 64, "expected 64 hexadecimal characters");
    let mut decoded = [0u8; 32];
    for (index, byte) in decoded.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&value[2 * index..2 * index + 2], 16)
            .context("invalid hexadecimal byte")?;
    }
    Ok(decoded)
}

fn parse_args(arguments: &[String], mode: CommandMode) -> Result<DevnetConfig> {
    let mut values = BTreeMap::<String, String>::new();
    let mut execute_interlock = false;
    let mut index = 0usize;
    while index < arguments.len() {
        let key = &arguments[index];
        if key == "--execute-devnet" {
            ensure!(!execute_interlock, "duplicate --execute-devnet");
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
        "--pool-keypair",
        "--proof-account-keypair",
        "--release",
        "--sbf",
        "--proof",
        "--statement",
        "--solana-cli",
        "--evidence",
        "--program-max-len",
        "--fee-reserve-lamports",
        "--acknowledgement",
    ];
    for key in values.keys() {
        ensure!(allowed.contains(&key.as_str()), "unknown argument {key}");
    }
    if mode == CommandMode::Readiness {
        ensure!(
            !execute_interlock && !values.contains_key("--acknowledgement"),
            "readiness refuses execution interlocks"
        );
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
    Ok(DevnetConfig {
        rpc_url: required("--rpc-url")?,
        payer_keypair: absolute("--payer-keypair")?,
        program_keypair: absolute("--program-keypair")?,
        pool_keypair: absolute("--pool-keypair")?,
        proof_account_keypair: absolute("--proof-account-keypair")?,
        release: absolute("--release")?,
        sbf: absolute("--sbf")?,
        proof: absolute("--proof")?,
        statement: absolute("--statement")?,
        solana_cli: absolute("--solana-cli")?,
        evidence: absolute("--evidence")?,
        program_max_len: required("--program-max-len")?
            .parse()
            .context("--program-max-len is not usize")?,
        fee_reserve_lamports: required("--fee-reserve-lamports")?
            .parse()
            .context("--fee-reserve-lamports is not u64")?,
        execute_interlock,
        acknowledgement: values.get("--acknowledgement").cloned(),
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
        "input must be a regular non-symlink file: {}",
        path.display()
    );
    fs::read(path).with_context(|| format!("read {}", path.display()))
}

fn rpc_origin(endpoint: &str) -> Result<String> {
    let url = reqwest::Url::parse(endpoint).context("invalid RPC URL")?;
    ensure!(url.scheme() == "https", "devnet RPC must use HTTPS");
    ensure!(
        url.username().is_empty() && url.password().is_none(),
        "RPC credentials may not use URL userinfo"
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

fn release_artifacts_exact(release: &Value, workspace_root: &Path) -> Result<()> {
    let artifacts = release["source_artifacts"]
        .as_array()
        .context("release source_artifacts missing")?;
    for artifact in artifacts {
        let path = artifact["path"]
            .as_str()
            .context("release source path missing")?;
        let expected_len = artifact["bytes"]
            .as_u64()
            .context("release source bytes missing")?;
        let expected_sha = artifact["sha256"]
            .as_str()
            .context("release source hash missing")?;
        let path = if Path::new(path).is_absolute() {
            PathBuf::from(path)
        } else {
            workspace_root.join(path)
        };
        let bytes = exact_regular_file(&path)?;
        ensure!(
            bytes.len() as u64 == expected_len,
            "release source length drift: {}",
            path.display()
        );
        ensure!(
            sha256(&bytes) == expected_sha,
            "release source hash drift: {}",
            path.display()
        );
    }
    Ok(())
}

fn parse_program(account: &RpcAccount) -> Result<Pubkey> {
    ensure!(
        account.owner == bpf_loader_upgradeable::id() && account.executable,
        "program account is not executable BPFLoaderUpgradeable"
    );
    match bincode::deserialize(&account.data)? {
        UpgradeableLoaderState::Program {
            programdata_address,
        } => Ok(programdata_address),
        _ => bail!("declared program address is not a Program account"),
    }
}

fn deployed_program_exact(
    rpc: &Rpc,
    program_id: &Pubkey,
    expected_sbf: &[u8],
    expected_max_len: usize,
    expected_authority: &Pubkey,
) -> Result<bool> {
    let Some(program) = rpc.account(program_id)? else {
        return Ok(false);
    };
    let programdata_address = parse_program(&program)?;
    let programdata = rpc
        .account(&programdata_address)?
        .context("ProgramData account missing")?;
    ensure!(programdata.owner == bpf_loader_upgradeable::id());
    let state: UpgradeableLoaderState = bincode::deserialize(&programdata.data)?;
    let UpgradeableLoaderState::ProgramData {
        upgrade_authority_address,
        ..
    } = state
    else {
        bail!("linked account is not ProgramData")
    };
    ensure!(
        upgrade_authority_address == Some(*expected_authority),
        "devnet rehearsal upgrade authority does not equal explicit payer"
    );
    let code = programdata
        .data
        .get(PROGRAMDATA_METADATA_BYTES..)
        .context("ProgramData shorter than metadata")?;
    ensure!(
        code.len() == expected_max_len,
        "ProgramData max length mismatch"
    );
    ensure!(
        code.get(..expected_sbf.len()) == Some(expected_sbf),
        "deployed program bytes differ from release SBF"
    );
    ensure!(
        code[expected_sbf.len()..].iter().all(|byte| *byte == 0),
        "deployed ProgramData padding is nonzero"
    );
    Ok(true)
}

fn nullifier_compatible(account: Option<&RpcAccount>, program_id: &Pubkey) -> bool {
    match account {
        None => true,
        Some(account) if account.owner == system_program::id() => {
            !account.executable && account.data.is_empty()
        }
        Some(account) if account.owner == *program_id => {
            !account.executable
                && account.data.len() == ATOMIC_NULLIFIER_MARKER_LEN
                && account.data.iter().all(|byte| *byte == 0)
        }
        Some(_) => false,
    }
}

fn gate(gates: &mut Vec<DevnetGate>, name: &str, passed: bool, evidence: impl Into<String>) {
    gates.push(DevnetGate {
        name: name.to_owned(),
        passed,
        evidence: evidence.into(),
    });
}

fn inspect(workspace_root: &Path, config: &DevnetConfig) -> Result<Profile23DevnetReadiness> {
    let mut gates = Vec::new();
    let rpc_origin = rpc_origin(&config.rpc_url).ok();
    gate(
        &mut gates,
        "explicit_https_rpc",
        rpc_origin.is_some(),
        format!("redacted_origin={rpc_origin:?}"),
    );
    let rpc = Rpc::new(config.rpc_url.clone())?;
    let observed_genesis = rpc.genesis_hash().ok();
    gate(
        &mut gates,
        "exact_devnet_genesis",
        observed_genesis.as_deref() == Some(DEVNET_GENESIS_HASH),
        format!("observed={observed_genesis:?}, expected={DEVNET_GENESIS_HASH}"),
    );

    let payer = secure_keypair(&config.payer_keypair).ok();
    let program = secure_keypair(&config.program_keypair).ok();
    let pool = secure_keypair(&config.pool_keypair).ok();
    let proof_account = secure_keypair(&config.proof_account_keypair).ok();
    gate(
        &mut gates,
        "payer_keypair_secure",
        payer.is_some(),
        "explicit secure keypair",
    );
    gate(
        &mut gates,
        "program_keypair_secure",
        program.is_some(),
        "explicit secure keypair",
    );
    gate(
        &mut gates,
        "pool_keypair_secure",
        pool.is_some(),
        "explicit secure keypair",
    );
    gate(
        &mut gates,
        "proof_account_keypair_secure",
        proof_account.is_some(),
        "explicit secure keypair",
    );
    let declared_program = aspis_verifier::id();
    gate(
        &mut gates,
        "program_keypair_matches_declared_id",
        program.as_ref().map(Signer::pubkey) == Some(declared_program),
        format!(
            "declared={declared_program}, explicit={:?}",
            program.as_ref().map(Signer::pubkey)
        ),
    );
    let distinct_keys = payer
        .as_ref()
        .zip(program.as_ref())
        .zip(pool.as_ref())
        .zip(proof_account.as_ref())
        .is_some_and(|(((payer, program), pool), proof_account)| {
            let keys = [
                payer.pubkey(),
                program.pubkey(),
                pool.pubkey(),
                proof_account.pubkey(),
            ];
            (0..keys.len())
                .all(|left| (left + 1..keys.len()).all(|right| keys[left] != keys[right]))
        });
    gate(
        &mut gates,
        "payer_program_pool_and_proof_keys_distinct",
        distinct_keys,
        "all four explicit signer identities are pairwise distinct",
    );

    let release_bytes = exact_regular_file(&config.release).ok();
    let release_sha = release_bytes.as_deref().map(sha256);
    let release = release_bytes
        .as_deref()
        .and_then(|bytes| serde_json::from_slice::<Value>(bytes).ok());
    let release_gates = release.as_ref().and_then(|value| value["gates"].as_array());
    let release_green = release.as_ref().is_some_and(|value| {
        value["released"].as_bool() == Some(true)
            && value["status"].as_str() == Some("released_all_required_gates_green")
    }) && release_gates.is_some_and(|items| {
        items.len() == 30
            && items
                .iter()
                .all(|item| item["passed"].as_bool() == Some(true))
    });
    gate(
        &mut gates,
        "release_certificate_exactly_30_green_gates",
        release_green,
        format!(
            "gate_count={:?}, released={release_green}",
            release_gates.map(Vec::len)
        ),
    );
    let source_exact = release
        .as_ref()
        .is_some_and(|release| release_artifacts_exact(release, workspace_root).is_ok());
    gate(
        &mut gates,
        "release_source_hashes_exact",
        source_exact,
        "all release-pinned source artifacts rehashed",
    );

    let proof = exact_regular_file(&config.proof).ok();
    let sbf = exact_regular_file(&config.sbf).ok();
    let statement_bytes = exact_regular_file(&config.statement).ok();
    let proof_sha = proof.as_deref().map(sha256);
    let sbf_sha = sbf.as_deref().map(sha256);
    let statement_sha = statement_bytes.as_deref().map(sha256);
    let release_proof_exact = release.as_ref().is_some_and(|release| {
        release["proof"]["bytes"].as_u64() == proof.as_ref().map(|bytes| bytes.len() as u64)
            && release["proof"]["sha256"].as_str() == proof_sha.as_deref()
    });
    let release_sbf_exact = release.as_ref().is_some_and(|release| {
        release["default_production_sbf"]["bytes"].as_u64()
            == sbf.as_ref().map(|bytes| bytes.len() as u64)
            && release["default_production_sbf"]["sha256"].as_str() == sbf_sha.as_deref()
    });
    gate(
        &mut gates,
        "explicit_proof_matches_release",
        release_proof_exact,
        format!("sha256={proof_sha:?}"),
    );
    gate(
        &mut gates,
        "explicit_sbf_matches_release",
        release_sbf_exact,
        format!("sha256={sbf_sha:?}"),
    );
    gate(
        &mut gates,
        "program_max_len_explicit_and_sufficient",
        sbf.as_ref()
            .is_some_and(|bytes| config.program_max_len >= bytes.len()),
        format!(
            "max_len={}, sbf_len={:?}",
            config.program_max_len,
            sbf.as_ref().map(Vec::len)
        ),
    );

    let statement = statement_bytes
        .as_deref()
        .and_then(|bytes| serde_json::from_slice::<StatementSidecar>(bytes).ok());
    let pool_pubkey = pool.as_ref().map(Signer::pubkey);
    let sidecar_valid = statement.as_ref().is_some_and(|statement| {
        statement.artifact == "profile23_production_statement"
            && statement.witness_independent_public_metadata
            && statement.public().is_ok()
            && statement.pool().ok() == pool_pubkey
    });
    gate(
        &mut gates,
        "fresh_pool_known_before_proof_and_release",
        sidecar_valid,
        format!("pool_pubkey={pool_pubkey:?}, sidecar_sha256={statement_sha:?}"),
    );

    let program_already_deployed = rpc
        .account(&declared_program)
        .ok()
        .map(|value| value.is_some());
    let program_ready = match (program_already_deployed, sbf.as_ref(), payer.as_ref()) {
        (Some(false), Some(_), Some(_)) => true,
        (Some(true), Some(sbf), Some(payer)) => deployed_program_exact(
            &rpc,
            &declared_program,
            sbf,
            config.program_max_len,
            &payer.pubkey(),
        )
        .unwrap_or(false),
        _ => false,
    };
    gate(
        &mut gates,
        "program_absent_or_exact_release_deployment",
        program_ready,
        format!("already_deployed={program_already_deployed:?}"),
    );

    let pool_absent = pool_pubkey
        .and_then(|key| rpc.account(&key).ok())
        .is_some_and(|account| account.is_none());
    let proof_account_pubkey = proof_account.as_ref().map(Signer::pubkey);
    let proof_account_absent = proof_account_pubkey
        .and_then(|key| rpc.account(&key).ok())
        .is_some_and(|account| account.is_none());
    gate(
        &mut gates,
        "fresh_pool_account_absent",
        pool_absent,
        format!("pool={pool_pubkey:?}"),
    );
    gate(
        &mut gates,
        "fresh_proof_account_absent",
        proof_account_absent,
        format!("proof_account={proof_account_pubkey:?}"),
    );

    let nullifier_address = statement
        .as_ref()
        .and_then(|statement| statement.public().ok())
        .map(|public| atomic_nullifier_address(&declared_program, &public.nullifier).0);
    let nullifier_state = nullifier_address
        .and_then(|address| rpc.account(&address).ok())
        .flatten();
    let nullifier_ready = nullifier_address.is_some()
        && nullifier_compatible(nullifier_state.as_ref(), &declared_program);
    gate(
        &mut gates,
        "canonical_nullifier_absent_or_prefunded_compatible",
        nullifier_ready,
        format!(
            "address={nullifier_address:?}, observed={}",
            nullifier_state.is_some()
        ),
    );

    let solana_cli_ok = fs::symlink_metadata(&config.solana_cli).is_ok_and(|metadata| {
        metadata.file_type().is_file()
            && !metadata.file_type().is_symlink()
            && metadata.permissions().mode() & 0o111 != 0
    });
    gate(
        &mut gates,
        "explicit_solana_cli_executable",
        solana_cli_ok,
        format!("path={}", config.solana_cli.display()),
    );
    gate(
        &mut gates,
        "evidence_path_does_not_exist",
        !config.evidence.exists(),
        format!("path={}", config.evidence.display()),
    );

    let mut rent_budget = DevnetRentBudget {
        fee_reserve_lamports: config.fee_reserve_lamports,
        ..DevnetRentBudget::default()
    };
    if let (Some(payer), Some(proof), Some(sbf)) = (payer.as_ref(), proof.as_ref(), sbf.as_ref()) {
        rent_budget.program_buffer_lamports = rpc
            .rent(BUFFER_METADATA_BYTES + config.program_max_len)
            .ok();
        rent_budget.programdata_lamports = rpc
            .rent(PROGRAMDATA_METADATA_BYTES + config.program_max_len)
            .ok();
        rent_budget.program_account_lamports = rpc.rent(PROGRAM_ACCOUNT_BYTES).ok();
        rent_budget.pool_account_lamports = rpc.rent(ATOMIC_POOL_STATE_LEN).ok();
        rent_budget.proof_account_lamports = rpc.rent(PROOF_ACCOUNT_HEADER_LEN + proof.len()).ok();
        rent_budget.nullifier_account_lamports = rpc.rent(ATOMIC_NULLIFIER_MARKER_LEN).ok();
        rent_budget.payer_balance_lamports = rpc.balance(&payer.pubkey()).ok();
        let setup = rent_budget
            .pool_account_lamports
            .zip(rent_budget.proof_account_lamports)
            .and_then(|(pool, proof)| pool.checked_add(proof))
            .and_then(|sum| {
                rent_budget
                    .nullifier_account_lamports
                    .and_then(|marker| sum.checked_add(marker))
            })
            .and_then(|sum| sum.checked_add(config.fee_reserve_lamports));
        let fresh = rent_budget
            .program_buffer_lamports
            .zip(rent_budget.programdata_lamports)
            .and_then(|(buffer, data)| buffer.checked_add(data))
            .and_then(|sum| {
                rent_budget
                    .program_account_lamports
                    .and_then(|program| sum.checked_add(program))
            })
            .and_then(|sum| setup.and_then(|setup| sum.checked_add(setup)));
        rent_budget.conservative_required_lamports = match program_already_deployed {
            Some(true) => setup,
            Some(false) => fresh,
            None => None,
        };
        rent_budget.surplus_lamports = rent_budget
            .payer_balance_lamports
            .zip(rent_budget.conservative_required_lamports)
            .map(|(balance, required)| i128::from(balance) - i128::from(required));
        let _ = sbf;
    }
    let funded = rent_budget
        .surplus_lamports
        .is_some_and(|surplus| surplus >= 0);
    gate(
        &mut gates,
        "payer_covers_conservative_rent_and_fees",
        funded,
        format!(
            "balance={:?}, required={:?}, surplus={:?}",
            rent_budget.payer_balance_lamports,
            rent_budget.conservative_required_lamports,
            rent_budget.surplus_lamports
        ),
    );

    let blockers = gates
        .iter()
        .filter(|gate| !gate.passed)
        .map(|gate| gate.name.clone())
        .collect::<Vec<_>>();
    Ok(Profile23DevnetReadiness {
        artifact: "profile23_devnet_readiness",
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        mode: "read_only",
        mutations_performed: false,
        ready: blockers.is_empty(),
        expected_genesis_hash: DEVNET_GENESIS_HASH,
        observed_genesis_hash: observed_genesis,
        rpc_origin_redacted: rpc_origin,
        program_id: declared_program.to_string(),
        payer_pubkey: payer.as_ref().map(|key| key.pubkey().to_string()),
        pool_pubkey: pool_pubkey.map(|key| key.to_string()),
        proof_account_pubkey: proof_account_pubkey.map(|key| key.to_string()),
        proof_sha256: proof_sha,
        sbf_sha256: sbf_sha,
        release_sha256: release_sha,
        statement_sha256: statement_sha,
        nullifier_address: nullifier_address.map(|key| key.to_string()),
        program_already_deployed,
        rent_budget,
        gates,
        blockers,
        explicit_nonclaims: vec![
            "Readiness never signs, deploys, creates accounts, uploads proof bytes, or submits transactions.",
            "A devnet rehearsal is not mainnet-beta evidence.",
            "Proof upload/finalization and pool initialization are setup transactions, not the one-transaction verification/state-transition claim.",
        ],
    })
}

pub fn readiness(workspace_root: &Path, arguments: &[String]) -> Result<Profile23DevnetReadiness> {
    let config = parse_args(arguments, CommandMode::Readiness)?;
    inspect(workspace_root, &config)
}

fn signed_transaction(
    payer: &Keypair,
    signers: &[&Keypair],
    instructions: &[Instruction],
    blockhash: Hash,
) -> Transaction {
    let mut all_signers = Vec::<&Keypair>::with_capacity(signers.len() + 1);
    all_signers.push(payer);
    for signer in signers {
        if signer.pubkey() != payer.pubkey() {
            all_signers.push(*signer);
        }
    }
    Transaction::new_signed_with_payer(instructions, Some(&payer.pubkey()), &all_signers, blockhash)
}

fn proof_instruction(
    payer: Pubkey,
    proof_account: Pubkey,
    instruction: &AspisInstruction,
) -> Result<Instruction> {
    Ok(Instruction {
        program_id: aspis_verifier::id(),
        accounts: vec![
            AccountMeta::new(
                proof_account,
                matches!(instruction, AspisInstruction::InitProof { .. }),
            ),
            AccountMeta::new_readonly(payer, true),
        ],
        data: to_vec(instruction)?,
    })
}

fn create_account_transaction(
    rpc: &Rpc,
    payer: &Keypair,
    account: &Keypair,
    lamports: u64,
    space: usize,
    label: &str,
) -> Result<TransactionEvidence> {
    let instruction = system_instruction::create_account(
        &payer.pubkey(),
        &account.pubkey(),
        lamports,
        space as u64,
        &aspis_verifier::id(),
    );
    let transaction =
        signed_transaction(payer, &[account], &[instruction], rpc.latest_blockhash()?);
    rpc.submit_transaction(&transaction, label)
}

fn extract_deploy_signature(stdout: &[u8]) -> Result<Signature> {
    if let Ok(value) = serde_json::from_slice::<Value>(stdout) {
        for key in ["signature", "transactionSignature"] {
            if let Some(value) = value[key].as_str() {
                return Signature::from_str(value).context("invalid deployment signature");
            }
        }
    }
    let text = std::str::from_utf8(stdout).context("deployment output was not UTF-8")?;
    for line in text.lines() {
        if let Some(value) = line.strip_prefix("Signature: ") {
            return Signature::from_str(value.trim()).context("invalid deployment signature");
        }
    }
    bail!("Solana CLI deployment output omitted a parseable signature")
}

fn deploy_if_needed(
    rpc: &Rpc,
    config: &DevnetConfig,
    payer: &Keypair,
    sbf: &[u8],
) -> Result<Option<TransactionEvidence>> {
    if deployed_program_exact(
        rpc,
        &aspis_verifier::id(),
        sbf,
        config.program_max_len,
        &payer.pubkey(),
    )? {
        return Ok(None);
    }
    ensure!(
        rpc.account(&aspis_verifier::id())?.is_none(),
        "program address exists but does not match the exact release"
    );
    let output = Command::new(&config.solana_cli)
        .arg("--url")
        .arg(&config.rpc_url)
        .arg("--keypair")
        .arg(&config.payer_keypair)
        .arg("--output")
        .arg("json")
        .arg("program")
        .arg("deploy")
        .arg(&config.sbf)
        .arg("--program-id")
        .arg(&config.program_keypair)
        .arg("--upgrade-authority")
        .arg(&config.payer_keypair)
        .arg("--max-len")
        .arg(config.program_max_len.to_string())
        .output()
        .context("run explicit Solana CLI deploy")?;
    ensure!(
        output.status.success(),
        "Solana CLI deploy failed with status {}",
        output.status
    );
    let signature = extract_deploy_signature(&output.stdout)?;
    let slot = rpc.wait_finalized(&signature)?;
    ensure!(
        deployed_program_exact(
            rpc,
            &aspis_verifier::id(),
            sbf,
            config.program_max_len,
            &payer.pubkey(),
        )?,
        "finalized deployed program did not match release bytes/max-len/authority"
    );
    let (wire_sha256, message_sha256) = rpc.transaction_wire_and_message_hash(&signature)?;
    Ok(Some(TransactionEvidence {
        label: "deploy_exact_release_sbf".to_owned(),
        signature: signature.to_string(),
        finalized_slot: slot,
        // The CLI owns construction, so both hashes are refetched from the
        // finalized transaction rather than inferred from its stdout.
        message_sha256,
        serialized_transaction_sha256: wire_sha256,
        compute_units_consumed: rpc.transaction_cu(&signature)?,
        identical_wire_retries: 0,
    }))
}

fn expected_proof_account(proof: &[u8], authority: Pubkey, finalized: bool) -> Vec<u8> {
    let mut expected = vec![0u8; PROOF_ACCOUNT_HEADER_LEN + proof.len()];
    expected[..4].copy_from_slice(PROOF_MAGIC);
    expected[4..8].copy_from_slice(&(proof.len() as u32).to_le_bytes());
    if !finalized {
        expected[PROOF_AUTHORITY_OFFSET..PROOF_AUTHORITY_OFFSET + 32]
            .copy_from_slice(authority.as_ref());
    }
    expected[PROOF_ACCOUNT_HEADER_LEN..].copy_from_slice(proof);
    expected
}

fn expected_nullifier_marker(pool: Pubkey, nullifier: [u8; 32]) -> Vec<u8> {
    let mut expected = vec![0u8; ATOMIC_NULLIFIER_MARKER_LEN];
    expected[..4].copy_from_slice(&ATOMIC_NULLIFIER_MAGIC);
    expected[4] = ATOMIC_NULLIFIER_VERSION;
    expected[8..40].copy_from_slice(pool.as_ref());
    expected[40..72].copy_from_slice(&nullifier);
    expected
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
            .open(path)
            .with_context(|| format!("reserve evidence path {}", path.display()))?;
        let placeholder = json!({
            "artifact": "profile23_devnet_finalized_rehearsal",
            "status": "in_progress_no_claim",
            "reserved_at_utc": chrono::Utc::now().to_rfc3339(),
            "warning": "If this file remains in_progress, execution did not reach the finalized evidence commit. Inspect chain state by recorded signer history before retrying."
        });
        let mut bytes = serde_json::to_vec_pretty(&placeholder)?;
        bytes.push(b'\n');
        file.write_all(&bytes)?;
        file.sync_all()?;
        Ok(Self {
            file,
            path: path.to_path_buf(),
        })
    }

    fn commit(self, value: &impl Serialize) -> Result<u32> {
        let mut bytes = serde_json::to_vec_pretty(value)?;
        bytes.push(b'\n');
        self.file.sync_all()?;
        let parent = self.path.parent().context("evidence path omitted parent")?;
        let name = self
            .path
            .file_name()
            .and_then(|name| name.to_str())
            .context("evidence filename is not UTF-8")?;
        let temporary_path = parent.join(format!(".{name}.complete-{}", std::process::id()));
        let mut completed = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&temporary_path)
            .with_context(|| format!("create completed evidence {}", temporary_path.display()))?;
        completed.write_all(&bytes)?;
        completed.sync_all()?;
        let mut permissions = completed.metadata()?.permissions();
        permissions.set_mode(0o444);
        fs::set_permissions(&temporary_path, permissions)?;
        fs::rename(&temporary_path, &self.path)?;
        fs::File::open(parent)?.sync_all()?;
        Ok(0o444)
    }
}

#[allow(clippy::too_many_lines)]
pub fn execute(workspace_root: &Path, arguments: &[String]) -> Result<Profile23DevnetEvidence> {
    let config = parse_args(arguments, CommandMode::Execute)?;
    ensure!(
        config.execute_interlock,
        "missing --execute-devnet interlock"
    );
    ensure!(
        config.acknowledgement.as_deref() == Some(EXECUTE_ACK),
        "missing exact devnet mutation acknowledgement"
    );
    let readiness = inspect(workspace_root, &config)?;
    ensure!(
        readiness.ready,
        "devnet readiness blocked: {}",
        readiness.blockers.join(", ")
    );

    let rpc = Rpc::new(config.rpc_url.clone())?;
    ensure!(
        rpc.genesis_hash()? == DEVNET_GENESIS_HASH,
        "devnet genesis changed after readiness"
    );
    let payer = secure_keypair(&config.payer_keypair)?;
    let program = secure_keypair(&config.program_keypair)?;
    let pool = secure_keypair(&config.pool_keypair)?;
    let proof_account = secure_keypair(&config.proof_account_keypair)?;
    ensure!(program.pubkey() == aspis_verifier::id());
    let signer_keys = [
        payer.pubkey(),
        program.pubkey(),
        pool.pubkey(),
        proof_account.pubkey(),
    ];
    ensure!((0..signer_keys.len()).all(|left| {
        (left + 1..signer_keys.len()).all(|right| signer_keys[left] != signer_keys[right])
    }));
    let release_bytes = exact_regular_file(&config.release)?;
    let release: Value = serde_json::from_slice(&release_bytes)?;
    ensure!(release["gates"]
        .as_array()
        .is_some_and(|gates| gates.len() == 30
            && gates
                .iter()
                .all(|gate| gate["passed"].as_bool() == Some(true))));
    release_artifacts_exact(&release, workspace_root)?;
    let sbf = exact_regular_file(&config.sbf)?;
    let proof = exact_regular_file(&config.proof)?;
    let statement_bytes = exact_regular_file(&config.statement)?;
    let statement: StatementSidecar = serde_json::from_slice(&statement_bytes)?;
    let public = statement.public()?;
    ensure!(statement.pool()? == pool.pubkey());

    // Recheck all fresh-account predicates immediately before the first write.
    ensure!(
        rpc.account(&pool.pubkey())?.is_none(),
        "pool account ceased to be fresh"
    );
    ensure!(
        rpc.account(&proof_account.pubkey())?.is_none(),
        "proof account ceased to be fresh"
    );
    let (nullifier_address, _) = atomic_nullifier_address(&aspis_verifier::id(), &public.nullifier);
    let nullifier_before_snapshot = rpc.account(&nullifier_address)?;
    ensure!(nullifier_compatible(
        nullifier_before_snapshot.as_ref(),
        &aspis_verifier::id()
    ));

    // Reserve the evidence filename before the first network mutation. If the
    // process fails later, a synced `in_progress_no_claim` record remains and
    // prevents a blind rerun from reusing the same setup identities.
    let evidence_reservation = EvidenceReservation::reserve(&config.evidence)?;

    let deployment = deploy_if_needed(&rpc, &config, &payer, &sbf)?;
    let mut setup_transactions = Vec::new();

    let pool_rent = rpc.rent(ATOMIC_POOL_STATE_LEN)?;
    setup_transactions.push(create_account_transaction(
        &rpc,
        &payer,
        &pool,
        pool_rent,
        ATOMIC_POOL_STATE_LEN,
        "create_pool_account",
    )?);
    let initialize_pool = Instruction {
        program_id: aspis_verifier::id(),
        accounts: vec![AccountMeta::new(pool.pubkey(), true)],
        data: to_vec(&AspisInstruction::InitializeAtomicPool {
            sequence: statement.sequence,
            anchor: public.current_anchor,
        })?,
    };
    let initialize_pool_tx = signed_transaction(
        &payer,
        &[&pool],
        &[initialize_pool],
        rpc.latest_blockhash()?,
    );
    setup_transactions.push(rpc.submit_transaction(&initialize_pool_tx, "tag63_initialize_pool")?);
    let pool_before_snapshot = rpc
        .account(&pool.pubkey())?
        .context("initialized pool missing")?;
    ensure!(pool_before_snapshot.owner == aspis_verifier::id());
    let pool_before_state = AtomicPoolStateV1::decode(&pool_before_snapshot.data)
        .map_err(|error| anyhow!("decode initialized pool: {error:?}"))?;
    ensure!(
        pool_before_state.sequence == statement.sequence
            && pool_before_state.anchor == public.current_anchor
    );

    let proof_rent = rpc.rent(PROOF_ACCOUNT_HEADER_LEN + proof.len())?;
    setup_transactions.push(create_account_transaction(
        &rpc,
        &payer,
        &proof_account,
        proof_rent,
        PROOF_ACCOUNT_HEADER_LEN + proof.len(),
        "create_proof_account",
    )?);
    let init = proof_instruction(
        payer.pubkey(),
        proof_account.pubkey(),
        &AspisInstruction::InitProof {
            total_len: proof.len() as u32,
        },
    )?;
    let init_tx = signed_transaction(&payer, &[&proof_account], &[init], rpc.latest_blockhash()?);
    setup_transactions.push(rpc.submit_transaction(&init_tx, "init_proof_account")?);
    for (index, chunk) in proof.chunks(UPLOAD_CHUNK_BYTES).enumerate() {
        let upload = proof_instruction(
            payer.pubkey(),
            proof_account.pubkey(),
            &AspisInstruction::UploadChunk {
                offset: (index * UPLOAD_CHUNK_BYTES) as u32,
                chunk: chunk.to_vec(),
            },
        )?;
        let upload_tx = signed_transaction(&payer, &[], &[upload], rpc.latest_blockhash()?);
        setup_transactions
            .push(rpc.submit_transaction(&upload_tx, &format!("upload_proof_chunk_{index}"))?);
    }
    let uploaded = rpc
        .account(&proof_account.pubkey())?
        .context("uploaded proof account missing")?;
    ensure!(
        uploaded.data == expected_proof_account(&proof, payer.pubkey(), false),
        "full pre-finalization proof account bytes differ"
    );
    let finalize = proof_instruction(
        payer.pubkey(),
        proof_account.pubkey(),
        &AspisInstruction::FinalizeProof,
    )?;
    let finalize_tx = signed_transaction(&payer, &[], &[finalize], rpc.latest_blockhash()?);
    setup_transactions.push(rpc.submit_transaction(&finalize_tx, "tag62_finalize_proof")?);
    let finalized_proof = rpc
        .account(&proof_account.pubkey())?
        .context("finalized proof account missing")?;
    ensure!(
        finalized_proof.data == expected_proof_account(&proof, payer.pubkey(), true),
        "finalized proof bytes/header drift"
    );

    let post_finalize_before = finalized_proof.clone();
    let forbidden_upload = proof_instruction(
        payer.pubkey(),
        proof_account.pubkey(),
        &AspisInstruction::UploadChunk {
            offset: 0,
            chunk: vec![proof[0] ^ 1],
        },
    )?;
    let forbidden_upload_tx =
        signed_transaction(&payer, &[], &[forbidden_upload], rpc.latest_blockhash()?);
    let post_finalize_upload_rejected = rpc
        .simulate_exact(&bincode::serialize(&forbidden_upload_tx)?)?
        .error
        .is_some();
    ensure!(
        post_finalize_upload_rejected,
        "sealed proof accepted an upload simulation"
    );
    let second_finalize = proof_instruction(
        payer.pubkey(),
        proof_account.pubkey(),
        &AspisInstruction::FinalizeProof,
    )?;
    let second_finalize_tx =
        signed_transaction(&payer, &[], &[second_finalize], rpc.latest_blockhash()?);
    let post_finalize_second_finalize_rejected = rpc
        .simulate_exact(&bincode::serialize(&second_finalize_tx)?)?
        .error
        .is_some();
    ensure!(
        post_finalize_second_finalize_rejected,
        "sealed proof accepted second finalization"
    );
    ensure!(rpc.account(&proof_account.pubkey())?.as_ref() == Some(&post_finalize_before));

    let tag60 = Instruction {
        program_id: aspis_verifier::id(),
        accounts: vec![
            AccountMeta::new_readonly(proof_account.pubkey(), false),
            AccountMeta::new(pool.pubkey(), false),
            AccountMeta::new(nullifier_address, false),
            AccountMeta::new(payer.pubkey(), true),
            AccountMeta::new_readonly(system_program::id(), false),
        ],
        data: to_vec(&AspisInstruction::ApplyAtomicStateOnlyProfile23V3 {
            current_anchor: public.current_anchor,
            nullifier: public.nullifier,
            output_commitment: public.output_commitment,
            output_anchor: public.output_anchor,
            asset_id: public.asset_id,
            fee: public.fee,
        })?,
    };
    let final_tx = signed_transaction(
        &payer,
        &[],
        &[
            ComputeBudgetInstruction::set_compute_unit_limit(CU_LIMIT),
            ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
            tag60.clone(),
        ],
        rpc.latest_blockhash()?,
    );
    let final_wire = bincode::serialize(&final_tx)?;
    let final_message_hash = sha256(&bincode::serialize(&final_tx.message)?);
    let final_wire_hash = sha256(&final_wire);
    let simulation = rpc.simulate_exact(&final_wire)?;
    ensure!(
        simulation.error.is_none(),
        "exact signed tag60 simulation rejected: {:?}",
        simulation.error
    );
    let simulation_cu = simulation.units.context("tag60 simulation omitted CU")?;
    ensure!(
        simulation_cu < u64::from(CU_LIMIT),
        "tag60 simulation exceeded CU limit"
    );
    ensure!(rpc.account(&pool.pubkey())?.as_ref() == Some(&pool_before_snapshot));
    ensure!(rpc.account(&nullifier_address)? == nullifier_before_snapshot);

    // Submit the exact byte string that was simulated. On an ambiguous RPC
    // response only that same byte string may be retried once.
    let final_transaction = rpc.submit_wire(
        &final_wire,
        final_tx.signatures[0],
        true,
        "tag60_atomic_verify_and_apply",
        final_message_hash.clone(),
    )?;
    ensure!(final_transaction.serialized_transaction_sha256 == final_wire_hash);
    let landed_cu = final_transaction
        .compute_units_consumed
        .context("finalized tag60 transaction omitted computeUnitsConsumed")?;
    ensure!(
        landed_cu < u64::from(CU_LIMIT),
        "finalized tag60 exceeded CU limit"
    );
    let pool_after_snapshot = rpc
        .account(&pool.pubkey())?
        .context("pool missing after tag60")?;
    let pool_after_state = AtomicPoolStateV1::decode(&pool_after_snapshot.data)
        .map_err(|error| anyhow!("decode poststate pool: {error:?}"))?;
    ensure!(
        pool_after_state.sequence
            == statement
                .sequence
                .checked_add(1)
                .context("sequence overflow")?
    );
    ensure!(pool_after_state.anchor == public.output_anchor);
    let nullifier_after_snapshot = rpc
        .account(&nullifier_address)?
        .context("nullifier missing after tag60")?;
    ensure!(nullifier_after_snapshot.owner == aspis_verifier::id());
    ensure!(
        nullifier_after_snapshot.data == expected_nullifier_marker(pool.pubkey(), public.nullifier)
    );
    ensure!(rpc.account(&proof_account.pubkey())?.as_ref() == Some(&finalized_proof));

    let duplicate_tx = signed_transaction(
        &payer,
        &[],
        &[
            ComputeBudgetInstruction::set_compute_unit_limit(CU_LIMIT),
            ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
            tag60,
        ],
        rpc.latest_blockhash()?,
    );
    let duplicate_simulation_rejected = rpc
        .simulate_exact(&bincode::serialize(&duplicate_tx)?)?
        .error
        .is_some();
    ensure!(
        duplicate_simulation_rejected,
        "duplicate tag60 simulation unexpectedly accepted"
    );
    ensure!(rpc.account(&pool.pubkey())?.as_ref() == Some(&pool_after_snapshot));
    ensure!(rpc.account(&nullifier_address)?.as_ref() == Some(&nullifier_after_snapshot));

    let mut evidence = Profile23DevnetEvidence {
        artifact: "profile23_devnet_finalized_rehearsal",
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        network: "devnet",
        genesis_hash: DEVNET_GENESIS_HASH.to_owned(),
        program_id: aspis_verifier::id().to_string(),
        release_certificate_path: config.release.display().to_string(),
        release_certificate_sha256: sha256(&release_bytes),
        release_gate_count: 30,
        sbf_path: config.sbf.display().to_string(),
        sbf_bytes: sbf.len(),
        sbf_sha256: sha256(&sbf),
        proof_path: config.proof.display().to_string(),
        proof_bytes: proof.len(),
        proof_sha256: sha256(&proof),
        statement_path: config.statement.display().to_string(),
        statement_sha256: sha256(&statement_bytes),
        program_max_len: config.program_max_len,
        deployment,
        setup_transactions,
        final_transaction,
        final_transaction_simulation_cu: simulation_cu,
        final_transaction_wire_sha256: final_wire_hash,
        final_transaction_message_sha256: final_message_hash,
        final_transaction_submitted_identically_to_simulation: true,
        proof_account: finalized_proof.evidence(proof_account.pubkey()),
        proof_account_finalized: true,
        post_finalize_upload_rejected,
        post_finalize_second_finalize_rejected,
        pool_before: pool_before_snapshot.evidence(pool.pubkey()),
        pool_after: pool_after_snapshot.evidence(pool.pubkey()),
        sequence_before: pool_before_state.sequence,
        sequence_after: pool_after_state.sequence,
        nullifier_before: nullifier_before_snapshot.map(|account| account.evidence(nullifier_address)),
        nullifier_after: nullifier_after_snapshot.evidence(nullifier_address),
        duplicate_simulation_rejected,
        evidence_path: config.evidence.display().to_string(),
        evidence_file_mode: 0,
        explicit_scope: vec![
            "Devnet rehearsal only; this is not mainnet-beta evidence.",
            "The single tag60 transaction consumes a previously finalized proof account and atomically mutates pool/nullifier state.",
            "Deployment, pool initialization, proof-account creation, uploads, and finalization are setup transactions.",
            "The deployment is left upgradeable under the explicit payer for rehearsal; the mainnet executor must independently enforce its selected authority policy.",
        ],
    };
    evidence.evidence_file_mode = 0o444;
    evidence_reservation.commit(&evidence)?;
    Ok(evidence)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn complete_args() -> Vec<String> {
        vec![
            "--rpc-url",
            "https://api.devnet.solana.com",
            "--payer-keypair",
            "/tmp/payer.json",
            "--program-keypair",
            "/tmp/program.json",
            "--pool-keypair",
            "/tmp/pool.json",
            "--proof-account-keypair",
            "/tmp/proof-account.json",
            "--release",
            "/tmp/release.json",
            "--sbf",
            "/tmp/program.so",
            "--proof",
            "/tmp/proof.bin",
            "--statement",
            "/tmp/proof.statement.json",
            "--solana-cli",
            "/usr/local/bin/solana",
            "--evidence",
            "/tmp/evidence.json",
            "--program-max-len",
            "7000000",
            "--fee-reserve-lamports",
            "100000000",
        ]
        .into_iter()
        .map(str::to_owned)
        .collect()
    }

    #[test]
    fn readiness_refuses_execution_interlocks() {
        let mut args = complete_args();
        args.push("--execute-devnet".to_owned());
        assert!(parse_args(&args, CommandMode::Readiness).is_err());
    }

    #[test]
    fn executor_requires_both_interlocks() {
        let args = complete_args();
        let parsed = parse_args(&args, CommandMode::Execute).unwrap();
        assert!(!parsed.execute_interlock);
        assert_ne!(parsed.acknowledgement.as_deref(), Some(EXECUTE_ACK));
    }

    #[test]
    fn explicit_paths_are_mandatory() {
        let mut args = complete_args();
        let index = args.iter().position(|arg| arg == "--proof").unwrap();
        args[index + 1] = "relative.bin".to_owned();
        assert!(parse_args(&args, CommandMode::Readiness).is_err());
    }

    #[test]
    fn nullifier_accepts_only_absent_or_supported_prefunding_shapes() {
        let program_id = Pubkey::new_unique();
        assert!(nullifier_compatible(None, &program_id));
        assert!(nullifier_compatible(
            Some(&RpcAccount {
                lamports: 1,
                owner: system_program::id(),
                executable: false,
                data: Vec::new(),
            }),
            &program_id
        ));
        assert!(!nullifier_compatible(
            Some(&RpcAccount {
                lamports: 1,
                owner: Pubkey::new_unique(),
                executable: false,
                data: Vec::new(),
            }),
            &program_id
        ));
    }

    #[test]
    fn evidence_reservation_commits_read_only_json() {
        let path = std::env::temp_dir().join(format!(
            "aspis-profile23-devnet-evidence-test-{}-{}.json",
            std::process::id(),
            chrono::Utc::now().timestamp_nanos_opt().unwrap()
        ));
        let reservation = EvidenceReservation::reserve(&path).unwrap();
        let in_progress: Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        assert_eq!(in_progress["status"], "in_progress_no_claim");
        reservation
            .commit(&json!({"status":"finalized_evidence"}))
            .unwrap();
        let completed: Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        assert_eq!(completed["status"], "finalized_evidence");
        assert_eq!(
            fs::metadata(&path).unwrap().permissions().mode() & 0o777,
            0o444
        );
        let mut permissions = fs::metadata(&path).unwrap().permissions();
        permissions.set_mode(0o600);
        fs::set_permissions(&path, permissions).unwrap();
        fs::remove_file(path).unwrap();
    }
}
