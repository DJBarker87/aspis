//! Post-Tag67 close of one finalized V5 proof account on mainnet.
//!
//! This command performs exactly one tag-64 proof-account close. It does not
//! close ProgramData, upgrade the verifier, or infer any identity from account
//! history. The refund destination is the explicitly pinned dedicated payer.
//! The exact signed transaction is simulated, submitted unchanged, fetched
//! again after finality, and reconciled against its finalized balances.

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
    message::VersionedMessage,
    pubkey::Pubkey,
    signature::{read_keypair_file, Keypair, Signature, Signer},
    system_program,
    transaction::{Transaction, VersionedTransaction},
};

use aspis_verifier::PROOF_ACCOUNT_HEADER_LEN;

const MAINNET_GENESIS_HASH: &str = "5eykt4UsFv8P8NJdTREpY1vzqKqZKvdpKuc147dw2N9d";
const FROZEN_V5_SBF_BYTES: usize = 1_258_496;
const FROZEN_V5_SBF_SHA256: &str =
    "4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40";
const FROZEN_V5_PROGRAM_MAX_LEN: usize = 1_300_000;
const MAX_TAG64_FEE_LAMPORTS: u64 = 1_000_000;
const EXECUTE_ACK: &str =
    "I_ACKNOWLEDGE_V5_MAINNET_TAG64_CLOSE_IRREVERSIBLY_DESTROYS_THE_PROOF_ACCOUNT_AND_REFUNDS_ITS_RENT_TO_THE_PINNED_DEDICATED_PAYER";
const TAG_CLOSE_FINALIZED_PROOF: u8 = 64;
const PROOF_MAGIC: &[u8; 4] = b"ASPU";
const PROOF_AUTHORITY_OFFSET: usize = 8;
const PROGRAMDATA_METADATA_BYTES: usize = 45;
const READ_RETRIES: u8 = 12;
const FINALITY_TIMEOUT: Duration = Duration::from_secs(180);
const POLL_INTERVAL: Duration = Duration::from_secs(2);
const ARTIFACT: &str = "aspis_v5_mainnet_tag64_proof_close";
const IN_PROGRESS_WARNING: &str = "Execution did not reach the immutable finalized evidence commit. Inspect the recorded expected signature and signed-wire hash on mainnet before considering any retry.";

#[derive(Debug)]
struct Config {
    rpc_url: String,
    payer_keypair: PathBuf,
    proof_account_keypair: PathBuf,
    upgrade_authority_keypair: PathBuf,
    expected_payer: Pubkey,
    expected_proof_account: Pubkey,
    expected_proof_sha256: String,
    expected_tag67_signature: Signature,
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

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
struct Tag67RunEvidence {
    signature: String,
    finalized_slot: u64,
    signed_wire_sha256: String,
    tag67_instruction_index: usize,
    tag67_instruction_data_sha256: String,
    proof_account: String,
    proof_role_readonly: bool,
    proof_role_non_signer: bool,
    tag67_payer: String,
    canonical_program_success_log_exact: bool,
    finalized_meta_succeeded: bool,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
struct Tag67InstructionEvidence {
    tag67_instruction_index: usize,
    tag67_instruction_data_sha256: String,
    proof_account: String,
    proof_role_readonly: bool,
    proof_role_non_signer: bool,
    tag67_payer: String,
}

#[derive(Clone, Debug, Serialize)]
struct RefundEvidence {
    fee_lamports: u64,
    payer_account_index: usize,
    proof_account_index: usize,
    payer_pre_lamports: u64,
    payer_post_lamports: u64,
    proof_pre_lamports: u64,
    proof_post_lamports: u64,
    refund_lamports: u64,
    payer_delta_plus_fee_lamports: i128,
    exact_refund_equation_reconciled: bool,
    every_other_message_account_balance_unchanged: bool,
}

#[derive(Clone, Debug, Serialize)]
pub struct V5MainnetProofCloseEvidence {
    pub signature: String,
    pub finalized_slot: u64,
    pub refund_lamports: u64,
    pub evidence_path: String,
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

    fn fee_for_message(&self, transaction: &Transaction) -> Result<u64> {
        let message = bincode::serialize(&transaction.message)?;
        self.read(
            "getFeeForMessage",
            json!([BASE64.encode(message), {"commitment":"finalized"}]),
        )?["value"]
            .as_u64()
            .context("getFeeForMessage returned no fee")
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

    fn finalized_tag67_run(
        &self,
        signature: &Signature,
        expected_proof: Pubkey,
        expected_payer: Pubkey,
    ) -> Result<Tag67RunEvidence> {
        let status = self
            .signature_status(signature)?
            .context("expected tag67 signature is absent from mainnet history")?;
        ensure!(status.1, "expected tag67 transaction is not finalized");
        ensure!(
            status.2.is_none(),
            "expected tag67 transaction status reports failure"
        );
        let finalized = self.finalized_transaction(signature, status.0)?;
        let instruction = validate_finalized_tag67_wire(
            &finalized.wire,
            signature,
            expected_proof,
            expected_payer,
        )?;
        let success_log = format!("Program {} success", aspis_verifier::id());
        let canonical_program_success_log_exact = finalized
            .logs
            .iter()
            .filter(|line| line.as_str() == success_log.as_str())
            .count()
            == 1;
        ensure!(
            canonical_program_success_log_exact,
            "finalized tag67 transaction omitted the canonical verifier success log or logged it more than once"
        );
        Ok(Tag67RunEvidence {
            signature: signature.to_string(),
            finalized_slot: finalized.slot,
            signed_wire_sha256: sha256(&finalized.wire),
            tag67_instruction_index: instruction.tag67_instruction_index,
            tag67_instruction_data_sha256: instruction.tag67_instruction_data_sha256,
            proof_account: instruction.proof_account,
            proof_role_readonly: instruction.proof_role_readonly,
            proof_role_non_signer: instruction.proof_role_non_signer,
            tag67_payer: instruction.tag67_payer,
            canonical_program_success_log_exact,
            finalized_meta_succeeded: true,
        })
    }
}

fn parse_args(arguments: &[String]) -> Result<Config> {
    let mut values = BTreeMap::<String, String>::new();
    let mut execute_interlock = false;
    let mut index = 0usize;
    while index < arguments.len() {
        let key = &arguments[index];
        if key == "--execute-v5-mainnet-tag64-close" {
            ensure!(
                !execute_interlock,
                "duplicate --execute-v5-mainnet-tag64-close"
            );
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
        "--upgrade-authority-keypair",
        "--expected-payer",
        "--expected-proof-account",
        "--expected-proof-sha256",
        "--expected-tag67-signature",
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
    ensure!(
        program_max_len == FROZEN_V5_PROGRAM_MAX_LEN,
        "--program-max-len differs from the frozen V5 deployment allocation"
    );
    let expected_payer = required("--expected-payer")?
        .parse::<Pubkey>()
        .context("--expected-payer is not a Solana pubkey")?;
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
    let expected_tag67_signature = required("--expected-tag67-signature")?
        .parse::<Signature>()
        .context("--expected-tag67-signature is not a Solana transaction signature")?;
    Ok(Config {
        rpc_url: required("--rpc-url")?,
        payer_keypair: absolute("--payer-keypair")?,
        proof_account_keypair: absolute("--proof-account-keypair")?,
        upgrade_authority_keypair: absolute("--upgrade-authority-keypair")?,
        expected_payer,
        expected_proof_account,
        expected_proof_sha256,
        expected_tag67_signature,
        sbf: absolute("--sbf")?,
        program_max_len,
        evidence: absolute("--evidence")?,
        execute_interlock,
        acknowledgement: values.get("--acknowledgement").cloned(),
    })
}

fn rpc_origin(endpoint: &str) -> Result<String> {
    let url = reqwest::Url::parse(endpoint).context("invalid RPC URL")?;
    ensure!(url.scheme() == "https", "mainnet RPC must use HTTPS");
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

fn file_name(path: &Path) -> Result<String> {
    path.file_name()
        .and_then(|name| name.to_str())
        .map(ToOwned::to_owned)
        .with_context(|| format!("path has no UTF-8 filename: {}", path.display()))
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

fn validate_frozen_sbf(sbf: &[u8]) -> Result<()> {
    ensure!(
        sbf.len() == FROZEN_V5_SBF_BYTES,
        "SBF size differs from the frozen V5 release"
    );
    ensure!(
        sha256(sbf) == FROZEN_V5_SBF_SHA256,
        "SBF SHA-256 differs from the frozen V5 release"
    );
    Ok(())
}

fn validate_key_roles(
    payer: Pubkey,
    proof: Pubkey,
    upgrade_authority: Pubkey,
    expected_payer: Pubkey,
    expected_proof: Pubkey,
) -> Result<()> {
    ensure!(
        payer == expected_payer,
        "payer keypair does not match --expected-payer; refusing refund"
    );
    ensure!(
        proof == expected_proof,
        "proof keypair does not match --expected-proof-account; refusing destructive close"
    );
    ensure!(
        payer != proof && payer != upgrade_authority && proof != upgrade_authority,
        "payer, proof, and upgrade-authority keypairs must be pairwise distinct"
    );
    ensure!(
        payer != aspis_verifier::id()
            && proof != aspis_verifier::id()
            && upgrade_authority != aspis_verifier::id(),
        "no signer key may equal the canonical verifier program id"
    );
    Ok(())
}

fn validate_finalized_tag67_wire(
    wire: &[u8],
    expected_signature: &Signature,
    expected_proof: Pubkey,
    expected_payer: Pubkey,
) -> Result<Tag67InstructionEvidence> {
    let transaction: VersionedTransaction =
        bincode::deserialize(wire).context("decode finalized tag67 transaction wire")?;
    transaction
        .verify_and_hash_message()
        .map_err(|error| anyhow!("verify finalized tag67 transaction signatures: {error}"))?;
    ensure!(
        transaction.signatures.len() == 1
            && transaction.signatures.first() == Some(expected_signature),
        "finalized tag67 wire does not carry the exact expected transaction signature"
    );
    let VersionedMessage::Legacy(message) = &transaction.message else {
        bail!("finalized tag67 transaction must use the canonical legacy transaction message")
    };
    ensure!(
        message.header.num_required_signatures == 1,
        "finalized tag67 transaction must require exactly its dedicated payer signature"
    );

    let mut tag67 = None;
    for (instruction_index, instruction) in message.instructions.iter().enumerate() {
        let program_index = usize::from(instruction.program_id_index);
        let program = message
            .account_keys
            .get(program_index)
            .context("tag67 instruction program index is out of range")?;
        if *program == aspis_verifier::id()
            && instruction.data.first()
                == Some(&aspis_verifier::v5_full_transaction::V5_FULL_CU_TRANSACTION_TAG)
        {
            ensure!(
                tag67.is_none(),
                "finalized transaction contains more than one canonical verifier tag67 instruction"
            );
            tag67 = Some((instruction_index, instruction));
        }
    }
    let (instruction_index, instruction) =
        tag67.context("finalized transaction contains no canonical verifier tag67 instruction")?;
    ensure!(
        instruction.data.len()
            == aspis_verifier::v5_full_transaction::V5_FULL_CU_TRANSACTION_WIRE_BYTES
            && instruction.data.len() == 169,
        "finalized tag67 data is not the exact 169-byte public wire"
    );
    aspis_verifier::v5_full_transaction::parse_v5_full_cu_public_inputs(&instruction.data)
        .map_err(|error| anyhow!("parse finalized tag67 public wire: {error:?}"))?;
    ensure!(
        instruction.accounts.len() == 5,
        "finalized tag67 account count differs from the canonical five-account layout"
    );

    let account_index = |position: usize| -> Result<usize> {
        instruction
            .accounts
            .get(position)
            .copied()
            .map(usize::from)
            .context("finalized tag67 account index is absent")
    };
    let account_key = |index: usize| -> Result<Pubkey> {
        message
            .account_keys
            .get(index)
            .copied()
            .context("finalized tag67 account index is out of range")
    };
    let proof_index = account_index(0)?;
    let pool_index = account_index(1)?;
    let nullifier_index = account_index(2)?;
    let payer_index = account_index(3)?;
    let system_index = account_index(4)?;
    let role_indices = [
        proof_index,
        pool_index,
        nullifier_index,
        payer_index,
        system_index,
    ];
    for (position, index) in role_indices.iter().enumerate() {
        ensure!(
            !role_indices[..position].contains(index),
            "finalized tag67 transaction aliases two account roles"
        );
    }

    let proof = account_key(proof_index)?;
    let pool = account_key(pool_index)?;
    let nullifier = account_key(nullifier_index)?;
    let payer = account_key(payer_index)?;
    let system = account_key(system_index)?;
    ensure!(
        proof == expected_proof,
        "finalized tag67 transaction used a different proof account"
    );
    ensure!(
        payer == expected_payer,
        "finalized tag67 transaction used a different dedicated payer"
    );
    ensure!(
        system == system_program::id(),
        "finalized tag67 system-program account is not canonical"
    );
    ensure!(
        !message.is_signer(proof_index) && !message.is_maybe_writable(proof_index, None),
        "finalized tag67 proof role is not readonly and non-signer"
    );
    ensure!(
        !message.is_signer(pool_index) && message.is_maybe_writable(pool_index, None),
        "finalized tag67 pool role is not writable and non-signer"
    );
    ensure!(
        !message.is_signer(nullifier_index) && message.is_maybe_writable(nullifier_index, None),
        "finalized tag67 nullifier role is not writable and non-signer"
    );
    ensure!(
        message.is_signer(payer_index) && message.is_maybe_writable(payer_index, None),
        "finalized tag67 payer role is not writable signer"
    );
    ensure!(
        !message.is_signer(system_index) && !message.is_maybe_writable(system_index, None),
        "finalized tag67 system-program role is not readonly and non-signer"
    );
    let program_index = usize::from(instruction.program_id_index);
    ensure!(
        !message.is_signer(program_index) && !message.is_maybe_writable(program_index, None),
        "canonical verifier program role is not readonly and non-signer"
    );
    ensure!(
        pool != aspis_verifier::id()
            && nullifier != aspis_verifier::id()
            && payer != aspis_verifier::id()
            && proof != aspis_verifier::id()
            && system != aspis_verifier::id(),
        "finalized tag67 transaction aliases an instruction role to the verifier program"
    );

    Ok(Tag67InstructionEvidence {
        tag67_instruction_index: instruction_index,
        tag67_instruction_data_sha256: sha256(&instruction.data),
        proof_account: proof.to_string(),
        proof_role_readonly: true,
        proof_role_non_signer: true,
        tag67_payer: payer.to_string(),
    })
}

fn validate_fee_quote(quoted_fee_lamports: u64) -> Result<()> {
    ensure!(
        quoted_fee_lamports > 0,
        "tag64 fee quote must be nonzero on mainnet"
    );
    ensure!(
        quoted_fee_lamports <= MAX_TAG64_FEE_LAMPORTS,
        "tag64 fee quote exceeds the explicit 1,000,000-lamport cap"
    );
    Ok(())
}

fn account_value(account: &RpcAccount, address: Pubkey, context_slot: u64) -> Value {
    let mut raw = Vec::with_capacity(8 + 32 + 1 + account.data.len());
    raw.extend_from_slice(&account.lamports.to_le_bytes());
    raw.extend_from_slice(account.owner.as_ref());
    raw.push(u8::from(account.executable));
    raw.extend_from_slice(&account.data);
    json!({
        "address": address.to_string(),
        "context_slot": context_slot,
        "lamports": account.lamports,
        "owner": account.owner.to_string(),
        "executable": account.executable,
        "data_len": account.data.len(),
        "data_sha256": sha256(&account.data),
        "raw_account_image_sha256": sha256(&raw),
    })
}

fn program_value(snapshot: &ProgramSnapshot) -> Value {
    json!({
        "program_account": account_value(
            &snapshot.program,
            snapshot.program_id,
            snapshot.program_context_slot,
        ),
        "programdata_address": snapshot.programdata_address.to_string(),
        "programdata_account": account_value(
            &snapshot.programdata,
            snapshot.programdata_address,
            snapshot.programdata_context_slot,
        ),
        "programdata_deployment_slot": snapshot.programdata_deployment_slot,
        "upgrade_authority": snapshot.upgrade_authority.to_string(),
    })
}

fn program_continuity(before: &ProgramSnapshot, after: &ProgramSnapshot) -> Value {
    json!({
        "programdata_address_unchanged":
            after.programdata_address == before.programdata_address,
        "program_raw_account_image_unchanged": after.program == before.program,
        "programdata_raw_account_image_unchanged":
            after.programdata == before.programdata,
        "programdata_deployment_slot_unchanged":
            after.programdata_deployment_slot == before.programdata_deployment_slot,
        "upgrade_authority_unchanged":
            after.upgrade_authority == before.upgrade_authority,
    })
}

fn deployed_program_exact(
    rpc: &Rpc,
    expected_sbf: &[u8],
    expected_max_len: usize,
    expected_authority: Pubkey,
) -> Result<ProgramSnapshot> {
    validate_frozen_sbf(expected_sbf)?;
    ensure!(
        expected_sbf.len() <= expected_max_len,
        "SBF is longer than declared ProgramData maximum length"
    );
    let program_id = aspis_verifier::id();
    let program_read = rpc.account(&program_id)?;
    let program = program_read
        .account
        .context("canonical V5 verifier Program account is absent")?;
    ensure!(
        program.owner == bpf_loader_upgradeable::id() && program.executable,
        "canonical V5 verifier is not executable BPFLoaderUpgradeable"
    );
    let state: UpgradeableLoaderState =
        bincode::deserialize(&program.data).context("decode verifier Program state")?;
    let UpgradeableLoaderState::Program {
        programdata_address,
    } = state
    else {
        bail!("canonical V5 verifier address is not an upgradeable Program account")
    };
    let programdata_read = rpc.account(&programdata_address)?;
    let programdata = programdata_read
        .account
        .context("linked V5 verifier ProgramData account is absent")?;
    ensure!(
        programdata.owner == bpf_loader_upgradeable::id() && !programdata.executable,
        "linked verifier account is not non-executable ProgramData"
    );
    let state: UpgradeableLoaderState =
        bincode::deserialize(&programdata.data).context("decode verifier ProgramData state")?;
    let UpgradeableLoaderState::ProgramData {
        slot: programdata_deployment_slot,
        upgrade_authority_address,
    } = state
    else {
        bail!("linked verifier account is not ProgramData")
    };
    let upgrade_authority = upgrade_authority_address
        .context("V5 verifier ProgramData is immutable; explicit authority check failed")?;
    ensure!(
        upgrade_authority == expected_authority,
        "V5 verifier ProgramData authority does not equal the separate explicit upgrade-authority keypair"
    );
    let code = programdata
        .data
        .get(PROGRAMDATA_METADATA_BYTES..)
        .context("V5 verifier ProgramData is shorter than loader metadata")?;
    ensure!(
        code.len() == expected_max_len,
        "V5 verifier ProgramData maximum length mismatch"
    );
    ensure!(
        code.get(..expected_sbf.len()) == Some(expected_sbf),
        "deployed verifier bytes differ from the frozen V5 SBF"
    );
    ensure!(
        code[expected_sbf.len()..].iter().all(|byte| *byte == 0),
        "deployed verifier ProgramData padding is nonzero"
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

fn validate_dedicated_payer(read: AccountRead, payer: Pubkey) -> Result<Value> {
    let account = read.account.context("dedicated payer account is absent")?;
    ensure!(
        account.owner == system_program::id(),
        "dedicated payer is not System-owned"
    );
    ensure!(
        !account.executable,
        "dedicated payer must not be executable"
    );
    ensure!(
        account.data.is_empty(),
        "dedicated payer must have no account data"
    );
    ensure!(
        account.lamports > 0,
        "dedicated payer has no lamports for the close fee"
    );
    Ok(account_value(&account, payer, read.context_slot))
}

fn sealed_proof_exact(read: AccountRead, proof_address: Pubkey) -> Result<(RpcAccount, Value)> {
    let account = read.account.context("proof account is absent")?;
    ensure!(
        account.owner == aspis_verifier::id(),
        "proof account is not owned by the canonical V5 verifier"
    );
    ensure!(!account.executable, "proof account must not be executable");
    ensure!(
        account.lamports > 0,
        "proof account has no refundable lamports"
    );
    ensure!(
        account.data.len() >= PROOF_ACCOUNT_HEADER_LEN,
        "proof account is shorter than the verifier header"
    );
    ensure!(
        account.data.get(..4) == Some(PROOF_MAGIC.as_slice()),
        "proof account magic is not ASPU"
    );
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
    let evidence = json!({
        "account": account_value(&account, proof_address, read.context_slot),
        "magic_exact": true,
        "authority_erased": true,
        "stored_proof_bytes": stored_proof_bytes,
        "stored_proof_sha256":
            sha256(&account.data[PROOF_ACCOUNT_HEADER_LEN..proof_end]),
        "trailing_allocation_bytes": account.data.len() - proof_end,
    });
    Ok((account, evidence))
}

fn close_instruction(proof: Pubkey, payer: Pubkey) -> Result<Instruction> {
    ensure!(proof != payer, "proof and refund payer must differ");
    let instruction = Instruction {
        program_id: aspis_verifier::id(),
        accounts: vec![AccountMeta::new(proof, true), AccountMeta::new(payer, true)],
        data: vec![TAG_CLOSE_FINALIZED_PROOF],
    };
    ensure!(
        instruction.data == [TAG_CLOSE_FINALIZED_PROOF],
        "tag64 instruction encoding drift"
    );
    ensure!(
        instruction.accounts.len() == 2
            && instruction.accounts[0].pubkey == proof
            && instruction.accounts[0].is_signer
            && instruction.accounts[0].is_writable
            && instruction.accounts[1].pubkey == payer
            && instruction.accounts[1].is_signer
            && instruction.accounts[1].is_writable,
        "tag64 instruction account layout drift"
    );
    Ok(instruction)
}

fn reconcile_refund(
    keys: &[Pubkey],
    pre_balances: &[u64],
    post_balances: &[u64],
    fee: u64,
    payer: Pubkey,
    proof: Pubkey,
    program: Pubkey,
    validated_proof_lamports: u64,
    validated_program_lamports: u64,
) -> Result<RefundEvidence> {
    ensure!(
        pre_balances.len() == keys.len() && post_balances.len() == keys.len(),
        "finalized balance arrays do not match the exact message account count"
    );
    let account_index = |address: Pubkey| -> Result<usize> {
        keys.iter()
            .position(|key| *key == address)
            .with_context(|| format!("tag64 message omitted account {address}"))
    };
    let payer_index = account_index(payer)?;
    let proof_index = account_index(proof)?;
    let program_index = account_index(program)?;
    ensure!(payer_index != proof_index, "payer/proof indices alias");
    let payer_pre = pre_balances[payer_index];
    let payer_post = post_balances[payer_index];
    let proof_pre = pre_balances[proof_index];
    let proof_post = post_balances[proof_index];
    ensure!(
        proof_pre == validated_proof_lamports,
        "transaction proof pre-balance differs from the validated sealed account"
    );
    ensure!(proof_post == 0, "closed proof post-balance is not zero");
    let refund_lamports = proof_pre
        .checked_sub(proof_post)
        .context("closed proof balance increased")?;
    ensure!(
        refund_lamports == validated_proof_lamports,
        "tag64 did not refund the complete proof-account balance"
    );
    let payer_delta_plus_fee = i128::from(payer_post) - i128::from(payer_pre) + i128::from(fee);
    let exact_refund_equation_reconciled = payer_delta_plus_fee == i128::from(refund_lamports);
    ensure!(
        exact_refund_equation_reconciled,
        "payer delta plus fee does not equal the complete proof refund"
    );
    let every_other_unchanged = pre_balances
        .iter()
        .zip(post_balances)
        .enumerate()
        .all(|(index, (pre, post))| index == payer_index || index == proof_index || pre == post);
    ensure!(
        every_other_unchanged,
        "tag64 changed a message-account balance other than payer/proof"
    );
    ensure!(
        pre_balances[program_index] == validated_program_lamports
            && post_balances[program_index] == validated_program_lamports,
        "canonical verifier Program balance changed during tag64"
    );
    Ok(RefundEvidence {
        fee_lamports: fee,
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
    })
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
        write_json(
            &mut file,
            &json!({
                "artifact": ARTIFACT,
                "status": "in_progress_no_finalized_claim",
                "reserved_at_utc": chrono::Utc::now().to_rfc3339(),
                "warning": IN_PROGRESS_WARNING,
            }),
        )?;
        Ok(Self {
            file,
            path: path.to_path_buf(),
        })
    }

    fn mark_prepared(
        &mut self,
        signature: Signature,
        wire_sha256: &str,
        tag67_run: &Tag67RunEvidence,
        quoted_fee_lamports: u64,
    ) -> Result<()> {
        self.file.set_len(0)?;
        self.file.seek(SeekFrom::Start(0))?;
        write_json(
            &mut self.file,
            &json!({
                "artifact": ARTIFACT,
                "status": "prepared_or_submitted_no_finalized_claim",
                "expected_signature": signature.to_string(),
                "exact_signed_wire_sha256": wire_sha256,
                "required_finalized_tag67_signature": tag67_run.signature,
                "required_finalized_tag67_slot": tag67_run.finalized_slot,
                "required_finalized_tag67_wire_sha256": tag67_run.signed_wire_sha256,
                "quoted_fee_lamports": quoted_fee_lamports,
                "maximum_fee_lamports": MAX_TAG64_FEE_LAMPORTS,
                "updated_at_utc": chrono::Utc::now().to_rfc3339(),
                "warning": IN_PROGRESS_WARNING,
            }),
        )
    }

    fn commit(self, value: &Value) -> Result<()> {
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

/// Close exactly one finalized V5 proof account and refund it to the pinned
/// dedicated mainnet payer. This function has no ProgramData close path.
#[allow(clippy::too_many_lines)]
pub fn execute(arguments: &[String]) -> Result<V5MainnetProofCloseEvidence> {
    let config = parse_args(arguments)?;
    ensure!(
        config.execute_interlock,
        "V5 mainnet proof close requires --execute-v5-mainnet-tag64-close"
    );
    ensure!(
        config.acknowledgement.as_deref() == Some(EXECUTE_ACK),
        "V5 mainnet proof-close acknowledgement mismatch; exact required value: {EXECUTE_ACK}"
    );

    let sbf = exact_regular_file(&config.sbf)?;
    validate_frozen_sbf(&sbf)?;
    ensure!(
        sbf.len() <= config.program_max_len,
        "frozen V5 SBF exceeds declared ProgramData maximum length"
    );

    let payer = secure_keypair(&config.payer_keypair)?;
    let proof = secure_keypair(&config.proof_account_keypair)?;
    let upgrade_authority = secure_keypair(&config.upgrade_authority_keypair)?;
    validate_key_roles(
        payer.pubkey(),
        proof.pubkey(),
        upgrade_authority.pubkey(),
        config.expected_payer,
        config.expected_proof_account,
    )?;

    let rpc_origin_redacted = rpc_origin(&config.rpc_url)?;
    let rpc = Rpc::new(config.rpc_url.clone())?;
    let genesis_hash = rpc.genesis_hash()?;
    ensure!(
        genesis_hash == MAINNET_GENESIS_HASH,
        "V5 proof close requires the pinned Solana mainnet genesis"
    );

    // Prove that this exact retained proof participated in the successful
    // finalized Tag 67 run before constructing or signing any close.
    let tag67_run = rpc.finalized_tag67_run(
        &config.expected_tag67_signature,
        proof.pubkey(),
        payer.pubkey(),
    )?;

    // Acquire the close blockhash only after the Tag 67 check. The proof and
    // dedicated payer are then checked, followed by the exact executable
    // image. No RPC read intervenes between the final executable check and
    // simulation of the signed wire.
    let blockhash = rpc.latest_blockhash()?;
    let payer_before = validate_dedicated_payer(rpc.account(&payer.pubkey())?, payer.pubkey())?;
    let (proof_before_account, proof_before) =
        sealed_proof_exact(rpc.account(&proof.pubkey())?, proof.pubkey())?;
    ensure!(
        proof_before["stored_proof_sha256"].as_str() == Some(config.expected_proof_sha256.as_str()),
        "sealed proof payload does not match --expected-proof-sha256; refusing destructive close"
    );
    let program_before = deployed_program_exact(
        &rpc,
        &sbf,
        config.program_max_len,
        upgrade_authority.pubkey(),
    )?;

    let instruction = close_instruction(proof.pubkey(), payer.pubkey())?;
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
        transaction.signatures.len() == 2
            && transaction.message.header.num_required_signatures == 2,
        "tag64 wire must contain exactly the dedicated payer and proof signatures"
    );
    ensure!(
        transaction.message.account_keys.first() == Some(&payer.pubkey()),
        "dedicated payer is not the transaction fee payer"
    );
    ensure!(
        transaction.message.account_keys.contains(&proof.pubkey())
            && transaction
                .message
                .account_keys
                .contains(&aspis_verifier::id())
            && !transaction
                .message
                .account_keys
                .contains(&upgrade_authority.pubkey()),
        "tag64 message account set drifted or included the non-signing upgrade authority"
    );
    let wire = bincode::serialize(&transaction)?;
    let wire_sha256 = sha256(&wire);
    let message_sha256 = sha256(&bincode::serialize(&transaction.message)?);
    let expected_signature = transaction.signatures[0];
    let quoted_fee_lamports = rpc.fee_for_message(&transaction)?;
    validate_fee_quote(quoted_fee_lamports)?;

    let mut reservation = EvidenceReservation::reserve(&config.evidence)?;
    reservation.mark_prepared(
        expected_signature,
        &wire_sha256,
        &tag67_run,
        quoted_fee_lamports,
    )?;

    let simulation = rpc.simulate_exact(&wire)?;
    ensure!(
        simulation.error.is_none(),
        "exact signed tag64 simulation rejected: {:?}",
        simulation.error
    );
    let simulation_value = json!({
        "exact_signed_wire_simulated": true,
        "error": null,
        "compute_units_consumed": simulation.units,
        "log_count": simulation.logs.len(),
        "logs_sha256": joined_logs_sha256(&simulation.logs),
    });

    // Submit the serialized bytes that were simulated. Never rebuild the
    // message after simulation.
    rpc.send_exact_once(&wire, &expected_signature)?;
    let finalized_slot = rpc.wait_finalized(&expected_signature)?;
    let finalized = rpc.finalized_transaction(&expected_signature, finalized_slot)?;
    ensure!(finalized.slot == finalized_slot);
    ensure!(
        finalized.wire == wire,
        "finalized transaction wire differs from the simulated and submitted bytes"
    );
    ensure!(
        finalized.fee == quoted_fee_lamports,
        "finalized tag64 fee differs from the exact pre-submit message quote"
    );

    let refund = reconcile_refund(
        &transaction.message.account_keys,
        &finalized.pre_balances,
        &finalized.post_balances,
        finalized.fee,
        payer.pubkey(),
        proof.pubkey(),
        aspis_verifier::id(),
        proof_before_account.lamports,
        program_before.program.lamports,
    )?;
    let refund_lamports = refund.refund_lamports;

    let proof_after = rpc.account(&proof.pubkey())?;
    ensure!(
        proof_after.account.is_none(),
        "proof account still exists after finalized tag64"
    );
    let program_after = deployed_program_exact(
        &rpc,
        &sbf,
        config.program_max_len,
        upgrade_authority.pubkey(),
    )?;
    ensure!(
        program_after.programdata_address == program_before.programdata_address
            && program_after.program == program_before.program
            && program_after.programdata == program_before.programdata
            && program_after.programdata_deployment_slot
                == program_before.programdata_deployment_slot
            && program_after.upgrade_authority == program_before.upgrade_authority,
        "verifier Program or ProgramData changed across proof-account close"
    );
    let landed_compute_units = finalized
        .compute_units
        .context("finalized tag64 transaction omitted computeUnitsConsumed")?;
    let evidence = json!({
        "artifact": ARTIFACT,
        "generated_at_utc": chrono::Utc::now().to_rfc3339(),
        "network": "solana-mainnet-beta",
        "genesis_hash": genesis_hash,
        "rpc_origin_redacted": rpc_origin_redacted,
        "canonical_program_id": aspis_verifier::id().to_string(),
        "canonical_program_identity_exact": true,
        "pinned_identities": {
            "payer_and_refund_destination": payer.pubkey().to_string(),
            "expected_payer": config.expected_payer.to_string(),
            "proof_account": proof.pubkey().to_string(),
            "expected_proof_account": config.expected_proof_account.to_string(),
            "upgrade_authority": upgrade_authority.pubkey().to_string(),
            "payer_proof_upgrade_authority_pairwise_distinct": true,
            "upgrade_authority_not_in_tag64_message": true,
        },
        "interlocks": {
            "destructive_execute_interlock_present": true,
            "irreversible_acknowledgement_exact": true,
            "proof_target_identity_exact": true,
            "refund_destination_identity_exact": true,
        },
        "required_finalized_tag67_run": tag67_run,
        "frozen_sbf": {
            "file_name": file_name(&config.sbf)?,
            "bytes": sbf.len(),
            "expected_bytes": FROZEN_V5_SBF_BYTES,
            "sha256": sha256(&sbf),
            "expected_sha256": FROZEN_V5_SBF_SHA256,
            "identity_exact": true,
            "program_max_len": config.program_max_len,
            "expected_program_max_len": FROZEN_V5_PROGRAM_MAX_LEN,
        },
        "payer_before": payer_before,
        "proof_before": proof_before,
        "expected_proof_payload_sha256": config.expected_proof_sha256,
        "program_before": program_value(&program_before),
        "instruction": {
            "tag": TAG_CLOSE_FINALIZED_PROOF,
            "data_hex": format!("{TAG_CLOSE_FINALIZED_PROOF:02x}"),
            "accounts": [
                {
                    "index": 0,
                    "address": proof.pubkey().to_string(),
                    "writable": true,
                    "signer": true,
                    "role": "sealed_program_owned_proof_to_close",
                },
                {
                    "index": 1,
                    "address": payer.pubkey().to_string(),
                    "writable": true,
                    "signer": true,
                    "role": "pinned_dedicated_refund_destination_and_fee_payer",
                }
            ],
            "programdata_close_instruction_present": false,
        },
        "transaction": {
            "signature": expected_signature.to_string(),
            "finalized_slot": finalized_slot,
            "signed_wire_bytes": wire.len(),
            "signed_wire_sha256": wire_sha256,
            "message_sha256": message_sha256,
            "simulation": simulation_value,
            "submitted_identically_to_simulation": true,
            "landed_wire_sha256": sha256(&finalized.wire),
            "landed_wire_identical_to_submitted": true,
            "landed_message_account_count": transaction.message.account_keys.len(),
            "landed_compute_units_consumed": landed_compute_units,
            "landed_log_count": finalized.logs.len(),
            "landed_logs_sha256": joined_logs_sha256(&finalized.logs),
            "quoted_fee_lamports": quoted_fee_lamports,
            "maximum_fee_lamports": MAX_TAG64_FEE_LAMPORTS,
            "landed_fee_lamports": finalized.fee,
            "landed_fee_equals_quote": true,
        },
        "refund": refund,
        "proof_account_absent_after_finality": true,
        "program_after": program_value(&program_after),
        "program_continuity": program_continuity(&program_before, &program_after),
        "programdata_account_remains_present_and_unchanged": true,
        "evidence_file_name": file_name(&config.evidence)?,
        "evidence_file_mode": "0444",
        "scope": [
            "This record covers one finalized tag64 close of the exact pinned V5 proof account on the pinned Solana mainnet genesis.",
            "The complete proof-account balance is refunded to the exact dedicated payer named before signing, with the transaction fee reconciled separately.",
            "The canonical verifier Program and ProgramData remain present and byte-for-byte unchanged.",
            "This command cannot close ProgramData and does not sweep the dedicated payer.",
        ],
    });
    reservation.commit(&evidence)?;

    Ok(V5MainnetProofCloseEvidence {
        signature: expected_signature.to_string(),
        finalized_slot,
        refund_lamports,
        evidence_path: config.evidence.display().to_string(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn valid_args() -> Vec<String> {
        let payer = Pubkey::new_unique();
        let proof = Pubkey::new_unique();
        let tag67_signature = Keypair::new().sign_message(b"test tag67 transaction identity");
        vec![
            "--rpc-url".to_owned(),
            "https://rpc.example.test/private".to_owned(),
            "--payer-keypair".to_owned(),
            "/keys/payer.json".to_owned(),
            "--proof-account-keypair".to_owned(),
            "/keys/proof.json".to_owned(),
            "--upgrade-authority-keypair".to_owned(),
            "/keys/upgrade.json".to_owned(),
            "--expected-payer".to_owned(),
            payer.to_string(),
            "--expected-proof-account".to_owned(),
            proof.to_string(),
            "--expected-proof-sha256".to_owned(),
            "11".repeat(32),
            "--expected-tag67-signature".to_owned(),
            tag67_signature.to_string(),
            "--sbf".to_owned(),
            "/artifacts/aspis_verifier.so".to_owned(),
            "--program-max-len".to_owned(),
            "1300000".to_owned(),
            "--evidence".to_owned(),
            "/evidence/v5-mainnet-proof-close.json".to_owned(),
            "--acknowledgement".to_owned(),
            EXECUTE_ACK.to_owned(),
            "--execute-v5-mainnet-tag64-close".to_owned(),
        ]
    }

    #[test]
    fn parser_requires_every_explicit_identity_and_interlock() {
        let parsed = parse_args(&valid_args()).unwrap();
        assert!(parsed.execute_interlock);
        assert_eq!(parsed.acknowledgement.as_deref(), Some(EXECUTE_ACK));

        let mut missing_payer = valid_args();
        let position = missing_payer
            .iter()
            .position(|arg| arg == "--expected-payer")
            .unwrap();
        missing_payer.drain(position..=position + 1);
        assert!(parse_args(&missing_payer).is_err());

        let mut missing_tag67_signature = valid_args();
        let position = missing_tag67_signature
            .iter()
            .position(|arg| arg == "--expected-tag67-signature")
            .unwrap();
        missing_tag67_signature.drain(position..=position + 1);
        assert!(parse_args(&missing_tag67_signature).is_err());
    }

    #[test]
    fn parser_rejects_unknown_duplicate_and_relative_paths() {
        let mut unknown = valid_args();
        unknown.extend(["--wat".to_owned(), "x".to_owned()]);
        assert!(parse_args(&unknown).is_err());

        let mut duplicate = valid_args();
        duplicate.push("--execute-v5-mainnet-tag64-close".to_owned());
        assert!(parse_args(&duplicate).is_err());

        let mut relative = valid_args();
        let position = relative
            .iter()
            .position(|arg| arg == "--payer-keypair")
            .unwrap();
        relative[position + 1] = "payer.json".to_owned();
        assert!(parse_args(&relative).is_err());

        let mut malformed_signature = valid_args();
        let position = malformed_signature
            .iter()
            .position(|arg| arg == "--expected-tag67-signature")
            .unwrap();
        malformed_signature[position + 1] = "not-a-signature".to_owned();
        assert!(parse_args(&malformed_signature).is_err());
    }

    #[test]
    fn key_roles_pin_refund_and_keep_authority_separate() {
        let payer = Pubkey::new_unique();
        let proof = Pubkey::new_unique();
        let authority = Pubkey::new_unique();
        validate_key_roles(payer, proof, authority, payer, proof).unwrap();
        assert!(validate_key_roles(payer, proof, payer, payer, proof).is_err());
        assert!(validate_key_roles(payer, proof, authority, Pubkey::new_unique(), proof).is_err());
        assert!(validate_key_roles(payer, proof, authority, payer, Pubkey::new_unique()).is_err());
    }

    #[test]
    fn close_wire_is_exact_tag64_with_two_writable_signers() {
        let payer = Pubkey::new_unique();
        let proof = Pubkey::new_unique();
        let instruction = close_instruction(proof, payer).unwrap();
        assert_eq!(instruction.program_id, aspis_verifier::id());
        assert_eq!(instruction.data, vec![64]);
        assert_eq!(
            instruction.accounts,
            vec![AccountMeta::new(proof, true), AccountMeta::new(payer, true)]
        );
        assert!(close_instruction(payer, payer).is_err());
    }

    fn signed_tag67_test_transaction(
        proof_writable: bool,
        duplicate_tag67: bool,
    ) -> (Transaction, Pubkey, Pubkey) {
        let payer = Keypair::new();
        let proof = Pubkey::new_unique();
        let pool = Pubkey::new_unique();
        let nullifier = Pubkey::new_unique();
        let mut data =
            vec![0u8; aspis_verifier::v5_full_transaction::V5_FULL_CU_TRANSACTION_WIRE_BYTES];
        data[0] = aspis_verifier::v5_full_transaction::V5_FULL_CU_TRANSACTION_TAG;
        let proof_meta = if proof_writable {
            AccountMeta::new(proof, false)
        } else {
            AccountMeta::new_readonly(proof, false)
        };
        let instruction = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![
                proof_meta,
                AccountMeta::new(pool, false),
                AccountMeta::new(nullifier, false),
                AccountMeta::new(payer.pubkey(), true),
                AccountMeta::new_readonly(system_program::id(), false),
            ],
            data,
        };
        let instructions = if duplicate_tag67 {
            vec![instruction.clone(), instruction]
        } else {
            vec![instruction]
        };
        let transaction = Transaction::new_signed_with_payer(
            &instructions,
            Some(&payer.pubkey()),
            &[&payer],
            Hash::new_unique(),
        );
        (transaction, payer.pubkey(), proof)
    }

    #[test]
    fn finalized_tag67_wire_binds_exact_readonly_proof_and_payer() {
        let (transaction, payer, proof) = signed_tag67_test_transaction(false, false);
        let signature = transaction.signatures[0];
        let wire = bincode::serialize(&VersionedTransaction::from(transaction)).unwrap();
        let evidence = validate_finalized_tag67_wire(&wire, &signature, proof, payer).unwrap();
        assert_eq!(evidence.tag67_instruction_index, 0);
        assert_eq!(evidence.proof_account, proof.to_string());
        assert_eq!(evidence.tag67_payer, payer.to_string());
        assert!(evidence.proof_role_readonly);
        assert!(evidence.proof_role_non_signer);
    }

    #[test]
    fn finalized_tag67_wire_rejects_wrong_role_identity_signature_and_duplicate() {
        let (writable, payer, proof) = signed_tag67_test_transaction(true, false);
        let writable_signature = writable.signatures[0];
        let writable_wire = bincode::serialize(&VersionedTransaction::from(writable)).unwrap();
        assert!(
            validate_finalized_tag67_wire(&writable_wire, &writable_signature, proof, payer)
                .is_err()
        );

        let (valid, payer, proof) = signed_tag67_test_transaction(false, false);
        let valid_signature = valid.signatures[0];
        let valid_wire = bincode::serialize(&VersionedTransaction::from(valid)).unwrap();
        assert!(validate_finalized_tag67_wire(
            &valid_wire,
            &valid_signature,
            Pubkey::new_unique(),
            payer,
        )
        .is_err());
        let different_signature = Keypair::new().sign_message(b"different transaction");
        assert!(
            validate_finalized_tag67_wire(&valid_wire, &different_signature, proof, payer).is_err()
        );

        let (duplicate, payer, proof) = signed_tag67_test_transaction(false, true);
        let duplicate_signature = duplicate.signatures[0];
        let duplicate_wire = bincode::serialize(&VersionedTransaction::from(duplicate)).unwrap();
        assert!(
            validate_finalized_tag67_wire(&duplicate_wire, &duplicate_signature, proof, payer,)
                .is_err()
        );
    }

    #[test]
    fn tag64_fee_quote_cap_is_explicit() {
        validate_fee_quote(MAX_TAG64_FEE_LAMPORTS).unwrap();
        assert!(validate_fee_quote(0).is_err());
        assert!(validate_fee_quote(MAX_TAG64_FEE_LAMPORTS + 1).is_err());
    }

    #[test]
    fn frozen_sbf_check_rejects_nonrelease_bytes() {
        assert!(validate_frozen_sbf(&[]).is_err());
        assert!(validate_frozen_sbf(&vec![0u8; FROZEN_V5_SBF_BYTES]).is_err());
    }

    #[test]
    fn frozen_sbf_check_accepts_committed_release_artifact() {
        let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
        let sbf =
            fs::read(workspace.join(
                "release/aspis-v5-tag67-frozen-candidate-v1/program/aspis_verifier_v5_tag67.so",
            ))
            .unwrap();
        validate_frozen_sbf(&sbf).unwrap();
    }

    #[test]
    fn refund_equation_requires_full_close_and_only_payer_proof_changes() {
        let payer = Pubkey::new_unique();
        let proof = Pubkey::new_unique();
        let program = Pubkey::new_unique();
        let keys = [payer, proof, program];
        let before = [1_000_000, 400_000, 1_141_440];
        let after = [1_395_000, 0, 1_141_440];
        let refund = reconcile_refund(
            &keys, &before, &after, 5_000, payer, proof, program, 400_000, 1_141_440,
        )
        .unwrap();
        assert_eq!(refund.refund_lamports, 400_000);
        assert!(refund.exact_refund_equation_reconciled);

        let bad_after = [1_395_000, 1, 1_141_440];
        assert!(reconcile_refund(
            &keys, &before, &bad_after, 5_000, payer, proof, program, 400_000, 1_141_440,
        )
        .is_err());

        let changed_program = [1_395_000, 0, 1_141_441];
        assert!(reconcile_refund(
            &keys,
            &before,
            &changed_program,
            5_000,
            payer,
            proof,
            program,
            400_000,
            1_141_440,
        )
        .is_err());
    }

    #[test]
    fn rpc_policy_requires_https_and_redacts_credentials_in_path() {
        assert!(rpc_origin("http://api.mainnet-beta.solana.com").is_err());
        assert_eq!(
            rpc_origin("https://rpc.example.test/private?token=secret").unwrap(),
            "https://rpc.example.test/<redacted>"
        );
    }
}
