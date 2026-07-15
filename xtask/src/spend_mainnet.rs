//! Fail-closed, read-only readiness checks for the Spend mainnet-beta run.
//!
//! This module intentionally contains no transaction submission path.  The
//! production runbook describes the reviewed sequence that a future executor
//! must implement.  Keeping readiness read-only makes an accidental invocation
//! incapable of spending SOL or changing mainnet state.

use std::{
    env, fs,
    net::{IpAddr, Ipv4Addr},
    os::unix::fs::PermissionsExt,
    path::{Component, Path, PathBuf},
    time::Duration,
};

use anyhow::{anyhow, Context, Result};
use serde::Serialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use solana_sdk::{
    bpf_loader_upgradeable,
    pubkey::Pubkey,
    signature::{read_keypair_file, Signer},
};

use aspis_verifier::{
    atomic_payment::{
        atomic_nullifier_address, ATOMIC_NULLIFIER_MARKER_LEN, ATOMIC_POOL_STATE_LEN,
    },
    PROOF_ACCOUNT_HEADER_LEN,
};

const MAINNET_BETA_GENESIS_HASH: &str = "5eykt4UsFv8P8NJdTREpY1vzqKqZKvdpKuc147dw2N9d";
const CU_LIMIT: u64 = 1_400_000;
const BUFFER_METADATA_BYTES: usize = 37;
const PROGRAMDATA_METADATA_BYTES: usize = 45;
const PROGRAM_ACCOUNT_BYTES: usize = 36;
const REPLAY_PROBE_PROOF_BYTES: usize = 1;
const MAX_TRANSACTION_FEES_LAMPORTS: u64 = 50_000_000;
const CLEANUP_RESOURCE_COUNT: u64 = 4;
const MAX_CLEANUP_TRANSACTION_FEE_LAMPORTS: u64 = 1_000_000;
const CLEANUP_FEE_RESERVE_LAMPORTS: u64 =
    CLEANUP_RESOURCE_COUNT * MAX_CLEANUP_TRANSACTION_FEE_LAMPORTS;
const FORWARD_FEE_BUDGET_LAMPORTS: u64 =
    MAX_TRANSACTION_FEES_LAMPORTS - CLEANUP_FEE_RESERVE_LAMPORTS;
const MAX_DEMO_COST_USD_CENTS: u64 = 2_000;
const SOL_USD_QUOTE_MAX_AGE_SECONDS: i64 = 3_600;
const SOL_USD_QUOTE_SAFETY_BPS: u64 = 11_000;
const SOL_USD_TICKER_URL: &str = "https://api.exchange.coinbase.com/products/SOL-USD/ticker";
const SOL_USD_QUOTE_ACK: &str = "I_ACKNOWLEDGE_THE_PINNED_COINBASE_SOL_USD_QUOTE_FETCH";
const PRIVATE_RPC_ACK: &str = "I_CONFIRM_THIS_IS_A_DEDICATED_PAID_MAINNET_RPC";
const PUBLIC_RPC_DIRECT_TPU_ACK: &str =
    "I_ACCEPT_OFFICIAL_PUBLIC_RPC_READS_WITH_DIRECT_TPU_LOADER_SUBMISSION";

#[derive(Clone, Debug, Serialize)]
pub struct ReadinessGate {
    pub name: String,
    pub passed: bool,
    pub evidence: String,
}

#[derive(Clone, Debug, Default, Serialize)]
pub struct RentBudget {
    pub program_buffer_lamports: Option<u64>,
    pub programdata_lamports: Option<u64>,
    pub program_account_lamports: Option<u64>,
    pub pool_account_lamports: Option<u64>,
    pub proof_account_lamports: Option<u64>,
    pub replay_probe_account_lamports: Option<u64>,
    pub nullifier_account_lamports: Option<u64>,
    pub fee_reserve_lamports: u64,
    pub forward_fee_budget_lamports: u64,
    pub cleanup_fee_reserve_lamports: u64,
    pub cleanup_resource_count: u64,
    pub max_cleanup_transaction_fee_lamports: u64,
    /// Working capital for the complete fresh demo. Loader-v3 drains the
    /// temporary buffer back to the payer before funding ProgramData, so these
    /// two rent deposits must never be added together.
    pub conservative_fresh_deploy_peak_lamports: Option<u64>,
    /// Rent returned by successful tag65 proof consumption followed by
    /// loader-v3 program closure.
    pub refundable_after_success_lamports: Option<u64>,
    /// Upper bound retained or spent after both refunds. This deliberately
    /// counts the complete fee reserve and the small pool/nullifier accounts.
    pub projected_nonrefundable_lamports: Option<u64>,
    pub sol_usd_observed_microdollars: Option<u64>,
    pub sol_usd_cap_microdollars: Option<u64>,
    pub sol_usd_quoted_at_utc: Option<String>,
    pub sol_usd_fetched_at_utc: Option<String>,
    pub sol_usd_quote_response_sha256: Option<String>,
    pub sol_usd_quote_source: &'static str,
    pub sol_usd_quote_safety_bps: u64,
    pub sol_usd_quote_error: Option<String>,
    pub max_demo_cost_usd_cents: u64,
    pub max_nonrefundable_lamports_at_quote: Option<u64>,
    pub projected_nonrefundable_usd_cents_at_quote: Option<u64>,
    pub required_from_current_state_lamports: Option<u64>,
    pub payer_balance_lamports: Option<u64>,
    pub surplus_lamports: Option<i128>,
}

#[derive(Clone, Debug, Serialize)]
pub struct RequiredFutureSigningSafetyPolicy {
    pub implementation_status: &'static str,
    pub hard_demo_cost_usd_cents: u64,
    pub aggregate_transaction_fee_ceiling_lamports: u64,
    pub forward_fee_budget_lamports: u64,
    pub cleanup_fee_reserve_lamports: u64,
    pub cleanup_resource_count: u64,
    pub max_cleanup_transaction_fee_lamports: u64,
    pub journal_must_be_hash_chained_and_fsynced_before_signing: bool,
    pub signed_wire_must_be_journaled_before_submission: bool,
    pub restart_must_reconcile_journal_before_signing: bool,
    pub stale_quote_or_failed_forward_fee_gate_enters_cleanup_only_mode: bool,
    pub cleanup_only_mode_is_irreversible_for_run: bool,
    pub cleanup_only_mode_may_create_accounts_or_rent: bool,
    pub cleanup_refund_destination_must_be_payer: bool,
    pub forward_signing_requirements: Vec<&'static str>,
    pub cleanup_signing_requirements: Vec<&'static str>,
    pub cleanup_only_allowlist: Vec<&'static str>,
}

#[derive(Clone, Debug, Serialize)]
pub struct SpendMainnetReadiness {
    pub artifact: &'static str,
    pub generated_at_utc: String,
    pub command: String,
    pub mode: &'static str,
    pub mutations_performed: bool,
    pub read_only_preflight_green: bool,
    pub readiness_is_execution_attestation: bool,
    pub current_executor_journal_scope: &'static str,
    pub expected_mainnet_genesis_hash: &'static str,
    pub observed_genesis_hash: Option<String>,
    pub rpc_origin_redacted: Option<String>,
    /// The runtime address supplied by the disposable mainnet program
    /// keypair. Every ProgramData address, PDA, and owner check is relative to
    /// this value, never to the compile-time code identity below.
    pub program_id: Option<String>,
    pub canonical_code_program_id: String,
    pub expected_programdata_address: Option<String>,
    pub expected_loader_program_id: String,
    pub certified_statement_path: Option<String>,
    pub certified_statement_bytes: Option<usize>,
    pub certified_statement_sha256: Option<String>,
    pub certified_pool_address: Option<String>,
    pub certified_statement_nullifier_hex: Option<String>,
    pub expected_nullifier_address: Option<String>,
    pub expected_nullifier_bump: Option<u8>,
    pub fresh_address_snapshot_context_slot: Option<u64>,
    pub payer_pubkey: Option<String>,
    pub deploy_keypair_pubkey: Option<String>,
    pub upgrade_policy: Option<String>,
    pub observed_upgrade_authority: Option<String>,
    pub program_already_deployed: Option<bool>,
    pub release_certificate_path: String,
    pub release_certificate_sha256: Option<String>,
    pub release_certificate_generated_at_utc: Option<String>,
    pub release_certificate_green: bool,
    pub proof_path: Option<String>,
    pub proof_bytes: Option<usize>,
    pub proof_sha256: Option<String>,
    pub sbf_path: Option<String>,
    pub sbf_bytes: Option<usize>,
    pub sbf_sha256: Option<String>,
    pub program_max_len: Option<usize>,
    pub rent_budget: RentBudget,
    pub required_future_signing_safety_policy: RequiredFutureSigningSafetyPolicy,
    pub gates: Vec<ReadinessGate>,
    pub blockers: Vec<String>,
    pub required_future_execution_sequence: Vec<&'static str>,
    pub required_future_execution_evidence_fields: Vec<&'static str>,
    pub explicit_nonclaims: Vec<&'static str>,
}

struct Rpc {
    endpoint: String,
    client: reqwest::blocking::Client,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct FinalizedAccountPresenceSnapshot {
    context_slot: u64,
    exists: Vec<bool>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CertifiedStatement {
    path: String,
    bytes: usize,
    sha256: String,
    pool_address: Pubkey,
    nullifier: [u8; 32],
}

impl Rpc {
    fn new(endpoint: String) -> Result<Self> {
        Ok(Self {
            endpoint,
            client: reqwest::blocking::Client::builder()
                .timeout(Duration::from_secs(45))
                .build()?,
        })
    }

    fn call(&self, method: &str, params: Value) -> Result<Value> {
        let response = self
            .client
            .post(&self.endpoint)
            .json(&json!({"jsonrpc": "2.0", "id": 1, "method": method, "params": params}))
            .send()
            .with_context(|| format!("RPC {method} request failed"))?;
        let value: Value = response
            .json()
            .with_context(|| format!("RPC {method} returned non-JSON data"))?;
        if let Some(error) = value.get("error") {
            return Err(anyhow!("RPC {method} returned an error: {error}"));
        }
        value
            .get("result")
            .cloned()
            .ok_or_else(|| anyhow!("RPC {method} omitted result"))
    }

    fn balance_finalized(&self, address: &Pubkey) -> Result<u64> {
        self.call(
            "getBalance",
            json!([address.to_string(), {"commitment": "finalized"}]),
        )?["value"]
            .as_u64()
            .context("getBalance result was not u64")
    }

    fn rent_exempt(&self, bytes: usize) -> Result<u64> {
        self.call("getMinimumBalanceForRentExemption", json!([bytes]))?
            .as_u64()
            .context("rent result was not u64")
    }

    fn accounts_exist_finalized(
        &self,
        addresses: &[Pubkey],
    ) -> Result<FinalizedAccountPresenceSnapshot> {
        let result = self.call(
            "getMultipleAccounts",
            json!([
                addresses.iter().map(ToString::to_string).collect::<Vec<_>>(),
                {
                    "encoding": "base64",
                    "commitment": "finalized",
                    "dataSlice": {"offset": 0, "length": 0}
                }
            ]),
        )?;
        parse_account_presence_snapshot(&result, addresses.len())
    }
}

fn parse_account_presence_snapshot(
    result: &Value,
    expected_accounts: usize,
) -> Result<FinalizedAccountPresenceSnapshot> {
    let context_slot = result["context"]["slot"]
        .as_u64()
        .context("getMultipleAccounts result omitted context.slot")?;
    let values = result["value"]
        .as_array()
        .context("getMultipleAccounts result omitted value array")?;
    if values.len() != expected_accounts {
        return Err(anyhow!(
            "getMultipleAccounts returned {} accounts; expected {expected_accounts}",
            values.len()
        ));
    }
    let exists = values
        .iter()
        .map(|value| {
            if value.is_null() {
                Ok(false)
            } else if value.is_object() {
                Ok(true)
            } else {
                Err(anyhow!(
                    "getMultipleAccounts value was neither null nor an account object"
                ))
            }
        })
        .collect::<Result<Vec<_>>>()?;
    Ok(FinalizedAccountPresenceSnapshot {
        context_slot,
        exists,
    })
}

#[derive(Clone, Debug)]
struct SolUsdQuote {
    observed_microdollars: u64,
    cap_microdollars: u64,
    quoted_at_utc: String,
    fetched_at_utc: String,
    response_sha256: String,
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn usd_cent_cap_lamports(usd_cents: u64, sol_usd_microdollars: u64) -> Option<u64> {
    if sol_usd_microdollars == 0 {
        return None;
    }
    let numerator = u128::from(usd_cents)
        .checked_mul(10_000)?
        .checked_mul(1_000_000_000)?;
    u64::try_from(numerator / u128::from(sol_usd_microdollars)).ok()
}

fn lamports_to_usd_cents_ceiling(lamports: u64, sol_usd_microdollars: u64) -> Option<u64> {
    if sol_usd_microdollars == 0 {
        return None;
    }
    let denominator = 1_000_000_000u128.checked_mul(10_000)?;
    let numerator = u128::from(lamports).checked_mul(u128::from(sol_usd_microdollars))?;
    let rounded = numerator.checked_add(denominator.checked_sub(1)?)? / denominator;
    u64::try_from(rounded).ok()
}

fn decimal_usd_to_microdollars_ceiling(value: &str) -> Option<u64> {
    let (whole, fraction) = value.split_once('.').unwrap_or((value, ""));
    if whole.is_empty()
        || !whole.bytes().all(|byte| byte.is_ascii_digit())
        || !fraction.bytes().all(|byte| byte.is_ascii_digit())
    {
        return None;
    }
    let whole = whole.parse::<u64>().ok()?;
    let retained_len = fraction.len().min(6);
    let retained = &fraction[..retained_len];
    let mut micros = whole.checked_mul(1_000_000)?.checked_add(
        retained.parse::<u64>().unwrap_or(0).checked_mul(
            10u64.checked_pow(u32::try_from(6usize.checked_sub(retained_len)?).ok()?)?,
        )?,
    )?;
    if fraction
        .get(retained_len..)
        .is_some_and(|tail| tail.bytes().any(|byte| byte != b'0'))
    {
        micros = micros.checked_add(1)?;
    }
    (micros > 0).then_some(micros)
}

fn fetch_sol_usd_quote() -> Result<SolUsdQuote> {
    let response = reqwest::blocking::Client::builder()
        .timeout(Duration::from_secs(10))
        .build()?
        .get(SOL_USD_TICKER_URL)
        .header(reqwest::header::USER_AGENT, "aspis-spend-readiness/1")
        .send()
        .context("pinned SOL/USD quote request failed")?
        .error_for_status()
        .context("pinned SOL/USD quote returned an error status")?;
    let bytes = response.bytes().context("SOL/USD quote body unavailable")?;
    if bytes.len() > 64 * 1024 {
        return Err(anyhow!("SOL/USD quote body exceeded 64 KiB"));
    }
    let value: Value = serde_json::from_slice(&bytes).context("SOL/USD quote was not JSON")?;
    let price = value["price"]
        .as_str()
        .and_then(decimal_usd_to_microdollars_ceiling)
        .context("SOL/USD ticker price was missing or invalid")?;
    let ask = value["ask"]
        .as_str()
        .and_then(decimal_usd_to_microdollars_ceiling)
        .context("SOL/USD ticker ask was missing or invalid")?;
    let observed_microdollars = price.max(ask);
    let cap_price_numerator = u128::from(observed_microdollars)
        .checked_mul(u128::from(SOL_USD_QUOTE_SAFETY_BPS))
        .and_then(|value| value.checked_add(9_999))
        .context("SOL/USD safety-price arithmetic overflow")?;
    let cap_microdollars =
        u64::try_from(cap_price_numerator / 10_000).context("SOL/USD safety price exceeded u64")?;
    let quoted_at_utc = value["time"]
        .as_str()
        .context("SOL/USD ticker time was missing")?;
    chrono::DateTime::parse_from_rfc3339(quoted_at_utc)
        .context("SOL/USD ticker time was invalid")?;
    Ok(SolUsdQuote {
        observed_microdollars,
        cap_microdollars,
        quoted_at_utc: quoted_at_utc.to_owned(),
        fetched_at_utc: chrono::Utc::now().to_rfc3339(),
        response_sha256: sha256(&bytes),
    })
}

fn workspace_path(root: &Path, path: &str) -> PathBuf {
    let path = PathBuf::from(path);
    if path.is_absolute() {
        path
    } else {
        root.join(path)
    }
}

fn decode_lower_hex_32(value: &str, label: &str) -> Result<[u8; 32]> {
    let bytes = value.as_bytes();
    if bytes.len() != 64
        || !bytes
            .iter()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(byte))
    {
        return Err(anyhow!(
            "{label} must be exactly 64 lowercase hex characters"
        ));
    }
    let mut decoded = [0u8; 32];
    for (index, pair) in bytes.chunks_exact(2).enumerate() {
        let nibble = |byte: u8| -> u8 {
            if byte.is_ascii_digit() {
                byte - b'0'
            } else {
                byte - b'a' + 10
            }
        };
        decoded[index] = (nibble(pair[0]) << 4) | nibble(pair[1]);
    }
    Ok(decoded)
}

fn lower_hex_32(bytes: &[u8; 32]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn certified_statement_from_release(root: &Path, release: &Value) -> Result<CertifiedStatement> {
    let instance = release
        .get("release_instance")
        .context("release certificate omitted release_instance")?;
    let statement_path = instance["statement_path"]
        .as_str()
        .context("release instance omitted statement_path")?;
    let relative = Path::new(statement_path);
    if relative.is_absolute()
        || relative
            .components()
            .any(|component| !matches!(component, Component::Normal(_)))
    {
        return Err(anyhow!(
            "release statement_path must be a normal workspace-relative path"
        ));
    }
    let expected_bytes = instance["statement_bytes"]
        .as_u64()
        .and_then(|bytes| usize::try_from(bytes).ok())
        .context("release instance statement_bytes was missing or invalid")?;
    let expected_sha = instance["statement_sha256"]
        .as_str()
        .context("release instance omitted statement_sha256")?;
    decode_lower_hex_32(expected_sha, "release statement SHA-256")?;

    let pinned_statement = release["source_artifacts"]
        .as_array()
        .context("release source_artifacts missing")?
        .iter()
        .filter(|artifact| artifact["label"].as_str() == Some("production_statement"))
        .collect::<Vec<_>>();
    if pinned_statement.len() != 1 {
        return Err(anyhow!(
            "release source_artifacts must contain exactly one production_statement"
        ));
    }
    let pinned_statement = pinned_statement[0];
    if pinned_statement["path"].as_str() != Some(statement_path)
        || pinned_statement["bytes"].as_u64() != Some(expected_bytes as u64)
        || pinned_statement["sha256"].as_str() != Some(expected_sha)
    {
        return Err(anyhow!(
            "release instance statement identity disagrees with production_statement source artifact"
        ));
    }

    let bytes = fs::read(root.join(relative)).with_context(|| {
        format!("release-certified statement sidecar is unavailable: {statement_path}")
    })?;
    if bytes.len() != expected_bytes || sha256(&bytes) != expected_sha {
        return Err(anyhow!(
            "release-certified statement sidecar length or SHA-256 mismatch"
        ));
    }
    let statement: Value =
        serde_json::from_slice(&bytes).context("release-certified statement is not JSON")?;
    if statement["artifact"].as_str() != Some("profile23_production_statement") {
        return Err(anyhow!(
            "release-certified statement has the wrong artifact identifier"
        ));
    }
    let pool_hex = statement["pool_hex"]
        .as_str()
        .context("release-certified statement omitted pool_hex")?;
    let pool_bytes = decode_lower_hex_32(pool_hex, "statement pool_hex")?;
    if instance["statement_pool_hex"].as_str() != Some(pool_hex) {
        return Err(anyhow!(
            "release instance statement_pool_hex disagrees with certified sidecar"
        ));
    }
    let statement_sequence = statement["sequence"]
        .as_u64()
        .context("release-certified statement omitted sequence")?;
    if instance["statement_sequence"].as_u64() != Some(statement_sequence) {
        return Err(anyhow!(
            "release instance statement_sequence disagrees with certified sidecar"
        ));
    }
    let nullifier = decode_lower_hex_32(
        statement["nullifier_hex"]
            .as_str()
            .context("release-certified statement omitted nullifier_hex")?,
        "statement nullifier_hex",
    )?;

    Ok(CertifiedStatement {
        path: statement_path.to_owned(),
        bytes: bytes.len(),
        sha256: expected_sha.to_owned(),
        pool_address: Pubkey::new_from_array(pool_bytes),
        nullifier,
    })
}

fn disposable_program_id_is_distinct(candidate: Option<Pubkey>, canonical: Pubkey) -> bool {
    candidate.is_some_and(|program_id| program_id != canonical)
}

fn public_key_from_private_file(path: &Path) -> Result<Pubkey> {
    let metadata = fs::symlink_metadata(path)
        .with_context(|| format!("keypair file is unavailable: {}", path.display()))?;
    if !metadata.file_type().is_file() || metadata.file_type().is_symlink() {
        return Err(anyhow!("keypair path must be a regular, non-symlink file"));
    }
    if metadata.permissions().mode() & 0o077 != 0 {
        return Err(anyhow!(
            "keypair file permissions are too broad; require no group/other bits"
        ));
    }
    // No secret bytes or paths derived from their contents are ever serialized.
    let keypair = read_keypair_file(path).map_err(|_| anyhow!("could not read keypair file"))?;
    Ok(keypair.pubkey())
}

fn rpc_policy(endpoint: &str) -> Result<String> {
    let url = reqwest::Url::parse(endpoint).context("RPC URL is invalid")?;
    if url.scheme() != "https" {
        return Err(anyhow!("RPC must use HTTPS"));
    }
    if !url.username().is_empty() || url.password().is_some() {
        return Err(anyhow!("RPC credentials must not use URL userinfo"));
    }
    let host = url.host_str().context("RPC URL has no host")?;
    let normalized = host.to_ascii_lowercase();
    let public_endpoints = [
        "api.mainnet-beta.solana.com",
        "api.mainnet.solana.com",
        "solana-api.projectserum.com",
    ];
    if public_endpoints.contains(&normalized.as_str()) {
        if env::var("ASPIS_SPEND_MAINNET_PUBLIC_RPC_DIRECT_TPU_ACK").as_deref()
            != Ok(PUBLIC_RPC_DIRECT_TPU_ACK)
        {
            return Err(anyhow!(
                "public RPC requires the exact direct-TPU transport acknowledgement"
            ));
        }
        let port = url
            .port()
            .map(|port| format!(":{port}"))
            .unwrap_or_default();
        return Ok(format!("https://{host}{port}/<public-read-rpc>"));
    }
    if normalized == "localhost" || normalized.ends_with(".localhost") {
        return Err(anyhow!("local RPC endpoint is prohibited"));
    }
    if let Ok(ip) = normalized.parse::<IpAddr>() {
        let prohibited = match ip {
            IpAddr::V4(ip) => {
                ip.is_loopback()
                    || ip.is_private()
                    || ip.is_link_local()
                    || ip == Ipv4Addr::UNSPECIFIED
            }
            IpAddr::V6(ip) => ip.is_loopback() || ip.is_unspecified(),
        };
        if prohibited {
            return Err(anyhow!("local/private RPC address is prohibited"));
        }
    }
    if env::var("ASPIS_SPEND_MAINNET_RPC_IS_PRIVATE").as_deref() != Ok(PRIVATE_RPC_ACK) {
        return Err(anyhow!(
            "missing exact dedicated/private RPC acknowledgement"
        ));
    }
    let port = url
        .port()
        .map(|port| format!(":{port}"))
        .unwrap_or_default();
    Ok(format!("https://{host}{port}/<redacted>"))
}

fn release_source_artifacts_are_exact(root: &Path, release: &Value) -> Result<(bool, String)> {
    let artifacts = release["source_artifacts"]
        .as_array()
        .context("release source_artifacts missing")?;
    let mut failures = Vec::new();
    for artifact in artifacts {
        let label = artifact["label"].as_str().unwrap_or("unnamed");
        let path = artifact["path"]
            .as_str()
            .ok_or_else(|| anyhow!("source artifact {label} has no path"))?;
        let expected_bytes = artifact["bytes"]
            .as_u64()
            .ok_or_else(|| anyhow!("source artifact {label} has no byte count"))?;
        let expected_sha = artifact["sha256"]
            .as_str()
            .ok_or_else(|| anyhow!("source artifact {label} has no SHA-256"))?;
        let bytes = match fs::read(workspace_path(root, path)) {
            Ok(bytes) => bytes,
            Err(_) => {
                failures.push(format!("{label}:missing"));
                continue;
            }
        };
        if bytes.len() as u64 != expected_bytes || sha256(&bytes) != expected_sha {
            failures.push(format!("{label}:drift"));
        }
    }
    Ok((
        failures.is_empty(),
        if failures.is_empty() {
            format!("{} release-pinned artifacts match", artifacts.len())
        } else {
            format!("mismatches={}", failures.join(","))
        },
    ))
}

fn gate(gates: &mut Vec<ReadinessGate>, name: &str, passed: bool, evidence: impl Into<String>) {
    gates.push(ReadinessGate {
        name: name.to_owned(),
        passed,
        evidence: evidence.into(),
    });
}

fn add_blockers(gates: &[ReadinessGate]) -> Vec<String> {
    gates
        .iter()
        .filter(|gate| !gate.passed)
        .map(|gate| gate.name.clone())
        .collect()
}

/// Executes only read-only filesystem and RPC calls. `--execute` is parsed
/// solely to fail closed: live execution is exposed by a separate command.
pub fn evaluate(workspace_root: &Path, arguments: &[String]) -> SpendMainnetReadiness {
    let mut gates = Vec::new();
    let execute_requested = arguments.iter().any(|arg| arg == "--execute");
    let unknown_arguments = arguments
        .iter()
        .filter(|arg| arg.as_str() != "--execute")
        .cloned()
        .collect::<Vec<_>>();
    gate(
        &mut gates,
        "read_only_mode",
        !execute_requested,
        if execute_requested {
            "--execute is prohibited on readiness; use the separate reviewed mainnet executor"
        } else {
            "readiness performs no transaction construction, signing, submission, deployment, or account writes"
        },
    );
    gate(
        &mut gates,
        "known_arguments_only",
        unknown_arguments.is_empty(),
        format!("unknown_argument_count={}", unknown_arguments.len()),
    );

    let release_rel = "results/spend/spend_one_transaction_release.json";
    let release_path = workspace_root.join(release_rel);
    let release_bytes = fs::read(&release_path).ok();
    let release_sha = release_bytes.as_deref().map(sha256);
    let release: Option<Value> = release_bytes
        .as_deref()
        .and_then(|bytes| serde_json::from_slice(bytes).ok());
    gate(
        &mut gates,
        "release_certificate_present_and_parseable",
        release.is_some(),
        format!("path={release_rel}, sha256={release_sha:?}"),
    );

    let all_release_gates_green = release
        .as_ref()
        .and_then(|value| value["gates"].as_array())
        .is_some_and(|release_gates| {
            !release_gates.is_empty()
                && release_gates
                    .iter()
                    .all(|release_gate| release_gate["passed"].as_bool() == Some(true))
        });
    let release_declares_green = release.as_ref().is_some_and(|value| {
        value["released"].as_bool() == Some(true)
            && value["status"].as_str() == Some("released_all_required_gates_green")
    });
    gate(
        &mut gates,
        "release_certificate_all_gates_green",
        release_declares_green && all_release_gates_green,
        format!(
            "declares_green={release_declares_green}, all_embedded_gates_green={all_release_gates_green}"
        ),
    );

    let release_cu = release
        .as_ref()
        .and_then(|value| value["max_literal_production_tag65_cu"].as_u64());
    gate(
        &mut gates,
        "release_certificate_under_1_4m_cu",
        release_cu.is_some_and(|cu| cu < CU_LIMIT),
        format!("tag65_cu={release_cu:?}, limit={CU_LIMIT}"),
    );

    let (source_exact, source_evidence) = release
        .as_ref()
        .and_then(|release| release_source_artifacts_are_exact(workspace_root, release).ok())
        .unwrap_or((false, "release source artifacts unavailable".to_owned()));
    gate(
        &mut gates,
        "release_pinned_artifacts_exact",
        source_exact,
        source_evidence,
    );

    let certified_statement_result = release
        .as_ref()
        .ok_or_else(|| anyhow!("release certificate unavailable"))
        .and_then(|release| certified_statement_from_release(workspace_root, release));
    let (certified_statement, certified_statement_error) = match certified_statement_result {
        Ok(statement) => (Some(statement), None),
        Err(error) => (None, Some(error.to_string())),
    };
    gate(
        &mut gates,
        "release_certified_statement_sidecar_exact_and_derived",
        certified_statement.is_some(),
        format!(
            "path={:?}, bytes={:?}, sha256={:?}, pool_address={:?}, nullifier_hex={:?}, error={certified_statement_error:?}",
            certified_statement.as_ref().map(|statement| statement.path.as_str()),
            certified_statement.as_ref().map(|statement| statement.bytes),
            certified_statement.as_ref().map(|statement| statement.sha256.as_str()),
            certified_statement.as_ref().map(|statement| statement.pool_address),
            certified_statement
                .as_ref()
                .map(|statement| lower_hex_32(&statement.nullifier)),
        ),
    );

    let proof_rel = release
        .as_ref()
        .and_then(|value| value["proof"]["actual_path"].as_str())
        .map(ToOwned::to_owned);
    let proof_expected_sha = release
        .as_ref()
        .and_then(|value| value["proof"]["sha256"].as_str())
        .map(ToOwned::to_owned);
    let proof_expected_bytes = release
        .as_ref()
        .and_then(|value| value["proof"]["bytes"].as_u64())
        .and_then(|bytes| usize::try_from(bytes).ok());
    let proof_local = proof_rel
        .as_deref()
        .and_then(|path| fs::read(workspace_path(workspace_root, path)).ok());
    let proof_sha = proof_local.as_deref().map(sha256);
    let proof_exact = proof_local.as_ref().is_some_and(|bytes| {
        Some(bytes.len()) == proof_expected_bytes && proof_sha == proof_expected_sha
    });
    gate(
        &mut gates,
        "exact_release_proof_present",
        proof_exact,
        format!(
            "bytes={:?}/{proof_expected_bytes:?}, sha256_match={}",
            proof_local.as_ref().map(Vec::len),
            proof_sha == proof_expected_sha
        ),
    );
    let proof_sha_log_binding_ready = proof_exact
        && proof_expected_sha.as_deref().is_some_and(|digest| {
            digest.len() == 64
                && digest
                    .bytes()
                    .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        });
    gate(
        &mut gates,
        "release_proof_sha256_ready_for_program_log_binding",
        proof_sha_log_binding_ready,
        format!(
            "release_proof_sha256={proof_expected_sha:?}, local_sha256={proof_sha:?}, required_log_domain=aspis-proof-sha256-v1"
        ),
    );

    let sbf_rel = release
        .as_ref()
        .and_then(|value| value["default_production_sbf"]["path"].as_str())
        .map(ToOwned::to_owned);
    let sbf_expected_sha = release
        .as_ref()
        .and_then(|value| value["default_production_sbf"]["sha256"].as_str())
        .map(ToOwned::to_owned);
    let sbf_expected_bytes = release
        .as_ref()
        .and_then(|value| value["default_production_sbf"]["bytes"].as_u64())
        .and_then(|bytes| usize::try_from(bytes).ok());
    let sbf_local = sbf_rel
        .as_deref()
        .and_then(|path| fs::read(workspace_path(workspace_root, path)).ok());
    let sbf_sha = sbf_local.as_deref().map(sha256);
    let sbf_exact = sbf_local.as_ref().is_some_and(|bytes| {
        Some(bytes.len()) == sbf_expected_bytes && sbf_sha == sbf_expected_sha
    });
    gate(
        &mut gates,
        "exact_release_sbf_present",
        sbf_exact,
        format!(
            "bytes={:?}/{sbf_expected_bytes:?}, sha256_match={}",
            sbf_local.as_ref().map(Vec::len),
            sbf_sha == sbf_expected_sha
        ),
    );
    let program_max_len = env::var("ASPIS_SPEND_MAINNET_PROGRAM_MAX_LEN")
        .ok()
        .and_then(|value| value.parse::<usize>().ok());
    let program_max_len_exact = program_max_len
        .zip(sbf_local.as_ref().map(Vec::len))
        .is_some_and(|(max_len, sbf_len)| max_len == sbf_len);
    gate(
        &mut gates,
        "program_max_len_equals_exact_sbf_length",
        program_max_len_exact,
        format!(
            "declared_max_len={program_max_len:?}, sbf_len={:?}",
            sbf_local.as_ref().map(Vec::len)
        ),
    );

    let canonical_code_program_id = aspis_verifier::id();
    let deploy_pubkey = env::var_os("ASPIS_SPEND_MAINNET_PROGRAM_KEYPAIR")
        .and_then(|path| public_key_from_private_file(Path::new(&path)).ok());
    gate(
        &mut gates,
        "disposable_program_keypair_secure_and_readable",
        deploy_pubkey.is_some(),
        format!("disposable_program_id={deploy_pubkey:?}"),
    );
    gate(
        &mut gates,
        "disposable_program_id_differs_from_canonical_code_id",
        disposable_program_id_is_distinct(deploy_pubkey, canonical_code_program_id),
        format!(
            "disposable_program_id={deploy_pubkey:?}, canonical_code_program_id={canonical_code_program_id}"
        ),
    );
    let expected_programdata_address = deploy_pubkey
        .as_ref()
        .map(bpf_loader_upgradeable::get_program_data_address);
    let expected_nullifier = deploy_pubkey
        .as_ref()
        .zip(certified_statement.as_ref())
        .map(|(program_id, statement)| atomic_nullifier_address(program_id, &statement.nullifier));
    gate(
        &mut gates,
        "certified_pool_and_runtime_program_nullifier_addresses_derived",
        certified_statement.is_some() && expected_nullifier.is_some(),
        format!(
            "certified_pool_address={:?}, disposable_program_id={deploy_pubkey:?}, expected_nullifier_address={:?}, expected_nullifier_bump={:?}",
            certified_statement.as_ref().map(|statement| statement.pool_address),
            expected_nullifier.map(|(address, _)| address),
            expected_nullifier.map(|(_, bump)| bump),
        ),
    );

    let payer_pubkey = env::var_os("ASPIS_SPEND_MAINNET_PAYER_KEYPAIR")
        .and_then(|path| public_key_from_private_file(Path::new(&path)).ok());
    gate(
        &mut gates,
        "payer_keypair_secure_and_readable",
        payer_pubkey.is_some(),
        format!("payer_pubkey={payer_pubkey:?}"),
    );

    let upgrade_policy = env::var("ASPIS_SPEND_UPGRADE_POLICY").ok();
    let expected_upgrade_authority = if upgrade_policy.as_deref() == Some("keypair") {
        env::var_os("ASPIS_SPEND_MAINNET_UPGRADE_AUTHORITY_KEYPAIR")
            .and_then(|path| public_key_from_private_file(Path::new(&path)).ok())
    } else {
        None
    };
    let upgrade_policy_valid = match upgrade_policy.as_deref() {
        Some("keypair") => {
            expected_upgrade_authority.is_some()
                && expected_upgrade_authority != payer_pubkey
                && env::var("ASPIS_SPEND_ACCEPT_SINGLE_KEY_UPGRADE_RISK").as_deref()
                    == Ok("I_ACCEPT_THE_EXPLICIT_UPGRADE_AUTHORITY_RISK")
        }
        _ => false,
    };
    gate(
        &mut gates,
        "explicit_upgrade_authority_policy",
        upgrade_policy_valid,
        format!(
            "policy={upgrade_policy:?}, expected_authority={expected_upgrade_authority:?}, distinct_from_payer={}",
            expected_upgrade_authority.is_some() && expected_upgrade_authority != payer_pubkey
        ),
    );
    let signer_roles_distinct = deploy_pubkey.is_some()
        && deploy_pubkey != payer_pubkey
        && deploy_pubkey != expected_upgrade_authority
        && payer_pubkey.is_some()
        && expected_upgrade_authority.is_some()
        && payer_pubkey != expected_upgrade_authority;
    gate(
        &mut gates,
        "program_payer_and_upgrade_authority_roles_distinct",
        signer_roles_distinct,
        format!(
            "program={deploy_pubkey:?}, payer={payer_pubkey:?}, upgrade_authority={expected_upgrade_authority:?}"
        ),
    );

    let rpc_endpoint = env::var("ASPIS_SPEND_MAINNET_RPC_URL").ok();
    let rpc_origin = rpc_endpoint
        .as_deref()
        .and_then(|endpoint| rpc_policy(endpoint).ok());
    gate(
        &mut gates,
        "approved_mainnet_https_rpc_transport",
        rpc_origin.is_some(),
        format!("redacted_origin={rpc_origin:?}"),
    );

    let rpc = rpc_endpoint
        .as_ref()
        .filter(|_| rpc_origin.is_some())
        .and_then(|endpoint| Rpc::new(endpoint.clone()).ok());
    let observed_genesis = rpc
        .as_ref()
        .and_then(|rpc| rpc.call("getGenesisHash", json!([])).ok())
        .and_then(|value| value.as_str().map(ToOwned::to_owned));
    gate(
        &mut gates,
        "mainnet_beta_genesis_hash",
        observed_genesis.as_deref() == Some(MAINNET_BETA_GENESIS_HASH),
        format!("observed={observed_genesis:?}, expected={MAINNET_BETA_GENESIS_HASH}"),
    );

    let fresh_address_snapshot = match (
        rpc.as_ref(),
        deploy_pubkey,
        expected_programdata_address,
        certified_statement
            .as_ref()
            .map(|statement| statement.pool_address),
        expected_nullifier.map(|(address, _)| address),
    ) {
        (Some(rpc), Some(program), Some(programdata), Some(pool), Some(nullifier)) => {
            Some(rpc.accounts_exist_finalized(&[program, programdata, pool, nullifier]))
        }
        _ => None,
    };
    let program_already_deployed = fresh_address_snapshot
        .as_ref()
        .and_then(|result| result.as_ref().ok())
        .and_then(|snapshot| snapshot.exists.first().copied());
    let fresh_address_snapshot_context_slot = fresh_address_snapshot
        .as_ref()
        .and_then(|result| result.as_ref().ok())
        .map(|snapshot| snapshot.context_slot);
    let fresh_runtime_addresses_absent = fresh_address_snapshot
        .as_ref()
        .and_then(|result| result.as_ref().ok())
        .is_some_and(|snapshot| snapshot.exists == [false, false, false, false]);
    gate(
        &mut gates,
        "fresh_program_programdata_pool_and_nullifier_absent_at_one_finalized_snapshot",
        fresh_runtime_addresses_absent,
        format!(
            "context_slot={fresh_address_snapshot_context_slot:?}, ordered_addresses=[program={deploy_pubkey:?}, programdata={expected_programdata_address:?}, pool={:?}, nullifier={:?}], exists={:?}, error={:?}",
            certified_statement.as_ref().map(|statement| statement.pool_address),
            expected_nullifier.map(|(address, _)| address),
            fresh_address_snapshot
                .as_ref()
                .and_then(|result| result.as_ref().ok())
                .map(|snapshot| snapshot.exists.as_slice()),
            fresh_address_snapshot
                .as_ref()
                .and_then(|result| result.as_ref().err())
                .map(ToString::to_string),
        ),
    );

    gate(
        &mut gates,
        "fresh_deploy_upgrade_authority_is_precommitted",
        fresh_runtime_addresses_absent && upgrade_policy_valid,
        format!(
            "all_runtime_addresses_absent={fresh_runtime_addresses_absent}, expected_upgrade_authority={expected_upgrade_authority:?}"
        ),
    );

    let quote_result =
        if env::var("ASPIS_SPEND_FETCH_SOL_USD_QUOTE").as_deref() == Ok(SOL_USD_QUOTE_ACK) {
            fetch_sol_usd_quote()
        } else {
            Err(anyhow!("missing exact pinned-price-fetch acknowledgement"))
        };
    let (quote, quote_error) = match quote_result {
        Ok(quote) => (Some(quote), None),
        Err(error) => (None, Some(error.to_string())),
    };
    let quote_age_seconds = quote
        .as_ref()
        .map(|quote| quote.quoted_at_utc.as_str())
        .as_deref()
        .and_then(|value| chrono::DateTime::parse_from_rfc3339(value).ok())
        .map(|quoted_at| {
            chrono::Utc::now()
                .signed_duration_since(quoted_at)
                .num_seconds()
        });
    let price_quote_fresh = quote.is_some()
        && quote_age_seconds
            .is_some_and(|age| (-300..=SOL_USD_QUOTE_MAX_AGE_SECONDS).contains(&age));
    gate(
        &mut gates,
        "fresh_sol_usd_quote_for_20_usd_cap",
        price_quote_fresh,
        format!(
            "source={SOL_USD_TICKER_URL}, observed_microdollars={:?}, safety_adjusted_microdollars={:?}, quoted_at={:?}, response_sha256={:?}, age_seconds={quote_age_seconds:?}, max_age_seconds={SOL_USD_QUOTE_MAX_AGE_SECONDS}, fetch_error={quote_error:?}",
            quote.as_ref().map(|quote| quote.observed_microdollars),
            quote.as_ref().map(|quote| quote.cap_microdollars),
            quote.as_ref().map(|quote| quote.quoted_at_utc.as_str()),
            quote.as_ref().map(|quote| quote.response_sha256.as_str()),
        ),
    );

    let fee_reserve_lamports = MAX_TRANSACTION_FEES_LAMPORTS;
    let mut rent_budget = RentBudget {
        fee_reserve_lamports,
        forward_fee_budget_lamports: FORWARD_FEE_BUDGET_LAMPORTS,
        cleanup_fee_reserve_lamports: CLEANUP_FEE_RESERVE_LAMPORTS,
        cleanup_resource_count: CLEANUP_RESOURCE_COUNT,
        max_cleanup_transaction_fee_lamports: MAX_CLEANUP_TRANSACTION_FEE_LAMPORTS,
        sol_usd_observed_microdollars: quote.as_ref().map(|quote| quote.observed_microdollars),
        sol_usd_cap_microdollars: quote.as_ref().map(|quote| quote.cap_microdollars),
        sol_usd_quoted_at_utc: quote.as_ref().map(|quote| quote.quoted_at_utc.clone()),
        sol_usd_fetched_at_utc: quote.as_ref().map(|quote| quote.fetched_at_utc.clone()),
        sol_usd_quote_response_sha256: quote.as_ref().map(|quote| quote.response_sha256.clone()),
        sol_usd_quote_source: SOL_USD_TICKER_URL,
        sol_usd_quote_safety_bps: SOL_USD_QUOTE_SAFETY_BPS,
        sol_usd_quote_error: quote_error,
        max_demo_cost_usd_cents: MAX_DEMO_COST_USD_CENTS,
        max_nonrefundable_lamports_at_quote: quote
            .as_ref()
            .map(|quote| quote.cap_microdollars)
            .and_then(|price| usd_cent_cap_lamports(MAX_DEMO_COST_USD_CENTS, price)),
        ..RentBudget::default()
    };
    if let (Some(rpc), Some(_sbf), Some(proof), Some(payer), Some(max_len)) = (
        rpc.as_ref(),
        sbf_local.as_ref(),
        proof_local.as_ref(),
        payer_pubkey,
        program_max_len,
    ) {
        rent_budget.program_buffer_lamports = rpc
            .rent_exempt(BUFFER_METADATA_BYTES.saturating_add(max_len))
            .ok();
        rent_budget.programdata_lamports = rpc
            .rent_exempt(PROGRAMDATA_METADATA_BYTES.saturating_add(max_len))
            .ok();
        rent_budget.program_account_lamports = rpc.rent_exempt(PROGRAM_ACCOUNT_BYTES).ok();
        rent_budget.pool_account_lamports = rpc.rent_exempt(ATOMIC_POOL_STATE_LEN).ok();
        rent_budget.proof_account_lamports = rpc
            .rent_exempt(PROOF_ACCOUNT_HEADER_LEN.saturating_add(proof.len()))
            .ok();
        rent_budget.replay_probe_account_lamports = rpc
            .rent_exempt(PROOF_ACCOUNT_HEADER_LEN.saturating_add(REPLAY_PROBE_PROOF_BYTES))
            .ok();
        rent_budget.nullifier_account_lamports = rpc.rent_exempt(ATOMIC_NULLIFIER_MARKER_LEN).ok();
        rent_budget.payer_balance_lamports = rpc.balance_finalized(&payer).ok();
        let setup_accounts = rent_budget
            .pool_account_lamports
            .and_then(|pool| {
                rent_budget
                    .proof_account_lamports
                    .and_then(|proof| pool.checked_add(proof))
            })
            .and_then(|sum| {
                rent_budget
                    .nullifier_account_lamports
                    .and_then(|marker| sum.checked_add(marker))
            })
            .and_then(|sum| {
                rent_budget
                    .replay_probe_account_lamports
                    .and_then(|probe| sum.checked_add(probe))
            });
        let fresh_deploy_peak = rent_budget
            .program_buffer_lamports
            .zip(rent_budget.programdata_lamports)
            // Loader-v3 drains the buffer to the payer before creating
            // ProgramData, so the same lamports fund both accounts in turn.
            .map(|(buffer, programdata)| buffer.max(programdata))
            .and_then(|sum| {
                rent_budget
                    .program_account_lamports
                    .and_then(|program| sum.checked_add(program))
            })
            .and_then(|sum| setup_accounts.and_then(|setup| sum.checked_add(setup)))
            .and_then(|sum| sum.checked_add(fee_reserve_lamports));
        rent_budget.conservative_fresh_deploy_peak_lamports = fresh_deploy_peak;
        rent_budget.refundable_after_success_lamports = rent_budget
            .programdata_lamports
            .and_then(|programdata| {
                rent_budget
                    .proof_account_lamports
                    .and_then(|proof| programdata.checked_add(proof))
            })
            .and_then(|sum| {
                rent_budget
                    .replay_probe_account_lamports
                    .and_then(|probe| sum.checked_add(probe))
            });
        rent_budget.projected_nonrefundable_lamports = rent_budget
            .program_account_lamports
            .and_then(|program| {
                rent_budget
                    .pool_account_lamports
                    .and_then(|pool| program.checked_add(pool))
            })
            .and_then(|sum| {
                rent_budget
                    .nullifier_account_lamports
                    .and_then(|marker| sum.checked_add(marker))
            })
            .and_then(|sum| sum.checked_add(fee_reserve_lamports));
        rent_budget.projected_nonrefundable_usd_cents_at_quote = rent_budget
            .projected_nonrefundable_lamports
            .zip(rent_budget.sol_usd_cap_microdollars)
            .and_then(|(lamports, price)| lamports_to_usd_cents_ceiling(lamports, price));
        rent_budget.required_from_current_state_lamports = fresh_deploy_peak;
        rent_budget.surplus_lamports = rent_budget
            .payer_balance_lamports
            .zip(rent_budget.required_from_current_state_lamports)
            .map(|(balance, required)| i128::from(balance) - i128::from(required));
    }
    let funding_ready = rent_budget
        .surplus_lamports
        .is_some_and(|surplus| surplus >= 0);
    gate(
        &mut gates,
        "payer_covers_conservative_rent_and_fee_budget",
        funding_ready,
        format!(
            "balance={:?}, required={:?}, surplus={:?}",
            rent_budget.payer_balance_lamports,
            rent_budget.required_from_current_state_lamports,
            rent_budget.surplus_lamports
        ),
    );

    let cost_cap_ready = price_quote_fresh
        && rent_budget
            .projected_nonrefundable_lamports
            .zip(rent_budget.max_nonrefundable_lamports_at_quote)
            .is_some_and(|(projected, maximum)| projected <= maximum);
    gate(
        &mut gates,
        "projected_nonrefundable_cost_at_or_below_20_usd",
        cost_cap_ready,
        format!(
            "projected_lamports={:?}, maximum_lamports={:?}, projected_usd_cents={:?}, maximum_usd_cents={}",
            rent_budget.projected_nonrefundable_lamports,
            rent_budget.max_nonrefundable_lamports_at_quote,
            rent_budget.projected_nonrefundable_usd_cents_at_quote,
            rent_budget.max_demo_cost_usd_cents,
        ),
    );

    let cleanup_reserve_ready = CLEANUP_FEE_RESERVE_LAMPORTS
        == CLEANUP_RESOURCE_COUNT.saturating_mul(MAX_CLEANUP_TRANSACTION_FEE_LAMPORTS)
        && FORWARD_FEE_BUDGET_LAMPORTS.checked_add(CLEANUP_FEE_RESERVE_LAMPORTS)
            == Some(MAX_TRANSACTION_FEES_LAMPORTS)
        && CLEANUP_FEE_RESERVE_LAMPORTS > 0;
    gate(
        &mut gates,
        "cleanup_fees_reserved_inside_fixed_fee_and_usd_caps",
        cleanup_reserve_ready && cost_cap_ready,
        format!(
            "forward_budget={FORWARD_FEE_BUDGET_LAMPORTS}, cleanup_resources={CLEANUP_RESOURCE_COUNT}, max_cleanup_fee_each={MAX_CLEANUP_TRANSACTION_FEE_LAMPORTS}, cleanup_reserve={CLEANUP_FEE_RESERVE_LAMPORTS}, aggregate_fee_ceiling={MAX_TRANSACTION_FEES_LAMPORTS}, cost_cap_ready={cost_cap_ready}"
        ),
    );

    gate(
        &mut gates,
        "top_level_executor_command_registered",
        true,
        "stage2-spend-mainnet-execute is registered; this proves command availability only and does not attest per-wire journaling, restart reconciliation, live fee enforcement, cleanup-only transitions, or any execution",
    );

    let required_future_signing_safety_policy = RequiredFutureSigningSafetyPolicy {
        implementation_status:
            "required_future_contract_not_implemented_by_the_current_top_level_executor",
        hard_demo_cost_usd_cents: MAX_DEMO_COST_USD_CENTS,
        aggregate_transaction_fee_ceiling_lamports: MAX_TRANSACTION_FEES_LAMPORTS,
        forward_fee_budget_lamports: FORWARD_FEE_BUDGET_LAMPORTS,
        cleanup_fee_reserve_lamports: CLEANUP_FEE_RESERVE_LAMPORTS,
        cleanup_resource_count: CLEANUP_RESOURCE_COUNT,
        max_cleanup_transaction_fee_lamports: MAX_CLEANUP_TRANSACTION_FEE_LAMPORTS,
        journal_must_be_hash_chained_and_fsynced_before_signing: true,
        signed_wire_must_be_journaled_before_submission: true,
        restart_must_reconcile_journal_before_signing: true,
        stale_quote_or_failed_forward_fee_gate_enters_cleanup_only_mode: true,
        cleanup_only_mode_is_irreversible_for_run: true,
        cleanup_only_mode_may_create_accounts_or_rent: false,
        cleanup_refund_destination_must_be_payer: true,
        forward_signing_requirements: vec![
            "fresh pinned SOL/USD quote",
            "all prior signatures reconciled at finalized commitment",
            "finalized fees plus maximum unsettled fees plus next maximum fee remain within the forward fee budget",
            "retained rent plus fees plus the untouched cleanup reserve remain within the 20 USD cap",
            "pending intent and every recoverable resource identity are hash-chained and fsynced before signing",
        ],
        cleanup_signing_requirements: vec![
            "the exact recoverable resource and authority are already present in the reconciled journal",
            "the transaction creates no account, funds no rent, advances no demo state, uses zero priority fee, and returns value only to the payer",
            "the message fee quote fits one remaining cleanup slot and the expected refund exceeds that maximum fee",
            "the pending cleanup decision is fsynced before signing and the signed wire is fsynced before submission",
        ],
        cleanup_only_allowlist: vec![
            "close loader-v3 deployment buffer to payer",
            "atomically tag62-finalize then tag64-close an initialized partial primary proof account to payer; the two instructions must share one transaction so no invalid sealed intermediate can commit",
            "close sealed primary proof account with tag64 to payer",
            "close sealed replay-probe proof account with tag64 to payer",
            "close loader-v3 ProgramData with retained upgrade authority to payer",
        ],
    };

    let blockers = add_blockers(&gates);
    let ready = blockers.is_empty();
    SpendMainnetReadiness {
        artifact: "spend_mainnet_beta_readiness",
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-spend-mainnet-readiness"
            .to_owned(),
        mode: "read_only",
        mutations_performed: false,
        read_only_preflight_green: ready,
        readiness_is_execution_attestation: false,
        current_executor_journal_scope: "hash-chained top-level run start, preflight, finalized-success checkpoint, and completion only; no per-wire persistence, resource lifecycle, restart reconciliation, live fee-ledger enforcement, or cleanup-only transition",
        expected_mainnet_genesis_hash: MAINNET_BETA_GENESIS_HASH,
        observed_genesis_hash: observed_genesis,
        rpc_origin_redacted: rpc_origin,
        program_id: deploy_pubkey.map(|key| key.to_string()),
        canonical_code_program_id: canonical_code_program_id.to_string(),
        expected_programdata_address: expected_programdata_address.map(|key| key.to_string()),
        expected_loader_program_id: bpf_loader_upgradeable::id().to_string(),
        certified_statement_path: certified_statement
            .as_ref()
            .map(|statement| statement.path.clone()),
        certified_statement_bytes: certified_statement
            .as_ref()
            .map(|statement| statement.bytes),
        certified_statement_sha256: certified_statement
            .as_ref()
            .map(|statement| statement.sha256.clone()),
        certified_pool_address: certified_statement
            .as_ref()
            .map(|statement| statement.pool_address.to_string()),
        certified_statement_nullifier_hex: certified_statement
            .as_ref()
            .map(|statement| lower_hex_32(&statement.nullifier)),
        expected_nullifier_address: expected_nullifier.map(|(address, _)| address.to_string()),
        expected_nullifier_bump: expected_nullifier.map(|(_, bump)| bump),
        fresh_address_snapshot_context_slot,
        payer_pubkey: payer_pubkey.map(|key| key.to_string()),
        deploy_keypair_pubkey: deploy_pubkey.map(|key| key.to_string()),
        upgrade_policy,
        observed_upgrade_authority: None,
        program_already_deployed,
        release_certificate_path: release_rel.to_owned(),
        release_certificate_sha256: release_sha,
        release_certificate_generated_at_utc: release
            .as_ref()
            .and_then(|value| value["generated_at_utc"].as_str())
            .map(ToOwned::to_owned),
        release_certificate_green: release_declares_green && all_release_gates_green,
        proof_path: proof_rel,
        proof_bytes: proof_local.as_ref().map(Vec::len),
        proof_sha256: proof_sha,
        sbf_path: sbf_rel,
        sbf_bytes: sbf_local.as_ref().map(Vec::len),
        sbf_sha256: sbf_sha,
        program_max_len,
        rent_budget,
        required_future_signing_safety_policy,
        gates,
        blockers,
        required_future_execution_sequence: vec![
            "derive the pool pubkey and nullifier bytes from the exact release-certified statement sidecar, then derive ProgramData and the canonical nullifier PDA for the selected runtime program id and require Program, ProgramData, pool, and nullifier addresses all absent in one finalized getMultipleAccounts snapshot",
            "select the retained pool keypair only if its pubkey equals the release-certified sidecar pool pubkey, preserving the sidecar's exact initial sequence and canonical anchor",
            "reuse the already certified Spend proof and sidecar bound to that exact disposable-demo pool statement; do not re-grind merely because the target cluster changes",
            "rerun the complete release suite against the exact reused proof and SBF, then freeze their hashes and the release-certificate hash",
            "create an exclusive 0600 recovery journal outside the repository; record the payer, authorities, disposable runtime program id, loader-derived ProgramData address, buffer/proof/replay identities as they become known, release hashes, and the untouched cleanup-fee reserve; hash-chain and fsync every entry",
            "on every start or restart, verify the journal hash chain, reconcile every known signature and resource at finalized commitment, and forbid replacement resources or forward signing until the recovered state is unambiguous",
            "before every forward signature, append and fsync a decision proving the quote is fresh, prior fees are finalized, unsettled maximum fees are counted, the next maximum fee fits the forward budget, the cleanup reserve remains untouched, and projected net cost stays at or below 20 USD",
            "if any forward quote, fee, journal, reconciliation, or cap predicate fails, durably enter cleanup-only mode; permit no new account, rent, deployment, or demo transition and sign only an allowlisted value-recovering cleanup to the payer within its reserved cleanup envelope; an initialized partial proof is recovered by tag62 plus tag64 in one atomic transaction",
            "deploy the exact frozen SBF under the disposable runtime program id with max-len equal to the exact SBF length, zero priority fee, one signing attempt, and every endpoint/signer/commitment explicit",
            "immediately verify the loader-derived ProgramData address, deployed bytes, BPFLoaderUpgradeable ownership, and dedicated upgrade authority against the disposable runtime program id required for post-demo rent recovery",
            "create and tag63-initialize the fresh pool account owned by the disposable runtime program id to the already frozen initial statement",
            "create, initialize, chunk-upload, byte-verify, and tag62-finalize the already frozen proof in an account owned by the disposable runtime program id",
            "simulate the sealed-proof mutation teeth now, while the finalized proof account still exists, and verify its exact image is unchanged",
            "take a coherent finalized account snapshot, derive the canonical nullifier PDA from the disposable runtime program id plus nullifier only, and classify its accepted prestate",
            "build and sign one fresh-blockhash transaction candidate, then simulate those exact signed bytes below 1,400,000 CU with no state change",
            "after signing any transaction, append its signature, message hash, wire hash, resource transition, fee envelope, and decision-journal head and fsync them before the first submission",
            "submit only the byte-identical simulated candidate; after its first send, only query its journaled signature or rebroadcast identical journaled bytes",
            "wait for finalized commitment, then reverify ProgramData continuity, exact transaction metadata, proof-account refund, pool sequence/anchor, nullifier marker bytes, and the program-log proof SHA-256 under domain aspis-proof-sha256-v1 equals the release proof SHA-256 in both simulation and finalized logs",
            "create and seal a minimal replay-probe proof account whose keypair is retained solely for the post-commit nullifier tooth and refund",
            "simulate a poststate-anchor spend through the sealed replay probe and require the exact nullifier-already-spent error before proof verification",
            "close the sealed replay probe with tag64 and reconcile its exact finalized refund",
            "write, hash, make immutable, and durably copy the pre-close evidence artifact containing every finalized fact available while ProgramData still exists",
            "close the ProgramData account to the payer with the retained upgrade authority",
            "wait for finalized commitment, then write a post-close receipt that commits to the pre-close artifact hash and reconciles the exact ProgramData refund, permanent Program-account rent, and every transaction fee",
            "independently reconcile both linked evidence stages at or after the close slot, refresh the pinned SOL/USD quote, and write an immutable final manifest proving the net cost remained at or below 20 USD",
        ],
        required_future_execution_evidence_fields: vec![
            "schema_version",
            "generated_at_utc",
            "source_commit",
            "network",
            "mainnet_genesis_hash",
            "finalized_at_utc",
            "program_id",
            "canonical_code_program_id",
            "disposable_program_id",
            "expected_programdata_address",
            "expected_loader_program_id",
            "primary_rpc.origin_redacted",
            "primary_rpc.genesis_hash",
            "primary_rpc.snapshot_context_slot",
            "independent_rpc.origin_redacted",
            "independent_rpc.genesis_hash",
            "setup_transactions[].purpose",
            "setup_transactions[].signature",
            "setup_transactions[].finalized_slot",
            "setup_transactions[].fee_lamports",
            "setup_transactions[].payer_pre_lamports",
            "setup_transactions[].payer_post_lamports",
            "cleanup_transactions[].purpose",
            "cleanup_transactions[].signature",
            "cleanup_transactions[].finalized_slot",
            "cleanup_transactions[].fee_lamports",
            "cleanup_transactions[].payer_pre_lamports",
            "cleanup_transactions[].payer_post_lamports",
            "recovery_journal.schema_version",
            "recovery_journal.file_mode",
            "recovery_journal.exclusive_lock_acquired",
            "recovery_journal.hash_chain_valid",
            "recovery_journal.head_sha256",
            "recovery_journal.last_fsynced_sequence",
            "recovery_journal.restart_reconciled_at_finalized_commitment",
            "recovery_journal.cleanup_only_mode",
            "recovery_journal.cleanup_only_reason_or_null",
            "recovery_journal.cleanup_only_entered_sequence_or_null",
            "recovery_journal.cleanup_only_irreversible_for_run",
            "recovery_journal.required_resource_kinds",
            "recovery_journal.all_known_recoverable_resources_journaled",
            "recovery_journal.resources[].kind",
            "recovery_journal.resources[].address",
            "recovery_journal.resources[].authority",
            "recovery_journal.resources[].refund_destination",
            "recovery_journal.resources[].creation_signature_or_null",
            "recovery_journal.resources[].creation_wire_sha256_or_null",
            "recovery_journal.resources[].last_finalized_slot_or_null",
            "recovery_journal.resources[].observed_lamports_or_null",
            "recovery_journal.resources[].lifecycle_state",
            "recovery_journal.resources[].close_signature_or_null",
            "recovery_journal.resources[].refund_lamports_or_null",
            "signing_decisions[].sequence",
            "signing_decisions[].action",
            "signing_decisions[].action_class",
            "signing_decisions[].journal_head_before_sha256",
            "signing_decisions[].quote_response_sha256_or_null",
            "signing_decisions[].quote_age_seconds_or_null",
            "signing_decisions[].quote_fresh",
            "signing_decisions[].finalized_fees_lamports",
            "signing_decisions[].maximum_unsettled_fees_lamports",
            "signing_decisions[].maximum_next_fee_lamports",
            "signing_decisions[].forward_fee_budget_lamports",
            "signing_decisions[].cleanup_reserve_required_lamports",
            "signing_decisions[].cleanup_reserve_remaining_lamports",
            "signing_decisions[].expected_cleanup_refund_lamports_or_null",
            "signing_decisions[].cleanup_action_allowlisted",
            "signing_decisions[].cleanup_is_strictly_value_recovering",
            "signing_decisions[].creates_account_or_funds_rent",
            "signing_decisions[].projected_nonrefundable_lamports",
            "signing_decisions[].projected_nonrefundable_usd_cents_or_null",
            "signing_decisions[].fee_gate_passed",
            "signing_decisions[].usd_gate_passed",
            "signing_decisions[].decision",
            "signing_decisions[].decision_entry_fsynced_before_signing",
            "signing_decisions[].signature_or_null",
            "signing_decisions[].message_sha256_or_null",
            "signing_decisions[].wire_sha256_or_null",
            "signing_decisions[].signed_entry_fsynced_before_submission",
            "deployment.programdata_address",
            "deployment.program_id",
            "deployment.canonical_code_program_id",
            "deployment.expected_programdata_address",
            "deployment.programdata_address_matches_runtime_derivation",
            "deployment.program_account_owner",
            "deployment.programdata_owner",
            "deployment.loader_program_id",
            "deployment.programdata_max_len",
            "deployment.programdata_raw_sha256",
            "deployment.deployed_code_bytes",
            "deployment.deployed_code_sha256",
            "deployment.upgrade_authority",
            "deployment.deploy_signatures",
            "deployment.deploy_finalized_slots",
            "deployment.deploy_transactions[].signature",
            "deployment.deploy_transactions[].finalized_slot",
            "deployment.deploy_transactions[].fee_lamports",
            "deployment.deploy_transactions[].payer_pre_lamports",
            "deployment.deploy_transactions[].payer_post_lamports",
            "deployment.close_signature",
            "deployment.close_finalized_slot",
            "deployment.close_fee_lamports",
            "deployment.close_payer_pre_lamports",
            "deployment.close_payer_post_lamports",
            "deployment.programdata_refund_lamports",
            "deployment.program_account_unrecoverable_lamports",
            "release.certificate_sha256",
            "release.proof_sidecar_sha256",
            "release.proof_sha256",
            "release.proof_bytes",
            "release.sbf_sha256",
            "proof_account.address",
            "proof_account.owner",
            "proof_account.owner_matches_disposable_program_id",
            "proof_account.executable",
            "proof_account.data_len",
            "proof_account.raw_data_sha256",
            "proof_account.header_magic_hex",
            "proof_account.declared_proof_len",
            "proof_account.authority_is_zero",
            "proof_account.payload_sha256",
            "transaction.signature",
            "transaction.version",
            "transaction.fee_payer",
            "transaction.recent_blockhash",
            "transaction.last_valid_block_height",
            "transaction.message_sha256",
            "transaction.wire_sha256",
            "transaction.simulated_wire_sha256",
            "transaction.submitted_wire_sha256",
            "transaction.simulated_and_submitted_wire_identical",
            "transaction.simulation_context_slot",
            "transaction.simulation_err",
            "transaction.simulation_units_consumed",
            "transaction.simulation_logs_sha256",
            "transaction.proof_sha256_log.domain",
            "transaction.proof_sha256_log.simulation_value",
            "transaction.proof_sha256_log.finalized_value",
            "transaction.proof_sha256_log.simulation_matches_release",
            "transaction.proof_sha256_log.finalized_matches_release",
            "transaction.proof_sha256_log.simulation_and_finalized_match",
            "transaction.attempt_ledger",
            "transaction.compute_unit_limit",
            "transaction.heap_frame_bytes",
            "transaction.compute_unit_price_micro_lamports",
            "transaction.top_level_instructions",
            "transaction.tag65_accounts",
            "transaction.observed_inner_cpi_path",
            "transaction.meta_err",
            "transaction.fee_lamports",
            "transaction.compute_units_consumed",
            "transaction.slot",
            "transaction.block_time",
            "transaction.proof_refund_lamports",
            "replay_probe.address",
            "replay_probe.owner",
            "replay_probe.owner_matches_disposable_program_id",
            "replay_probe.rent_lamports",
            "replay_probe.raw_sha256_before_close",
            "replay_probe.close_signature",
            "replay_probe.close_finalized_slot",
            "replay_probe.close_fee_lamports",
            "replay_probe.refund_lamports",
            "replay_probe.absent_after_close",
            "pool.address",
            "pool.owner",
            "pool.owner_matches_disposable_program_id",
            "pool.data_len",
            "pool.before_raw_sha256",
            "pool.after_raw_sha256",
            "pool.sequence_before",
            "pool.sequence_after",
            "pool.anchor_before",
            "pool.anchor_after",
            "nullifier.address",
            "nullifier.bump",
            "nullifier.derivation_program_id",
            "nullifier.pda_matches_disposable_program_id_derivation",
            "nullifier.prestate_kind",
            "nullifier.prestate_owner",
            "nullifier.prestate_lamports",
            "nullifier.prestate_data_len",
            "nullifier.prestate_raw_sha256",
            "nullifier.after_owner",
            "nullifier.after_data_len",
            "nullifier.after_raw_sha256",
            "nullifier.after_magic_hex",
            "nullifier.after_version",
            "nullifier.after_pool",
            "nullifier.after_value",
            "negative_simulations.duplicate_spend.message_sha256",
            "negative_simulations.duplicate_spend.wire_sha256",
            "negative_simulations.duplicate_spend.context_slot",
            "negative_simulations.duplicate_spend.exact_error",
            "negative_simulations.duplicate_spend.logs_sha256",
            "negative_simulations.duplicate_spend.state_unchanged",
            "negative_simulations.duplicate_spend.pool_raw_sha256_before",
            "negative_simulations.duplicate_spend.pool_raw_sha256_after",
            "negative_simulations.duplicate_spend.nullifier_raw_sha256_before",
            "negative_simulations.duplicate_spend.nullifier_raw_sha256_after",
            "negative_simulations.duplicate_spend.replay_probe_raw_sha256_before",
            "negative_simulations.duplicate_spend.replay_probe_raw_sha256_after",
            "negative_simulations.sealed_init_proof.message_sha256",
            "negative_simulations.sealed_init_proof.wire_sha256",
            "negative_simulations.sealed_init_proof.context_slot",
            "negative_simulations.sealed_init_proof.exact_error",
            "negative_simulations.sealed_init_proof.logs_sha256",
            "negative_simulations.sealed_upload_chunk.message_sha256",
            "negative_simulations.sealed_upload_chunk.wire_sha256",
            "negative_simulations.sealed_upload_chunk.context_slot",
            "negative_simulations.sealed_upload_chunk.exact_error",
            "negative_simulations.sealed_upload_chunk.logs_sha256",
            "negative_simulations.sealed_finalize_proof.message_sha256",
            "negative_simulations.sealed_finalize_proof.wire_sha256",
            "negative_simulations.sealed_finalize_proof.context_slot",
            "negative_simulations.sealed_finalize_proof.exact_error",
            "negative_simulations.sealed_finalize_proof.logs_sha256",
            "negative_simulations.proof_raw_sha256_before",
            "negative_simulations.proof_raw_sha256_after",
            "independent_reconciliation.checked_at_utc",
            "independent_reconciliation.provider_origin_redacted",
            "independent_reconciliation.context_slot",
            "independent_reconciliation.at_or_after_transaction_slot",
            "independent_reconciliation.at_or_after_program_close_slot",
            "independent_reconciliation.all_predicates_match",
            "evidence.preclose_artifact_sha256",
            "evidence.preclose_artifact_immutable",
            "evidence.postclose_receipt.preclose_artifact_sha256",
            "evidence.postclose_receipt.sha256",
            "evidence.postclose_receipt.immutable",
            "evidence.final_manifest.preclose_artifact_sha256",
            "evidence.final_manifest.postclose_receipt_sha256",
            "evidence.final_manifest.immutable",
            "fee_ledger.submitted_transactions[].purpose",
            "fee_ledger.submitted_transactions[].signature",
            "fee_ledger.submitted_transactions[].finalized_slot",
            "fee_ledger.submitted_transactions[].meta_err",
            "fee_ledger.submitted_transactions[].fee_lamports",
            "fee_ledger.submitted_transactions[].payer_pre_lamports",
            "fee_ledger.submitted_transactions[].payer_post_lamports",
            "fee_ledger.submitted_transactions[].balance_delta_reconciled",
            "fee_ledger.aggregate_transaction_fees_lamports",
            "fee_ledger.maximum_unsettled_fees_lamports",
            "fee_ledger.fixed_fee_ceiling_lamports",
            "fee_ledger.forward_fee_budget_lamports",
            "fee_ledger.cleanup_fee_reserve_initial_lamports",
            "fee_ledger.cleanup_fee_reserve_remaining_lamports",
            "fee_ledger.cleanup_resource_slots_remaining",
            "fee_ledger.fee_ceiling_never_exceeded",
            "cost.sol_usd_observed_microdollars",
            "cost.sol_usd_cap_microdollars",
            "cost.sol_usd_quoted_at_utc",
            "cost.sol_usd_fetched_at_utc",
            "cost.sol_usd_quote_source",
            "cost.sol_usd_quote_response_sha256",
            "cost.sol_usd_quote_safety_bps",
            "cost.payer_pre_lamports",
            "cost.payer_post_lamports",
            "cost.aggregate_transaction_fees_lamports",
            "cost.refunded_programdata_lamports",
            "cost.refunded_proof_lamports",
            "cost.refunded_replay_probe_lamports",
            "cost.retained_program_account_lamports",
            "cost.retained_pool_lamports",
            "cost.retained_nullifier_lamports",
            "cost.balance_equation_reconciled",
            "cost.fee_ceiling_lamports",
            "cost.fee_ceiling_not_exceeded",
            "cost.cleanup_fee_reserve_was_precommitted",
            "cost.cleanup_fees_lamports",
            "cost.nonrefundable_lamports",
            "cost.nonrefundable_usd_cents",
            "cost.at_or_below_20_usd",
            "explorer_url",
        ],
        explicit_nonclaims: vec![
            "This readiness command never signs or submits a transaction.",
            "No mainnet-beta signature exists merely because readiness passes.",
            "This readiness result is a read-only preflight report, not an execution attestation.",
            "The required_future_signing_safety_policy, required_future_execution_sequence, and required_future_execution_evidence_fields describe a target executor contract; the current top-level executor does not implement or attest the per-wire, restart-reconciliation, live fee-ledger, resource-lifecycle, or cleanup-only controls in that contract.",
            "The current executor limits its journal to a hash-chained run start and read-only preflight, plus a finalized-success checkpoint and completed outcome on success; it is not durable per-wire recovery.",
            "Proof-account creation/upload/finalization and pool initialization are prior setup transactions, not part of the one-transaction verification/state-transition claim.",
            "A simulation result is not a finalized mainnet-beta execution result.",
            "The readiness command's single finalized getMultipleAccounts preflight snapshot is advisory and does not replace the live executor's immediately pre-signing coherent-slot snapshot.",
            "A primary-provider result does not constitute the required independent-provider reconciliation.",
            "The certified fixture-bound proof is eligible only for the disposable demo when its exact retained pool keypair is used and the pool account and nullifier PDA are absent on mainnet before setup.",
        ],
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;

    static ENVIRONMENT_LOCK: Mutex<()> = Mutex::new(());

    #[test]
    fn twenty_usd_cap_uses_integer_rounding_that_never_overstates_budget() {
        let price = 77_970_000;
        assert_eq!(
            usd_cent_cap_lamports(MAX_DEMO_COST_USD_CENTS, price),
            Some(256_508_913)
        );
        assert_eq!(lamports_to_usd_cents_ceiling(53_758_400, price), Some(420));
        assert_eq!(usd_cent_cap_lamports(2_000, 0), None);
        assert_eq!(lamports_to_usd_cents_ceiling(1, 0), None);
    }

    #[test]
    fn cleanup_reserve_is_precommitted_inside_the_fee_ceiling() {
        assert_eq!(REPLAY_PROBE_PROOF_BYTES, 1);
        assert_eq!(
            PROOF_ACCOUNT_HEADER_LEN.saturating_add(REPLAY_PROBE_PROOF_BYTES),
            PROOF_ACCOUNT_HEADER_LEN + 1
        );
        assert_eq!(CLEANUP_RESOURCE_COUNT, 4);
        assert_eq!(CLEANUP_FEE_RESERVE_LAMPORTS, 4_000_000);
        assert_eq!(FORWARD_FEE_BUDGET_LAMPORTS, 46_000_000);
        assert_eq!(
            FORWARD_FEE_BUDGET_LAMPORTS + CLEANUP_FEE_RESERVE_LAMPORTS,
            MAX_TRANSACTION_FEES_LAMPORTS
        );
    }

    #[test]
    fn disposable_runtime_id_cannot_reuse_the_canonical_code_id() {
        let canonical = aspis_verifier::id();
        let disposable = Pubkey::new_unique();
        assert!(!disposable_program_id_is_distinct(None, canonical));
        assert!(!disposable_program_id_is_distinct(
            Some(canonical),
            canonical
        ));
        assert!(disposable_program_id_is_distinct(
            Some(disposable),
            canonical
        ));
        assert_ne!(
            bpf_loader_upgradeable::get_program_data_address(&disposable),
            bpf_loader_upgradeable::get_program_data_address(&canonical)
        );
    }

    #[test]
    fn quote_decimal_conversion_rounds_price_up() {
        assert_eq!(
            decimal_usd_to_microdollars_ceiling("77.97"),
            Some(77_970_000)
        );
        assert_eq!(
            decimal_usd_to_microdollars_ceiling("77.9700001"),
            Some(77_970_001)
        );
        assert_eq!(decimal_usd_to_microdollars_ceiling("0"), None);
        assert_eq!(decimal_usd_to_microdollars_ceiling("-1"), None);
    }

    #[test]
    fn rpc_policy_rejects_public_and_local_endpoints() {
        let _guard = ENVIRONMENT_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        env::remove_var("ASPIS_SPEND_MAINNET_PUBLIC_RPC_DIRECT_TPU_ACK");
        assert!(rpc_policy("https://api.mainnet-beta.solana.com").is_err());
        assert!(rpc_policy("http://127.0.0.1:8899").is_err());
        assert!(rpc_policy("https://localhost/rpc").is_err());
    }

    #[test]
    fn rpc_policy_accepts_public_reads_only_with_direct_tpu_ack() {
        let _guard = ENVIRONMENT_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        env::set_var(
            "ASPIS_SPEND_MAINNET_PUBLIC_RPC_DIRECT_TPU_ACK",
            PUBLIC_RPC_DIRECT_TPU_ACK,
        );
        let redacted = rpc_policy("https://api.mainnet-beta.solana.com").unwrap();
        env::remove_var("ASPIS_SPEND_MAINNET_PUBLIC_RPC_DIRECT_TPU_ACK");
        assert_eq!(
            redacted,
            "https://api.mainnet-beta.solana.com/<public-read-rpc>"
        );
    }

    #[test]
    fn rpc_policy_never_returns_path_or_query() {
        let _guard = ENVIRONMENT_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        env::set_var("ASPIS_SPEND_MAINNET_RPC_IS_PRIVATE", PRIVATE_RPC_ACK);
        let redacted = rpc_policy("https://provider.example/secret-token?api-key=hunter2").unwrap();
        env::remove_var("ASPIS_SPEND_MAINNET_RPC_IS_PRIVATE");
        assert_eq!(redacted, "https://provider.example/<redacted>");
        assert!(!redacted.contains("secret"));
        assert!(!redacted.contains("hunter2"));
    }

    #[test]
    fn certified_statement_derives_pool_and_nullifier_and_rejects_release_disagreement() {
        let root = env::temp_dir().join(format!(
            "aspis-spend-mainnet-statement-{}-{}",
            std::process::id(),
            Pubkey::new_unique()
        ));
        fs::create_dir(&root).unwrap();
        let pool = [7u8; 32];
        let nullifier = [9u8; 32];
        let statement = serde_json::to_vec(&json!({
            "artifact": "profile23_production_statement",
            "pool_hex": lower_hex_32(&pool),
            "nullifier_hex": lower_hex_32(&nullifier),
            "sequence": 3,
        }))
        .unwrap();
        fs::write(root.join("statement.json"), &statement).unwrap();
        let statement_sha = sha256(&statement);
        let mut release = json!({
            "release_instance": {
                "statement_path": "statement.json",
                "statement_bytes": statement.len(),
                "statement_sha256": statement_sha,
                "statement_pool_hex": lower_hex_32(&pool),
                "statement_sequence": 3,
            },
            "source_artifacts": [{
                "label": "production_statement",
                "path": "statement.json",
                "bytes": statement.len(),
                "sha256": sha256(&statement),
            }],
        });

        let certified = certified_statement_from_release(&root, &release).unwrap();
        assert_eq!(certified.pool_address, Pubkey::new_from_array(pool));
        assert_eq!(certified.nullifier, nullifier);
        let first_program = Pubkey::new_unique();
        let second_program = Pubkey::new_unique();
        assert_ne!(
            atomic_nullifier_address(&first_program, &certified.nullifier),
            atomic_nullifier_address(&second_program, &certified.nullifier)
        );

        release["release_instance"]["statement_pool_hex"] = json!(lower_hex_32(&[8u8; 32]));
        assert!(certified_statement_from_release(&root, &release).is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn coherent_account_snapshot_parser_is_fail_closed() {
        let all_absent = parse_account_presence_snapshot(
            &json!({"context": {"slot": 42}, "value": [null, null, null, null]}),
            4,
        )
        .unwrap();
        assert_eq!(all_absent.context_slot, 42);
        assert_eq!(all_absent.exists, [false, false, false, false]);

        let one_present = parse_account_presence_snapshot(
            &json!({"context": {"slot": 43}, "value": [null, {}, null, null]}),
            4,
        )
        .unwrap();
        assert_eq!(one_present.exists, [false, true, false, false]);
        assert!(parse_account_presence_snapshot(
            &json!({"context": {"slot": 44}, "value": [null, null, null]}),
            4,
        )
        .is_err());
        assert!(parse_account_presence_snapshot(
            &json!({"context": {}, "value": [null, null, null, null]}),
            4,
        )
        .is_err());
    }

    #[test]
    fn readiness_rejects_execution_and_labels_future_contract_truthfully() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
        let summary = evaluate(root, &["--execute".to_owned()]);
        assert!(!summary.mutations_performed);
        assert!(!summary.read_only_preflight_green);
        assert!(!summary.readiness_is_execution_attestation);
        assert!(summary
            .current_executor_journal_scope
            .contains("no per-wire persistence"));
        assert_eq!(
            summary.canonical_code_program_id,
            aspis_verifier::id().to_string()
        );
        assert!(summary.blockers.iter().any(|name| name == "read_only_mode"));
        assert!(!summary
            .blockers
            .iter()
            .any(|name| name == "top_level_executor_command_registered"));
        assert!(summary
            .gates
            .iter()
            .any(|gate| gate.name == "top_level_executor_command_registered" && gate.passed));

        let release_freeze = summary
            .required_future_execution_sequence
            .iter()
            .position(|step| step.contains("freeze their hashes"))
            .unwrap();
        let deploy = summary
            .required_future_execution_sequence
            .iter()
            .position(|step| step.starts_with("deploy the exact frozen SBF"))
            .unwrap();
        assert!(release_freeze < deploy);
        let journal = summary
            .required_future_execution_sequence
            .iter()
            .position(|step| step.contains("recovery journal"))
            .unwrap();
        assert!(journal < deploy);
        assert!(summary
            .required_future_execution_sequence
            .iter()
            .any(|step| step.contains("program id plus nullifier only")));
        assert!(summary
            .required_future_execution_sequence
            .iter()
            .any(|step| step.contains("byte-identical simulated candidate")));
        let evidence = summary
            .required_future_execution_sequence
            .iter()
            .position(|step| step.contains("pre-close evidence artifact"))
            .unwrap();
        let close = summary
            .required_future_execution_sequence
            .iter()
            .position(|step| step.contains("close the ProgramData account"))
            .unwrap();
        assert!(evidence < close);
        assert!(summary
            .required_future_execution_evidence_fields
            .contains(&"transaction.simulated_and_submitted_wire_identical"));
        assert!(summary
            .required_future_execution_evidence_fields
            .contains(&"nullifier.prestate_kind"));
        assert!(summary
            .required_future_execution_evidence_fields
            .contains(&"negative_simulations.sealed_finalize_proof.exact_error"));
        assert!(summary
            .required_future_execution_evidence_fields
            .contains(&"independent_reconciliation.all_predicates_match"));
        assert!(summary
            .required_future_execution_evidence_fields
            .contains(&"deployment.programdata_refund_lamports"));
        assert!(summary
            .required_future_execution_evidence_fields
            .contains(&"fee_ledger.aggregate_transaction_fees_lamports"));
        assert!(summary
            .required_future_execution_evidence_fields
            .contains(&"evidence.postclose_receipt.preclose_artifact_sha256"));
        assert!(summary
            .required_future_execution_evidence_fields
            .contains(&"cost.balance_equation_reconciled"));
        assert!(summary
            .required_future_execution_evidence_fields
            .contains(&"cost.at_or_below_20_usd"));
        assert!(summary
            .required_future_execution_evidence_fields
            .contains(&"canonical_code_program_id"));
        assert!(summary
            .required_future_execution_evidence_fields
            .contains(&"deployment.programdata_address_matches_runtime_derivation"));
        assert!(summary
            .required_future_execution_evidence_fields
            .contains(&"recovery_journal.hash_chain_valid"));
        assert!(summary
            .required_future_execution_evidence_fields
            .contains(&"signing_decisions[].decision_entry_fsynced_before_signing"));
        assert!(summary
            .required_future_execution_evidence_fields
            .contains(&"transaction.proof_sha256_log.finalized_matches_release"));
        assert_eq!(
            summary
                .required_future_signing_safety_policy
                .cleanup_fee_reserve_lamports,
            CLEANUP_FEE_RESERVE_LAMPORTS
        );
        assert!(
            summary
                .required_future_signing_safety_policy
                .stale_quote_or_failed_forward_fee_gate_enters_cleanup_only_mode
        );
        assert!(
            summary
                .required_future_signing_safety_policy
                .cleanup_only_mode_is_irreversible_for_run
        );
        assert!(
            !summary
                .required_future_signing_safety_policy
                .cleanup_only_mode_may_create_accounts_or_rent
        );
        assert_eq!(
            summary
                .required_future_signing_safety_policy
                .implementation_status,
            "required_future_contract_not_implemented_by_the_current_top_level_executor"
        );
        assert!(summary.explicit_nonclaims.iter().any(
            |claim| claim.contains("read-only preflight report, not an execution attestation")
        ));
    }
}
