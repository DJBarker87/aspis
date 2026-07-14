//! Fail-closed, read-only readiness checks for the Profile23 mainnet-beta run.
//!
//! This module intentionally contains no transaction submission path.  The
//! production runbook describes the reviewed sequence that a future executor
//! must implement.  Keeping readiness read-only makes an accidental invocation
//! incapable of spending SOL or changing mainnet state.

use std::{
    env, fs,
    net::{IpAddr, Ipv4Addr},
    os::unix::fs::PermissionsExt,
    path::{Path, PathBuf},
    time::Duration,
};

use anyhow::{anyhow, Context, Result};
use base64::{engine::general_purpose::STANDARD as BASE64, Engine};
use serde::Serialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use solana_sdk::{
    bpf_loader_upgradeable::{self, UpgradeableLoaderState},
    pubkey::Pubkey,
    signature::{read_keypair_file, Signer},
};

use aspis_verifier::{
    atomic_payment::{ATOMIC_NULLIFIER_MARKER_LEN, ATOMIC_POOL_STATE_LEN},
    PROOF_ACCOUNT_HEADER_LEN,
};

const MAINNET_BETA_GENESIS_HASH: &str = "5eykt4UsFv8P8NJdTREpY1vzqKqZKvdpKuc147dw2dYd";
const CU_LIMIT: u64 = 1_400_000;
const BUFFER_METADATA_BYTES: usize = 37;
const PROGRAMDATA_METADATA_BYTES: usize = 45;
const PROGRAM_ACCOUNT_BYTES: usize = 36;
const DEFAULT_FEE_RESERVE_LAMPORTS: u64 = 100_000_000;
const PRIVATE_RPC_ACK: &str = "I_CONFIRM_THIS_IS_A_DEDICATED_PAID_MAINNET_RPC";

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
    pub nullifier_account_lamports: Option<u64>,
    pub fee_reserve_lamports: u64,
    /// Conservative peak balance for a fresh CLI deployment.  The buffer is
    /// included even though its rent is normally reclaimed after deployment.
    pub conservative_fresh_deploy_peak_lamports: Option<u64>,
    pub required_from_current_state_lamports: Option<u64>,
    pub payer_balance_lamports: Option<u64>,
    pub surplus_lamports: Option<i128>,
}

#[derive(Clone, Debug, Serialize)]
pub struct Profile23MainnetReadiness {
    pub artifact: &'static str,
    pub generated_at_utc: String,
    pub command: String,
    pub mode: &'static str,
    pub mutations_performed: bool,
    pub ready_for_reviewed_live_executor: bool,
    pub expected_mainnet_genesis_hash: &'static str,
    pub observed_genesis_hash: Option<String>,
    pub rpc_origin_redacted: Option<String>,
    pub program_id: String,
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
    pub rent_budget: RentBudget,
    pub gates: Vec<ReadinessGate>,
    pub blockers: Vec<String>,
    pub execution_sequence: Vec<&'static str>,
    pub evidence_schema_required_fields: Vec<&'static str>,
    pub explicit_nonclaims: Vec<&'static str>,
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

    fn account_finalized(&self, address: &Pubkey) -> Result<Option<RpcAccount>> {
        let result = self.call(
            "getAccountInfo",
            json!([address.to_string(), {"encoding": "base64", "commitment": "finalized"}]),
        )?;
        let value = &result["value"];
        if value.is_null() {
            return Ok(None);
        }
        let owner = value["owner"]
            .as_str()
            .context("account owner missing")?
            .parse()?;
        let executable = value["executable"]
            .as_bool()
            .context("account executable flag missing")?;
        let data = value["data"][0]
            .as_str()
            .context("base64 account data missing")?;
        Ok(Some(RpcAccount {
            owner,
            executable,
            data: BASE64.decode(data).context("invalid base64 account data")?,
        }))
    }
}

struct RpcAccount {
    owner: Pubkey,
    executable: bool,
    data: Vec<u8>,
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn workspace_path(root: &Path, path: &str) -> PathBuf {
    let path = PathBuf::from(path);
    if path.is_absolute() {
        path
    } else {
        root.join(path)
    }
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
        return Err(anyhow!("known public RPC endpoint is prohibited"));
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
    if env::var("ASPIS_PROFILE23_MAINNET_RPC_IS_PRIVATE").as_deref() != Ok(PRIVATE_RPC_ACK) {
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

fn parse_program_state(account: &RpcAccount) -> Result<Pubkey> {
    if account.owner != bpf_loader_upgradeable::id() || !account.executable {
        return Err(anyhow!(
            "program account is not executable under BPFLoaderUpgradeable"
        ));
    }
    match bincode::deserialize(&account.data).context("decode upgradeable program state")? {
        UpgradeableLoaderState::Program {
            programdata_address,
        } => Ok(programdata_address),
        _ => Err(anyhow!("declared program address is not a Program account")),
    }
}

fn parse_programdata_state(account: &RpcAccount) -> Result<(Option<Pubkey>, &[u8])> {
    if account.owner != bpf_loader_upgradeable::id() {
        return Err(anyhow!("ProgramData owner is not BPFLoaderUpgradeable"));
    }
    let state: UpgradeableLoaderState =
        bincode::deserialize(&account.data).context("decode ProgramData state")?;
    let UpgradeableLoaderState::ProgramData {
        upgrade_authority_address,
        ..
    } = state
    else {
        return Err(anyhow!("linked account is not ProgramData"));
    };
    let code = account
        .data
        .get(PROGRAMDATA_METADATA_BYTES..)
        .context("ProgramData is shorter than its metadata")?;
    Ok((upgrade_authority_address, code))
}

/// Executes only read-only filesystem and RPC calls.  `--execute` is parsed
/// solely to fail closed with an explicit, machine-readable blocker.
pub fn evaluate(workspace_root: &Path, arguments: &[String]) -> Profile23MainnetReadiness {
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
            "--execute requested, but the reviewed live executor is intentionally not implemented"
        } else {
            "no transaction construction, signing, submission, deployment, or account writes exist in this command"
        },
    );
    gate(
        &mut gates,
        "known_arguments_only",
        unknown_arguments.is_empty(),
        format!("unknown_argument_count={}", unknown_arguments.len()),
    );

    let release_rel = "results/stage2/profile23_one_transaction_release.json";
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
        .and_then(|value| value["max_literal_production_tag60_cu"].as_u64());
    gate(
        &mut gates,
        "release_certificate_under_1_4m_cu",
        release_cu.is_some_and(|cu| cu < CU_LIMIT),
        format!("tag60_cu={release_cu:?}, limit={CU_LIMIT}"),
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

    let program_id = aspis_verifier::id();
    let deploy_pubkey = env::var_os("ASPIS_PROFILE23_MAINNET_PROGRAM_KEYPAIR")
        .and_then(|path| public_key_from_private_file(Path::new(&path)).ok());
    gate(
        &mut gates,
        "deploy_keypair_matches_declared_program_id",
        deploy_pubkey == Some(program_id),
        format!("declared={program_id}, deploy_pubkey={deploy_pubkey:?}"),
    );

    let payer_pubkey = env::var_os("ASPIS_PROFILE23_MAINNET_PAYER_KEYPAIR")
        .and_then(|path| public_key_from_private_file(Path::new(&path)).ok());
    gate(
        &mut gates,
        "payer_keypair_secure_and_readable",
        payer_pubkey.is_some(),
        format!("payer_pubkey={payer_pubkey:?}"),
    );

    let upgrade_policy = env::var("ASPIS_PROFILE23_UPGRADE_POLICY").ok();
    let expected_upgrade_authority = if upgrade_policy.as_deref() == Some("keypair") {
        env::var_os("ASPIS_PROFILE23_MAINNET_UPGRADE_AUTHORITY_KEYPAIR")
            .and_then(|path| public_key_from_private_file(Path::new(&path)).ok())
    } else {
        None
    };
    let upgrade_policy_valid = match upgrade_policy.as_deref() {
        Some("immutable") => true,
        Some("keypair") => {
            expected_upgrade_authority.is_some()
                && env::var("ASPIS_PROFILE23_ACCEPT_SINGLE_KEY_UPGRADE_RISK").as_deref()
                    == Ok("I_ACCEPT_THE_EXPLICIT_UPGRADE_AUTHORITY_RISK")
        }
        _ => false,
    };
    gate(
        &mut gates,
        "explicit_upgrade_authority_policy",
        upgrade_policy_valid,
        format!("policy={upgrade_policy:?}, expected_authority={expected_upgrade_authority:?}"),
    );

    let rpc_endpoint = env::var("ASPIS_PROFILE23_MAINNET_RPC_URL").ok();
    let rpc_origin = rpc_endpoint
        .as_deref()
        .and_then(|endpoint| rpc_policy(endpoint).ok());
    gate(
        &mut gates,
        "dedicated_nonlocal_nonpublic_https_rpc",
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

    let program_account = rpc
        .as_ref()
        .and_then(|rpc| rpc.account_finalized(&program_id).ok());
    let program_already_deployed = program_account.as_ref().map(Option::is_some);
    let mut observed_upgrade_authority = None;
    let mut deployed_code_exact = false;
    let mut deployed_program_state_valid = false;
    if let (Some(rpc), Some(Some(program_account)), Some(local_sbf)) =
        (rpc.as_ref(), program_account.as_ref(), sbf_local.as_ref())
    {
        if let Ok(programdata_address) = parse_program_state(program_account) {
            if let Ok(Some(programdata)) = rpc.account_finalized(&programdata_address) {
                if let Ok((authority, deployed_code)) = parse_programdata_state(&programdata) {
                    observed_upgrade_authority = authority;
                    deployed_program_state_valid = true;
                    deployed_code_exact = deployed_code
                        .get(..local_sbf.len())
                        .is_some_and(|prefix| prefix == local_sbf)
                        && deployed_code
                            .get(local_sbf.len()..)
                            .is_some_and(|padding| padding.iter().all(|byte| *byte == 0));
                }
            }
        }
    }
    let program_state_ready = match program_already_deployed {
        Some(false) => true,
        Some(true) => deployed_program_state_valid && deployed_code_exact,
        None => false,
    };
    gate(
        &mut gates,
        "program_absent_or_exact_release_sbf_deployed",
        program_state_ready,
        format!(
            "already_deployed={program_already_deployed:?}, valid_upgradeable_state={deployed_program_state_valid}, exact_code={deployed_code_exact}"
        ),
    );

    let upgrade_state_ready = match (program_already_deployed, upgrade_policy.as_deref()) {
        (Some(false), Some("immutable")) => true,
        (Some(false), Some("keypair")) => expected_upgrade_authority.is_some(),
        (Some(true), Some("immutable")) => observed_upgrade_authority.is_none(),
        (Some(true), Some("keypair")) => observed_upgrade_authority == expected_upgrade_authority,
        _ => false,
    };
    gate(
        &mut gates,
        "onchain_upgrade_authority_matches_policy",
        upgrade_state_ready,
        format!(
            "already_deployed={program_already_deployed:?}, observed={observed_upgrade_authority:?}, expected={expected_upgrade_authority:?}"
        ),
    );

    let fee_reserve_lamports = env::var("ASPIS_PROFILE23_MAINNET_FEE_RESERVE_LAMPORTS")
        .ok()
        .and_then(|value| value.parse::<u64>().ok())
        .unwrap_or(DEFAULT_FEE_RESERVE_LAMPORTS);
    let mut rent_budget = RentBudget {
        fee_reserve_lamports,
        ..RentBudget::default()
    };
    if let (Some(rpc), Some(sbf), Some(proof), Some(payer)) = (
        rpc.as_ref(),
        sbf_local.as_ref(),
        proof_local.as_ref(),
        payer_pubkey,
    ) {
        rent_budget.program_buffer_lamports = rpc
            .rent_exempt(BUFFER_METADATA_BYTES.saturating_add(sbf.len()))
            .ok();
        rent_budget.programdata_lamports = rpc
            .rent_exempt(PROGRAMDATA_METADATA_BYTES.saturating_add(sbf.len()))
            .ok();
        rent_budget.program_account_lamports = rpc.rent_exempt(PROGRAM_ACCOUNT_BYTES).ok();
        rent_budget.pool_account_lamports = rpc.rent_exempt(ATOMIC_POOL_STATE_LEN).ok();
        rent_budget.proof_account_lamports = rpc
            .rent_exempt(PROOF_ACCOUNT_HEADER_LEN.saturating_add(proof.len()))
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
            });
        let fresh_deploy_peak = rent_budget
            .program_buffer_lamports
            .and_then(|buffer| {
                rent_budget
                    .programdata_lamports
                    .and_then(|programdata| buffer.checked_add(programdata))
            })
            .and_then(|sum| {
                rent_budget
                    .program_account_lamports
                    .and_then(|program| sum.checked_add(program))
            })
            .and_then(|sum| setup_accounts.and_then(|setup| sum.checked_add(setup)))
            .and_then(|sum| sum.checked_add(fee_reserve_lamports));
        rent_budget.conservative_fresh_deploy_peak_lamports = fresh_deploy_peak;
        rent_budget.required_from_current_state_lamports = match program_already_deployed {
            Some(true) => setup_accounts.and_then(|sum| sum.checked_add(fee_reserve_lamports)),
            Some(false) => fresh_deploy_peak,
            None => None,
        };
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

    gate(
        &mut gates,
        "reviewed_live_executor_available",
        false,
        "intentionally unimplemented: readiness cannot deploy, create accounts, upload proofs, simulate, or submit",
    );

    let blockers = add_blockers(&gates);
    let ready = blockers.is_empty();
    Profile23MainnetReadiness {
        artifact: "profile23_mainnet_beta_readiness",
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-profile23-mainnet-readiness"
            .to_owned(),
        mode: "read_only",
        mutations_performed: false,
        ready_for_reviewed_live_executor: ready,
        expected_mainnet_genesis_hash: MAINNET_BETA_GENESIS_HASH,
        observed_genesis_hash: observed_genesis,
        rpc_origin_redacted: rpc_origin,
        program_id: program_id.to_string(),
        payer_pubkey: payer_pubkey.map(|key| key.to_string()),
        deploy_keypair_pubkey: deploy_pubkey.map(|key| key.to_string()),
        upgrade_policy,
        observed_upgrade_authority: observed_upgrade_authority.map(|key| key.to_string()),
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
        rent_budget,
        gates,
        blockers,
        execution_sequence: vec![
            "select the real pool pubkey, initial sequence, canonical anchor, and matching witness offline before any mainnet mutation",
            "mine a fresh Profile23 proof and sidecar bound to that exact pool statement",
            "rerun the complete release suite against the exact proof and SBF, then freeze their hashes and the release-certificate hash",
            "deploy the exact frozen SBF under the declared program id with every CLI endpoint, signer, commitment, and max-len flag explicit",
            "verify deployed ProgramData bytes and irreversibly freeze or exactly verify the declared upgrade-authority policy",
            "create and tag63-initialize the fresh program-owned pool account to the already frozen initial statement",
            "create, initialize, chunk-upload, byte-verify, and tag62-finalize the already frozen proof in its proof account",
            "take a coherent finalized account snapshot, derive the canonical nullifier PDA from program id plus nullifier only, and classify its accepted prestate",
            "build and sign one fresh-blockhash transaction candidate, then simulate those exact signed bytes below 1,400,000 CU with no state change",
            "submit only the byte-identical simulated candidate; after its first send, only query its known signature or rebroadcast identical bytes",
            "wait for finalized commitment, then verify exact transaction metadata, pool sequence/anchor, and nullifier marker bytes",
            "simulate duplicate-spend and sealed-proof mutation teeth without submission or state change",
            "write the forensic evidence artifact and reconcile it from an independent mainnet-beta provider at or after the finalized slot",
        ],
        evidence_schema_required_fields: vec![
            "schema_version",
            "generated_at_utc",
            "source_commit",
            "network",
            "mainnet_genesis_hash",
            "finalized_at_utc",
            "program_id",
            "primary_rpc.origin_redacted",
            "primary_rpc.genesis_hash",
            "primary_rpc.snapshot_context_slot",
            "independent_rpc.origin_redacted",
            "independent_rpc.genesis_hash",
            "setup_transactions[].purpose",
            "setup_transactions[].signature",
            "setup_transactions[].finalized_slot",
            "deployment.programdata_address",
            "deployment.programdata_max_len",
            "deployment.programdata_raw_sha256",
            "deployment.deployed_code_bytes",
            "deployment.deployed_code_sha256",
            "deployment.upgrade_authority",
            "deployment.deploy_signatures",
            "deployment.deploy_finalized_slots",
            "deployment.freeze_signature",
            "deployment.freeze_finalized_slot",
            "release.certificate_sha256",
            "release.proof_sidecar_sha256",
            "release.proof_sha256",
            "release.proof_bytes",
            "release.sbf_sha256",
            "proof_account.address",
            "proof_account.owner",
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
            "transaction.attempt_ledger",
            "transaction.compute_unit_limit",
            "transaction.heap_frame_bytes",
            "transaction.compute_unit_price_micro_lamports",
            "transaction.top_level_instructions",
            "transaction.tag60_accounts",
            "transaction.observed_inner_cpi_path",
            "transaction.meta_err",
            "transaction.fee_lamports",
            "transaction.compute_units_consumed",
            "transaction.slot",
            "transaction.block_time",
            "pool.address",
            "pool.owner",
            "pool.data_len",
            "pool.before_raw_sha256",
            "pool.after_raw_sha256",
            "pool.sequence_before",
            "pool.sequence_after",
            "pool.anchor_before",
            "pool.anchor_after",
            "nullifier.address",
            "nullifier.bump",
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
            "negative_simulations.duplicate_spend.proof_raw_sha256_before",
            "negative_simulations.duplicate_spend.proof_raw_sha256_after",
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
            "independent_reconciliation.all_predicates_match",
            "explorer_url",
        ],
        explicit_nonclaims: vec![
            "This readiness command never signs or submits a transaction.",
            "No mainnet-beta signature exists merely because readiness passes.",
            "Proof-account creation/upload/finalization and pool initialization are prior setup transactions, not part of the one-transaction verification/state-transition claim.",
            "A simulation result is not a finalized mainnet-beta execution result.",
            "The readiness command's separate finalized RPC reads are advisory and do not constitute the live executor's required coherent-slot account snapshot.",
            "A primary-provider result does not constitute the required independent-provider reconciliation.",
            "The fixture-bound local proof is not eligible for mainnet; the real-pool proof must pass the complete release suite before any mainnet mutation.",
        ],
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rpc_policy_rejects_public_and_local_endpoints() {
        assert!(rpc_policy("https://api.mainnet-beta.solana.com").is_err());
        assert!(rpc_policy("http://127.0.0.1:8899").is_err());
        assert!(rpc_policy("https://localhost/rpc").is_err());
    }

    #[test]
    fn rpc_policy_never_returns_path_or_query() {
        env::set_var("ASPIS_PROFILE23_MAINNET_RPC_IS_PRIVATE", PRIVATE_RPC_ACK);
        let redacted = rpc_policy("https://provider.example/secret-token?api-key=hunter2").unwrap();
        env::remove_var("ASPIS_PROFILE23_MAINNET_RPC_IS_PRIVATE");
        assert_eq!(redacted, "https://provider.example/<redacted>");
        assert!(!redacted.contains("secret"));
        assert!(!redacted.contains("hunter2"));
    }

    #[test]
    fn execution_gate_is_permanently_closed() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
        let summary = evaluate(root, &["--execute".to_owned()]);
        assert!(!summary.mutations_performed);
        assert!(!summary.ready_for_reviewed_live_executor);
        assert!(summary.blockers.iter().any(|name| name == "read_only_mode"));
        assert!(summary
            .blockers
            .iter()
            .any(|name| name == "reviewed_live_executor_available"));

        let release_freeze = summary
            .execution_sequence
            .iter()
            .position(|step| step.contains("freeze their hashes"))
            .unwrap();
        let deploy = summary
            .execution_sequence
            .iter()
            .position(|step| step.starts_with("deploy the exact frozen SBF"))
            .unwrap();
        assert!(release_freeze < deploy);
        assert!(summary
            .execution_sequence
            .iter()
            .any(|step| step.contains("program id plus nullifier only")));
        assert!(summary
            .execution_sequence
            .iter()
            .any(|step| step.contains("byte-identical simulated candidate")));
        assert!(summary
            .evidence_schema_required_fields
            .contains(&"transaction.simulated_and_submitted_wire_identical"));
        assert!(summary
            .evidence_schema_required_fields
            .contains(&"nullifier.prestate_kind"));
        assert!(summary
            .evidence_schema_required_fields
            .contains(&"negative_simulations.sealed_finalize_proof.exact_error"));
        assert!(summary
            .evidence_schema_required_fields
            .contains(&"independent_reconciliation.all_predicates_match"));
    }
}
