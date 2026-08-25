//! One-shot local-SVM measurement of the opt-in frozen Tag-73 ASVQ handler.
//!
//! The program and proof account are preloaded at validator genesis. The
//! signed wire is submitted exactly once to `simulateTransaction`; this module
//! never calls `sendTransaction`, deploys, uploads, finalizes or mutates Pool
//! state.

use std::{
    collections::BTreeMap,
    fs::{self, OpenOptions},
    io::Write,
    path::{Path, PathBuf},
    process::Command,
};

use anyhow::{anyhow, ensure, Context, Result};
use aspis_prover::HOST_HASH;
use aspis_statement::{
    atomic_payment_statement_digest_v4,
    pool_v1::{
        decode_verifier_dispatch_result_v1, encode_verifier_dispatch_request_v1,
        encode_verifier_dispatch_result_v1, verifier_dispatch_binding_from_envelope_v1,
        verifier_proof_body_digest_v1, HistoricalAnchorEnvelopeV1, PoolV1TransitionKind,
        VerifierDispatchRequestV1, VerifierDispatchResultV1,
        POOL_V1_VERIFIER_DISPATCH_BINDING_PREFIX_BYTES, POOL_V1_VERIFIER_DISPATCH_RESULT_BYTES,
        POOL_V1_VERIFIER_DISPATCH_SUCCESS_CODE,
    },
};
use aspis_verifier::{
    v7_pool_dispatch::{
        encode_v7_pool_tag73_profile_payload_v1, V7PoolTag73ProfilePayloadV1,
        V7_POOL_TAG73_CHECK_ALL_WORK, V7_POOL_TAG73_FRONTIER_NODES, V7_POOL_TAG73_PROFILE_BINDING,
        V7_POOL_TAG73_PROFILE_BINDING_PREIMAGE, V7_POOL_TAG73_PROFILE_PAYLOAD_BYTES,
        V7_POOL_TAG73_PROOF_BODY_BYTES,
    },
    v7_transaction::V7_RELEASE_BINDING,
    PROOF_ACCOUNT_HEADER_LEN,
};
use serde_json::json;
use sha2::{Digest as _, Sha256};

use crate::{
    spend_measure::simulate_readonly_program_account_instruction_with_return_data_no_send,
    v6_release::load_v7_execution_inputs,
};

const BUILD_COMMAND: &str = "NO_DNA=1 CARGO_BUILD_JOBS=2 cargo-build-sbf --manifest-path programs/aspis-verifier/Cargo.toml --no-default-features --features v7-pool-dispatch-profile --sbf-out-dir target/p3f-svm-deploy";
const PREFERRED_COMPUTE_LIMIT: u64 = 1_300_000;
const HARD_TRANSACTION_COMPUTE_LIMIT: u64 = 1_400_000;
const CONTEXT_ONLY_ATOMIC_TAG73_CU: u64 = 1_258_013;

pub(crate) struct V7PoolDispatchMeasurementOutcome {
    pub(crate) outer_handler_compute_units: u64,
    pub(crate) evidence_path: PathBuf,
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn command_version(program: &str, arguments: &[&str]) -> String {
    Command::new(program)
        .env("NO_DNA", "1")
        .args(arguments)
        .output()
        .map(|output| {
            let stdout = String::from_utf8_lossy(&output.stdout).trim().to_string();
            let stderr = String::from_utf8_lossy(&output.stderr).trim().to_string();
            if stdout.is_empty() {
                stderr
            } else if stderr.is_empty() {
                stdout
            } else {
                format!("{stdout}\n{stderr}")
            }
        })
        .unwrap_or_else(|error| format!("unavailable: {error}"))
}

fn parse_arguments(arguments: &[String]) -> Result<BTreeMap<String, String>> {
    const ALLOWED: [&str; 5] = ["--sbf", "--proof", "--statement", "--metadata", "--out"];
    let mut values = BTreeMap::new();
    let mut index = 0usize;
    while index < arguments.len() {
        let key = arguments.get(index).context("missing P3f argument")?;
        ensure!(
            ALLOWED.contains(&key.as_str()),
            "unknown P3f measurement argument {key}"
        );
        let value = arguments
            .get(index + 1)
            .with_context(|| format!("missing value for {key}"))?;
        ensure!(
            values.insert(key.clone(), value.clone()).is_none(),
            "duplicate P3f measurement argument {key}"
        );
        index += 2;
    }
    for key in ALLOWED {
        ensure!(values.contains_key(key), "missing P3f measurement {key}");
    }
    Ok(values)
}

fn required_path(values: &BTreeMap<String, String>, key: &str) -> Result<PathBuf> {
    let path = PathBuf::from(values.get(key).with_context(|| format!("missing {key}"))?);
    ensure!(path.is_absolute(), "{key} must be absolute");
    Ok(path)
}

fn sealed_exact_proof_account(proof: &[u8]) -> Result<Vec<u8>> {
    ensure!(
        proof.len() == V7_POOL_TAG73_PROOF_BODY_BYTES as usize,
        "P3f proof length changed"
    );
    let mut data = vec![0u8; PROOF_ACCOUNT_HEADER_LEN + proof.len()];
    data[..4].copy_from_slice(b"ASPU");
    data[4..8].copy_from_slice(&V7_POOL_TAG73_PROOF_BODY_BYTES.to_le_bytes());
    data[PROOF_ACCOUNT_HEADER_LEN..].copy_from_slice(proof);
    Ok(data)
}

fn parse_outer_program_compute(logs: &[String], program_id: &str) -> Result<u64> {
    let prefix = format!("Program {program_id} consumed ");
    let matches = logs
        .iter()
        .filter_map(|line| {
            line.strip_prefix(&prefix)
                .and_then(|tail| tail.split_whitespace().next())
                .and_then(|value| value.parse::<u64>().ok())
        })
        .collect::<Vec<_>>();
    ensure!(
        matches.len() == 1,
        "expected one outer program-consumption log, found {matches:?}"
    );
    Ok(matches[0])
}

fn create_new(path: &Path, bytes: &[u8]) -> Result<()> {
    let mut file = OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(path)
        .with_context(|| format!("create {}", path.display()))?;
    file.write_all(bytes)?;
    Ok(())
}

pub(crate) fn run(arguments: &[String]) -> Result<V7PoolDispatchMeasurementOutcome> {
    let values = parse_arguments(arguments)?;
    let sbf_path = required_path(&values, "--sbf")?;
    let proof_path = required_path(&values, "--proof")?;
    let statement_path = required_path(&values, "--statement")?;
    let metadata_path = required_path(&values, "--metadata")?;
    let evidence_path = required_path(&values, "--out")?;
    for path in [&sbf_path, &proof_path, &statement_path, &metadata_path] {
        ensure!(path.is_file(), "missing P3f input {}", path.display());
    }
    ensure!(
        !evidence_path.exists(),
        "refusing to overwrite {}",
        evidence_path.display()
    );

    let inputs = load_v7_execution_inputs(&proof_path, &statement_path, &metadata_path, "devnet")?;
    ensure!(
        inputs.frontier_nodes == usize::from(V7_POOL_TAG73_FRONTIER_NODES),
        "frozen P3f frontier count changed"
    );
    ensure!(
        inputs.program_id == aspis_verifier::id(),
        "frozen verifier program changed"
    );

    let proof_body_digest = verifier_proof_body_digest_v1(&inputs.proof, HOST_HASH);
    let atomic_statement_digest = atomic_payment_statement_digest_v4(&inputs.statement, HOST_HASH)
        .map_err(|error| anyhow!("derive P3f atomic statement digest: {error:?}"))?;
    let profile = V7PoolTag73ProfilePayloadV1 {
        frontier_nodes: V7_POOL_TAG73_FRONTIER_NODES,
        proof_body_length: V7_POOL_TAG73_PROOF_BODY_BYTES,
        proof_body_digest,
        verifier_program: inputs.program_id.to_bytes(),
        release_binding: V7_RELEASE_BINDING,
        attempt_id: inputs.proof_account.to_bytes(),
        statement_digest: atomic_statement_digest,
        statement: inputs.statement.clone(),
        check_pow: V7_POOL_TAG73_CHECK_ALL_WORK == 1,
    };
    let payload = encode_v7_pool_tag73_profile_payload_v1(&profile, HOST_HASH)
        .map_err(|error| anyhow!("encode P3f payload: {error:?}"))?;
    let envelope = HistoricalAnchorEnvelopeV1 {
        transition_kind: PoolV1TransitionKind::PrivateTransfer,
        pool: inputs.statement.pool,
        deployment_domain: inputs.statement.deployment_domain,
        anchor_sequence: inputs.statement.sequence,
        anchor_root: inputs.statement.spend.anchor,
        nullifier: inputs.statement.spend.nullifier,
        verifier_profile: V7_POOL_TAG73_PROFILE_BINDING,
        verifier_release: V7_RELEASE_BINDING,
    };
    let binding = verifier_dispatch_binding_from_envelope_v1(
        inputs.program_id.to_bytes(),
        &envelope,
        &payload,
        inputs.proof_account.to_bytes(),
        proof_body_digest,
        V7_POOL_TAG73_PROOF_BODY_BYTES,
        HOST_HASH,
    )
    .map_err(|error| anyhow!("derive P3f ASVQ binding: {error:?}"))?;
    let request = encode_verifier_dispatch_request_v1(
        &VerifierDispatchRequestV1 {
            binding,
            statement_payload: &payload,
        },
        HOST_HASH,
    )
    .map_err(|error| anyhow!("encode P3f ASVQ: {error:?}"))?;
    ensure!(
        request.len()
            == POOL_V1_VERIFIER_DISPATCH_BINDING_PREFIX_BYTES + V7_POOL_TAG73_PROFILE_PAYLOAD_BYTES,
        "P3f complete ASVQ length changed"
    );
    let expected_result = encode_verifier_dispatch_result_v1(&VerifierDispatchResultV1 {
        success_code: POOL_V1_VERIFIER_DISPATCH_SUCCESS_CODE,
        binding,
    })
    .map_err(|error| anyhow!("encode expected P3f ASVS: {error:?}"))?;
    let proof_account_data = sealed_exact_proof_account(&inputs.proof)?;

    // This is the one and only SVM execution in this command.
    let simulation = simulate_readonly_program_account_instruction_with_return_data_no_send(
        &sbf_path,
        inputs.proof_account,
        inputs.program_id,
        &proof_account_data,
        request.clone(),
    )?;
    let outer_handler_compute_units =
        parse_outer_program_compute(&simulation.logs, &inputs.program_id.to_string())?;
    ensure!(
        simulation.return_data_program_id == inputs.program_id,
        "P3f return-data writer changed"
    );
    ensure!(
        simulation.return_data == expected_result,
        "P3f return data does not equal exact expected ASVS"
    );
    let decoded_result = decode_verifier_dispatch_result_v1(&simulation.return_data)
        .map_err(|error| anyhow!("decode measured P3f ASVS: {error:?}"))?;
    ensure!(
        decoded_result.binding == binding
            && decoded_result.success_code == POOL_V1_VERIFIER_DISPATCH_SUCCESS_CODE,
        "measured P3f ASVS binding changed"
    );
    ensure!(
        simulation.account_owner_before == inputs.program_id
            && simulation.account_owner_after == inputs.program_id
            && simulation.account_data_before == proof_account_data
            && simulation.account_data_after == proof_account_data,
        "P3f proof-account snapshot changed"
    );

    let sbf = fs::read(&sbf_path)?;
    let over_preferred = outer_handler_compute_units > PREFERRED_COMPUTE_LIMIT;
    let source_diagnosis = if over_preferred {
        vec![
            "The dominant new wrapper candidate is the mandatory raw SHA-256 pass over all 30,504 proof bytes; this run did not add instrumentation or a second baseline, so the phase attribution is source-based rather than separately measured.",
            "The remaining wrapper hashes cover the 392-byte profile payload, 208-byte envelope and 216-byte atomic statement; canonical parsing/duplicate comparisons and the 384-byte return-data write are smaller source-level candidates.",
            "No optimization was attempted after observing the gate result.",
        ]
    } else {
        vec![
            "No phase instrumentation or second baseline was introduced; the exact result is the unmodified outer-handler program-consumption log.",
        ]
    };
    let measurement_command = format!(
        "NO_DNA=1 CARGO_BUILD_JOBS=2 cargo run -p aspis-xtask --bin aspis-xtask -- v7-pool-dispatch-simulate --sbf {} --proof {} --statement {} --metadata {} --out {}",
        sbf_path.display(),
        proof_path.display(),
        statement_path.display(),
        metadata_path.display(),
        evidence_path.display(),
    );
    let evidence = json!({
        "artifact": "aspis_v7_pool_dispatch_profile_p3f_svm_measurement",
        "schema_version": 1,
        "generated_at_utc": chrono::Utc::now().to_rfc3339(),
        "scope": "one isolated local-validator simulateTransaction of the opt-in ASVQ selected-verifier handler over the frozen honest Tag-73 proof; no Pool CPI/state semantics",
        "measurement_count": 1,
        "cluster": "isolated solana-test-validator",
        "no_send_transaction": true,
        "no_deploy_rpc": true,
        "program_preloaded_with_bpf_program": true,
        "build_command": BUILD_COMMAND,
        "measurement_command": measurement_command,
        "toolchain": {
            "solana_test_validator": command_version("solana-test-validator", &["--version"]),
            "solana_cli": command_version("solana", &["--version"]),
            "cargo_build_sbf": command_version("cargo-build-sbf", &["--version"]),
            "rustc": command_version("rustc", &["--version"]),
            "cargo": command_version("cargo", &["--version"]),
            "host": command_version("uname", &["-a"]),
        },
        "sbf": {
            "path": sbf_path,
            "bytes": sbf.len(),
            "sha256": sha256(&sbf),
            "feature": "v7-pool-dispatch-profile",
        },
        "profile": {
            "profile_binding_preimage": String::from_utf8_lossy(V7_POOL_TAG73_PROFILE_BINDING_PREIMAGE),
            "profile_binding": hex(&V7_POOL_TAG73_PROFILE_BINDING),
            "release_binding": hex(&V7_RELEASE_BINDING),
            "frontier_nodes": V7_POOL_TAG73_FRONTIER_NODES,
            "all_work_checked": true,
            "payload_bytes": payload.len(),
            "payload_sha256": sha256(&payload),
            "asvq_bytes": request.len(),
            "asvq_sha256": sha256(&request),
        },
        "proof": {
            "path": proof_path,
            "bytes": inputs.proof.len(),
            "sha256": inputs.proof_sha256,
            "account": inputs.proof_account.to_string(),
            "account_owner": inputs.program_id.to_string(),
            "account_bytes": proof_account_data.len(),
            "account_sha256_before": sha256(&simulation.account_data_before),
            "account_sha256_after": sha256(&simulation.account_data_after),
            "account_owner_before": simulation.account_owner_before.to_string(),
            "account_owner_after": simulation.account_owner_after.to_string(),
            "account_snapshot_unchanged": true,
            "instruction_meta_readonly": true,
            "instruction_meta_nonsigner": true,
        },
        "statement": {
            "path": statement_path,
            "sha256": inputs.statement_sha256,
            "atomic_statement_digest": hex(&atomic_statement_digest),
        },
        "result": {
            "simulation_success": true,
            "host_frozen_proof_replay_before_svm": true,
            "serialized_transaction_bytes": simulation.serialized_transaction_bytes,
            "transaction_units_consumed": simulation.units,
            "outer_handler_program_compute_units": outer_handler_compute_units,
            "transaction_minus_outer_program_cu": simulation.units as i64 - outer_handler_compute_units as i64,
            "preferred_limit": PREFERRED_COMPUTE_LIMIT,
            "headroom_under_preferred_limit": PREFERRED_COMPUTE_LIMIT as i64 - outer_handler_compute_units as i64,
            "hard_transaction_limit": HARD_TRANSACTION_COMPUTE_LIMIT,
            "headroom_under_hard_transaction_limit": HARD_TRANSACTION_COMPUTE_LIMIT as i64 - outer_handler_compute_units as i64,
            "asvs_bytes": simulation.return_data.len(),
            "expected_asvs_bytes": POOL_V1_VERIFIER_DISPATCH_RESULT_BYTES,
            "asvs_sha256": sha256(&simulation.return_data),
            "asvs_writer": simulation.return_data_program_id.to_string(),
            "asvs_exact_expected_bytes": true,
            "asvs_binding_exact": true,
            "success_code": format!("0x{:08x}", decoded_result.success_code),
        },
        "baseline": {
            "same_environment_baseline_measured": false,
            "same_environment_delta": serde_json::Value::Null,
            "reason": "The task authorized exactly one SVM measurement. No second baseline transaction was simulated.",
            "context_only_prior_atomic_tag73": {
                "source": "results/spend/v7-devnet-20260825-fullc2/v7-production-sbf-simulation.json",
                "compute_units": CONTEXT_ONLY_ATOMIC_TAG73_CU,
                "comparable_delta": false,
                "reason": "The prior value is a different state-changing instruction/binary and is not a same-run outer-handler baseline."
            }
        },
        "source_diagnosis": source_diagnosis,
        "logs": simulation.logs,
        "limitations": [
            "This measures the selected verifier as the top-level program, not the Pool P3e CPI caller and not a Pool atomic transition.",
            "The RPC transaction total includes two compute-budget instructions; outer_handler_program_compute_units is taken from the validator's exact top-level program-consumption log.",
            "A simulation account snapshot cannot by itself prove rollback or runtime read-only enforcement; source account-meta checks and Solana runtime semantics remain boundaries.",
            "No same-environment baseline, repeat, devnet execution, deployment, transaction submission or Pool state write was performed.",
        ],
    });
    let mut bytes = serde_json::to_vec_pretty(&evidence)?;
    bytes.push(b'\n');
    create_new(&evidence_path, &bytes)?;

    Ok(V7PoolDispatchMeasurementOutcome {
        outer_handler_compute_units,
        evidence_path,
    })
}
