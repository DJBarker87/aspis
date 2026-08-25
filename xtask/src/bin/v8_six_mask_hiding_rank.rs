//! One-shot rank replay for the frozen accepted V7 transcript.

use std::{collections::BTreeMap, fs, path::PathBuf, str::FromStr, time::Instant};

use anyhow::{anyhow, ensure, Context, Result};
use aspis_prover::{v8_six_mask_hiding_rank::probe_frozen_v7_six_mask_hiding_rank, HOST_HASH};
use aspis_statement::{AtomicPaymentStatementV4, SpendPublic};
use aspis_verifier::v7_transaction::V7_RELEASE_BINDING;
use serde::Deserialize;
use serde_json::json;
use solana_sdk::pubkey::Pubkey;

#[derive(Debug, Deserialize)]
struct StatementSidecar {
    artifact: String,
    profile: String,
    program_id: String,
    pool: String,
    sequence: u64,
    current_anchor_hex: String,
    nullifier_hex: String,
    output_commitment_hex: String,
    output_anchor_hex: String,
    asset_id: u32,
    fee: u32,
    deployment_domain_hex: String,
    network_tag: String,
    proof_account: String,
    release_binding_hex: String,
}

#[derive(Debug, Deserialize)]
struct ProofMetadata {
    compact_counter: u8,
    frontier_nodes_per_tree: usize,
    queries: [u32; 16],
}

fn arguments() -> Result<BTreeMap<String, PathBuf>> {
    let arguments = std::env::args().skip(1).collect::<Vec<_>>();
    ensure!(
        arguments.len() == 6,
        "expected --proof, --statement and --metadata"
    );
    let mut values = BTreeMap::new();
    for pair in arguments.chunks_exact(2) {
        ensure!(
            ["--proof", "--statement", "--metadata"].contains(&pair[0].as_str()),
            "unknown argument {}",
            pair[0]
        );
        let path = PathBuf::from(&pair[1]);
        ensure!(
            path.is_absolute() && path.is_file(),
            "missing {}",
            path.display()
        );
        ensure!(
            values.insert(pair[0].clone(), path).is_none(),
            "duplicate {}",
            pair[0]
        );
    }
    Ok(values)
}

fn decode_hex_32(field: &str, value: &str) -> Result<[u8; 32]> {
    ensure!(value.len() == 64, "{field} is not 32-byte hex");
    let mut decoded = [0u8; 32];
    for (index, byte) in decoded.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&value[2 * index..2 * index + 2], 16)
            .with_context(|| format!("invalid {field}"))?;
    }
    Ok(decoded)
}

fn statement(sidecar: &StatementSidecar) -> Result<AtomicPaymentStatementV4> {
    ensure!(sidecar.artifact == "aspis_v7_compact_onefold_statement");
    ensure!(sidecar.profile == "V7-26C1-3C2-B10-q16-onefold-digest208-f203-fullC2");
    ensure!(sidecar.network_tag == "devnet");
    ensure!(sidecar.release_binding_hex == hex(&V7_RELEASE_BINDING));
    let digest = |field: &str, value: &str| {
        aspis_statement::decode_digest_canonical(&decode_hex_32(field, value)?)
            .map_err(|error| anyhow!("decode {field}: {error:?}"))
    };
    Ok(AtomicPaymentStatementV4 {
        pool: Pubkey::from_str(&sidecar.pool)?.to_bytes(),
        sequence: sidecar.sequence,
        spend: SpendPublic {
            anchor: digest("current_anchor_hex", &sidecar.current_anchor_hex)?,
            nullifier: digest("nullifier_hex", &sidecar.nullifier_hex)?,
            output_commitment: digest("output_commitment_hex", &sidecar.output_commitment_hex)?,
            asset_id: aspis_statement::decode_asset_id_canonical(sidecar.asset_id)
                .map_err(|error| anyhow!("decode asset_id: {error:?}"))?,
            fee: sidecar.fee,
        },
        output_anchor: digest("output_anchor_hex", &sidecar.output_anchor_hex)?,
        deployment_domain: decode_hex_32("deployment_domain_hex", &sidecar.deployment_domain_hex)?,
    })
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn main() -> Result<()> {
    let arguments = arguments()?;
    let proof = fs::read(&arguments["--proof"])?;
    let sidecar: StatementSidecar = serde_json::from_slice(&fs::read(&arguments["--statement"])?)?;
    let metadata: ProofMetadata = serde_json::from_slice(&fs::read(&arguments["--metadata"])?)?;
    let statement = statement(&sidecar)?;
    let program_id = Pubkey::from_str(&sidecar.program_id)?;
    let proof_account = Pubkey::from_str(&sidecar.proof_account)?;
    ensure!(program_id == aspis_verifier::id());

    let accepted = aspis_verifier::v7_verifier::verify_v7_read_only(
        HOST_HASH,
        &proof,
        metadata.frontier_nodes_per_tree,
        &program_id,
        V7_RELEASE_BINDING,
        &proof_account,
        &statement,
        true,
    )
    .map_err(|error| anyhow!("frozen V7 replay failed: {error:?}"))?;
    ensure!(accepted.transcript.compact_counter == metadata.compact_counter);
    ensure!(accepted.transcript.queries == metadata.queries);

    let started = Instant::now();
    let report = probe_frozen_v7_six_mask_hiding_rank(&accepted.transcript)
        .map_err(|error| anyhow!("rank gate failed: {error:?}"))?;
    let elapsed_ms = started.elapsed().as_millis();
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "artifact": "aspis_v8_six_mask_frozen_v7_complete_view_rank",
            "scope": "focused_host_rank_gate_no_protocol_change_no_deployment",
            "decision": "BLOCKED",
            "frozen_v7": {
                "proof_bytes": proof.len(),
                "compact_counter": metadata.compact_counter,
                "queries": metadata.queries,
            },
            "rank_model": {
                "mask_oracles": report.mask_oracles,
                "variables_qm31": report.variables_qm31,
                "variables_m31": 4 * report.variables_qm31,
                "complete_gamma_combined_root_message_qm31": report.complete_root_message_qm31,
                "complete_root_rank_qm31": report.complete_root_rank_qm31,
                "query_observations_per_oracle_qm31": report.query_observations_per_oracle_qm31,
                "point_observations_per_oracle_qm31": report.point_observations_per_oracle_qm31,
                "conditioning_rank_per_free_oracle_qm31": report.conditioning_rank_per_free_oracle_qm31,
                "conditioning_rank_after_root_qm31": report.conditioning_rank_after_root_qm31,
                "conditioned_kernel_qm31": report.conditioned_kernel_qm31,
                "sumcheck_fields_qm31": report.sumcheck_fields_qm31,
                "conditioned_sumcheck_rank_by_revealed_points_qm31": report.conditioned_sumcheck_rank_by_revealed_points_qm31,
                "conditioned_sumcheck_rank_qm31": report.conditioned_sumcheck_rank_qm31,
                "complete_view_rank_qm31": report.complete_view_rank_qm31,
                "complete_view_rank_m31": 4 * report.complete_view_rank_qm31,
                "complete_view_kernel_qm31": report.complete_view_kernel_qm31,
                "complete_view_kernel_m31": 4 * report.complete_view_kernel_qm31,
            },
            "universal_local_gate": {
                "factor_rank": report.universal_last_round_factor_rank,
                "factor_dimension": report.universal_last_round_factor_dimension,
                "meaning": "rank of {f_k(t), t*f_k(t)}; valid for every nine-round prefix because L_last=201 is nonzero",
            },
            "schedule_guards": {
                "gamma_nonzero": report.gamma_nonzero,
                "kappa_nonzero": report.kappa_nonzero,
                "distinct_queries": report.distinct_queries,
            },
            "frozen_schedule_pass": report.frozen_schedule_pass,
            "interpretation": {
                "ambient_deficit_qm31": report.sumcheck_fields_qm31 - report.conditioned_sumcheck_rank_qm31,
                "attribution": "full root costs one ambient sumcheck direction; the first revealed point z costs five; successor(z) and xor12(z) cost none",
                "not_a_standalone_privacy_break": "legal V7 views obey terminal/root compatibility relations; witness-difference containment has not yet been enumerated for a degree-10 atomic relation",
                "go_kill": "kill direct six-mask transplant into unchanged degree-27 V7; retain only after a genuine degree-at-most-10 arithmetization and coupled legal-view proof",
            },
            "rank_elapsed_ms": elapsed_ms,
            "formal_boundary": [
                "one accepted transcript proves a nonzero minor, not the same ranks for every legal transcript",
                "a V8 wire/transcript does not yet assign the six mask lanes or bind an independent post-root nonzero batching challenge",
                "Merkle/SHA-256 salted-root hiding and Fiat-Shamir adaptive scheduling remain external",
                "the degree-10 semantic relation has not yet been source-bridged to the atomic V7 statement",
            ],
        }))?
    );
    Ok(())
}
