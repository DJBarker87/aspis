mod spend_bundle;
mod spend_devnet;
mod spend_devnet_close;
mod spend_mainnet;
mod spend_mainnet_cleanup;
mod spend_mainnet_journal;
mod spend_mainnet_loader;
mod spend_mainnet_v5_close;
mod spend_measure;
mod spend_release;
mod spend_statement;
mod v5_component_c_fmat;
mod v5_component_c_maps;
mod v5_component_c_obstruction;
mod v5_component_c_rank;
mod v5_cu_probe;
mod v5_mainnet_refund;
mod v6_cu_probe;
mod v6_release;
mod v7_pool_dispatch_measure;

use std::fs;
use std::path::PathBuf;

use anyhow::{anyhow, bail, Result};

fn stage2_results_dir() -> Result<PathBuf> {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let root = manifest
        .parent()
        .ok_or_else(|| anyhow!("no workspace root"))?
        .to_path_buf();
    let dir = root.join("results/spend");
    fs::create_dir_all(&dir)?;
    Ok(dir)
}

fn main() -> Result<()> {
    let mut args = std::env::args().skip(1);
    match args.next().as_deref() {
        Some("v5-component-c-obstruction") => {
            let dir = stage2_results_dir()?;
            let outcome = v5_component_c_obstruction::run(&dir)?;
            eprintln!(
                "v5-component-c-obstruction: exact 19-dimensional quotient certificate {} bytes sha256 {}; pairs sha256 {}; wrote {} and {} in {} ms",
                outcome.artifact_bytes,
                outcome.artifact_sha256,
                outcome.pair_sha256,
                outcome.artifact_path.display(),
                outcome.manifest_path.display(),
                outcome.total_ms,
            );
            Ok(())
        }
        Some("v5-component-c-rank") => {
            let dir = stage2_results_dir()?;
            let outcome = v5_component_c_rank::run(&dir)?;
            eprintln!(
                "v5-component-c-rank: exact QM31 ranks E={}, F={}, [E;F]={} in {} ms; certificate {} sha256 {}; wrote {}",
                outcome.emat_rank,
                outcome.fmat_rank,
                outcome.joint_rank,
                outcome.total_ms,
                outcome
                    .certificate_path
                    .as_ref()
                    .map_or_else(|| "none".to_owned(), |path| path.display().to_string()),
                outcome.certificate_sha256.as_deref().unwrap_or("none"),
                outcome.manifest_path.display(),
            );
            Ok(())
        }
        Some("v5-component-c-fmat") => {
            let dir = stage2_results_dir()?;
            let outcome = v5_component_c_fmat::run(&dir)?;
            eprintln!(
                "v5-component-c-fmat: maps-only intrinsic {}x{} F matrix generated in {} ms ({} ms total); artifact {} bytes sha256 {}; matrix sha256 {}; wrote {} and {}",
                aspis_prover::v5_mask::component_c_fmat::V5_C_FMAT_ROWS,
                aspis_prover::v5_mask::component_c_fmat::V5_C_FMAT_COLUMNS,
                outcome.generation_ms,
                outcome.total_ms,
                outcome.artifact_bytes,
                outcome.artifact_sha256,
                outcome.matrix_sha256,
                outcome.artifact_path.display(),
                outcome.manifest_path.display(),
            );
            Ok(())
        }
        Some("v5-component-c-emat") => {
            let dir = stage2_results_dir()?;
            let outcome = v5_component_c_maps::run(&dir)?;
            eprintln!(
                "v5-component-c-emat: maps-only {}x{} E matrix generated in {} ms ({} ms total); artifact {} bytes sha256 {}; matrix sha256 {}; wrote {} and {}",
                aspis_prover::v5_mask::component_c_emat::V5_C_EMAT_ROWS,
                aspis_prover::v5_mask::component_c_emat::V5_C_EMAT_COLUMNS,
                outcome.generation_ms,
                outcome.total_ms,
                outcome.artifact_bytes,
                outcome.artifact_sha256,
                outcome.matrix_sha256,
                outcome.artifact_path.display(),
                outcome.manifest_path.display(),
            );
            Ok(())
        }
        Some("v5-cu-probe") => {
            let dir = stage2_results_dir()?;
            let outcome = v5_cu_probe::run(&dir)?;
            eprintln!(
                "v5-cu-probe: genuine tag-67 full atomic transaction accepted at {} CU; wrote {}",
                outcome.candidate_kernel_cu,
                outcome.path.display(),
            );
            Ok(())
        }
        Some("v6-onefold-cu-probe") => {
            let dir = stage2_results_dir()?;
            let outcome = v6_cu_probe::run(&dir)?;
            eprintln!(
                "v6-onefold-cu-probe: packed parser, two Merkle trees, and q16 one-fold checks used {} CU; wrote {}",
                outcome.compute_units,
                outcome.path.display(),
            );
            Ok(())
        }
        Some("v6-full-readonly-cu-probe") => {
            let dir = stage2_results_dir()?;
            let outcome = v6_cu_probe::run_full_read_only(&dir)?;
            eprintln!(
                "v6-full-readonly-cu-probe: transcript, relation, two Merkle trees, and one-fold checks used {} CU; wrote {}",
                outcome.compute_units,
                outcome.path.display(),
            );
            Ok(())
        }
        Some("v6-terminal-cu-probe") => {
            let dir = stage2_results_dir()?;
            let outcome = v6_cu_probe::run_terminal(&dir)?;
            eprintln!(
                "v6-terminal-cu-probe: transcript prefix plus exact atomic terminal used {} CU; wrote {}",
                outcome.compute_units,
                outcome.path.display(),
            );
            Ok(())
        }
        Some("v6-integrated-cu-probe") => {
            let dir = stage2_results_dir()?;
            let outcome = v6_cu_probe::run_integrated(&dir)?;
            eprintln!(
                "v6-integrated-cu-probe: exact terminal, work hashes, transcript, relation, two Merkle trees and one-fold checks used {} CU; wrote {}",
                outcome.compute_units,
                outcome.path.display(),
            );
            Ok(())
        }
        Some("v6-atomic-cu-probe") => {
            let dir = stage2_results_dir()?;
            let outcome = v6_cu_probe::run_atomic(&dir)?;
            eprintln!(
                "v6-atomic-cu-probe: complete atomic wrapper worst case used {} CU; wrote {}",
                outcome.compute_units,
                outcome.path.display(),
            );
            Ok(())
        }
        Some("v6-honest-proof") => {
            let arguments = args.collect::<Vec<_>>();
            let outcome = v6_release::build_honest_proof(&arguments)?;
            eprintln!(
                "v6-honest-proof: mined proof accepted on host; body={} selector={} counter={} frontier={}; wrote {}",
                outcome.proof_bytes,
                outcome.selector,
                outcome.compact_counter,
                outcome.frontier_nodes,
                outcome.metadata_path.display(),
            );
            Ok(())
        }
        Some("v7-honest-proof") => {
            let arguments = args.collect::<Vec<_>>();
            let outcome = v6_release::build_honest_v7_proof(&arguments)?;
            eprintln!(
                "v7-honest-proof: mined proof accepted on host; body={} counter={} frontier={}; wrote {}",
                outcome.proof_bytes,
                outcome.compact_counter,
                outcome.frontier_nodes,
                outcome.metadata_path.display(),
            );
            Ok(())
        }
        Some("v6-production-simulate") => {
            let arguments = args.collect::<Vec<_>>();
            let outcome = v6_release::simulate_production(&arguments)?;
            eprintln!(
                "v6-production-simulate: honest tag-72 accepted at {} CU (worst measured marker path); wrote {}",
                outcome.maximum_compute_units,
                outcome.evidence_path.display(),
            );
            Ok(())
        }
        Some("v7-production-simulate") => {
            let arguments = args.collect::<Vec<_>>();
            let outcome = v6_release::simulate_v7_production(&arguments)?;
            eprintln!(
                "v7-production-simulate: honest V7 accepted at {} CU; wrote {}",
                outcome.compute_units,
                outcome.evidence_path.display(),
            );
            Ok(())
        }
        Some("v7-pool-dispatch-simulate") => {
            let arguments = args.collect::<Vec<_>>();
            let outcome = v7_pool_dispatch_measure::run(&arguments)?;
            eprintln!(
                "v7-pool-dispatch-simulate: frozen honest ASVQ handler accepted at {} program CU; wrote {}",
                outcome.outer_handler_compute_units,
                outcome.evidence_path.display(),
            );
            Ok(())
        }
        Some("v6-adversarial") => {
            let arguments = args.collect::<Vec<_>>();
            let outcome = v6_release::run_adversarial(&arguments)?;
            eprintln!(
                "v6-adversarial: honest production proof accepted and all {} mutation cases rejected; wrote {}",
                outcome.rejected_cases,
                outcome.evidence_path.display(),
            );
            Ok(())
        }
        Some("v7-adversarial") => {
            let arguments = args.collect::<Vec<_>>();
            let outcome = v6_release::run_v7_adversarial(&arguments)?;
            eprintln!(
                "v7-adversarial: honest production proof accepted and all {} focused mutation cases rejected; wrote {}",
                outcome.rejected_cases,
                outcome.evidence_path.display(),
            );
            Ok(())
        }
        Some("v6-devnet-execute") => {
            let arguments = args.collect::<Vec<_>>();
            let outcome = spend_devnet::execute_v6(&arguments)?;
            eprintln!(
                "v6-devnet-execute: finalized tag72 {} at slot {} using {} CU; immutable evidence {}",
                outcome.final_transaction.signature,
                outcome.final_transaction.finalized_slot,
                outcome.landed_compute_units,
                outcome.evidence_path,
            );
            Ok(())
        }
        Some("v7-devnet-execute") => {
            let arguments = args.collect::<Vec<_>>();
            let outcome = spend_devnet::execute_v7(&arguments)?;
            eprintln!(
                "v7-devnet-execute: finalized V7 {} at slot {} using {} CU; immutable evidence {}",
                outcome.final_transaction.signature,
                outcome.final_transaction.finalized_slot,
                outcome.landed_compute_units,
                outcome.evidence_path,
            );
            Ok(())
        }
        Some("spend-measure") => {
            let dir = stage2_results_dir()?;
            let outcome = spend_measure::run_spend_measure(&dir)?;
            eprintln!(
                "spend-measure: production tag59 {} CU, worst-case production tag65 {} CU ({} CU headroom under 1.4M); wrote {} and {}",
                outcome.acceptance_tag59_cu,
                outcome.max_production_tag65_cu,
                1_400_000_i64 - outcome.max_production_tag65_cu as i64,
                outcome.acceptance_path.display(),
                outcome.mutation_path.display(),
            );
            Ok(())
        }
        Some("spend-release") => {
            let dir = stage2_results_dir()?;
            let workspace_root = dir
                .parent()
                .and_then(|results| results.parent())
                .ok_or_else(|| anyhow!("no workspace root above stage2 results"))?;
            let summary = spend_release::evaluate(workspace_root)?;
            let path = dir.join("spend_one_transaction_release.json");
            fs::write(
                &path,
                format!("{}\n", serde_json::to_string_pretty(&summary)?),
            )?;
            if !summary.released {
                bail!(
                    "spend-release: fail-closed; failed gates: {}; wrote {}",
                    summary.failed_gates.join(", "),
                    path.display()
                );
            }
            eprintln!(
                "spend-release: released at {} CU ({} CU headroom); wrote {}",
                summary.max_literal_production_tag65_cu.unwrap_or_default(),
                summary.exact_headroom_under_1_4m_cu.unwrap_or_default(),
                path.display()
            );
            Ok(())
        }
        Some("spend-bundle") => {
            let dir = stage2_results_dir()?;
            let workspace_root = dir
                .parent()
                .and_then(|results| results.parent())
                .ok_or_else(|| anyhow!("no workspace root above stage2 results"))?
                .to_path_buf();
            spend_bundle::run(&workspace_root)
        }
        Some("spend-mainnet-readiness") => {
            let arguments = args.collect::<Vec<_>>();
            let dir = stage2_results_dir()?;
            let workspace_root = dir
                .parent()
                .and_then(|results| results.parent())
                .ok_or_else(|| anyhow!("no workspace root above stage2 results"))?;
            let summary = spend_mainnet::evaluate(workspace_root, &arguments);
            let path = dir.join("spend_mainnet_beta_readiness.json");
            fs::write(
                &path,
                format!("{}\n", serde_json::to_string_pretty(&summary)?),
            )?;
            if !summary.read_only_preflight_green {
                bail!(
                    "spend-mainnet-readiness: fail-closed; blockers: {}; wrote {}",
                    summary.blockers.join(", "),
                    path.display()
                );
            }
            eprintln!(
                "spend-mainnet-readiness: all readiness gates passed; wrote {}",
                path.display()
            );
            Ok(())
        }
        Some("spend-mainnet-execute") => {
            let arguments = args.collect::<Vec<_>>();
            let dir = stage2_results_dir()?;
            let workspace_root = dir
                .parent()
                .and_then(|results| results.parent())
                .ok_or_else(|| anyhow!("no workspace root above stage2 results"))?;

            // Re-run the independent, read-only policy immediately before the
            // executor revalidates the same release instance and first write.
            let readiness = spend_mainnet::evaluate(workspace_root, &[]);
            if !readiness.read_only_preflight_green {
                bail!(
                    "spend-mainnet-execute: preflight blocked: {}",
                    readiness.blockers.join(", ")
                );
            }

            let run_directory = std::env::var("ASPIS_SPEND_MAINNET_RUN_DIR")
                .map(PathBuf::from)
                .map_err(|_| anyhow!("ASPIS_SPEND_MAINNET_RUN_DIR is required"))?;
            let mut journal = if run_directory.exists() {
                spend_mainnet_journal::RecoveryJournal::reopen(&run_directory)?
            } else {
                let run_id = format!(
                    "spend-mainnet-{}",
                    chrono::Utc::now().format("%Y%m%dT%H%M%SZ")
                );
                spend_mainnet_journal::RecoveryJournal::create(&run_directory, run_id)?
            };
            if journal.state().completed_outcome.is_some() {
                bail!("spend-mainnet-execute: recovery journal is already complete");
            }
            journal.record_checkpoint(
                "immediate_read_only_preflight_green",
                serde_json::to_value(&readiness)?,
            )?;

            let evidence = spend_devnet::execute_mainnet(workspace_root, &arguments)?;
            journal.record_checkpoint(
                "tag65_and_replay_probe_finalized",
                serde_json::json!({
                    "network": evidence.network,
                    "program_id": evidence.program_id,
                    "tag65_signature": evidence.final_transaction.signature,
                    "tag65_finalized_slot": evidence.final_transaction.finalized_slot,
                    "replay_close_signature": evidence.replay_probe_close_transaction.signature,
                    "replay_close_finalized_slot": evidence.replay_probe_close_transaction.finalized_slot,
                    "evidence_path": evidence.evidence_path,
                }),
            )?;
            journal.complete("tag65_and_replay_probe_finalized")?;
            eprintln!(
                "spend-mainnet-execute: finalized {} at slot {}; immutable evidence {}; completed top-level run checkpoint journal {} (not per-wire recovery)",
                evidence.final_transaction.signature,
                evidence.final_transaction.finalized_slot,
                evidence.evidence_path,
                journal.journal_path().display(),
            );
            Ok(())
        }
        Some("spend-mainnet-cleanup") => {
            let arguments = args.collect::<Vec<_>>();
            let outcome = spend_mainnet_cleanup::execute(&arguments)?;
            eprintln!(
                "spend-mainnet-cleanup: finalized {} at slot {}; refunded {} lamports; fee {} lamports; immutable evidence {} and {}",
                outcome.signature,
                outcome.finalized_slot,
                outcome.refund_lamports,
                outcome.fee_lamports,
                outcome.preclose_evidence.path,
                outcome.postclose_evidence.path,
            );
            Ok(())
        }
        Some("v5-mainnet-proof-close") => {
            let arguments = args.collect::<Vec<_>>();
            let evidence = spend_mainnet_v5_close::execute(&arguments)?;
            eprintln!(
                "v5-mainnet-proof-close: finalized {} at slot {}; refunded {} lamports; immutable evidence {}",
                evidence.signature,
                evidence.finalized_slot,
                evidence.refund_lamports,
                evidence.evidence_path,
            );
            Ok(())
        }
        Some("v5-mainnet-payer-sweep") => {
            let arguments = args.collect::<Vec<_>>();
            let outcome = v5_mainnet_refund::execute(&arguments)?;
            eprintln!(
                "v5-mainnet-payer-sweep: finalized {} at slot {}; sent {} lamports to {}; fee {} lamports; payer post-balance {}; immutable evidence {} and {}",
                outcome.signature,
                outcome.finalized_slot,
                outcome.transfer_lamports,
                outcome.refund_recipient_pubkey,
                outcome.fee_lamports,
                outcome.payer_post_lamports,
                outcome.presubmit_evidence.path,
                outcome.postsubmit_evidence.path,
            );
            Ok(())
        }
        Some("v5-devnet-build") => {
            let arguments = args.collect::<Vec<_>>();
            let outcome = spend_devnet::v5::build_sbf(&arguments)?;
            println!("{}", serde_json::to_string_pretty(&outcome)?);
            eprintln!(
                "v5-devnet-build: created feature-only SBF {} bytes at {} and provenance {} (HEAD {})",
                outcome.sbf_bytes,
                outcome.sbf_path,
                outcome.provenance_path,
                outcome.git_head,
            );
            Ok(())
        }
        Some("v5-devnet-artifact") => {
            let arguments = args.collect::<Vec<_>>();
            let outcome = spend_devnet::v5::generate_artifact(&arguments)?;
            println!("{}", serde_json::to_string_pretty(&outcome)?);
            eprintln!(
                "v5-devnet-artifact: created {} proof bytes at {} and strict statement {} (leastGood={}, successful attempt index={})",
                outcome.proof_bytes,
                outcome.proof_path,
                outcome.statement_path,
                outcome.least_good_selector,
                outcome.successful_attempt_index,
            );
            Ok(())
        }
        Some("v5-devnet-readiness") => {
            let arguments = args.collect::<Vec<_>>();
            let readiness = spend_devnet::v5::readiness(&arguments)?;
            println!("{}", serde_json::to_string_pretty(&readiness)?);
            eprintln!(
                "v5-devnet-readiness: read-only gates passed for program {}, pool {}, proof account {}",
                readiness.program_id, readiness.pool, readiness.proof_account,
            );
            Ok(())
        }
        Some("v5-devnet-execute") => {
            let arguments = args.collect::<Vec<_>>();
            let evidence = spend_devnet::v5::execute(&arguments)?;
            println!("{}", serde_json::to_string_pretty(&evidence)?);
            eprintln!(
                "v5-devnet-execute: finalized tag-67 {} at slot {}; immutable evidence {}",
                evidence.final_transaction.signature,
                evidence.final_transaction.finalized_slot,
                evidence.evidence_path,
            );
            Ok(())
        }
        Some("v5-mainnet-artifact") => {
            let arguments = args.collect::<Vec<_>>();
            let outcome = spend_devnet::v5::generate_mainnet_artifact(&arguments)?;
            println!("{}", serde_json::to_string_pretty(&outcome)?);
            eprintln!(
                "v5-mainnet-artifact: created {} proof bytes at {} and strict statement {} (leastGood={}, successful attempt index={})",
                outcome.proof_bytes,
                outcome.proof_path,
                outcome.statement_path,
                outcome.least_good_selector,
                outcome.successful_attempt_index,
            );
            Ok(())
        }
        Some("v5-mainnet-readiness") => {
            let arguments = args.collect::<Vec<_>>();
            let readiness = spend_devnet::v5::mainnet_readiness(&arguments)?;
            println!("{}", serde_json::to_string_pretty(&readiness)?);
            if readiness.ready {
                eprintln!(
                    "v5-mainnet-readiness: ready for program {}, pool {}, proof account {}, solana-core {}, feature-set {}",
                    readiness.program_id,
                    readiness.pool,
                    readiness.proof_account,
                    readiness
                        .observed_solana_core
                        .as_deref()
                        .unwrap_or("unavailable"),
                    readiness
                        .observed_feature_set
                        .map_or_else(|| "unavailable".to_owned(), |value| value.to_string()),
                );
            } else {
                eprintln!(
                    "v5-mainnet-readiness: exact read-only identities matched; execution remains blocked: {}",
                    readiness
                        .execution_stop_reason
                        .unwrap_or("unspecified stop condition")
                );
            }
            Ok(())
        }
        Some("v5-mainnet-execute") => {
            let arguments = args.collect::<Vec<_>>();
            let evidence = spend_devnet::v5::execute_mainnet(&arguments)?;
            println!("{}", serde_json::to_string_pretty(&evidence)?);
            eprintln!(
                "v5-mainnet-execute: finalized tag-67 {} at slot {}; immutable evidence {}",
                evidence.signature()?,
                evidence.finalized_slot()?,
                evidence.evidence_path()?,
            );
            Ok(())
        }
        Some("spend-devnet-readiness") => {
            let arguments = args.collect::<Vec<_>>();
            let dir = stage2_results_dir()?;
            let workspace_root = dir
                .parent()
                .and_then(|results| results.parent())
                .ok_or_else(|| anyhow!("no workspace root above stage2 results"))?;
            let summary = spend_devnet::readiness(workspace_root, &arguments)?;
            let path = dir.join("spend_devnet_readiness.json");
            fs::write(
                &path,
                format!("{}\n", serde_json::to_string_pretty(&summary)?),
            )?;
            if !summary.ready {
                bail!(
                    "spend-devnet-readiness: fail-closed; blockers: {}; wrote {}",
                    summary.blockers.join(", "),
                    path.display()
                );
            }
            eprintln!(
                "spend-devnet-readiness: all read-only gates passed; wrote {}",
                path.display()
            );
            Ok(())
        }
        Some("spend-devnet-execute") => {
            let arguments = args.collect::<Vec<_>>();
            let dir = stage2_results_dir()?;
            let workspace_root = dir
                .parent()
                .and_then(|results| results.parent())
                .ok_or_else(|| anyhow!("no workspace root above stage2 results"))?;
            let evidence = spend_devnet::execute(workspace_root, &arguments)?;
            eprintln!(
                "spend-devnet-execute: finalized {} at slot {}; immutable evidence {}",
                evidence.final_transaction.signature,
                evidence.final_transaction.finalized_slot,
                evidence.evidence_path
            );
            Ok(())
        }
        Some("spend-devnet-upload-smoke") => {
            let arguments = args.collect::<Vec<_>>();
            let evidence = spend_devnet::upload_smoke(&arguments)?;
            eprintln!(
                "spend-devnet-upload-smoke: sealed {} bytes in {} uploads/{} ms; immutable evidence {}",
                evidence.proof_bytes,
                evidence.proof_upload_transaction_count,
                evidence.upload_wall_milliseconds,
                evidence.evidence_path
            );
            Ok(())
        }
        Some("spend-devnet-close-smoke") => {
            let arguments = args.collect::<Vec<_>>();
            let evidence = spend_devnet_close::execute(&arguments)?;
            eprintln!(
                "spend-devnet-close-smoke: finalized {} at slot {}; refunded {} lamports; immutable evidence {}",
                evidence.signature,
                evidence.finalized_slot,
                evidence.refund_lamports,
                evidence.evidence_path
            );
            Ok(())
        }
        other => bail!(
            "usage: cargo run -p aspis-xtask -- v5-component-c-obstruction | v5-component-c-rank | v5-component-c-fmat | v5-component-c-emat | v5-cu-probe | v5-devnet-build | v5-devnet-artifact | v5-devnet-readiness | v5-devnet-execute | v5-mainnet-artifact | v5-mainnet-readiness | v5-mainnet-execute | v5-mainnet-proof-close | v5-mainnet-payer-sweep | spend-measure | spend-release | spend-bundle | spend-mainnet-readiness | spend-mainnet-execute | spend-mainnet-cleanup | spend-devnet-readiness | spend-devnet-execute | spend-devnet-upload-smoke | spend-devnet-close-smoke | v7-pool-dispatch-simulate (got {:?})",
            other
        ),
    }
}
