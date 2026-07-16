mod spend_bundle;
mod spend_devnet;
mod spend_devnet_close;
mod spend_mainnet;
mod spend_mainnet_cleanup;
mod spend_mainnet_journal;
mod spend_mainnet_loader;
mod spend_measure;
mod spend_release;
mod spend_statement;

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
                "spend-mainnet-readiness: all readiness gates green; wrote {}",
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
                "spend-devnet-readiness: all read-only gates green; wrote {}",
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
            "usage: cargo run -p aspis-xtask -- spend-measure | spend-release | spend-bundle | spend-mainnet-readiness | spend-mainnet-execute | spend-mainnet-cleanup | spend-devnet-readiness | spend-devnet-execute | spend-devnet-upload-smoke | spend-devnet-close-smoke (got {:?})",
            other
        ),
    }
}
