mod profile23_devnet;
mod profile23_devnet_close;
mod profile23_mainnet;
mod profile23_mainnet_cleanup;
mod profile23_mainnet_journal;
mod profile23_mainnet_loader;
mod profile23_release;
mod profile23_statement;

use std::fs;
use std::path::PathBuf;

use anyhow::{anyhow, bail, Result};

fn stage2_results_dir() -> Result<PathBuf> {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let root = manifest
        .parent()
        .ok_or_else(|| anyhow!("no workspace root"))?
        .to_path_buf();
    let dir = root.join("results/stage2");
    fs::create_dir_all(&dir)?;
    Ok(dir)
}

fn main() -> Result<()> {
    let mut args = std::env::args().skip(1);
    match args.next().as_deref() {
        Some("stage2-profile23-one-transaction-release") => {
            let dir = stage2_results_dir()?;
            let workspace_root = dir
                .parent()
                .and_then(|results| results.parent())
                .ok_or_else(|| anyhow!("no workspace root above stage2 results"))?;
            let summary = profile23_release::evaluate(workspace_root)?;
            let path = dir.join("profile23_one_transaction_release.json");
            fs::write(
                &path,
                format!("{}\n", serde_json::to_string_pretty(&summary)?),
            )?;
            if !summary.released {
                bail!(
                    "stage2-profile23-one-transaction-release: fail-closed; failed gates: {}; wrote {}",
                    summary.failed_gates.join(", "),
                    path.display()
                );
            }
            eprintln!(
                "stage2-profile23-one-transaction-release: released at {} CU ({} CU headroom); wrote {}",
                summary.max_literal_production_tag65_cu.unwrap_or_default(),
                summary.exact_headroom_under_1_4m_cu.unwrap_or_default(),
                path.display()
            );
            Ok(())
        }
        Some("stage2-profile23-mainnet-readiness") => {
            let arguments = args.collect::<Vec<_>>();
            let dir = stage2_results_dir()?;
            let workspace_root = dir
                .parent()
                .and_then(|results| results.parent())
                .ok_or_else(|| anyhow!("no workspace root above stage2 results"))?;
            let summary = profile23_mainnet::evaluate(workspace_root, &arguments);
            let path = dir.join("profile23_mainnet_beta_readiness.json");
            fs::write(
                &path,
                format!("{}\n", serde_json::to_string_pretty(&summary)?),
            )?;
            if !summary.read_only_preflight_green {
                bail!(
                    "stage2-profile23-mainnet-readiness: fail-closed; blockers: {}; wrote {}",
                    summary.blockers.join(", "),
                    path.display()
                );
            }
            eprintln!(
                "stage2-profile23-mainnet-readiness: all readiness gates green; wrote {}",
                path.display()
            );
            Ok(())
        }
        Some("stage2-profile23-mainnet-execute") => {
            let arguments = args.collect::<Vec<_>>();
            let dir = stage2_results_dir()?;
            let workspace_root = dir
                .parent()
                .and_then(|results| results.parent())
                .ok_or_else(|| anyhow!("no workspace root above stage2 results"))?;

            // Re-run the independent, read-only policy immediately before the
            // executor revalidates the same release instance and first write.
            let readiness = profile23_mainnet::evaluate(workspace_root, &[]);
            if !readiness.read_only_preflight_green {
                bail!(
                    "stage2-profile23-mainnet-execute: preflight blocked: {}",
                    readiness.blockers.join(", ")
                );
            }

            let run_directory = std::env::var("ASPIS_PROFILE23_MAINNET_RUN_DIR")
                .map(PathBuf::from)
                .map_err(|_| anyhow!("ASPIS_PROFILE23_MAINNET_RUN_DIR is required"))?;
            let mut journal = if run_directory.exists() {
                profile23_mainnet_journal::RecoveryJournal::reopen(&run_directory)?
            } else {
                let run_id = format!(
                    "profile23-mainnet-{}",
                    chrono::Utc::now().format("%Y%m%dT%H%M%SZ")
                );
                profile23_mainnet_journal::RecoveryJournal::create(&run_directory, run_id)?
            };
            if journal.state().completed_outcome.is_some() {
                bail!("stage2-profile23-mainnet-execute: recovery journal is already complete");
            }
            journal.record_checkpoint(
                "immediate_read_only_preflight_green",
                serde_json::to_value(&readiness)?,
            )?;

            let evidence = profile23_devnet::execute_mainnet(workspace_root, &arguments)?;
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
                "stage2-profile23-mainnet-execute: finalized {} at slot {}; immutable evidence {}; completed top-level run checkpoint journal {} (not per-wire recovery)",
                evidence.final_transaction.signature,
                evidence.final_transaction.finalized_slot,
                evidence.evidence_path,
                journal.journal_path().display(),
            );
            Ok(())
        }
        Some("stage2-profile23-mainnet-cleanup") => {
            let arguments = args.collect::<Vec<_>>();
            let outcome = profile23_mainnet_cleanup::execute(&arguments)?;
            eprintln!(
                "stage2-profile23-mainnet-cleanup: finalized {} at slot {}; refunded {} lamports; fee {} lamports; immutable evidence {} and {}",
                outcome.signature,
                outcome.finalized_slot,
                outcome.refund_lamports,
                outcome.fee_lamports,
                outcome.preclose_evidence.path,
                outcome.postclose_evidence.path,
            );
            Ok(())
        }
        Some("stage2-profile23-devnet-readiness") => {
            let arguments = args.collect::<Vec<_>>();
            let dir = stage2_results_dir()?;
            let workspace_root = dir
                .parent()
                .and_then(|results| results.parent())
                .ok_or_else(|| anyhow!("no workspace root above stage2 results"))?;
            let summary = profile23_devnet::readiness(workspace_root, &arguments)?;
            let path = dir.join("profile23_devnet_readiness.json");
            fs::write(
                &path,
                format!("{}\n", serde_json::to_string_pretty(&summary)?),
            )?;
            if !summary.ready {
                bail!(
                    "stage2-profile23-devnet-readiness: fail-closed; blockers: {}; wrote {}",
                    summary.blockers.join(", "),
                    path.display()
                );
            }
            eprintln!(
                "stage2-profile23-devnet-readiness: all read-only gates green; wrote {}",
                path.display()
            );
            Ok(())
        }
        Some("stage2-profile23-devnet-execute") => {
            let arguments = args.collect::<Vec<_>>();
            let dir = stage2_results_dir()?;
            let workspace_root = dir
                .parent()
                .and_then(|results| results.parent())
                .ok_or_else(|| anyhow!("no workspace root above stage2 results"))?;
            let evidence = profile23_devnet::execute(workspace_root, &arguments)?;
            eprintln!(
                "stage2-profile23-devnet-execute: finalized {} at slot {}; immutable evidence {}",
                evidence.final_transaction.signature,
                evidence.final_transaction.finalized_slot,
                evidence.evidence_path
            );
            Ok(())
        }
        Some("stage2-profile23-devnet-upload-smoke") => {
            let arguments = args.collect::<Vec<_>>();
            let evidence = profile23_devnet::upload_smoke(&arguments)?;
            eprintln!(
                "stage2-profile23-devnet-upload-smoke: sealed {} bytes in {} uploads/{} ms; immutable evidence {}",
                evidence.proof_bytes,
                evidence.proof_upload_transaction_count,
                evidence.upload_wall_milliseconds,
                evidence.evidence_path
            );
            Ok(())
        }
        Some("stage2-profile23-devnet-close-smoke") => {
            let arguments = args.collect::<Vec<_>>();
            let evidence = profile23_devnet_close::execute(&arguments)?;
            eprintln!(
                "stage2-profile23-devnet-close-smoke: finalized {} at slot {}; refunded {} lamports; immutable evidence {}",
                evidence.signature,
                evidence.finalized_slot,
                evidence.refund_lamports,
                evidence.evidence_path
            );
            Ok(())
        }
        other => bail!(
            "usage: cargo run -p aspis-xtask -- stage2-profile23-one-transaction-release | stage2-profile23-mainnet-readiness | stage2-profile23-mainnet-execute | stage2-profile23-mainnet-cleanup | stage2-profile23-devnet-readiness | stage2-profile23-devnet-execute | stage2-profile23-devnet-upload-smoke | stage2-profile23-devnet-close-smoke (got {:?})",
            other
        ),
    }
}
