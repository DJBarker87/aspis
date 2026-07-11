mod host;
mod onchain;
mod retired_numbers;
mod stage1;
mod stage1_theta;
mod stage2;

use std::fs;
use std::path::PathBuf;

use anyhow::{anyhow, bail, Result};

pub(crate) fn host_statement_digest(seed: u64) -> [u8; 32] {
    use sha2::{Digest, Sha256};
    let mut h = Sha256::new();
    h.update(b"aspis-stage0-statement");
    h.update(seed.to_le_bytes());
    h.finalize().into()
}

fn results_dir() -> Result<PathBuf> {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let root = manifest
        .parent()
        .ok_or_else(|| anyhow!("no workspace root"))?
        .to_path_buf();
    let dir = root.join("results/stage0");
    fs::create_dir_all(&dir)?;
    Ok(dir)
}

fn stage1_results_dir() -> Result<PathBuf> {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let root = manifest
        .parent()
        .ok_or_else(|| anyhow!("no workspace root"))?
        .to_path_buf();
    let dir = root.join("results/stage1");
    fs::create_dir_all(&dir)?;
    Ok(dir)
}

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
        Some("stage0-host") => {
            let summary = host::run_stage0_host()?;
            let dir = results_dir()?;
            let path = dir.join("host_summary.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!("stage0-host: wrote {}", path.display());
            Ok(())
        }
        Some("stage0-onchain") => {
            let summary = onchain::run_stage0_onchain(false)?;
            let dir = results_dir()?;
            let path = dir.join("onchain_summary.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!("stage0-onchain: wrote {}", path.display());
            Ok(())
        }
        Some("stage0-onchain-gate") => {
            let summary = onchain::run_stage0_onchain(true)?;
            let dir = results_dir()?;
            let path = dir.join("onchain_summary.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!("stage0-onchain-gate: wrote {}", path.display());
            Ok(())
        }
        Some("stage0-onchain-g32") => {
            let summary = onchain::run_stage0_onchain_g32()?;
            let dir = results_dir()?;
            let path = dir.join("onchain_g32_summary.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!("stage0-onchain-g32: wrote {}", path.display());
            Ok(())
        }
        Some("stage0-onchain-layout-target") => {
            let summary = onchain::run_stage0_onchain_layout_target()?;
            let dir = results_dir()?;
            let path = dir.join("onchain_layout_target_summary.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!("stage0-onchain-layout-target: wrote {}", path.display());
            Ok(())
        }
        Some("stage0-onchain-profile") => {
            let summary = onchain::run_stage0_onchain_profile()?;
            let dir = results_dir()?;
            let path = dir.join("onchain_profile.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!("stage0-onchain-profile: wrote {}", path.display());
            Ok(())
        }
        Some("stage0-layout-sweep") => {
            let summary = onchain::run_layout_sweep()?;
            let dir = results_dir()?;
            let path = dir.join("layout_sweep.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!("stage0-layout-sweep: wrote {}", path.display());
            Ok(())
        }
        Some("stage0-transcript-kat") => {
            let summary = onchain::run_transcript_kat()?;
            anyhow::ensure!(
                summary.matched_on_sbf,
                "transcript KAT MISMATCH on SBF — host/chain divergence"
            );
            let dir = results_dir()?;
            let path = dir.join("transcript_kat.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!("stage0-transcript-kat: matched; wrote {}", path.display());
            Ok(())
        }
        Some("stage1-soundness-pin") => {
            let pin = stage1::soundness_pin();
            let dir = stage1_results_dir()?;
            let path = dir.join("upstream_soundness_pin.json");
            fs::write(&path, serde_json::to_string_pretty(&pin)?)?;
            eprintln!("stage1-soundness-pin: wrote {}", path.display());
            Ok(())
        }
        Some("stage1-theta-optimize") => {
            let artifact = stage1_theta::theta_optimizer_artifact();
            let dir = stage1_results_dir()?;
            let path = dir.join("theta_optimizer.json");
            fs::write(&path, format!("{}\n", serde_json::to_string_pretty(&artifact)?))?;
            eprintln!("stage1-theta-optimize: wrote {}", path.display());
            Ok(())
        }
        Some("stage1-retired-number-lint") => {
            let summary = retired_numbers::lint_retired_numbers()?;
            eprintln!(
                "stage1-retired-number-lint: {} files, {} allowed historical occurrences, 0 violations",
                summary.files_scanned,
                summary.retired_occurrences_allowed
            );
            Ok(())
        }
        Some("stage1-onchain-hardening") => {
            let summary = onchain::run_stage1_onchain_hardening()?;
            let dir = stage1_results_dir()?;
            let path = dir.join("onchain_hardening_summary.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!("stage1-onchain-hardening: wrote {}", path.display());
            Ok(())
        }
        Some("stage2-evaluator") => {
            let summary = stage2::run_evaluator_corpus()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("evaluator_corpus.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!("stage2-evaluator: wrote {}", path.display());
            Ok(())
        }
        Some("stage2-logup-compression-kat") => {
            let summary = onchain::run_logup_compression_kat()?;
            anyhow::ensure!(
                summary.matched_on_sbf,
                "LogUp compression KAT MISMATCH on SBF — host/chain divergence"
            );
            let dir = stage2_results_dir()?;
            let path = dir.join("logup_compression_kat.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!(
                "stage2-logup-compression-kat: matched; wrote {}",
                path.display()
            );
            Ok(())
        }
        Some("stage2-s2-ood-probe") => {
            let summary = onchain::run_stage2_s2_ood_probe()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("s2_ood_probe.json");
            fs::write(&path, format!("{}\n", serde_json::to_string_pretty(&summary)?))?;
            eprintln!(
                "stage2-s2-ood-probe: second-sample transcript/relation delta={} CU; wrote {}",
                summary.pcs_s2_second_ood_sample_transcript_relation_cu,
                path.display()
            );
            Ok(())
        }
        Some("stage2-v4-s2-pcs-scaffold-kat") => {
            let summary = onchain::run_transcript_kat_v4_s2_pcs_scaffold()?;
            anyhow::ensure!(
                summary.matched_on_sbf,
                "v4/s=2 PCS-scaffold transcript KAT MISMATCH on SBF"
            );
            let dir = stage2_results_dir()?;
            let path = dir.join("transcript_kat_v4_s2_pcs_scaffold.json");
            fs::write(&path, format!("{}\n", serde_json::to_string_pretty(&summary)?))?;
            eprintln!(
                "stage2-v4-s2-pcs-scaffold-kat: matched; wrote {}",
                path.display()
            );
            Ok(())
        }
        Some("stage2-v4-s2-pcs-scaffold") => {
            let summary = onchain::run_stage2_v4_s2_pcs_scaffold()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("v4_s2_pcs_scaffold_g16.json");
            fs::write(&path, format!("{}\n", serde_json::to_string_pretty(&summary)?))?;
            eprintln!(
                "stage2-v4-s2-pcs-scaffold: paired delta mean={:.1} CU; wrote {}",
                summary.paired_verify_cu_delta_mean,
                path.display()
            );
            Ok(())
        }
        Some("stage2-v4-exact-wide-reconciled") => {
            let summary = onchain::run_stage2_reconciled_exact_wide_v4_scaffold()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("v4_exact_wide_reconciled_g16.json");
            fs::write(&path, format!("{}\n", serde_json::to_string_pretty(&summary)?))?;
            eprintln!(
                "stage2-v4-exact-wide-reconciled: accepted={} cap_exhausted={}; wrote {}",
                summary.accepted_seed_count,
                summary.compute_budget_exhausted_seed_count,
                path.display()
            );
            Ok(())
        }
        Some("stage2-exact-wide-v4-diagnostic") => {
            let summary = onchain::run_stage2_exact_wide_v4_diagnostic()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("exact_wide_v4_diagnostic.json");
            fs::write(&path, format!("{}\n", serde_json::to_string_pretty(&summary)?))?;
            eprintln!(
                "stage2-exact-wide-v4-diagnostic: fused savings={} CU, C1 hash={} CU; wrote {}",
                summary.fused_dot4_savings_cu,
                summary.c1_leaf_hash_incremental_over_empty_cu,
                path.display()
            );
            Ok(())
        }
        Some("stage2-m31-circle-basis-probe") => {
            let summary = onchain::run_stage2_m31_circle_basis_probe()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("m31_circle_basis_probe.json");
            fs::write(&path, format!("{}\n", serde_json::to_string_pretty(&summary)?))?;
            eprintln!(
                "stage2-m31-circle-basis-probe: winner={} at {} CU, saving={} CU vs structured; wrote {}",
                summary.winning_rlc_mode,
                summary.winning_rlc_cu_mean,
                summary.winning_rlc_savings_vs_structured_cu,
                path.display()
            );
            Ok(())
        }
        Some("stage2-composition-probe") => {
            let summary = onchain::run_stage2_composition_probe()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("composition_probe.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!("stage2-composition-probe: wrote {}", path.display());
            Ok(())
        }
        Some("stage2-layout-probe") => {
            let summary = onchain::run_stage2_layout_probe()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("layout_probe.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!("stage2-layout-probe: wrote {}", path.display());
            Ok(())
        }
        Some("stage2-poseidon2-probe") => {
            let summary = onchain::run_stage2_poseidon2_probe()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("poseidon2_probe.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!("stage2-poseidon2-probe: wrote {}", path.display());
            Ok(())
        }
        Some("stage2-zk-kernel-probe") => {
            let summary = onchain::run_stage2_zk_kernel_probe()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("zk_kernel_probe.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!("stage2-zk-kernel-probe: wrote {}", path.display());
            Ok(())
        }
        Some("stage2-wide-rlc-probe") => {
            let summary = onchain::run_stage2_wide_rlc_probe()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("wide_rlc_probe.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!("stage2-wide-rlc-probe: wrote {}", path.display());
            Ok(())
        }
        Some("stage2-merkle-arity-probe") => {
            let summary = onchain::run_stage2_merkle_arity_probe()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("merkle_arity_probe.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!("stage2-merkle-arity-probe: wrote {}", path.display());
            Ok(())
        }
        Some("stage2-radix4-g16") => {
            let summary = onchain::run_stage2_radix4_g16()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("radix4_g16.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!("stage2-radix4-g16: wrote {}", path.display());
            Ok(())
        }
        Some("stage2-radix4-g32") => {
            let summary = onchain::run_stage2_radix4_g32()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("radix4_g32.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!("stage2-radix4-g32: wrote {}", path.display());
            Ok(())
        }
        Some("stage2-sumcheck-probe") => {
            let summary = onchain::run_stage2_sumcheck_probe()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("sumcheck_probe.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!(
                "stage2-sumcheck-probe: central={} allowance_error={}; wrote {}",
                summary.central_replaces_allowance_cu,
                summary.allowance_error_cu,
                path.display()
            );
            Ok(())
        }
        Some("stage2-query-trade-g16") => {
            let summary = onchain::run_stage2_query_trade_g16()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("query_trade_g16.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!(
                "stage2-query-trade-g16: q36->q34 saves {:.0}, q36->q32 saves {:.0}; wrote {}",
                summary.q36_to_q34_mean_saving_cu,
                summary.q36_to_q32_mean_saving_cu,
                path.display()
            );
            Ok(())
        }
        Some("stage2-variance-g16") => {
            let summary = onchain::run_stage2_variance_g16()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("variance_g16.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!(
                "stage2-variance-g16: criterion_passes={}; wrote {}",
                summary.criterion_passes,
                path.display()
            );
            Ok(())
        }
        other => bail!(
            "usage: cargo run -p aspis-xtask -- stage0-host | stage0-onchain | stage0-onchain-gate | stage0-onchain-g32 | stage0-onchain-layout-target | stage0-onchain-profile | stage0-layout-sweep | stage0-transcript-kat | stage1-soundness-pin | stage1-theta-optimize | stage1-retired-number-lint | stage1-onchain-hardening | stage2-evaluator | stage2-logup-compression-kat | stage2-s2-ood-probe | stage2-v4-s2-pcs-scaffold-kat | stage2-v4-s2-pcs-scaffold | stage2-exact-wide-v4-diagnostic | stage2-m31-circle-basis-probe | stage2-composition-probe | stage2-layout-probe | stage2-poseidon2-probe | stage2-zk-kernel-probe | stage2-wide-rlc-probe | stage2-merkle-arity-probe | stage2-radix4-g16 | stage2-radix4-g32 | stage2-variance-g16 | stage2-sumcheck-probe | stage2-query-trade-g16 (got {:?})",
            other
        ),
    }
}
