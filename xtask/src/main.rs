mod host;
mod onchain;
mod profile23_devnet;
mod profile23_devnet_close;
mod profile23_mainnet;
mod profile23_mainnet_cleanup;
mod profile23_mainnet_journal;
mod profile23_mainnet_loader;
mod profile23_release;
mod profile23_statement;
mod retired_numbers;
mod stage1;
mod stage1_theta;
mod stage2;
mod stage2_rate16_soundness;

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
        Some("stage2-two-point-batching-probe") => {
            let summary = onchain::run_stage2_two_point_batching_probe()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("two_point_batching_probe.json");
            fs::write(&path, format!("{}\n", serde_json::to_string_pretty(&summary)?))?;
            eprintln!(
                "stage2-two-point-batching-probe: measured {} neutral modes; wrote {}",
                summary.variants.len(),
                path.display()
            );
            Ok(())
        }
        Some("stage2-m31-fresh-kappa-sbf") => {
            let summary = onchain::run_stage2_m31_fresh_kappa_sbf()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("m31_circle_fresh_kappa_sbf.json");
            fs::write(&path, format!("{}\n", serde_json::to_string_pretty(&summary)?))?;
            eprintln!(
                "stage2-m31-fresh-kappa-sbf: mean={} CU over {} runs; wrote {}",
                summary.simulation_cu_mean,
                summary.simulation_cu.len(),
                path.display()
            );
            Ok(())
        }
        Some("stage2-m31-johnson-sbf") => {
            let summary = onchain::run_stage2_m31_johnson_sbf()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("m31_circle_johnson_q74_g32_sbf.json");
            fs::write(&path, format!("{}\n", serde_json::to_string_pretty(&summary)?))?;
            eprintln!(
                "stage2-m31-johnson-sbf: reconciled={} CU (headroom={}); wrote {}",
                summary.reconciled_integrated_cu,
                summary.headroom_vs_1_4m_cu,
                path.display()
            );
            Ok(())
        }
        Some("stage2-m31-rate16-sbf") => {
            let summary = onchain::run_stage2_m31_rate16_sbf()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("m31_circle_johnson_b4_q36_g32_sbf.json");
            fs::write(&path, format!("{}\n", serde_json::to_string_pretty(&summary)?))?;
            eprintln!(
                "stage2-m31-rate16-sbf: selected={} CU (headroom={}); wrote {}",
                summary.selected_integrated_cu,
                summary.headroom_vs_1_4m_cu,
                path.display()
            );
            Ok(())
        }
        Some("stage2-m31-rate16-hardened-sbf") => {
            let summary = onchain::run_stage2_m31_rate16_hardened_sbf()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("m31_circle_johnson_b4_q36_g36_foldpow_sbf.json");
            fs::write(&path, format!("{}\n", serde_json::to_string_pretty(&summary)?))?;
            eprintln!(
                "stage2-m31-rate16-hardened-sbf: selected={} CU (headroom={}); wrote {}",
                summary.selected_integrated_cu,
                summary.headroom_vs_1_4m_cu,
                path.display()
            );
            Ok(())
        }
        Some("stage2-rate16-soundness") => {
            let artifact = stage2_rate16_soundness::rate16_soundness_artifact();
            let dir = stage2_results_dir()?;
            let path = dir.join("rate16_hardened_soundness.json");
            fs::write(&path, format!("{}\n", serde_json::to_string_pretty(&artifact)?))?;
            eprintln!("stage2-rate16-soundness: wrote {}", path.display());
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
        Some("stage2-final-payment-v4-kat") => {
            let summary = onchain::run_final_payment_transcript_kat_v4()?;
            anyhow::ensure!(
                summary.matched_on_sbf,
                "final payment-v4 transcript KAT MISMATCH on SBF"
            );
            let dir = stage2_results_dir()?;
            let path = dir.join("transcript_kat_final_payment_v4.json");
            fs::write(&path, format!("{}\n", serde_json::to_string_pretty(&summary)?))?;
            eprintln!("stage2-final-payment-v4-kat: matched; wrote {}", path.display());
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
        Some("stage2-hvzk-whir-mask-probe") => {
            let summary = onchain::run_stage2_hvzk_whir_mask_probe()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("hvzk_whir_mask_probe.json");
            fs::write(&path, format!("{}\n", serde_json::to_string_pretty(&summary)?))?;
            eprintln!(
                "stage2-hvzk-whir-mask-probe: measured {} rows; wrote {}",
                summary.rows.len(),
                path.display()
            );
            Ok(())
        }
        Some("stage2-radix8-merkle-probe") => {
            let summary = onchain::run_stage2_radix8_merkle_probe()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("radix8_merkle_probe.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!("stage2-radix8-merkle-probe: wrote {}", path.display());
            Ok(())
        }
        Some("stage2-merkle-forest-probe") => {
            let summary = onchain::run_stage2_merkle_forest_probe()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("merkle_forest_probe.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!("stage2-merkle-forest-probe: wrote {}", path.display());
            Ok(())
        }
        Some("stage2-layer0-dot-width-probe") => {
            let summary = onchain::run_stage2_layer0_dot_width_probe()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("layer0_dot_width_probe.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!("stage2-layer0-dot-width-probe: wrote {}", path.display());
            Ok(())
        }
        Some("stage2-state-only-helper-dot2-probe") => {
            let summary = onchain::run_stage2_state_only_helper_dot2_probe()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("state_only_helper_dot2_probe.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!(
                "stage2-state-only-helper-dot2-probe: savings={} CU; wrote {}",
                summary.measured_savings_cu,
                path.display()
            );
            Ok(())
        }
        Some("stage2-state-only-helper-dot3-probe") => {
            let summary = onchain::run_stage2_state_only_helper_dot3_probe()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("state_only_helper_dot3_probe.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!(
                "stage2-state-only-helper-dot3-probe: savings={} CU; wrote {}",
                summary.measured_savings_cu,
                path.display()
            );
            Ok(())
        }
        Some("stage2-state-only-fold-polynomial-probe") => {
            let summary = onchain::run_stage2_state_only_fold_polynomial_probe()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("state_only_fold_polynomial_probe.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!(
                "stage2-state-only-fold-polynomial-probe: savings={} CU; wrote {}",
                summary.measured_savings_cu,
                path.display()
            );
            Ok(())
        }
        Some("stage2-atomic-routing-partition-probe") => {
            let summary = onchain::run_stage2_atomic_routing_partition_probe()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("atomic_routing_partition_probe.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!(
                "stage2-atomic-routing-partition-probe: savings={} CU; wrote {}",
                summary.optimized_savings_cu,
                path.display()
            );
            Ok(())
        }
        Some("stage2-atomic-profile20-cost") => {
            let summary = onchain::run_stage2_atomic_profile20_cost_candidate()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("atomic_state_only_profile20_cost.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!(
                "stage2-atomic-profile20-cost: overlap={} CU; wrote {}",
                summary.overlap_substituted_ledger.overlap_reconciled_total_cu,
                path.display()
            );
            Ok(())
        }
        Some("stage2-atomic-profile20-acceptance") => {
            let summary = onchain::run_stage2_atomic_profile20_acceptance()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("atomic_state_only_profile20_acceptance.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!(
                "stage2-atomic-profile20-acceptance: literal={:?} CU; wrote {}",
                summary.literal_simulation_cu,
                path.display()
            );
            Ok(())
        }
        Some("stage2-atomic-profile20-mutation") => {
            let summary = onchain::run_stage2_atomic_profile20_mutation()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("atomic_state_only_profile20_mutation.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!(
                "stage2-atomic-profile20-mutation: paths={} CU; wrote {}",
                summary
                    .paths
                    .iter()
                    .map(|path| path.literal_simulation_cu.to_string())
                    .collect::<Vec<_>>()
                    .join(","),
                path.display()
            );
            Ok(())
        }
        Some("stage2-atomic-profile21-acceptance") => {
            let summary = onchain::run_stage2_atomic_profile21_acceptance()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("atomic_state_only_profile21_acceptance.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!(
                "stage2-atomic-profile21-acceptance: literal={} CU; wrote {}",
                summary.literal_simulation_cu,
                path.display()
            );
            Ok(())
        }
        Some("stage2-atomic-profile21-mutation") => {
            let summary = onchain::run_stage2_atomic_profile21_mutation()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("atomic_state_only_profile21_mutation.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!(
                "stage2-atomic-profile21-mutation: paths={} CU; wrote {}",
                summary
                    .paths
                    .iter()
                    .map(|path| path.literal_simulation_cu.to_string())
                    .collect::<Vec<_>>()
                    .join(","),
                path.display()
            );
            Ok(())
        }
        Some("stage2-atomic-profile22-acceptance") => {
            let summary = onchain::run_stage2_atomic_profile22_acceptance()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("atomic_state_only_profile22_acceptance.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!(
                "stage2-atomic-profile22-acceptance: literal={} CU; wrote {}",
                summary.literal_simulation_cu,
                path.display()
            );
            Ok(())
        }
        Some("stage2-atomic-profile22-mutation") => {
            let summary = onchain::run_stage2_atomic_profile22_mutation()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("atomic_state_only_profile22_mutation.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!(
                "stage2-atomic-profile22-mutation: paths={} CU; wrote {}",
                summary
                    .paths
                    .iter()
                    .map(|path| path.literal_simulation_cu.to_string())
                    .collect::<Vec<_>>()
                    .join(","),
                path.display()
            );
            Ok(())
        }
        Some("stage2-atomic-profile23-acceptance") => {
            let summary = onchain::run_stage2_atomic_profile23_acceptance()?;
            let dir = stage2_results_dir()?;
            let path = dir.join(if summary.proof_source_override {
                "atomic_state_only_profile23_acceptance_production_mined.json"
            } else {
                "atomic_state_only_profile23_acceptance.json"
            });
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!(
                "stage2-atomic-profile23-acceptance: literal={} CU; wrote {}",
                summary.literal_simulation_cu,
                path.display()
            );
            Ok(())
        }
        Some("stage2-atomic-profile23-mutation") => {
            let summary = onchain::run_stage2_atomic_profile23_mutation()?;
            let dir = stage2_results_dir()?;
            let path = dir.join(if summary.proof_source_override {
                "atomic_state_only_profile23_mutation_production_mined.json"
            } else {
                "atomic_state_only_profile23_mutation.json"
            });
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            let diagnostic_paths = summary
                .paths
                .iter()
                .map(|path| path.literal_simulation_cu.to_string())
                .collect::<Vec<_>>()
                .join(",");
            let production_paths = summary
                .production_paths
                .iter()
                .map(|path| path.literal_tag65_simulation_cu.to_string())
                .collect::<Vec<_>>()
                .join(",");
            eprintln!(
                "stage2-atomic-profile23-mutation: diagnostic_tag61_paths={} CU; production_tag65_paths={} CU; wrote {}",
                diagnostic_paths,
                if production_paths.is_empty() {
                    "not-run"
                } else {
                    &production_paths
                },
                path.display()
            );
            Ok(())
        }
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
        Some("stage2-state-only-relation-structural-probe") => {
            let summary = onchain::run_stage2_state_only_relation_structural_probe()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("state_only_relation_structural_probe.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!(
                "stage2-state-only-relation-structural-probe: savings={} CU; wrote {}",
                summary.optimized_savings_cu,
                path.display()
            );
            Ok(())
        }
        Some("stage2-state-only-masked-switch-profile21-probe") => {
            let summary =
                onchain::run_stage2_state_only_masked_switch_profile21_probe()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("state_only_masked_switch_profile21_probe.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!(
                "stage2-state-only-masked-switch-profile21-probe: mean={} CU; wrote {}",
                summary.simulation_cu_mean,
                path.display()
            );
            Ok(())
        }
        Some("stage2-state-only-private-merkle-salt-probe") => {
            let summary = onchain::run_stage2_state_only_private_merkle_salt_probe()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("state_only_private_merkle_salt_probe.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!(
                "stage2-state-only-private-merkle-salt-probe: widening={} CU salt={} CU net={} CU; wrote {}",
                summary.shared_c2_leaf_widening_delta_cu,
                summary.all_five_tree_private_salt_delta_cu,
                summary.shared_root_net_saving_after_salts_cu,
                path.display()
            );
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
        Some("stage2-payment-statement-v4") => {
            let summary = onchain::run_stage2_payment_statement_v4()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("payment_statement_v4.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!(
                "stage2-payment-statement-v4: mean={:.0} CU; wrote {}",
                summary.simulation_cu_mean,
                path.display()
            );
            Ok(())
        }
        Some("stage2-payment-hiding-placement-v4") => {
            let summary = onchain::run_stage2_payment_hiding_placement_v4()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("payment_hiding_placement_v4.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!(
                "stage2-payment-hiding-placement-v4: separate-in_batch={} CU; wrote {}",
                summary.separate_minus_in_batch_cu,
                path.display()
            );
            Ok(())
        }
        Some("stage2-payment-hiding-aggregate-v4") => {
            let summary = onchain::run_stage2_payment_hiding_aggregate_v4()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("payment_hiding_aggregate_v4.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!(
                "stage2-payment-hiding-aggregate-v4: mean={:.0} CU; wrote {}",
                summary.simulation_cu_mean,
                path.display()
            );
            Ok(())
        }
        Some("stage2-payment-hiding-profile15") => {
            let summary = onchain::run_stage2_payment_hiding_profile15()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("payment_hiding_profile15.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!(
                "stage2-payment-hiding-profile15: reconciled={} CU (headroom={}); wrote {}",
                summary.overlap_subtracted_integrated_cu,
                summary.headroom_under_1_4m,
                path.display()
            );
            Ok(())
        }
        Some("stage2-state-only-width28") => {
            let summary = onchain::run_stage2_state_only_width28()?;
            let dir = stage2_results_dir()?;
            let path = dir.join("state_only_width28_global_inactive.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            for row in &summary.rows {
                eprintln!(
                    "stage2-state-only-width28: {} q{} proof={} CU={:?} error={:?}",
                    row.rho,
                    row.query_count,
                    row.proof_bytes,
                    row.simulation_cu,
                    row.simulation_error,
                );
            }
            eprintln!("stage2-state-only-width28: wrote {}", path.display());
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
            "usage: cargo run -p aspis-xtask -- stage0-host | stage0-onchain | stage0-onchain-gate | stage0-onchain-g32 | stage0-onchain-layout-target | stage0-onchain-profile | stage0-layout-sweep | stage0-transcript-kat | stage1-soundness-pin | stage1-theta-optimize | stage1-retired-number-lint | stage1-onchain-hardening | stage2-evaluator | stage2-logup-compression-kat | stage2-s2-ood-probe | stage2-v4-s2-pcs-scaffold-kat | stage2-v4-s2-pcs-scaffold | stage2-exact-wide-v4-diagnostic | stage2-m31-circle-basis-probe | stage2-m31-fresh-kappa-sbf | stage2-m31-johnson-sbf | stage2-m31-rate16-sbf | stage2-m31-rate16-hardened-sbf | stage2-rate16-soundness | stage2-composition-probe | stage2-layout-probe | stage2-poseidon2-probe | stage2-zk-kernel-probe | stage2-wide-rlc-probe | stage2-merkle-arity-probe | stage2-hvzk-whir-mask-probe | stage2-radix8-merkle-probe | stage2-merkle-forest-probe | stage2-layer0-dot-width-probe | stage2-state-only-helper-dot2-probe | stage2-state-only-helper-dot3-probe | stage2-state-only-fold-polynomial-probe | stage2-atomic-routing-partition-probe | stage2-atomic-profile20-cost | stage2-atomic-profile20-acceptance | stage2-atomic-profile20-mutation | stage2-atomic-profile21-acceptance | stage2-atomic-profile21-mutation | stage2-atomic-profile22-acceptance | stage2-atomic-profile22-mutation | stage2-atomic-profile23-acceptance | stage2-atomic-profile23-mutation | stage2-profile23-one-transaction-release | stage2-profile23-mainnet-readiness | stage2-profile23-mainnet-execute | stage2-profile23-mainnet-cleanup | stage2-profile23-devnet-readiness | stage2-profile23-devnet-execute | stage2-profile23-devnet-upload-smoke | stage2-profile23-devnet-close-smoke | stage2-state-only-relation-structural-probe | stage2-state-only-masked-switch-profile21-probe | stage2-state-only-private-merkle-salt-probe | stage2-radix4-g16 | stage2-radix4-g32 | stage2-variance-g16 | stage2-sumcheck-probe | stage2-payment-statement-v4 | stage2-payment-hiding-profile15 | stage2-state-only-width28 | stage2-query-trade-g16 (got {:?})",
            other
        ),
    }
}
