mod host;
mod onchain;
mod stage1;
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
        other => bail!(
            "usage: cargo run -p aspis-xtask -- stage0-host | stage0-onchain | stage0-onchain-gate | stage0-onchain-g32 | stage0-onchain-layout-target | stage0-onchain-profile | stage0-layout-sweep | stage0-transcript-kat | stage1-soundness-pin | stage1-onchain-hardening | stage2-evaluator | stage2-composition-probe | stage2-layout-probe | stage2-poseidon2-probe (got {:?})",
            other
        ),
    }
}
