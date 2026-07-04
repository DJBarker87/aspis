mod host;
mod onchain;

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
            let summary = onchain::run_stage0_onchain()?;
            let dir = results_dir()?;
            let path = dir.join("onchain_summary.json");
            fs::write(&path, serde_json::to_string_pretty(&summary)?)?;
            eprintln!("stage0-onchain: wrote {}", path.display());
            Ok(())
        }
        other => bail!(
            "usage: cargo run -p aspis-xtask -- stage0-host | stage0-onchain (got {:?})",
            other
        ),
    }
}
