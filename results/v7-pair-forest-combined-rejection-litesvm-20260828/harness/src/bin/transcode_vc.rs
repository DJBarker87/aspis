use std::{env, fs, path::PathBuf};

use anyhow::{bail, Context, Result};
use aspis_core::v7_fixed_canonical_audit::transcode_tag73_to_canonical_fixed;

fn main() -> Result<()> {
    let args = env::args().skip(1).collect::<Vec<_>>();
    if args.len() != 3 {
        bail!("usage: transcode_vc <packed-proof.bin> <canonical-proof.bin> <frontier-nodes>");
    }
    let input = PathBuf::from(&args[0]);
    let output = PathBuf::from(&args[1]);
    let frontier_nodes = args[2].parse::<usize>().context("parse frontier nodes")?;
    let packed = fs::read(&input).with_context(|| format!("read {}", input.display()))?;
    let canonical = transcode_tag73_to_canonical_fixed(&packed, frontier_nodes)
        .map_err(|error| anyhow::anyhow!("canonical transcode failed: {error:?}"))?;
    if output.exists() {
        bail!("refusing to overwrite {}", output.display());
    }
    fs::write(&output, &canonical).with_context(|| format!("write {}", output.display()))?;
    println!("packed_bytes={}", packed.len());
    println!("canonical_bytes={}", canonical.len());
    println!("delta_bytes={}", canonical.len() - packed.len());
    Ok(())
}
