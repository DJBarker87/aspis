use std::{
    env, fs,
    path::{Path, PathBuf},
    str::FromStr,
};

use anyhow::{ensure, Context, Result};
use base64::{engine::general_purpose::STANDARD as BASE64, Engine as _};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use sha2::{Digest as _, Sha256};
use solana_program::pubkey::Pubkey;

#[derive(Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
struct GenesisAccount {
    data: (String, String),
    executable: bool,
    lamports: u64,
    owner: String,
    rent_epoch: u64,
    space: usize,
}

#[derive(Serialize)]
struct KeyedGenesisAccount<'a> {
    pubkey: &'a str,
    account: &'a GenesisAccount,
}

fn write_keyed_account(path: &Path, pubkey: &str, account: &GenesisAccount) -> Result<()> {
    fs::write(
        path,
        serde_json::to_vec_pretty(&KeyedGenesisAccount { pubkey, account })?,
    )?;
    Ok(())
}

fn resolve(root: &Path, relative: &str) -> Result<PathBuf> {
    ensure!(
        !relative.starts_with('/') && !relative.contains(".."),
        "unsafe source path"
    );
    Ok(root.join(relative))
}

fn main() -> Result<()> {
    let withdrawal_cpi_test_mode = env::var("ASPIS_V7_LIVE_WITHDRAWAL_CPI_CASE").ok();
    ensure!(
        withdrawal_cpi_test_mode
            .as_deref()
            .is_none_or(|mode| mode == "frozen-destination"),
        "unsupported withdrawal CPI test mode"
    );
    let mut args = env::args_os().skip(1);
    let repo = PathBuf::from(args.next().context(
        "usage: prepare-live-genesis <repo-root> <config.json> <payer-pubkey> <source-authority-pubkey> <new-output-dir>",
    )?);
    let config_path = PathBuf::from(args.next().context("missing config")?);
    let payer = Pubkey::from_str(&args.next().context("missing payer")?.to_string_lossy())
        .context("invalid payer")?;
    let source_authority = Pubkey::from_str(
        &args
            .next()
            .context("missing source authority")?
            .to_string_lossy(),
    )
    .context("invalid source authority")?;
    ensure!(source_authority != payer, "source authority aliases payer");
    let output = PathBuf::from(args.next().context("missing output directory")?);
    ensure!(args.next().is_none(), "unexpected extra argument");
    ensure!(!output.exists(), "refusing to overwrite genesis output");
    let config: Value = serde_json::from_slice(&fs::read(config_path)?)?;
    ensure!(
        config["mainnetReady"] == false
            && config["identitySet"]["auditOnly"] == true
            && config["disposableLiveGenesis"]["enabledOnlyWithDisposableAcknowledgement"] == true,
        "live genesis is not explicitly disposable/audit-only"
    );
    fs::create_dir(&output)?;
    let mint_id = config["disposableLiveGenesis"]["mint"]["id"]
        .as_str()
        .context("missing mint id")?;
    let mint_source = resolve(
        &repo,
        config["disposableLiveGenesis"]["mint"]["source"]
            .as_str()
            .context("missing mint source")?,
    )?;
    let mut mint: GenesisAccount = serde_json::from_slice(&fs::read(mint_source)?)?;
    ensure!(
        mint.owner == "TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA",
        "wrong mint owner"
    );
    let mut mint_data = BASE64.decode(&mint.data.0)?;
    ensure!(
        mint.data.1 == "base64" && mint_data.len() == 82 && mint_data[45] == 1,
        "source is not an initialized legacy SPL mint"
    );
    mint_data[..4].copy_from_slice(&1u32.to_le_bytes());
    mint_data[4..36].copy_from_slice(&payer.to_bytes());
    mint_data[36..44].fill(0);
    mint_data[46..50].fill(0);
    mint_data[50..82].fill(0);
    mint.data.0 = BASE64.encode(&mint_data);
    let mint_output = output.join("mint.json");
    write_keyed_account(&mint_output, mint_id, &mint)?;
    let mut accounts = vec![serde_json::json!({
        "kind":"disposable-mint-with-ephemeral-authority", "address":mint_id,
        "file":mint_output, "dataSha256":format!("{:x}", Sha256::digest(&mint_data))
    })];
    for (field, address_byte, amount, filename) in [
        ("sourceTokenAccount", 0x43, 1_000_u64, "source-token.json"),
        (
            "withdrawalDestinationTokenAccount",
            0x46,
            0_u64,
            "withdrawal-destination-token.json",
        ),
    ] {
        let address = config["disposableLiveGenesis"][field]
            .as_str()
            .with_context(|| format!("missing {field}"))?;
        ensure!(
            Pubkey::from_str(address)? == Pubkey::new_from_array([address_byte; 32]),
            "unexpected disposable token account identity for {field}"
        );
        let mut data = vec![0_u8; 165];
        data[..32].copy_from_slice(&Pubkey::from_str(mint_id)?.to_bytes());
        data[32..64].copy_from_slice(&source_authority.to_bytes());
        data[64..72].copy_from_slice(&amount.to_le_bytes());
        let frozen_destination = field == "withdrawalDestinationTokenAccount"
            && withdrawal_cpi_test_mode.as_deref() == Some("frozen-destination");
        data[108] = if frozen_destination { 2 } else { 1 };
        let account = GenesisAccount {
            data: (BASE64.encode(&data), "base64".to_owned()),
            executable: false,
            lamports: 2_039_280,
            owner: "TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA".to_owned(),
            rent_epoch: 0,
            space: data.len(),
        };
        let destination = output.join(filename);
        write_keyed_account(&destination, address, &account)?;
        accounts.push(serde_json::json!({
            "kind":"disposable-token-account-with-ephemeral-owner",
            "address":address,
            "file":destination,
            "amount":amount,
            "accountState":if frozen_destination { "frozen" } else { "initialized" },
            "dataSha256":format!("{:x}", Sha256::digest(&data))
        }));
    }
    for (index, binding) in config["disposableLiveGenesis"]["bindingAccounts"]
        .as_array()
        .context("missing binding accounts")?
        .iter()
        .enumerate()
    {
        let id = binding["id"].as_str().context("missing binding id")?;
        let source = resolve(
            &repo,
            binding["source"]
                .as_str()
                .context("missing binding source")?,
        )?;
        let raw = fs::read(&source)?;
        let decoded: GenesisAccount = serde_json::from_slice(&raw)?;
        let data = BASE64.decode(&decoded.data.0)?;
        let expected = config["identitySet"]["bindingAccounts"]
            .as_array()
            .context("missing expected bindings")?
            .iter()
            .find(|expected| expected["id"] == id)
            .context("unapproved binding id")?;
        ensure!(decoded.owner == expected["owner"], "binding owner mismatch");
        ensure!(
            format!("{:x}", Sha256::digest(&data)) == expected["dataSha256"],
            "binding data hash mismatch"
        );
        let destination = output.join(format!("binding-{index}.json"));
        write_keyed_account(&destination, id, &decoded)?;
        accounts.push(serde_json::json!({
            "kind":"audit-only-registry-binding", "address":id, "file":destination,
            "dataSha256":expected["dataSha256"]
        }));
    }
    println!(
        "{}",
        serde_json::to_string(&serde_json::json!({
            "schema":"aspis.v7.disposable-live-genesis.v1", "auditOnly":true,
            "withdrawalCpiTestMode":withdrawal_cpi_test_mode,
            "ephemeralMintAuthority":payer.to_string(),
            "ephemeralTokenAuthority":source_authority.to_string(), "accounts":accounts
        }))?
    );
    Ok(())
}
