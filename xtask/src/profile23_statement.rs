//! Canonical Profile23 production-statement sidecar parsing and identity.
//!
//! This module is the single fail-closed boundary for statement sidecars used
//! by the host artifact builders, release tooling, and cluster rehearsals.

use std::{
    fs,
    path::{Path, PathBuf},
};

use anyhow::{anyhow, ensure, Context, Result};
use serde::Deserialize;
use sha2::{Digest as _, Sha256};

use aspis_prover::HOST_HASH;
use aspis_statement::{AtomicPaymentStatementV3, SpendPublic};

pub(crate) const PROFILE23_STATEMENT_ARTIFACT: &str = "profile23_production_statement";
pub(crate) const PROFILE23_STATEMENT_SELECTION_RULE: &str =
    "least Good23 selector from three post-final branches";

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Profile23StatementSidecar {
    artifact: String,
    pool_hex: String,
    sequence: u64,
    current_anchor_hex: String,
    nullifier_hex: String,
    output_commitment_hex: String,
    output_anchor_hex: String,
    asset_id: u32,
    fee: u32,
    selection_rule: String,
    witness_independent_public_metadata: bool,
}

/// A strict sidecar together with every byte- and path-level identity used by
/// Profile23 artifacts.
#[derive(Clone, Debug)]
pub(crate) struct Profile23StatementFile {
    pub(crate) statement: AtomicPaymentStatementV3,
    pub(crate) path: PathBuf,
    pub(crate) bytes: usize,
    pub(crate) sha256: String,
    pub(crate) canonical_public_input_digest: String,
}

pub(crate) fn profile23_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn decode_profile23_hex_32(field: &str, value: &str) -> Result<[u8; 32]> {
    let bytes = value.as_bytes();
    ensure!(
        bytes.len() == 64,
        "Profile23 statement sidecar {field} must contain exactly 64 lowercase hex characters"
    );
    ensure!(
        bytes
            .iter()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(byte)),
        "Profile23 statement sidecar {field} is not canonical lowercase hex"
    );
    let mut decoded = [0u8; 32];
    for (index, output) in decoded.iter_mut().enumerate() {
        let high = match bytes[index * 2] {
            b'0'..=b'9' => bytes[index * 2] - b'0',
            byte => byte - b'a' + 10,
        };
        let low = match bytes[index * 2 + 1] {
            b'0'..=b'9' => bytes[index * 2 + 1] - b'0',
            byte => byte - b'a' + 10,
        };
        *output = (high << 4) | low;
    }
    Ok(decoded)
}

fn statement_from_sidecar(sidecar: Profile23StatementSidecar) -> Result<AtomicPaymentStatementV3> {
    ensure!(
        sidecar.artifact == PROFILE23_STATEMENT_ARTIFACT,
        "Profile23 statement sidecar artifact must be {PROFILE23_STATEMENT_ARTIFACT}"
    );
    ensure!(
        sidecar.selection_rule == PROFILE23_STATEMENT_SELECTION_RULE,
        "Profile23 statement sidecar selection_rule drift"
    );
    ensure!(
        sidecar.witness_independent_public_metadata,
        "Profile23 statement sidecar must declare witness-independent public metadata"
    );

    let current_anchor_bytes =
        decode_profile23_hex_32("current_anchor_hex", &sidecar.current_anchor_hex)?;
    let nullifier_bytes = decode_profile23_hex_32("nullifier_hex", &sidecar.nullifier_hex)?;
    let output_commitment_bytes =
        decode_profile23_hex_32("output_commitment_hex", &sidecar.output_commitment_hex)?;
    let output_anchor_bytes =
        decode_profile23_hex_32("output_anchor_hex", &sidecar.output_anchor_hex)?;
    let statement = AtomicPaymentStatementV3 {
        pool: decode_profile23_hex_32("pool_hex", &sidecar.pool_hex)?,
        sequence: sidecar.sequence,
        spend: SpendPublic {
            anchor: aspis_statement::decode_digest_canonical(&current_anchor_bytes).map_err(
                |_| anyhow!("Profile23 statement sidecar current_anchor_hex is noncanonical"),
            )?,
            nullifier: aspis_statement::decode_digest_canonical(&nullifier_bytes).map_err(
                |_| anyhow!("Profile23 statement sidecar nullifier_hex is noncanonical"),
            )?,
            output_commitment: aspis_statement::decode_digest_canonical(&output_commitment_bytes)
                .map_err(|_| {
                anyhow!("Profile23 statement sidecar output_commitment_hex is noncanonical")
            })?,
            asset_id: aspis_statement::decode_asset_id_canonical(sidecar.asset_id)
                .map_err(|_| anyhow!("Profile23 statement sidecar asset_id is noncanonical"))?,
            fee: sidecar.fee,
        },
        output_anchor: aspis_statement::decode_digest_canonical(&output_anchor_bytes).map_err(
            |_| anyhow!("Profile23 statement sidecar output_anchor_hex is noncanonical"),
        )?,
    };
    aspis_statement::encode_atomic_payment_statement_v3(&statement)
        .map_err(|error| anyhow!("Profile23 statement sidecar is noncanonical: {error:?}"))?;
    Ok(statement)
}

pub(crate) fn decode_profile23_statement_sidecar(bytes: &[u8]) -> Result<AtomicPaymentStatementV3> {
    let sidecar: Profile23StatementSidecar =
        serde_json::from_slice(bytes).context("decode canonical Profile23 statement sidecar")?;
    statement_from_sidecar(sidecar)
}

pub(crate) fn canonical_profile23_public_input_digest(
    statement: &AtomicPaymentStatementV3,
) -> Result<String> {
    Ok(profile23_hex(
        &aspis_statement::atomic_payment_statement_digest_v3(statement, HOST_HASH)
            .map_err(|error| anyhow!("canonical Profile23 public-input digest: {error:?}"))?,
    ))
}

/// Resolve, read, strictly decode, and identify an explicit Profile23 sidecar.
/// Relative paths are resolved against `root`; absolute paths retain the
/// existing artifact-builder semantics.
pub(crate) fn load_profile23_statement_file(
    root: &Path,
    supplied_path: &Path,
) -> Result<Profile23StatementFile> {
    let path = if supplied_path.is_absolute() {
        supplied_path.to_path_buf()
    } else {
        root.join(supplied_path)
    };
    let path = fs::canonicalize(&path)
        .with_context(|| format!("resolve Profile23 statement sidecar {}", path.display()))?;
    let bytes = fs::read(&path)
        .with_context(|| format!("read Profile23 statement sidecar {}", path.display()))?;
    let statement = decode_profile23_statement_sidecar(&bytes).with_context(|| {
        format!(
            "decode canonical Profile23 statement sidecar {}",
            path.display()
        )
    })?;
    Ok(Profile23StatementFile {
        canonical_public_input_digest: canonical_profile23_public_input_digest(&statement)?,
        statement,
        path,
        bytes: bytes.len(),
        sha256: profile23_hex(&Sha256::digest(&bytes)),
    })
}

pub(crate) fn profile23_recorded_path(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .display()
        .to_string()
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicU64, Ordering};

    use aspis_core::field::M31;
    use serde_json::{json, Value};

    use super::*;

    static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

    struct TempRoot(PathBuf);

    impl TempRoot {
        fn new() -> Self {
            let suffix = NEXT_TEMP.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "aspis-shared-profile23-statement-{}-{suffix}",
                std::process::id()
            ));
            fs::create_dir_all(&path).unwrap();
            Self(path)
        }
    }

    impl Drop for TempRoot {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn statement() -> AtomicPaymentStatementV3 {
        let digest = |seed: u32| core::array::from_fn(|index| M31(seed + index as u32));
        AtomicPaymentStatementV3 {
            pool: [0x42; 32],
            sequence: 91,
            spend: SpendPublic {
                anchor: digest(11),
                nullifier: digest(31),
                output_commitment: digest(51),
                asset_id: M31(17),
                fee: 1,
            },
            output_anchor: digest(71),
        }
    }

    fn sidecar(statement: &AtomicPaymentStatementV3) -> Value {
        json!({
            "artifact": PROFILE23_STATEMENT_ARTIFACT,
            "pool_hex": profile23_hex(&statement.pool),
            "sequence": statement.sequence,
            "current_anchor_hex": profile23_hex(
                &aspis_statement::encode_digest_canonical(&statement.spend.anchor)
            ),
            "nullifier_hex": profile23_hex(
                &aspis_statement::encode_digest_canonical(&statement.spend.nullifier)
            ),
            "output_commitment_hex": profile23_hex(
                &aspis_statement::encode_digest_canonical(&statement.spend.output_commitment)
            ),
            "output_anchor_hex": profile23_hex(
                &aspis_statement::encode_digest_canonical(&statement.output_anchor)
            ),
            "asset_id": statement.spend.asset_id.0,
            "fee": statement.spend.fee,
            "selection_rule": PROFILE23_STATEMENT_SELECTION_RULE,
            "witness_independent_public_metadata": true,
        })
    }

    #[test]
    fn canonical_sidecar_reconstructs_every_public_field() {
        let expected = statement();
        let bytes = serde_json::to_vec_pretty(&sidecar(&expected)).unwrap();

        let decoded = decode_profile23_statement_sidecar(&bytes).unwrap();
        assert_eq!(decoded, expected);
        assert_eq!(
            canonical_profile23_public_input_digest(&decoded)
                .unwrap()
                .len(),
            64
        );
    }

    #[test]
    fn rejects_noncanonical_fields_and_schema_drift() {
        let statement = statement();

        let mut uppercase = sidecar(&statement);
        uppercase["pool_hex"] = Value::String("AA".repeat(32));
        let error = decode_profile23_statement_sidecar(&serde_json::to_vec(&uppercase).unwrap())
            .unwrap_err();
        assert!(error.to_string().contains("canonical lowercase hex"));

        let mut noncanonical_digest = sidecar(&statement);
        let mut digest = [0u8; 32];
        digest[..4].copy_from_slice(&aspis_core::field::P.to_le_bytes());
        noncanonical_digest["current_anchor_hex"] = Value::String(profile23_hex(&digest));
        let error =
            decode_profile23_statement_sidecar(&serde_json::to_vec(&noncanonical_digest).unwrap())
                .unwrap_err();
        assert!(error
            .to_string()
            .contains("current_anchor_hex is noncanonical"));

        let mut invalid_asset = sidecar(&statement);
        invalid_asset["asset_id"] = Value::from(aspis_core::field::P);
        let error =
            decode_profile23_statement_sidecar(&serde_json::to_vec(&invalid_asset).unwrap())
                .unwrap_err();
        assert!(error.to_string().contains("asset_id is noncanonical"));

        let mut invalid_fee = sidecar(&statement);
        invalid_fee["fee"] = Value::from(aspis_statement::VALUE_LIMIT);
        let error = decode_profile23_statement_sidecar(&serde_json::to_vec(&invalid_fee).unwrap())
            .unwrap_err();
        assert!(error.to_string().contains("FeeOutOfRange"));

        let mut wrong_artifact = sidecar(&statement);
        wrong_artifact["artifact"] = Value::String("profile23_statement".to_owned());
        let error =
            decode_profile23_statement_sidecar(&serde_json::to_vec(&wrong_artifact).unwrap())
                .unwrap_err();
        assert!(error.to_string().contains("artifact must be"));

        let mut wrong_rule = sidecar(&statement);
        wrong_rule["selection_rule"] = Value::String("first branch".to_owned());
        let error = decode_profile23_statement_sidecar(&serde_json::to_vec(&wrong_rule).unwrap())
            .unwrap_err();
        assert!(error.to_string().contains("selection_rule drift"));

        let mut witness_dependent = sidecar(&statement);
        witness_dependent["witness_independent_public_metadata"] = Value::Bool(false);
        let error =
            decode_profile23_statement_sidecar(&serde_json::to_vec(&witness_dependent).unwrap())
                .unwrap_err();
        assert!(error
            .to_string()
            .contains("witness-independent public metadata"));

        let mut unknown_field = sidecar(&statement);
        unknown_field["unreviewed"] = Value::Bool(true);
        let error =
            decode_profile23_statement_sidecar(&serde_json::to_vec(&unknown_field).unwrap())
                .unwrap_err();
        assert!(format!("{error:#}").contains("unknown field"));
    }

    #[test]
    fn loaded_file_pins_canonical_path_raw_sha_and_statement_digest() {
        let root = TempRoot::new();
        let canonical_root = fs::canonicalize(&root.0).unwrap();
        let expected = statement();
        let bytes = serde_json::to_vec_pretty(&sidecar(&expected)).unwrap();
        let relative = PathBuf::from("statement.json");
        fs::write(root.0.join(&relative), &bytes).unwrap();

        let loaded = load_profile23_statement_file(&canonical_root, &relative).unwrap();
        assert_eq!(loaded.statement, expected);
        assert_eq!(
            loaded.path,
            fs::canonicalize(root.0.join("statement.json")).unwrap()
        );
        assert_eq!(loaded.sha256, profile23_hex(&Sha256::digest(&bytes)));
        assert_eq!(loaded.bytes, bytes.len());
        assert_eq!(
            loaded.canonical_public_input_digest,
            canonical_profile23_public_input_digest(&expected).unwrap()
        );
        assert_eq!(
            profile23_recorded_path(&canonical_root, &loaded.path),
            "statement.json"
        );
    }
}
