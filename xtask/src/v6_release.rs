//! Honest V6 proof construction and release evidence.

use std::{
    collections::BTreeMap,
    fs::{self, OpenOptions},
    io::Write,
    path::{Path, PathBuf},
    str::FromStr,
};

use anyhow::{anyhow, ensure, Context, Result};
use aspis_core::{
    field::{M31, P},
    v6_onefold::{
        V6_BODY_WITHOUT_FRONTIERS, V6_C1_LIMBS_PER_QUERY, V6_C1_PACKED_BYTES_PER_QUERY,
        V6_C2_LIMBS_PER_QUERY, V6_C2_PACKED_BYTES_PER_QUERY, V6_FINAL_QM31_OFFSET,
        V6_FIXED_PACKED_FIELD_BYTES, V6_FIXED_QM31_VALUES, V6_FRONTIER_CAP_PER_TREE,
        V6_INACTIVE_CLAIM_QM31_OFFSET, V6_OOD_QM31_OFFSET, V6_POINT_CLAIMS_QM31_OFFSET,
        V6_PRIVATE_SALT_BYTES, V6_QUERY_BYTES, V6_QUERY_COUNT, V6_RELATION_QM31_OFFSET,
        V6_SEMANTIC_QM31_OFFSET,
    },
    v7_onefold::{
        V7_COMPACT_BODY_WITHOUT_FRONTIERS, V7_COMPACT_C1_BYTES_PER_QUERY,
        V7_COMPACT_C2_BYTES_PER_QUERY, V7_COMPACT_DIGEST_BYTES, V7_COMPACT_FRONTIER_CAP_PER_TREE,
        V7_COMPACT_PRIVATE_SALT_BYTES, V7_COMPACT_QUERY_BYTES,
    },
};
use aspis_prover::{
    state_only_entropy::{DurableStateOnlyMaskNonceStore, StateOnlyAttemptSecrets},
    v6_onefold_prover::{
        build_v6_onefold_proof_production, build_v7_compact_onefold_proof_production,
        verify_v6_onefold_proof_production, verify_v7_compact_onefold_proof_production,
        V6ProverContext, V7ProverContext,
    },
    HOST_HASH,
};
use aspis_statement::{
    atomic_deployment_domain, atomic_state_only_trace::atomic_merkle_root_v3, derive_nullifier,
    derive_owner_key, encode_digest_canonical, note_commitment, output_commitment,
    AtomicPaymentStatementV4, Digest, MerklePath, SpendPublic, SpendWitness,
};
use aspis_verifier::{
    atomic_payment::{
        atomic_nullifier_address, AtomicPoolStateV2, ATOMIC_NULLIFIER_MARKER_LEN,
        ATOMIC_POOL_STATE_LEN,
    },
    v6_transaction::{V6_ATOMIC_WIRE_BYTES, V6_PRODUCTION_TAG, V6_RELEASE_BINDING},
    v7_transaction::{V7_ATOMIC_WIRE_BYTES, V7_PRODUCTION_TAG, V7_RELEASE_BINDING},
    PROOF_ACCOUNT_HEADER_LEN,
};
use serde::{Deserialize, Serialize};
use serde_json::json;
use sha2::{Digest as _, Sha256};
use solana_sdk::pubkey::Pubkey;

#[derive(Clone, Debug, Serialize)]
pub(crate) struct V6HonestProofOutcome {
    pub(crate) proof_bytes: usize,
    pub(crate) selector: u8,
    pub(crate) compact_counter: u8,
    pub(crate) frontier_nodes: usize,
    pub(crate) metadata_path: PathBuf,
}

#[derive(Clone, Debug, Serialize)]
pub(crate) struct V7HonestProofOutcome {
    pub(crate) proof_bytes: usize,
    pub(crate) compact_counter: u8,
    pub(crate) frontier_nodes: usize,
    pub(crate) metadata_path: PathBuf,
}

#[derive(Clone, Debug, Serialize)]
pub(crate) struct V6ProductionSimulationOutcome {
    pub(crate) maximum_compute_units: u64,
    pub(crate) evidence_path: PathBuf,
}

#[derive(Clone, Debug, Serialize)]
pub(crate) struct V7ProductionSimulationOutcome {
    pub(crate) compute_units: u64,
    pub(crate) evidence_path: PathBuf,
}

#[derive(Clone, Debug, Serialize)]
pub(crate) struct V6AdversarialOutcome {
    pub(crate) rejected_cases: usize,
    pub(crate) evidence_path: PathBuf,
}

#[derive(Clone, Debug)]
pub(crate) struct V6ExecutionInputs {
    pub(crate) proof: Vec<u8>,
    pub(crate) proof_sha256: String,
    pub(crate) statement_bytes: Vec<u8>,
    pub(crate) statement_sha256: String,
    pub(crate) metadata_bytes: Vec<u8>,
    pub(crate) metadata_sha256: String,
    pub(crate) statement: AtomicPaymentStatementV4,
    pub(crate) program_id: Pubkey,
    pub(crate) pool: Pubkey,
    pub(crate) proof_account: Pubkey,
    pub(crate) selector: u8,
    pub(crate) compact_counter: u8,
    pub(crate) frontier_nodes: usize,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct V6StatementSidecar {
    artifact: String,
    profile: String,
    program_id: String,
    pool: String,
    sequence: u64,
    current_anchor_hex: String,
    nullifier_hex: String,
    output_commitment_hex: String,
    output_anchor_hex: String,
    asset_id: u32,
    fee: u32,
    deployment_domain_hex: String,
    network_tag: String,
    proof_account: String,
    release_binding_hex: String,
}

#[derive(Debug, Deserialize)]
struct V6ProofMetadata {
    artifact: String,
    proof_sha256: String,
    statement_sha256: String,
    program_id: String,
    pool: String,
    proof_account: String,
    selector: u8,
    compact_counter: u8,
    frontier_nodes_per_tree: usize,
    all_work_checked: bool,
    host_full_acceptance: bool,
    release_binding_hex: String,
}

#[derive(Debug, Deserialize)]
struct V7ProofMetadata {
    artifact: String,
    proof_sha256: String,
    statement_sha256: String,
    program_id: String,
    pool: String,
    proof_account: String,
    compact_counter: u8,
    frontier_nodes_per_tree: usize,
    frontier_digest_bytes: usize,
    all_work_checked: bool,
    host_full_acceptance: bool,
    release_binding_hex: String,
}

fn parse_arguments(arguments: &[String]) -> Result<BTreeMap<String, String>> {
    const ALLOWED: [&str; 7] = [
        "--program-id",
        "--pool",
        "--proof-account",
        "--sequence",
        "--network-tag",
        "--out-dir",
        "--nonce-store",
    ];
    let mut values = BTreeMap::new();
    let mut index = 0usize;
    while index < arguments.len() {
        let key = arguments
            .get(index)
            .ok_or_else(|| anyhow!("missing V6 argument"))?;
        ensure!(ALLOWED.contains(&key.as_str()), "unknown V6 argument {key}");
        let value = arguments
            .get(index + 1)
            .ok_or_else(|| anyhow!("missing value for {key}"))?;
        ensure!(
            values.insert(key.clone(), value.clone()).is_none(),
            "duplicate V6 argument {key}"
        );
        index += 2;
    }
    for key in ALLOWED {
        ensure!(
            values.contains_key(key),
            "missing required V6 argument {key}"
        );
    }
    Ok(values)
}

fn value<'a>(values: &'a BTreeMap<String, String>, key: &str) -> Result<&'a str> {
    values
        .get(key)
        .map(String::as_str)
        .ok_or_else(|| anyhow!("missing {key}"))
}

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + 17 * index as u32))
}

/// Deterministically domain-separate the public demo witness by the account
/// identity that will carry it.  The old fixture used one process-global
/// nullifier, so a successful rehearsal of any earlier release permanently
/// made every later devnet rehearsal collide with the same nullifier PDA.
/// This is fixture construction only: it does not alter the V6 transcript,
/// relation, hash functions, work factors, or verifier cryptography.
fn bound_demo_digest(
    label: &[u8],
    pool: &Pubkey,
    sequence: u64,
    deployment_domain: &[u8; 32],
) -> Digest {
    let mut hasher = Sha256::new();
    hasher.update(b"aspis-v6-onefold-demo-witness-v2");
    hasher.update((label.len() as u64).to_le_bytes());
    hasher.update(label);
    hasher.update(pool.as_ref());
    hasher.update(sequence.to_le_bytes());
    hasher.update(deployment_domain);
    let bytes = hasher.finalize();
    core::array::from_fn(|index| {
        let offset = 4 * index;
        M31(u32::from_le_bytes(
            bytes[offset..offset + 4]
                .try_into()
                .expect("SHA-256 chunk is four bytes"),
        ) % P)
    })
}

fn honest_demo_statement_and_witness(
    pool: Pubkey,
    sequence: u64,
    deployment_domain: [u8; 32],
) -> Result<(AtomicPaymentStatementV4, SpendWitness)> {
    let nullifier_key = bound_demo_digest(b"nullifier-key", &pool, sequence, &deployment_domain);
    let input_salt = bound_demo_digest(b"input-salt", &pool, sequence, &deployment_domain);
    let output_salt = bound_demo_digest(b"output-salt", &pool, sequence, &deployment_domain);
    let output_owner_key =
        bound_demo_digest(b"output-owner-key", &pool, sequence, &deployment_domain);
    let asset_id = M31(17);
    let value = 1_000_000;
    let value_out = 999_999;
    let merkle_path = MerklePath {
        siblings: (0..20).map(|level| digest(1_000 + 31 * level)).collect(),
        index: 0x5_a5a5,
    };
    let witness = SpendWitness {
        nullifier_key,
        input_salt,
        output_salt,
        output_owner_key,
        input_asset_id: asset_id,
        value,
        value_out,
        merkle_path,
    };
    let input = note_commitment(
        &derive_owner_key(&nullifier_key),
        value,
        asset_id,
        &input_salt,
    );
    let output = output_commitment(&output_owner_key, value_out, asset_id, &output_salt);
    let statement = AtomicPaymentStatementV4 {
        pool: pool.to_bytes(),
        sequence,
        spend: SpendPublic {
            anchor: atomic_merkle_root_v3(input, &witness.merkle_path)
                .map_err(|error| anyhow!("V6 input root: {error:?}"))?,
            nullifier: derive_nullifier(&nullifier_key, &input_salt),
            output_commitment: output,
            asset_id,
            fee: 1,
        },
        output_anchor: atomic_merkle_root_v3(output, &witness.merkle_path)
            .map_err(|error| anyhow!("V6 output root: {error:?}"))?,
        deployment_domain,
    };
    Ok((statement, witness))
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn decode_hex_32(field: &str, value: &str) -> Result<[u8; 32]> {
    ensure!(
        value.len() == 64
            && value
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
        "{field} is not canonical lowercase 32-byte hex"
    );
    let mut decoded = [0u8; 32];
    let bytes = value.as_bytes();
    for (index, output) in decoded.iter_mut().enumerate() {
        let nibble = |byte: u8| match byte {
            b'0'..=b'9' => byte - b'0',
            _ => byte - b'a' + 10,
        };
        *output = (nibble(bytes[2 * index]) << 4) | nibble(bytes[2 * index + 1]);
    }
    Ok(decoded)
}

fn sha256(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}

fn create_new(path: &Path, bytes: &[u8]) -> Result<()> {
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    let mut file = options
        .open(path)
        .with_context(|| format!("create V6 artifact {}", path.display()))?;
    file.write_all(bytes)?;
    file.sync_all()?;
    Ok(())
}

pub(crate) fn build_honest_proof(arguments: &[String]) -> Result<V6HonestProofOutcome> {
    let values = parse_arguments(arguments)?;
    let program_id =
        Pubkey::from_str(value(&values, "--program-id")?).context("invalid --program-id")?;
    let pool = Pubkey::from_str(value(&values, "--pool")?).context("invalid --pool")?;
    let proof_account =
        Pubkey::from_str(value(&values, "--proof-account")?).context("invalid --proof-account")?;
    ensure!(program_id != pool && pool != proof_account && program_id != proof_account);
    let sequence = value(&values, "--sequence")?
        .parse::<u64>()
        .context("invalid --sequence")?;
    let network_tag = value(&values, "--network-tag")?.as_bytes();
    ensure!(!network_tag.is_empty() && network_tag.len() <= 64);
    let out_dir = PathBuf::from(value(&values, "--out-dir")?);
    let nonce_store_dir = PathBuf::from(value(&values, "--nonce-store")?);
    ensure!(out_dir.is_absolute() && nonce_store_dir.is_absolute());
    fs::create_dir_all(&out_dir)?;

    let deployment_domain =
        atomic_deployment_domain(HOST_HASH, &program_id.to_bytes(), network_tag);
    let (statement, witness) =
        honest_demo_statement_and_witness(pool, sequence, deployment_domain)?;
    let context = V6ProverContext {
        program_id: program_id.to_bytes(),
        release_binding: V6_RELEASE_BINDING,
        attempt_id: proof_account.to_bytes(),
    };
    let attempt = StateOnlyAttemptSecrets::generate_for_mask_nonce(proof_account.to_bytes())
        .map_err(|error| anyhow!("generate V6 attempt entropy: {error:?}"))?;
    let mut nonce_store = DurableStateOnlyMaskNonceStore::open(&nonce_store_dir)
        .with_context(|| format!("open nonce store {}", nonce_store_dir.display()))?;
    let proof = build_v6_onefold_proof_production(
        &statement,
        &witness,
        context,
        attempt,
        &mut nonce_store,
        HOST_HASH,
    )
    .map_err(|error| anyhow!("build honest V6 proof: {error:?}"))?;
    ensure!(
        proof.pow_valid,
        "production V6 builder returned unmined proof"
    );
    let replay = verify_v6_onefold_proof_production(&proof, &statement, context, HOST_HASH)
        .map_err(|error| anyhow!("replay honest V6 proof: {error:?}"))?;
    ensure!(replay.selector == proof.selector);
    ensure!(replay.compact_counter == proof.compact_counter);
    ensure!(replay.frontier_nodes == proof.frontier_nodes);

    let proof_path = out_dir.join("v6-proof.bin");
    let statement_path = out_dir.join("v6-statement.json");
    let metadata_path = out_dir.join("v6-honest-proof.json");
    let statement_json = serde_json::to_vec_pretty(&json!({
        "artifact": "aspis_v6_onefold_statement",
        "profile": "V6-26C1-3C2-B10-q16-onefold-final256-f209",
        "program_id": program_id.to_string(),
        "pool": pool.to_string(),
        "sequence": sequence,
        "current_anchor_hex": hex(&encode_digest_canonical(&statement.spend.anchor)),
        "nullifier_hex": hex(&encode_digest_canonical(&statement.spend.nullifier)),
        "output_commitment_hex": hex(&encode_digest_canonical(&statement.spend.output_commitment)),
        "output_anchor_hex": hex(&encode_digest_canonical(&statement.output_anchor)),
        "asset_id": statement.spend.asset_id.0,
        "fee": statement.spend.fee,
        "deployment_domain_hex": hex(&statement.deployment_domain),
        "network_tag": String::from_utf8_lossy(network_tag),
        "proof_account": proof_account.to_string(),
        "release_binding_hex": hex(&V6_RELEASE_BINDING),
    }))?;
    let mut statement_json_newline = statement_json;
    statement_json_newline.push(b'\n');
    let metadata = serde_json::to_vec_pretty(&json!({
        "artifact": "aspis_v6_onefold_honest_mined_proof",
        "schema_version": 1,
        "proof_path": proof_path,
        "proof_bytes": proof.bytes.len(),
        "proof_sha256": sha256(&proof.bytes),
        "statement_path": statement_path,
        "statement_sha256": sha256(&statement_json_newline),
        "program_id": program_id.to_string(),
        "pool": pool.to_string(),
        "proof_account": proof_account.to_string(),
        "selector": proof.selector,
        "compact_counter": proof.compact_counter,
        "frontier_nodes_per_tree": proof.frontier_nodes,
        "queries": proof.queries,
        "work_nonces": proof.work_nonces,
        "work_bits": [34, 31, 34],
        "all_work_checked": proof.pow_valid,
        "host_full_acceptance": true,
        "release_binding_hex": hex(&V6_RELEASE_BINDING),
        "nonce_store": nonce_store_dir,
    }))?;
    let mut metadata_newline = metadata;
    metadata_newline.push(b'\n');
    create_new(&proof_path, &proof.bytes)?;
    create_new(&statement_path, &statement_json_newline)?;
    create_new(&metadata_path, &metadata_newline)?;

    Ok(V6HonestProofOutcome {
        proof_bytes: proof.bytes.len(),
        selector: proof.selector,
        compact_counter: proof.compact_counter,
        frontier_nodes: proof.frontier_nodes,
        metadata_path,
    })
}

/// Build and freeze one genuine compact V7 proof. The production prover mines
/// every work nonce; an externally configured Metal miner is accepted only
/// after the Rust transcript predicate rechecks its result.
pub(crate) fn build_honest_v7_proof(arguments: &[String]) -> Result<V7HonestProofOutcome> {
    let values = parse_arguments(arguments)?;
    let program_id =
        Pubkey::from_str(value(&values, "--program-id")?).context("invalid --program-id")?;
    let pool = Pubkey::from_str(value(&values, "--pool")?).context("invalid --pool")?;
    let proof_account =
        Pubkey::from_str(value(&values, "--proof-account")?).context("invalid --proof-account")?;
    ensure!(program_id != pool && pool != proof_account && program_id != proof_account);
    let sequence = value(&values, "--sequence")?
        .parse::<u64>()
        .context("invalid --sequence")?;
    let network_tag = value(&values, "--network-tag")?.as_bytes();
    ensure!(!network_tag.is_empty() && network_tag.len() <= 64);
    let out_dir = PathBuf::from(value(&values, "--out-dir")?);
    let nonce_store_dir = PathBuf::from(value(&values, "--nonce-store")?);
    ensure!(out_dir.is_absolute() && nonce_store_dir.is_absolute());
    fs::create_dir_all(&out_dir)?;

    let deployment_domain =
        atomic_deployment_domain(HOST_HASH, &program_id.to_bytes(), network_tag);
    let (statement, witness) =
        honest_demo_statement_and_witness(pool, sequence, deployment_domain)?;
    let context = V7ProverContext {
        program_id: program_id.to_bytes(),
        release_binding: V7_RELEASE_BINDING,
        attempt_id: proof_account.to_bytes(),
    };
    let attempt = StateOnlyAttemptSecrets::generate_for_mask_nonce(proof_account.to_bytes())
        .map_err(|error| anyhow!("generate V7 attempt entropy: {error:?}"))?;
    let mut nonce_store = DurableStateOnlyMaskNonceStore::open(&nonce_store_dir)
        .with_context(|| format!("open nonce store {}", nonce_store_dir.display()))?;
    let proof = build_v7_compact_onefold_proof_production(
        &statement,
        &witness,
        context,
        attempt,
        &mut nonce_store,
        HOST_HASH,
    )
    .map_err(|error| anyhow!("build honest V7 proof: {error:?}"))?;
    ensure!(
        proof.pow_valid,
        "production V7 builder returned unmined proof"
    );
    let replay = verify_v7_compact_onefold_proof_production(&proof, &statement, context, HOST_HASH)
        .map_err(|error| anyhow!("replay honest V7 proof: {error:?}"))?;
    ensure!(replay.compact_counter == proof.compact_counter);
    ensure!(replay.frontier_nodes == proof.frontier_nodes);

    let proof_path = out_dir.join("v7-proof.bin");
    let statement_path = out_dir.join("v7-statement.json");
    let metadata_path = out_dir.join("v7-honest-proof.json");
    let statement_json = serde_json::to_vec_pretty(&json!({
        "artifact": "aspis_v7_compact_onefold_statement",
        "profile": "V7-26C1-3C2-B10-q16-onefold-digest208-f203-fullC2",
        "program_id": program_id.to_string(),
        "pool": pool.to_string(),
        "sequence": sequence,
        "current_anchor_hex": hex(&encode_digest_canonical(&statement.spend.anchor)),
        "nullifier_hex": hex(&encode_digest_canonical(&statement.spend.nullifier)),
        "output_commitment_hex": hex(&encode_digest_canonical(&statement.spend.output_commitment)),
        "output_anchor_hex": hex(&encode_digest_canonical(&statement.output_anchor)),
        "asset_id": statement.spend.asset_id.0,
        "fee": statement.spend.fee,
        "deployment_domain_hex": hex(&statement.deployment_domain),
        "network_tag": String::from_utf8_lossy(network_tag),
        "proof_account": proof_account.to_string(),
        "release_binding_hex": hex(&V7_RELEASE_BINDING),
    }))?;
    let mut statement_json_newline = statement_json;
    statement_json_newline.push(b'\n');
    let metadata = serde_json::to_vec_pretty(&json!({
        "artifact": "aspis_v7_compact_onefold_honest_mined_proof",
        "schema_version": 1,
        "proof_path": proof_path,
        "proof_bytes": proof.bytes.len(),
        "proof_sha256": sha256(&proof.bytes),
        "statement_path": statement_path,
        "statement_sha256": sha256(&statement_json_newline),
        "program_id": program_id.to_string(),
        "pool": pool.to_string(),
        "proof_account": proof_account.to_string(),
        "compact_counter": proof.compact_counter,
        "frontier_nodes_per_tree": proof.frontier_nodes,
        "frontier_digest_bytes": V7_COMPACT_DIGEST_BYTES,
        "queries": proof.queries,
        "work_nonces": proof.work_nonces,
        "work_bits": [35, 31, 34],
        "all_work_checked": proof.pow_valid,
        "host_full_acceptance": true,
        "release_binding_hex": hex(&V7_RELEASE_BINDING),
        "nonce_store": nonce_store_dir,
    }))?;
    let mut metadata_newline = metadata;
    metadata_newline.push(b'\n');
    create_new(&proof_path, &proof.bytes)?;
    create_new(&statement_path, &statement_json_newline)?;
    create_new(&metadata_path, &metadata_newline)?;

    Ok(V7HonestProofOutcome {
        proof_bytes: proof.bytes.len(),
        compact_counter: proof.compact_counter,
        frontier_nodes: proof.frontier_nodes,
        metadata_path,
    })
}

fn statement_from_sidecar(sidecar: &V6StatementSidecar) -> Result<AtomicPaymentStatementV4> {
    ensure!(sidecar.artifact == "aspis_v6_onefold_statement");
    ensure!(sidecar.profile == "V6-26C1-3C2-B10-q16-onefold-final256-f209");
    ensure!(sidecar.release_binding_hex == hex(&V6_RELEASE_BINDING));
    let decode_digest = |field: &str, encoded: &str| {
        aspis_statement::decode_digest_canonical(&decode_hex_32(field, encoded)?)
            .map_err(|error| anyhow!("decode {field}: {error:?}"))
    };
    let statement = AtomicPaymentStatementV4 {
        pool: Pubkey::from_str(&sidecar.pool)
            .context("invalid V6 statement pool")?
            .to_bytes(),
        sequence: sidecar.sequence,
        spend: SpendPublic {
            anchor: decode_digest("current_anchor_hex", &sidecar.current_anchor_hex)?,
            nullifier: decode_digest("nullifier_hex", &sidecar.nullifier_hex)?,
            output_commitment: decode_digest(
                "output_commitment_hex",
                &sidecar.output_commitment_hex,
            )?,
            asset_id: aspis_statement::decode_asset_id_canonical(sidecar.asset_id)
                .map_err(|error| anyhow!("decode V6 asset id: {error:?}"))?,
            fee: sidecar.fee,
        },
        output_anchor: decode_digest("output_anchor_hex", &sidecar.output_anchor_hex)?,
        deployment_domain: decode_hex_32("deployment_domain_hex", &sidecar.deployment_domain_hex)?,
    };
    aspis_statement::encode_atomic_payment_statement_v4(&statement)
        .map_err(|error| anyhow!("noncanonical V6 statement: {error:?}"))?;
    Ok(statement)
}

fn statement_from_v7_sidecar(sidecar: &V6StatementSidecar) -> Result<AtomicPaymentStatementV4> {
    ensure!(sidecar.artifact == "aspis_v7_compact_onefold_statement");
    ensure!(sidecar.profile == "V7-26C1-3C2-B10-q16-onefold-digest208-f203-fullC2");
    ensure!(sidecar.release_binding_hex == hex(&V7_RELEASE_BINDING));
    let decode_digest = |field: &str, encoded: &str| {
        aspis_statement::decode_digest_canonical(&decode_hex_32(field, encoded)?)
            .map_err(|error| anyhow!("decode {field}: {error:?}"))
    };
    let statement = AtomicPaymentStatementV4 {
        pool: Pubkey::from_str(&sidecar.pool)
            .context("invalid V7 statement pool")?
            .to_bytes(),
        sequence: sidecar.sequence,
        spend: SpendPublic {
            anchor: decode_digest("current_anchor_hex", &sidecar.current_anchor_hex)?,
            nullifier: decode_digest("nullifier_hex", &sidecar.nullifier_hex)?,
            output_commitment: decode_digest(
                "output_commitment_hex",
                &sidecar.output_commitment_hex,
            )?,
            asset_id: aspis_statement::decode_asset_id_canonical(sidecar.asset_id)
                .map_err(|error| anyhow!("decode V7 asset id: {error:?}"))?,
            fee: sidecar.fee,
        },
        output_anchor: decode_digest("output_anchor_hex", &sidecar.output_anchor_hex)?,
        deployment_domain: decode_hex_32("deployment_domain_hex", &sidecar.deployment_domain_hex)?,
    };
    aspis_statement::encode_atomic_payment_statement_v4(&statement)
        .map_err(|error| anyhow!("noncanonical V7 statement: {error:?}"))?;
    Ok(statement)
}

fn sealed_proof_account(body: &[u8]) -> Result<Vec<u8>> {
    let length = u32::try_from(body.len()).context("V6 proof exceeds u32 framing")?;
    let mut account = vec![0u8; PROOF_ACCOUNT_HEADER_LEN + body.len()];
    account[0..4].copy_from_slice(b"ASPU");
    account[4..8].copy_from_slice(&length.to_le_bytes());
    account[PROOF_ACCOUNT_HEADER_LEN..].copy_from_slice(body);
    Ok(account)
}

pub(crate) fn production_instruction(
    frontier: usize,
    selector: u8,
    statement: &AtomicPaymentStatementV4,
) -> Result<Vec<u8>> {
    let frontier = u16::try_from(frontier).context("V6 frontier does not fit u16")?;
    let mut wire = Vec::with_capacity(V6_ATOMIC_WIRE_BYTES);
    wire.push(V6_PRODUCTION_TAG);
    wire.extend_from_slice(&frontier.to_le_bytes());
    wire.extend_from_slice(&frontier.to_le_bytes());
    wire.push(selector);
    wire.extend_from_slice(&encode_digest_canonical(&statement.spend.anchor));
    wire.extend_from_slice(&encode_digest_canonical(&statement.spend.nullifier));
    wire.extend_from_slice(&encode_digest_canonical(&statement.spend.output_commitment));
    wire.extend_from_slice(&encode_digest_canonical(&statement.output_anchor));
    wire.extend_from_slice(&statement.spend.asset_id.0.to_le_bytes());
    wire.extend_from_slice(&statement.spend.fee.to_le_bytes());
    wire.extend_from_slice(&statement.deployment_domain);
    ensure!(wire.len() == V6_ATOMIC_WIRE_BYTES);
    Ok(wire)
}

pub(crate) fn v7_production_instruction(
    frontier: usize,
    statement: &AtomicPaymentStatementV4,
) -> Result<Vec<u8>> {
    let frontier = u16::try_from(frontier).context("V7 frontier does not fit u16")?;
    let mut wire = Vec::with_capacity(V7_ATOMIC_WIRE_BYTES);
    wire.push(V7_PRODUCTION_TAG);
    wire.extend_from_slice(&frontier.to_le_bytes());
    wire.extend_from_slice(&encode_digest_canonical(&statement.spend.anchor));
    wire.extend_from_slice(&encode_digest_canonical(&statement.spend.nullifier));
    wire.extend_from_slice(&encode_digest_canonical(&statement.spend.output_commitment));
    wire.extend_from_slice(&encode_digest_canonical(&statement.output_anchor));
    wire.extend_from_slice(&statement.spend.asset_id.0.to_le_bytes());
    wire.extend_from_slice(&statement.spend.fee.to_le_bytes());
    wire.extend_from_slice(&statement.deployment_domain);
    ensure!(wire.len() == V7_ATOMIC_WIRE_BYTES);
    Ok(wire)
}

pub(crate) fn load_execution_inputs(
    proof_path: &Path,
    statement_path: &Path,
    metadata_path: &Path,
    required_network_tag: &str,
) -> Result<V6ExecutionInputs> {
    for path in [proof_path, statement_path, metadata_path] {
        ensure!(
            path.is_absolute() && path.is_file(),
            "missing {}",
            path.display()
        );
    }
    let proof = fs::read(proof_path)?;
    let statement_bytes = fs::read(statement_path)?;
    let metadata_bytes = fs::read(metadata_path)?;
    let sidecar: V6StatementSidecar = serde_json::from_slice(&statement_bytes)?;
    let metadata: V6ProofMetadata = serde_json::from_slice(&metadata_bytes)?;
    let statement = statement_from_sidecar(&sidecar)?;
    ensure!(metadata.artifact == "aspis_v6_onefold_honest_mined_proof");
    ensure!(metadata.proof_sha256 == sha256(&proof));
    ensure!(metadata.statement_sha256 == sha256(&statement_bytes));
    ensure!(metadata.program_id == sidecar.program_id);
    ensure!(metadata.pool == sidecar.pool);
    ensure!(metadata.proof_account == sidecar.proof_account);
    ensure!(metadata.release_binding_hex == hex(&V6_RELEASE_BINDING));
    ensure!(metadata.all_work_checked && metadata.host_full_acceptance);
    ensure!(metadata.selector < 3 && metadata.compact_counter < 8);
    ensure!(metadata.frontier_nodes_per_tree > 0);
    ensure!(metadata.frontier_nodes_per_tree <= V6_FRONTIER_CAP_PER_TREE);
    ensure!(proof.len() == V6_BODY_WITHOUT_FRONTIERS + 64 * metadata.frontier_nodes_per_tree);
    let program_id = Pubkey::from_str(&sidecar.program_id)?;
    let pool = Pubkey::from_str(&sidecar.pool)?;
    let proof_account = Pubkey::from_str(&sidecar.proof_account)?;
    ensure!(program_id == aspis_verifier::id());
    ensure!(sidecar.network_tag == required_network_tag);
    ensure!(
        atomic_deployment_domain(
            HOST_HASH,
            &program_id.to_bytes(),
            required_network_tag.as_bytes(),
        ) == statement.deployment_domain
    );
    let replay = aspis_verifier::v6_verifier::verify_v6_read_only(
        HOST_HASH,
        &proof,
        metadata.frontier_nodes_per_tree,
        metadata.frontier_nodes_per_tree,
        metadata.selector,
        &program_id,
        V6_RELEASE_BINDING,
        &proof_account,
        &statement,
        true,
    )
    .map_err(|error| anyhow!("production V6 host replay rejected: {error:?}"))?;
    ensure!(replay.transcript.compact_counter == metadata.compact_counter);
    ensure!(replay.transcript.frontier_nodes == metadata.frontier_nodes_per_tree);

    Ok(V6ExecutionInputs {
        proof_sha256: sha256(&proof),
        statement_sha256: sha256(&statement_bytes),
        metadata_sha256: sha256(&metadata_bytes),
        proof,
        statement_bytes,
        metadata_bytes,
        statement,
        program_id,
        pool,
        proof_account,
        selector: metadata.selector,
        compact_counter: metadata.compact_counter,
        frontier_nodes: metadata.frontier_nodes_per_tree,
    })
}

pub(crate) fn load_v7_execution_inputs(
    proof_path: &Path,
    statement_path: &Path,
    metadata_path: &Path,
    required_network_tag: &str,
) -> Result<V6ExecutionInputs> {
    for path in [proof_path, statement_path, metadata_path] {
        ensure!(
            path.is_absolute() && path.is_file(),
            "missing {}",
            path.display()
        );
    }
    let proof = fs::read(proof_path)?;
    let statement_bytes = fs::read(statement_path)?;
    let metadata_bytes = fs::read(metadata_path)?;
    let sidecar: V6StatementSidecar = serde_json::from_slice(&statement_bytes)?;
    let metadata: V7ProofMetadata = serde_json::from_slice(&metadata_bytes)?;
    let statement = statement_from_v7_sidecar(&sidecar)?;
    ensure!(metadata.artifact == "aspis_v7_compact_onefold_honest_mined_proof");
    ensure!(metadata.proof_sha256 == sha256(&proof));
    ensure!(metadata.statement_sha256 == sha256(&statement_bytes));
    ensure!(metadata.program_id == sidecar.program_id);
    ensure!(metadata.pool == sidecar.pool);
    ensure!(metadata.proof_account == sidecar.proof_account);
    ensure!(metadata.release_binding_hex == hex(&V7_RELEASE_BINDING));
    ensure!(metadata.all_work_checked && metadata.host_full_acceptance);
    ensure!(metadata.compact_counter < 64);
    ensure!(metadata.frontier_digest_bytes == V7_COMPACT_DIGEST_BYTES);
    ensure!(metadata.frontier_nodes_per_tree > 0);
    ensure!(metadata.frontier_nodes_per_tree <= V7_COMPACT_FRONTIER_CAP_PER_TREE);
    ensure!(
        proof.len()
            == V7_COMPACT_BODY_WITHOUT_FRONTIERS
                + 2 * V7_COMPACT_DIGEST_BYTES * metadata.frontier_nodes_per_tree
    );
    let program_id = Pubkey::from_str(&sidecar.program_id)?;
    let pool = Pubkey::from_str(&sidecar.pool)?;
    let proof_account = Pubkey::from_str(&sidecar.proof_account)?;
    ensure!(program_id == aspis_verifier::id());
    ensure!(sidecar.network_tag == required_network_tag);
    ensure!(
        atomic_deployment_domain(
            HOST_HASH,
            &program_id.to_bytes(),
            required_network_tag.as_bytes(),
        ) == statement.deployment_domain
    );
    let replay = aspis_verifier::v7_verifier::verify_v7_read_only(
        HOST_HASH,
        &proof,
        metadata.frontier_nodes_per_tree,
        &program_id,
        V7_RELEASE_BINDING,
        &proof_account,
        &statement,
        true,
    )
    .map_err(|error| anyhow!("production V7 host replay rejected: {error:?}"))?;
    ensure!(replay.transcript.compact_counter == metadata.compact_counter);
    ensure!(replay.transcript.frontier_nodes == metadata.frontier_nodes_per_tree);

    Ok(V6ExecutionInputs {
        proof_sha256: sha256(&proof),
        statement_sha256: sha256(&statement_bytes),
        metadata_sha256: sha256(&metadata_bytes),
        proof,
        statement_bytes,
        metadata_bytes,
        statement,
        program_id,
        pool,
        proof_account,
        selector: 0,
        compact_counter: metadata.compact_counter,
        frontier_nodes: metadata.frontier_nodes_per_tree,
    })
}

fn parse_simulation_arguments(arguments: &[String]) -> Result<BTreeMap<String, String>> {
    const ALLOWED: [&str; 5] = ["--sbf", "--proof", "--statement", "--metadata", "--out"];
    let mut values = BTreeMap::new();
    let mut index = 0usize;
    while index < arguments.len() {
        let key = arguments
            .get(index)
            .context("missing simulation argument")?;
        ensure!(
            ALLOWED.contains(&key.as_str()),
            "unknown simulation argument {key}"
        );
        let item = arguments
            .get(index + 1)
            .ok_or_else(|| anyhow!("missing value for {key}"))?;
        ensure!(
            values.insert(key.clone(), item.clone()).is_none(),
            "duplicate simulation argument {key}"
        );
        index += 2;
    }
    for key in ALLOWED {
        ensure!(
            values.contains_key(key),
            "missing simulation argument {key}"
        );
    }
    Ok(values)
}

pub(crate) fn simulate_production(arguments: &[String]) -> Result<V6ProductionSimulationOutcome> {
    let values = parse_simulation_arguments(arguments)?;
    let sbf_path = PathBuf::from(value(&values, "--sbf")?);
    let proof_path = PathBuf::from(value(&values, "--proof")?);
    let statement_path = PathBuf::from(value(&values, "--statement")?);
    let metadata_path = PathBuf::from(value(&values, "--metadata")?);
    let evidence_path = PathBuf::from(value(&values, "--out")?);
    for path in [&sbf_path, &proof_path, &statement_path, &metadata_path] {
        ensure!(
            path.is_absolute() && path.is_file(),
            "missing input {}",
            path.display()
        );
    }
    ensure!(evidence_path.is_absolute() && !evidence_path.exists());
    let sbf = fs::read(&sbf_path)?;
    let proof = fs::read(&proof_path)?;
    let statement_bytes = fs::read(&statement_path)?;
    let metadata_bytes = fs::read(&metadata_path)?;
    let sidecar: V6StatementSidecar = serde_json::from_slice(&statement_bytes)?;
    let metadata: V6ProofMetadata = serde_json::from_slice(&metadata_bytes)?;
    let statement = statement_from_sidecar(&sidecar)?;
    ensure!(metadata.artifact == "aspis_v6_onefold_honest_mined_proof");
    ensure!(metadata.proof_sha256 == sha256(&proof));
    ensure!(metadata.statement_sha256 == sha256(&statement_bytes));
    ensure!(metadata.program_id == sidecar.program_id);
    ensure!(metadata.pool == sidecar.pool);
    ensure!(metadata.proof_account == sidecar.proof_account);
    ensure!(metadata.release_binding_hex == hex(&V6_RELEASE_BINDING));
    ensure!(metadata.all_work_checked && metadata.host_full_acceptance);
    ensure!(metadata.selector < 3 && metadata.compact_counter < 8);
    let program_id = Pubkey::from_str(&sidecar.program_id)?;
    let pool = Pubkey::from_str(&sidecar.pool)?;
    let proof_account = Pubkey::from_str(&sidecar.proof_account)?;
    ensure!(
        program_id == aspis_verifier::id(),
        "simulation SBF id mismatch"
    );
    ensure!(sidecar.network_tag == "devnet");
    ensure!(
        atomic_deployment_domain(
            HOST_HASH,
            &program_id.to_bytes(),
            sidecar.network_tag.as_bytes()
        ) == statement.deployment_domain
    );

    let host = aspis_verifier::v6_verifier::verify_v6_read_only(
        HOST_HASH,
        &proof,
        metadata.frontier_nodes_per_tree,
        metadata.frontier_nodes_per_tree,
        metadata.selector,
        &program_id,
        V6_RELEASE_BINDING,
        &proof_account,
        &statement,
        true,
    )
    .map_err(|error| anyhow!("production V6 host verifier rejected: {error:?}"))?;
    ensure!(host.transcript.compact_counter == metadata.compact_counter);
    ensure!(host.transcript.frontier_nodes == metadata.frontier_nodes_per_tree);

    let proof_data = sealed_proof_account(&proof)?;
    let mut pool_data = [0u8; ATOMIC_POOL_STATE_LEN];
    AtomicPoolStateV2 {
        sequence: statement.sequence,
        anchor: encode_digest_canonical(&statement.spend.anchor),
        deployment_domain: statement.deployment_domain,
    }
    .encode(&mut pool_data)
    .map_err(|error| anyhow!("encode V6 simulation pool: {error:?}"))?;
    let nullifier = encode_digest_canonical(&statement.spend.nullifier);
    let marker = atomic_nullifier_address(&program_id, &nullifier).0;
    let marker_data = [0u8; ATOMIC_NULLIFIER_MARKER_LEN];
    let wires = vec![
        production_instruction(
            metadata.frontier_nodes_per_tree,
            metadata.selector,
            &statement,
        )?;
        3
    ];
    let program_owned = crate::spend_measure::simulate_atomic_program_account_instructions(
        &sbf_path,
        proof_account,
        &proof_data,
        pool,
        &pool_data,
        marker,
        &marker_data,
        &wires,
    )?;
    let missing =
        crate::spend_measure::simulate_atomic_program_account_instructions_with_absent_marker(
            &sbf_path,
            proof_account,
            &proof_data,
            pool,
            &pool_data,
            marker,
            &wires,
        )?;
    let program_owned_cu = program_owned
        .iter()
        .map(|result| result.units)
        .collect::<Vec<_>>();
    let missing_cu = missing
        .iter()
        .map(|result| result.units)
        .collect::<Vec<_>>();
    ensure!(program_owned_cu.len() == 3 && missing_cu.len() == 3);
    ensure!(program_owned_cu
        .iter()
        .all(|units| *units == program_owned_cu[0]));
    ensure!(missing_cu.iter().all(|units| *units == missing_cu[0]));
    let system_id = Pubkey::default().to_string();
    let cpi_complete = missing.iter().all(|result| {
        let invoke = format!("Program {system_id} invoke");
        let success = format!("Program {system_id} success");
        result
            .logs
            .iter()
            .position(|line| line.starts_with(&invoke))
            .is_some_and(|position| {
                result
                    .logs
                    .iter()
                    .skip(position + 1)
                    .any(|line| line == &success)
            })
    });
    ensure!(
        cpi_complete,
        "missing-marker simulation omitted successful CPI"
    );
    let maximum_compute_units = program_owned_cu[0].max(missing_cu[0]);
    ensure!(
        maximum_compute_units < 1_300_000,
        "honest production V6 exceeds 1.3M CU: {maximum_compute_units}"
    );
    let evidence = serde_json::to_vec_pretty(&json!({
        "artifact": "aspis_v6_onefold_production_sbf_simulation",
        "schema_version": 1,
        "sbf_path": sbf_path,
        "sbf_bytes": sbf.len(),
        "sbf_sha256": sha256(&sbf),
        "proof_path": proof_path,
        "proof_bytes": proof.len(),
        "proof_sha256": sha256(&proof),
        "statement_path": statement_path,
        "statement_sha256": sha256(&statement_bytes),
        "program_id": program_id.to_string(),
        "pool": pool.to_string(),
        "proof_account": proof_account.to_string(),
        "nullifier_marker": marker.to_string(),
        "selector": metadata.selector,
        "compact_counter": metadata.compact_counter,
        "frontier_nodes_per_tree": metadata.frontier_nodes_per_tree,
        "program_owned_marker_repeated_compute_units": program_owned_cu,
        "missing_marker_repeated_compute_units": missing_cu,
        "maximum_compute_units": maximum_compute_units,
        "headroom_under_1_3m": 1_300_000_i64 - maximum_compute_units as i64,
        "deterministic_three_of_three_both_paths": true,
        "missing_marker_completed_system_program_cpi": cpi_complete,
        "host_production_acceptance": true,
        "real_work_checks": true,
        "exact_terminal_equality": true,
        "build_command": "NO_DNA=1 cargo-build-sbf --manifest-path programs/aspis-verifier/Cargo.toml --no-default-features --features v6-production-tag72",
    }))?;
    let mut evidence_newline = evidence;
    evidence_newline.push(b'\n');
    create_new(&evidence_path, &evidence_newline)?;
    Ok(V6ProductionSimulationOutcome {
        maximum_compute_units,
        evidence_path,
    })
}

/// Run the genuine V7 production binary once through the missing-marker
/// atomic path. This is the exact state-changing path needed for the CU gate;
/// repeated determinism and lifecycle replay are deferred to devnet evidence.
pub(crate) fn simulate_v7_production(
    arguments: &[String],
) -> Result<V7ProductionSimulationOutcome> {
    let values = parse_simulation_arguments(arguments)?;
    let sbf_path = PathBuf::from(value(&values, "--sbf")?);
    let proof_path = PathBuf::from(value(&values, "--proof")?);
    let statement_path = PathBuf::from(value(&values, "--statement")?);
    let metadata_path = PathBuf::from(value(&values, "--metadata")?);
    let evidence_path = PathBuf::from(value(&values, "--out")?);
    for path in [&sbf_path, &proof_path, &statement_path, &metadata_path] {
        ensure!(
            path.is_absolute() && path.is_file(),
            "missing input {}",
            path.display()
        );
    }
    ensure!(evidence_path.is_absolute() && !evidence_path.exists());

    let sbf = fs::read(&sbf_path)?;
    let proof = fs::read(&proof_path)?;
    let statement_bytes = fs::read(&statement_path)?;
    let metadata_bytes = fs::read(&metadata_path)?;
    let sidecar: V6StatementSidecar = serde_json::from_slice(&statement_bytes)?;
    let metadata: V7ProofMetadata = serde_json::from_slice(&metadata_bytes)?;
    let statement = statement_from_v7_sidecar(&sidecar)?;
    ensure!(metadata.artifact == "aspis_v7_compact_onefold_honest_mined_proof");
    ensure!(metadata.proof_sha256 == sha256(&proof));
    ensure!(metadata.statement_sha256 == sha256(&statement_bytes));
    ensure!(metadata.program_id == sidecar.program_id);
    ensure!(metadata.pool == sidecar.pool);
    ensure!(metadata.proof_account == sidecar.proof_account);
    ensure!(metadata.release_binding_hex == hex(&V7_RELEASE_BINDING));
    ensure!(metadata.all_work_checked && metadata.host_full_acceptance);
    ensure!(metadata.compact_counter < 64);
    ensure!(metadata.frontier_digest_bytes == V7_COMPACT_DIGEST_BYTES);
    ensure!(metadata.frontier_nodes_per_tree <= V7_COMPACT_FRONTIER_CAP_PER_TREE);
    ensure!(
        proof.len()
            == V7_COMPACT_BODY_WITHOUT_FRONTIERS
                + 2 * V7_COMPACT_DIGEST_BYTES * metadata.frontier_nodes_per_tree
    );

    let program_id = Pubkey::from_str(&sidecar.program_id)?;
    let pool = Pubkey::from_str(&sidecar.pool)?;
    let proof_account = Pubkey::from_str(&sidecar.proof_account)?;
    ensure!(
        program_id == aspis_verifier::id(),
        "simulation SBF id mismatch"
    );
    ensure!(sidecar.network_tag == "devnet");
    ensure!(
        atomic_deployment_domain(HOST_HASH, &program_id.to_bytes(), b"devnet")
            == statement.deployment_domain
    );

    let host = aspis_verifier::v7_verifier::verify_v7_read_only(
        HOST_HASH,
        &proof,
        metadata.frontier_nodes_per_tree,
        &program_id,
        V7_RELEASE_BINDING,
        &proof_account,
        &statement,
        true,
    )
    .map_err(|error| anyhow!("production V7 host verifier rejected: {error:?}"))?;
    ensure!(host.transcript.compact_counter == metadata.compact_counter);
    ensure!(host.transcript.frontier_nodes == metadata.frontier_nodes_per_tree);

    let proof_data = sealed_proof_account(&proof)?;
    let mut pool_data = [0u8; ATOMIC_POOL_STATE_LEN];
    AtomicPoolStateV2 {
        sequence: statement.sequence,
        anchor: encode_digest_canonical(&statement.spend.anchor),
        deployment_domain: statement.deployment_domain,
    }
    .encode(&mut pool_data)
    .map_err(|error| anyhow!("encode V7 simulation pool: {error:?}"))?;
    let nullifier = encode_digest_canonical(&statement.spend.nullifier);
    let marker = atomic_nullifier_address(&program_id, &nullifier).0;
    let instruction = v7_production_instruction(metadata.frontier_nodes_per_tree, &statement)?;
    let simulations =
        crate::spend_measure::simulate_atomic_program_account_instructions_with_absent_marker(
            &sbf_path,
            proof_account,
            &proof_data,
            pool,
            &pool_data,
            marker,
            &[instruction],
        )?;
    let simulation = simulations
        .first()
        .context("V7 local-validator simulation returned no result")?;
    let system_id = Pubkey::default().to_string();
    let invoke = format!("Program {system_id} invoke");
    let success = format!("Program {system_id} success");
    let cpi_complete = simulation
        .logs
        .iter()
        .position(|line| line.starts_with(&invoke))
        .is_some_and(|position| {
            simulation
                .logs
                .iter()
                .skip(position + 1)
                .any(|line| line == &success)
        });
    ensure!(
        cpi_complete,
        "V7 missing-marker simulation omitted successful CPI"
    );
    ensure!(
        simulation.units < 1_300_000,
        "honest production V7 exceeds 1.3M CU: {}",
        simulation.units
    );

    let evidence = serde_json::to_vec_pretty(&json!({
        "artifact": "aspis_v7_compact_onefold_production_sbf_simulation",
        "schema_version": 1,
        "sbf_path": sbf_path,
        "sbf_bytes": sbf.len(),
        "sbf_sha256": sha256(&sbf),
        "proof_path": proof_path,
        "proof_bytes": proof.len(),
        "proof_sha256": sha256(&proof),
        "statement_path": statement_path,
        "statement_sha256": sha256(&statement_bytes),
        "program_id": program_id.to_string(),
        "pool": pool.to_string(),
        "proof_account": proof_account.to_string(),
        "nullifier_marker": marker.to_string(),
        "compact_counter": metadata.compact_counter,
        "frontier_nodes_per_tree": metadata.frontier_nodes_per_tree,
        "compute_units": simulation.units,
        "headroom_under_1_3m": 1_300_000_i64 - simulation.units as i64,
        "missing_marker_completed_system_program_cpi": cpi_complete,
        "host_production_acceptance": true,
        "real_work_checks": true,
        "exact_terminal_equality": true,
        "build_command": "NO_DNA=1 cargo-build-sbf --manifest-path programs/aspis-verifier/Cargo.toml --no-default-features --features v7-production-tag73",
    }))?;
    let mut evidence_newline = evidence;
    evidence_newline.push(b'\n');
    create_new(&evidence_path, &evidence_newline)?;
    Ok(V7ProductionSimulationOutcome {
        compute_units: simulation.units,
        evidence_path,
    })
}

fn parse_adversarial_arguments(arguments: &[String]) -> Result<BTreeMap<String, String>> {
    const ALLOWED: [&str; 4] = ["--proof", "--statement", "--metadata", "--out"];
    let mut values = BTreeMap::new();
    let mut index = 0usize;
    while index < arguments.len() {
        let key = arguments
            .get(index)
            .context("missing adversarial argument")?;
        ensure!(
            ALLOWED.contains(&key.as_str()),
            "unknown adversarial argument {key}"
        );
        let item = arguments
            .get(index + 1)
            .ok_or_else(|| anyhow!("missing value for {key}"))?;
        ensure!(
            values.insert(key.clone(), item.clone()).is_none(),
            "duplicate adversarial argument {key}"
        );
        index += 2;
    }
    for key in ALLOWED {
        ensure!(
            values.contains_key(key),
            "missing adversarial argument {key}"
        );
    }
    Ok(values)
}

fn toggle_qm31_limb_low_bit(proof: &mut [u8], qm31_index: usize) {
    let bit = qm31_index * 4 * 31;
    proof[bit / 8] ^= 1 << (bit % 8);
}

fn toggle_packed_m31_limb_low_bit(proof: &mut [u8], section_start: usize, limb: usize) {
    let bit = section_start * 8 + limb * 31;
    proof[bit / 8] ^= 1 << (bit % 8);
}

fn overwrite_packed_m31(proof: &mut [u8], section_start: usize, limb: usize, value: u32) {
    debug_assert!(value < 1 << 31);
    let first_bit = section_start * 8 + limb * 31;
    for bit in 0..31 {
        let absolute = first_bit + bit;
        let mask = 1u8 << (absolute % 8);
        if (value >> bit) & 1 == 0 {
            proof[absolute / 8] &= !mask;
        } else {
            proof[absolute / 8] |= mask;
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn require_host_rejection(
    name: &str,
    category: &str,
    proof: &[u8],
    c1_frontier_nodes: usize,
    c2_frontier_nodes: usize,
    selector: u8,
    program_id: &Pubkey,
    release_binding: [u8; 32],
    proof_account: &Pubkey,
    statement: &AtomicPaymentStatementV4,
) -> Result<serde_json::Value> {
    let error = aspis_verifier::v6_verifier::verify_v6_read_only(
        HOST_HASH,
        proof,
        c1_frontier_nodes,
        c2_frontier_nodes,
        selector,
        program_id,
        release_binding,
        proof_account,
        statement,
        true,
    )
    .err()
    .with_context(|| format!("adversarial V6 case {name} was accepted"))?;
    Ok(json!({
        "name": name,
        "category": category,
        "rejected": true,
        "error": format!("{error:?}"),
    }))
}

fn require_v7_host_rejection(
    name: &str,
    category: &str,
    proof: &[u8],
    frontier_nodes: usize,
    program_id: &Pubkey,
    release_binding: [u8; 32],
    proof_account: &Pubkey,
    statement: &AtomicPaymentStatementV4,
) -> Result<serde_json::Value> {
    let error = aspis_verifier::v7_verifier::verify_v7_read_only(
        HOST_HASH,
        proof,
        frontier_nodes,
        program_id,
        release_binding,
        proof_account,
        statement,
        true,
    )
    .err()
    .with_context(|| format!("adversarial V7 case {name} was accepted"))?;
    Ok(json!({
        "name": name,
        "category": category,
        "rejected": true,
        "error": format!("{error:?}"),
    }))
}

/// Replay the honest production proof and then require rejection for a
/// position-complete set of fixed fields, query-record limbs, salts, frontier
/// nodes, transcript context, canonical encoding, framing, selector and
/// public-statement mutations.
/// Every replay keeps production PoW enabled.
pub(crate) fn run_adversarial(arguments: &[String]) -> Result<V6AdversarialOutcome> {
    let values = parse_adversarial_arguments(arguments)?;
    let proof_path = PathBuf::from(value(&values, "--proof")?);
    let statement_path = PathBuf::from(value(&values, "--statement")?);
    let metadata_path = PathBuf::from(value(&values, "--metadata")?);
    let evidence_path = PathBuf::from(value(&values, "--out")?);
    for path in [&proof_path, &statement_path, &metadata_path] {
        ensure!(
            path.is_absolute() && path.is_file(),
            "missing adversarial input {}",
            path.display()
        );
    }
    ensure!(evidence_path.is_absolute() && !evidence_path.exists());

    let proof = fs::read(&proof_path)?;
    let statement_bytes = fs::read(&statement_path)?;
    let metadata_bytes = fs::read(&metadata_path)?;
    let sidecar: V6StatementSidecar = serde_json::from_slice(&statement_bytes)?;
    let metadata: V6ProofMetadata = serde_json::from_slice(&metadata_bytes)?;
    let statement = statement_from_sidecar(&sidecar)?;
    ensure!(metadata.artifact == "aspis_v6_onefold_honest_mined_proof");
    ensure!(metadata.proof_sha256 == sha256(&proof));
    ensure!(metadata.statement_sha256 == sha256(&statement_bytes));
    ensure!(metadata.program_id == sidecar.program_id);
    ensure!(metadata.pool == sidecar.pool);
    ensure!(metadata.proof_account == sidecar.proof_account);
    ensure!(metadata.release_binding_hex == hex(&V6_RELEASE_BINDING));
    ensure!(metadata.all_work_checked && metadata.host_full_acceptance);
    ensure!(metadata.selector < 3 && metadata.compact_counter < 8);
    ensure!(
        metadata.frontier_nodes_per_tree <= V6_FRONTIER_CAP_PER_TREE,
        "metadata frontier exceeds V6 cap"
    );
    let frontier = metadata.frontier_nodes_per_tree;
    ensure!(frontier > 0, "metadata frontier must be nonzero");
    ensure!(
        proof.len() == V6_BODY_WITHOUT_FRONTIERS + 64 * frontier,
        "proof length/frontier mismatch"
    );
    let program_id = Pubkey::from_str(&sidecar.program_id)?;
    let proof_account = Pubkey::from_str(&sidecar.proof_account)?;
    ensure!(program_id == aspis_verifier::id());
    ensure!(sidecar.network_tag == "devnet");
    ensure!(
        atomic_deployment_domain(HOST_HASH, &program_id.to_bytes(), b"devnet")
            == statement.deployment_domain
    );

    let baseline = aspis_verifier::v6_verifier::verify_v6_read_only(
        HOST_HASH,
        &proof,
        frontier,
        frontier,
        metadata.selector,
        &program_id,
        V6_RELEASE_BINDING,
        &proof_account,
        &statement,
        true,
    )
    .map_err(|error| anyhow!("adversarial baseline rejected: {error:?}"))?;
    ensure!(baseline.transcript.compact_counter == metadata.compact_counter);
    ensure!(baseline.transcript.frontier_nodes == frontier);

    let mut proof_cases = Vec::<(String, &'static str, Vec<u8>)>::new();
    let fixed_field_category = |field: usize| {
        if field < V6_SEMANTIC_QM31_OFFSET {
            "initial_claim"
        } else if field < V6_POINT_CLAIMS_QM31_OFFSET {
            "semantic_sumcheck"
        } else if field < V6_INACTIVE_CLAIM_QM31_OFFSET {
            "point_claims"
        } else if field < V6_OOD_QM31_OFFSET {
            "inactive_claim"
        } else if field < V6_RELATION_QM31_OFFSET {
            "ood_values"
        } else if field < V6_FINAL_QM31_OFFSET {
            "relation_sumcheck"
        } else {
            "terminal_polynomial"
        }
    };
    for field in 0..V6_FIXED_QM31_VALUES {
        let mut mutated = proof.clone();
        toggle_qm31_limb_low_bit(&mut mutated, field);
        proof_cases.push((
            format!("fixed_qm31_{field}"),
            fixed_field_category(field),
            mutated,
        ));
    }

    let c1_root_start = V6_FIXED_PACKED_FIELD_BYTES;
    let c2_root_start = c1_root_start + 32;
    let nonce_start = c2_root_start + 32;
    for (name, offset) in [
        ("c1_root", c1_root_start),
        ("c2_root", c2_root_start),
        ("batch_work_nonce", nonce_start),
        ("fold_work_nonce", nonce_start + 8),
        ("final_work_nonce", nonce_start + 16),
    ] {
        let mut mutated = proof.clone();
        mutated[offset] ^= 1;
        proof_cases.push((name.to_owned(), "root_or_work", mutated));
    }

    let query_section_start = nonce_start + 24;
    for query in 0..V6_QUERY_COUNT {
        let query_start = query_section_start + query * V6_QUERY_BYTES;
        for limb in 0..V6_C1_LIMBS_PER_QUERY {
            let mut mutated = proof.clone();
            toggle_packed_m31_limb_low_bit(&mut mutated, query_start, limb);
            proof_cases.push((
                format!("query_{query}_c1_limb_{limb}"),
                "authenticated_query_c1",
                mutated,
            ));
        }
        let c2_start = query_start + V6_C1_PACKED_BYTES_PER_QUERY;
        for limb in 0..V6_C2_LIMBS_PER_QUERY {
            let mut mutated = proof.clone();
            toggle_packed_m31_limb_low_bit(&mut mutated, c2_start, limb);
            proof_cases.push((
                format!("query_{query}_c2_limb_{limb}"),
                "authenticated_query_c2",
                mutated,
            ));
        }
        let salt_start = c2_start + V6_C2_PACKED_BYTES_PER_QUERY;
        for byte in 0..V6_PRIVATE_SALT_BYTES {
            let mut mutated = proof.clone();
            mutated[salt_start + byte] ^= 1;
            proof_cases.push((
                format!("query_{query}_salt_byte_{byte}"),
                "authenticated_query_salt",
                mutated,
            ));
        }
    }

    let c1_frontier_start = V6_BODY_WITHOUT_FRONTIERS;
    let c2_frontier_start = c1_frontier_start + 32 * frontier;
    for (tree, start) in [("c1", c1_frontier_start), ("c2", c2_frontier_start)] {
        for node in 0..frontier {
            let mut mutated = proof.clone();
            mutated[start + 32 * node] ^= 1;
            proof_cases.push((
                format!("{tree}_frontier_node_{node}"),
                "merkle_frontier",
                mutated,
            ));
        }
    }

    let mut fixed_noncanonical = proof.clone();
    overwrite_packed_m31(&mut fixed_noncanonical, 0, 0, P);
    proof_cases.push((
        "noncanonical_fixed_m31".to_owned(),
        "canonical_encoding",
        fixed_noncanonical,
    ));
    let mut c1_noncanonical = proof.clone();
    overwrite_packed_m31(&mut c1_noncanonical, query_section_start, 0, P);
    proof_cases.push((
        "noncanonical_query_c1_m31".to_owned(),
        "canonical_encoding",
        c1_noncanonical,
    ));
    let mut c2_noncanonical = proof.clone();
    overwrite_packed_m31(
        &mut c2_noncanonical,
        query_section_start + V6_C1_PACKED_BYTES_PER_QUERY,
        0,
        P,
    );
    proof_cases.push((
        "noncanonical_query_c2_m31".to_owned(),
        "canonical_encoding",
        c2_noncanonical,
    ));
    let mut nonzero_padding = proof.clone();
    nonzero_padding[V6_FIXED_PACKED_FIELD_BYTES - 1] |= 0xf0;
    proof_cases.push((
        "nonzero_fixed_padding_bits".to_owned(),
        "canonical_encoding",
        nonzero_padding,
    ));

    let mut rejected = Vec::new();
    for (name, category, mutated) in &proof_cases {
        rejected.push(require_host_rejection(
            name,
            category,
            mutated,
            frontier,
            frontier,
            metadata.selector,
            &program_id,
            V6_RELEASE_BINDING,
            &proof_account,
            &statement,
        )?);
    }

    let truncated = &proof[..proof.len() - 1];
    rejected.push(require_host_rejection(
        "proof_truncated",
        "framing",
        truncated,
        frontier,
        frontier,
        metadata.selector,
        &program_id,
        V6_RELEASE_BINDING,
        &proof_account,
        &statement,
    )?);
    let mut trailing = proof.clone();
    trailing.push(0);
    rejected.push(require_host_rejection(
        "proof_trailing_byte",
        "framing",
        &trailing,
        frontier,
        frontier,
        metadata.selector,
        &program_id,
        V6_RELEASE_BINDING,
        &proof_account,
        &statement,
    )?);
    for (name, c1, c2) in [
        ("frontier_c1_minus_one", frontier - 1, frontier),
        ("frontier_c2_minus_one", frontier, frontier - 1),
        ("frontier_both_zero", 0, 0),
        ("frontier_above_cap", V6_FRONTIER_CAP_PER_TREE + 1, frontier),
    ] {
        rejected.push(require_host_rejection(
            name,
            "frontier_framing",
            &proof,
            c1,
            c2,
            metadata.selector,
            &program_id,
            V6_RELEASE_BINDING,
            &proof_account,
            &statement,
        )?);
    }
    for selector in 0u8..3 {
        if selector != metadata.selector {
            rejected.push(require_host_rejection(
                &format!("wrong_valid_selector_{selector}"),
                "selector_binding",
                &proof,
                frontier,
                frontier,
                selector,
                &program_id,
                V6_RELEASE_BINDING,
                &proof_account,
                &statement,
            )?);
        }
    }
    for selector in [3u8, u8::MAX] {
        rejected.push(require_host_rejection(
            &format!("invalid_selector_{selector}"),
            "selector_binding",
            &proof,
            frontier,
            frontier,
            selector,
            &program_id,
            V6_RELEASE_BINDING,
            &proof_account,
            &statement,
        )?);
    }

    let mut changed_binding = V6_RELEASE_BINDING;
    changed_binding[0] ^= 1;
    rejected.push(require_host_rejection(
        "release_binding",
        "transcript_context",
        &proof,
        frontier,
        frontier,
        metadata.selector,
        &program_id,
        changed_binding,
        &proof_account,
        &statement,
    )?);
    let changed_program = Pubkey::new_unique();
    rejected.push(require_host_rejection(
        "runtime_program_id",
        "transcript_context",
        &proof,
        frontier,
        frontier,
        metadata.selector,
        &changed_program,
        V6_RELEASE_BINDING,
        &proof_account,
        &statement,
    )?);
    let changed_attempt = Pubkey::new_unique();
    rejected.push(require_host_rejection(
        "proof_account_attempt_id",
        "transcript_context",
        &proof,
        frontier,
        frontier,
        metadata.selector,
        &program_id,
        V6_RELEASE_BINDING,
        &changed_attempt,
        &statement,
    )?);

    let mut statement_cases = Vec::<(&'static str, AtomicPaymentStatementV4)>::new();
    let mut changed = statement.clone();
    changed.pool[0] ^= 1;
    statement_cases.push(("statement_pool", changed));
    let mut changed = statement.clone();
    changed.sequence = changed
        .sequence
        .checked_add(1)
        .context("sequence overflow")?;
    statement_cases.push(("statement_sequence", changed));
    let mut changed = statement.clone();
    changed.spend.anchor[0].0 ^= 1;
    statement_cases.push(("statement_current_anchor", changed));
    let mut changed = statement.clone();
    changed.spend.nullifier[0].0 ^= 1;
    statement_cases.push(("statement_nullifier", changed));
    let mut changed = statement.clone();
    changed.spend.output_commitment[0].0 ^= 1;
    statement_cases.push(("statement_output_commitment", changed));
    let mut changed = statement.clone();
    changed.output_anchor[0].0 ^= 1;
    statement_cases.push(("statement_output_anchor", changed));
    let mut changed = statement.clone();
    changed.spend.asset_id = M31(changed.spend.asset_id.0 ^ 1);
    statement_cases.push(("statement_asset_id", changed));
    let mut changed = statement.clone();
    changed.spend.fee ^= 1;
    statement_cases.push(("statement_fee", changed));
    let mut changed = statement.clone();
    changed.deployment_domain[0] ^= 1;
    statement_cases.push(("statement_deployment_domain", changed));
    for (name, changed) in &statement_cases {
        rejected.push(require_host_rejection(
            name,
            "public_statement_binding",
            &proof,
            frontier,
            frontier,
            metadata.selector,
            &program_id,
            V6_RELEASE_BINDING,
            &proof_account,
            changed,
        )?);
    }

    let baseline_wire = production_instruction(frontier, metadata.selector, &statement)?;
    ensure!(
        aspis_verifier::v6_transaction::process_v6_atomic_instruction(
            &program_id,
            &[],
            &baseline_wire,
        ) == Err(solana_sdk::program_error::ProgramError::NotEnoughAccountKeys),
        "exact V6 wire did not pass framing before account validation"
    );
    let mut bad_tag = baseline_wire.clone();
    bad_tag[0] ^= 1;
    let mut trailing_wire = baseline_wire.clone();
    trailing_wire.push(0);
    for (name, wire) in [
        ("instruction_bad_tag", bad_tag.as_slice()),
        (
            "instruction_truncated",
            &baseline_wire[..baseline_wire.len() - 1],
        ),
        ("instruction_trailing_byte", trailing_wire.as_slice()),
    ] {
        ensure!(
            aspis_verifier::v6_transaction::process_v6_atomic_instruction(&program_id, &[], wire,)
                == Err(solana_sdk::program_error::ProgramError::InvalidInstructionData),
            "malformed production wire {name} passed exact framing"
        );
        rejected.push(json!({
            "name": name,
            "category": "instruction_framing",
            "rejected": true,
            "error": "InvalidInstructionData",
        }));
    }

    let rejected_case_count = rejected.len();
    let evidence = serde_json::to_vec_pretty(&json!({
        "artifact": "aspis_v6_onefold_host_adversarial_replay",
        "schema_version": 1,
        "proof_path": proof_path,
        "proof_bytes": proof.len(),
        "proof_sha256": sha256(&proof),
        "statement_path": statement_path,
        "statement_sha256": sha256(&statement_bytes),
        "metadata_path": metadata_path,
        "metadata_sha256": sha256(&metadata_bytes),
        "program_id": program_id.to_string(),
        "proof_account": proof_account.to_string(),
        "selector": metadata.selector,
        "compact_counter": metadata.compact_counter,
        "frontier_nodes_per_tree": frontier,
        "production_pow_enabled_for_every_host_replay": true,
        "honest_baseline_accepted": true,
        "all_mutations_rejected": true,
        "rejected_case_count": rejected_case_count,
        "cases": rejected,
        "scope": [
            "every one of the 641 fixed QM31 positions",
            "every semantic and relation sumcheck coefficient",
            "every point-claim and final-polynomial coefficient",
            "every M31 limb and every salt byte in all sixteen query records",
            "both roots and all three work nonces",
            "every node in both Merkle frontiers",
            "canonical packed-field and padding teeth",
            "proof and instruction exact framing",
            "selector/frontier metadata",
            "program/release/attempt transcript context",
            "every public statement component"
        ],
    }))?;
    let mut evidence_newline = evidence;
    evidence_newline.push(b'\n');
    create_new(&evidence_path, &evidence_newline)?;
    Ok(V6AdversarialOutcome {
        rejected_cases: rejected_case_count,
        evidence_path,
    })
}

/// Replay the frozen V7 production proof and require rejection for a
/// position-complete set of authenticated wire and public-context mutations.
/// This is deliberately a single focused release corpus, not a broad test run.
pub(crate) fn run_v7_adversarial(arguments: &[String]) -> Result<V6AdversarialOutcome> {
    let values = parse_adversarial_arguments(arguments)?;
    let proof_path = PathBuf::from(value(&values, "--proof")?);
    let statement_path = PathBuf::from(value(&values, "--statement")?);
    let metadata_path = PathBuf::from(value(&values, "--metadata")?);
    let evidence_path = PathBuf::from(value(&values, "--out")?);
    for path in [&proof_path, &statement_path, &metadata_path] {
        ensure!(
            path.is_absolute() && path.is_file(),
            "missing adversarial input {}",
            path.display()
        );
    }
    ensure!(evidence_path.is_absolute() && !evidence_path.exists());

    let proof = fs::read(&proof_path)?;
    let statement_bytes = fs::read(&statement_path)?;
    let metadata_bytes = fs::read(&metadata_path)?;
    let sidecar: V6StatementSidecar = serde_json::from_slice(&statement_bytes)?;
    let metadata: V7ProofMetadata = serde_json::from_slice(&metadata_bytes)?;
    let statement = statement_from_v7_sidecar(&sidecar)?;
    ensure!(metadata.artifact == "aspis_v7_compact_onefold_honest_mined_proof");
    ensure!(metadata.proof_sha256 == sha256(&proof));
    ensure!(metadata.statement_sha256 == sha256(&statement_bytes));
    ensure!(metadata.program_id == sidecar.program_id);
    ensure!(metadata.pool == sidecar.pool);
    ensure!(metadata.proof_account == sidecar.proof_account);
    ensure!(metadata.release_binding_hex == hex(&V7_RELEASE_BINDING));
    ensure!(metadata.all_work_checked && metadata.host_full_acceptance);
    ensure!(metadata.compact_counter < 64);
    ensure!(metadata.frontier_digest_bytes == V7_COMPACT_DIGEST_BYTES);
    ensure!(
        metadata.frontier_nodes_per_tree <= V7_COMPACT_FRONTIER_CAP_PER_TREE,
        "metadata frontier exceeds V7 cap"
    );
    let frontier = metadata.frontier_nodes_per_tree;
    ensure!(frontier > 0, "metadata frontier must be nonzero");
    ensure!(
        proof.len() == V7_COMPACT_BODY_WITHOUT_FRONTIERS + 2 * V7_COMPACT_DIGEST_BYTES * frontier,
        "proof length/frontier mismatch"
    );
    let program_id = Pubkey::from_str(&sidecar.program_id)?;
    let proof_account = Pubkey::from_str(&sidecar.proof_account)?;
    ensure!(program_id == aspis_verifier::id());
    ensure!(sidecar.network_tag == "devnet");
    ensure!(
        atomic_deployment_domain(HOST_HASH, &program_id.to_bytes(), b"devnet")
            == statement.deployment_domain
    );

    let baseline = aspis_verifier::v7_verifier::verify_v7_read_only(
        HOST_HASH,
        &proof,
        frontier,
        &program_id,
        V7_RELEASE_BINDING,
        &proof_account,
        &statement,
        true,
    )
    .map_err(|error| anyhow!("V7 adversarial baseline rejected: {error:?}"))?;
    ensure!(baseline.transcript.compact_counter == metadata.compact_counter);
    ensure!(baseline.transcript.frontier_nodes == frontier);

    let fixed_field_category = |field: usize| {
        if field < V6_SEMANTIC_QM31_OFFSET {
            "initial_claim"
        } else if field < V6_POINT_CLAIMS_QM31_OFFSET {
            "semantic_sumcheck"
        } else if field < V6_INACTIVE_CLAIM_QM31_OFFSET {
            "point_claims"
        } else if field < V6_OOD_QM31_OFFSET {
            "inactive_claim"
        } else if field < V6_RELATION_QM31_OFFSET {
            "ood_values"
        } else if field < V6_FINAL_QM31_OFFSET {
            "relation_sumcheck"
        } else {
            "terminal_polynomial"
        }
    };
    let mut rejected = Vec::with_capacity(4_020);
    for field in 0..V6_FIXED_QM31_VALUES {
        let mut mutated = proof.clone();
        toggle_qm31_limb_low_bit(&mut mutated, field);
        rejected.push(require_v7_host_rejection(
            &format!("fixed_qm31_{field}"),
            fixed_field_category(field),
            &mutated,
            frontier,
            &program_id,
            V7_RELEASE_BINDING,
            &proof_account,
            &statement,
        )?);
    }

    let c1_root_start = V6_FIXED_PACKED_FIELD_BYTES;
    let c2_root_start = c1_root_start + V7_COMPACT_DIGEST_BYTES;
    let nonce_start = c2_root_start + V7_COMPACT_DIGEST_BYTES;
    for (name, offset) in [
        ("c1_root", c1_root_start),
        ("c2_root", c2_root_start),
        ("batch_work_nonce", nonce_start),
        ("fold_work_nonce", nonce_start + 8),
        ("final_work_nonce", nonce_start + 16),
    ] {
        let mut mutated = proof.clone();
        mutated[offset] ^= 1;
        rejected.push(require_v7_host_rejection(
            name,
            "root_or_work",
            &mutated,
            frontier,
            &program_id,
            V7_RELEASE_BINDING,
            &proof_account,
            &statement,
        )?);
    }

    let query_section_start = nonce_start + 24;
    for query in 0..V6_QUERY_COUNT {
        let query_start = query_section_start + query * V7_COMPACT_QUERY_BYTES;
        for limb in 0..V6_C1_LIMBS_PER_QUERY {
            let mut mutated = proof.clone();
            toggle_packed_m31_limb_low_bit(&mut mutated, query_start, limb);
            rejected.push(require_v7_host_rejection(
                &format!("query_{query}_c1_limb_{limb}"),
                "authenticated_query_c1",
                &mutated,
                frontier,
                &program_id,
                V7_RELEASE_BINDING,
                &proof_account,
                &statement,
            )?);
        }
        let c2_start = query_start + V7_COMPACT_C1_BYTES_PER_QUERY;
        for limb in 0..V6_C2_LIMBS_PER_QUERY {
            let mut mutated = proof.clone();
            toggle_packed_m31_limb_low_bit(&mut mutated, c2_start, limb);
            rejected.push(require_v7_host_rejection(
                &format!("query_{query}_c2_limb_{limb}"),
                "authenticated_query_c2",
                &mutated,
                frontier,
                &program_id,
                V7_RELEASE_BINDING,
                &proof_account,
                &statement,
            )?);
        }
        let salt_start = c2_start + V7_COMPACT_C2_BYTES_PER_QUERY;
        for byte in 0..V7_COMPACT_PRIVATE_SALT_BYTES {
            let mut mutated = proof.clone();
            mutated[salt_start + byte] ^= 1;
            rejected.push(require_v7_host_rejection(
                &format!("query_{query}_salt_byte_{byte}"),
                "authenticated_query_salt",
                &mutated,
                frontier,
                &program_id,
                V7_RELEASE_BINDING,
                &proof_account,
                &statement,
            )?);
        }
    }

    let c1_frontier_start = V7_COMPACT_BODY_WITHOUT_FRONTIERS;
    let c2_frontier_start = c1_frontier_start + V7_COMPACT_DIGEST_BYTES * frontier;
    for (tree, start) in [("c1", c1_frontier_start), ("c2", c2_frontier_start)] {
        for node in 0..frontier {
            let mut mutated = proof.clone();
            mutated[start + V7_COMPACT_DIGEST_BYTES * node] ^= 1;
            rejected.push(require_v7_host_rejection(
                &format!("{tree}_frontier_node_{node}"),
                "merkle_frontier",
                &mutated,
                frontier,
                &program_id,
                V7_RELEASE_BINDING,
                &proof_account,
                &statement,
            )?);
        }
    }

    for (name, section_start) in [
        ("noncanonical_fixed_m31", 0),
        ("noncanonical_query_c1_m31", query_section_start),
        (
            "noncanonical_query_c2_m31",
            query_section_start + V7_COMPACT_C1_BYTES_PER_QUERY,
        ),
    ] {
        let mut mutated = proof.clone();
        overwrite_packed_m31(&mut mutated, section_start, 0, P);
        rejected.push(require_v7_host_rejection(
            name,
            "canonical_encoding",
            &mutated,
            frontier,
            &program_id,
            V7_RELEASE_BINDING,
            &proof_account,
            &statement,
        )?);
    }
    let mut nonzero_padding = proof.clone();
    nonzero_padding[V6_FIXED_PACKED_FIELD_BYTES - 1] |= 0xf0;
    rejected.push(require_v7_host_rejection(
        "nonzero_fixed_padding_bits",
        "canonical_encoding",
        &nonzero_padding,
        frontier,
        &program_id,
        V7_RELEASE_BINDING,
        &proof_account,
        &statement,
    )?);

    rejected.push(require_v7_host_rejection(
        "proof_truncated",
        "framing",
        &proof[..proof.len() - 1],
        frontier,
        &program_id,
        V7_RELEASE_BINDING,
        &proof_account,
        &statement,
    )?);
    let mut trailing = proof.clone();
    trailing.push(0);
    rejected.push(require_v7_host_rejection(
        "proof_trailing_byte",
        "framing",
        &trailing,
        frontier,
        &program_id,
        V7_RELEASE_BINDING,
        &proof_account,
        &statement,
    )?);
    for (name, changed_frontier) in [
        ("frontier_minus_one", frontier - 1),
        ("frontier_zero", 0),
        ("frontier_above_cap", V7_COMPACT_FRONTIER_CAP_PER_TREE + 1),
    ] {
        rejected.push(require_v7_host_rejection(
            name,
            "frontier_framing",
            &proof,
            changed_frontier,
            &program_id,
            V7_RELEASE_BINDING,
            &proof_account,
            &statement,
        )?);
    }

    let mut changed_binding = V7_RELEASE_BINDING;
    changed_binding[0] ^= 1;
    rejected.push(require_v7_host_rejection(
        "release_binding",
        "transcript_context",
        &proof,
        frontier,
        &program_id,
        changed_binding,
        &proof_account,
        &statement,
    )?);
    let changed_program = Pubkey::new_unique();
    rejected.push(require_v7_host_rejection(
        "runtime_program_id",
        "transcript_context",
        &proof,
        frontier,
        &changed_program,
        V7_RELEASE_BINDING,
        &proof_account,
        &statement,
    )?);
    let changed_attempt = Pubkey::new_unique();
    rejected.push(require_v7_host_rejection(
        "proof_account_attempt_id",
        "transcript_context",
        &proof,
        frontier,
        &program_id,
        V7_RELEASE_BINDING,
        &changed_attempt,
        &statement,
    )?);

    let mut statement_cases = Vec::<(&'static str, AtomicPaymentStatementV4)>::new();
    let mut changed = statement.clone();
    changed.pool[0] ^= 1;
    statement_cases.push(("statement_pool", changed));
    let mut changed = statement.clone();
    changed.sequence = changed
        .sequence
        .checked_add(1)
        .context("sequence overflow")?;
    statement_cases.push(("statement_sequence", changed));
    let mut changed = statement.clone();
    changed.spend.anchor[0].0 ^= 1;
    statement_cases.push(("statement_current_anchor", changed));
    let mut changed = statement.clone();
    changed.spend.nullifier[0].0 ^= 1;
    statement_cases.push(("statement_nullifier", changed));
    let mut changed = statement.clone();
    changed.spend.output_commitment[0].0 ^= 1;
    statement_cases.push(("statement_output_commitment", changed));
    let mut changed = statement.clone();
    changed.output_anchor[0].0 ^= 1;
    statement_cases.push(("statement_output_anchor", changed));
    let mut changed = statement.clone();
    changed.spend.asset_id = M31(changed.spend.asset_id.0 ^ 1);
    statement_cases.push(("statement_asset_id", changed));
    let mut changed = statement.clone();
    changed.spend.fee ^= 1;
    statement_cases.push(("statement_fee", changed));
    let mut changed = statement.clone();
    changed.deployment_domain[0] ^= 1;
    statement_cases.push(("statement_deployment_domain", changed));
    for (name, changed) in &statement_cases {
        rejected.push(require_v7_host_rejection(
            name,
            "public_statement_binding",
            &proof,
            frontier,
            &program_id,
            V7_RELEASE_BINDING,
            &proof_account,
            changed,
        )?);
    }

    let baseline_wire = v7_production_instruction(frontier, &statement)?;
    ensure!(
        aspis_verifier::v7_transaction::process_v7_atomic_instruction(
            &program_id,
            &[],
            &baseline_wire,
        ) == Err(solana_sdk::program_error::ProgramError::NotEnoughAccountKeys),
        "exact V7 wire did not pass framing before account validation"
    );
    let mut bad_tag = baseline_wire.clone();
    bad_tag[0] ^= 1;
    let mut trailing_wire = baseline_wire.clone();
    trailing_wire.push(0);
    for (name, wire) in [
        ("instruction_bad_tag", bad_tag.as_slice()),
        (
            "instruction_truncated",
            &baseline_wire[..baseline_wire.len() - 1],
        ),
        ("instruction_trailing_byte", trailing_wire.as_slice()),
    ] {
        ensure!(
            aspis_verifier::v7_transaction::process_v7_atomic_instruction(&program_id, &[], wire,)
                == Err(solana_sdk::program_error::ProgramError::InvalidInstructionData),
            "malformed production wire {name} passed exact framing"
        );
        rejected.push(json!({
            "name": name,
            "category": "instruction_framing",
            "rejected": true,
            "error": "InvalidInstructionData",
        }));
    }

    let rejected_case_count = rejected.len();
    ensure!(
        rejected_case_count == 4_020,
        "V7 adversarial inventory drifted: expected 4020, got {rejected_case_count}"
    );
    let evidence = serde_json::to_vec_pretty(&json!({
        "artifact": "aspis_v7_onefold_host_adversarial_replay",
        "schema_version": 1,
        "proof_path": proof_path,
        "proof_bytes": proof.len(),
        "proof_sha256": sha256(&proof),
        "statement_path": statement_path,
        "statement_sha256": sha256(&statement_bytes),
        "metadata_path": metadata_path,
        "metadata_sha256": sha256(&metadata_bytes),
        "program_id": program_id.to_string(),
        "proof_account": proof_account.to_string(),
        "compact_counter": metadata.compact_counter,
        "frontier_nodes_per_tree": frontier,
        "frontier_digest_bytes": V7_COMPACT_DIGEST_BYTES,
        "production_pow_enabled_for_every_host_replay": true,
        "honest_baseline_accepted": true,
        "all_mutations_rejected": true,
        "rejected_case_count": rejected_case_count,
        "cases": rejected,
        "scope": [
            "every one of the 641 fixed QM31 positions",
            "every semantic and relation sumcheck coefficient",
            "every point-claim and final-polynomial coefficient",
            "every M31 limb and every 256-bit salt byte in all sixteen complete-C2 query records",
            "both 208-bit roots and all three work nonces",
            "every 208-bit node in both Merkle frontiers",
            "canonical packed-field and padding teeth",
            "proof and instruction exact framing",
            "frontier metadata",
            "program/release/attempt transcript context",
            "every public statement component"
        ],
    }))?;
    let mut evidence_newline = evidence;
    evidence_newline.push(b'\n');
    create_new(&evidence_path, &evidence_newline)?;
    Ok(V6AdversarialOutcome {
        rejected_cases: rejected_case_count,
        evidence_path,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn v6_demo_nullifier_is_deterministic_and_bound_to_fresh_pool() {
        let domain = [0x5au8; 32];
        let pool_a = Pubkey::new_from_array([0x11; 32]);
        let pool_b = Pubkey::new_from_array([0x22; 32]);
        let (statement_a1, witness_a1) =
            honest_demo_statement_and_witness(pool_a, 0, domain).unwrap();
        let (statement_a2, witness_a2) =
            honest_demo_statement_and_witness(pool_a, 0, domain).unwrap();
        let (statement_b, _) = honest_demo_statement_and_witness(pool_b, 0, domain).unwrap();

        assert_eq!(statement_a1, statement_a2);
        assert_eq!(witness_a1, witness_a2);
        assert_ne!(statement_a1.spend.nullifier, statement_b.spend.nullifier);
        assert_ne!(statement_a1.spend.anchor, statement_b.spend.anchor);
    }

    #[test]
    fn bound_demo_digest_limbs_are_canonical_m31() {
        let pool = Pubkey::new_from_array([0x33; 32]);
        let digest = bound_demo_digest(b"canonicality", &pool, 7, &[0xa5; 32]);
        assert!(digest.iter().all(|limb| limb.0 < P));
    }
}
