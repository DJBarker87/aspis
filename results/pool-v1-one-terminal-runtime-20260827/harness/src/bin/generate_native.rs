use std::{env, fs, path::PathBuf};

use anyhow::{anyhow, Context, Result};
use aspis_core::field::M31;
use aspis_pool::{pool_v1_state_address, POOL_V1_EMPTY_ROOTS};
use aspis_prover::{
    state_only_entropy::StateOnlyAttemptSecrets,
    state_only_hiding::InMemoryStateOnlyMaskNonceStore,
    v6_onefold_prover::{build_v7_pool_private_transfer_onefold_proof_production, V7ProverContext},
    HOST_HASH,
};
use aspis_statement::{
    derive_owner_key,
    pool_v1::{
        encode_pool_v1_private_transfer_public_v1, pool_v1_membership_root_v1,
        pool_v1_note_commitment, pool_v1_nullifier, verifier_statement_payload_digest_v1,
        PoolV1InputNoteWitnessV1, PoolV1MembershipWitnessV1, PoolV1OutputNoteWitnessV1,
        PoolV1PaymentRelationContextV1, PoolV1PaymentRuntimeBindingV1,
        PoolV1PrivateTransferPublicV1, PoolV1PrivateTransferWitnessV1,
        POOL_V1_HISTORICAL_ANCHOR_VERSION, V7_POOL_NATIVE_TAG73_PROFILE_BINDING,
        V7_POOL_NATIVE_TAG73_RELEASE_BINDING,
    },
    poseidon2::Digest,
};
use serde::Serialize;
use sha2::{Digest as ShaDigest, Sha256};
use solana_program::pubkey::Pubkey;

const POOL_PROGRAM_BYTES: [u8; 32] = [0xA5; 32];
const VERIFIER_PROGRAM_BYTES: [u8; 32] = [0xB6; 32];
const MINT_BYTES: [u8; 32] = [0x51; 32];
const PROOF_ACCOUNT_BYTES: [u8; 32] = [0x71; 32];
const DEPLOYMENT_DOMAIN_BYTES: [u8; 32] = [0x4C; 32];
const ASSET_ID: M31 = M31(73);

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + 29 * index as u32))
}

fn sha256_hex(bytes: &[u8]) -> String {
    let mut hash = Sha256::new();
    hash.update(bytes);
    hash.finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn bytes_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

#[derive(Serialize)]
struct ProofEvidence {
    schema: &'static str,
    proof_bytes: usize,
    proof_sha256: String,
    frontier_nodes_per_tree: usize,
    queries: [u32; 16],
    work_nonces: [u64; 3],
    all_work_checked: bool,
    pool: String,
    verifier_program: String,
    proof_account: String,
    anchor_sequence: u64,
    input_note_commitment: Vec<u32>,
    anchor_root: Vec<u32>,
    nullifier: Vec<u32>,
    recipient_commitment: Vec<u32>,
    change_commitment: Vec<u32>,
    statement_digest_hex: String,
}

fn main() -> Result<()> {
    let mut args = env::args_os().skip(1);
    let proof_path = args
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| anyhow!("usage: generate_native <proof.bin> <evidence.json>"))?;
    let evidence_path = args
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| anyhow!("usage: generate_native <proof.bin> <evidence.json>"))?;
    if args.next().is_some() {
        return Err(anyhow!("unexpected extra argument"));
    }

    let pool_program = Pubkey::new_from_array(POOL_PROGRAM_BYTES);
    let mint = Pubkey::new_from_array(MINT_BYTES);
    let pool = pool_v1_state_address(&pool_program, &mint).0;

    let input = PoolV1InputNoteWitnessV1 {
        nullifier_key: digest(10),
        salt: digest(700),
        value: 1_000,
        membership: PoolV1MembershipWitnessV1 {
            siblings: core::array::from_fn(|level| POOL_V1_EMPTY_ROOTS[level]),
            index: 0,
        },
    };
    let recipient = PoolV1OutputNoteWitnessV1 {
        owner_key: digest(2_300),
        salt: digest(2_400),
        value: 600,
    };
    let change = PoolV1OutputNoteWitnessV1 {
        owner_key: digest(2_500),
        salt: digest(2_600),
        value: 400,
    };
    let witness = PoolV1PrivateTransferWitnessV1 {
        input,
        recipient,
        change,
    };
    let input_note = pool_v1_note_commitment(
        &derive_owner_key(&witness.input.nullifier_key),
        witness.input.value,
        ASSET_ID,
        &witness.input.salt,
    );
    let anchor_root = pool_v1_membership_root_v1(input_note, &witness.input.membership)
        .map_err(|error| anyhow!("construct input membership root: {error:?}"))?;
    let public = PoolV1PrivateTransferPublicV1 {
        pool: pool.to_bytes(),
        deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
        anchor_sequence: 1,
        anchor_root,
        nullifier: pool_v1_nullifier(&witness.input.nullifier_key, &witness.input.salt),
        asset_id: ASSET_ID,
        recipient_commitment: pool_v1_note_commitment(
            &witness.recipient.owner_key,
            witness.recipient.value,
            ASSET_ID,
            &witness.recipient.salt,
        ),
        change_commitment: pool_v1_note_commitment(
            &witness.change.owner_key,
            witness.change.value,
            ASSET_ID,
            &witness.change.salt,
        ),
    };
    let payload = encode_pool_v1_private_transfer_public_v1(&public)
        .map_err(|error| anyhow!("encode native Pool statement: {error:?}"))?;
    let statement_digest = verifier_statement_payload_digest_v1(
        POOL_V1_HISTORICAL_ANCHOR_VERSION,
        &V7_POOL_NATIVE_TAG73_PROFILE_BINDING,
        &V7_POOL_NATIVE_TAG73_RELEASE_BINDING,
        &payload,
        HOST_HASH,
    )
    .map_err(|error| anyhow!("derive statement digest: {error:?}"))?;
    let relation_context = PoolV1PaymentRelationContextV1 {
        runtime_binding: PoolV1PaymentRuntimeBindingV1 {
            pool: public.pool,
            deployment_domain: public.deployment_domain,
            anchor_sequence: public.anchor_sequence,
            anchor_root: public.anchor_root,
            asset_id: public.asset_id,
        },
        spent_nullifiers: &[],
    };
    let context = V7ProverContext {
        program_id: VERIFIER_PROGRAM_BYTES,
        release_binding: V7_POOL_NATIVE_TAG73_RELEASE_BINDING,
        attempt_id: PROOF_ACCOUNT_BYTES,
    };
    let attempt = StateOnlyAttemptSecrets::deterministic_spend_fixture(
        PROOF_ACCOUNT_BYTES,
        [0x49; 32],
        [0x6B; 32],
    );
    let mut nonce_store = InMemoryStateOnlyMaskNonceStore::default();
    let proof = build_v7_pool_private_transfer_onefold_proof_production(
        &public,
        &witness,
        relation_context,
        statement_digest,
        context,
        attempt,
        &mut nonce_store,
        HOST_HASH,
    )
    .map_err(|error| anyhow!("build native Pool Tag-73 proof: {error:?}"))?;
    if !proof.pow_valid {
        return Err(anyhow!("production proof returned without valid work"));
    }

    fs::write(&proof_path, &proof.bytes)
        .with_context(|| format!("write {}", proof_path.display()))?;
    let limbs = |value: Digest| value.into_iter().map(|limb| limb.0).collect::<Vec<_>>();
    let evidence = ProofEvidence {
        schema: "aspis.pool-v1.native-tag73-proof.v1",
        proof_bytes: proof.bytes.len(),
        proof_sha256: sha256_hex(&proof.bytes),
        frontier_nodes_per_tree: proof.frontier_nodes,
        queries: proof.queries,
        work_nonces: proof.work_nonces,
        all_work_checked: proof.pow_valid,
        pool: pool.to_string(),
        verifier_program: Pubkey::new_from_array(VERIFIER_PROGRAM_BYTES).to_string(),
        proof_account: Pubkey::new_from_array(PROOF_ACCOUNT_BYTES).to_string(),
        anchor_sequence: public.anchor_sequence,
        input_note_commitment: limbs(input_note),
        anchor_root: limbs(public.anchor_root),
        nullifier: limbs(public.nullifier),
        recipient_commitment: limbs(public.recipient_commitment),
        change_commitment: limbs(public.change_commitment),
        statement_digest_hex: bytes_hex(&statement_digest),
    };
    fs::write(&evidence_path, serde_json::to_vec_pretty(&evidence)?)
        .with_context(|| format!("write {}", evidence_path.display()))?;
    println!(
        "native Pool Tag-73 proof: bytes={} frontier={} sha256={}",
        proof.bytes.len(),
        proof.frontier_nodes,
        sha256_hex(&proof.bytes),
    );
    Ok(())
}
