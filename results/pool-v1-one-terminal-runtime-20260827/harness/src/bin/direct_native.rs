use std::{env, fs, path::PathBuf};

use anyhow::{anyhow, bail, Context, Result};
use aspis_core::{field::M31, transcript::HashFn};
use aspis_pool::{pool_v1_state_address, POOL_V1_EMPTY_ROOTS};
use aspis_statement::{
    derive_owner_key,
    pool_v1::{
        encode_pool_v1_private_transfer_public_v1, encode_verifier_dispatch_request_v1,
        pool_v1_membership_root_v1, pool_v1_note_commitment, pool_v1_nullifier,
        verifier_dispatch_binding_from_envelope_v1, verifier_proof_body_digest_v1,
        HistoricalAnchorEnvelopeV1, PoolV1MembershipWitnessV1, PoolV1PrivateTransferPublicV1,
        PoolV1TransitionKind, VerifierDispatchRequestV1,
        POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES, POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC,
        V7_POOL_NATIVE_TAG73_PROFILE_BINDING, V7_POOL_NATIVE_TAG73_RELEASE_BINDING,
    },
    poseidon2::Digest,
};
use litesvm::LiteSVM;
use serde_json::json;
use sha2::{Digest as ShaDigest, Sha256};
use solana_account::Account;
use solana_address::Address;
use solana_compute_budget_interface::ComputeBudgetInstruction;
use solana_instruction::{AccountMeta, Instruction};
use solana_keypair::Keypair;
use solana_signer::Signer;
use solana_transaction::Transaction;

const VERIFIER: [u8; 32] = [0xB6; 32];
const POOL_PROGRAM: [u8; 32] = [0xA5; 32];
const PROOF_ACCOUNT: [u8; 32] = [0x71; 32];
const DEPLOYMENT: [u8; 32] = [0x4C; 32];
const MINT: [u8; 32] = [0x51; 32];
const ASSET: M31 = M31(73);
const CU_LIMIT: u32 = 1_400_000;

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + 29 * index as u32))
}

fn host_hash(parts: &[&[u8]]) -> [u8; 32] {
    let mut hash = Sha256::new();
    for part in parts {
        hash.update(part);
    }
    hash.finalize().into()
}

fn sha256_hex(bytes: &[u8]) -> String {
    host_hash(&[bytes])
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn proof_data(body: &[u8]) -> Vec<u8> {
    let mut data = vec![0; POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES + body.len()];
    data[..4].copy_from_slice(&POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC);
    data[4..8].copy_from_slice(&(body.len() as u32).to_le_bytes());
    data[POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES..].copy_from_slice(body);
    data
}

fn main() -> Result<()> {
    let mut args = env::args_os().skip(1);
    let verifier_path = args
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| anyhow!("usage: direct_native <verifier.so> <proof.bin> <evidence.json>"))?;
    let proof_path = args
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| anyhow!("usage: direct_native <verifier.so> <proof.bin> <evidence.json>"))?;
    let output_path = args
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| anyhow!("usage: direct_native <verifier.so> <proof.bin> <evidence.json>"))?;
    if args.next().is_some() {
        bail!("unexpected extra argument");
    }

    let verifier = fs::read(&verifier_path)?;
    let proof = fs::read(&proof_path)?;
    let pool_program = solana_program::pubkey::Pubkey::new_from_array(POOL_PROGRAM);
    let mint = solana_program::pubkey::Pubkey::new_from_array(MINT);
    let pool = pool_v1_state_address(&pool_program, &mint).0;
    let input_note =
        pool_v1_note_commitment(&derive_owner_key(&digest(10)), 1_000, ASSET, &digest(700));
    let anchor_root = pool_v1_membership_root_v1(
        input_note,
        &PoolV1MembershipWitnessV1 {
            siblings: core::array::from_fn(|level| POOL_V1_EMPTY_ROOTS[level]),
            index: 0,
        },
    )
    .map_err(|error| anyhow!("derive anchor root: {error:?}"))?;
    let statement = PoolV1PrivateTransferPublicV1 {
        pool: pool.to_bytes(),
        deployment_domain: DEPLOYMENT,
        anchor_sequence: 1,
        anchor_root,
        nullifier: pool_v1_nullifier(&digest(10), &digest(700)),
        asset_id: ASSET,
        recipient_commitment: pool_v1_note_commitment(&digest(2_300), 600, ASSET, &digest(2_400)),
        change_commitment: pool_v1_note_commitment(&digest(2_500), 400, ASSET, &digest(2_600)),
    };
    let payload = encode_pool_v1_private_transfer_public_v1(&statement)
        .map_err(|error| anyhow!("encode statement: {error:?}"))?;
    let envelope = HistoricalAnchorEnvelopeV1 {
        transition_kind: PoolV1TransitionKind::PrivateTransfer,
        pool: statement.pool,
        deployment_domain: statement.deployment_domain,
        anchor_sequence: statement.anchor_sequence,
        anchor_root: statement.anchor_root,
        nullifier: statement.nullifier,
        verifier_profile: V7_POOL_NATIVE_TAG73_PROFILE_BINDING,
        verifier_release: V7_POOL_NATIVE_TAG73_RELEASE_BINDING,
    };
    let binding = verifier_dispatch_binding_from_envelope_v1(
        VERIFIER,
        &envelope,
        &payload,
        PROOF_ACCOUNT,
        verifier_proof_body_digest_v1(&proof, host_hash as HashFn),
        proof.len() as u32,
        host_hash as HashFn,
    )
    .map_err(|error| anyhow!("construct binding: {error:?}"))?;
    let request = encode_verifier_dispatch_request_v1(
        &VerifierDispatchRequestV1 {
            binding,
            statement_payload: &payload,
        },
        host_hash as HashFn,
    )
    .map_err(|error| anyhow!("encode ASVQ: {error:?}"))?;
    if request.len() != 600 {
        bail!("native ASVQ was not 600 bytes");
    }

    let verifier_address = Address::from(VERIFIER);
    let proof_address = Address::from(PROOF_ACCOUNT);
    let mut svm = LiteSVM::new();
    svm.add_program(verifier_address, &verifier)?;
    let account_data = proof_data(&proof);
    svm.set_account(
        proof_address,
        Account {
            lamports: svm.minimum_balance_for_rent_exemption(account_data.len()),
            data: account_data,
            owner: verifier_address,
            executable: false,
            rent_epoch: 0,
        },
    )
    .map_err(|error| anyhow!("install proof account: {error}"))?;
    let payer = Keypair::new_from_array([1; 32]);
    svm.airdrop(&payer.pubkey(), 1_000_000)
        .map_err(|failed| anyhow!("fund payer: {:?}", failed.err))?;
    let tx = Transaction::new_signed_with_payer(
        &[
            ComputeBudgetInstruction::set_compute_unit_limit(CU_LIMIT),
            Instruction {
                program_id: verifier_address,
                accounts: vec![AccountMeta::new_readonly(proof_address, false)],
                data: request,
            },
        ],
        Some(&payer.pubkey()),
        &[&payer],
        svm.latest_blockhash(),
    );
    let simulation = svm
        .simulate_transaction(tx.clone())
        .expect_err("native direct verifier unexpectedly fit the strict cap");
    let execution = svm
        .send_transaction(tx)
        .expect_err("native direct verifier unexpectedly fit the strict cap");
    if simulation.err != execution.err || simulation.meta != execution.meta {
        bail!("simulation metadata differed from execution");
    }
    let evidence = json!({
        "schema": "aspis.pool-v1.native-tag73-direct-verifier-red.v1",
        "compute_unit_limit": CU_LIMIT,
        "compute_units": execution.meta.compute_units_consumed,
        "simulation_error": format!("{:?}", simulation.err),
        "execution_error": format!("{:?}", execution.err),
        "simulation_metadata_equals_execution": true,
        "return_data_bytes": execution.meta.return_data.data.len(),
        "logs": execution.meta.pretty_logs(),
        "verifier_sbf": {
            "bytes": verifier.len(),
            "sha256": sha256_hex(&verifier),
        },
        "proof": {
            "bytes": proof.len(),
            "sha256": sha256_hex(&proof),
            "account_bytes": POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES + proof.len(),
        },
        "instruction": {
            "data_bytes": 600,
            "account_metas": 1,
            "writable_metas": 0,
            "signer_metas": 0,
        },
        "no_network_send_or_deploy": true,
    });
    fs::write(&output_path, serde_json::to_vec_pretty(&evidence)?)
        .with_context(|| format!("write {}", output_path.display()))?;
    println!(
        "native Tag-73 direct verifier: RED ({} CU)",
        execution.meta.compute_units_consumed
    );
    Ok(())
}
