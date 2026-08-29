use std::{collections::BTreeMap, env, fs, path::PathBuf, str::FromStr};

use anyhow::{anyhow, ensure, Context, Result};
use aspis_core::HashFn;
use aspis_statement::{
    atomic_payment_statement_digest_v4, decode_asset_id_canonical, decode_digest_canonical,
    encode_atomic_payment_statement_v4,
    pool_v1::{
        decode_pool_v1_authorization_receipt_account_v1, decode_verifier_dispatch_request_v1,
        encode_verifier_dispatch_request_v1, finalize_pool_v1_authorization_receipt_account_v1,
        initialize_pool_v1_authorization_receipt_account_v1,
        pool_v1_authorization_receipt_binding_digest_v1,
        verifier_dispatch_binding_from_envelope_v1, verifier_proof_body_digest_v1,
        HistoricalAnchorEnvelopeV1, PoolV1AuthorizationReceiptAccountStatusV1,
        PoolV1AuthorizationReceiptV1, PoolV1TransitionKind, VerifierDispatchBindingV1,
        VerifierDispatchRequestV1, POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES,
        POOL_V1_AUTHORIZATION_RECEIPT_SEED, POOL_V1_VERIFIER_DISPATCH_BINDING_PREFIX_BYTES,
    },
    AtomicPaymentStatementV4, SpendPublic,
};
use aspis_verifier::{
    v7_pool_dispatch::{
        encode_v7_pool_tag73_profile_payload_v1, V7PoolTag73ProfilePayloadV1,
        V7_POOL_TAG73_CHECK_ALL_WORK, V7_POOL_TAG73_FRONTIER_NODES, V7_POOL_TAG73_PROFILE_BINDING,
        V7_POOL_TAG73_PROFILE_PAYLOAD_BYTES, V7_POOL_TAG73_PROOF_BODY_BYTES,
    },
    v7_pool_receipt::{
        V7_POOL_RECEIPT_CLOSE_TAG, V7_POOL_RECEIPT_FINALIZE_TAG, V7_POOL_RECEIPT_INITIALIZE_TAG,
    },
    v7_transaction::V7_RELEASE_BINDING,
    PROOF_ACCOUNT_HEADER_LEN,
};
use litesvm::{types::TransactionMetadata, LiteSVM};
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};
use solana_account::Account;
use solana_address::Address;
use solana_compute_budget_interface::ComputeBudgetInstruction;
use solana_instruction::{AccountMeta, Instruction};
use solana_instruction_error::InstructionError;
use solana_keypair::Keypair;
use solana_program::pubkey::Pubkey as LegacyPubkey;
use solana_sdk_ids::system_program;
use solana_signer::Signer;
use solana_transaction::Transaction;
use solana_transaction_error::TransactionError;

const HARNESS_VERSION: &str = "aspis-verifier-receipt-litesvm-evidence-v1";
const SOURCE_COMMIT: &str = "b484a8772680e90681cb099b57929b9700c1d4a1";
const RECEIPT_COMMIT: &str = "de997860";
const LITESVM_VERSION: &str = "0.16.0";
const AGAVE_RUNTIME_VERSION: &str = "4.2.1";
const MAX_TRANSACTION_BYTES: usize = 1_232;
const COMPUTE_UNIT_LIMIT: u32 = 1_400_000;
const FINALIZE_SLOT: u64 = 424_242;
const EXPECTED_PROOF_BYTES: usize = 30_504;
const EXPECTED_PROOF_SHA256: &str =
    "e8e15ce268447b92ac1344292bc879dcb0bf7534621ce077d8790097975dcecb";
const EXPECTED_STATEMENT_SHA256: &str =
    "7dd15bd17b8f052d540d0187caf4f1d616f4220e66a14be78b56f9c736a5a375";
const EXPECTED_METADATA_SHA256: &str =
    "fa5a49b2b029432ba1af8bb8c185650ee21f4c716fd548842c7f21f41f35e3cd";
const EXPECTED_PROGRAM_ID: &str = "7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue";
const EXPECTED_PROOF_ACCOUNT: &str = "97dyPnMkxRwsS2X8rBdosa7q35fXmMAyCMffhCuvao31";

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct AccountSnapshot {
    exists: bool,
    lamports: Option<u64>,
    owner: Option<String>,
    executable: Option<bool>,
    rent_epoch: Option<u64>,
    data_bytes: Option<usize>,
    data_sha256: Option<String>,
}

#[derive(Clone, Debug, Serialize)]
struct AccountChangeEvidence {
    label: String,
    address: String,
    before: AccountSnapshot,
    after: AccountSnapshot,
    exact_match: bool,
}

#[derive(Clone, Debug, Serialize)]
struct ProgramConsumptionEvidence {
    program_id: String,
    compute_units: u64,
    available_compute_units: u64,
}

#[derive(Clone, Debug, Serialize)]
struct ReturnEvidence {
    program_id: String,
    data_bytes: usize,
    data_sha256: String,
}

#[derive(Clone, Debug, Serialize)]
struct StepEvidence {
    name: String,
    instruction_names: Vec<String>,
    slot: u64,
    outcome: String,
    expected_error: Option<String>,
    actual_error: Option<String>,
    simulation_matches_execution: bool,
    transaction_bytes: usize,
    transaction_compute_units: u64,
    compute_unit_limit: u32,
    verifier_instruction_compute_units: Vec<u64>,
    all_program_consumption: Vec<ProgramConsumptionEvidence>,
    fee_lamports: u64,
    payer_before_lamports: u64,
    payer_after_lamports: u64,
    payer_delta_lamports: u64,
    return_data: ReturnEvidence,
    system_program_invoke_observed: bool,
    system_program_success_observed: bool,
    accounts: Vec<AccountChangeEvidence>,
    logs: Vec<String>,
}

#[derive(Debug, Serialize)]
struct FileEvidence {
    path: String,
    bytes: usize,
    sha256: String,
}

#[derive(Debug, Serialize)]
struct ArtifactEvidence {
    path: String,
    bytes: usize,
    sha256: String,
    expected_bytes: usize,
    expected_sha256: String,
    exact_match: bool,
}

#[derive(Debug, Serialize)]
struct RentEvidence {
    receipt_account_bytes: usize,
    receipt_rent_lamports: u64,
    prefunded_lamports: u64,
    prefunded_init_authority_debit: u64,
    prefunded_init_expected_deficit: u64,
    pending_close_refund: u64,
    fresh_init_authority_debit: u64,
    fresh_init_expected_rent: u64,
    verified_close_refund: u64,
}

#[derive(Debug, Serialize)]
struct Evidence {
    schema: String,
    harness_version: String,
    source_commit: String,
    receipt_commit: String,
    litesvm_version: String,
    agave_runtime_version: String,
    execution_environment: String,
    compute_unit_limit: u32,
    program_id: String,
    artifact: ArtifactEvidence,
    fixtures: Vec<FileEvidence>,
    addresses: BTreeMap<String, String>,
    request_bytes: usize,
    request_sha256: String,
    steps: Vec<StepEvidence>,
    rent: RentEvidence,
    assertions: BTreeMap<String, bool>,
    explicit_boundaries: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct StatementSidecar {
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
struct ProofMetadata {
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

struct Inputs {
    proof: Vec<u8>,
    statement: AtomicPaymentStatementV4,
    program_id: LegacyPubkey,
    proof_account: LegacyPubkey,
    files: Vec<FileEvidence>,
}

#[derive(Clone)]
struct RequestFixture {
    request: Vec<u8>,
    binding: VerifierDispatchBindingV1,
    proof_account: LegacyPubkey,
    receipt: LegacyPubkey,
    bump: u8,
}

fn host_hashv(inputs: &[&[u8]]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    for input in inputs {
        hasher.update(input);
    }
    hasher.finalize().into()
}

const HOST_HASH: HashFn = host_hashv;

fn sha256_hex(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn file_evidence(path: &PathBuf) -> Result<FileEvidence> {
    let bytes = fs::read(path).with_context(|| format!("read {}", path.display()))?;
    Ok(FileEvidence {
        path: path.display().to_string(),
        bytes: bytes.len(),
        sha256: sha256_hex(&bytes),
    })
}

fn decode_hex_32(label: &str, encoded: &str) -> Result<[u8; 32]> {
    ensure!(
        encoded.len() == 64
            && encoded
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
        "{label} is not canonical lowercase 32-byte hex"
    );
    let mut output = [0u8; 32];
    for (index, byte) in output.iter_mut().enumerate() {
        let nibble = |value: u8| match value {
            b'0'..=b'9' => value.checked_sub(b'0').expect("digit lower bound matched"),
            b'a'..=b'f' => value
                .checked_sub(b'a')
                .and_then(|offset| offset.checked_add(10))
                .expect("lowercase hex bounds matched"),
            _ => unreachable!("canonical lowercase hex validated above"),
        };
        let encoded = encoded.as_bytes();
        *byte = (nibble(encoded[2 * index]) << 4) | nibble(encoded[2 * index + 1]);
    }
    Ok(output)
}

fn load_inputs(
    proof_path: PathBuf,
    statement_path: PathBuf,
    metadata_path: PathBuf,
) -> Result<Inputs> {
    let proof =
        fs::read(&proof_path).with_context(|| format!("read proof {}", proof_path.display()))?;
    let statement_bytes = fs::read(&statement_path)
        .with_context(|| format!("read statement {}", statement_path.display()))?;
    let metadata_bytes = fs::read(&metadata_path)
        .with_context(|| format!("read metadata {}", metadata_path.display()))?;
    ensure!(proof.len() == EXPECTED_PROOF_BYTES);
    ensure!(sha256_hex(&proof) == EXPECTED_PROOF_SHA256);
    ensure!(sha256_hex(&statement_bytes) == EXPECTED_STATEMENT_SHA256);
    ensure!(sha256_hex(&metadata_bytes) == EXPECTED_METADATA_SHA256);

    let sidecar: StatementSidecar = serde_json::from_slice(&statement_bytes)?;
    let metadata: ProofMetadata = serde_json::from_slice(&metadata_bytes)?;
    ensure!(sidecar.artifact == "aspis_v7_compact_onefold_statement");
    ensure!(sidecar.profile == "V7-26C1-3C2-B10-q16-onefold-digest208-f203-fullC2");
    ensure!(sidecar.program_id == EXPECTED_PROGRAM_ID);
    ensure!(sidecar.proof_account == EXPECTED_PROOF_ACCOUNT);
    ensure!(sidecar.network_tag == "devnet");
    ensure!(sidecar.release_binding_hex == hex(&V7_RELEASE_BINDING));
    ensure!(metadata.artifact == "aspis_v7_compact_onefold_honest_mined_proof");
    ensure!(metadata.proof_sha256 == EXPECTED_PROOF_SHA256);
    ensure!(metadata.statement_sha256 == EXPECTED_STATEMENT_SHA256);
    ensure!(metadata.program_id == sidecar.program_id);
    ensure!(metadata.pool == sidecar.pool);
    ensure!(metadata.proof_account == sidecar.proof_account);
    ensure!(metadata.release_binding_hex == sidecar.release_binding_hex);
    ensure!(metadata.all_work_checked && metadata.host_full_acceptance);
    ensure!(metadata.compact_counter < 64);
    ensure!(metadata.frontier_digest_bytes == 26);
    ensure!(metadata.frontier_nodes_per_tree == usize::from(V7_POOL_TAG73_FRONTIER_NODES));

    let program_id = LegacyPubkey::from_str(&sidecar.program_id)?;
    let proof_account = LegacyPubkey::from_str(&sidecar.proof_account)?;
    ensure!(program_id == aspis_verifier::id());
    let decode_digest = |label: &str, encoded: &str| {
        decode_digest_canonical(&decode_hex_32(label, encoded)?)
            .map_err(|error| anyhow!("decode {label}: {error:?}"))
    };
    let statement = AtomicPaymentStatementV4 {
        pool: LegacyPubkey::from_str(&sidecar.pool)?.to_bytes(),
        sequence: sidecar.sequence,
        spend: SpendPublic {
            anchor: decode_digest("current_anchor_hex", &sidecar.current_anchor_hex)?,
            nullifier: decode_digest("nullifier_hex", &sidecar.nullifier_hex)?,
            output_commitment: decode_digest(
                "output_commitment_hex",
                &sidecar.output_commitment_hex,
            )?,
            asset_id: decode_asset_id_canonical(sidecar.asset_id)
                .map_err(|error| anyhow!("decode asset id: {error:?}"))?,
            fee: sidecar.fee,
        },
        output_anchor: decode_digest("output_anchor_hex", &sidecar.output_anchor_hex)?,
        deployment_domain: decode_hex_32("deployment_domain_hex", &sidecar.deployment_domain_hex)?,
    };
    encode_atomic_payment_statement_v4(&statement)
        .map_err(|error| anyhow!("noncanonical statement: {error:?}"))?;

    Ok(Inputs {
        proof,
        statement,
        program_id,
        proof_account,
        files: vec![
            file_evidence(&proof_path)?,
            file_evidence(&statement_path)?,
            file_evidence(&metadata_path)?,
        ],
    })
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn address(key: &LegacyPubkey) -> Address {
    Address::from(key.to_bytes())
}

fn account_meta(key: Address, signer: bool, writable: bool) -> AccountMeta {
    if writable {
        AccountMeta::new(key, signer)
    } else {
        AccountMeta::new_readonly(key, signer)
    }
}

fn build_request(
    program_id: LegacyPubkey,
    proof_account: LegacyPubkey,
    statement: &AtomicPaymentStatementV4,
    proof: &[u8],
) -> Result<RequestFixture> {
    let proof_body_digest = verifier_proof_body_digest_v1(proof, HOST_HASH);
    let statement_digest = atomic_payment_statement_digest_v4(statement, HOST_HASH)
        .map_err(|error| anyhow!("statement digest: {error:?}"))?;
    let profile = V7PoolTag73ProfilePayloadV1 {
        frontier_nodes: V7_POOL_TAG73_FRONTIER_NODES,
        proof_body_length: V7_POOL_TAG73_PROOF_BODY_BYTES,
        proof_body_digest,
        verifier_program: program_id.to_bytes(),
        release_binding: V7_RELEASE_BINDING,
        attempt_id: proof_account.to_bytes(),
        statement_digest,
        statement: statement.clone(),
        check_pow: V7_POOL_TAG73_CHECK_ALL_WORK == 1,
    };
    let payload = encode_v7_pool_tag73_profile_payload_v1(&profile, HOST_HASH)
        .map_err(|error| anyhow!("encode Tag-73 profile: {error:?}"))?;
    let envelope = HistoricalAnchorEnvelopeV1 {
        transition_kind: PoolV1TransitionKind::PrivateTransfer,
        pool: statement.pool,
        deployment_domain: statement.deployment_domain,
        anchor_sequence: statement.sequence,
        anchor_root: statement.spend.anchor,
        nullifier: statement.spend.nullifier,
        verifier_profile: V7_POOL_TAG73_PROFILE_BINDING,
        verifier_release: V7_RELEASE_BINDING,
    };
    let binding = verifier_dispatch_binding_from_envelope_v1(
        program_id.to_bytes(),
        &envelope,
        &payload,
        proof_account.to_bytes(),
        proof_body_digest,
        V7_POOL_TAG73_PROOF_BODY_BYTES,
        HOST_HASH,
    )
    .map_err(|error| anyhow!("derive ASVQ binding: {error:?}"))?;
    let request = encode_verifier_dispatch_request_v1(
        &VerifierDispatchRequestV1 {
            binding,
            statement_payload: &payload,
        },
        HOST_HASH,
    )
    .map_err(|error| anyhow!("encode ASVQ: {error:?}"))?;
    ensure!(
        request.len()
            == POOL_V1_VERIFIER_DISPATCH_BINDING_PREFIX_BYTES + V7_POOL_TAG73_PROFILE_PAYLOAD_BYTES
    );
    let binding_digest = pool_v1_authorization_receipt_binding_digest_v1(&binding, HOST_HASH)
        .map_err(|error| anyhow!("receipt binding digest: {error:?}"))?;
    let (receipt, bump) = LegacyPubkey::find_program_address(
        &[
            POOL_V1_AUTHORIZATION_RECEIPT_SEED,
            proof_account.as_ref(),
            &binding.statement_digest,
            &binding_digest,
        ],
        &program_id,
    );
    Ok(RequestFixture {
        request,
        binding,
        proof_account,
        receipt,
        bump,
    })
}

fn unsealed_proof_data(proof: &[u8], authority: Address) -> Result<Vec<u8>> {
    ensure!(proof.len() == EXPECTED_PROOF_BYTES);
    let mut data = vec![0u8; PROOF_ACCOUNT_HEADER_LEN + proof.len()];
    data[..4].copy_from_slice(b"ASPU");
    data[4..8].copy_from_slice(&(proof.len() as u32).to_le_bytes());
    data[8..40].copy_from_slice(authority.as_ref());
    data[PROOF_ACCOUNT_HEADER_LEN..].copy_from_slice(proof);
    Ok(data)
}

fn expected_pending_image(
    fixture: &RequestFixture,
    authority: Address,
) -> Result<[u8; POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES]> {
    let request = decode_verifier_dispatch_request_v1(&fixture.request, HOST_HASH)
        .map_err(|error| anyhow!("decode expected pending request: {error:?}"))?;
    initialize_pool_v1_authorization_receipt_account_v1(
        &request,
        fixture.proof_account.to_bytes(),
        authority.to_bytes(),
        Some(authority.to_bytes()),
        authority.to_bytes(),
        fixture.bump,
        HOST_HASH,
    )
    .map_err(|error| anyhow!("construct exact pending image: {error:?}"))
}

fn expected_finalized_image(
    fixture: &RequestFixture,
    pending: &[u8],
    verified_slot: u64,
) -> Result<[u8; POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES]> {
    let request = decode_verifier_dispatch_request_v1(&fixture.request, HOST_HASH)
        .map_err(|error| anyhow!("decode expected finalized request: {error:?}"))?;
    finalize_pool_v1_authorization_receipt_account_v1(
        pending,
        &request,
        &PoolV1AuthorizationReceiptV1 {
            pda_bump: fixture.bump,
            verified_slot,
            binding: fixture.binding,
        },
        HOST_HASH,
    )
    .map_err(|error| anyhow!("construct exact finalized image: {error:?}"))
}

fn put_account(
    svm: &mut LiteSVM,
    key: Address,
    owner: Address,
    data: Vec<u8>,
    lamports: u64,
) -> Result<()> {
    svm.set_account(
        key,
        Account {
            lamports,
            data,
            owner,
            executable: false,
            rent_epoch: 0,
        },
    )
    .map_err(|error| anyhow!("set account {key}: {error}"))
}

fn put_proof_account(
    svm: &mut LiteSVM,
    program_id: LegacyPubkey,
    proof_account: LegacyPubkey,
    proof: &[u8],
    authority: Address,
) -> Result<()> {
    let data = unsealed_proof_data(proof, authority)?;
    let lamports = svm.minimum_balance_for_rent_exemption(data.len()).max(1);
    put_account(
        svm,
        address(&proof_account),
        address(&program_id),
        data,
        lamports,
    )
}

fn verifier_instruction(
    program_id: LegacyPubkey,
    accounts: Vec<AccountMeta>,
    data: Vec<u8>,
) -> Instruction {
    Instruction {
        program_id: address(&program_id),
        accounts,
        data,
    }
}

fn initialize_instruction(
    fixture: &RequestFixture,
    program_id: LegacyPubkey,
    authority: Address,
    receipt_override: Option<Address>,
) -> Instruction {
    let mut data = Vec::with_capacity(1 + fixture.request.len());
    data.push(V7_POOL_RECEIPT_INITIALIZE_TAG);
    data.extend_from_slice(&fixture.request);
    verifier_instruction(
        program_id,
        vec![
            account_meta(address(&fixture.proof_account), false, false),
            account_meta(
                receipt_override.unwrap_or_else(|| address(&fixture.receipt)),
                false,
                true,
            ),
            account_meta(authority, true, true),
            account_meta(system_program::id(), false, false),
        ],
        data,
    )
}

fn proof_finalize_instruction(
    program_id: LegacyPubkey,
    proof_account: LegacyPubkey,
    authority: Address,
) -> Instruction {
    verifier_instruction(
        program_id,
        vec![
            account_meta(address(&proof_account), false, true),
            account_meta(authority, true, false),
        ],
        vec![62],
    )
}

fn receipt_finalize_instruction(
    fixture: &RequestFixture,
    program_id: LegacyPubkey,
    request_override: Option<&[u8]>,
) -> Instruction {
    let request = request_override.unwrap_or(&fixture.request);
    let mut data = Vec::with_capacity(1 + request.len());
    data.push(V7_POOL_RECEIPT_FINALIZE_TAG);
    data.extend_from_slice(request);
    verifier_instruction(
        program_id,
        vec![
            account_meta(address(&fixture.proof_account), false, false),
            account_meta(address(&fixture.receipt), false, true),
        ],
        data,
    )
}

fn close_instruction(
    fixture: &RequestFixture,
    program_id: LegacyPubkey,
    refund_authority: Address,
) -> Instruction {
    verifier_instruction(
        program_id,
        vec![
            account_meta(address(&fixture.receipt), false, true),
            account_meta(refund_authority, true, true),
        ],
        vec![V7_POOL_RECEIPT_CLOSE_TAG],
    )
}

fn transaction(
    svm: &mut LiteSVM,
    instructions: &[Instruction],
    payer: &Keypair,
    extra_signers: &[&Keypair],
) -> Transaction {
    svm.expire_blockhash();
    let mut signers = vec![payer];
    for signer in extra_signers {
        if signer.pubkey() != payer.pubkey() {
            signers.push(*signer);
        }
    }
    let mut budgeted = Vec::with_capacity(1 + instructions.len());
    budgeted.push(ComputeBudgetInstruction::set_compute_unit_limit(
        COMPUTE_UNIT_LIMIT,
    ));
    budgeted.extend_from_slice(instructions);
    Transaction::new_signed_with_payer(
        &budgeted,
        Some(&payer.pubkey()),
        &signers,
        svm.latest_blockhash(),
    )
}

fn snapshot(svm: &LiteSVM, key: &Address) -> AccountSnapshot {
    match svm.get_account(key) {
        None => AccountSnapshot {
            exists: false,
            lamports: None,
            owner: None,
            executable: None,
            rent_epoch: None,
            data_bytes: None,
            data_sha256: None,
        },
        Some(account) => AccountSnapshot {
            exists: true,
            lamports: Some(account.lamports),
            owner: Some(account.owner.to_string()),
            executable: Some(account.executable),
            rent_epoch: Some(account.rent_epoch),
            data_bytes: Some(account.data.len()),
            data_sha256: Some(sha256_hex(&account.data)),
        },
    }
}

fn capture_accounts(
    svm: &LiteSVM,
    tracked: &[(&str, Address)],
) -> Vec<(String, Address, AccountSnapshot)> {
    tracked
        .iter()
        .map(|(label, key)| ((*label).to_string(), *key, snapshot(svm, key)))
        .collect()
}

fn account_changes(
    svm: &LiteSVM,
    before: Vec<(String, Address, AccountSnapshot)>,
) -> Vec<AccountChangeEvidence> {
    before
        .into_iter()
        .map(|(label, key, before)| {
            let after = snapshot(svm, &key);
            AccountChangeEvidence {
                label,
                address: key.to_string(),
                exact_match: before == after,
                before,
                after,
            }
        })
        .collect()
}

fn parse_program_consumption(logs: &[String]) -> Vec<ProgramConsumptionEvidence> {
    logs.iter()
        .filter_map(|line| {
            let words = line.split_whitespace().collect::<Vec<_>>();
            if words.len() == 8
                && words[0] == "Program"
                && words[2] == "consumed"
                && words[4] == "of"
                && words[6] == "compute"
                && words[7] == "units"
            {
                Some(ProgramConsumptionEvidence {
                    program_id: words[1].to_string(),
                    compute_units: words[3].parse().ok()?,
                    available_compute_units: words[5].parse().ok()?,
                })
            } else {
                None
            }
        })
        .collect()
}

fn system_program_flags(logs: &[String]) -> (bool, bool) {
    let prefix = format!("Program {}", system_program::id());
    (
        logs.iter()
            .any(|line| line.starts_with(&prefix) && line.contains(" invoke [")),
        logs.iter().any(|line| line == &format!("{prefix} success")),
    )
}

fn return_evidence(metadata: &TransactionMetadata) -> ReturnEvidence {
    ReturnEvidence {
        program_id: metadata.return_data.program_id.to_string(),
        data_bytes: metadata.return_data.data.len(),
        data_sha256: sha256_hex(&metadata.return_data.data),
    }
}

#[allow(clippy::too_many_arguments)]
fn success_step(
    svm: &mut LiteSVM,
    payer: &Keypair,
    program_id: LegacyPubkey,
    name: &str,
    instruction_names: &[&str],
    transaction: Transaction,
    tracked: &[(&str, Address)],
) -> Result<StepEvidence> {
    let before = capture_accounts(svm, tracked);
    let transaction_bytes = wincode::serialized_size(&transaction)? as usize;
    ensure!(
        transaction_bytes <= MAX_TRANSACTION_BYTES,
        "{name}: transaction is {transaction_bytes} bytes"
    );
    let payer_before = svm
        .get_balance(&payer.pubkey())
        .ok_or_else(|| anyhow!("{name}: missing payer"))?;
    let simulation = svm
        .simulate_transaction(transaction.clone())
        .map_err(|failed| {
            anyhow!(
                "{name} simulation failed: {:?}\n{}",
                failed.err,
                failed.meta.pretty_logs()
            )
        })?;
    let executed = svm.send_transaction(transaction).map_err(|failed| {
        anyhow!(
            "{name} execution failed: {:?}\n{}",
            failed.err,
            failed.meta.pretty_logs()
        )
    })?;
    ensure!(
        simulation.meta == executed,
        "{name}: simulation/execution drift"
    );
    ensure!(
        executed.compute_units_consumed < u64::from(COMPUTE_UNIT_LIMIT),
        "{name}: compute cap reached"
    );
    ensure!(
        executed.return_data.data.is_empty(),
        "{name}: unexpected return data"
    );
    let payer_after = svm
        .get_balance(&payer.pubkey())
        .ok_or_else(|| anyhow!("{name}: missing payer after"))?;
    let payer_delta = payer_before
        .checked_sub(payer_after)
        .ok_or_else(|| anyhow!("{name}: payer unexpectedly increased"))?;
    ensure!(
        payer_delta == executed.fee,
        "{name}: payer delta != exact fee"
    );
    let consumption = parse_program_consumption(&executed.logs);
    let verifier_compute = consumption
        .iter()
        .filter(|entry| entry.program_id == program_id.to_string())
        .map(|entry| entry.compute_units)
        .collect::<Vec<_>>();
    ensure!(
        verifier_compute.len() == instruction_names.len(),
        "{name}: missing exact per-instruction verifier CU logs: {verifier_compute:?}"
    );
    let (system_invoke, system_success) = system_program_flags(&executed.logs);
    Ok(StepEvidence {
        name: name.to_string(),
        instruction_names: instruction_names
            .iter()
            .map(|value| (*value).to_string())
            .collect(),
        slot: FINALIZE_SLOT,
        outcome: "success".to_string(),
        expected_error: None,
        actual_error: None,
        simulation_matches_execution: true,
        transaction_bytes,
        transaction_compute_units: executed.compute_units_consumed,
        compute_unit_limit: COMPUTE_UNIT_LIMIT,
        verifier_instruction_compute_units: verifier_compute,
        all_program_consumption: consumption,
        fee_lamports: executed.fee,
        payer_before_lamports: payer_before,
        payer_after_lamports: payer_after,
        payer_delta_lamports: payer_delta,
        return_data: return_evidence(&executed),
        system_program_invoke_observed: system_invoke,
        system_program_success_observed: system_success,
        accounts: account_changes(svm, before),
        logs: executed.logs,
    })
}

#[allow(clippy::too_many_arguments)]
fn failure_step(
    svm: &mut LiteSVM,
    payer: &Keypair,
    program_id: LegacyPubkey,
    name: &str,
    instruction_names: &[&str],
    transaction: Transaction,
    expected_error: TransactionError,
    tracked: &[(&str, Address)],
    require_system_success: bool,
) -> Result<StepEvidence> {
    let before = capture_accounts(svm, tracked);
    let transaction_bytes = wincode::serialized_size(&transaction)? as usize;
    ensure!(
        transaction_bytes <= MAX_TRANSACTION_BYTES,
        "{name}: transaction is {transaction_bytes} bytes"
    );
    let payer_before = svm
        .get_balance(&payer.pubkey())
        .ok_or_else(|| anyhow!("{name}: missing payer"))?;
    let simulation = svm
        .simulate_transaction(transaction.clone())
        .expect_err("negative simulation must reject");
    let executed = svm
        .send_transaction(transaction)
        .expect_err("negative execution must reject");
    ensure!(
        simulation.err == executed.err,
        "{name}: simulation error drift"
    );
    ensure!(
        simulation.meta == executed.meta,
        "{name}: failed metadata drift"
    );
    ensure!(
        executed.err == expected_error,
        "{name}: wrong error {:?}",
        executed.err
    );
    ensure!(
        executed.meta.compute_units_consumed < u64::from(COMPUTE_UNIT_LIMIT),
        "{name}: rejected transaction reached compute cap"
    );
    ensure!(
        executed.meta.return_data.data.is_empty(),
        "{name}: rejected transaction retained return data"
    );
    let payer_after = svm
        .get_balance(&payer.pubkey())
        .ok_or_else(|| anyhow!("{name}: missing payer after"))?;
    let payer_delta = payer_before
        .checked_sub(payer_after)
        .ok_or_else(|| anyhow!("{name}: payer unexpectedly increased"))?;
    ensure!(
        payer_delta == executed.meta.fee,
        "{name}: rejected payer delta != fee"
    );
    let accounts = account_changes(svm, before);
    ensure!(
        accounts.iter().all(|account| account.exact_match),
        "{name}: rejected transaction mutated a tracked account"
    );
    let consumption = parse_program_consumption(&executed.meta.logs);
    let verifier_compute = consumption
        .iter()
        .filter(|entry| entry.program_id == program_id.to_string())
        .map(|entry| entry.compute_units)
        .collect::<Vec<_>>();
    ensure!(
        verifier_compute.len() == instruction_names.len(),
        "{name}: missing exact rejected-instruction CU logs: {verifier_compute:?}"
    );
    let (system_invoke, system_success) = system_program_flags(&executed.meta.logs);
    if require_system_success {
        ensure!(
            system_invoke && system_success,
            "{name}: no successful System CPI before rollback"
        );
    }
    Ok(StepEvidence {
        name: name.to_string(),
        instruction_names: instruction_names
            .iter()
            .map(|value| (*value).to_string())
            .collect(),
        slot: FINALIZE_SLOT,
        outcome: "rejected".to_string(),
        expected_error: Some(format!("{expected_error:?}")),
        actual_error: Some(format!("{:?}", executed.err)),
        simulation_matches_execution: true,
        transaction_bytes,
        transaction_compute_units: executed.meta.compute_units_consumed,
        compute_unit_limit: COMPUTE_UNIT_LIMIT,
        verifier_instruction_compute_units: verifier_compute,
        all_program_consumption: consumption,
        fee_lamports: executed.meta.fee,
        payer_before_lamports: payer_before,
        payer_after_lamports: payer_after,
        payer_delta_lamports: payer_delta,
        return_data: return_evidence(&executed.meta),
        system_program_invoke_observed: system_invoke,
        system_program_success_observed: system_success,
        accounts,
        logs: executed.meta.logs,
    })
}

fn instruction_error(index: u8, error: InstructionError) -> TransactionError {
    TransactionError::InstructionError(index, error)
}

fn account_lamports(svm: &LiteSVM, key: &Address) -> Result<u64> {
    svm.get_account(key)
        .map(|account| account.lamports)
        .ok_or_else(|| anyhow!("missing account {key}"))
}

fn parse_args() -> Result<(PathBuf, PathBuf, PathBuf, PathBuf, String, usize, PathBuf)> {
    let args = env::args().skip(1).collect::<Vec<_>>();
    ensure!(
        args.len() == 7,
        "usage: harness <sbf> <proof> <statement> <metadata> <expected-sbf-sha256> <expected-sbf-bytes> <evidence.json>"
    );
    let expected_bytes = args[5]
        .parse::<usize>()
        .context("invalid expected SBF bytes")?;
    Ok((
        PathBuf::from(&args[0]),
        PathBuf::from(&args[1]),
        PathBuf::from(&args[2]),
        PathBuf::from(&args[3]),
        args[4].clone(),
        expected_bytes,
        PathBuf::from(&args[6]),
    ))
}

fn main() -> Result<()> {
    let (
        artifact_path,
        proof_path,
        statement_path,
        metadata_path,
        expected_artifact_sha,
        expected_artifact_bytes,
        output_path,
    ) = parse_args()?;
    ensure!(
        !output_path.exists(),
        "refusing to overwrite {}",
        output_path.display()
    );
    ensure!(
        expected_artifact_sha.len() == 64
            && expected_artifact_sha
                .bytes()
                .all(|byte| { byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte) }),
        "expected artifact SHA is not canonical lowercase hex"
    );
    let artifact_bytes = fs::read(&artifact_path)
        .with_context(|| format!("read artifact {}", artifact_path.display()))?;
    let artifact_sha = sha256_hex(&artifact_bytes);
    ensure!(artifact_bytes.len() == expected_artifact_bytes);
    ensure!(artifact_sha == expected_artifact_sha);
    let inputs = load_inputs(proof_path, statement_path, metadata_path)?;
    let main_request = build_request(
        inputs.program_id,
        inputs.proof_account,
        &inputs.statement,
        &inputs.proof,
    )?;
    let prefunded_request = build_request(
        inputs.program_id,
        LegacyPubkey::new_from_array([0x41; 32]),
        &inputs.statement,
        &inputs.proof,
    )?;
    let rollback_request = build_request(
        inputs.program_id,
        LegacyPubkey::new_from_array([0x42; 32]),
        &inputs.statement,
        &inputs.proof,
    )?;

    let mut svm = LiteSVM::new();
    svm.add_program(address(&inputs.program_id), &artifact_bytes)?;
    svm.warp_to_slot(FINALIZE_SLOT);
    let payer = Keypair::new_from_array([1u8; 32]);
    let upload_authority = Keypair::new_from_array([2u8; 32]);
    let wrong_authority = Keypair::new_from_array([3u8; 32]);
    svm.airdrop(&payer.pubkey(), 10_000_000_000)
        .map_err(|failed| anyhow!("fund payer: {:?}", failed.err))?;
    svm.airdrop(&upload_authority.pubkey(), 100_000_000)
        .map_err(|failed| anyhow!("fund upload authority: {:?}", failed.err))?;
    svm.airdrop(&wrong_authority.pubkey(), 1_000_000)
        .map_err(|failed| anyhow!("fund wrong authority: {:?}", failed.err))?;
    for fixture in [&main_request, &prefunded_request, &rollback_request] {
        put_proof_account(
            &mut svm,
            inputs.program_id,
            fixture.proof_account,
            &inputs.proof,
            upload_authority.pubkey(),
        )?;
    }

    let receipt_rent =
        svm.minimum_balance_for_rent_exemption(POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES);
    let prefunded_lamports = (receipt_rent / 3).max(1);
    let prefunded_expected_deficit = receipt_rent
        .checked_sub(prefunded_lamports)
        .context("prefunded lamports exceed receipt rent")?;
    put_account(
        &mut svm,
        address(&prefunded_request.receipt),
        system_program::id(),
        Vec::new(),
        prefunded_lamports,
    )?;
    let wrong_receipt = Address::from([0xee; 32]);
    put_account(
        &mut svm,
        wrong_receipt,
        system_program::id(),
        Vec::new(),
        17_777,
    )?;

    let mut steps = Vec::new();

    let wrong_prefunded_tx = transaction(
        &mut svm,
        &[initialize_instruction(
            &prefunded_request,
            inputs.program_id,
            wrong_authority.pubkey(),
            None,
        )],
        &payer,
        &[&wrong_authority],
    );
    steps.push(failure_step(
        &mut svm,
        &payer,
        inputs.program_id,
        "prefunded_pda_wrong_authority_cannot_squat",
        &["tag74_initialize_prefunded_wrong_authority"],
        wrong_prefunded_tx,
        instruction_error(1, InstructionError::InvalidAccountData),
        &[
            ("proof", address(&prefunded_request.proof_account)),
            ("prefunded_receipt", address(&prefunded_request.receipt)),
            ("upload_authority", upload_authority.pubkey()),
            ("wrong_authority", wrong_authority.pubkey()),
        ],
        false,
    )?);

    let prefunded_authority_before = account_lamports(&svm, &upload_authority.pubkey())?;
    let prefunded_init_tx = transaction(
        &mut svm,
        &[initialize_instruction(
            &prefunded_request,
            inputs.program_id,
            upload_authority.pubkey(),
            None,
        )],
        &payer,
        &[&upload_authority],
    );
    steps.push(success_step(
        &mut svm,
        &payer,
        inputs.program_id,
        "prefunded_pda_exact_authority_initializes",
        &["tag74_initialize_prefunded"],
        prefunded_init_tx,
        &[
            ("proof", address(&prefunded_request.proof_account)),
            ("prefunded_receipt", address(&prefunded_request.receipt)),
            ("upload_authority", upload_authority.pubkey()),
        ],
    )?);
    let prefunded_authority_after = account_lamports(&svm, &upload_authority.pubkey())?;
    let prefunded_init_debit = prefunded_authority_before
        .checked_sub(prefunded_authority_after)
        .context("prefunded init unexpectedly increased authority balance")?;
    ensure!(prefunded_init_debit == prefunded_expected_deficit);
    let prefunded_account = svm
        .get_account(&address(&prefunded_request.receipt))
        .context("prefunded receipt missing after init")?;
    ensure!(prefunded_account.owner == address(&inputs.program_id));
    ensure!(prefunded_account.data.len() == POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES);
    ensure!(prefunded_account.lamports == receipt_rent);
    ensure!(
        prefunded_account.data
            == expected_pending_image(&prefunded_request, upload_authority.pubkey())?
    );
    let prefunded_decoded =
        decode_pool_v1_authorization_receipt_account_v1(&prefunded_account.data, HOST_HASH)
            .map_err(|error| anyhow!("decode prefunded pending receipt: {error:?}"))?;
    ensure!(prefunded_decoded.status == PoolV1AuthorizationReceiptAccountStatusV1::Pending);
    ensure!(prefunded_decoded.pda_bump == prefunded_request.bump);
    ensure!(
        prefunded_decoded.binding_digest
            == pool_v1_authorization_receipt_binding_digest_v1(
                &prefunded_request.binding,
                HOST_HASH
            )
            .map_err(|error| anyhow!("prefunded binding digest: {error:?}"))?
    );
    ensure!(prefunded_decoded.proof_upload_authority == upload_authority.pubkey().to_bytes());
    ensure!(prefunded_decoded.close_refund_authority == upload_authority.pubkey().to_bytes());

    let pending_close_before = account_lamports(&svm, &upload_authority.pubkey())?;
    let pending_close_tx = transaction(
        &mut svm,
        &[close_instruction(
            &prefunded_request,
            inputs.program_id,
            upload_authority.pubkey(),
        )],
        &payer,
        &[&upload_authority],
    );
    steps.push(success_step(
        &mut svm,
        &payer,
        inputs.program_id,
        "close_prefunded_pending_receipt_refunds_embedded_authority",
        &["tag76_close_pending"],
        pending_close_tx,
        &[
            ("prefunded_receipt", address(&prefunded_request.receipt)),
            ("upload_authority", upload_authority.pubkey()),
        ],
    )?);
    let pending_close_after = account_lamports(&svm, &upload_authority.pubkey())?;
    let pending_close_refund = pending_close_after
        .checked_sub(pending_close_before)
        .context("pending close unexpectedly decreased authority balance")?;
    ensure!(pending_close_refund == receipt_rent);
    ensure!(!snapshot(&svm, &address(&prefunded_request.receipt)).exists);

    let wrong_pda_tx = transaction(
        &mut svm,
        &[initialize_instruction(
            &main_request,
            inputs.program_id,
            upload_authority.pubkey(),
            Some(wrong_receipt),
        )],
        &payer,
        &[&upload_authority],
    );
    steps.push(failure_step(
        &mut svm,
        &payer,
        inputs.program_id,
        "wrong_receipt_pda_rejected_without_mutation",
        &["tag74_initialize_wrong_pda"],
        wrong_pda_tx,
        instruction_error(1, InstructionError::InvalidSeeds),
        &[
            ("proof", address(&main_request.proof_account)),
            ("wrong_receipt", wrong_receipt),
            ("upload_authority", upload_authority.pubkey()),
        ],
        false,
    )?);

    let rollback_authority_before = account_lamports(&svm, &upload_authority.pubkey())?;
    let mut rollback_failure = close_instruction(
        &rollback_request,
        inputs.program_id,
        upload_authority.pubkey(),
    );
    rollback_failure.data.push(0);
    let rollback_tx = transaction(
        &mut svm,
        &[
            initialize_instruction(
                &rollback_request,
                inputs.program_id,
                upload_authority.pubkey(),
                None,
            ),
            rollback_failure,
        ],
        &payer,
        &[&upload_authority],
    );
    steps.push(failure_step(
        &mut svm,
        &payer,
        inputs.program_id,
        "successful_system_cpi_then_later_rejection_rolls_back",
        &["tag74_initialize_created", "tag76_trailing_byte_reject"],
        rollback_tx,
        instruction_error(2, InstructionError::InvalidInstructionData),
        &[
            ("proof", address(&rollback_request.proof_account)),
            ("receipt", address(&rollback_request.receipt)),
            ("upload_authority", upload_authority.pubkey()),
        ],
        true,
    )?);
    ensure!(account_lamports(&svm, &upload_authority.pubkey())? == rollback_authority_before);
    ensure!(!snapshot(&svm, &address(&rollback_request.receipt)).exists);

    let fresh_authority_before = account_lamports(&svm, &upload_authority.pubkey())?;
    let main_init_tx = transaction(
        &mut svm,
        &[initialize_instruction(
            &main_request,
            inputs.program_id,
            upload_authority.pubkey(),
            None,
        )],
        &payer,
        &[&upload_authority],
    );
    steps.push(success_step(
        &mut svm,
        &payer,
        inputs.program_id,
        "initialize_exact_pending_receipt",
        &["tag74_initialize_fresh"],
        main_init_tx,
        &[
            ("proof", address(&main_request.proof_account)),
            ("receipt", address(&main_request.receipt)),
            ("upload_authority", upload_authority.pubkey()),
        ],
    )?);
    let fresh_authority_after = account_lamports(&svm, &upload_authority.pubkey())?;
    let fresh_init_debit = fresh_authority_before
        .checked_sub(fresh_authority_after)
        .context("fresh init unexpectedly increased authority balance")?;
    ensure!(fresh_init_debit == receipt_rent);
    let pending_account = svm
        .get_account(&address(&main_request.receipt))
        .context("main pending receipt missing")?;
    let pending_image = pending_account.data.clone();
    ensure!(pending_image == expected_pending_image(&main_request, upload_authority.pubkey())?);
    let pending_decoded =
        decode_pool_v1_authorization_receipt_account_v1(&pending_image, HOST_HASH)
            .map_err(|error| anyhow!("decode main pending receipt: {error:?}"))?;
    ensure!(pending_decoded.status == PoolV1AuthorizationReceiptAccountStatusV1::Pending);
    ensure!(pending_decoded.proof_account == main_request.proof_account.to_bytes());
    ensure!(pending_decoded.statement_digest == main_request.binding.statement_digest);

    let early_finalize_tx = transaction(
        &mut svm,
        &[receipt_finalize_instruction(
            &main_request,
            inputs.program_id,
            None,
        )],
        &payer,
        &[],
    );
    steps.push(failure_step(
        &mut svm,
        &payer,
        inputs.program_id,
        "early_receipt_finalize_rejects_unsealed_proof",
        &["tag75_finalize_unsealed"],
        early_finalize_tx,
        instruction_error(1, InstructionError::InvalidAccountData),
        &[
            ("proof", address(&main_request.proof_account)),
            ("receipt", address(&main_request.receipt)),
        ],
        false,
    )?);

    let proof_finalize_tx = transaction(
        &mut svm,
        &[proof_finalize_instruction(
            inputs.program_id,
            main_request.proof_account,
            upload_authority.pubkey(),
        )],
        &payer,
        &[&upload_authority],
    );
    steps.push(success_step(
        &mut svm,
        &payer,
        inputs.program_id,
        "seal_exact_proof_upload",
        &["tag62_finalize_proof"],
        proof_finalize_tx,
        &[("proof", address(&main_request.proof_account))],
    )?);
    let sealed_proof = svm
        .get_account(&address(&main_request.proof_account))
        .context("sealed proof missing")?;
    ensure!(sealed_proof.data[8..40] == [0u8; 32]);
    ensure!(sha256_hex(&sealed_proof.data[PROOF_ACCOUNT_HEADER_LEN..]) == EXPECTED_PROOF_SHA256);

    let mut mutated_request = main_request.request.clone();
    let last = mutated_request.len() - 1;
    mutated_request[last] ^= 1;
    let mutated_finalize_tx = transaction(
        &mut svm,
        &[receipt_finalize_instruction(
            &main_request,
            inputs.program_id,
            Some(&mutated_request),
        )],
        &payer,
        &[],
    );
    steps.push(failure_step(
        &mut svm,
        &payer,
        inputs.program_id,
        "mutated_asvq_rejected_without_receipt_or_proof_mutation",
        &["tag75_finalize_mutated_asvq"],
        mutated_finalize_tx,
        instruction_error(1, InstructionError::InvalidInstructionData),
        &[
            ("proof", address(&main_request.proof_account)),
            ("receipt", address(&main_request.receipt)),
        ],
        false,
    )?);

    let receipt_finalize_tx = transaction(
        &mut svm,
        &[receipt_finalize_instruction(
            &main_request,
            inputs.program_id,
            None,
        )],
        &payer,
        &[],
    );
    steps.push(success_step(
        &mut svm,
        &payer,
        inputs.program_id,
        "honest_tag73_acceptance_finalizes_receipt",
        &["tag75_finalize_honest_tag73"],
        receipt_finalize_tx,
        &[
            ("proof", address(&main_request.proof_account)),
            ("receipt", address(&main_request.receipt)),
        ],
    )?);
    let finalized_account = svm
        .get_account(&address(&main_request.receipt))
        .context("finalized receipt missing")?;
    ensure!(finalized_account.lamports == receipt_rent);
    let finalized_image = finalized_account.data.clone();
    ensure!(
        finalized_image == expected_finalized_image(&main_request, &pending_image, FINALIZE_SLOT)?
    );
    let finalized = decode_pool_v1_authorization_receipt_account_v1(&finalized_image, HOST_HASH)
        .map_err(|error| anyhow!("decode finalized receipt: {error:?}"))?;
    ensure!(finalized.status == PoolV1AuthorizationReceiptAccountStatusV1::Verified);
    ensure!(finalized.verified_slot == FINALIZE_SLOT);
    let nested = finalized.receipt.context("finalized receipt body absent")?;
    ensure!(nested.binding == main_request.binding);
    ensure!(nested.pda_bump == main_request.bump);
    ensure!(nested.verified_slot == FINALIZE_SLOT);
    ensure!(pending_image != finalized_image);

    let duplicate_finalize_tx = transaction(
        &mut svm,
        &[receipt_finalize_instruction(
            &main_request,
            inputs.program_id,
            None,
        )],
        &payer,
        &[],
    );
    steps.push(failure_step(
        &mut svm,
        &payer,
        inputs.program_id,
        "receipt_finalization_is_one_way",
        &["tag75_duplicate_finalize"],
        duplicate_finalize_tx,
        instruction_error(1, InstructionError::InvalidAccountData),
        &[
            ("proof", address(&main_request.proof_account)),
            ("receipt", address(&main_request.receipt)),
        ],
        false,
    )?);

    let wrong_close_tx = transaction(
        &mut svm,
        &[close_instruction(
            &main_request,
            inputs.program_id,
            wrong_authority.pubkey(),
        )],
        &payer,
        &[&wrong_authority],
    );
    steps.push(failure_step(
        &mut svm,
        &payer,
        inputs.program_id,
        "wrong_close_authority_rejected_without_mutation",
        &["tag76_close_wrong_authority"],
        wrong_close_tx,
        instruction_error(1, InstructionError::InvalidArgument),
        &[
            ("receipt", address(&main_request.receipt)),
            ("upload_authority", upload_authority.pubkey()),
            ("wrong_authority", wrong_authority.pubkey()),
        ],
        false,
    )?);

    let verified_close_before = account_lamports(&svm, &upload_authority.pubkey())?;
    let close_tx = transaction(
        &mut svm,
        &[close_instruction(
            &main_request,
            inputs.program_id,
            upload_authority.pubkey(),
        )],
        &payer,
        &[&upload_authority],
    );
    steps.push(success_step(
        &mut svm,
        &payer,
        inputs.program_id,
        "close_verified_receipt_refunds_embedded_authority",
        &["tag76_close_verified"],
        close_tx,
        &[
            ("receipt", address(&main_request.receipt)),
            ("upload_authority", upload_authority.pubkey()),
        ],
    )?);
    let verified_close_after = account_lamports(&svm, &upload_authority.pubkey())?;
    let verified_close_refund = verified_close_after
        .checked_sub(verified_close_before)
        .context("verified close unexpectedly decreased authority balance")?;
    ensure!(verified_close_refund == receipt_rent);
    ensure!(!snapshot(&svm, &address(&main_request.receipt)).exists);

    let all_returns_empty = steps.iter().all(|step| step.return_data.data_bytes == 0);
    let all_under_cap = steps
        .iter()
        .all(|step| step.transaction_compute_units < u64::from(COMPUTE_UNIT_LIMIT));
    let all_rejections_rolled_back = steps
        .iter()
        .filter(|step| step.outcome == "rejected")
        .all(|step| step.accounts.iter().all(|account| account.exact_match));
    let exact_cu_for_every_instruction = steps
        .iter()
        .all(|step| step.instruction_names.len() == step.verifier_instruction_compute_units.len());
    ensure!(all_returns_empty && all_under_cap && all_rejections_rolled_back);
    ensure!(exact_cu_for_every_instruction);

    let mut addresses = BTreeMap::new();
    addresses.insert("program".to_string(), inputs.program_id.to_string());
    addresses.insert("payer".to_string(), payer.pubkey().to_string());
    addresses.insert(
        "upload_authority".to_string(),
        upload_authority.pubkey().to_string(),
    );
    addresses.insert(
        "wrong_authority".to_string(),
        wrong_authority.pubkey().to_string(),
    );
    addresses.insert(
        "honest_proof".to_string(),
        main_request.proof_account.to_string(),
    );
    addresses.insert(
        "honest_receipt".to_string(),
        main_request.receipt.to_string(),
    );
    addresses.insert(
        "prefunded_proof".to_string(),
        prefunded_request.proof_account.to_string(),
    );
    addresses.insert(
        "prefunded_receipt".to_string(),
        prefunded_request.receipt.to_string(),
    );
    addresses.insert(
        "rollback_proof".to_string(),
        rollback_request.proof_account.to_string(),
    );
    addresses.insert(
        "rollback_receipt".to_string(),
        rollback_request.receipt.to_string(),
    );
    addresses.insert("wrong_receipt".to_string(), wrong_receipt.to_string());

    let assertions = BTreeMap::from([
        ("artifact_exact".to_string(), true),
        ("fixture_hashes_exact".to_string(), true),
        ("complete_unsealed_aspu_preloaded".to_string(), true),
        ("prefunded_wrong_authority_rollback_exact".to_string(), true),
        (
            "prefunded_canonical_authority_initialized".to_string(),
            true,
        ),
        ("prefunded_deficit_exact".to_string(), true),
        ("wrong_pda_rollback_exact".to_string(), true),
        ("system_cpi_later_failure_rollback_exact".to_string(), true),
        ("early_finalize_rollback_exact".to_string(), true),
        ("proof_sealed_before_receipt_finalize".to_string(), true),
        ("mutated_asvq_rollback_exact".to_string(), true),
        ("honest_tag73_accepted".to_string(), true),
        ("verified_slot_exact".to_string(), true),
        ("finalization_one_way".to_string(), true),
        ("wrong_close_authority_rollback_exact".to_string(), true),
        ("pending_and_verified_close_refunds_exact".to_string(), true),
        ("all_returns_empty".to_string(), all_returns_empty),
        (
            "all_transactions_strictly_under_1_4m".to_string(),
            all_under_cap,
        ),
        (
            "all_rejections_exact_rollback".to_string(),
            all_rejections_rolled_back,
        ),
        (
            "exact_cu_for_every_instruction".to_string(),
            exact_cu_for_every_instruction,
        ),
    ]);
    let evidence = Evidence {
        schema: "aspis/verifier-receipt-runtime-litesvm/v1".to_string(),
        harness_version: HARNESS_VERSION.to_string(),
        source_commit: SOURCE_COMMIT.to_string(),
        receipt_commit: RECEIPT_COMMIT.to_string(),
        litesvm_version: LITESVM_VERSION.to_string(),
        agave_runtime_version: AGAVE_RUNTIME_VERSION.to_string(),
        execution_environment: "LiteSVM local runtime; no RPC, deployment, wallet, or transaction broadcast".to_string(),
        compute_unit_limit: COMPUTE_UNIT_LIMIT,
        program_id: inputs.program_id.to_string(),
        artifact: ArtifactEvidence {
            path: artifact_path.display().to_string(),
            bytes: artifact_bytes.len(),
            sha256: artifact_sha.clone(),
            expected_bytes: expected_artifact_bytes,
            expected_sha256: expected_artifact_sha,
            exact_match: true,
        },
        fixtures: inputs.files,
        addresses,
        request_bytes: main_request.request.len(),
        request_sha256: sha256_hex(&main_request.request),
        steps,
        rent: RentEvidence {
            receipt_account_bytes: POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES,
            receipt_rent_lamports: receipt_rent,
            prefunded_lamports,
            prefunded_init_authority_debit: prefunded_init_debit,
            prefunded_init_expected_deficit: prefunded_expected_deficit,
            pending_close_refund,
            fresh_init_authority_debit: fresh_init_debit,
            fresh_init_expected_rent: receipt_rent,
            verified_close_refund,
        },
        assertions,
        explicit_boundaries: vec![
            "The honest proof, statement, and metadata are the existing frozen devnet fixture; this harness does not generate or mine cryptography.".to_string(),
            "Complete unsealed ASPU images are installed as genesis fixtures. Tags 0/1 upload chunk transport are outside this tags-74/75/76 lifecycle run.".to_string(),
            "Tag 75 inherits the committed Tag-73 AtomicPaymentStatementV4 private-transfer profile. This is not evidence for the newer full Pool payment relation.".to_string(),
            "LiteSVM is an isolated local Agave runtime. No validator RPC, deployment, wallet, or network transaction is used.".to_string(),
        ],
    };
    let encoded = serde_json::to_vec_pretty(&evidence)?;
    fs::write(&output_path, encoded)
        .with_context(|| format!("write evidence {}", output_path.display()))?;
    println!(
        "GREEN steps={} artifact_bytes={} artifact_sha256={} max_tx_cu={}",
        evidence.steps.len(),
        evidence.artifact.bytes,
        evidence.artifact.sha256,
        evidence
            .steps
            .iter()
            .map(|step| step.transaction_compute_units)
            .max()
            .unwrap_or(0)
    );
    Ok(())
}
