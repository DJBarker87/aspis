//! Deterministic account/input bundle for the disposable V7 TxV1 lifecycle suite.
//!
//! This generator does not load a signer, contact RPC, execute SBF, or mutate a
//! cluster. It materializes only public genesis-account images, unsigned
//! transaction inputs, expected successful poststates, and fail-closed case
//! metadata for the disposable-Agave runner.

use std::{
    collections::{BTreeMap, BTreeSet},
    env, fs,
    path::{Path, PathBuf},
    str::FromStr,
};

use anyhow::{anyhow, ensure, Context, Result};
use aspis_core::field::{M31, P};
use aspis_pool::{
    pool_v1_nullifier_marker_address, pool_v1_pair_forest_checkpoint_address,
    pool_v1_pair_forest_lane_address, pool_v1_pair_forest_master_address,
    pool_v1_root_page_address, pool_v1_vault_authority_address,
    pool_v1_vault_token_account_address, POOL_V1_PAIR_EMPTY_ROOTS,
};
use aspis_registry::{pool_v1_verifier_entry_v2_address, pool_v1_verifier_registry_v2_address};
use aspis_statement::pool_v1::root_history::{
    append_root_history_page_bytes_v1, initialize_root_history_page_bytes_v1, root_history_location,
};
use aspis_statement::{
    derive_owner_key, encode_digest_canonical,
    pool_v1::{
        decode_pool_v1_pair_verified_afterstate_v1, decode_verifier_registry_entry_v2,
        decode_verifier_registry_v2, encode_pool_v1_nullifier_marker,
        encode_pool_v1_pair_forest_checkpoint_v1, encode_pool_v1_pair_forest_lane_state_v1,
        encode_pool_v1_pair_forest_master_v1, encode_pool_v1_pair_forest_terminal_request_v1,
        encode_pool_v1_pair_forest_terminal_result_v1, encode_pool_v1_pair_verified_afterstate_v1,
        pool_v1_note_commitment, pool_v1_nullifier, pool_v1_pair_forest_output_lane_v1,
        pool_v1_tree_parent, IncrementalMerkleTreeV1, PoolIdentityV1, PoolV1NullifierMarkerV1,
        PoolV1PairForestCheckpointV1, PoolV1PairForestLaneStateV1, PoolV1PairForestMasterV1,
        PoolV1PairForestTerminalPaymentV1, PoolV1PairForestTerminalRequestV1,
        PoolV1PairForestTerminalResultV1, PoolV1PairLeafWitnessV1, PoolV1PairVerifiedAfterstateV1,
        PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1, VerifierEntryStatusV1,
        VerifierPolicyV1, POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES,
        POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES, POOL_V1_PAIR_FOREST_TERMINAL_VERSION,
        POOL_V1_PAIR_TREE_DEPTH, POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
        POOL_V1_ROOT_HISTORY_CAPACITY, POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
        POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
        POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT,
        POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY,
        POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES, POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC,
        POOL_V1_VERIFIER_REGISTRY_FLAG_IMMUTABLE, V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,
        V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
    },
    poseidon2::Digest,
};
use base64::{engine::general_purpose::STANDARD as BASE64_STANDARD, Engine as _};
use serde_json::{json, Value};
use sha2::{Digest as _, Sha256};
use solana_program::{pubkey::Pubkey, rent::Rent};

const PROGRAM_SOURCE_COMMIT: &str = "7179f7c550fe0461f4251dea5268af73876da91d";
const PROGRAM_SOURCE_TREE: &str = "72d8ccd295994277bcb5f9df922c2a1483ac0443";
const POOL_SOURCE_TREE: &str = "0bebca6b10c61e1d97949da10e6b4901d5117fa0";
const VERIFIER_SOURCE_TREE: &str = "0b9627c523ac47682f3c987abd68ae2027ac5eb2";
const REGISTRY_SOURCE_TREE: &str = "50edc0c660f12c68baa6298f8f01e3422ea8b70b";
const PROFILE_SLOT: u64 = 150;

const POOL_PROGRAM_BYTES: [u8; 32] = [0x41; 32];
const VERIFIER_PROGRAM_ID: &str = "7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue";
const SIMULATION_FEE_PAYER_ID: &str = "AKnL4NNf3DGWZJS6cPknBuEGnVsV4A4m5tgebLHaRSZ9";
const REGISTRY_PROGRAM_BYTES: [u8; 32] = [0x44; 32];
const REGISTRY_AUTHORITY_BYTES: [u8; 32] = [0; 32];
const POLICY_BINDING_BYTES: [u8; 32] = [7; 32];
const DEPLOYMENT_DOMAIN_BYTES: [u8; 32] = [5; 32];
const PROOF_ACCOUNT_BYTES: [u8; 32] = [0x45; 32];
const DESTINATION_TOKEN_ACCOUNT_BYTES: [u8; 32] = [0x49; 32];
const DESTINATION_TOKEN_OWNER_BYTES: [u8; 32] = [0x4a; 32];
const LEGACY_SPL_TOKEN_PROGRAM_ID: &str = "TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA";
const BPF_LOADER_UPGRADEABLE_ID: &str = "BPFLoaderUpgradeab1e11111111111111111111111";
const WRONG_RELEASE_BINDING: [u8; 32] = [0xee; 32];
const REGISTRY_FIXTURE_ROOT: &str = "results/v7-pair-forest-registry-v2-litesvm-20260830";
const LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES: usize = 82;
const LEGACY_SPL_TOKEN_ACCOUNT_BYTES: usize = 165;
const WITHDRAWAL_AMOUNT: u64 = 250;
const VAULT_BALANCE_BEFORE: u64 = 10_000;
const DESTINATION_BALANCE_BEFORE: u64 = 17;
const DATA_ACCOUNT_LAMPORTS: u64 = 1_000_000_000;
const PAYER_LAMPORTS: u64 = 10_000_000_000;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Operation {
    Transfer,
    Withdrawal,
}

impl Operation {
    fn input_name(self) -> &'static str {
        match self {
            Self::Transfer => "private-transfer",
            Self::Withdrawal => "withdrawal",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Mutation {
    None,
    StaleLane,
    ReplayMarker,
    WrongRegistryRelease,
    StrictProofMutation,
    MalformedResult,
    MutatedResult,
    FailingWithdrawalCpi,
}

#[derive(Clone, Copy)]
struct CaseSpec {
    name: &'static str,
    operation: Operation,
    populated_pairs: u32,
    mutation: Mutation,
    fixture: &'static str,
    registry_fixture_stem: &'static str,
    failure_stage: Option<&'static str>,
}

impl CaseSpec {
    fn succeeds(self) -> bool {
        self.mutation == Mutation::None
    }

    fn history_name(self) -> &'static str {
        if self.populated_pairs == 255 {
            "rollover"
        } else {
            "same-page"
        }
    }

    fn uses_result_double(self) -> bool {
        matches!(
            self.mutation,
            Mutation::MalformedResult | Mutation::MutatedResult
        )
    }
}

const CASES: [CaseSpec; 11] = [
    CaseSpec {
        name: "transfer-same-page",
        operation: Operation::Transfer,
        populated_pairs: 13,
        mutation: Mutation::None,
        fixture: "results/v7-pair-forest-combined-rejection-litesvm-20260828/evidence/v7-pair-forest-transfer-strict-work-canonical-fixed.bin",
        registry_fixture_stem: "production-transfer-same-success",
        failure_stage: None,
    },
    CaseSpec {
        name: "transfer-rollover",
        operation: Operation::Transfer,
        populated_pairs: 255,
        mutation: Mutation::None,
        fixture: "results/v7-pair-forest-combined-rejection-litesvm-20260828/evidence/transfer-rollover-strict-canonical.bin",
        registry_fixture_stem: "production-transfer-rollover-success",
        failure_stage: None,
    },
    CaseSpec {
        name: "withdrawal-same-page",
        operation: Operation::Withdrawal,
        populated_pairs: 13,
        mutation: Mutation::None,
        fixture: "results/v7-pair-forest-combined-rejection-litesvm-20260828/evidence/withdrawal-same-page-counter0-strict-canonical.bin",
        registry_fixture_stem: "production-withdrawal-same-success",
        failure_stage: None,
    },
    CaseSpec {
        name: "withdrawal-rollover",
        operation: Operation::Withdrawal,
        populated_pairs: 255,
        mutation: Mutation::None,
        fixture: "results/v7-pair-forest-combined-rejection-litesvm-20260828/evidence/withdrawal-rollover-counter0-strict-canonical.bin",
        registry_fixture_stem: "production-withdrawal-rollover-success",
        failure_stage: None,
    },
    CaseSpec {
        name: "strict-proof-mutation-rejection",
        operation: Operation::Transfer,
        populated_pairs: 13,
        mutation: Mutation::StrictProofMutation,
        fixture: "results/v7-pair-forest-combined-rejection-litesvm-20260828/evidence/v7-pair-forest-transfer-strict-work-canonical-fixed.bin",
        registry_fixture_stem: "production-proof-rejection",
        failure_stage: Some("authenticated strict-work proof body changed after construction"),
    },
    CaseSpec {
        name: "wrong-registry-release-rejection",
        operation: Operation::Transfer,
        populated_pairs: 13,
        mutation: Mutation::WrongRegistryRelease,
        fixture: "results/v7-pair-forest-combined-rejection-litesvm-20260828/evidence/v7-pair-forest-transfer-strict-work-canonical-fixed.bin",
        registry_fixture_stem: "production-wrong-release",
        failure_stage: Some("request release differs from the canonical Registry V2 entry PDA"),
    },
    CaseSpec {
        name: "stale-selected-lane-rejection",
        operation: Operation::Transfer,
        populated_pairs: 13,
        mutation: Mutation::StaleLane,
        fixture: "results/v7-pair-forest-combined-rejection-litesvm-20260828/evidence/v7-pair-forest-transfer-strict-work-canonical-fixed.bin",
        registry_fixture_stem: "production-stale-lane",
        failure_stage: Some("live selected lane advanced after proof construction"),
    },
    CaseSpec {
        name: "replay-nullifier-rejection",
        operation: Operation::Transfer,
        populated_pairs: 13,
        mutation: Mutation::ReplayMarker,
        fixture: "results/v7-pair-forest-combined-rejection-litesvm-20260828/evidence/v7-pair-forest-transfer-strict-work-canonical-fixed.bin",
        registry_fixture_stem: "production-replay-nullifier",
        failure_stage: Some("canonical nullifier marker already populated"),
    },
    CaseSpec {
        name: "malformed-result-rejection",
        operation: Operation::Transfer,
        populated_pairs: 13,
        mutation: Mutation::MalformedResult,
        fixture: "results/v7-pair-forest-combined-rejection-litesvm-20260828/evidence/v7-pair-forest-transfer-strict-work-canonical-fixed.bin",
        registry_fixture_stem: "production-malformed-result",
        failure_stage: Some("selected verifier returns a truncated ASR8 result"),
    },
    CaseSpec {
        name: "mutated-result-rejection",
        operation: Operation::Transfer,
        populated_pairs: 13,
        mutation: Mutation::MutatedResult,
        fixture: "results/v7-pair-forest-combined-rejection-litesvm-20260828/evidence/v7-pair-forest-transfer-strict-work-canonical-fixed.bin",
        registry_fixture_stem: "production-mutated-result",
        failure_stage: Some("selected verifier returns a canonical ASR8 with the wrong selected-lane binding"),
    },
    CaseSpec {
        name: "failed-withdrawal-cpi-rollback",
        operation: Operation::Withdrawal,
        populated_pairs: 13,
        mutation: Mutation::FailingWithdrawalCpi,
        fixture: "results/v7-pair-forest-combined-rejection-litesvm-20260828/evidence/withdrawal-same-page-counter0-strict-canonical.bin",
        registry_fixture_stem: "production-withdrawal-cpi-failure",
        failure_stage: Some("selected verifier succeeds, deterministic token-program test double rejects CPI"),
    },
];

#[derive(Clone)]
struct FixtureAccount {
    lamports: u64,
    data: Vec<u8>,
    owner: Pubkey,
    executable: bool,
    rent_epoch: u64,
}

impl FixtureAccount {
    fn validator_json(&self) -> Value {
        json!({
            "lamports": self.lamports,
            "data": [BASE64_STANDARD.encode(&self.data), "base64"],
            "owner": self.owner.to_string(),
            "executable": self.executable,
            "rentEpoch": self.rent_epoch,
            "space": self.data.len(),
        })
    }

    fn rpc_json(&self) -> Value {
        self.validator_json()
    }
}

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31((seed + 17 * index as u32 + 1) % P))
}

fn strict_lane_digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31((seed + 17 * index as u32) % P))
}

fn deterministic_anchor_and_nullifier() -> Result<(Digest, Digest)> {
    let nullifier_key = digest(10);
    let salt = digest(100);
    let asset_id = M31(77);
    let input_commitment =
        pool_v1_note_commitment(&derive_owner_key(&nullifier_key), 1_000, asset_id, &salt);
    let mut anchor = PoolV1PairLeafWitnessV1::two_outputs(input_commitment, digest(900))
        .map_err(|error| anyhow!("construct deterministic input pair: {error:?}"))?
        .leaf_digest()
        .map_err(|error| anyhow!("hash deterministic input pair: {error:?}"))?;
    let membership_index = 0x5_4321u64;
    for level in 0..20 {
        let sibling = digest(2_000 + 20 * level as u32);
        anchor = if ((membership_index >> level) & 1) == 0 {
            pool_v1_tree_parent(&anchor, &sibling)
        } else {
            pool_v1_tree_parent(&sibling, &anchor)
        };
    }
    for (sibling, direction) in [digest(3_000), digest(3_100), digest(3_200)]
        .into_iter()
        .zip([true, false, true])
    {
        anchor = if direction {
            pool_v1_tree_parent(&sibling, &anchor)
        } else {
            pool_v1_tree_parent(&anchor, &sibling)
        };
    }
    Ok((anchor, pool_v1_nullifier(&nullifier_key, &salt)))
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest: [u8; 32] = Sha256::digest(bytes).into();
    digest.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn initialized_mint_data(supply: u64, decimals: u8) -> Vec<u8> {
    let mut data = vec![0u8; LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES];
    data[36..44].copy_from_slice(&supply.to_le_bytes());
    data[44] = decimals;
    data[45] = 1;
    data
}

fn initialized_token_data(mint: Pubkey, owner: Pubkey, amount: u64) -> Vec<u8> {
    let mut data = vec![0u8; LEGACY_SPL_TOKEN_ACCOUNT_BYTES];
    data[..32].copy_from_slice(&mint.to_bytes());
    data[32..64].copy_from_slice(&owner.to_bytes());
    data[64..72].copy_from_slice(&amount.to_le_bytes());
    data[108] = 1;
    data
}

fn write_json(path: &Path, value: &Value) -> Result<String> {
    let mut bytes = serde_json::to_vec_pretty(value)?;
    bytes.push(b'\n');
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(path, &bytes)?;
    Ok(sha256_hex(&bytes))
}

fn account_key(key: &Pubkey) -> String {
    key.to_string()
}

fn insert_account(
    accounts: &mut BTreeMap<String, FixtureAccount>,
    key: Pubkey,
    owner: Pubkey,
    data: Vec<u8>,
    lamports: u64,
) -> Result<()> {
    let previous = accounts.insert(
        account_key(&key),
        FixtureAccount {
            lamports,
            data,
            owner,
            executable: false,
            // Keep the fixture in jq's exact-integer range because the replay
            // canonically hashes RPC JSON with `jq -cS`.
            rent_epoch: 0,
        },
    );
    ensure!(previous.is_none(), "duplicate fixture account: {key}");
    Ok(())
}

fn replace_account_data(
    accounts: &mut BTreeMap<String, FixtureAccount>,
    key: Pubkey,
    data: Vec<u8>,
) -> Result<()> {
    accounts
        .get_mut(&account_key(&key))
        .with_context(|| format!("replace missing fixture account {key}"))?
        .data = data;
    Ok(())
}

fn load_payload(repo: &Path, path: &str, expected_afterstate: &[u8]) -> Result<Vec<u8>> {
    let fixture_path = repo.join(path);
    let fixture = fs::read(&fixture_path)
        .with_context(|| format!("read proof fixture {}", fixture_path.display()))?;
    let payload = if fixture.len() >= POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
        && fixture[..POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES] == expected_afterstate[..]
    {
        fixture
    } else {
        let mut payload =
            Vec::with_capacity(POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES + fixture.len());
        payload.extend_from_slice(expected_afterstate);
        payload.extend_from_slice(&fixture);
        payload
    };
    ensure!(
        payload.len() > POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
        "proof payload is too short"
    );
    ensure!(
        payload[..POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES] == expected_afterstate[..],
        "fixture afterstate differs from deterministic scenario"
    );
    decode_pool_v1_pair_verified_afterstate_v1(&payload[..POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES])
        .map_err(|error| anyhow!("decode fixture afterstate: {error:?}"))?;
    Ok(payload)
}

fn account_meta(key: Pubkey, writable: bool, signer: bool) -> Value {
    json!({
        "pubkey": key.to_string(),
        "writable": writable,
        "signer": signer,
    })
}

fn materialize_account_file(output: &Path, account: &FixtureAccount) -> Result<(String, String)> {
    let value = account.validator_json();
    let mut bytes = serde_json::to_vec_pretty(&value)?;
    bytes.push(b'\n');
    let sha = sha256_hex(&bytes);
    let relative = format!("accounts/{sha}.json");
    let path = output.join(&relative);
    if path.exists() {
        ensure!(
            fs::read(&path)? == bytes,
            "content-addressed account collision"
        );
    } else {
        fs::write(&path, bytes)?;
    }
    Ok((relative, sha))
}

struct SbfArtifact {
    source: PathBuf,
    relative: &'static str,
    bytes: Vec<u8>,
    sha256: String,
    digest: [u8; 32],
}

struct SbfArtifacts {
    pool: SbfArtifact,
    verifier: SbfArtifact,
    registry: SbfArtifact,
    result_double: SbfArtifact,
}

impl SbfArtifacts {
    fn selected_verifier(&self, spec: CaseSpec) -> &SbfArtifact {
        if spec.uses_result_double() {
            &self.result_double
        } else {
            &self.verifier
        }
    }
}

fn case_bundle(
    repo: &Path,
    output: &Path,
    artifacts: &SbfArtifacts,
    spec: CaseSpec,
    request_id: u64,
) -> Result<Value> {
    let pool_program = Pubkey::new_from_array(POOL_PROGRAM_BYTES);
    let verifier_program = Pubkey::from_str(VERIFIER_PROGRAM_ID)?;
    let registry_program = Pubkey::new_from_array(REGISTRY_PROGRAM_BYTES);
    let token_program = Pubkey::from_str(LEGACY_SPL_TOKEN_PROGRAM_ID)?;
    let mint = Pubkey::new_from_array([0x42; 32]);
    let master_key = pool_v1_pair_forest_master_address(&pool_program, &mint).0;
    let (historical_global_anchor, nullifier) = deterministic_anchor_and_nullifier()?;

    let policy = VerifierPolicyV1 {
        flags: POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY
            | POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT,
        registry_program: REGISTRY_PROGRAM_BYTES,
        registry_authority: REGISTRY_AUTHORITY_BYTES,
        policy_binding: POLICY_BINDING_BYTES,
    };
    let master = PoolV1PairForestMasterV1 {
        identity: PoolIdentityV1 {
            pool: master_key.to_bytes(),
            asset_mint: mint.to_bytes(),
            token_program: token_program.to_bytes(),
            asset_id: M31(77),
            deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
        },
        verifier_policy: policy,
        initialized_lane_mask: 0xff,
        has_checkpoint: true,
        next_checkpoint_sequence: 43,
        last_checkpoint_lane_sequences: [0; 8],
    };

    let output_lane = pool_v1_pair_forest_output_lane_v1(&nullifier)
        .map_err(|error| anyhow!("derive output lane: {error:?}"))?;
    let lane_key = pool_v1_pair_forest_lane_address(&pool_program, &master_key, output_lane)?.0;
    let mut tree = IncrementalMerkleTreeV1 {
        next_leaf_index: 0,
        root: POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH],
        frontier: core::array::from_fn(|level| POOL_V1_PAIR_EMPTY_ROOTS[level]),
    };
    let mut all_lane_roots = vec![tree.root];
    for leaf in 0..spec.populated_pairs {
        tree = tree
            .append_one_with_empty_roots(
                strict_lane_digest(20_000 + 32 * leaf),
                &POOL_V1_PAIR_EMPTY_ROOTS,
            )
            .map_err(|error| anyhow!("populate deterministic lane: {error:?}"))?
            .0;
        all_lane_roots.push(tree.root);
    }
    let lane = PoolV1PairForestLaneStateV1 {
        master: master_key.to_bytes(),
        lane_id: output_lane,
        tree,
    };

    let checkpoint_sequence = 42u64;
    let checkpoint_key =
        pool_v1_pair_forest_checkpoint_address(&pool_program, &master_key, checkpoint_sequence).0;
    let checkpoint = PoolV1PairForestCheckpointV1 {
        master: master_key.to_bytes(),
        deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
        checkpoint_sequence,
        global_root: historical_global_anchor,
        lane_sequences: [0; 8],
    };

    let asset_id = M31(77);
    let recipient = pool_v1_note_commitment(&digest(300), 600, asset_id, &digest(400));
    let change = pool_v1_note_commitment(&digest(500), 400, asset_id, &digest(600));
    let transfer_public = PoolV1PrivateTransferPublicV1 {
        pool: master_key.to_bytes(),
        deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
        anchor_sequence: checkpoint_sequence,
        anchor_root: checkpoint.global_root,
        nullifier,
        asset_id,
        recipient_commitment: recipient,
        change_commitment: change,
    };
    let withdrawal_change = pool_v1_note_commitment(&digest(700), 750, asset_id, &digest(800));
    let withdrawal_public = PoolV1WithdrawalPublicV1 {
        pool: master_key.to_bytes(),
        deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
        anchor_sequence: checkpoint_sequence,
        anchor_root: checkpoint.global_root,
        nullifier,
        asset_id,
        amount: WITHDRAWAL_AMOUNT as u32,
        destination_token_account: DESTINATION_TOKEN_ACCOUNT_BYTES,
        change_commitment: withdrawal_change,
    };
    let payment = match spec.operation {
        Operation::Transfer => PoolV1PairForestTerminalPaymentV1::PrivateTransfer(transfer_public),
        Operation::Withdrawal => PoolV1PairForestTerminalPaymentV1::Withdrawal(withdrawal_public),
    };
    let request = PoolV1PairForestTerminalRequestV1 {
        verifier_profile: V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,
        verifier_release: if spec.mutation == Mutation::WrongRegistryRelease {
            WRONG_RELEASE_BINDING
        } else {
            V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING
        },
        pool_program: pool_program.to_bytes(),
        public: payment,
    };
    let instruction_data = encode_pool_v1_pair_forest_terminal_request_v1(&request)
        .map_err(|error| anyhow!("encode ASQ8: {error:?}"))?;
    ensure!(
        instruction_data.len() == POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES,
        "ASQ8 length changed"
    );

    let output_pair = match spec.operation {
        Operation::Transfer => PoolV1PairLeafWitnessV1::two_outputs(recipient, change),
        Operation::Withdrawal => PoolV1PairLeafWitnessV1::single_output(withdrawal_change),
    }
    .map_err(|error| anyhow!("construct output pair: {error:?}"))?;
    let output_leaf = output_pair
        .leaf_digest()
        .map_err(|error| anyhow!("hash output pair: {error:?}"))?;
    let next_tree = lane
        .tree
        .append_one_with_empty_roots(output_leaf, &POOL_V1_PAIR_EMPTY_ROOTS)
        .map_err(|error| anyhow!("construct afterstate: {error:?}"))?
        .0;
    let candidate_afterstate = PoolV1PairVerifiedAfterstateV1 {
        next_pair_index: next_tree.next_leaf_index,
        next_root: next_tree.root,
        next_frontier: next_tree.frontier,
    };
    let expected_afterstate = encode_pool_v1_pair_verified_afterstate_v1(&candidate_afterstate)
        .map_err(|error| anyhow!("encode afterstate: {error:?}"))?;
    let expected_result = PoolV1PairForestTerminalResultV1 {
        transition_kind: request.public.transition_kind(),
        master_account: master_key.to_bytes(),
        selected_lane_account: lane_key.to_bytes(),
        output_lane,
        nullifier,
        verified_afterstate: candidate_afterstate,
    };
    let expected_result_bytes = encode_pool_v1_pair_forest_terminal_result_v1(&expected_result)
        .map_err(|error| anyhow!("encode expected ASR8: {error:?}"))?;
    let mut payload = if spec.uses_result_double() {
        match spec.mutation {
            Mutation::MalformedResult => {
                expected_result_bytes[..expected_result_bytes.len() - 1].to_vec()
            }
            Mutation::MutatedResult => {
                let mut wrong = expected_result;
                wrong.selected_lane_account[0] ^= 1;
                encode_pool_v1_pair_forest_terminal_result_v1(&wrong)
                    .map_err(|error| anyhow!("encode canonical wrong ASR8: {error:?}"))?
                    .to_vec()
            }
            _ => unreachable!(),
        }
    } else {
        load_payload(repo, spec.fixture, &expected_afterstate)?
    };
    if spec.mutation == Mutation::StrictProofMutation {
        let final_byte = payload
            .last_mut()
            .context("proof mutation fixture is empty")?;
        *final_byte ^= 1;
    }
    ensure!(
        payload.len() <= u32::MAX as usize,
        "proof payload too large"
    );
    let mut proof_image = vec![0u8; POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES + payload.len()];
    proof_image[..4].copy_from_slice(&POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC);
    proof_image[4..8].copy_from_slice(&(payload.len() as u32).to_le_bytes());
    proof_image[POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES..].copy_from_slice(&payload);
    let proof_key = Pubkey::new_from_array(PROOF_ACCOUNT_BYTES);

    let current_history_location = root_history_location(lane.tree.next_leaf_index);
    let next_history_location = root_history_location(lane.tree.next_leaf_index + 1);
    let rollover = current_history_location.page_number != next_history_location.page_number;
    ensure!(
        rollover == (spec.populated_pairs == 255),
        "case history classification drifted"
    );
    let page_key = pool_v1_root_page_address(
        &pool_program,
        &lane_key,
        current_history_location.page_number,
    )
    .0;
    let next_page_key = rollover.then(|| {
        pool_v1_root_page_address(&pool_program, &lane_key, next_history_location.page_number).0
    });
    let marker_key = pool_v1_nullifier_marker_address(
        &pool_program,
        &master_key,
        &encode_digest_canonical(&nullifier),
    )?
    .0;
    let registry_key = pool_v1_verifier_registry_v2_address(&registry_program, &master_key).0;
    let entry_key = pool_v1_verifier_entry_v2_address(
        &registry_program,
        &master_key,
        &V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,
        &V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
    )
    .0;
    let registry_fixture = repo
        .join(REGISTRY_FIXTURE_ROOT)
        .join(format!("{}.asr2.bin", spec.registry_fixture_stem));
    let entry_fixture = repo
        .join(REGISTRY_FIXTURE_ROOT)
        .join(format!("{}.ase2.bin", spec.registry_fixture_stem));
    let registry_image = fs::read(&registry_fixture)
        .with_context(|| format!("read Registry V2 image {}", registry_fixture.display()))?;
    let entry_image = fs::read(&entry_fixture)
        .with_context(|| format!("read Registry V2 entry {}", entry_fixture.display()))?;
    let registry = decode_verifier_registry_v2(&registry_image)
        .map_err(|error| anyhow!("decode frozen ASR2: {error:?}"))?;
    let entry = decode_verifier_registry_entry_v2(&entry_image)
        .map_err(|error| anyhow!("decode frozen ASE2: {error:?}"))?;
    let loader = Pubkey::from_str(BPF_LOADER_UPGRADEABLE_ID)?;
    let registry_programdata =
        Pubkey::find_program_address(&[registry_program.as_ref()], &loader).0;
    let verifier_programdata =
        Pubkey::find_program_address(&[verifier_program.as_ref()], &loader).0;
    let selected_verifier = artifacts.selected_verifier(spec);
    ensure!(
        registry.flags == POOL_V1_VERIFIER_REGISTRY_FLAG_IMMUTABLE
            && registry.pool == master_key.to_bytes()
            && registry.authority == REGISTRY_AUTHORITY_BYTES
            && registry.policy_binding == POLICY_BINDING_BYTES
            && registry.generation == 3
            && registry.registry_program == registry_program.to_bytes()
            && registry.loader_program == loader.to_bytes()
            && registry.programdata_address == registry_programdata.to_bytes()
            && registry.executable_hash == artifacts.registry.digest,
        "frozen ASR2 is not the exact immutable Registry V2 certificate"
    );
    ensure!(
        entry.status == VerifierEntryStatusV1::Active
            && entry.statement_version == POOL_V1_PAIR_FOREST_TERMINAL_VERSION
            && entry.pool == master_key.to_bytes()
            && entry.verifier_program == verifier_program.to_bytes()
            && entry.profile_binding == V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING
            && entry.release_binding == V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING
            && entry.loader_program == loader.to_bytes()
            && entry.programdata_address == verifier_programdata.to_bytes()
            && entry.executable_hash == selected_verifier.digest
            && entry.expected_upgrade_authority == [0u8; 32]
            && entry.activation_slot == 120
            && entry.retirement_slot == POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT
            && entry.policy_binding == POLICY_BINDING_BYTES,
        "frozen ASE2 is not the exact active verifier certificate"
    );

    let current_page_first =
        current_history_location.page_number * POOL_V1_ROOT_HISTORY_CAPACITY as u64;
    let current_roots = &all_lane_roots[current_page_first as usize..];
    ensure!(
        all_lane_roots.len() == lane.tree.next_leaf_index as usize + 1,
        "history/root sequence mismatch"
    );
    let mut history_image = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
    initialize_root_history_page_bytes_v1(
        &mut history_image,
        lane_key.to_bytes(),
        current_history_location.page_number,
        current_roots,
    )
    .map_err(|error| anyhow!("initialize history: {error:?}"))?;
    let mut successful_history = history_image.clone();
    let mut successful_next_page = None;
    if rollover {
        let mut next = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        initialize_root_history_page_bytes_v1(
            &mut next,
            lane_key.to_bytes(),
            next_history_location.page_number,
            &[candidate_afterstate.next_root],
        )
        .map_err(|error| anyhow!("initialize next history page: {error:?}"))?;
        successful_next_page = Some(next);
    } else {
        append_root_history_page_bytes_v1(
            &mut successful_history,
            candidate_afterstate.next_pair_index,
            candidate_afterstate.next_root,
        )
        .map_err(|error| anyhow!("append expected history: {error:?}"))?;
    }

    let marker_payload = PoolV1NullifierMarkerV1 {
        transition_kind: request.public.transition_kind(),
        pool: master_key.to_bytes(),
        deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
        nullifier,
        retained_anchor_sequence: checkpoint_sequence,
        retained_anchor_root: historical_global_anchor,
        verifier_profile: V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,
        verifier_release: V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
    };
    let expected_marker = encode_pool_v1_nullifier_marker(&marker_payload)
        .map_err(|error| anyhow!("encode marker: {error:?}"))?;

    let vault_authority = pool_v1_vault_authority_address(&pool_program, &master_key).0;
    let vault_key = pool_v1_vault_token_account_address(&pool_program, &master_key).0;
    let destination_key = Pubkey::new_from_array(DESTINATION_TOKEN_ACCOUNT_BYTES);
    let mut accounts = BTreeMap::new();
    insert_account(
        &mut accounts,
        master_key,
        pool_program,
        encode_pool_v1_pair_forest_master_v1(&master)
            .map_err(|error| anyhow!("encode master: {error:?}"))?
            .to_vec(),
        DATA_ACCOUNT_LAMPORTS,
    )?;
    insert_account(
        &mut accounts,
        checkpoint_key,
        pool_program,
        encode_pool_v1_pair_forest_checkpoint_v1(&checkpoint)
            .map_err(|error| anyhow!("encode checkpoint: {error:?}"))?
            .to_vec(),
        DATA_ACCOUNT_LAMPORTS,
    )?;
    insert_account(
        &mut accounts,
        lane_key,
        pool_program,
        encode_pool_v1_pair_forest_lane_state_v1(&lane, &POOL_V1_PAIR_EMPTY_ROOTS)
            .map_err(|error| anyhow!("encode lane: {error:?}"))?
            .to_vec(),
        DATA_ACCOUNT_LAMPORTS,
    )?;
    insert_account(
        &mut accounts,
        page_key,
        pool_program,
        history_image.clone(),
        DATA_ACCOUNT_LAMPORTS,
    )?;
    if let Some(next_page_key) = next_page_key {
        insert_account(
            &mut accounts,
            next_page_key,
            pool_program,
            vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES],
            DATA_ACCOUNT_LAMPORTS,
        )?;
    }
    insert_account(&mut accounts, marker_key, Pubkey::default(), Vec::new(), 0)?;
    insert_account(
        &mut accounts,
        registry_key,
        registry_program,
        registry_image.to_vec(),
        DATA_ACCOUNT_LAMPORTS,
    )?;
    insert_account(
        &mut accounts,
        entry_key,
        registry_program,
        entry_image.to_vec(),
        DATA_ACCOUNT_LAMPORTS,
    )?;
    insert_account(
        &mut accounts,
        proof_key,
        verifier_program,
        proof_image,
        DATA_ACCOUNT_LAMPORTS,
    )?;
    if spec.operation == Operation::Withdrawal {
        insert_account(
            &mut accounts,
            mint,
            token_program,
            initialized_mint_data(1_000_000, 6),
            DATA_ACCOUNT_LAMPORTS,
        )?;
        insert_account(
            &mut accounts,
            vault_key,
            token_program,
            initialized_token_data(mint, vault_authority, VAULT_BALANCE_BEFORE),
            DATA_ACCOUNT_LAMPORTS,
        )?;
        insert_account(
            &mut accounts,
            destination_key,
            token_program,
            initialized_token_data(
                mint,
                Pubkey::new_from_array(DESTINATION_TOKEN_OWNER_BYTES),
                DESTINATION_BALANCE_BEFORE,
            ),
            DATA_ACCOUNT_LAMPORTS,
        )?;
        insert_account(
            &mut accounts,
            vault_authority,
            Pubkey::default(),
            Vec::new(),
            DATA_ACCOUNT_LAMPORTS,
        )?;
    }

    match spec.mutation {
        Mutation::None
        | Mutation::WrongRegistryRelease
        | Mutation::StrictProofMutation
        | Mutation::MalformedResult
        | Mutation::MutatedResult
        | Mutation::FailingWithdrawalCpi => {}
        Mutation::StaleLane => {
            let stale_tree = lane
                .tree
                .append_one_with_empty_roots(strict_lane_digest(50_000), &POOL_V1_PAIR_EMPTY_ROOTS)
                .map_err(|error| anyhow!("advance stale lane: {error:?}"))?
                .0;
            let stale_lane = PoolV1PairForestLaneStateV1 {
                master: lane.master,
                lane_id: lane.lane_id,
                tree: stale_tree,
            };
            replace_account_data(
                &mut accounts,
                lane_key,
                encode_pool_v1_pair_forest_lane_state_v1(&stale_lane, &POOL_V1_PAIR_EMPTY_ROOTS)
                    .map_err(|error| anyhow!("encode stale lane: {error:?}"))?
                    .to_vec(),
            )?;
            let mut stale_history = history_image.clone();
            append_root_history_page_bytes_v1(
                &mut stale_history,
                stale_tree.next_leaf_index,
                stale_tree.root,
            )
            .map_err(|error| anyhow!("append stale history: {error:?}"))?;
            replace_account_data(&mut accounts, page_key, stale_history)?;
        }
        Mutation::ReplayMarker => {
            let marker = accounts
                .get_mut(&account_key(&marker_key))
                .context("missing replay marker")?;
            marker.owner = pool_program;
            marker.data = expected_marker.to_vec();
            marker.lamports = Rent::default()
                .minimum_balance(POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES)
                .max(1);
        }
    }

    // The fixture needs only a public fee-payer address. The wallet emits a
    // zero-signature simulation request, so no private key is constructed,
    // stored, serialized, or loaded by this generator.
    let payer_key = Pubkey::from_str(SIMULATION_FEE_PAYER_ID)
        .context("decode deterministic public simulation fee payer")?;
    insert_account(
        &mut accounts,
        payer_key,
        Pubkey::default(),
        Vec::new(),
        PAYER_LAMPORTS,
    )?;

    let mut post_keys = vec![master_key, checkpoint_key, lane_key, page_key];
    if let Some(next_page_key) = next_page_key {
        post_keys.push(next_page_key);
    }
    post_keys.extend([marker_key, registry_key, entry_key, proof_key]);
    if spec.operation == Operation::Withdrawal {
        post_keys.extend([mint, vault_key, destination_key, vault_authority]);
    }
    ensure!(
        post_keys
            .iter()
            .map(ToString::to_string)
            .collect::<BTreeSet<_>>()
            .len()
            == post_keys.len(),
        "post-state account list contains duplicates"
    );

    let mut instruction_accounts = vec![
        account_meta(master_key, false, false),
        account_meta(checkpoint_key, false, false),
        account_meta(lane_key, true, false),
        account_meta(page_key, !rollover, false),
    ];
    if let Some(next_page_key) = next_page_key {
        instruction_accounts.push(account_meta(next_page_key, true, false));
    }
    instruction_accounts.extend([
        account_meta(marker_key, true, false),
        account_meta(payer_key, true, true),
        account_meta(Pubkey::default(), false, false),
        account_meta(registry_key, false, false),
        account_meta(entry_key, false, false),
        account_meta(verifier_program, false, false),
        account_meta(proof_key, false, false),
    ]);
    if spec.operation == Operation::Withdrawal {
        instruction_accounts.extend([
            account_meta(mint, false, false),
            account_meta(vault_key, true, false),
            account_meta(destination_key, true, false),
            account_meta(vault_authority, false, false),
            account_meta(token_program, false, false),
        ]);
    }

    let input = json!({
        "schema": "aspis.v7.txv1-simulation-input.v1",
        "requestId": request_id,
        "minContextSlot": 1,
        "feePayer": payer_key.to_string(),
        "recentBlockhash": "11111111111111111111111111111111",
        "poolProgram": pool_program.to_string(),
        "operation": spec.operation.input_name(),
        "historyPath": spec.history_name(),
        "instructionAccounts": instruction_accounts,
        "instructionDataBase64": BASE64_STANDARD.encode(instruction_data),
        "postStateAccounts": post_keys.iter().map(ToString::to_string).collect::<Vec<_>>(),
    });
    let case_relative = format!("cases/{}/input.json", spec.name);
    let input_sha = write_json(&output.join(&case_relative), &input)?;

    let mut genesis = Vec::new();
    for (address, account) in &accounts {
        let (file, file_sha) = materialize_account_file(output, account)?;
        genesis.push(json!({
            "address": address,
            "file": file,
            "fileSha256": file_sha,
            "loadAtGenesis": account.lamports > 0,
        }));
    }
    let genesis_sha = sha256_hex(&serde_json::to_vec(&genesis)?);
    let post_keys_json = post_keys
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    let post_keys_sha = sha256_hex(&serde_json::to_vec(&post_keys_json)?);

    let mut expected_simulation_accounts_sha = None;
    let mut expected_simulation_accounts_file = None;
    let mut expected_simulation_accounts_file_sha = None;
    if spec.succeeds() {
        let mut expected = accounts.clone();
        replace_account_data(
            &mut expected,
            lane_key,
            encode_pool_v1_pair_forest_lane_state_v1(
                &PoolV1PairForestLaneStateV1 {
                    master: lane.master,
                    lane_id: lane.lane_id,
                    tree: next_tree,
                },
                &POOL_V1_PAIR_EMPTY_ROOTS,
            )
            .map_err(|error| anyhow!("encode expected lane: {error:?}"))?
            .to_vec(),
        )?;
        replace_account_data(&mut expected, page_key, successful_history)?;
        if let (Some(next_page_key), Some(next_page)) = (next_page_key, successful_next_page) {
            replace_account_data(&mut expected, next_page_key, next_page)?;
        }
        let expected_marker_account = expected
            .get_mut(&account_key(&marker_key))
            .context("missing expected marker")?;
        expected_marker_account.owner = pool_program;
        expected_marker_account.data = expected_marker.to_vec();
        expected_marker_account.lamports = Rent::default()
            .minimum_balance(POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES)
            .max(1);
        if spec.operation == Operation::Withdrawal {
            replace_account_data(
                &mut expected,
                vault_key,
                initialized_token_data(
                    mint,
                    vault_authority,
                    VAULT_BALANCE_BEFORE - WITHDRAWAL_AMOUNT,
                ),
            )?;
            replace_account_data(
                &mut expected,
                destination_key,
                initialized_token_data(
                    mint,
                    Pubkey::new_from_array(DESTINATION_TOKEN_OWNER_BYTES),
                    DESTINATION_BALANCE_BEFORE + WITHDRAWAL_AMOUNT,
                ),
            )?;
        }
        let expected_accounts = post_keys
            .iter()
            .map(|key| {
                expected
                    .get(&account_key(key))
                    .with_context(|| format!("missing expected account {key}"))
                    .map(FixtureAccount::rpc_json)
            })
            .collect::<Result<Vec<_>>>()?;
        let expected_value = Value::Array(expected_accounts);
        expected_simulation_accounts_sha = Some(sha256_hex(&serde_json::to_vec(&expected_value)?));
        let expected_relative = format!("cases/{}/expected-simulation-accounts.json", spec.name);
        let expected_file_sha = write_json(&output.join(&expected_relative), &expected_value)?;
        expected_simulation_accounts_file = Some(expected_relative);
        expected_simulation_accounts_file_sha = Some(expected_file_sha);
    }

    let mut expected_logs = vec![format!("Program {} failed", pool_program)];
    let mut program_overrides = Vec::new();
    if spec.succeeds() {
        expected_logs = vec![
            format!("Program {} success", verifier_program),
            format!("Program {} success", pool_program),
        ];
        if spec.operation == Operation::Withdrawal {
            expected_logs.push(format!("Program {} success", token_program));
        }
    } else if spec.uses_result_double() {
        expected_logs.push(format!("Program {} success", verifier_program));
    } else if spec.mutation == Mutation::FailingWithdrawalCpi {
        expected_logs.push(format!("Program {} success", verifier_program));
        expected_logs.push(format!("Program {} failed", token_program));
        program_overrides.push(json!({
            "address": token_program.to_string(),
            "file": artifacts.result_double.relative,
            "fileSha256": artifacts.result_double.sha256,
            "loader": "bpf",
            "purpose": "deterministic rejecting CPI test double; production SPL Token is not replaced outside this disposable case",
        }));
    }

    Ok(json!({
        "name": spec.name,
        "input": case_relative,
        "inputSha256": input_sha,
        "expectedOutcome": if spec.succeeds() { "success" } else { "failure" },
        "expectedLogContains": expected_logs,
        "expectedFailureStage": spec.failure_stage,
        "rollbackRequired": !spec.succeeds(),
        "selectedVerifier": {
            "file": selected_verifier.relative,
            "fileSha256": selected_verifier.sha256,
            "fileBytes": selected_verifier.bytes.len(),
            "loader": "upgradeable-none",
        },
        "registryV2Fixtures": {
            "registrySource": registry_fixture.strip_prefix(repo)?.to_string_lossy(),
            "registrySha256": sha256_hex(&registry_image),
            "registryBytes": registry_image.len(),
            "entrySource": entry_fixture.strip_prefix(repo)?.to_string_lossy(),
            "entrySha256": sha256_hex(&entry_image),
            "entryBytes": entry_image.len(),
            "registryProgramdata": registry_programdata.to_string(),
            "verifierProgramdata": verifier_programdata.to_string(),
            "registryExecutableSha256": artifacts.registry.sha256,
            "selectedVerifierExecutableSha256": selected_verifier.sha256,
        },
        "markerStart": {
            "kind": if spec.mutation == Mutation::ReplayMarker {
                "consumed-pool-owned"
            } else {
                "zero-lamport-system-owned"
            },
            "lamports": accounts.get(&account_key(&marker_key)).map(|account| account.lamports),
            "owner": accounts.get(&account_key(&marker_key)).map(|account| account.owner.to_string()),
            "dataBytes": accounts.get(&account_key(&marker_key)).map(|account| account.data.len()),
        },
        "genesisAccounts": genesis,
        "genesisAccountsSha256": genesis_sha,
        "postStateAccountsSha256": post_keys_sha,
        "expectedSimulationAccountsSha256": expected_simulation_accounts_sha,
        "expectedSimulationAccountsFile": expected_simulation_accounts_file,
        "expectedSimulationAccountsFileSha256": expected_simulation_accounts_file_sha,
        "programOverrides": program_overrides,
    }))
}

fn collect_files(root: &Path, current: &Path, files: &mut Vec<PathBuf>) -> Result<()> {
    for entry in fs::read_dir(current)? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            collect_files(root, &path, files)?;
        } else {
            let relative = path.strip_prefix(root)?.to_path_buf();
            if relative != Path::new("TEMPLATE-SHA256SUMS") {
                files.push(relative);
            }
        }
    }
    Ok(())
}

fn load_sbf(source: &str, relative: &'static str) -> Result<SbfArtifact> {
    let bytes = fs::read(source).with_context(|| format!("read SBF artifact {source}"))?;
    ensure!(!bytes.is_empty(), "SBF artifact is empty: {source}");
    let digest: [u8; 32] = Sha256::digest(&bytes).into();
    Ok(SbfArtifact {
        source: PathBuf::from(source),
        relative,
        sha256: sha256_hex(&bytes),
        digest,
        bytes,
    })
}

fn parse_arguments() -> Result<(PathBuf, SbfArtifacts)> {
    let arguments = env::args().skip(1).collect::<Vec<_>>();
    match arguments.as_slice() {
        [output, pool_flag, pool_sbf, verifier_flag, verifier_sbf, registry_flag, registry_sbf, result_double_flag, result_double_sbf]
            if pool_flag == "--pool-sbf"
                && verifier_flag == "--verifier-sbf"
                && registry_flag == "--registry-sbf"
                && result_double_flag == "--result-double-sbf" =>
        {
            Ok((
                PathBuf::from(output),
                SbfArtifacts {
                    pool: load_sbf(pool_sbf, "sbf/aspis_pool.so")?,
                    verifier: load_sbf(verifier_sbf, "sbf/aspis_verifier.so")?,
                    registry: load_sbf(registry_sbf, "sbf/aspis_registry.so")?,
                    result_double: load_sbf(
                        result_double_sbf,
                        "sbf/aspis_pair_forest_result_double.so",
                    )?,
                },
            ))
        }
        _ => {
            eprintln!(
                "usage: generate_txv1_agave_bundle <new-output-directory> \
                 --pool-sbf <aspis_pool.so> --verifier-sbf <aspis_verifier.so> \
                 --registry-sbf <aspis_registry.so> \
                 --result-double-sbf <aspis_pair_forest_result_double.so>"
            );
            std::process::exit(2);
        }
    }
}

fn main() -> Result<()> {
    let (output, artifacts) = parse_arguments()?;
    ensure!(
        !output.exists(),
        "refusing to overwrite {}",
        output.display()
    );
    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .canonicalize()
        .context("resolve repository root")?;
    fs::create_dir_all(output.join("accounts"))?;
    fs::create_dir_all(output.join("cases"))?;
    fs::create_dir_all(output.join("sbf"))?;
    for artifact in [
        &artifacts.pool,
        &artifacts.verifier,
        &artifacts.registry,
        &artifacts.result_double,
    ] {
        let destination = output.join(artifact.relative);
        fs::copy(&artifact.source, &destination).with_context(|| {
            format!(
                "copy SBF {} to {}",
                artifact.source.display(),
                destination.display()
            )
        })?;
        ensure!(
            fs::read(&destination)? == artifact.bytes,
            "copied SBF differs: {}",
            artifact.relative
        );
    }

    let mut cases = Vec::new();
    for (index, spec) in CASES.into_iter().enumerate() {
        cases.push(case_bundle(
            &repo,
            &output,
            &artifacts,
            spec,
            1_000 + index as u64,
        )?);
    }
    let names = cases
        .iter()
        .map(|case| case["name"].as_str().unwrap_or_default())
        .collect::<BTreeSet<_>>();
    ensure!(names.len() == CASES.len(), "case names are not unique");

    let bundle = json!({
        "schema": "aspis.v7.registry-v2-disposable-agave-txv1-bundle.v1",
        "generatorSchema": "aspis.v7.registry-v2-deterministic-agave-bundle-generator.v1",
        "programSourceCommit": PROGRAM_SOURCE_COMMIT,
        "programSourceTree": PROGRAM_SOURCE_TREE,
        "poolSourceTree": POOL_SOURCE_TREE,
        "verifierSourceTree": VERIFIER_SOURCE_TREE,
        "registrySourceTree": REGISTRY_SOURCE_TREE,
        "poolProgram": Pubkey::new_from_array(POOL_PROGRAM_BYTES).to_string(),
        "verifierProgram": VERIFIER_PROGRAM_ID,
        "registryProgram": Pubkey::new_from_array(REGISTRY_PROGRAM_BYTES).to_string(),
        "poolSbf": artifacts.pool.relative,
        "poolSbfSha256": artifacts.pool.sha256,
        "poolSbfBytes": artifacts.pool.bytes.len(),
        "verifierSbf": artifacts.verifier.relative,
        "verifierSbfSha256": artifacts.verifier.sha256,
        "verifierSbfBytes": artifacts.verifier.bytes.len(),
        "registrySbf": artifacts.registry.relative,
        "registrySbfSha256": artifacts.registry.sha256,
        "registrySbfBytes": artifacts.registry.bytes.len(),
        "resultDoubleSbf": artifacts.result_double.relative,
        "resultDoubleSbfSha256": artifacts.result_double.sha256,
        "resultDoubleSbfBytes": artifacts.result_double.bytes.len(),
        "sbfBindingComplete": true,
        "sbfFilesIncludedInTemplate": true,
        "executionReady": true,
        "warpSlot": PROFILE_SLOT,
        "computeUnitCeiling": 1_300_000,
        "transactionByteCeilingExclusive": 4_096,
        "allNegativeCasesRequireRollback": true,
        "signed": false,
        "submitted": false,
        "deployed": false,
        "cases": cases,
    });
    write_json(&output.join("bundle.json"), &bundle)?;

    let mut files = Vec::new();
    collect_files(&output, &output, &mut files)?;
    files.sort();
    let mut sums = String::new();
    for relative in files {
        let bytes = fs::read(output.join(&relative))?;
        sums.push_str(&format!(
            "{}  {}\n",
            sha256_hex(&bytes),
            relative.to_string_lossy()
        ));
    }
    fs::write(output.join("TEMPLATE-SHA256SUMS"), sums)?;
    println!(
        "deterministic V7 TxV1 Agave bundle template generated: {}",
        output.display()
    );
    println!("cases={}", CASES.len());
    println!("sbf_binding_complete=true");
    println!("signed=false submitted=false deployed=false");
    Ok(())
}
