//! Smallest live-account adapter for the first finalized pair-forest deposit.
//!
//! This adapter is intentionally narrow.  It accepts the one state that can
//! be reconstructed without an indexer-maintained historical leaf stream:
//! eight freshly initialized lanes, one finalized public deposit, and the
//! immediately following coherent checkpoint.  A later or populated state is
//! rejected and must use the durable per-lane witness/indexer path instead.

use std::collections::BTreeSet;

use anyhow::{anyhow, ensure, Result};
use aspis_core::field::{M31, P};
use aspis_pool::{
    pool_v1_pair_forest_checkpoint_address, pool_v1_pair_forest_lane_address,
    pool_v1_pair_forest_master_address, POOL_V1_PAIR_EMPTY_ROOTS,
};
use aspis_statement::pool_v1::pair_trace::PoolV1PairInputNoteWitnessV1;
use aspis_statement::{
    derive_owner_key,
    pool_v1::{
        compile_pool_v1_pair_forest_private_transfer_merged_c1_v1,
        decode_pool_v1_pair_forest_checkpoint_v1, decode_pool_v1_pair_forest_lane_state_v1,
        decode_pool_v1_pair_forest_master_v1, decode_pool_v1_pair_forest_terminal_request_v1,
        decode_pool_v1_pair_forest_terminal_statement_v1, encode_pool_v1_pair_forest_checkpoint_v1,
        encode_pool_v1_pair_forest_lane_state_v1, encode_pool_v1_pair_forest_master_v1,
        encode_pool_v1_pair_forest_terminal_request_v1,
        encode_pool_v1_pair_forest_terminal_statement_v1, pool_v1_note_commitment,
        pool_v1_nullifier, pool_v1_pair_forest_deposit_lane_v1, pool_v1_pair_forest_output_lane_v1,
        pool_v1_tree_parent, reconstruct_pool_v1_pair_forest_terminal_statement_v1,
        v7_pool_pair_forest_tag73_statement_digest_v1,
        verify_pool_v1_pair_forest_terminal_inactive_v1, PoolV1MembershipWitnessV1,
        PoolV1OutputNoteWitnessV1, PoolV1PairForestInputNoteWitnessV1, PoolV1PairForestLaneStateV1,
        PoolV1PairForestPrivateTransferWitnessV1, PoolV1PairForestTerminalAccountsV1,
        PoolV1PairForestTerminalCommonV1, PoolV1PairForestTerminalPaymentV1,
        PoolV1PairForestTerminalRequestV1, PoolV1PairForestTerminalResultV1,
        PoolV1PairForestTerminalStatementV1, PoolV1PairLeafWitnessV1, PoolV1PairLiveSnapshotV1,
        PoolV1PaymentRelationContextV1, PoolV1PaymentRuntimeBindingV1,
        PoolV1PrivateTransferPublicV1, POOL_V1_PAIR_FOREST_ALL_LANES_MASK,
        POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES, POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES,
        POOL_V1_PAIR_FOREST_LANE_COUNT, POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES,
        POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES, POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES,
        POOL_V1_PAIR_TREE_DEPTH, V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,
        V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
    },
    poseidon2::Digest,
};
use sha2::{Digest as _, Sha256};
use solana_program::pubkey::Pubkey;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HarnessRpcCommitmentV1 {
    Processed,
    Confirmed,
    Finalized,
}

/// One account returned in a single coherent RPC snapshot.
///
/// `context_slot` is checked across the master, all lanes and checkpoint.
/// The caller remains responsible for obtaining these bytes from a trusted RPC
/// response; the adapter then validates ownership, executability, PDA and the
/// complete canonical account codec before using any field.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalizedPoolAccountImageV1 {
    pub address: [u8; 32],
    pub owner: [u8; 32],
    pub executable: bool,
    pub commitment: HarnessRpcCommitmentV1,
    pub context_slot: u64,
    pub data: Vec<u8>,
}

pub struct FreshDepositTransferAdapterInputV1<'a> {
    pub pool_program: [u8; 32],
    pub master: &'a FinalizedPoolAccountImageV1,
    /// Exact lane-id order `0..7` from the same finalized RPC context.
    pub lanes: &'a [FinalizedPoolAccountImageV1; POOL_V1_PAIR_FOREST_LANE_COUNT],
    pub checkpoint: &'a FinalizedPoolAccountImageV1,
    /// Local spending secret corresponding to `input_note.owner_key`.
    pub nullifier_key: Digest,
    /// Private opening of the finalized public deposit.
    pub input_note: PoolV1OutputNoteWitnessV1,
    pub recipient: PoolV1OutputNoteWitnessV1,
    pub change: PoolV1OutputNoteWitnessV1,
}

#[derive(Clone, Debug)]
pub struct BuiltFreshDepositTransferAdapterV1 {
    pub input_lane: u8,
    pub output_lane: u8,
    pub witness: PoolV1PairForestPrivateTransferWitnessV1,
    pub public: PoolV1PrivateTransferPublicV1,
    pub request: PoolV1PairForestTerminalRequestV1,
    pub statement: PoolV1PairForestTerminalStatementV1,
    pub terminal_result: PoolV1PairForestTerminalResultV1,
    pub asq8: [u8; POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES],
    pub asf8: [u8; POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES],
    pub statement_digest: [u8; 32],
}

fn sha256_hashv(inputs: &[&[u8]]) -> [u8; 32] {
    let mut hash = Sha256::new();
    for input in inputs {
        hash.update(input);
    }
    hash.finalize().into()
}

fn digest_is_canonical(value: &Digest) -> bool {
    value.iter().all(|limb| limb.0 < P)
}

fn require_finalized_pool_account(
    account: &FinalizedPoolAccountImageV1,
    pool_program: [u8; 32],
    context_slot: u64,
    expected_len: usize,
) -> Result<()> {
    ensure!(
        account.commitment == HarnessRpcCommitmentV1::Finalized,
        "account is not finalized"
    );
    ensure!(context_slot != 0, "zero RPC context slot");
    ensure!(
        account.context_slot == context_slot,
        "incoherent RPC context slot"
    );
    ensure!(account.owner == pool_program, "wrong Pool account owner");
    ensure!(!account.executable, "Pool state account is executable");
    ensure!(account.address != [0u8; 32], "zero Pool account address");
    ensure!(
        account.data.len() == expected_len,
        "wrong Pool account length"
    );
    Ok(())
}

fn forest_path_for_lane(
    lane_roots: &[Digest; POOL_V1_PAIR_FOREST_LANE_COUNT],
    lane: u8,
) -> ([Digest; 3], [bool; 3], Digest) {
    let lane = usize::from(lane);
    let level_one: [Digest; 4] = core::array::from_fn(|index| {
        pool_v1_tree_parent(&lane_roots[2 * index], &lane_roots[2 * index + 1])
    });
    let level_two = [
        pool_v1_tree_parent(&level_one[0], &level_one[1]),
        pool_v1_tree_parent(&level_one[2], &level_one[3]),
    ];
    let siblings = [
        lane_roots[lane ^ 1],
        level_one[(lane >> 1) ^ 1],
        level_two[(lane >> 2) ^ 1],
    ];
    let directions = [lane & 1 != 0, lane & 2 != 0, lane & 4 != 0];
    (
        siblings,
        directions,
        pool_v1_tree_parent(&level_two[0], &level_two[1]),
    )
}

/// Build the exact first-deposit input witness and its transfer ASQ8/ASF8.
///
/// This function refuses a populated forest.  That refusal is important: an
/// account frontier alone does not reveal historical authentication paths.
/// General operation requires the separately maintained finalized append
/// stream and durable per-lane witness state.
pub fn build_fresh_deposit_transfer_adapter_v1(
    input: FreshDepositTransferAdapterInputV1<'_>,
) -> Result<BuiltFreshDepositTransferAdapterV1> {
    ensure!(input.pool_program != [0u8; 32], "zero Pool program");
    ensure!(
        [
            &input.nullifier_key,
            &input.input_note.owner_key,
            &input.input_note.salt,
            &input.recipient.owner_key,
            &input.recipient.salt,
            &input.change.owner_key,
            &input.change.salt,
        ]
        .into_iter()
        .all(digest_is_canonical),
        "noncanonical private witness digest"
    );
    let context_slot = input.master.context_slot;
    require_finalized_pool_account(
        input.master,
        input.pool_program,
        context_slot,
        POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES,
    )?;
    require_finalized_pool_account(
        input.checkpoint,
        input.pool_program,
        context_slot,
        POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES,
    )?;
    for lane in input.lanes {
        require_finalized_pool_account(
            lane,
            input.pool_program,
            context_slot,
            POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES,
        )?;
    }

    let master = decode_pool_v1_pair_forest_master_v1(&input.master.data)
        .map_err(|error| anyhow!("decode master: {error:?}"))?;
    ensure!(
        encode_pool_v1_pair_forest_master_v1(&master)
            .map_err(|error| anyhow!("re-encode master: {error:?}"))?
            .as_slice()
            == input.master.data,
        "noncanonical master image"
    );
    let program = Pubkey::new_from_array(input.pool_program);
    let mint = Pubkey::new_from_array(master.identity.asset_mint);
    let expected_master = pool_v1_pair_forest_master_address(&program, &mint).0;
    ensure!(
        expected_master.to_bytes() == input.master.address
            && master.identity.pool == input.master.address,
        "master PDA/identity mismatch"
    );
    ensure!(
        master.initialized_lane_mask == POOL_V1_PAIR_FOREST_ALL_LANES_MASK,
        "not all lanes initialized"
    );

    let mut lane_states = Vec::with_capacity(POOL_V1_PAIR_FOREST_LANE_COUNT);
    let mut addresses = BTreeSet::new();
    for (lane_id, account) in input.lanes.iter().enumerate() {
        ensure!(addresses.insert(account.address), "lane account alias");
        let expected = pool_v1_pair_forest_lane_address(&program, &expected_master, lane_id as u8)
            .map_err(|error| anyhow!("derive lane {lane_id} PDA: {error:?}"))?
            .0;
        ensure!(
            expected.to_bytes() == account.address,
            "wrong lane PDA/order"
        );
        let lane =
            decode_pool_v1_pair_forest_lane_state_v1(&account.data, &POOL_V1_PAIR_EMPTY_ROOTS)
                .map_err(|error| anyhow!("decode lane {lane_id}: {error:?}"))?;
        ensure!(
            lane.master == input.master.address && usize::from(lane.lane_id) == lane_id,
            "lane master/id mismatch"
        );
        ensure!(
            encode_pool_v1_pair_forest_lane_state_v1(&lane, &POOL_V1_PAIR_EMPTY_ROOTS)
                .map_err(|error| anyhow!("re-encode lane {lane_id}: {error:?}"))?
                .as_slice()
                == account.data,
            "noncanonical lane image"
        );
        lane_states.push(lane);
    }
    let lane_states: [PoolV1PairForestLaneStateV1; POOL_V1_PAIR_FOREST_LANE_COUNT] = lane_states
        .try_into()
        .map_err(|_| anyhow!("wrong lane count"))?;

    let checkpoint = decode_pool_v1_pair_forest_checkpoint_v1(&input.checkpoint.data)
        .map_err(|error| anyhow!("decode checkpoint: {error:?}"))?;
    ensure!(
        encode_pool_v1_pair_forest_checkpoint_v1(&checkpoint)
            .map_err(|error| anyhow!("re-encode checkpoint: {error:?}"))?
            .as_slice()
            == input.checkpoint.data,
        "noncanonical checkpoint image"
    );
    let expected_checkpoint = pool_v1_pair_forest_checkpoint_address(
        &program,
        &expected_master,
        checkpoint.checkpoint_sequence,
    )
    .0;
    ensure!(
        expected_checkpoint.to_bytes() == input.checkpoint.address,
        "wrong checkpoint PDA"
    );
    ensure!(
        checkpoint.master == input.master.address
            && checkpoint.deployment_domain == master.identity.deployment_domain,
        "checkpoint identity mismatch"
    );
    ensure!(
        master.has_checkpoint
            && checkpoint.checkpoint_sequence == 0
            && master.next_checkpoint_sequence == 1
            && master.last_checkpoint_lane_sequences == checkpoint.lane_sequences,
        "not the first coherent checkpoint"
    );

    let owner_key = derive_owner_key(&input.nullifier_key);
    ensure!(
        owner_key == input.input_note.owner_key,
        "nullifier key does not own input note"
    );
    let input_commitment = pool_v1_note_commitment(
        &input.input_note.owner_key,
        input.input_note.value,
        master.identity.asset_id,
        &input.input_note.salt,
    );
    let input_lane = pool_v1_pair_forest_deposit_lane_v1(&input_commitment)
        .map_err(|error| anyhow!("derive input lane: {error:?}"))?;
    let pair_leaf = PoolV1PairLeafWitnessV1::single_output(input_commitment)
        .map_err(|error| anyhow!("construct deposited pair leaf: {error:?}"))?;
    let pair_leaf_digest = pair_leaf
        .leaf_digest()
        .map_err(|error| anyhow!("hash deposited pair leaf: {error:?}"))?;

    let empty_tree = PoolV1PairForestLaneStateV1 {
        master: input.master.address,
        lane_id: 0,
        tree: aspis_statement::pool_v1::IncrementalMerkleTreeV1 {
            next_leaf_index: 0,
            root: POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH],
            frontier: core::array::from_fn(|level| POOL_V1_PAIR_EMPTY_ROOTS[level]),
        },
    };
    let expected_deposit_tree = empty_tree
        .tree
        .append_one_with_empty_roots(pair_leaf_digest, &POOL_V1_PAIR_EMPTY_ROOTS)
        .map_err(|error| anyhow!("replay first deposit: {error:?}"))?
        .0;
    for (lane_id, lane) in lane_states.iter().enumerate() {
        let expected_tree = if lane_id == usize::from(input_lane) {
            expected_deposit_tree
        } else {
            empty_tree.tree
        };
        ensure!(
            lane.tree == expected_tree,
            "forest is not exactly fresh-init plus one deposit"
        );
        ensure!(
            checkpoint.lane_sequences[lane_id] == expected_tree.next_leaf_index,
            "checkpoint lane sequence mismatch"
        );
    }

    let lane_roots = lane_states.each_ref().map(|lane| lane.tree.root);
    let (super_root_siblings, super_root_directions, global_root) =
        forest_path_for_lane(&lane_roots, input_lane);
    ensure!(
        global_root == checkpoint.global_root,
        "checkpoint global root mismatch"
    );
    let input_witness = PoolV1PairForestInputNoteWitnessV1 {
        pair: PoolV1PairInputNoteWitnessV1 {
            nullifier_key: input.nullifier_key,
            salt: input.input_note.salt,
            value: input.input_note.value,
            pair_leaf,
            selected_second: false,
            membership: PoolV1MembershipWitnessV1 {
                siblings: core::array::from_fn(|level| POOL_V1_PAIR_EMPTY_ROOTS[level]),
                index: 0,
            },
        },
        super_root_siblings,
        super_root_directions,
    };
    let witness = PoolV1PairForestPrivateTransferWitnessV1 {
        input: input_witness,
        recipient: input.recipient,
        change: input.change,
    };

    let nullifier = pool_v1_nullifier(&input.nullifier_key, &input.input_note.salt);
    let recipient_commitment = pool_v1_note_commitment(
        &input.recipient.owner_key,
        input.recipient.value,
        master.identity.asset_id,
        &input.recipient.salt,
    );
    let change_commitment = pool_v1_note_commitment(
        &input.change.owner_key,
        input.change.value,
        master.identity.asset_id,
        &input.change.salt,
    );
    let public = PoolV1PrivateTransferPublicV1 {
        pool: input.master.address,
        deployment_domain: master.identity.deployment_domain,
        anchor_sequence: checkpoint.checkpoint_sequence,
        anchor_root: checkpoint.global_root,
        nullifier,
        asset_id: master.identity.asset_id,
        recipient_commitment,
        change_commitment,
    };
    let output_lane = pool_v1_pair_forest_output_lane_v1(&nullifier)
        .map_err(|error| anyhow!("derive output lane: {error:?}"))?;
    let selected_lane = lane_states[usize::from(output_lane)];
    let snapshot = PoolV1PairLiveSnapshotV1 {
        pool: input.master.address,
        deployment_domain: master.identity.deployment_domain,
        sequence: selected_lane.tree.next_leaf_index,
        next_pair_index: selected_lane.tree.next_leaf_index,
        current_root: selected_lane.tree.root,
        frontier: selected_lane.tree.frontier,
    };
    let relation_context = PoolV1PaymentRelationContextV1 {
        runtime_binding: PoolV1PaymentRuntimeBindingV1 {
            pool: input.master.address,
            deployment_domain: master.identity.deployment_domain,
            anchor_sequence: checkpoint.checkpoint_sequence,
            anchor_root: checkpoint.global_root,
            asset_id: master.identity.asset_id,
        },
        spent_nullifiers: &[],
    };
    let compilation = compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(
        &public,
        &witness,
        relation_context,
        snapshot,
    )
    .map_err(|error| anyhow!("compile exact forest relation: {error:?}"))?;

    let common = PoolV1PairForestTerminalCommonV1 {
        master_account: input.master.address,
        checkpoint_account: input.checkpoint.address,
        selected_lane_account: input.lanes[usize::from(output_lane)].address,
        output_lane,
        checkpoint_sequence: checkpoint.checkpoint_sequence,
        historical_global_anchor: checkpoint.global_root,
        lane_transition: compilation.public_statement,
    };
    let request = PoolV1PairForestTerminalRequestV1 {
        verifier_profile: V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,
        verifier_release: V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
        pool_program: input.pool_program,
        public: PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public),
    };
    let statement = PoolV1PairForestTerminalStatementV1::PrivateTransfer { common, public };
    let asq8 = encode_pool_v1_pair_forest_terminal_request_v1(&request)
        .map_err(|error| anyhow!("encode ASQ8: {error:?}"))?;
    let decoded_request = decode_pool_v1_pair_forest_terminal_request_v1(&asq8)
        .map_err(|error| anyhow!("decode ASQ8: {error:?}"))?;
    ensure!(
        decoded_request == request,
        "ASQ8 canonical round trip mismatch"
    );
    let reconstructed =
        reconstruct_pool_v1_pair_forest_terminal_statement_v1(&decoded_request, common)
            .map_err(|error| anyhow!("reconstruct ASF8: {error:?}"))?;
    ensure!(
        reconstructed == statement,
        "ASQ8 reconstructed the wrong ASF8"
    );
    let asf8 = encode_pool_v1_pair_forest_terminal_statement_v1(&statement)
        .map_err(|error| anyhow!("encode ASF8: {error:?}"))?;
    ensure!(
        decode_pool_v1_pair_forest_terminal_statement_v1(&asf8)
            .map_err(|error| anyhow!("decode ASF8: {error:?}"))?
            == statement,
        "ASF8 canonical round trip mismatch"
    );

    let terminal_accounts = PoolV1PairForestTerminalAccountsV1 {
        master_account: input.master.address,
        checkpoint_account: input.checkpoint.address,
        selected_lane_account: input.lanes[usize::from(output_lane)].address,
        master,
        checkpoint,
        selected_lane,
        withdrawal_destination_token_account: [0u8; 32],
    };
    let terminal_result = verify_pool_v1_pair_forest_terminal_inactive_v1(
        &statement,
        &terminal_accounts,
        &compilation,
    )
    .map_err(|error| anyhow!("verify exact semantic terminal: {error:?}"))?;
    let statement_digest = v7_pool_pair_forest_tag73_statement_digest_v1(&asf8, sha256_hashv);

    Ok(BuiltFreshDepositTransferAdapterV1 {
        input_lane,
        output_lane,
        witness,
        public,
        request,
        statement,
        terminal_result,
        asq8,
        asf8,
        statement_digest,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_statement::pool_v1::{
        encode_pool_v1_pair_forest_checkpoint_v1, encode_pool_v1_pair_forest_lane_state_v1,
        encode_pool_v1_pair_forest_master_v1, plan_pool_v1_pair_forest_checkpoint_v1,
        IncrementalMerkleTreeV1, PoolIdentityV1, PoolV1PairForestMasterV1, VerifierPolicyV1,
        POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT,
        POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY,
    };

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|lane| M31(seed + 17 * lane as u32 + 1))
    }

    fn account(
        address: [u8; 32],
        owner: [u8; 32],
        context_slot: u64,
        data: Vec<u8>,
    ) -> FinalizedPoolAccountImageV1 {
        FinalizedPoolAccountImageV1 {
            address,
            owner,
            executable: false,
            commitment: HarnessRpcCommitmentV1::Finalized,
            context_slot,
            data,
        }
    }

    struct Fixture {
        program: [u8; 32],
        master: FinalizedPoolAccountImageV1,
        lanes: [FinalizedPoolAccountImageV1; 8],
        checkpoint: FinalizedPoolAccountImageV1,
        nullifier_key: Digest,
        input_note: PoolV1OutputNoteWitnessV1,
        recipient: PoolV1OutputNoteWitnessV1,
        change: PoolV1OutputNoteWitnessV1,
    }

    fn fixture() -> Fixture {
        let program = [0x41; 32];
        let program_key = Pubkey::new_from_array(program);
        let mint = Pubkey::new_from_array([0x42; 32]);
        let master_key = pool_v1_pair_forest_master_address(&program_key, &mint).0;
        let nullifier_key = digest(10);
        let input_note = PoolV1OutputNoteWitnessV1 {
            owner_key: derive_owner_key(&nullifier_key),
            salt: digest(100),
            value: 1_000,
        };
        let input_commitment = pool_v1_note_commitment(
            &input_note.owner_key,
            input_note.value,
            M31(77),
            &input_note.salt,
        );
        let deposit_lane = pool_v1_pair_forest_deposit_lane_v1(&input_commitment).unwrap();
        let pair_leaf = PoolV1PairLeafWitnessV1::single_output(input_commitment)
            .unwrap()
            .leaf_digest()
            .unwrap();
        let empty_tree = IncrementalMerkleTreeV1 {
            next_leaf_index: 0,
            root: POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH],
            frontier: core::array::from_fn(|level| POOL_V1_PAIR_EMPTY_ROOTS[level]),
        };
        let mut lane_values: [PoolV1PairForestLaneStateV1; 8] =
            core::array::from_fn(|lane| PoolV1PairForestLaneStateV1 {
                master: master_key.to_bytes(),
                lane_id: lane as u8,
                tree: empty_tree,
            });
        lane_values[usize::from(deposit_lane)].tree = empty_tree
            .append_one_with_empty_roots(pair_leaf, &POOL_V1_PAIR_EMPTY_ROOTS)
            .unwrap()
            .0;
        let initial_master = PoolV1PairForestMasterV1 {
            identity: PoolIdentityV1 {
                pool: master_key.to_bytes(),
                asset_mint: mint.to_bytes(),
                token_program: [3u8; 32],
                asset_id: M31(77),
                deployment_domain: [5u8; 32],
            },
            verifier_policy: VerifierPolicyV1 {
                flags: POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY
                    | POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT,
                registry_program: [6u8; 32],
                registry_authority: [0u8; 32],
                policy_binding: [7u8; 32],
            },
            initialized_lane_mask: POOL_V1_PAIR_FOREST_ALL_LANES_MASK,
            has_checkpoint: false,
            next_checkpoint_sequence: 0,
            last_checkpoint_lane_sequences: [0u64; 8],
        };
        let lane_roots = lane_values.each_ref().map(|lane| lane.tree.root);
        let (_, _, global_root) = forest_path_for_lane(&lane_roots, deposit_lane);
        let plan =
            plan_pool_v1_pair_forest_checkpoint_v1(&initial_master, &lane_values, global_root)
                .unwrap();
        let checkpoint_key = pool_v1_pair_forest_checkpoint_address(
            &program_key,
            &master_key,
            plan.checkpoint.checkpoint_sequence,
        )
        .0;
        let context_slot = 9001;
        let lanes = core::array::from_fn(|lane| {
            let lane_key = pool_v1_pair_forest_lane_address(&program_key, &master_key, lane as u8)
                .unwrap()
                .0;
            account(
                lane_key.to_bytes(),
                program,
                context_slot,
                encode_pool_v1_pair_forest_lane_state_v1(
                    &lane_values[lane],
                    &POOL_V1_PAIR_EMPTY_ROOTS,
                )
                .unwrap()
                .to_vec(),
            )
        });
        Fixture {
            program,
            master: account(
                master_key.to_bytes(),
                program,
                context_slot,
                encode_pool_v1_pair_forest_master_v1(&plan.next_master)
                    .unwrap()
                    .to_vec(),
            ),
            lanes,
            checkpoint: account(
                checkpoint_key.to_bytes(),
                program,
                context_slot,
                encode_pool_v1_pair_forest_checkpoint_v1(&plan.checkpoint)
                    .unwrap()
                    .to_vec(),
            ),
            nullifier_key,
            input_note,
            recipient: PoolV1OutputNoteWitnessV1 {
                owner_key: digest(300),
                salt: digest(400),
                value: 600,
            },
            change: PoolV1OutputNoteWitnessV1 {
                owner_key: digest(500),
                salt: digest(600),
                value: 400,
            },
        }
    }

    fn build(fixture: &Fixture) -> Result<BuiltFreshDepositTransferAdapterV1> {
        build_fresh_deposit_transfer_adapter_v1(FreshDepositTransferAdapterInputV1 {
            pool_program: fixture.program,
            master: &fixture.master,
            lanes: &fixture.lanes,
            checkpoint: &fixture.checkpoint,
            nullifier_key: fixture.nullifier_key,
            input_note: fixture.input_note,
            recipient: fixture.recipient,
            change: fixture.change,
        })
    }

    #[test]
    fn first_finalized_deposit_maps_to_exact_witness_asq8_and_asf8() {
        let fixture = fixture();
        let built = build(&fixture).unwrap();
        assert_eq!(built.asq8.len(), 320);
        assert_eq!(built.asf8.len(), 1_880);
        assert_eq!(built.witness.input.pair.membership.index, 0);
        assert!(!built.witness.input.pair.selected_second);
        assert_eq!(built.statement.common().output_lane, built.output_lane);
        assert_eq!(
            built.public.anchor_root,
            built.statement.common().historical_global_anchor
        );
        assert_eq!(built.terminal_result.nullifier, built.public.nullifier);
        assert_ne!(built.statement_digest, [0u8; 32]);
    }

    #[test]
    fn adapter_fails_closed_on_rpc_account_and_secret_mismatch() {
        let mut nonfinalized = fixture();
        nonfinalized.lanes[0].commitment = HarnessRpcCommitmentV1::Confirmed;
        assert!(build(&nonfinalized).is_err());

        let mut wrong_owner = fixture();
        wrong_owner.checkpoint.owner[0] ^= 1;
        assert!(build(&wrong_owner).is_err());

        let mut incoherent = fixture();
        incoherent.lanes[0].context_slot += 1;
        assert!(build(&incoherent).is_err());

        let mut wrong_secret = fixture();
        wrong_secret.nullifier_key = digest(11);
        assert!(build(&wrong_secret).is_err());

        let mut malformed = fixture();
        malformed.lanes[0].data[0] ^= 1;
        assert!(build(&malformed).is_err());

        // A completely canonical first checkpoint containing two deposits is
        // still outside this adapter. Its historical path must come from the
        // durable append stream rather than being guessed from frontiers.
        let mut populated = fixture();
        let input_commitment = pool_v1_note_commitment(
            &populated.input_note.owner_key,
            populated.input_note.value,
            M31(77),
            &populated.input_note.salt,
        );
        let input_lane = pool_v1_pair_forest_deposit_lane_v1(&input_commitment).unwrap();
        let lane_index = usize::from(input_lane);
        let mut lane = decode_pool_v1_pair_forest_lane_state_v1(
            &populated.lanes[lane_index].data,
            &POOL_V1_PAIR_EMPTY_ROOTS,
        )
        .unwrap();
        let second_leaf = PoolV1PairLeafWitnessV1::single_output(digest(900))
            .unwrap()
            .leaf_digest()
            .unwrap();
        lane.tree = lane
            .tree
            .append_one_with_empty_roots(second_leaf, &POOL_V1_PAIR_EMPTY_ROOTS)
            .unwrap()
            .0;
        populated.lanes[lane_index].data =
            encode_pool_v1_pair_forest_lane_state_v1(&lane, &POOL_V1_PAIR_EMPTY_ROOTS)
                .unwrap()
                .to_vec();
        let lane_values: [PoolV1PairForestLaneStateV1; 8] = core::array::from_fn(|index| {
            decode_pool_v1_pair_forest_lane_state_v1(
                &populated.lanes[index].data,
                &POOL_V1_PAIR_EMPTY_ROOTS,
            )
            .unwrap()
        });
        let lane_roots = lane_values.each_ref().map(|value| value.tree.root);
        let (_, _, global_root) = forest_path_for_lane(&lane_roots, input_lane);
        let mut checkpoint =
            decode_pool_v1_pair_forest_checkpoint_v1(&populated.checkpoint.data).unwrap();
        checkpoint.lane_sequences = lane_values.map(|value| value.tree.next_leaf_index);
        checkpoint.global_root = global_root;
        populated.checkpoint.data = encode_pool_v1_pair_forest_checkpoint_v1(&checkpoint)
            .unwrap()
            .to_vec();
        let mut master = decode_pool_v1_pair_forest_master_v1(&populated.master.data).unwrap();
        master.last_checkpoint_lane_sequences = checkpoint.lane_sequences;
        populated.master.data = encode_pool_v1_pair_forest_master_v1(&master)
            .unwrap()
            .to_vec();
        assert!(build(&populated).is_err());
    }
}
