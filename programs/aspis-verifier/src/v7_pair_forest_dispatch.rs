//! Default-off ASQ8 -> ASF8 -> Tag-73 -> ASR8 verifier composition.
//!
//! The compact request never makes account state trustworthy by itself.  This
//! module authenticates the exact read-only Pool accounts, reconstructs the
//! complete ASF8 statement (including the proof-account candidate afterstate),
//! binds that statement into the Tag-73 transcript, and emits ASR8 only after
//! the eight-lane semantic terminal and the complete one-fold verifier accept.

extern crate alloc;

use alloc::boxed::Box;

use aspis_core::v7_onefold::{
    V7_COMPACT_BODY_WITHOUT_FRONTIERS, V7_COMPACT_DIGEST_BYTES, V7_COMPACT_FRONTIER_CAP_PER_TREE,
};
use aspis_statement::pool_v1::{
    decode_pool_v1_pair_forest_checkpoint_v1, decode_pool_v1_pair_forest_lane_state_v1,
    decode_pool_v1_pair_forest_master_v1, decode_pool_v1_pair_forest_terminal_request_v1,
    decode_pool_v1_pair_verified_afterstate_v1, encode_pool_v1_pair_forest_terminal_result_v1,
    encode_pool_v1_pair_forest_terminal_statement_v1, pool_v1_pair_forest_output_lane_v1,
    v7_pool_pair_forest_tag73_statement_digest_v1,
    validate_pool_v1_pair_forest_terminal_result_against_statement_v1,
    validate_pool_v1_pair_forest_terminal_statement_v1, PoolV1PairForestCheckpointV1,
    PoolV1PairForestLaneStateV1, PoolV1PairForestMasterV1, PoolV1PairForestTerminalCommonV1,
    PoolV1PairForestTerminalRequestV1, PoolV1PairForestTerminalResultV1,
    PoolV1PairForestTerminalStatementV1, PoolV1PairLatePublicStatementV1, PoolV1PairLiveSnapshotV1,
    POOL_V1_PAIR_FOREST_ALL_LANES_MASK, POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES,
    POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES, V7_POOL_NATIVE_TAG73_MIN_FRONTIER_NODES,
    V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING, V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
};
use solana_program::{
    account_info::AccountInfo, entrypoint::ProgramResult, program, program_error::ProgramError,
    pubkey::Pubkey,
};

use crate::{
    lifecycle::{proof_account_finalized, uploaded_proof_bounds},
    v7_pair_empty_roots::V7_PAIR_EMPTY_ROOTS,
};

const PAIR_FOREST_MASTER_SEED: &[u8] = b"aspis-pair-forest-master-v1";
const PAIR_FOREST_LANE_SEED: &[u8] = b"aspis-pair-forest-lane-v1";
const PAIR_FOREST_CHECKPOINT_SEED: &[u8] = b"aspis-pair-forest-checkpoint-v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValidatedV7PairForestAsq8V1 {
    pub statement: Box<PoolV1PairForestTerminalStatementV1>,
    pub frontier_nodes: usize,
    pub proof_length: usize,
}

struct AuthenticatedV7PairForestAsq8AccountsV1 {
    master_account: [u8; 32],
    checkpoint_account: [u8; 32],
    selected_lane_account: [u8; 32],
    master: Box<PoolV1PairForestMasterV1>,
    checkpoint: Box<PoolV1PairForestCheckpointV1>,
    selected_lane: Box<PoolV1PairForestLaneStateV1>,
    live_snapshot: Box<PoolV1PairLiveSnapshotV1>,
}

struct ScannedV7PairForestAsq8ProofV1 {
    candidate_afterstate: Box<aspis_statement::pool_v1::PoolV1PairVerifiedAfterstateV1>,
    frontier_nodes: usize,
    proof_length: usize,
}

fn frontier_nodes_from_proof_length(length: usize) -> Option<usize> {
    let frontier_bytes = length.checked_sub(V7_COMPACT_BODY_WITHOUT_FRONTIERS)?;
    let both_tree_node_bytes = 2usize.checked_mul(V7_COMPACT_DIGEST_BYTES)?;
    if frontier_bytes % both_tree_node_bytes != 0 {
        return None;
    }
    let nodes = frontier_bytes / both_tree_node_bytes;
    (nodes >= V7_POOL_NATIVE_TAG73_MIN_FRONTIER_NODES && nodes <= V7_COMPACT_FRONTIER_CAP_PER_TREE)
        .then_some(nodes)
}

fn require_readonly_account(account: &AccountInfo<'_>, owner: &Pubkey) -> ProgramResult {
    if account.owner != owner || account.is_signer || account.is_writable || account.executable {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}

fn require_distinct_accounts(accounts: &[&AccountInfo<'_>; 4]) -> ProgramResult {
    for (index, account) in accounts.iter().enumerate() {
        if accounts[..index]
            .iter()
            .any(|previous| previous.key == account.key)
        {
            return Err(ProgramError::InvalidArgument);
        }
    }
    Ok(())
}

#[inline(never)]
fn decode_master_box(bytes: &[u8]) -> Result<Box<PoolV1PairForestMasterV1>, ProgramError> {
    Ok(Box::new(
        decode_pool_v1_pair_forest_master_v1(bytes)
            .map_err(|_| ProgramError::InvalidAccountData)?,
    ))
}

#[inline(never)]
fn decode_checkpoint_box(bytes: &[u8]) -> Result<Box<PoolV1PairForestCheckpointV1>, ProgramError> {
    Ok(Box::new(
        decode_pool_v1_pair_forest_checkpoint_v1(bytes)
            .map_err(|_| ProgramError::InvalidAccountData)?,
    ))
}

#[inline(never)]
fn decode_lane_box(bytes: &[u8]) -> Result<Box<PoolV1PairForestLaneStateV1>, ProgramError> {
    Ok(Box::new(
        decode_pool_v1_pair_forest_lane_state_v1(bytes, &V7_PAIR_EMPTY_ROOTS)
            .map_err(|_| ProgramError::InvalidAccountData)?,
    ))
}

#[inline(never)]
fn live_snapshot_box(
    master_account: [u8; 32],
    deployment_domain: [u8; 32],
    selected_lane: &PoolV1PairForestLaneStateV1,
) -> Box<PoolV1PairLiveSnapshotV1> {
    Box::new(PoolV1PairLiveSnapshotV1 {
        pool: master_account,
        deployment_domain,
        sequence: selected_lane.tree.next_leaf_index,
        next_pair_index: selected_lane.tree.next_leaf_index,
        current_root: selected_lane.tree.root,
        frontier: selected_lane.tree.frontier,
    })
}

#[inline(never)]
fn authenticate_asq8_accounts_v1(
    verifier_program: &Pubkey,
    accounts: &[AccountInfo<'_>],
    pool_program: &Pubkey,
    output_lane: u8,
) -> Result<AuthenticatedV7PairForestAsq8AccountsV1, ProgramError> {
    let [proof_account, master_account, checkpoint_account, lane_account] = accounts else {
        return Err(if accounts.len() < 4 {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    };
    require_readonly_account(proof_account, verifier_program)?;
    require_readonly_account(master_account, pool_program)?;
    require_readonly_account(checkpoint_account, pool_program)?;
    require_readonly_account(lane_account, pool_program)?;
    require_distinct_accounts(&[
        proof_account,
        master_account,
        checkpoint_account,
        lane_account,
    ])?;

    let master = decode_master_box(&master_account.try_borrow_data()?)?;
    if master.identity.pool != master_account.key.to_bytes()
        || master.initialized_lane_mask != POOL_V1_PAIR_FOREST_ALL_LANES_MASK
        || Pubkey::find_program_address(
            &[
                PAIR_FOREST_MASTER_SEED,
                Pubkey::new_from_array(master.identity.asset_mint).as_ref(),
            ],
            pool_program,
        )
        .0 != *master_account.key
    {
        return Err(ProgramError::InvalidAccountData);
    }

    let checkpoint = decode_checkpoint_box(&checkpoint_account.try_borrow_data()?)?;
    if checkpoint.master != master_account.key.to_bytes()
        || checkpoint.deployment_domain != master.identity.deployment_domain
        || Pubkey::find_program_address(
            &[
                PAIR_FOREST_CHECKPOINT_SEED,
                master_account.key.as_ref(),
                &checkpoint.checkpoint_sequence.to_le_bytes(),
            ],
            pool_program,
        )
        .0 != *checkpoint_account.key
    {
        return Err(ProgramError::InvalidAccountData);
    }

    let selected_lane = decode_lane_box(&lane_account.try_borrow_data()?)?;
    if selected_lane.master != master_account.key.to_bytes()
        || selected_lane.lane_id != output_lane
        || Pubkey::find_program_address(
            &[
                PAIR_FOREST_LANE_SEED,
                master_account.key.as_ref(),
                &[output_lane],
            ],
            pool_program,
        )
        .0 != *lane_account.key
    {
        return Err(ProgramError::InvalidAccountData);
    }

    let live_snapshot = live_snapshot_box(
        master_account.key.to_bytes(),
        master.identity.deployment_domain,
        &selected_lane,
    );
    Ok(AuthenticatedV7PairForestAsq8AccountsV1 {
        master_account: master_account.key.to_bytes(),
        checkpoint_account: checkpoint_account.key.to_bytes(),
        selected_lane_account: lane_account.key.to_bytes(),
        master,
        checkpoint,
        selected_lane,
        live_snapshot,
    })
}

#[inline(never)]
fn scan_asq8_proof_v1(
    proof_account: &AccountInfo<'_>,
) -> Result<ScannedV7PairForestAsq8ProofV1, ProgramError> {
    let data = proof_account.try_borrow_data()?;
    if !proof_account_finalized(&data) {
        return Err(ProgramError::InvalidAccountData);
    }
    let (payload_start, payload_end) = uploaded_proof_bounds(&data)?;
    if payload_end != data.len()
        || payload_end - payload_start <= POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let payload = &data[payload_start..payload_end];
    let (candidate_bytes, proof) = payload.split_at(POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES);
    let candidate_afterstate = Box::new(
        decode_pool_v1_pair_verified_afterstate_v1(candidate_bytes)
            .map_err(|_| ProgramError::InvalidAccountData)?,
    );
    let proof_length = proof.len();
    let frontier_nodes =
        frontier_nodes_from_proof_length(proof_length).ok_or(ProgramError::InvalidAccountData)?;
    Ok(ScannedV7PairForestAsq8ProofV1 {
        candidate_afterstate,
        frontier_nodes,
        proof_length,
    })
}

#[inline(never)]
fn asq8_common_box_v1(
    authenticated: &AuthenticatedV7PairForestAsq8AccountsV1,
    candidate_afterstate: &aspis_statement::pool_v1::PoolV1PairVerifiedAfterstateV1,
) -> Box<PoolV1PairForestTerminalCommonV1> {
    Box::new(PoolV1PairForestTerminalCommonV1 {
        master_account: authenticated.master_account,
        checkpoint_account: authenticated.checkpoint_account,
        selected_lane_account: authenticated.selected_lane_account,
        output_lane: authenticated.selected_lane.lane_id,
        checkpoint_sequence: authenticated.checkpoint.checkpoint_sequence,
        historical_global_anchor: authenticated.checkpoint.global_root,
        lane_transition: PoolV1PairLatePublicStatementV1 {
            live_snapshot: *authenticated.live_snapshot,
            candidate_afterstate: *candidate_afterstate,
        },
    })
}

#[inline(never)]
fn transfer_statement_box_v1(
    common: Box<PoolV1PairForestTerminalCommonV1>,
    public: aspis_statement::pool_v1::PoolV1PrivateTransferPublicV1,
) -> Result<Box<PoolV1PairForestTerminalStatementV1>, ProgramError> {
    let statement = Box::new(PoolV1PairForestTerminalStatementV1::PrivateTransfer {
        common: *common,
        public,
    });
    validate_pool_v1_pair_forest_terminal_statement_v1(&statement)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    Ok(statement)
}

#[inline(never)]
fn withdrawal_statement_box_v1(
    common: Box<PoolV1PairForestTerminalCommonV1>,
    public: aspis_statement::pool_v1::PoolV1WithdrawalPublicV1,
) -> Result<Box<PoolV1PairForestTerminalStatementV1>, ProgramError> {
    let statement = Box::new(PoolV1PairForestTerminalStatementV1::Withdrawal {
        common: *common,
        public,
    });
    validate_pool_v1_pair_forest_terminal_statement_v1(&statement)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    Ok(statement)
}

#[inline(never)]
fn reconstruct_asq8_statement_box_v1(
    request: &PoolV1PairForestTerminalRequestV1,
    authenticated: &AuthenticatedV7PairForestAsq8AccountsV1,
    candidate_afterstate: &aspis_statement::pool_v1::PoolV1PairVerifiedAfterstateV1,
) -> Result<Box<PoolV1PairForestTerminalStatementV1>, ProgramError> {
    if authenticated.live_snapshot.next_pair_index.checked_add(1)
        != Some(candidate_afterstate.next_pair_index)
    {
        return Err(ProgramError::InvalidAccountData);
    }
    if authenticated.master.identity.asset_id
        != match request.public {
            aspis_statement::pool_v1::PoolV1PairForestTerminalPaymentV1::PrivateTransfer(
                public,
            ) => public.asset_id,
            aspis_statement::pool_v1::PoolV1PairForestTerminalPaymentV1::Withdrawal(public) => {
                public.asset_id
            }
        }
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    let common = asq8_common_box_v1(authenticated, candidate_afterstate);
    match request.public {
        aspis_statement::pool_v1::PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) => {
            transfer_statement_box_v1(common, public)
        }
        aspis_statement::pool_v1::PoolV1PairForestTerminalPaymentV1::Withdrawal(public) => {
            withdrawal_statement_box_v1(common, public)
        }
    }
}

pub fn validate_v7_pair_forest_asq8_request_v1(
    verifier_program: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
) -> Result<ValidatedV7PairForestAsq8V1, ProgramError> {
    if instruction_data.len() != POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES {
        return Err(ProgramError::InvalidInstructionData);
    }
    let request = decode_pool_v1_pair_forest_terminal_request_v1(instruction_data)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    if request.verifier_profile != V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING
        || request.verifier_release != V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    let pool_program = Pubkey::new_from_array(request.pool_program);
    let output_lane = pool_v1_pair_forest_output_lane_v1(request.public.nullifier())
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let authenticated =
        authenticate_asq8_accounts_v1(verifier_program, accounts, &pool_program, output_lane)?;
    let proof_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    let scanned = scan_asq8_proof_v1(proof_account)?;
    let statement =
        reconstruct_asq8_statement_box_v1(&request, &authenticated, &scanned.candidate_afterstate)?;
    Ok(ValidatedV7PairForestAsq8V1 {
        statement,
        frontier_nodes: scanned.frontier_nodes,
        proof_length: scanned.proof_length,
    })
}

#[inline(never)]
fn statement_digest_v1(
    statement: &PoolV1PairForestTerminalStatementV1,
) -> Result<[u8; 32], ProgramError> {
    let statement_bytes = encode_pool_v1_pair_forest_terminal_statement_v1(statement)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    Ok(v7_pool_pair_forest_tag73_statement_digest_v1(
        &statement_bytes,
        crate::verify::sbf_hashv,
    ))
}

#[inline(never)]
fn verify_statement_v1(
    verifier_program: &Pubkey,
    proof_account: &AccountInfo<'_>,
    proof: &[u8],
    frontier_nodes: usize,
    statement: &PoolV1PairForestTerminalStatementV1,
    statement_digest: [u8; 32],
) -> ProgramResult {
    let transition = &statement.common().lane_transition;
    match statement {
        PoolV1PairForestTerminalStatementV1::PrivateTransfer { public, .. } => {
            crate::v7_verifier::verify_v7_pool_pair_forest_private_transfer_with_statement_digest(
                crate::verify::sbf_hashv,
                proof,
                frontier_nodes,
                verifier_program,
                V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
                proof_account.key,
                public,
                transition,
                statement_digest,
                true,
            )
        }
        PoolV1PairForestTerminalStatementV1::Withdrawal { public, .. } => {
            crate::v7_verifier::verify_v7_pool_pair_forest_withdrawal_with_statement_digest(
                crate::verify::sbf_hashv,
                proof,
                frontier_nodes,
                verifier_program,
                V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
                proof_account.key,
                public,
                transition,
                statement_digest,
                true,
            )
        }
    }
    .map(|_| ())
    .map_err(|_| ProgramError::InvalidAccountData)
}

#[inline(never)]
fn emit_result_v1(statement: &PoolV1PairForestTerminalStatementV1) -> ProgramResult {
    let result = PoolV1PairForestTerminalResultV1 {
        transition_kind: statement.transition_kind(),
        master_account: statement.common().master_account,
        selected_lane_account: statement.common().selected_lane_account,
        output_lane: statement.common().output_lane,
        nullifier: *statement.nullifier(),
        verified_afterstate: statement.common().lane_transition.candidate_afterstate,
    };
    validate_pool_v1_pair_forest_terminal_result_against_statement_v1(statement, &result)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let encoded = encode_pool_v1_pair_forest_terminal_result_v1(&result)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    program::set_return_data(&encoded);
    Ok(())
}

fn process_with_clear_return_data<F>(
    verifier_program: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
    clear_return_data: F,
) -> ProgramResult
where
    F: FnOnce(),
{
    clear_return_data();
    let validated =
        validate_v7_pair_forest_asq8_request_v1(verifier_program, accounts, instruction_data)?;
    let proof_account = &accounts[0];
    let data = proof_account.try_borrow_data()?;
    let (payload_start, payload_end) = uploaded_proof_bounds(&data)?;
    if payload_end != data.len() {
        return Err(ProgramError::InvalidAccountData);
    }
    let payload = &data[payload_start..payload_end];
    let proof = payload
        .get(POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES..)
        .ok_or(ProgramError::InvalidAccountData)?;
    if proof.len() != validated.proof_length {
        return Err(ProgramError::InvalidAccountData);
    }
    let statement_digest = statement_digest_v1(&validated.statement)?;
    verify_statement_v1(
        verifier_program,
        proof_account,
        proof,
        validated.frontier_nodes,
        &validated.statement,
        statement_digest,
    )?;
    emit_result_v1(&validated.statement)
}

pub fn process_v7_pair_forest_asq8_instruction(
    verifier_program: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
) -> ProgramResult {
    process_with_clear_return_data(verifier_program, accounts, instruction_data, || {
        program::set_return_data(&[])
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::M31;
    use aspis_statement::pool_v1::{
        encode_pool_v1_pair_forest_checkpoint_v1, encode_pool_v1_pair_forest_lane_state_v1,
        encode_pool_v1_pair_forest_master_v1, encode_pool_v1_pair_forest_terminal_request_v1,
        encode_pool_v1_pair_verified_afterstate_v1, IncrementalMerkleTreeV1, PoolIdentityV1,
        PoolV1PairForestCheckpointV1, PoolV1PairForestLaneStateV1, PoolV1PairForestMasterV1,
        PoolV1PairForestTerminalPaymentV1, PoolV1PairForestTerminalRequestV1,
        PoolV1PairVerifiedAfterstateV1, PoolV1PrivateTransferPublicV1, VerifierPolicyV1,
        POOL_V1_PAIR_TREE_DEPTH,
    };
    use solana_program::clock::Epoch;

    fn digest(seed: u32) -> aspis_statement::Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    struct Fixture {
        verifier: Pubkey,
        proof_owner: Pubkey,
        master_owner: Pubkey,
        checkpoint_owner: Pubkey,
        lane_owner: Pubkey,
        proof_key: Pubkey,
        master_key: Pubkey,
        checkpoint_key: Pubkey,
        lane_key: Pubkey,
        proof_data: Vec<u8>,
        master_data: Vec<u8>,
        checkpoint_data: Vec<u8>,
        lane_data: Vec<u8>,
        request: Vec<u8>,
    }

    fn make_fixture() -> Fixture {
        let verifier = crate::id();
        let pool_program = Pubkey::new_unique();
        let mint = Pubkey::new_unique();
        let master_key =
            Pubkey::find_program_address(&[PAIR_FOREST_MASTER_SEED, mint.as_ref()], &pool_program)
                .0;
        let mut nullifier = digest(100);
        nullifier[0] = M31(3);
        let lane_id = pool_v1_pair_forest_output_lane_v1(&nullifier).unwrap();
        let lane_key = Pubkey::find_program_address(
            &[PAIR_FOREST_LANE_SEED, master_key.as_ref(), &[lane_id]],
            &pool_program,
        )
        .0;
        let checkpoint_sequence = 7u64;
        let checkpoint_key = Pubkey::find_program_address(
            &[
                PAIR_FOREST_CHECKPOINT_SEED,
                master_key.as_ref(),
                &checkpoint_sequence.to_le_bytes(),
            ],
            &pool_program,
        )
        .0;
        let empty = V7_PAIR_EMPTY_ROOTS;
        let lane = PoolV1PairForestLaneStateV1 {
            master: master_key.to_bytes(),
            lane_id,
            tree: IncrementalMerkleTreeV1 {
                next_leaf_index: 0,
                root: empty[POOL_V1_PAIR_TREE_DEPTH],
                frontier: core::array::from_fn(|level| empty[level]),
            },
        };
        let master = PoolV1PairForestMasterV1 {
            identity: PoolIdentityV1 {
                pool: master_key.to_bytes(),
                asset_mint: mint.to_bytes(),
                token_program: Pubkey::new_unique().to_bytes(),
                asset_id: M31(17),
                deployment_domain: [5; 32],
            },
            verifier_policy: VerifierPolicyV1 {
                flags: 1,
                registry_program: Pubkey::new_unique().to_bytes(),
                registry_authority: [0; 32],
                policy_binding: [7; 32],
            },
            initialized_lane_mask: POOL_V1_PAIR_FOREST_ALL_LANES_MASK,
            has_checkpoint: true,
            next_checkpoint_sequence: checkpoint_sequence + 1,
            last_checkpoint_lane_sequences: [0; 8],
        };
        let checkpoint = PoolV1PairForestCheckpointV1 {
            master: master_key.to_bytes(),
            deployment_domain: master.identity.deployment_domain,
            checkpoint_sequence,
            global_root: digest(500),
            lane_sequences: [0; 8],
        };
        let public = PoolV1PrivateTransferPublicV1 {
            pool: master_key.to_bytes(),
            deployment_domain: master.identity.deployment_domain,
            anchor_sequence: checkpoint_sequence,
            anchor_root: checkpoint.global_root,
            nullifier,
            asset_id: master.identity.asset_id,
            recipient_commitment: digest(600),
            change_commitment: digest(700),
        };
        let request = PoolV1PairForestTerminalRequestV1 {
            verifier_profile: V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,
            verifier_release: V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
            pool_program: pool_program.to_bytes(),
            public: PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public),
        };
        let next_tree = lane
            .tree
            .append_one_with_empty_roots(digest(800), &empty)
            .unwrap()
            .0;
        let candidate = PoolV1PairVerifiedAfterstateV1 {
            next_pair_index: next_tree.next_leaf_index,
            next_root: next_tree.root,
            next_frontier: next_tree.frontier,
        };
        let frontier_nodes = aspis_statement::pool_v1::V7_POOL_NATIVE_TAG73_MIN_FRONTIER_NODES;
        let proof_len =
            V7_COMPACT_BODY_WITHOUT_FRONTIERS + 2 * V7_COMPACT_DIGEST_BYTES * frontier_nodes;
        let payload_len = POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES + proof_len;
        let mut proof_data = vec![0u8; crate::PROOF_ACCOUNT_HEADER_LEN + payload_len];
        proof_data[..4].copy_from_slice(b"ASPU");
        proof_data[4..8].copy_from_slice(&(payload_len as u32).to_le_bytes());
        proof_data[crate::PROOF_ACCOUNT_HEADER_LEN
            ..crate::PROOF_ACCOUNT_HEADER_LEN + POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES]
            .copy_from_slice(&encode_pool_v1_pair_verified_afterstate_v1(&candidate).unwrap());
        Fixture {
            verifier,
            proof_owner: verifier,
            master_owner: pool_program,
            checkpoint_owner: pool_program,
            lane_owner: pool_program,
            proof_key: Pubkey::new_unique(),
            master_key,
            checkpoint_key,
            lane_key,
            proof_data,
            master_data: encode_pool_v1_pair_forest_master_v1(&master)
                .unwrap()
                .to_vec(),
            checkpoint_data: encode_pool_v1_pair_forest_checkpoint_v1(&checkpoint)
                .unwrap()
                .to_vec(),
            lane_data: encode_pool_v1_pair_forest_lane_state_v1(&lane, &empty)
                .unwrap()
                .to_vec(),
            request: encode_pool_v1_pair_forest_terminal_request_v1(&request)
                .unwrap()
                .to_vec(),
        }
    }

    fn with_fixture_accounts<T>(
        fixture: &mut Fixture,
        use_accounts: impl FnOnce(&[AccountInfo<'_>]) -> T,
    ) -> T {
        let mut proof_lamports = 1;
        let mut master_lamports = 1;
        let mut checkpoint_lamports = 1;
        let mut lane_lamports = 1;
        let proof = AccountInfo::new(
            &fixture.proof_key,
            false,
            false,
            &mut proof_lamports,
            &mut fixture.proof_data,
            &fixture.proof_owner,
            false,
            Epoch::default(),
        );
        let master = AccountInfo::new(
            &fixture.master_key,
            false,
            false,
            &mut master_lamports,
            &mut fixture.master_data,
            &fixture.master_owner,
            false,
            Epoch::default(),
        );
        let checkpoint = AccountInfo::new(
            &fixture.checkpoint_key,
            false,
            false,
            &mut checkpoint_lamports,
            &mut fixture.checkpoint_data,
            &fixture.checkpoint_owner,
            false,
            Epoch::default(),
        );
        let lane = AccountInfo::new(
            &fixture.lane_key,
            false,
            false,
            &mut lane_lamports,
            &mut fixture.lane_data,
            &fixture.lane_owner,
            false,
            Epoch::default(),
        );
        use_accounts(&[proof, master, checkpoint, lane])
    }

    fn validate_fixture(
        fixture: &mut Fixture,
    ) -> Result<ValidatedV7PairForestAsq8V1, ProgramError> {
        let verifier = fixture.verifier;
        let request = fixture.request.clone();
        with_fixture_accounts(fixture, |accounts| {
            validate_v7_pair_forest_asq8_request_v1(&verifier, accounts, &request)
        })
    }

    #[test]
    fn canonical_asq8_reconstructs_exact_asf8_and_reaches_fail_closed_crypto() {
        let mut fixture = make_fixture();
        let validated = validate_fixture(&mut fixture).unwrap();
        assert_eq!(
            validated.frontier_nodes,
            aspis_statement::pool_v1::V7_POOL_NATIVE_TAG73_MIN_FRONTIER_NODES
        );
        assert_eq!(
            validated.statement.common().master_account,
            fixture.master_key.to_bytes()
        );

        let verifier = fixture.verifier;
        let request = fixture.request.clone();
        let mut cleared = false;
        let result = with_fixture_accounts(&mut fixture, |accounts| {
            process_with_clear_return_data(&verifier, accounts, &request, || {
                cleared = true;
            })
        });
        assert!(cleared);
        assert_eq!(result, Err(ProgramError::InvalidAccountData));
    }

    #[test]
    fn asq8_rejects_every_compact_identity_field_mutation_and_trailing_data() {
        for offset in [8usize, 40, 72, 104] {
            let mut fixture = make_fixture();
            fixture.request[offset] ^= 1;
            assert!(validate_fixture(&mut fixture).is_err(), "offset {offset}");
        }
        let mut fixture = make_fixture();
        fixture.request.push(0);
        assert!(validate_fixture(&mut fixture).is_err());
    }

    #[test]
    fn asq8_rejects_account_codec_and_proof_framing_mutations() {
        let mut fixture = make_fixture();
        fixture.master_data[0] ^= 1;
        assert!(validate_fixture(&mut fixture).is_err());

        let mut fixture = make_fixture();
        fixture.checkpoint_data[80] ^= 1;
        assert!(validate_fixture(&mut fixture).is_err());

        let mut fixture = make_fixture();
        fixture.lane_data[5] = (fixture.lane_data[5] + 1) & 7;
        assert!(validate_fixture(&mut fixture).is_err());

        let mut fixture = make_fixture();
        fixture.proof_data[0] ^= 1;
        assert!(validate_fixture(&mut fixture).is_err());

        let mut fixture = make_fixture();
        fixture.proof_data.push(0);
        assert!(validate_fixture(&mut fixture).is_err());
    }

    #[test]
    fn asq8_rejects_malformed_lane_tree_images() {
        // Lane header (80 bytes), followed by the tree's explicit root at
        // tree offset 16.  A sequence-zero lane must use the pinned depth-20
        // pair root exactly.
        let mut fixture = make_fixture();
        fixture.lane_data[80 + 16] ^= 1;
        assert!(validate_fixture(&mut fixture).is_err());

        // The first frontier node begins at tree offset 48.  It is inactive
        // at sequence zero and therefore must equal pinned pair level zero.
        let mut fixture = make_fixture();
        fixture.lane_data[80 + 48] ^= 1;
        assert!(validate_fixture(&mut fixture).is_err());

        // Field limbs are canonical M31 encodings, not arbitrary u32 values.
        let mut fixture = make_fixture();
        fixture.lane_data[80 + 48..80 + 52].copy_from_slice(&u32::MAX.to_le_bytes());
        assert!(validate_fixture(&mut fixture).is_err());
    }

    #[test]
    fn asq8_rejects_wrong_owner_pda_and_aliases() {
        let mut fixture = make_fixture();
        fixture.master_owner = Pubkey::new_unique();
        assert!(validate_fixture(&mut fixture).is_err());

        let mut fixture = make_fixture();
        fixture.lane_key = Pubkey::new_unique();
        assert!(validate_fixture(&mut fixture).is_err());

        let mut fixture = make_fixture();
        fixture.lane_key = fixture.checkpoint_key;
        assert!(validate_fixture(&mut fixture).is_err());
    }
}
