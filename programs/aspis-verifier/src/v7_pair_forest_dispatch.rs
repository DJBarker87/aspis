//! Default-off ASQ8 account and statement reconstruction boundary.
//!
//! This module closes the compact request, canonical read-only account, proof
//! framing, PDA, and exact ASF8 reconstruction work.  It intentionally cannot
//! emit ASR8 yet: the accepted Tag-73 implementation does not contain the
//! merged-C1 pair-forest semantic terminal.  Returning a proof-carried
//! afterstate after running only the legacy ASCP/ASWP verifier would leave the
//! afterstate outside the transcript and would be a cryptographic weakening.

extern crate alloc;

use alloc::boxed::Box;

use aspis_core::v7_staged_pair::V7_STAGED_PAIR_BODY_WITHOUT_FRONTIERS;
use aspis_statement::decode_digest_canonical;
use aspis_statement::pool_v1::{
    decode_pool_v1_pair_forest_checkpoint_v1, decode_pool_v1_pair_forest_lane_state_v1,
    decode_pool_v1_pair_forest_master_v1, decode_pool_v1_pair_forest_terminal_request_v1,
    decode_pool_v1_pair_forest_terminal_statement_v1, decode_pool_v1_pair_live_snapshot_v1,
    decode_pool_v1_pair_verified_afterstate_v1, decode_pool_v1_private_transfer_public_v1,
    decode_pool_v1_withdrawal_public_v1, encode_pool_v1_pair_live_snapshot_v1,
    pool_v1_pair_forest_output_lane_v1, reconstruct_pool_v1_pair_forest_terminal_statement_v1,
    PoolV1PairForestCheckpointV1, PoolV1PairForestLaneStateV1, PoolV1PairForestMasterV1,
    PoolV1PairForestTerminalCommonV1, PoolV1PairForestTerminalRequestV1,
    PoolV1PairForestTerminalStatementV1, PoolV1PairLatePublicStatementV1, PoolV1PairLiveSnapshotV1,
    PoolV1PairVerifiedAfterstateV1, PoolV1TransitionKind, POOL_V1_DIGEST_ENCODING_VERSION,
    POOL_V1_PAIR_FOREST_ALL_LANES_MASK, POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES,
    POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES, POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC,
    POOL_V1_PAIR_FOREST_TERMINAL_VERSION, POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES,
    POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES, POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT,
    POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC, POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION,
    POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES, POOL_V1_PAIR_TREE_DEPTH,
    POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES, POOL_V1_PAYMENT_STATEMENT_BYTES,
};
use solana_program::{
    account_info::AccountInfo, entrypoint::ProgramResult, program, program_error::ProgramError,
    pubkey::Pubkey,
};

use crate::{
    lifecycle::{proof_account_finalized, uploaded_proof_bounds},
    v7_pair_empty_roots::V7_PAIR_EMPTY_ROOTS,
    v7_staged_pair_profile::{
        parse_v7_staged_pair_inputs_v1, V7_STAGED_PAIR_PROFILE_BINDING,
        V7_STAGED_PAIR_RELEASE_BINDING,
    },
};

const PAIR_FOREST_MASTER_SEED: &[u8] = b"aspis-pair-forest-master-v1";
const PAIR_FOREST_LANE_SEED: &[u8] = b"aspis-pair-forest-lane-v1";
const PAIR_FOREST_CHECKPOINT_SEED: &[u8] = b"aspis-pair-forest-checkpoint-v1";

const ASF8_MASTER_OFFSET: usize = 8;
const ASF8_CHECKPOINT_OFFSET: usize = 40;
const ASF8_LANE_OFFSET: usize = 72;
const ASF8_CHECKPOINT_SEQUENCE_OFFSET: usize = 104;
const ASF8_ANCHOR_OFFSET: usize = 112;
const ASF8_LATE_OFFSET: usize = 144;
const ASF8_PAYMENT_OFFSET: usize = ASF8_LATE_OFFSET + POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES;
const ASF8_LIVE_OFFSET: usize = ASF8_LATE_OFFSET + POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES;
const ASF8_CANDIDATE_OFFSET: usize = ASF8_LIVE_OFFSET + POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES;

/// No successful execution can currently return this error: it is the hard
/// integration gate after every byte/account/PDA check has passed.
pub const V7_PAIR_FOREST_ASQ8_CRYPTO_NOT_INTEGRATED: u32 = 0x4153_5138;
/// The full-statement measurement profile is deliberately not registered in
/// the production dispatcher. Even a fully authenticated request stops here
/// until the merged-C1 cryptographic terminal is integrated.
pub const V7_PAIR_FOREST_ASF8_CRYPTO_NOT_INTEGRATED: u32 = 0x4153_4638;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValidatedV7PairForestAsq8V1 {
    pub request: PoolV1PairForestTerminalRequestV1,
    pub master: PoolV1PairForestMasterV1,
    pub checkpoint: PoolV1PairForestCheckpointV1,
    pub selected_lane: PoolV1PairForestLaneStateV1,
    pub statement: Box<PoolV1PairForestTerminalStatementV1>,
    pub frontier_nodes: usize,
}

/// Account-derived identity for the default-off full-ASF8 profile.
///
/// There are intentionally no caller-provided profile, release, or Pool
/// program fields in ASF8. The executing verifier selects the two compiled
/// bindings, while the Pool program is the single common owner of the three
/// canonical state accounts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AuthenticatedV7PairForestAsf8AccountsV1 {
    pub verifier_program: [u8; 32],
    pub pool_program: [u8; 32],
    pub verifier_profile: [u8; 32],
    pub verifier_release: [u8; 32],
    pub master_account: [u8; 32],
    pub checkpoint_account: [u8; 32],
    pub selected_lane_account: [u8; 32],
    pub master: Box<PoolV1PairForestMasterV1>,
    pub checkpoint: Box<PoolV1PairForestCheckpointV1>,
    pub selected_lane: Box<PoolV1PairForestLaneStateV1>,
    pub live_snapshot: Box<PoolV1PairLiveSnapshotV1>,
}

/// Result of the independently executed proof-account lifecycle and canonical
/// proof-wire scan. No cryptographic equation has been accepted at this seam.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ScannedV7PairForestAsf8ProofWireV1 {
    pub frontier_nodes: usize,
    pub proof_bytes: usize,
    pub candidate_afterstate: PoolV1PairVerifiedAfterstateV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValidatedV7PairForestAsf8V1 {
    pub statement: Box<PoolV1PairForestTerminalStatementV1>,
    pub accounts: AuthenticatedV7PairForestAsf8AccountsV1,
    pub proof_wire: ScannedV7PairForestAsf8ProofWireV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValidatedV7PairForestAsf8StreamingV1 {
    pub accounts: AuthenticatedV7PairForestAsf8AccountsV1,
    pub proof_wire: ScannedV7PairForestAsf8ProofWireV1,
}

fn frontier_nodes_from_staged_proof_length(length: usize) -> Option<usize> {
    let frontier_bytes = length.checked_sub(V7_STAGED_PAIR_BODY_WITHOUT_FRONTIERS)?;
    let both_tree_node_bytes = 2usize.checked_mul(26)?;
    if frontier_bytes % both_tree_node_bytes != 0 {
        return None;
    }
    let nodes = frontier_bytes / both_tree_node_bytes;
    (nodes >= aspis_statement::pool_v1::V7_POOL_NATIVE_TAG73_MIN_FRONTIER_NODES
        && nodes <= aspis_core::v7_onefold::V7_COMPACT_FRONTIER_CAP_PER_TREE)
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
fn decode_live_snapshot_box(bytes: &[u8]) -> Result<Box<PoolV1PairLiveSnapshotV1>, ProgramError> {
    Ok(Box::new(
        decode_pool_v1_pair_live_snapshot_v1(bytes)
            .map_err(|_| ProgramError::InvalidInstructionData)?,
    ))
}

#[inline(never)]
fn decode_afterstate_box(
    bytes: &[u8],
) -> Result<Box<PoolV1PairVerifiedAfterstateV1>, ProgramError> {
    Ok(Box::new(
        decode_pool_v1_pair_verified_afterstate_v1(bytes)
            .map_err(|_| ProgramError::InvalidInstructionData)?,
    ))
}

fn statement_public_identity(
    statement: &PoolV1PairForestTerminalStatementV1,
) -> (
    [u8; 32],
    [u8; 32],
    u64,
    aspis_statement::Digest,
    aspis_core::field::M31,
) {
    match statement {
        PoolV1PairForestTerminalStatementV1::PrivateTransfer { public, .. } => (
            public.pool,
            public.deployment_domain,
            public.anchor_sequence,
            public.anchor_root,
            public.asset_id,
        ),
        PoolV1PairForestTerminalStatementV1::Withdrawal { public, .. } => (
            public.pool,
            public.deployment_domain,
            public.anchor_sequence,
            public.anchor_root,
            public.asset_id,
        ),
    }
}

fn validate_asf8_late_header(bytes: &[u8]) -> ProgramResult {
    if bytes[..8] != POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC
        || bytes[8] != POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION
        || bytes[9] != POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT
        || u16::from_le_bytes(bytes[10..12].try_into().unwrap()) as usize
            != POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES
        || u32::from_le_bytes(bytes[12..16].try_into().unwrap()) as usize
            != POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
        || u32::from_le_bytes(bytes[16..20].try_into().unwrap()) as usize
            != POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
        || u32::from_le_bytes(bytes[20..24].try_into().unwrap()) as usize
            != POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES
        || bytes[24..32].iter().any(|byte| *byte != 0)
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    Ok(())
}

/// Stack-bounded SBF form of the full ASF8 profile. It validates the same
/// fixed layout in streaming components and never materializes the 1,880-byte
/// nested statement value on the 4 KiB SBF stack.
pub fn validate_v7_pair_forest_asf8_streaming_v1(
    verifier_program: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
) -> Result<ValidatedV7PairForestAsf8StreamingV1, ProgramError> {
    if instruction_data.len() != POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES
        || instruction_data[..4] != POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC
        || instruction_data[4] != POOL_V1_PAIR_FOREST_TERMINAL_VERSION
        || instruction_data[6] != POOL_V1_DIGEST_ENCODING_VERSION
        || ASF8_PAYMENT_OFFSET + POOL_V1_PAYMENT_STATEMENT_BYTES != instruction_data.len()
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    let authenticated = authenticate_v7_pair_forest_asf8_accounts_v1(verifier_program, accounts)?;
    if instruction_data[ASF8_MASTER_OFFSET..ASF8_CHECKPOINT_OFFSET] != authenticated.master_account
        || instruction_data[ASF8_CHECKPOINT_OFFSET..ASF8_LANE_OFFSET]
            != authenticated.checkpoint_account
        || instruction_data[ASF8_LANE_OFFSET..ASF8_CHECKPOINT_SEQUENCE_OFFSET]
            != authenticated.selected_lane_account
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    let checkpoint_sequence = u64::from_le_bytes(
        instruction_data[ASF8_CHECKPOINT_SEQUENCE_OFFSET..ASF8_ANCHOR_OFFSET]
            .try_into()
            .unwrap(),
    );
    let anchor = decode_digest_canonical(
        instruction_data[ASF8_ANCHOR_OFFSET..ASF8_LATE_OFFSET]
            .try_into()
            .unwrap(),
    )
    .map_err(|_| ProgramError::InvalidInstructionData)?;
    if checkpoint_sequence != authenticated.checkpoint.checkpoint_sequence
        || anchor != authenticated.checkpoint.global_root
    {
        return Err(ProgramError::InvalidInstructionData);
    }

    validate_asf8_late_header(
        &instruction_data
            [ASF8_LATE_OFFSET..ASF8_LATE_OFFSET + POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES],
    )?;
    let live_snapshot =
        decode_live_snapshot_box(&instruction_data[ASF8_LIVE_OFFSET..ASF8_CANDIDATE_OFFSET])?;
    let candidate =
        decode_afterstate_box(&instruction_data[ASF8_CANDIDATE_OFFSET..ASF8_PAYMENT_OFFSET])?;
    if *live_snapshot != *authenticated.live_snapshot
        || live_snapshot.next_pair_index.checked_add(1) != Some(candidate.next_pair_index)
    {
        return Err(ProgramError::InvalidInstructionData);
    }

    let payment = &instruction_data[ASF8_PAYMENT_OFFSET..];
    let nullifier = match instruction_data[5] {
        value if value == PoolV1TransitionKind::PrivateTransfer as u8 => {
            let public = decode_pool_v1_private_transfer_public_v1(payment)
                .map_err(|_| ProgramError::InvalidInstructionData)?;
            if public.pool != authenticated.master.identity.pool
                || public.deployment_domain != authenticated.master.identity.deployment_domain
                || public.anchor_sequence != authenticated.checkpoint.checkpoint_sequence
                || public.anchor_root != authenticated.checkpoint.global_root
                || public.asset_id != authenticated.master.identity.asset_id
            {
                return Err(ProgramError::InvalidInstructionData);
            }
            public.nullifier
        }
        value if value == PoolV1TransitionKind::Withdrawal as u8 => {
            let public = decode_pool_v1_withdrawal_public_v1(payment)
                .map_err(|_| ProgramError::InvalidInstructionData)?;
            if public.pool != authenticated.master.identity.pool
                || public.deployment_domain != authenticated.master.identity.deployment_domain
                || public.anchor_sequence != authenticated.checkpoint.checkpoint_sequence
                || public.anchor_root != authenticated.checkpoint.global_root
                || public.asset_id != authenticated.master.identity.asset_id
            {
                return Err(ProgramError::InvalidInstructionData);
            }
            public.nullifier
        }
        _ => return Err(ProgramError::InvalidInstructionData),
    };
    let output_lane = pool_v1_pair_forest_output_lane_v1(&nullifier)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    if instruction_data[7] != output_lane || output_lane != authenticated.selected_lane.lane_id {
        return Err(ProgramError::InvalidInstructionData);
    }

    let proof_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    let proof_wire =
        scan_v7_pair_forest_asf8_proof_wire_v1(proof_account, &authenticated.live_snapshot)?;
    if proof_wire.candidate_afterstate != *candidate {
        return Err(ProgramError::InvalidInstructionData);
    }
    Ok(ValidatedV7PairForestAsf8StreamingV1 {
        accounts: authenticated,
        proof_wire,
    })
}

/// Phase 1: canonical decoding of exactly one 1,880-byte ASF8 statement.
/// No account or proof data is consulted in this phase.
pub fn decode_v7_pair_forest_asf8_statement_v1(
    instruction_data: &[u8],
) -> Result<PoolV1PairForestTerminalStatementV1, ProgramError> {
    if instruction_data.len() != POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES {
        return Err(ProgramError::InvalidInstructionData);
    }
    decode_pool_v1_pair_forest_terminal_statement_v1(instruction_data)
        .map_err(|_| ProgramError::InvalidInstructionData)
}

/// Phase 2: authenticate the complete deployment and selected-lane state from
/// the four read-only accounts without consulting any ASF8 field.
///
/// The Pool program is not accepted from instruction bytes. It is derived
/// from the master owner, required to own checkpoint and lane as well, and
/// used for all three canonical PDA derivations. Profile and release are also
/// not instruction fields: invoking this function selects the compiled pair
/// profile constants below.
pub fn authenticate_v7_pair_forest_asf8_accounts_v1(
    verifier_program: &Pubkey,
    accounts: &[AccountInfo<'_>],
) -> Result<AuthenticatedV7PairForestAsf8AccountsV1, ProgramError> {
    let [proof_account, master_account, checkpoint_account, lane_account] = accounts else {
        return Err(if accounts.len() < 4 {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    };
    let pool_program = *master_account.owner;
    require_readonly_account(proof_account, verifier_program)?;
    require_readonly_account(master_account, &pool_program)?;
    require_readonly_account(checkpoint_account, &pool_program)?;
    require_readonly_account(lane_account, &pool_program)?;
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
            &pool_program,
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
            &pool_program,
        )
        .0 != *checkpoint_account.key
    {
        return Err(ProgramError::InvalidAccountData);
    }

    let selected_lane = decode_lane_box(&lane_account.try_borrow_data()?)?;
    let output_lane = selected_lane.lane_id;
    if selected_lane.master != master_account.key.to_bytes()
        || selected_lane.lane_id != output_lane
        || Pubkey::find_program_address(
            &[
                PAIR_FOREST_LANE_SEED,
                master_account.key.as_ref(),
                &[output_lane],
            ],
            &pool_program,
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
    Ok(AuthenticatedV7PairForestAsf8AccountsV1 {
        verifier_program: verifier_program.to_bytes(),
        pool_program: pool_program.to_bytes(),
        verifier_profile: V7_STAGED_PAIR_PROFILE_BINDING,
        verifier_release: V7_STAGED_PAIR_RELEASE_BINDING,
        master_account: master_account.key.to_bytes(),
        checkpoint_account: checkpoint_account.key.to_bytes(),
        selected_lane_account: lane_account.key.to_bytes(),
        master,
        checkpoint,
        selected_lane,
        live_snapshot,
    })
}

/// Phase 3: compare every ASF8 field that is determined by authenticated
/// account state. Keeping this separate proves the decoder never lends trust
/// to caller bytes during PDA/owner/account authentication.
pub fn compare_v7_pair_forest_asf8_to_authenticated_accounts_v1(
    statement: &PoolV1PairForestTerminalStatementV1,
    authenticated: &AuthenticatedV7PairForestAsf8AccountsV1,
) -> ProgramResult {
    let common = statement.common();
    let output_lane = pool_v1_pair_forest_output_lane_v1(statement.nullifier())
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let (public_pool, public_deployment, public_anchor_sequence, public_anchor, public_asset) =
        statement_public_identity(statement);
    if common.master_account != authenticated.master_account
        || common.checkpoint_account != authenticated.checkpoint_account
        || common.selected_lane_account != authenticated.selected_lane_account
        || common.output_lane != output_lane
        || common.output_lane != authenticated.selected_lane.lane_id
        || common.checkpoint_sequence != authenticated.checkpoint.checkpoint_sequence
        || common.historical_global_anchor != authenticated.checkpoint.global_root
        || common.lane_transition.live_snapshot != *authenticated.live_snapshot
        || public_pool != authenticated.master.identity.pool
        || public_deployment != authenticated.master.identity.deployment_domain
        || public_anchor_sequence != authenticated.checkpoint.checkpoint_sequence
        || public_anchor != authenticated.checkpoint.global_root
        || public_asset != authenticated.master.identity.asset_id
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    Ok(())
}

/// Phase 4: validate the proof-account lifecycle framing and scan the complete
/// staged proof grammar canonically. This phase uses only the already-derived
/// live snapshot and returns the proof-carried candidate for a later equality
/// check; it does not accept any cryptographic equation.
pub fn scan_v7_pair_forest_asf8_proof_wire_v1(
    proof_account: &AccountInfo<'_>,
    account_derived_live_snapshot: &PoolV1PairLiveSnapshotV1,
) -> Result<ScannedV7PairForestAsf8ProofWireV1, ProgramError> {
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
    let proof_bytes = payload.len() - POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;
    let frontier_nodes = frontier_nodes_from_staged_proof_length(proof_bytes)
        .ok_or(ProgramError::InvalidAccountData)?;
    let mut live_snapshot_bytes = [0u8; POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES];
    encode_pool_v1_pair_live_snapshot_v1(account_derived_live_snapshot, &mut live_snapshot_bytes)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let parsed = parse_v7_staged_pair_inputs_v1(payload, frontier_nodes, &live_snapshot_bytes)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    Ok(ScannedV7PairForestAsf8ProofWireV1 {
        frontier_nodes,
        proof_bytes,
        candidate_afterstate: parsed.late_statement.candidate_afterstate,
    })
}

/// Compose the three independently attributable ASF8 phases and require the
/// proof-carried ASJA candidate to equal the instruction's canonical candidate
/// exactly. This is transport authentication only, never proof acceptance.
pub fn validate_v7_pair_forest_asf8_request_v1(
    verifier_program: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
) -> Result<ValidatedV7PairForestAsf8V1, ProgramError> {
    let statement = decode_v7_pair_forest_asf8_statement_v1(instruction_data)?;
    let authenticated = authenticate_v7_pair_forest_asf8_accounts_v1(verifier_program, accounts)?;
    compare_v7_pair_forest_asf8_to_authenticated_accounts_v1(&statement, &authenticated)?;
    let proof_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    let proof_wire =
        scan_v7_pair_forest_asf8_proof_wire_v1(proof_account, &authenticated.live_snapshot)?;
    if proof_wire.candidate_afterstate != statement.common().lane_transition.candidate_afterstate {
        return Err(ProgramError::InvalidInstructionData);
    }
    Ok(ValidatedV7PairForestAsf8V1 {
        statement: Box::new(statement),
        accounts: authenticated,
        proof_wire,
    })
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
    if request.verifier_profile != V7_STAGED_PAIR_PROFILE_BINDING
        || request.verifier_release != V7_STAGED_PAIR_RELEASE_BINDING
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    let [proof_account, master_account, checkpoint_account, lane_account] = accounts else {
        return Err(if accounts.len() < 4 {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    };
    let pool_program = Pubkey::new_from_array(request.pool_program);
    require_readonly_account(proof_account, verifier_program)?;
    require_readonly_account(master_account, &pool_program)?;
    require_readonly_account(checkpoint_account, &pool_program)?;
    require_readonly_account(lane_account, &pool_program)?;
    require_distinct_accounts(&[
        proof_account,
        master_account,
        checkpoint_account,
        lane_account,
    ])?;

    let master = decode_pool_v1_pair_forest_master_v1(&master_account.try_borrow_data()?)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    if master.identity.pool != master_account.key.to_bytes()
        || master.initialized_lane_mask != POOL_V1_PAIR_FOREST_ALL_LANES_MASK
        || Pubkey::find_program_address(
            &[
                PAIR_FOREST_MASTER_SEED,
                Pubkey::new_from_array(master.identity.asset_mint).as_ref(),
            ],
            &pool_program,
        )
        .0 != *master_account.key
    {
        return Err(ProgramError::InvalidAccountData);
    }

    let checkpoint =
        decode_pool_v1_pair_forest_checkpoint_v1(&checkpoint_account.try_borrow_data()?)
            .map_err(|_| ProgramError::InvalidAccountData)?;
    if checkpoint.master != master_account.key.to_bytes()
        || checkpoint.deployment_domain != master.identity.deployment_domain
        || Pubkey::find_program_address(
            &[
                PAIR_FOREST_CHECKPOINT_SEED,
                master_account.key.as_ref(),
                &checkpoint.checkpoint_sequence.to_le_bytes(),
            ],
            &pool_program,
        )
        .0 != *checkpoint_account.key
    {
        return Err(ProgramError::InvalidAccountData);
    }

    let output_lane = pool_v1_pair_forest_output_lane_v1(request.public.nullifier())
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let selected_lane = decode_pool_v1_pair_forest_lane_state_v1(
        &lane_account.try_borrow_data()?,
        &V7_PAIR_EMPTY_ROOTS,
    )
    .map_err(|_| ProgramError::InvalidAccountData)?;
    if selected_lane.master != master_account.key.to_bytes()
        || selected_lane.lane_id != output_lane
        || Pubkey::find_program_address(
            &[
                PAIR_FOREST_LANE_SEED,
                master_account.key.as_ref(),
                &[output_lane],
            ],
            &pool_program,
        )
        .0 != *lane_account.key
    {
        return Err(ProgramError::InvalidAccountData);
    }

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
    let proof_length = payload.len() - POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;
    let frontier_nodes = frontier_nodes_from_staged_proof_length(proof_length)
        .ok_or(ProgramError::InvalidAccountData)?;
    let live_snapshot = PoolV1PairLiveSnapshotV1 {
        pool: master_account.key.to_bytes(),
        deployment_domain: master.identity.deployment_domain,
        sequence: selected_lane.tree.next_leaf_index,
        next_pair_index: selected_lane.tree.next_leaf_index,
        current_root: selected_lane.tree.root,
        frontier: selected_lane.tree.frontier,
    };
    let mut live_snapshot_bytes = [0u8; POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES];
    encode_pool_v1_pair_live_snapshot_v1(&live_snapshot, &mut live_snapshot_bytes)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let parsed = parse_v7_staged_pair_inputs_v1(payload, frontier_nodes, &live_snapshot_bytes)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let common = PoolV1PairForestTerminalCommonV1 {
        master_account: master_account.key.to_bytes(),
        checkpoint_account: checkpoint_account.key.to_bytes(),
        selected_lane_account: lane_account.key.to_bytes(),
        output_lane,
        checkpoint_sequence: checkpoint.checkpoint_sequence,
        historical_global_anchor: checkpoint.global_root,
        lane_transition: PoolV1PairLatePublicStatementV1 {
            live_snapshot,
            candidate_afterstate: parsed.late_statement.candidate_afterstate,
        },
    };
    let statement = reconstruct_pool_v1_pair_forest_terminal_statement_v1(&request, common)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    if master.identity.asset_id
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
    Ok(ValidatedV7PairForestAsq8V1 {
        request,
        master,
        checkpoint,
        selected_lane,
        statement: Box::new(statement),
        frontier_nodes,
    })
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
    let _validated =
        validate_v7_pair_forest_asq8_request_v1(verifier_program, accounts, instruction_data)?;
    Err(ProgramError::Custom(
        V7_PAIR_FOREST_ASQ8_CRYPTO_NOT_INTEGRATED,
    ))
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

fn process_asf8_with_clear_return_data<F>(
    verifier_program: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
    clear_return_data: F,
) -> ProgramResult
where
    F: FnOnce(),
{
    clear_return_data();
    let _validated =
        validate_v7_pair_forest_asf8_streaming_v1(verifier_program, accounts, instruction_data)?;
    Err(ProgramError::Custom(
        V7_PAIR_FOREST_ASF8_CRYPTO_NOT_INTEGRATED,
    ))
}

/// Default-off component entry. It is intentionally absent from the
/// production dispatcher and therefore cannot be reached by any deployed wire
/// tag. Focused host/SBF component tests call it directly.
pub fn process_v7_pair_forest_asf8_instruction(
    verifier_program: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
) -> ProgramResult {
    process_asf8_with_clear_return_data(verifier_program, accounts, instruction_data, || {
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
        encode_pool_v1_pair_forest_terminal_statement_v1,
        encode_pool_v1_pair_verified_afterstate_v1, IncrementalMerkleTreeV1, PoolIdentityV1,
        PoolV1PairForestTerminalPaymentV1, PoolV1PairVerifiedAfterstateV1,
        PoolV1PrivateTransferPublicV1, VerifierPolicyV1,
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
            verifier_profile: V7_STAGED_PAIR_PROFILE_BINDING,
            verifier_release: V7_STAGED_PAIR_RELEASE_BINDING,
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
        let proof_len = V7_STAGED_PAIR_BODY_WITHOUT_FRONTIERS + 2 * 26 * frontier_nodes;
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

    fn asf8_for_fixture(fixture: &mut Fixture) -> Vec<u8> {
        let statement = validate_fixture(fixture).unwrap().statement;
        encode_pool_v1_pair_forest_terminal_statement_v1(&statement)
            .unwrap()
            .to_vec()
    }

    fn validate_asf8_fixture(
        fixture: &mut Fixture,
        statement: &[u8],
    ) -> Result<ValidatedV7PairForestAsf8V1, ProgramError> {
        let verifier = fixture.verifier;
        with_fixture_accounts(fixture, |accounts| {
            validate_v7_pair_forest_asf8_request_v1(&verifier, accounts, statement)
        })
    }

    fn validate_asf8_streaming_fixture(
        fixture: &mut Fixture,
        statement: &[u8],
    ) -> Result<ValidatedV7PairForestAsf8StreamingV1, ProgramError> {
        let verifier = fixture.verifier;
        with_fixture_accounts(fixture, |accounts| {
            validate_v7_pair_forest_asf8_streaming_v1(&verifier, accounts, statement)
        })
    }

    fn resize_fixture_proof_frontier(fixture: &mut Fixture, frontier_nodes: usize) {
        let candidate = fixture.proof_data[crate::PROOF_ACCOUNT_HEADER_LEN
            ..crate::PROOF_ACCOUNT_HEADER_LEN + POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES]
            .to_vec();
        let proof_len = V7_STAGED_PAIR_BODY_WITHOUT_FRONTIERS + 2 * 26 * frontier_nodes;
        let payload_len = POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES + proof_len;
        fixture.proof_data = vec![0u8; crate::PROOF_ACCOUNT_HEADER_LEN + payload_len];
        fixture.proof_data[..4].copy_from_slice(b"ASPU");
        fixture.proof_data[4..8].copy_from_slice(&(payload_len as u32).to_le_bytes());
        fixture.proof_data[crate::PROOF_ACCOUNT_HEADER_LEN
            ..crate::PROOF_ACCOUNT_HEADER_LEN + POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES]
            .copy_from_slice(&candidate);
    }

    #[test]
    fn canonical_asq8_reconstructs_exact_asf8_but_cannot_emit_asr8() {
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
        assert_eq!(
            result,
            Err(ProgramError::Custom(
                V7_PAIR_FOREST_ASQ8_CRYPTO_NOT_INTEGRATED
            ))
        );
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

    #[test]
    fn canonical_asf8_authenticates_compiled_profile_accounts_and_proof_candidate() {
        let mut fixture = make_fixture();
        let asf8 = asf8_for_fixture(&mut fixture);
        assert_eq!(asf8.len(), POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES);
        let validated = validate_asf8_fixture(&mut fixture, &asf8).unwrap();
        assert_eq!(
            validated.accounts.verifier_profile,
            V7_STAGED_PAIR_PROFILE_BINDING
        );
        assert_eq!(
            validated.accounts.verifier_release,
            V7_STAGED_PAIR_RELEASE_BINDING
        );
        assert_eq!(
            validated.accounts.pool_program,
            fixture.master_owner.to_bytes()
        );
        assert_eq!(
            validated.proof_wire.candidate_afterstate,
            validated
                .statement
                .common()
                .lane_transition
                .candidate_afterstate
        );

        let verifier = fixture.verifier;
        let mut cleared = false;
        let result = with_fixture_accounts(&mut fixture, |accounts| {
            process_asf8_with_clear_return_data(&verifier, accounts, &asf8, || {
                cleared = true;
            })
        });
        assert!(cleared);
        assert_eq!(
            result,
            Err(ProgramError::Custom(
                V7_PAIR_FOREST_ASF8_CRYPTO_NOT_INTEGRATED
            ))
        );
    }

    #[test]
    fn asf8_phases_are_separate_and_compose_to_the_same_canonical_statement() {
        let mut fixture = make_fixture();
        let asf8 = asf8_for_fixture(&mut fixture);
        let statement = decode_v7_pair_forest_asf8_statement_v1(&asf8).unwrap();
        let verifier = fixture.verifier;
        with_fixture_accounts(&mut fixture, |accounts| {
            let authenticated =
                authenticate_v7_pair_forest_asf8_accounts_v1(&verifier, accounts).unwrap();
            compare_v7_pair_forest_asf8_to_authenticated_accounts_v1(&statement, &authenticated)
                .unwrap();
            let scanned =
                scan_v7_pair_forest_asf8_proof_wire_v1(&accounts[0], &authenticated.live_snapshot)
                    .unwrap();
            assert_eq!(
                scanned.candidate_afterstate,
                statement.common().lane_transition.candidate_afterstate
            );
            assert_eq!(
                scanned.frontier_nodes,
                aspis_statement::pool_v1::V7_POOL_NATIVE_TAG73_MIN_FRONTIER_NODES
            );
        });
    }

    #[test]
    fn asf8_rejects_statement_account_deployment_and_candidate_mismatches() {
        // Each offset is a distinct account-derived binding in canonical ASF8:
        // master, checkpoint, lane, checkpoint sequence, historical root,
        // live snapshot, proof-carried candidate, and payment master.
        for offset in [8usize, 40, 72, 104, 112, 144, 960, 1_672] {
            let mut fixture = make_fixture();
            let mut asf8 = asf8_for_fixture(&mut fixture);
            asf8[offset] ^= 1;
            assert!(
                validate_asf8_fixture(&mut fixture, &asf8).is_err(),
                "offset {offset}"
            );
            assert!(
                validate_asf8_streaming_fixture(&mut fixture, &asf8).is_err(),
                "streaming offset {offset}"
            );
        }

        let mut fixture = make_fixture();
        let mut asf8 = asf8_for_fixture(&mut fixture);
        asf8.push(0);
        assert!(validate_asf8_fixture(&mut fixture, &asf8).is_err());
        assert!(validate_asf8_streaming_fixture(&mut fixture, &asf8).is_err());

        // Changing the proof candidate without changing ASF8 is rejected by
        // the final cross-phase equality, even when the mutated digest limb is
        // still canonically encoded.
        let mut fixture = make_fixture();
        let asf8 = asf8_for_fixture(&mut fixture);
        fixture.proof_data[crate::PROOF_ACCOUNT_HEADER_LEN + 16] ^= 1;
        assert!(validate_asf8_fixture(&mut fixture, &asf8).is_err());
        assert!(validate_asf8_streaming_fixture(&mut fixture, &asf8).is_err());

        // A common counterfeit owner does not help: all three PDAs are
        // rederived under that owner and therefore fail closed.
        let mut fixture = make_fixture();
        let asf8 = asf8_for_fixture(&mut fixture);
        let counterfeit = Pubkey::new_unique();
        fixture.master_owner = counterfeit;
        fixture.checkpoint_owner = counterfeit;
        fixture.lane_owner = counterfeit;
        assert!(validate_asf8_fixture(&mut fixture, &asf8).is_err());
        assert!(validate_asf8_streaming_fixture(&mut fixture, &asf8).is_err());
    }

    /// Host-only component evidence. This is deliberately ignored during
    /// normal tests because wall-clock nanoseconds are not Solana CU. Run the
    /// exact filtered release test when refreshing the audit evidence.
    #[test]
    #[ignore = "manual focused host component measurement"]
    fn asf8_host_component_measurement_separates_all_three_phases() {
        use std::{hint::black_box, time::Instant};

        const ITERATIONS: u32 = 256;
        let mut fixture = make_fixture();
        resize_fixture_proof_frontier(
            &mut fixture,
            aspis_core::v7_onefold::V7_COMPACT_FRONTIER_CAP_PER_TREE,
        );
        let asf8 = asf8_for_fixture(&mut fixture);
        let statement = decode_v7_pair_forest_asf8_statement_v1(&asf8).unwrap();
        let verifier = fixture.verifier;
        let asq8 = fixture.request.clone();
        let state_bytes =
            fixture.master_data.len() + fixture.checkpoint_data.len() + fixture.lane_data.len();
        with_fixture_accounts(&mut fixture, |accounts| {
            let authenticated =
                authenticate_v7_pair_forest_asf8_accounts_v1(&verifier, accounts).unwrap();
            let scanned =
                scan_v7_pair_forest_asf8_proof_wire_v1(&accounts[0], &authenticated.live_snapshot)
                    .unwrap();

            let start = Instant::now();
            for _ in 0..ITERATIONS {
                black_box(decode_v7_pair_forest_asf8_statement_v1(black_box(&asf8)).unwrap());
            }
            let parse_ns = start.elapsed().as_nanos() / u128::from(ITERATIONS);

            let start = Instant::now();
            for _ in 0..ITERATIONS {
                black_box(
                    authenticate_v7_pair_forest_asf8_accounts_v1(&verifier, accounts).unwrap(),
                );
            }
            let account_ns = start.elapsed().as_nanos() / u128::from(ITERATIONS);

            let start = Instant::now();
            for _ in 0..ITERATIONS {
                black_box(
                    compare_v7_pair_forest_asf8_to_authenticated_accounts_v1(
                        black_box(&statement),
                        black_box(&authenticated),
                    )
                    .unwrap(),
                );
            }
            let statement_compare_ns = start.elapsed().as_nanos() / u128::from(ITERATIONS);

            let start = Instant::now();
            for _ in 0..ITERATIONS {
                black_box(
                    scan_v7_pair_forest_asf8_proof_wire_v1(
                        &accounts[0],
                        black_box(&authenticated.live_snapshot),
                    )
                    .unwrap(),
                );
            }
            let proof_scan_ns = start.elapsed().as_nanos() / u128::from(ITERATIONS);

            let start = Instant::now();
            for _ in 0..ITERATIONS {
                black_box(
                    validate_v7_pair_forest_asf8_request_v1(&verifier, accounts, black_box(&asf8))
                        .unwrap(),
                );
            }
            let full_asf8_ns = start.elapsed().as_nanos() / u128::from(ITERATIONS);

            let start = Instant::now();
            for _ in 0..ITERATIONS {
                black_box(
                    validate_v7_pair_forest_asq8_request_v1(&verifier, accounts, black_box(&asq8))
                        .unwrap(),
                );
            }
            let full_asq8_ns = start.elapsed().as_nanos() / u128::from(ITERATIONS);

            println!(
                "ASF8_HOST_COMPONENT iterations={ITERATIONS} asf8_bytes={} state_bytes={} proof_bytes={} parse_ns={parse_ns} account_auth_ns={account_ns} statement_compare_ns={statement_compare_ns} proof_scan_ns={proof_scan_ns} full_asf8_ns={full_asf8_ns} full_asq8_ns={full_asq8_ns}",
                asf8.len(), state_bytes, scanned.proof_bytes
            );
        });
    }
}
