//! Production-inactive Solana account plumbing for the eight-lane pair forest.
//!
//! This module is compiled only under the explicit
//! `pair-forest-account-evidence` feature. It defines exact initialization and
//! permissionless checkpoint instructions plus a vault-backed deterministic
//! lane deposit and a compact one-terminal spend caller. The spend caller is
//! still inactive by default and requires a separately reviewed selected
//! verifier ASQ8 handler. The checkpoint reads all eight lane PDAs in one
//! invocation and computes the seven frozen Pool Poseidon parents internally.

extern crate alloc;

use alloc::{boxed::Box, vec::Vec};

use aspis_statement::{
    pool_v1::{
        decode_pool_v1_pair_forest_checkpoint_v1, decode_pool_v1_pair_forest_lane_state_v1,
        decode_pool_v1_pair_forest_master_v1, decode_pool_v1_pair_forest_terminal_request_v1,
        encode_pool_v1_pair_forest_checkpoint_v1, encode_pool_v1_pair_forest_lane_state_v1,
        encode_pool_v1_pair_forest_master_v1, encode_pool_v1_pair_forest_terminal_result_v1,
        plan_pool_v1_pair_forest_checkpoint_v1, pool_v1_note_commitment,
        pool_v1_pair_forest_deposit_lane_v1, pool_v1_tree_parent,
        reconstruct_pool_v1_pair_forest_terminal_statement_v1, root_history_location,
        validate_pool_v1_pair_forest_terminal_result_against_statement_v1, IncrementalMerkleTreeV1,
        PoolIdentityV1, PoolV1NullifierMarkerV1, PoolV1PairForestCheckpointV1,
        PoolV1PairForestLaneStateV1, PoolV1PairForestMasterV1, PoolV1PairForestTerminalCommonV1,
        PoolV1PairForestTerminalPaymentV1, PoolV1PairForestTerminalRequestV1,
        PoolV1PairLeafWitnessV1, POOL_V1_DIGEST_ENCODING_VERSION, POOL_V1_PAIR_CAPACITY,
        POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES, POOL_V1_PAIR_FOREST_LANE_COUNT,
        POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES, POOL_V1_PAIR_TREE_DEPTH,
        POOL_V1_ROOT_HISTORY_CAPACITY, POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
        POOL_V1_ROOT_HISTORY_PAGE_SEED,
    },
    poseidon2::Digest,
};
use solana_program::{
    account_info::AccountInfo, entrypoint::ProgramResult, program_error::ProgramError,
    pubkey::Pubkey, rent::Rent,
};

use crate::{
    deposit::DepositRequestV1,
    deposit_transport::{
        decode_deposit_instruction_with_magic_v1, encode_deposit_instruction_v1,
        DepositInstructionFormatErrorV1,
    },
    empty_roots::POOL_V1_PAIR_EMPTY_ROOTS,
    error::PoolV1ProgramError,
    history::{
        append_roots_unchecked, pool_v1_root_page_address, read_retained_root,
        require_program_account, validate_root_page_bytes, write_new_page_unchecked,
        RootPageHeaderV1,
    },
    instruction::{
        decode_initialize_instruction_v1, encode_initialize_instruction_v1,
        PoolInstructionFormatErrorV1, POOL_V1_INITIALIZE_INSTRUCTION_BYTES,
        POOL_V1_INITIALIZE_INSTRUCTION_MAGIC, POOL_V1_INSTRUCTION_VERSION,
    },
    nullifier::{plan_nullifier_marker_consumption_v1, NullifierMarkerPreparationV1},
    pair_forest_dispatch::{
        dispatch_pair_forest_terminal_readonly_v1, AuthenticatedPairForestResultV1,
    },
    processor::{
        create_or_allocate_pda, initialize_vault_account, plan_fresh_program_pda,
        plan_vault_initialization, require_payer_and_system_program, require_token_program_account,
        require_unique_accounts, FreshPdaPreparationV1, PoolCpiRuntimeV1,
    },
    state::PoolInitializationV1,
    vault::{
        exact_transfer_account_infos_v1, exact_withdrawal_transfer_account_infos_v1,
        parse_legacy_mint_v1, plan_legacy_deposit_transfer_from_identity_v1,
        plan_legacy_withdrawal_transfer_from_identity_v1, validate_exact_deposit_delta_v1,
        validate_exact_withdrawal_delta_v1, LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES,
        LEGACY_SPL_TOKEN_PROGRAM_ID, POOL_V1_VAULT_AUTHORITY_SEED,
    },
};

pub const POOL_V1_PAIR_FOREST_MASTER_SEED: &[u8] = b"aspis-pair-forest-master-v1";
pub const POOL_V1_PAIR_FOREST_LANE_SEED: &[u8] = b"aspis-pair-forest-lane-v1";
pub const POOL_V1_PAIR_FOREST_CHECKPOINT_SEED: &[u8] = b"aspis-pair-forest-checkpoint-v1";

pub const POOL_V1_PAIR_FOREST_INITIALIZE_INSTRUCTION_MAGIC: [u8; 4] = *b"AS8I";
pub const POOL_V1_PAIR_FOREST_CHECKPOINT_INSTRUCTION_MAGIC: [u8; 4] = *b"AS8C";
pub const POOL_V1_PAIR_FOREST_DEPOSIT_INSTRUCTION_MAGIC: [u8; 4] = *b"AS8D";
pub const POOL_V1_PAIR_FOREST_CHECKPOINT_INSTRUCTION_BYTES: usize = 8;
pub const POOL_V1_PAIR_FOREST_INITIALIZE_ACCOUNT_COUNT: usize = 14;
pub const POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_COUNT: usize = 12;

const FOREST_MASTER_ACCOUNT_INDEX: usize = 0;
const FOREST_FIRST_LANE_ACCOUNT_INDEX: usize = 1;
const FOREST_MINT_OR_CHECKPOINT_ACCOUNT_INDEX: usize = 9;
const FOREST_INIT_VAULT_ACCOUNT_INDEX: usize = 10;
const FOREST_INIT_TOKEN_PROGRAM_ACCOUNT_INDEX: usize = 11;
const FOREST_INIT_PAYER_ACCOUNT_INDEX: usize = 12;
const FOREST_INIT_SYSTEM_ACCOUNT_INDEX: usize = 13;
const FOREST_CHECKPOINT_PAYER_ACCOUNT_INDEX: usize = 10;
const FOREST_CHECKPOINT_SYSTEM_ACCOUNT_INDEX: usize = 11;

const FOREST_DEPOSIT_MASTER_ACCOUNT_INDEX: usize = 0;
const FOREST_DEPOSIT_LANE_ACCOUNT_INDEX: usize = 1;
const FOREST_DEPOSIT_CURRENT_PAGE_ACCOUNT_INDEX: usize = 2;
const FOREST_DEPOSIT_SAME_PAGE_ACCOUNT_COUNT: usize = 8;
const FOREST_DEPOSIT_GENESIS_PAGE_ACCOUNT_COUNT: usize = 10;
const FOREST_DEPOSIT_ROLLOVER_ACCOUNT_COUNT: usize = 11;

pub fn encode_pair_forest_initialize_instruction_v1(
    initialization: &PoolInitializationV1,
) -> Result<[u8; POOL_V1_INITIALIZE_INSTRUCTION_BYTES], PoolInstructionFormatErrorV1> {
    let mut encoded = encode_initialize_instruction_v1(initialization)?;
    encoded[..4].copy_from_slice(&POOL_V1_PAIR_FOREST_INITIALIZE_INSTRUCTION_MAGIC);
    encoded[5] = POOL_V1_PAIR_FOREST_LANE_COUNT as u8;
    encoded[6] = POOL_V1_DIGEST_ENCODING_VERSION;
    Ok(encoded)
}

pub fn decode_pair_forest_initialize_instruction_v1(
    bytes: &[u8],
) -> Result<PoolInitializationV1, PoolInstructionFormatErrorV1> {
    if bytes.len() != POOL_V1_INITIALIZE_INSTRUCTION_BYTES {
        return Err(PoolInstructionFormatErrorV1::WrongLength);
    }
    if bytes[..4] != POOL_V1_PAIR_FOREST_INITIALIZE_INSTRUCTION_MAGIC {
        return Err(PoolInstructionFormatErrorV1::WrongMagic);
    }
    if bytes[4] != POOL_V1_INSTRUCTION_VERSION {
        return Err(PoolInstructionFormatErrorV1::WrongVersion);
    }
    if bytes[5] != POOL_V1_PAIR_FOREST_LANE_COUNT as u8
        || bytes[6] != POOL_V1_DIGEST_ENCODING_VERSION
    {
        return Err(PoolInstructionFormatErrorV1::NonCanonicalField);
    }
    if bytes[7] != 0 {
        return Err(PoolInstructionFormatErrorV1::NonZeroReserved);
    }
    let mut legacy = [0u8; POOL_V1_INITIALIZE_INSTRUCTION_BYTES];
    legacy.copy_from_slice(bytes);
    legacy[..4].copy_from_slice(&POOL_V1_INITIALIZE_INSTRUCTION_MAGIC);
    legacy[5..8].fill(0);
    decode_initialize_instruction_v1(&legacy)
}

pub fn encode_pair_forest_checkpoint_instruction_v1(
) -> [u8; POOL_V1_PAIR_FOREST_CHECKPOINT_INSTRUCTION_BYTES] {
    [
        POOL_V1_PAIR_FOREST_CHECKPOINT_INSTRUCTION_MAGIC[0],
        POOL_V1_PAIR_FOREST_CHECKPOINT_INSTRUCTION_MAGIC[1],
        POOL_V1_PAIR_FOREST_CHECKPOINT_INSTRUCTION_MAGIC[2],
        POOL_V1_PAIR_FOREST_CHECKPOINT_INSTRUCTION_MAGIC[3],
        POOL_V1_INSTRUCTION_VERSION,
        POOL_V1_PAIR_FOREST_LANE_COUNT as u8,
        POOL_V1_DIGEST_ENCODING_VERSION,
        0,
    ]
}

pub fn decode_pair_forest_checkpoint_instruction_v1(bytes: &[u8]) -> ProgramResult {
    if bytes != encode_pair_forest_checkpoint_instruction_v1() {
        return Err(ProgramError::InvalidInstructionData);
    }
    Ok(())
}

pub fn encode_pair_forest_deposit_instruction_v1(
    request: &DepositRequestV1<'_>,
) -> Result<Vec<u8>, DepositInstructionFormatErrorV1> {
    let mut encoded = encode_deposit_instruction_v1(request)?.as_bytes().to_vec();
    encoded[..4].copy_from_slice(&POOL_V1_PAIR_FOREST_DEPOSIT_INSTRUCTION_MAGIC);
    Ok(encoded)
}

pub fn decode_pair_forest_deposit_instruction_v1(
    bytes: &[u8],
) -> Result<DepositRequestV1<'_>, DepositInstructionFormatErrorV1> {
    decode_deposit_instruction_with_magic_v1(bytes, POOL_V1_PAIR_FOREST_DEPOSIT_INSTRUCTION_MAGIC)
}

/// Exact frozen binary tree over lanes 0 through 7. The order is part of the
/// checkpoint ABI and uses the existing Pool parent primitive seven times.
pub fn pool_v1_pair_forest_global_root_v1(
    lane_roots: &[Digest; POOL_V1_PAIR_FOREST_LANE_COUNT],
) -> Digest {
    let level_one = [
        pool_v1_tree_parent(&lane_roots[0], &lane_roots[1]),
        pool_v1_tree_parent(&lane_roots[2], &lane_roots[3]),
        pool_v1_tree_parent(&lane_roots[4], &lane_roots[5]),
        pool_v1_tree_parent(&lane_roots[6], &lane_roots[7]),
    ];
    let level_two = [
        pool_v1_tree_parent(&level_one[0], &level_one[1]),
        pool_v1_tree_parent(&level_one[2], &level_one[3]),
    ];
    pool_v1_tree_parent(&level_two[0], &level_two[1])
}

pub fn pool_v1_pair_forest_master_address(
    program_id: &Pubkey,
    asset_mint: &Pubkey,
) -> (Pubkey, u8) {
    Pubkey::find_program_address(
        &[POOL_V1_PAIR_FOREST_MASTER_SEED, asset_mint.as_ref()],
        program_id,
    )
}

pub fn pool_v1_pair_forest_lane_address(
    program_id: &Pubkey,
    master: &Pubkey,
    lane_id: u8,
) -> Result<(Pubkey, u8), ProgramError> {
    if usize::from(lane_id) >= POOL_V1_PAIR_FOREST_LANE_COUNT {
        return Err(ProgramError::InvalidSeeds);
    }
    Ok(Pubkey::find_program_address(
        &[POOL_V1_PAIR_FOREST_LANE_SEED, master.as_ref(), &[lane_id]],
        program_id,
    ))
}

pub fn pool_v1_pair_forest_checkpoint_address(
    program_id: &Pubkey,
    master: &Pubkey,
    checkpoint_sequence: u64,
) -> (Pubkey, u8) {
    Pubkey::find_program_address(
        &[
            POOL_V1_PAIR_FOREST_CHECKPOINT_SEED,
            master.as_ref(),
            &checkpoint_sequence.to_le_bytes(),
        ],
        program_id,
    )
}

/// Lane-local root-history identity. Existing root-page bytes remain unchanged:
/// their `pool` field is the canonical lane-state PDA, not the forest master.
pub fn pool_v1_pair_forest_lane_root_page_address(
    program_id: &Pubkey,
    master: &Pubkey,
    lane_id: u8,
    page_number: u64,
) -> Result<(Pubkey, u8), ProgramError> {
    let lane = pool_v1_pair_forest_lane_address(program_id, master, lane_id)?.0;
    Ok(pool_v1_root_page_address(program_id, &lane, page_number))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlannedPairForestCheckpointAccountsV1 {
    pub master: Pubkey,
    pub checkpoint: Pubkey,
    pub lane_sequences: [u64; POOL_V1_PAIR_FOREST_LANE_COUNT],
    pub next_master_image: [u8; POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES],
    pub checkpoint_image: [u8; POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES],
}

fn require_exact_account_count(accounts: &[AccountInfo<'_>], expected: usize) -> ProgramResult {
    if accounts.len() != expected {
        return Err(if accounts.len() < expected {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    }
    Ok(())
}

fn require_forest_mint_account(
    initialization: &PoolInitializationV1,
    mint: &AccountInfo<'_>,
) -> ProgramResult {
    if mint.key.to_bytes() != initialization.asset_mint
        || initialization.token_program != LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes()
        || mint.owner != &LEGACY_SPL_TOKEN_PROGRAM_ID
        || mint.executable
        || mint.is_signer
        || mint.is_writable
        || mint.data_len() != LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES
    {
        return Err(PoolV1ProgramError::InvalidMint.into());
    }
    parse_legacy_mint_v1(&mint.try_borrow_data()?)?;
    Ok(())
}

fn require_program_owned_zeroed(
    account: &AccountInfo<'_>,
    program_id: &Pubkey,
    exact_bytes: usize,
    rent: &Rent,
) -> ProgramResult {
    require_program_account(account, program_id, true)?;
    let data = account.try_borrow_data()?;
    if data.len() != exact_bytes
        || data.iter().any(|byte| *byte != 0)
        || !rent.is_exempt(account.lamports(), exact_bytes)
    {
        return Err(PoolV1ProgramError::InvalidFreshAccount.into());
    }
    Ok(())
}

fn genesis_lane_state(master: &Pubkey, lane_id: u8) -> PoolV1PairForestLaneStateV1 {
    PoolV1PairForestLaneStateV1 {
        master: master.to_bytes(),
        lane_id,
        tree: IncrementalMerkleTreeV1 {
            next_leaf_index: 0,
            root: POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH],
            frontier: core::array::from_fn(|level| POOL_V1_PAIR_EMPTY_ROOTS[level]),
        },
    }
}

fn decode_master_account(
    program_id: &Pubkey,
    account: &AccountInfo<'_>,
    writable: bool,
) -> Result<PoolV1PairForestMasterV1, ProgramError> {
    require_program_account(account, program_id, writable)?;
    if account.is_signer {
        return Err(ProgramError::InvalidAccountData);
    }
    let master = decode_pool_v1_pair_forest_master_v1(&account.try_borrow_data()?)
        .map_err(|_| PoolV1ProgramError::InvalidAccountType)?;
    let mint = Pubkey::new_from_array(master.identity.asset_mint);
    if account.key != &pool_v1_pair_forest_master_address(program_id, &mint).0
        || master.identity.pool != account.key.to_bytes()
    {
        return Err(PoolV1ProgramError::InvalidPoolStateAddress.into());
    }
    Ok(master)
}

fn decode_lane_account(
    program_id: &Pubkey,
    master: &Pubkey,
    expected_lane: u8,
    account: &AccountInfo<'_>,
    writable: bool,
) -> Result<PoolV1PairForestLaneStateV1, ProgramError> {
    require_program_account(account, program_id, writable)?;
    if account.is_signer
        || account.key != &pool_v1_pair_forest_lane_address(program_id, master, expected_lane)?.0
    {
        return Err(PoolV1ProgramError::InvalidPoolStateAddress.into());
    }
    let lane = decode_pool_v1_pair_forest_lane_state_v1(
        &account.try_borrow_data()?,
        &POOL_V1_PAIR_EMPTY_ROOTS,
    )
    .map_err(|_| PoolV1ProgramError::InvalidAccountType)?;
    if lane.master != master.to_bytes() || lane.lane_id != expected_lane {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    Ok(lane)
}

fn require_alias_free(
    master: &AccountInfo<'_>,
    lanes: &[AccountInfo<'_>],
    checkpoint: &AccountInfo<'_>,
) -> Result<(), ProgramError> {
    if master.key == checkpoint.key {
        return Err(ProgramError::InvalidArgument);
    }
    for (index, lane) in lanes.iter().enumerate() {
        if lane.key == master.key
            || lane.key == checkpoint.key
            || lanes[..index]
                .iter()
                .any(|previous| previous.key == lane.key)
        {
            return Err(ProgramError::InvalidArgument);
        }
    }
    Ok(())
}

/// Authenticate the exact fixed-order account snapshot and prepare, without
/// mutation, one master update plus one immutable checkpoint image.
pub fn plan_pair_forest_checkpoint_accounts_v1(
    program_id: &Pubkey,
    master_account: &AccountInfo<'_>,
    lane_accounts: &[AccountInfo<'_>],
    checkpoint_account: &AccountInfo<'_>,
) -> Result<PlannedPairForestCheckpointAccountsV1, ProgramError> {
    if lane_accounts.len() != POOL_V1_PAIR_FOREST_LANE_COUNT {
        return Err(if lane_accounts.len() < POOL_V1_PAIR_FOREST_LANE_COUNT {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    }
    require_alias_free(master_account, lane_accounts, checkpoint_account)?;
    let master = decode_master_account(program_id, master_account, true)?;
    let mut lane_states = Vec::with_capacity(POOL_V1_PAIR_FOREST_LANE_COUNT);
    for lane in 0..POOL_V1_PAIR_FOREST_LANE_COUNT {
        lane_states.push(decode_lane_account(
            program_id,
            master_account.key,
            lane as u8,
            &lane_accounts[lane],
            false,
        )?);
    }
    let lane_states: Box<[PoolV1PairForestLaneStateV1; POOL_V1_PAIR_FOREST_LANE_COUNT]> =
        lane_states
            .into_boxed_slice()
            .try_into()
            .map_err(|_| ProgramError::InvalidAccountData)?;
    let lane_roots = lane_states.each_ref().map(|lane| lane.tree.root);
    let global_root = pool_v1_pair_forest_global_root_v1(&lane_roots);
    let pure = plan_pool_v1_pair_forest_checkpoint_v1(&master, &lane_states, global_root)
        .map_err(|_| PoolV1ProgramError::StateHistoryMismatch)?;
    let expected_checkpoint = pool_v1_pair_forest_checkpoint_address(
        program_id,
        master_account.key,
        pure.checkpoint.checkpoint_sequence,
    )
    .0;
    plan_fresh_program_pda(
        checkpoint_account,
        program_id,
        &expected_checkpoint,
        POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES,
    )?;
    let next_master_image = encode_pool_v1_pair_forest_master_v1(&pure.next_master)
        .map_err(|_| PoolV1ProgramError::StateHistoryMismatch)?;
    let checkpoint_image = encode_pool_v1_pair_forest_checkpoint_v1(&pure.checkpoint)
        .map_err(|_| PoolV1ProgramError::StateHistoryMismatch)?;
    Ok(PlannedPairForestCheckpointAccountsV1 {
        master: *master_account.key,
        checkpoint: expected_checkpoint,
        lane_sequences: pure.checkpoint.lane_sequences,
        next_master_image,
        checkpoint_image,
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PairForestDepositPageModeV1 {
    FreshGenesis {
        preparation: FreshPdaPreparationV1,
        bump: u8,
    },
    ExistingSamePage {
        header: RootPageHeaderV1,
    },
    FreshRollover {
        preparation: FreshPdaPreparationV1,
        next_page_number: u64,
        bump: u8,
    },
}

fn account_is_zeroed_program_page(
    account: &AccountInfo<'_>,
    program_id: &Pubkey,
) -> Result<bool, ProgramError> {
    if account.owner != program_id || account.data_len() != POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES
    {
        return Ok(false);
    }
    Ok(account.try_borrow_data()?.iter().all(|byte| *byte == 0))
}

fn validate_lane_current_page(
    program_id: &Pubkey,
    lane_account: &AccountInfo<'_>,
    page: &AccountInfo<'_>,
    lane: &PoolV1PairForestLaneStateV1,
    writable: bool,
) -> Result<RootPageHeaderV1, ProgramError> {
    let location = root_history_location(lane.tree.next_leaf_index);
    require_program_account(page, program_id, writable)?;
    if page.is_signer {
        return Err(ProgramError::InvalidAccountData);
    }
    crate::history::require_root_page_address(
        program_id,
        lane_account.key,
        location.page_number,
        page,
    )?;
    let data = page.try_borrow_data()?;
    let header = validate_root_page_bytes(&data, lane_account.key, location.page_number)?;
    if header.filled != location.slot + 1
        || read_retained_root(&data, header, lane.tree.next_leaf_index)? != lane.tree.root
    {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    Ok(header)
}

/// Apply one vault-backed public deposit to its deterministic pair-forest
/// lane. The first pair slot is the occupied note commitment and the second
/// slot is the relation's algebraic empty `(occupied = 0, commitment = 0)`.
///
/// Existing-page accounts are
/// `[master, lane, current_page, mint, source, authority, vault, token]`.
/// A fresh genesis page additionally appends `[payer, system]`. Rollover uses
/// `[master, lane, current_page, next_page, mint, source, authority, vault,
/// token, payer, system]`.
pub(crate) fn process_pair_forest_deposit_with_runtime_v1<'info, R: PoolCpiRuntimeV1>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'info>],
    instruction_data: &[u8],
    rent: &Rent,
    runtime: &mut R,
) -> ProgramResult {
    let request = decode_pair_forest_deposit_instruction_v1(instruction_data)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let master_account = accounts
        .get(FOREST_DEPOSIT_MASTER_ACCOUNT_INDEX)
        .ok_or(ProgramError::NotEnoughAccountKeys)?;
    let lane_account = accounts
        .get(FOREST_DEPOSIT_LANE_ACCOUNT_INDEX)
        .ok_or(ProgramError::NotEnoughAccountKeys)?;
    let current_page = accounts
        .get(FOREST_DEPOSIT_CURRENT_PAGE_ACCOUNT_INDEX)
        .ok_or(ProgramError::NotEnoughAccountKeys)?;
    let master = decode_master_account(program_id, master_account, false)?;
    let commitment = pool_v1_note_commitment(
        &request.owner_key,
        request.amount,
        master.identity.asset_id,
        &request.salt,
    );
    let lane_id = pool_v1_pair_forest_deposit_lane_v1(&commitment)
        .map_err(|_| PoolV1ProgramError::NonCanonicalLeaf)?;
    if master.initialized_lane_mask & (1u8 << lane_id) == 0 {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    let lane = decode_lane_account(program_id, master_account.key, lane_id, lane_account, true)?;
    if lane.tree.next_leaf_index >= POOL_V1_PAIR_CAPACITY {
        return Err(PoolV1ProgramError::TreeFull.into());
    }
    let pair_leaf = PoolV1PairLeafWitnessV1::single_output(commitment)
        .and_then(|witness| witness.leaf_digest())
        .map_err(|_| PoolV1ProgramError::NonCanonicalLeaf)?;
    let (next_tree, append) = lane
        .tree
        .append_one_with_empty_roots(pair_leaf, &POOL_V1_PAIR_EMPTY_ROOTS)
        .map_err(|_| PoolV1ProgramError::StateHistoryMismatch)?;
    let next_lane = PoolV1PairForestLaneStateV1 {
        master: lane.master,
        lane_id,
        tree: next_tree,
    };
    let next_lane_image =
        encode_pool_v1_pair_forest_lane_state_v1(&next_lane, &POOL_V1_PAIR_EMPTY_ROOTS)
            .map_err(|_| PoolV1ProgramError::StateHistoryMismatch)?;

    let current_location = root_history_location(lane.tree.next_leaf_index);
    let next_location = root_history_location(append.root_sequence);
    let fresh_genesis = lane.tree.next_leaf_index == 0
        && ((current_page.owner == &solana_sdk_ids::system_program::id()
            && current_page.data_is_empty())
            || account_is_zeroed_program_page(current_page, program_id)?);
    let (mode, token_start, expected_accounts) = if fresh_genesis {
        let (expected, bump) = pool_v1_root_page_address(program_id, lane_account.key, 0);
        let preparation = plan_fresh_program_pda(
            current_page,
            program_id,
            &expected,
            POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
        )?;
        (
            PairForestDepositPageModeV1::FreshGenesis { preparation, bump },
            3,
            FOREST_DEPOSIT_GENESIS_PAGE_ACCOUNT_COUNT,
        )
    } else if next_location.page_number == current_location.page_number {
        let header =
            validate_lane_current_page(program_id, lane_account, current_page, &lane, true)?;
        (
            PairForestDepositPageModeV1::ExistingSamePage { header },
            3,
            FOREST_DEPOSIT_SAME_PAGE_ACCOUNT_COUNT,
        )
    } else {
        let current_header =
            validate_lane_current_page(program_id, lane_account, current_page, &lane, false)?;
        if usize::from(current_header.filled) != POOL_V1_ROOT_HISTORY_CAPACITY {
            return Err(PoolV1ProgramError::StateHistoryMismatch.into());
        }
        let next_page = accounts.get(3).ok_or(ProgramError::NotEnoughAccountKeys)?;
        let (expected, bump) =
            pool_v1_root_page_address(program_id, lane_account.key, next_location.page_number);
        let preparation = plan_fresh_program_pda(
            next_page,
            program_id,
            &expected,
            POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
        )?;
        (
            PairForestDepositPageModeV1::FreshRollover {
                preparation,
                next_page_number: next_location.page_number,
                bump,
            },
            4,
            FOREST_DEPOSIT_ROLLOVER_ACCOUNT_COUNT,
        )
    };

    require_exact_account_count(accounts, expected_accounts)?;
    require_unique_accounts(accounts)?;
    let token_accounts = &accounts[token_start..token_start + 5];
    require_token_program_account(&token_accounts[4])?;
    let transfer_plan = plan_legacy_deposit_transfer_from_identity_v1(
        program_id,
        master_account.key,
        &master.identity,
        token_accounts,
        request.amount,
    )?;
    let transfer_infos = exact_transfer_account_infos_v1(token_accounts)?;

    let writable_page = match mode {
        PairForestDepositPageModeV1::FreshGenesis { preparation, bump } => {
            let payer = &accounts[8];
            let system_program = &accounts[9];
            require_payer_and_system_program(payer, system_program)?;
            if preparation == FreshPdaPreparationV1::CreateOrAllocateSystemOwned {
                let page_number = 0u64.to_le_bytes();
                let bump = [bump];
                let seeds: &[&[u8]] = &[
                    POOL_V1_ROOT_HISTORY_PAGE_SEED,
                    lane_account.key.as_ref(),
                    &page_number,
                    &bump,
                ];
                create_or_allocate_pda(
                    runtime,
                    payer,
                    current_page,
                    system_program,
                    POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
                    program_id,
                    seeds,
                )?;
            }
            require_program_owned_zeroed(
                current_page,
                program_id,
                POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
                rent,
            )?;
            current_page
        }
        PairForestDepositPageModeV1::ExistingSamePage { .. } => current_page,
        PairForestDepositPageModeV1::FreshRollover {
            preparation,
            next_page_number,
            bump,
            ..
        } => {
            let next_page = &accounts[3];
            let payer = &accounts[9];
            let system_program = &accounts[10];
            require_payer_and_system_program(payer, system_program)?;
            if preparation == FreshPdaPreparationV1::CreateOrAllocateSystemOwned {
                let page_number = next_page_number.to_le_bytes();
                let bump = [bump];
                let seeds: &[&[u8]] = &[
                    POOL_V1_ROOT_HISTORY_PAGE_SEED,
                    lane_account.key.as_ref(),
                    &page_number,
                    &bump,
                ];
                create_or_allocate_pda(
                    runtime,
                    payer,
                    next_page,
                    system_program,
                    POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
                    program_id,
                    seeds,
                )?;
            }
            require_program_owned_zeroed(
                next_page,
                program_id,
                POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
                rent,
            )?;
            next_page
        }
    };

    // Acquire every Pool-owned mutable borrow before the token CPI. A failed
    // CPI or post-CPI balance check therefore leaves writes to Solana's outer
    // transaction rollback boundary, with no partial Pool persistence.
    let mut lane_data = lane_account.try_borrow_mut_data()?;
    let mut page_data = writable_page.try_borrow_mut_data()?;
    runtime.invoke(&transfer_plan.instruction, &transfer_infos)?;
    validate_exact_deposit_delta_v1(token_accounts, &transfer_plan)?;

    lane_data.copy_from_slice(&next_lane_image);
    match mode {
        PairForestDepositPageModeV1::FreshGenesis { .. } => write_new_page_unchecked(
            &mut page_data,
            lane_account.key,
            0,
            0,
            &[lane.tree.root, append.root],
        ),
        PairForestDepositPageModeV1::ExistingSamePage { header } => {
            append_roots_unchecked(&mut page_data, header, &[append.root]);
        }
        PairForestDepositPageModeV1::FreshRollover {
            next_page_number, ..
        } => write_new_page_unchecked(
            &mut page_data,
            lane_account.key,
            next_page_number,
            append.root_sequence,
            &[append.root],
        ),
    }
    Ok(())
}

#[derive(Clone, Copy)]
enum PairForestSpendPageV1 {
    Genesis,
    SamePage(RootPageHeaderV1),
    Rollover { next_index: usize, page_number: u64 },
}

#[derive(Clone, Copy)]
struct PairForestSpendLayoutV1 {
    page: PairForestSpendPageV1,
    marker_index: usize,
    registry_start: usize,
    verifier_index: usize,
    proof_index: usize,
    token_start: usize,
}

fn plan_pair_forest_spend_layout_v1(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    lane: &PoolV1PairForestLaneStateV1,
    withdrawal: bool,
) -> Result<PairForestSpendLayoutV1, ProgramError> {
    if lane.tree.next_leaf_index >= POOL_V1_PAIR_CAPACITY {
        return Err(PoolV1ProgramError::TreeFull.into());
    }
    let lane_account = accounts.get(2).ok_or(ProgramError::NotEnoughAccountKeys)?;
    let current = accounts.get(3).ok_or(ProgramError::NotEnoughAccountKeys)?;
    let current_location = root_history_location(lane.tree.next_leaf_index);
    let next_location = root_history_location(lane.tree.next_leaf_index + 1);
    let (page, cursor) = if lane.tree.next_leaf_index == 0
        && account_is_zeroed_program_page(current, program_id)?
    {
        crate::history::require_root_page_address(program_id, lane_account.key, 0, current)?;
        require_program_account(current, program_id, true)?;
        (PairForestSpendPageV1::Genesis, 4)
    } else if current_location.page_number == next_location.page_number {
        let header = validate_lane_current_page(program_id, lane_account, current, lane, true)?;
        (PairForestSpendPageV1::SamePage(header), 4)
    } else {
        let header = validate_lane_current_page(program_id, lane_account, current, lane, false)?;
        if usize::from(header.filled) != POOL_V1_ROOT_HISTORY_CAPACITY {
            return Err(PoolV1ProgramError::StateHistoryMismatch.into());
        }
        let next_index = 4;
        let next = accounts
            .get(next_index)
            .ok_or(ProgramError::NotEnoughAccountKeys)?;
        crate::history::require_root_page_address(
            program_id,
            lane_account.key,
            next_location.page_number,
            next,
        )?;
        if !account_is_zeroed_program_page(next, program_id)? || !next.is_writable {
            return Err(PoolV1ProgramError::InvalidFreshAccount.into());
        }
        (
            PairForestSpendPageV1::Rollover {
                next_index,
                page_number: next_location.page_number,
            },
            5,
        )
    };
    let marker_index = cursor;
    let registry_start = cursor + 1;
    let verifier_index = cursor + 3;
    let proof_index = cursor + 4;
    let token_start: usize = cursor + 5;
    let expected = token_start
        .checked_add(if withdrawal { 5 } else { 0 })
        .ok_or(PoolV1ProgramError::ArithmeticOverflow)?;
    require_exact_account_count(accounts, expected)?;
    require_unique_accounts(accounts)?;
    Ok(PairForestSpendLayoutV1 {
        page,
        marker_index,
        registry_start,
        verifier_index,
        proof_index,
        token_start,
    })
}

fn validate_pair_forest_request_accounts_v1(
    program_id: &Pubkey,
    master_account: &AccountInfo<'_>,
    checkpoint_account: &AccountInfo<'_>,
    lane_account: &AccountInfo<'_>,
    master: &PoolV1PairForestMasterV1,
    checkpoint: &PoolV1PairForestCheckpointV1,
    lane: &PoolV1PairForestLaneStateV1,
    request: &PoolV1PairForestTerminalRequestV1,
) -> ProgramResult {
    if request.pool_program != program_id.to_bytes() {
        return Err(PoolV1ProgramError::VerifierDispatchIdentityMismatch.into());
    }
    let (pool, deployment, anchor_sequence, anchor_root, asset_id, destination) =
        match request.public {
            PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) => (
                public.pool,
                public.deployment_domain,
                public.anchor_sequence,
                public.anchor_root,
                public.asset_id,
                [0u8; 32],
            ),
            PoolV1PairForestTerminalPaymentV1::Withdrawal(public) => (
                public.pool,
                public.deployment_domain,
                public.anchor_sequence,
                public.anchor_root,
                public.asset_id,
                public.destination_token_account,
            ),
        };
    let output_lane =
        aspis_statement::pool_v1::pool_v1_pair_forest_output_lane_v1(request.public.nullifier())
            .map_err(|_| PoolV1ProgramError::NonCanonicalLeaf)?;
    if pool != master_account.key.to_bytes()
        || master.identity.pool != pool
        || deployment != master.identity.deployment_domain
        || asset_id != master.identity.asset_id
        || checkpoint_account.key.to_bytes() == [0u8; 32]
        || checkpoint.master != pool
        || checkpoint.deployment_domain != deployment
        || checkpoint.checkpoint_sequence != anchor_sequence
        || checkpoint.global_root != anchor_root
        || lane_account.key
            != &pool_v1_pair_forest_lane_address(program_id, master_account.key, output_lane)?.0
        || lane.master != pool
        || lane.lane_id != output_lane
        || master.initialized_lane_mask & (1u8 << output_lane) == 0
        || (request.public.transition_kind()
            == aspis_statement::pool_v1::PoolV1TransitionKind::Withdrawal
            && destination == [0u8; 32])
    {
        return Err(PoolV1ProgramError::VerifierDispatchIdentityMismatch.into());
    }
    Ok(())
}

fn next_pair_forest_lane_v1(
    lane: &PoolV1PairForestLaneStateV1,
    result: &aspis_statement::pool_v1::PoolV1PairForestTerminalResultV1,
) -> Result<PoolV1PairForestLaneStateV1, ProgramError> {
    let afterstate = result.verified_afterstate;
    if lane.tree.next_leaf_index.checked_add(1) != Some(afterstate.next_pair_index) {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    for (level, node) in afterstate.next_frontier.iter().enumerate() {
        if (afterstate.next_pair_index >> level) & 1 == 0
            && *node != POOL_V1_PAIR_EMPTY_ROOTS[level]
        {
            return Err(PoolV1ProgramError::StateHistoryMismatch.into());
        }
    }
    Ok(PoolV1PairForestLaneStateV1 {
        master: lane.master,
        lane_id: lane.lane_id,
        tree: IncrementalMerkleTreeV1 {
            next_leaf_index: afterstate.next_pair_index,
            root: afterstate.next_root,
            frontier: afterstate.next_frontier,
        },
    })
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn process_pair_forest_terminal_with_verifier_v1<'info, R, V, S>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'info>],
    instruction_data: &[u8],
    current_slot: u64,
    runtime: &mut R,
    verify: V,
    set_return_data: S,
) -> ProgramResult
where
    R: PoolCpiRuntimeV1,
    V: FnOnce(
        &Pubkey,
        &AccountInfo<'info>,
        &AccountInfo<'info>,
        &AccountInfo<'info>,
        &aspis_statement::pool_v1::VerifierPolicyV1,
        &[AccountInfo<'info>],
        &AccountInfo<'info>,
        &AccountInfo<'info>,
        &PoolV1PairForestTerminalRequestV1,
        u64,
    ) -> Result<AuthenticatedPairForestResultV1, ProgramError>,
    S: FnOnce(&[u8]),
{
    let request = decode_pool_v1_pair_forest_terminal_request_v1(instruction_data)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let master_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    let checkpoint_account = accounts.get(1).ok_or(ProgramError::NotEnoughAccountKeys)?;
    let lane_account = accounts.get(2).ok_or(ProgramError::NotEnoughAccountKeys)?;
    let master = decode_master_account(program_id, master_account, false)?;
    let checkpoint = decode_retained_pair_forest_checkpoint_account_v1(
        program_id,
        master_account.key,
        checkpoint_account,
    )?;
    let output_lane =
        aspis_statement::pool_v1::pool_v1_pair_forest_output_lane_v1(request.public.nullifier())
            .map_err(|_| PoolV1ProgramError::NonCanonicalLeaf)?;
    let lane = decode_lane_account(
        program_id,
        master_account.key,
        output_lane,
        lane_account,
        true,
    )?;
    validate_pair_forest_request_accounts_v1(
        program_id,
        master_account,
        checkpoint_account,
        lane_account,
        &master,
        &checkpoint,
        &lane,
        &request,
    )?;
    let withdrawal = matches!(
        request.public,
        PoolV1PairForestTerminalPaymentV1::Withdrawal(_)
    );
    let layout = plan_pair_forest_spend_layout_v1(program_id, accounts, &lane, withdrawal)?;

    let marker = &accounts[layout.marker_index];
    let marker_payload = PoolV1NullifierMarkerV1 {
        transition_kind: request.public.transition_kind(),
        pool: master_account.key.to_bytes(),
        deployment_domain: master.identity.deployment_domain,
        nullifier: *request.public.nullifier(),
        retained_anchor_sequence: checkpoint.checkpoint_sequence,
        retained_anchor_root: checkpoint.global_root,
        verifier_profile: request.verifier_profile,
        verifier_release: request.verifier_release,
    };
    let planned_marker = plan_nullifier_marker_consumption_v1(program_id, marker, marker_payload)?;
    if planned_marker.preparation() != NullifierMarkerPreparationV1::PopulateProgramOwnedZeroed {
        return Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into());
    }

    let withdrawal_plan =
        if let PoolV1PairForestTerminalPaymentV1::Withdrawal(public) = request.public {
            let token_accounts = &accounts[layout.token_start..layout.token_start + 5];
            Some(plan_legacy_withdrawal_transfer_from_identity_v1(
                program_id,
                master_account.key,
                &master.identity,
                token_accounts,
                &Pubkey::new_from_array(public.destination_token_account),
                public.amount,
            )?)
        } else {
            None
        };

    let authenticated = verify(
        program_id,
        master_account,
        checkpoint_account,
        lane_account,
        &master.verifier_policy,
        &accounts[layout.registry_start..layout.registry_start + 2],
        &accounts[layout.verifier_index],
        &accounts[layout.proof_index],
        &request,
        current_slot,
    )?;
    let result = authenticated.value();
    let common = PoolV1PairForestTerminalCommonV1 {
        master_account: master_account.key.to_bytes(),
        checkpoint_account: checkpoint_account.key.to_bytes(),
        selected_lane_account: lane_account.key.to_bytes(),
        output_lane,
        checkpoint_sequence: checkpoint.checkpoint_sequence,
        historical_global_anchor: checkpoint.global_root,
        lane_transition: aspis_statement::pool_v1::PoolV1PairLatePublicStatementV1 {
            live_snapshot: aspis_statement::pool_v1::PoolV1PairLiveSnapshotV1 {
                pool: master_account.key.to_bytes(),
                deployment_domain: master.identity.deployment_domain,
                sequence: lane.tree.next_leaf_index,
                next_pair_index: lane.tree.next_leaf_index,
                current_root: lane.tree.root,
                frontier: lane.tree.frontier,
            },
            candidate_afterstate: result.verified_afterstate,
        },
    };
    let statement = reconstruct_pool_v1_pair_forest_terminal_statement_v1(&request, common)
        .map_err(|_| PoolV1ProgramError::InvalidVerifierReturnData)?;
    validate_pool_v1_pair_forest_terminal_result_against_statement_v1(&statement, result)
        .map_err(|_| PoolV1ProgramError::InvalidVerifierReturnData)?;
    let next_lane = next_pair_forest_lane_v1(&lane, result)?;
    let next_lane_image =
        encode_pool_v1_pair_forest_lane_state_v1(&next_lane, &POOL_V1_PAIR_EMPTY_ROOTS)
            .map_err(|_| PoolV1ProgramError::StateHistoryMismatch)?;
    let result_bytes = encode_pool_v1_pair_forest_terminal_result_v1(result)
        .map_err(|_| PoolV1ProgramError::InvalidVerifierReturnData)?;

    let writable_page = match layout.page {
        PairForestSpendPageV1::Genesis | PairForestSpendPageV1::SamePage(_) => &accounts[3],
        PairForestSpendPageV1::Rollover { next_index, .. } => &accounts[next_index],
    };
    let mut lane_data = lane_account.try_borrow_mut_data()?;
    let mut page_data = writable_page.try_borrow_mut_data()?;
    let mut marker_data = marker.try_borrow_mut_data()?;
    if let Some(plan) = withdrawal_plan {
        let token_accounts = &accounts[layout.token_start..layout.token_start + 5];
        let infos = exact_withdrawal_transfer_account_infos_v1(token_accounts)?;
        let bump = [plan.authority_bump];
        let seeds: &[&[u8]] = &[
            POOL_V1_VAULT_AUTHORITY_SEED,
            master_account.key.as_ref(),
            &bump,
        ];
        runtime.invoke_signed(&plan.instruction, &infos, &[seeds])?;
        validate_exact_withdrawal_delta_v1(token_accounts, &plan)?;
    }

    lane_data.copy_from_slice(&next_lane_image);
    match layout.page {
        PairForestSpendPageV1::Genesis => write_new_page_unchecked(
            &mut page_data,
            lane_account.key,
            0,
            0,
            &[lane.tree.root, result.verified_afterstate.next_root],
        ),
        PairForestSpendPageV1::SamePage(header) => append_roots_unchecked(
            &mut page_data,
            header,
            &[result.verified_afterstate.next_root],
        ),
        PairForestSpendPageV1::Rollover { page_number, .. } => write_new_page_unchecked(
            &mut page_data,
            lane_account.key,
            page_number,
            result.verified_afterstate.next_pair_index,
            &[result.verified_afterstate.next_root],
        ),
    }
    marker_data.copy_from_slice(&planned_marker.encoded_marker());
    set_return_data(&result_bytes);
    Ok(())
}

pub(crate) fn process_pair_forest_terminal_v1<'info, R: PoolCpiRuntimeV1>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'info>],
    instruction_data: &[u8],
    current_slot: u64,
    runtime: &mut R,
) -> ProgramResult {
    process_pair_forest_terminal_with_verifier_v1(
        program_id,
        accounts,
        instruction_data,
        current_slot,
        runtime,
        dispatch_pair_forest_terminal_readonly_v1,
        solana_program::program::set_return_data,
    )
}

/// Initialize
/// `[master, lane_0, ..., lane_7, mint, vault, token_program, payer,
/// system_program]`.
/// Every program account is either a fresh System account at its canonical PDA
/// or an exactly sized, zeroed, precreated Pool-owned account.
pub(crate) fn process_pair_forest_initialize_with_runtime_v1<'info, R: PoolCpiRuntimeV1>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'info>],
    instruction_data: &[u8],
    rent: &Rent,
    runtime: &mut R,
) -> ProgramResult {
    require_exact_account_count(accounts, POOL_V1_PAIR_FOREST_INITIALIZE_ACCOUNT_COUNT)?;
    require_unique_accounts(accounts)?;
    let initialization = decode_pair_forest_initialize_instruction_v1(instruction_data)?;
    let master = &accounts[FOREST_MASTER_ACCOUNT_INDEX];
    let lanes = &accounts[FOREST_FIRST_LANE_ACCOUNT_INDEX
        ..FOREST_FIRST_LANE_ACCOUNT_INDEX + POOL_V1_PAIR_FOREST_LANE_COUNT];
    let mint = &accounts[FOREST_MINT_OR_CHECKPOINT_ACCOUNT_INDEX];
    let vault = &accounts[FOREST_INIT_VAULT_ACCOUNT_INDEX];
    let token_program = &accounts[FOREST_INIT_TOKEN_PROGRAM_ACCOUNT_INDEX];
    let payer = &accounts[FOREST_INIT_PAYER_ACCOUNT_INDEX];
    let system_program_account = &accounts[FOREST_INIT_SYSTEM_ACCOUNT_INDEX];
    require_payer_and_system_program(payer, system_program_account)?;
    require_token_program_account(token_program)?;
    require_forest_mint_account(&initialization, mint)?;

    let (expected_master, master_bump) = pool_v1_pair_forest_master_address(program_id, mint.key);
    let master_preparation = plan_fresh_program_pda(
        master,
        program_id,
        &expected_master,
        POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES,
    )?;
    let vault_preparation =
        plan_vault_initialization(program_id, &expected_master, mint.key, vault)?;
    let mut lane_preparations =
        [FreshPdaPreparationV1::ProgramOwnedZeroed; POOL_V1_PAIR_FOREST_LANE_COUNT];
    let mut lane_bumps = [0u8; POOL_V1_PAIR_FOREST_LANE_COUNT];
    for lane in 0..POOL_V1_PAIR_FOREST_LANE_COUNT {
        let (expected_lane, bump) =
            pool_v1_pair_forest_lane_address(program_id, &expected_master, lane as u8)?;
        lane_preparations[lane] = plan_fresh_program_pda(
            &lanes[lane],
            program_id,
            &expected_lane,
            aspis_statement::pool_v1::POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES,
        )?;
        lane_bumps[lane] = bump;
    }

    // Freeze every program-owned output image before the first CPI.
    let master_state = PoolV1PairForestMasterV1 {
        identity: PoolIdentityV1 {
            pool: expected_master.to_bytes(),
            asset_mint: initialization.asset_mint,
            token_program: initialization.token_program,
            asset_id: initialization.asset_id,
            deployment_domain: initialization.deployment_domain,
        },
        verifier_policy: initialization.verifier_policy,
        initialized_lane_mask: aspis_statement::pool_v1::POOL_V1_PAIR_FOREST_ALL_LANES_MASK,
        has_checkpoint: false,
        next_checkpoint_sequence: 0,
        last_checkpoint_lane_sequences: [0u64; POOL_V1_PAIR_FOREST_LANE_COUNT],
    };
    let master_image = encode_pool_v1_pair_forest_master_v1(&master_state)
        .map_err(|_| PoolV1ProgramError::StateHistoryMismatch)?;
    let mut lane_images = Vec::with_capacity(POOL_V1_PAIR_FOREST_LANE_COUNT);
    for lane in 0..POOL_V1_PAIR_FOREST_LANE_COUNT {
        lane_images.push(
            encode_pool_v1_pair_forest_lane_state_v1(
                &genesis_lane_state(&expected_master, lane as u8),
                &POOL_V1_PAIR_EMPTY_ROOTS,
            )
            .map_err(|_| PoolV1ProgramError::StateHistoryMismatch)?,
        );
    }

    if master_preparation == FreshPdaPreparationV1::CreateOrAllocateSystemOwned {
        let bump = [master_bump];
        let seeds: &[&[u8]] = &[POOL_V1_PAIR_FOREST_MASTER_SEED, mint.key.as_ref(), &bump];
        create_or_allocate_pda(
            runtime,
            payer,
            master,
            system_program_account,
            POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES,
            program_id,
            seeds,
        )?;
    }
    for lane in 0..POOL_V1_PAIR_FOREST_LANE_COUNT {
        if lane_preparations[lane] == FreshPdaPreparationV1::CreateOrAllocateSystemOwned {
            let lane_id = [lane as u8];
            let bump = [lane_bumps[lane]];
            let seeds: &[&[u8]] = &[
                POOL_V1_PAIR_FOREST_LANE_SEED,
                expected_master.as_ref(),
                &lane_id,
                &bump,
            ];
            create_or_allocate_pda(
                runtime,
                payer,
                &lanes[lane],
                system_program_account,
                aspis_statement::pool_v1::POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES,
                program_id,
                seeds,
            )?;
        }
    }
    initialize_vault_account(
        runtime,
        program_id,
        &expected_master,
        mint,
        vault,
        token_program,
        payer,
        system_program_account,
        vault_preparation,
    )?;

    require_program_owned_zeroed(
        master,
        program_id,
        POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES,
        rent,
    )?;
    for lane in lanes {
        require_program_owned_zeroed(
            lane,
            program_id,
            aspis_statement::pool_v1::POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES,
            rent,
        )?;
    }

    // Acquire every mutable borrow before the first write. Runtime rollback
    // remains the outer atomicity boundary for preceding System CPIs.
    let mut master_data = master.try_borrow_mut_data()?;
    let mut lane_data = Vec::with_capacity(POOL_V1_PAIR_FOREST_LANE_COUNT);
    for lane in lanes {
        lane_data.push(lane.try_borrow_mut_data()?);
    }
    master_data.copy_from_slice(&master_image);
    for lane in 0..POOL_V1_PAIR_FOREST_LANE_COUNT {
        lane_data[lane].copy_from_slice(&lane_images[lane]);
    }
    Ok(())
}

/// Create one permissionless coherent checkpoint from
/// `[master, lane_0, ..., lane_7, checkpoint, payer, system_program]`.
/// Lane accounts are read-only. Only the fresh immutable checkpoint and the
/// master's checkpoint metadata are written.
pub(crate) fn process_pair_forest_checkpoint_with_runtime_v1<'info, R: PoolCpiRuntimeV1>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'info>],
    instruction_data: &[u8],
    rent: &Rent,
    runtime: &mut R,
) -> ProgramResult {
    decode_pair_forest_checkpoint_instruction_v1(instruction_data)?;
    require_exact_account_count(accounts, POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_COUNT)?;
    require_unique_accounts(accounts)?;
    let master = &accounts[FOREST_MASTER_ACCOUNT_INDEX];
    let lanes = &accounts[FOREST_FIRST_LANE_ACCOUNT_INDEX
        ..FOREST_FIRST_LANE_ACCOUNT_INDEX + POOL_V1_PAIR_FOREST_LANE_COUNT];
    let checkpoint = &accounts[FOREST_MINT_OR_CHECKPOINT_ACCOUNT_INDEX];
    let payer = &accounts[FOREST_CHECKPOINT_PAYER_ACCOUNT_INDEX];
    let system_program_account = &accounts[FOREST_CHECKPOINT_SYSTEM_ACCOUNT_INDEX];
    require_payer_and_system_program(payer, system_program_account)?;

    let planned = plan_pair_forest_checkpoint_accounts_v1(program_id, master, lanes, checkpoint)?;
    let preparation = plan_fresh_program_pda(
        checkpoint,
        program_id,
        &planned.checkpoint,
        POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES,
    )?;
    if preparation == FreshPdaPreparationV1::CreateOrAllocateSystemOwned {
        let sequence = decode_pool_v1_pair_forest_checkpoint_v1(&planned.checkpoint_image)
            .map_err(|_| PoolV1ProgramError::StateHistoryMismatch)?
            .checkpoint_sequence;
        let sequence_bytes = sequence.to_le_bytes();
        let bump = pool_v1_pair_forest_checkpoint_address(program_id, master.key, sequence).1;
        let bump_bytes = [bump];
        let seeds: &[&[u8]] = &[
            POOL_V1_PAIR_FOREST_CHECKPOINT_SEED,
            master.key.as_ref(),
            &sequence_bytes,
            &bump_bytes,
        ];
        create_or_allocate_pda(
            runtime,
            payer,
            checkpoint,
            system_program_account,
            POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES,
            program_id,
            seeds,
        )?;
    }
    require_program_owned_zeroed(
        checkpoint,
        program_id,
        POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES,
        rent,
    )?;

    let mut master_data = master.try_borrow_mut_data()?;
    let mut checkpoint_data = checkpoint.try_borrow_mut_data()?;
    checkpoint_data.copy_from_slice(&planned.checkpoint_image);
    master_data.copy_from_slice(&planned.next_master_image);
    Ok(())
}

/// Authenticate one retained immutable checkpoint account. Historical records
/// remain valid after later checkpoints; no comparison to a mutable "latest"
/// value is made here.
pub fn decode_retained_pair_forest_checkpoint_account_v1(
    program_id: &Pubkey,
    expected_master: &Pubkey,
    account: &AccountInfo<'_>,
) -> Result<PoolV1PairForestCheckpointV1, ProgramError> {
    require_program_account(account, program_id, false)?;
    if account.is_signer {
        return Err(ProgramError::InvalidAccountData);
    }
    let checkpoint = decode_pool_v1_pair_forest_checkpoint_v1(&account.try_borrow_data()?)
        .map_err(|_| PoolV1ProgramError::InvalidAccountType)?;
    if checkpoint.master != expected_master.to_bytes()
        || account.key
            != &pool_v1_pair_forest_checkpoint_address(
                program_id,
                expected_master,
                checkpoint.checkpoint_sequence,
            )
            .0
    {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    Ok(checkpoint)
}

#[cfg(test)]
mod tests {
    use std::{vec, vec::Vec};

    use aspis_core::field::M31;
    use aspis_statement::pool_v1::{
        encode_pool_v1_pair_forest_checkpoint_v1, encode_pool_v1_pair_forest_lane_state_v1,
        encode_pool_v1_pair_forest_master_v1, encode_pool_v1_pair_forest_terminal_request_v1,
        IncrementalMerkleTreeV1, PoolIdentityV1, PoolV1PairForestTerminalPaymentV1,
        PoolV1PairForestTerminalRequestV1, PoolV1PairForestTerminalResultV1,
        PoolV1PairVerifiedAfterstateV1, PoolV1PrivateTransferPublicV1, PoolV1TransitionKind,
        PoolV1WithdrawalPublicV1, VerifierPolicyV1, POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES,
        POOL_V1_PAIR_FOREST_ALL_LANES_MASK, POOL_V1_PAIR_TREE_DEPTH,
    };
    use solana_program::{clock::Epoch, instruction::Instruction};
    use solana_sdk_ids::{bpf_loader, native_loader, system_program};

    use super::*;

    #[derive(Clone)]
    struct TestAccount {
        key: Pubkey,
        owner: Pubkey,
        lamports: u64,
        data: Vec<u8>,
        signer: bool,
        writable: bool,
        executable: bool,
    }

    impl TestAccount {
        fn info(&mut self) -> AccountInfo<'_> {
            AccountInfo::new(
                &self.key,
                self.signer,
                self.writable,
                &mut self.lamports,
                &mut self.data,
                &self.owner,
                self.executable,
                Epoch::default(),
            )
        }
    }

    struct NoCpi;

    impl PoolCpiRuntimeV1 for NoCpi {
        fn invoke<'info>(&mut self, _: &Instruction, _: &[AccountInfo<'info>]) -> ProgramResult {
            panic!("unexpected unsigned CPI")
        }

        fn invoke_signed<'info>(
            &mut self,
            _: &Instruction,
            _: &[AccountInfo<'info>],
            _: &[&[&[u8]]],
        ) -> ProgramResult {
            panic!("unexpected signed CPI")
        }
    }

    struct DepositCpi {
        apply_exact_delta: bool,
        calls: usize,
    }

    struct WithdrawalCpi {
        fail: bool,
        calls: usize,
    }

    impl PoolCpiRuntimeV1 for WithdrawalCpi {
        fn invoke<'info>(&mut self, _: &Instruction, _: &[AccountInfo<'info>]) -> ProgramResult {
            panic!("unexpected unsigned CPI")
        }

        fn invoke_signed<'info>(
            &mut self,
            instruction: &Instruction,
            infos: &[AccountInfo<'info>],
            _: &[&[&[u8]]],
        ) -> ProgramResult {
            self.calls += 1;
            if self.fail {
                return Err(ProgramError::Custom(0xc057));
            }
            let amount = u64::from_le_bytes(
                instruction.data[1..9]
                    .try_into()
                    .map_err(|_| ProgramError::InvalidInstructionData)?,
            );
            let vault = u64::from_le_bytes(
                infos[0].try_borrow_data()?[64..72]
                    .try_into()
                    .map_err(|_| ProgramError::InvalidAccountData)?,
            );
            let destination = u64::from_le_bytes(
                infos[2].try_borrow_data()?[64..72]
                    .try_into()
                    .map_err(|_| ProgramError::InvalidAccountData)?,
            );
            crate::vault::write_token_amount_for_test(
                &infos[0],
                vault
                    .checked_sub(amount)
                    .ok_or(PoolV1ProgramError::ArithmeticOverflow)?,
            )?;
            crate::vault::write_token_amount_for_test(
                &infos[2],
                destination
                    .checked_add(amount)
                    .ok_or(PoolV1ProgramError::ArithmeticOverflow)?,
            )
        }
    }

    impl PoolCpiRuntimeV1 for DepositCpi {
        fn invoke<'info>(
            &mut self,
            instruction: &Instruction,
            infos: &[AccountInfo<'info>],
        ) -> ProgramResult {
            assert_eq!(instruction.program_id, LEGACY_SPL_TOKEN_PROGRAM_ID);
            assert_eq!(instruction.data.len(), 10);
            assert_eq!(instruction.data[0], 12);
            assert_eq!(infos.len(), 5);
            self.calls += 1;
            if !self.apply_exact_delta {
                return Ok(());
            }
            let amount = u64::from_le_bytes(instruction.data[1..9].try_into().unwrap());
            let source_before =
                u64::from_le_bytes(infos[0].try_borrow_data()?[64..72].try_into().unwrap());
            let vault_before =
                u64::from_le_bytes(infos[2].try_borrow_data()?[64..72].try_into().unwrap());
            crate::vault::write_token_amount_for_test(
                &infos[0],
                source_before.checked_sub(amount).unwrap(),
            )?;
            crate::vault::write_token_amount_for_test(
                &infos[2],
                vault_before.checked_add(amount).unwrap(),
            )
        }

        fn invoke_signed<'info>(
            &mut self,
            _: &Instruction,
            _: &[AccountInfo<'info>],
            _: &[&[&[u8]]],
        ) -> ProgramResult {
            panic!("unexpected signed CPI")
        }
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 13 * index as u32))
    }

    fn master(program_id: Pubkey, mint: Pubkey) -> (Pubkey, PoolV1PairForestMasterV1) {
        let key = pool_v1_pair_forest_master_address(&program_id, &mint).0;
        (
            key,
            PoolV1PairForestMasterV1 {
                identity: PoolIdentityV1 {
                    pool: key.to_bytes(),
                    asset_mint: mint.to_bytes(),
                    token_program: [3u8; 32],
                    asset_id: M31(4),
                    deployment_domain: [5u8; 32],
                },
                verifier_policy: VerifierPolicyV1 {
                    flags: 1,
                    registry_program: [6u8; 32],
                    registry_authority: [0u8; 32],
                    policy_binding: [7u8; 32],
                },
                initialized_lane_mask: POOL_V1_PAIR_FOREST_ALL_LANES_MASK,
                has_checkpoint: false,
                next_checkpoint_sequence: 0,
                last_checkpoint_lane_sequences: [0u64; 8],
            },
        )
    }

    fn lane_state(master: Pubkey, lane: u8) -> PoolV1PairForestLaneStateV1 {
        PoolV1PairForestLaneStateV1 {
            master: master.to_bytes(),
            lane_id: lane,
            tree: IncrementalMerkleTreeV1 {
                next_leaf_index: 0,
                root: POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH],
                frontier: core::array::from_fn(|level| POOL_V1_PAIR_EMPTY_ROOTS[level]),
            },
        }
    }

    fn fixtures(program_id: Pubkey) -> (TestAccount, [TestAccount; 8], TestAccount, Pubkey) {
        let mint = Pubkey::new_unique();
        let (master_key, master) = master(program_id, mint);
        let master_account = TestAccount {
            key: master_key,
            owner: program_id,
            lamports: 1,
            data: encode_pool_v1_pair_forest_master_v1(&master)
                .unwrap()
                .to_vec(),
            signer: false,
            writable: true,
            executable: false,
        };
        let lanes = core::array::from_fn(|lane| TestAccount {
            key: pool_v1_pair_forest_lane_address(&program_id, &master_key, lane as u8)
                .unwrap()
                .0,
            owner: program_id,
            lamports: 1,
            data: encode_pool_v1_pair_forest_lane_state_v1(
                &lane_state(master_key, lane as u8),
                &POOL_V1_PAIR_EMPTY_ROOTS,
            )
            .unwrap()
            .to_vec(),
            signer: false,
            writable: false,
            executable: false,
        });
        let checkpoint_key = pool_v1_pair_forest_checkpoint_address(&program_id, &master_key, 0).0;
        let checkpoint = TestAccount {
            key: checkpoint_key,
            owner: program_id,
            lamports: 1,
            data: vec![0u8; POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES],
            signer: false,
            writable: true,
            executable: false,
        };
        (master_account, lanes, checkpoint, master_key)
    }

    fn forest_initialization(mint: Pubkey) -> PoolInitializationV1 {
        PoolInitializationV1 {
            asset_mint: mint.to_bytes(),
            token_program: LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes(),
            asset_id: M31(4),
            deployment_domain: [5u8; 32],
            verifier_policy: VerifierPolicyV1 {
                flags: 1,
                registry_program: [6u8; 32],
                registry_authority: [0u8; 32],
                policy_binding: [7u8; 32],
            },
        }
    }

    fn initialized_mint_data() -> Vec<u8> {
        let mut data = vec![0u8; LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES];
        data[45] = 1;
        data
    }

    fn initialized_token_data(mint: Pubkey, authority: Pubkey, amount: u64) -> Vec<u8> {
        let mut data = vec![0u8; crate::vault::LEGACY_SPL_TOKEN_ACCOUNT_BYTES];
        data[..32].copy_from_slice(mint.as_ref());
        data[32..64].copy_from_slice(authority.as_ref());
        data[64..72].copy_from_slice(&amount.to_le_bytes());
        data[108] = 1;
        data
    }

    fn rent_lamports(bytes: usize) -> u64 {
        Rent::default().minimum_balance(bytes).max(1)
    }

    fn terminal_base_accounts(
        program_id: Pubkey,
        master_key: Pubkey,
        master_state: &PoolV1PairForestMasterV1,
        checkpoint_key: Pubkey,
        checkpoint: &PoolV1PairForestCheckpointV1,
        lane_key: Pubkey,
        lane: &PoolV1PairForestLaneStateV1,
        marker_key: Pubkey,
    ) -> Vec<TestAccount> {
        let page_key = pool_v1_root_page_address(&program_id, &lane_key, 0).0;
        vec![
            TestAccount {
                key: master_key,
                owner: program_id,
                lamports: 1,
                data: encode_pool_v1_pair_forest_master_v1(master_state)
                    .unwrap()
                    .to_vec(),
                signer: false,
                writable: false,
                executable: false,
            },
            TestAccount {
                key: checkpoint_key,
                owner: program_id,
                lamports: 1,
                data: encode_pool_v1_pair_forest_checkpoint_v1(checkpoint)
                    .unwrap()
                    .to_vec(),
                signer: false,
                writable: false,
                executable: false,
            },
            TestAccount {
                key: lane_key,
                owner: program_id,
                lamports: 1,
                data: encode_pool_v1_pair_forest_lane_state_v1(lane, &POOL_V1_PAIR_EMPTY_ROOTS)
                    .unwrap()
                    .to_vec(),
                signer: false,
                writable: true,
                executable: false,
            },
            TestAccount {
                key: page_key,
                owner: program_id,
                lamports: 1,
                data: vec![0; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES],
                signer: false,
                writable: true,
                executable: false,
            },
            TestAccount {
                key: marker_key,
                owner: program_id,
                lamports: 1,
                data: vec![0; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES],
                signer: false,
                writable: true,
                executable: false,
            },
            TestAccount {
                key: Pubkey::new_unique(),
                owner: Pubkey::new_unique(),
                lamports: 1,
                data: vec![],
                signer: false,
                writable: false,
                executable: false,
            },
            TestAccount {
                key: Pubkey::new_unique(),
                owner: Pubkey::new_unique(),
                lamports: 1,
                data: vec![],
                signer: false,
                writable: false,
                executable: false,
            },
            TestAccount {
                key: Pubkey::new_unique(),
                owner: bpf_loader::id(),
                lamports: 1,
                data: vec![],
                signer: false,
                writable: false,
                executable: true,
            },
            TestAccount {
                key: Pubkey::new_unique(),
                owner: Pubkey::new_unique(),
                lamports: 1,
                data: vec![],
                signer: false,
                writable: false,
                executable: false,
            },
        ]
    }

    fn initialization_accounts(program_id: Pubkey, mint: Pubkey) -> Vec<TestAccount> {
        let master = pool_v1_pair_forest_master_address(&program_id, &mint).0;
        let mut accounts = Vec::with_capacity(POOL_V1_PAIR_FOREST_INITIALIZE_ACCOUNT_COUNT);
        accounts.push(TestAccount {
            key: master,
            owner: program_id,
            lamports: rent_lamports(POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES),
            data: vec![0u8; POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES],
            signer: false,
            writable: true,
            executable: false,
        });
        for lane in 0..POOL_V1_PAIR_FOREST_LANE_COUNT {
            accounts.push(TestAccount {
                key: pool_v1_pair_forest_lane_address(&program_id, &master, lane as u8)
                    .unwrap()
                    .0,
                owner: program_id,
                lamports: rent_lamports(
                    aspis_statement::pool_v1::POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES,
                ),
                data: vec![0u8; aspis_statement::pool_v1::POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES],
                signer: false,
                writable: true,
                executable: false,
            });
        }
        accounts.push(TestAccount {
            key: mint,
            owner: LEGACY_SPL_TOKEN_PROGRAM_ID,
            lamports: 1,
            data: initialized_mint_data(),
            signer: false,
            writable: false,
            executable: false,
        });
        let vault_authority = crate::pool_v1_vault_authority_address(&program_id, &master).0;
        accounts.push(TestAccount {
            key: crate::pool_v1_vault_token_account_address(&program_id, &master).0,
            owner: LEGACY_SPL_TOKEN_PROGRAM_ID,
            lamports: rent_lamports(crate::vault::LEGACY_SPL_TOKEN_ACCOUNT_BYTES),
            data: initialized_token_data(mint, vault_authority, 0),
            signer: false,
            writable: true,
            executable: false,
        });
        accounts.push(TestAccount {
            key: LEGACY_SPL_TOKEN_PROGRAM_ID,
            owner: bpf_loader::id(),
            lamports: 1,
            data: Vec::new(),
            signer: false,
            writable: false,
            executable: true,
        });
        accounts.push(TestAccount {
            key: Pubkey::new_unique(),
            owner: system_program::id(),
            lamports: 1_000_000_000,
            data: Vec::new(),
            signer: true,
            writable: true,
            executable: false,
        });
        accounts.push(TestAccount {
            key: system_program::id(),
            owner: native_loader::id(),
            lamports: 1,
            data: Vec::new(),
            signer: false,
            writable: false,
            executable: true,
        });
        accounts
    }

    fn genesis_deposit_fixture(
        program_id: Pubkey,
        mint: Pubkey,
    ) -> (Vec<TestAccount>, Vec<u8>, u8, Digest) {
        let initialization = forest_initialization(mint);
        let mut initialized = initialization_accounts(program_id, mint);
        let initialize_instruction =
            encode_pair_forest_initialize_instruction_v1(&initialization).unwrap();
        {
            let infos: Vec<_> = initialized.iter_mut().map(TestAccount::info).collect();
            process_pair_forest_initialize_with_runtime_v1(
                &program_id,
                &infos,
                &initialize_instruction,
                &Rent::default(),
                &mut NoCpi,
            )
            .unwrap();
        }
        let request = DepositRequestV1 {
            owner_key: digest(700),
            amount: 7,
            salt: digest(900),
            encrypted_note_payload: b"forest-note",
        };
        let commitment = pool_v1_note_commitment(
            &request.owner_key,
            request.amount,
            initialization.asset_id,
            &request.salt,
        );
        let lane_id = pool_v1_pair_forest_deposit_lane_v1(&commitment).unwrap();
        let instruction = encode_pair_forest_deposit_instruction_v1(&request).unwrap();
        let master_key = initialized[0].key;
        let lane_key = initialized[1 + usize::from(lane_id)].key;
        let source_authority = Pubkey::new_unique();
        let source = Pubkey::new_unique();
        let mut master = initialized[0].clone();
        master.writable = false;
        let mut lane = initialized[1 + usize::from(lane_id)].clone();
        lane.writable = true;
        let accounts = vec![
            master,
            lane,
            TestAccount {
                key: pool_v1_root_page_address(&program_id, &lane_key, 0).0,
                owner: program_id,
                lamports: rent_lamports(POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES),
                data: vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES],
                signer: false,
                writable: true,
                executable: false,
            },
            initialized[9].clone(),
            TestAccount {
                key: source,
                owner: LEGACY_SPL_TOKEN_PROGRAM_ID,
                lamports: 1,
                data: initialized_token_data(mint, source_authority, 100),
                signer: false,
                writable: true,
                executable: false,
            },
            TestAccount {
                key: source_authority,
                owner: system_program::id(),
                lamports: 1,
                data: Vec::new(),
                signer: true,
                writable: false,
                executable: false,
            },
            initialized[10].clone(),
            initialized[11].clone(),
            initialized[12].clone(),
            initialized[13].clone(),
        ];
        assert_eq!(accounts[0].key, master_key);
        (accounts, instruction, lane_id, commitment)
    }

    #[test]
    fn instruction_wires_are_exact_versioned_and_trailing_closed() {
        let initialization = forest_initialization(Pubkey::new_unique());
        let encoded = encode_pair_forest_initialize_instruction_v1(&initialization).unwrap();
        assert_eq!(encoded.len(), POOL_V1_INITIALIZE_INSTRUCTION_BYTES);
        assert_eq!(
            decode_pair_forest_initialize_instruction_v1(&encoded),
            Ok(initialization)
        );
        let mut wrong_lane_count = encoded;
        wrong_lane_count[5] = 7;
        assert!(decode_pair_forest_initialize_instruction_v1(&wrong_lane_count).is_err());
        let mut trailing = encoded.to_vec();
        trailing.push(0);
        assert!(decode_pair_forest_initialize_instruction_v1(&trailing).is_err());

        let checkpoint = encode_pair_forest_checkpoint_instruction_v1();
        assert_eq!(
            decode_pair_forest_checkpoint_instruction_v1(&checkpoint),
            Ok(())
        );
        let mut wrong_version = checkpoint;
        wrong_version[4] = 2;
        assert_eq!(
            decode_pair_forest_checkpoint_instruction_v1(&wrong_version),
            Err(ProgramError::InvalidInstructionData)
        );

        let request = DepositRequestV1 {
            owner_key: digest(100),
            amount: 7,
            salt: digest(200),
            encrypted_note_payload: b"forest-note",
        };
        let deposit = encode_pair_forest_deposit_instruction_v1(&request).unwrap();
        assert_eq!(&deposit[..4], b"AS8D");
        assert_eq!(
            decode_pair_forest_deposit_instruction_v1(&deposit),
            Ok(request)
        );
        let mut wrong_magic = deposit.clone();
        wrong_magic[..4].copy_from_slice(b"ASDI");
        assert!(decode_pair_forest_deposit_instruction_v1(&wrong_magic).is_err());
        let mut deposit_trailing = deposit;
        deposit_trailing.push(0);
        assert!(decode_pair_forest_deposit_instruction_v1(&deposit_trailing).is_err());
    }

    #[test]
    fn global_root_is_exact_seven_parent_fixed_order_tree() {
        let roots = core::array::from_fn(|lane| digest(100 + 100 * lane as u32));
        let first = [
            pool_v1_tree_parent(&roots[0], &roots[1]),
            pool_v1_tree_parent(&roots[2], &roots[3]),
            pool_v1_tree_parent(&roots[4], &roots[5]),
            pool_v1_tree_parent(&roots[6], &roots[7]),
        ];
        let second = [
            pool_v1_tree_parent(&first[0], &first[1]),
            pool_v1_tree_parent(&first[2], &first[3]),
        ];
        assert_eq!(
            pool_v1_pair_forest_global_root_v1(&roots),
            pool_v1_tree_parent(&second[0], &second[1])
        );
        let mut swapped = roots;
        swapped.swap(0, 1);
        assert_ne!(
            pool_v1_pair_forest_global_root_v1(&roots),
            pool_v1_pair_forest_global_root_v1(&swapped)
        );
    }

    #[test]
    fn precreated_initialize_writes_exact_master_and_all_eight_genesis_lanes() {
        let program_id = Pubkey::new_unique();
        let mint = Pubkey::new_unique();
        let initialization = forest_initialization(mint);
        let instruction = encode_pair_forest_initialize_instruction_v1(&initialization).unwrap();
        let mut accounts = initialization_accounts(program_id, mint);
        let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
        process_pair_forest_initialize_with_runtime_v1(
            &program_id,
            &infos,
            &instruction,
            &Rent::default(),
            &mut NoCpi,
        )
        .unwrap();
        drop(infos);

        let decoded_master = decode_pool_v1_pair_forest_master_v1(&accounts[0].data).unwrap();
        assert_eq!(decoded_master.identity.asset_mint, mint.to_bytes());
        assert_eq!(decoded_master.identity.deployment_domain, [5u8; 32]);
        assert_eq!(decoded_master.initialized_lane_mask, 0xff);
        assert!(!decoded_master.has_checkpoint);
        for lane in 0..POOL_V1_PAIR_FOREST_LANE_COUNT {
            let decoded = decode_pool_v1_pair_forest_lane_state_v1(
                &accounts[1 + lane].data,
                &POOL_V1_PAIR_EMPTY_ROOTS,
            )
            .unwrap();
            assert_eq!(decoded, genesis_lane_state(&accounts[0].key, lane as u8));
        }
    }

    #[test]
    fn vault_deposit_routes_one_occupied_empty_pair_and_creates_lane_history() {
        let program_id = Pubkey::new_unique();
        let mint = Pubkey::new_unique();
        let (mut accounts, instruction, lane_id, commitment) =
            genesis_deposit_fixture(program_id, mint);
        let source_before = accounts[4].data.clone();
        let mut runtime = DepositCpi {
            apply_exact_delta: true,
            calls: 0,
        };
        let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
        process_pair_forest_deposit_with_runtime_v1(
            &program_id,
            &infos,
            &instruction,
            &Rent::default(),
            &mut runtime,
        )
        .unwrap();
        drop(infos);
        assert_eq!(runtime.calls, 1);

        let lane =
            decode_pool_v1_pair_forest_lane_state_v1(&accounts[1].data, &POOL_V1_PAIR_EMPTY_ROOTS)
                .unwrap();
        assert_eq!(lane.lane_id, lane_id);
        assert_eq!(lane.tree.next_leaf_index, 1);
        let witness = PoolV1PairLeafWitnessV1::single_output(commitment).unwrap();
        assert_eq!(witness.second_occupied, M31::ZERO);
        assert_eq!(witness.second_commitment, [M31::ZERO; 8]);
        assert_eq!(witness.second_occupancy_inverse, M31::ZERO);
        let expected = genesis_lane_state(&accounts[0].key, lane_id)
            .tree
            .append_one_with_empty_roots(witness.leaf_digest().unwrap(), &POOL_V1_PAIR_EMPTY_ROOTS)
            .unwrap()
            .0;
        assert_eq!(lane.tree, expected);

        let page = validate_root_page_bytes(&accounts[2].data, &accounts[1].key, 0).unwrap();
        assert_eq!(page.filled, 2);
        assert_eq!(
            read_retained_root(&accounts[2].data, page, 0).unwrap(),
            POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH]
        );
        assert_eq!(
            read_retained_root(&accounts[2].data, page, 1).unwrap(),
            lane.tree.root
        );
        assert_eq!(
            u64::from_le_bytes(accounts[4].data[64..72].try_into().unwrap()),
            93
        );
        assert_eq!(
            u64::from_le_bytes(accounts[6].data[64..72].try_into().unwrap()),
            7
        );
        assert_ne!(accounts[4].data, source_before);

        // The next deposit uses the compact existing-page account shape and
        // appends without rewriting either retained root.
        accounts.truncate(FOREST_DEPOSIT_SAME_PAGE_ACCOUNT_COUNT);
        let first_page = accounts[2].data.clone();
        let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
        process_pair_forest_deposit_with_runtime_v1(
            &program_id,
            &infos,
            &instruction,
            &Rent::default(),
            &mut runtime,
        )
        .unwrap();
        drop(infos);
        assert_eq!(runtime.calls, 2);
        let lane =
            decode_pool_v1_pair_forest_lane_state_v1(&accounts[1].data, &POOL_V1_PAIR_EMPTY_ROOTS)
                .unwrap();
        assert_eq!(lane.tree.next_leaf_index, 2);
        let page = validate_root_page_bytes(&accounts[2].data, &accounts[1].key, 0).unwrap();
        assert_eq!(page.filled, 3);
        assert_eq!(
            &accounts[2].data[64..64 + 2 * 32],
            &first_page[64..64 + 2 * 32]
        );
        assert_eq!(
            read_retained_root(&accounts[2].data, page, 2).unwrap(),
            lane.tree.root
        );
    }

    #[test]
    fn deposit_alias_or_bad_token_delta_fails_without_pool_writes() {
        let program_id = Pubkey::new_unique();
        let mint = Pubkey::new_unique();
        let (mut bad_delta, instruction, _, _) = genesis_deposit_fixture(program_id, mint);
        let lane_before = bad_delta[1].data.clone();
        let page_before = bad_delta[2].data.clone();
        let infos: Vec<_> = bad_delta.iter_mut().map(TestAccount::info).collect();
        let mut runtime = DepositCpi {
            apply_exact_delta: false,
            calls: 0,
        };
        assert_eq!(
            process_pair_forest_deposit_with_runtime_v1(
                &program_id,
                &infos,
                &instruction,
                &Rent::default(),
                &mut runtime,
            ),
            Err(PoolV1ProgramError::TokenBalanceDeltaMismatch.into())
        );
        drop(infos);
        assert_eq!(runtime.calls, 1);
        assert_eq!(bad_delta[1].data, lane_before);
        assert_eq!(bad_delta[2].data, page_before);

        let (mut aliased, instruction, _, _) = genesis_deposit_fixture(program_id, mint);
        aliased[4].key = aliased[6].key;
        let lane_before = aliased[1].data.clone();
        let page_before = aliased[2].data.clone();
        let infos: Vec<_> = aliased.iter_mut().map(TestAccount::info).collect();
        let mut runtime = DepositCpi {
            apply_exact_delta: true,
            calls: 0,
        };
        assert_eq!(
            process_pair_forest_deposit_with_runtime_v1(
                &program_id,
                &infos,
                &instruction,
                &Rent::default(),
                &mut runtime,
            ),
            Err(ProgramError::InvalidArgument)
        );
        drop(infos);
        assert_eq!(runtime.calls, 0);
        assert_eq!(aliased[1].data, lane_before);
        assert_eq!(aliased[2].data, page_before);

        let (mut wrong_lane, instruction, lane_id, _) = genesis_deposit_fixture(program_id, mint);
        wrong_lane[1].key = pool_v1_pair_forest_lane_address(
            &program_id,
            &wrong_lane[0].key,
            lane_id.wrapping_add(1) & 7,
        )
        .unwrap()
        .0;
        let lane_before = wrong_lane[1].data.clone();
        let page_before = wrong_lane[2].data.clone();
        let infos: Vec<_> = wrong_lane.iter_mut().map(TestAccount::info).collect();
        let mut runtime = DepositCpi {
            apply_exact_delta: true,
            calls: 0,
        };
        assert!(process_pair_forest_deposit_with_runtime_v1(
            &program_id,
            &infos,
            &instruction,
            &Rent::default(),
            &mut runtime,
        )
        .is_err());
        drop(infos);
        assert_eq!(runtime.calls, 0);
        assert_eq!(wrong_lane[1].data, lane_before);
        assert_eq!(wrong_lane[2].data, page_before);
    }

    #[test]
    fn vault_deposit_rollover_preserves_full_history_and_starts_next_page() {
        let program_id = Pubkey::new_unique();
        let mint = Pubkey::new_unique();
        let (mut accounts, instruction, lane_id, _) = genesis_deposit_fixture(program_id, mint);
        let mut lane = genesis_lane_state(&accounts[0].key, lane_id);
        let mut roots = Vec::with_capacity(POOL_V1_ROOT_HISTORY_CAPACITY);
        roots.push(lane.tree.root);
        for index in 0..POOL_V1_ROOT_HISTORY_CAPACITY - 1 {
            let pair = PoolV1PairLeafWitnessV1::single_output(digest(20_000 + index as u32))
                .unwrap()
                .leaf_digest()
                .unwrap();
            lane.tree = lane
                .tree
                .append_one_with_empty_roots(pair, &POOL_V1_PAIR_EMPTY_ROOTS)
                .unwrap()
                .0;
            roots.push(lane.tree.root);
        }
        assert_eq!(lane.tree.next_leaf_index, 255);
        accounts[1].data =
            encode_pool_v1_pair_forest_lane_state_v1(&lane, &POOL_V1_PAIR_EMPTY_ROOTS)
                .unwrap()
                .to_vec();
        accounts[2].writable = false;
        let lane_key = accounts[1].key;
        write_new_page_unchecked(&mut accounts[2].data, &lane_key, 0, 0, &roots);
        let current_page_before = accounts[2].data.clone();
        accounts.insert(
            3,
            TestAccount {
                key: pool_v1_root_page_address(&program_id, &accounts[1].key, 1).0,
                owner: program_id,
                lamports: rent_lamports(POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES),
                data: vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES],
                signer: false,
                writable: true,
                executable: false,
            },
        );
        let mut runtime = DepositCpi {
            apply_exact_delta: true,
            calls: 0,
        };
        let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
        process_pair_forest_deposit_with_runtime_v1(
            &program_id,
            &infos,
            &instruction,
            &Rent::default(),
            &mut runtime,
        )
        .unwrap();
        drop(infos);
        assert_eq!(runtime.calls, 1);
        assert_eq!(accounts[2].data, current_page_before);
        let lane =
            decode_pool_v1_pair_forest_lane_state_v1(&accounts[1].data, &POOL_V1_PAIR_EMPTY_ROOTS)
                .unwrap();
        assert_eq!(lane.tree.next_leaf_index, 256);
        let next_header = validate_root_page_bytes(&accounts[3].data, &accounts[1].key, 1).unwrap();
        assert_eq!(next_header.first_sequence, 256);
        assert_eq!(next_header.filled, 1);
        assert_eq!(
            read_retained_root(&accounts[3].data, next_header, 256).unwrap(),
            lane.tree.root
        );
    }

    #[test]
    fn initialize_rejects_underfunded_or_aliased_accounts_before_writes() {
        let program_id = Pubkey::new_unique();
        let mint = Pubkey::new_unique();
        let instruction =
            encode_pair_forest_initialize_instruction_v1(&forest_initialization(mint)).unwrap();

        let mut underfunded = initialization_accounts(program_id, mint);
        underfunded[0].lamports =
            rent_lamports(POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES).saturating_sub(1);
        let infos: Vec<_> = underfunded.iter_mut().map(TestAccount::info).collect();
        assert!(process_pair_forest_initialize_with_runtime_v1(
            &program_id,
            &infos,
            &instruction,
            &Rent::default(),
            &mut NoCpi,
        )
        .is_err());
        drop(infos);
        assert!(underfunded[..9]
            .iter()
            .all(|account| account.data.iter().all(|byte| *byte == 0)));

        let mut aliased = initialization_accounts(program_id, mint);
        aliased[2].key = aliased[1].key;
        let infos: Vec<_> = aliased.iter_mut().map(TestAccount::info).collect();
        assert_eq!(
            process_pair_forest_initialize_with_runtime_v1(
                &program_id,
                &infos,
                &instruction,
                &Rent::default(),
                &mut NoCpi,
            ),
            Err(ProgramError::InvalidArgument)
        );
        drop(infos);
        assert!(aliased[..9]
            .iter()
            .all(|account| account.data.iter().all(|byte| *byte == 0)));
    }

    #[test]
    fn checkpoint_computes_root_writes_only_checkpoint_and_master_and_rejects_no_progress() {
        let program_id = Pubkey::new_unique();
        let mint = Pubkey::new_unique();
        let initialization = forest_initialization(mint);
        let initialize_instruction =
            encode_pair_forest_initialize_instruction_v1(&initialization).unwrap();
        let mut initialized = initialization_accounts(program_id, mint);
        let infos: Vec<_> = initialized.iter_mut().map(TestAccount::info).collect();
        process_pair_forest_initialize_with_runtime_v1(
            &program_id,
            &infos,
            &initialize_instruction,
            &Rent::default(),
            &mut NoCpi,
        )
        .unwrap();
        drop(infos);

        let master_key = initialized[0].key;
        let checkpoint_key = pool_v1_pair_forest_checkpoint_address(&program_id, &master_key, 0).0;
        let mut checkpoint_accounts = initialized[..9].to_vec();
        for lane in &mut checkpoint_accounts[1..9] {
            lane.writable = false;
        }
        checkpoint_accounts.push(TestAccount {
            key: checkpoint_key,
            owner: program_id,
            lamports: rent_lamports(POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES),
            data: vec![0u8; POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES],
            signer: false,
            writable: true,
            executable: false,
        });
        checkpoint_accounts.push(initialized[12].clone());
        checkpoint_accounts.push(initialized[13].clone());
        let lanes_before: [Vec<u8>; 8] =
            core::array::from_fn(|lane| checkpoint_accounts[1 + lane].data.clone());
        let instruction = encode_pair_forest_checkpoint_instruction_v1();
        let infos: Vec<_> = checkpoint_accounts
            .iter_mut()
            .map(TestAccount::info)
            .collect();
        process_pair_forest_checkpoint_with_runtime_v1(
            &program_id,
            &infos,
            &instruction,
            &Rent::default(),
            &mut NoCpi,
        )
        .unwrap();
        drop(infos);

        let master = decode_pool_v1_pair_forest_master_v1(&checkpoint_accounts[0].data).unwrap();
        assert!(master.has_checkpoint);
        assert_eq!(master.next_checkpoint_sequence, 1);
        let checkpoint =
            decode_pool_v1_pair_forest_checkpoint_v1(&checkpoint_accounts[9].data).unwrap();
        assert_eq!(checkpoint.master, master_key.to_bytes());
        assert_eq!(checkpoint.checkpoint_sequence, 0);
        assert_eq!(checkpoint.lane_sequences, [0u64; 8]);
        let roots = core::array::from_fn(|lane| {
            decode_pool_v1_pair_forest_lane_state_v1(
                &checkpoint_accounts[1 + lane].data,
                &POOL_V1_PAIR_EMPTY_ROOTS,
            )
            .unwrap()
            .tree
            .root
        });
        assert_eq!(
            checkpoint.global_root,
            pool_v1_pair_forest_global_root_v1(&roots)
        );
        for lane in 0..8 {
            assert_eq!(checkpoint_accounts[1 + lane].data, lanes_before[lane]);
        }

        let lane = 3usize;
        let mut advanced = decode_pool_v1_pair_forest_lane_state_v1(
            &checkpoint_accounts[1 + lane].data,
            &POOL_V1_PAIR_EMPTY_ROOTS,
        )
        .unwrap();
        advanced.tree = advanced
            .tree
            .append_one_with_empty_roots(digest(900), &POOL_V1_PAIR_EMPTY_ROOTS)
            .unwrap()
            .0;
        checkpoint_accounts[1 + lane].data =
            encode_pool_v1_pair_forest_lane_state_v1(&advanced, &POOL_V1_PAIR_EMPTY_ROOTS)
                .unwrap()
                .to_vec();

        let next_key = pool_v1_pair_forest_checkpoint_address(&program_id, &master_key, 1).0;
        checkpoint_accounts[9] = TestAccount {
            key: next_key,
            owner: program_id,
            lamports: rent_lamports(POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES),
            data: vec![0u8; POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES],
            signer: false,
            writable: true,
            executable: false,
        };
        let infos: Vec<_> = checkpoint_accounts
            .iter_mut()
            .map(TestAccount::info)
            .collect();
        process_pair_forest_checkpoint_with_runtime_v1(
            &program_id,
            &infos,
            &instruction,
            &Rent::default(),
            &mut NoCpi,
        )
        .unwrap();
        drop(infos);
        let master = decode_pool_v1_pair_forest_master_v1(&checkpoint_accounts[0].data).unwrap();
        assert_eq!(master.next_checkpoint_sequence, 2);
        let checkpoint =
            decode_pool_v1_pair_forest_checkpoint_v1(&checkpoint_accounts[9].data).unwrap();
        assert_eq!(checkpoint.checkpoint_sequence, 1);
        assert_eq!(checkpoint.lane_sequences[lane], 1);

        let no_progress_key = pool_v1_pair_forest_checkpoint_address(&program_id, &master_key, 2).0;
        checkpoint_accounts[9] = TestAccount {
            key: no_progress_key,
            owner: program_id,
            lamports: rent_lamports(POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES),
            data: vec![0u8; POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES],
            signer: false,
            writable: true,
            executable: false,
        };
        let master_before = checkpoint_accounts[0].data.clone();
        let infos: Vec<_> = checkpoint_accounts
            .iter_mut()
            .map(TestAccount::info)
            .collect();
        assert!(process_pair_forest_checkpoint_with_runtime_v1(
            &program_id,
            &infos,
            &instruction,
            &Rent::default(),
            &mut NoCpi,
        )
        .is_err());
        drop(infos);
        assert_eq!(checkpoint_accounts[0].data, master_before);
        assert!(checkpoint_accounts[9].data.iter().all(|byte| *byte == 0));
    }

    #[test]
    fn canonical_pdas_are_stable_distinct_and_lane_local_history_is_disjoint() {
        let program_id = Pubkey::new_unique();
        let mint = Pubkey::new_unique();
        let master = pool_v1_pair_forest_master_address(&program_id, &mint).0;
        let mut seen = std::collections::HashSet::new();
        for lane in 0..8u8 {
            let address = pool_v1_pair_forest_lane_address(&program_id, &master, lane)
                .unwrap()
                .0;
            assert!(seen.insert(address));
            assert_eq!(
                pool_v1_pair_forest_lane_root_page_address(&program_id, &master, lane, 0)
                    .unwrap()
                    .0,
                pool_v1_root_page_address(&program_id, &address, 0).0
            );
        }
        assert_eq!(
            pool_v1_pair_forest_lane_address(&program_id, &master, 8),
            Err(ProgramError::InvalidSeeds)
        );
    }

    #[test]
    fn fixed_order_snapshot_plans_exact_images_without_mutation() {
        let program_id = Pubkey::new_unique();
        let (mut master, mut lanes, mut checkpoint, master_key) = fixtures(program_id);
        let master_before = master.data.clone();
        let lane_before: [Vec<u8>; 8] = core::array::from_fn(|lane| lanes[lane].data.clone());
        let checkpoint_before = checkpoint.data.clone();
        let master_info = master.info();
        let lane_infos: Vec<_> = lanes.iter_mut().map(TestAccount::info).collect();
        let checkpoint_info = checkpoint.info();
        let plan = plan_pair_forest_checkpoint_accounts_v1(
            &program_id,
            &master_info,
            &lane_infos,
            &checkpoint_info,
        )
        .unwrap();
        assert_eq!(plan.master, master_key);
        assert_eq!(plan.checkpoint, *checkpoint_info.key);
        assert_eq!(plan.lane_sequences, [0u64; 8]);
        assert_eq!(
            decode_pool_v1_pair_forest_checkpoint_v1(&plan.checkpoint_image)
                .unwrap()
                .global_root,
            pool_v1_pair_forest_global_root_v1(&core::array::from_fn(|_| {
                POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH]
            }))
        );
        drop((master_info, lane_infos, checkpoint_info));
        assert_eq!(master.data, master_before);
        assert_eq!(checkpoint.data, checkpoint_before);
        for lane in 0..8 {
            assert_eq!(lanes[lane].data, lane_before[lane]);
        }
    }

    #[test]
    fn swapped_aliased_writable_and_wrong_pda_lanes_fail_closed() {
        let program_id = Pubkey::new_unique();
        let (mut master, mut lanes, mut checkpoint, _) = fixtures(program_id);
        let master_info = master.info();
        let lane_infos: Vec<_> = lanes.iter_mut().map(TestAccount::info).collect();
        let checkpoint_info = checkpoint.info();

        let mut swapped = lane_infos.clone();
        swapped.swap(0, 1);
        assert!(plan_pair_forest_checkpoint_accounts_v1(
            &program_id,
            &master_info,
            &swapped,
            &checkpoint_info
        )
        .is_err());

        let mut aliased = lane_infos.clone();
        aliased[1] = aliased[0].clone();
        assert_eq!(
            plan_pair_forest_checkpoint_accounts_v1(
                &program_id,
                &master_info,
                &aliased,
                &checkpoint_info
            ),
            Err(ProgramError::InvalidArgument)
        );

        let mut writable = lane_infos.clone();
        writable[0].is_writable = true;
        assert!(plan_pair_forest_checkpoint_accounts_v1(
            &program_id,
            &master_info,
            &writable,
            &checkpoint_info
        )
        .is_err());

        let mut wrong_pda = lane_infos.clone();
        let wrong_key = Pubkey::new_unique();
        wrong_pda[0].key = &wrong_key;
        assert!(plan_pair_forest_checkpoint_accounts_v1(
            &program_id,
            &master_info,
            &wrong_pda,
            &checkpoint_info
        )
        .is_err());
    }

    #[test]
    fn occupied_checkpoint_and_wrong_master_fail_before_any_write() {
        let program_id = Pubkey::new_unique();
        let (mut master, mut lanes, mut checkpoint, _) = fixtures(program_id);
        checkpoint.data[0] = 1;
        let before = checkpoint.data.clone();
        let master_info = master.info();
        let lane_infos: Vec<_> = lanes.iter_mut().map(TestAccount::info).collect();
        let checkpoint_info = checkpoint.info();
        assert!(plan_pair_forest_checkpoint_accounts_v1(
            &program_id,
            &master_info,
            &lane_infos,
            &checkpoint_info
        )
        .is_err());
        drop((master_info, lane_infos, checkpoint_info));
        assert_eq!(checkpoint.data, before);
    }

    #[test]
    fn one_terminal_transfer_updates_only_selected_lane_history_and_marker() {
        let program_id = Pubkey::new_unique();
        let mint = Pubkey::new_unique();
        let (master_key, mut master_state) = master(program_id, mint);
        master_state.identity.token_program = LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes();
        master_state.has_checkpoint = true;
        master_state.next_checkpoint_sequence = 1;
        let nullifier = digest(1);
        let lane_id =
            aspis_statement::pool_v1::pool_v1_pair_forest_output_lane_v1(&nullifier).unwrap();
        let lane_key = pool_v1_pair_forest_lane_address(&program_id, &master_key, lane_id)
            .unwrap()
            .0;
        let lane = genesis_lane_state(&master_key, lane_id);
        let (next_tree, _) = lane
            .tree
            .append_one_with_empty_roots(digest(9_000), &POOL_V1_PAIR_EMPTY_ROOTS)
            .unwrap();
        let checkpoint = PoolV1PairForestCheckpointV1 {
            master: master_key.to_bytes(),
            deployment_domain: master_state.identity.deployment_domain,
            checkpoint_sequence: 0,
            global_root: digest(7_000),
            lane_sequences: [0; 8],
        };
        let checkpoint_key = pool_v1_pair_forest_checkpoint_address(&program_id, &master_key, 0).0;
        let request = PoolV1PairForestTerminalRequestV1 {
            verifier_profile: [31; 32],
            verifier_release: [32; 32],
            pool_program: program_id.to_bytes(),
            public: PoolV1PairForestTerminalPaymentV1::PrivateTransfer(
                PoolV1PrivateTransferPublicV1 {
                    pool: master_key.to_bytes(),
                    deployment_domain: master_state.identity.deployment_domain,
                    anchor_sequence: 0,
                    anchor_root: checkpoint.global_root,
                    nullifier,
                    asset_id: master_state.identity.asset_id,
                    recipient_commitment: digest(100),
                    change_commitment: digest(200),
                },
            ),
        };
        let instruction = encode_pool_v1_pair_forest_terminal_request_v1(&request).unwrap();
        let result = PoolV1PairForestTerminalResultV1 {
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            master_account: master_key.to_bytes(),
            selected_lane_account: lane_key.to_bytes(),
            output_lane: lane_id,
            nullifier,
            verified_afterstate: PoolV1PairVerifiedAfterstateV1 {
                next_pair_index: next_tree.next_leaf_index,
                next_root: next_tree.root,
                next_frontier: next_tree.frontier,
            },
        };
        let marker_key = crate::pool_v1_nullifier_marker_address(
            &program_id,
            &master_key,
            &aspis_statement::encode_digest_canonical(&nullifier),
        )
        .unwrap()
        .0;
        let page_key =
            pool_v1_pair_forest_lane_root_page_address(&program_id, &master_key, lane_id, 0)
                .unwrap()
                .0;
        let mut accounts = vec![
            TestAccount {
                key: master_key,
                owner: program_id,
                lamports: 1,
                data: encode_pool_v1_pair_forest_master_v1(&master_state)
                    .unwrap()
                    .to_vec(),
                signer: false,
                writable: false,
                executable: false,
            },
            TestAccount {
                key: checkpoint_key,
                owner: program_id,
                lamports: 1,
                data: encode_pool_v1_pair_forest_checkpoint_v1(&checkpoint)
                    .unwrap()
                    .to_vec(),
                signer: false,
                writable: false,
                executable: false,
            },
            TestAccount {
                key: lane_key,
                owner: program_id,
                lamports: 1,
                data: encode_pool_v1_pair_forest_lane_state_v1(&lane, &POOL_V1_PAIR_EMPTY_ROOTS)
                    .unwrap()
                    .to_vec(),
                signer: false,
                writable: true,
                executable: false,
            },
            TestAccount {
                key: page_key,
                owner: program_id,
                lamports: 1,
                data: vec![0; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES],
                signer: false,
                writable: true,
                executable: false,
            },
            TestAccount {
                key: marker_key,
                owner: program_id,
                lamports: 1,
                data: vec![0; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES],
                signer: false,
                writable: true,
                executable: false,
            },
            TestAccount {
                key: Pubkey::new_unique(),
                owner: Pubkey::new_unique(),
                lamports: 1,
                data: vec![],
                signer: false,
                writable: false,
                executable: false,
            },
            TestAccount {
                key: Pubkey::new_unique(),
                owner: Pubkey::new_unique(),
                lamports: 1,
                data: vec![],
                signer: false,
                writable: false,
                executable: false,
            },
            TestAccount {
                key: Pubkey::new_unique(),
                owner: bpf_loader::id(),
                lamports: 1,
                data: vec![],
                signer: false,
                writable: false,
                executable: true,
            },
            TestAccount {
                key: Pubkey::new_unique(),
                owner: Pubkey::new_unique(),
                lamports: 1,
                data: vec![],
                signer: false,
                writable: false,
                executable: false,
            },
        ];
        let mut bad_requests = Vec::new();
        let mut wrong = request;
        wrong.pool_program[0] ^= 1;
        bad_requests.push(wrong);
        let mut wrong = request;
        if let PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) = &mut wrong.public {
            public.pool[0] ^= 1;
        }
        bad_requests.push(wrong);
        let mut wrong = request;
        if let PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) = &mut wrong.public {
            public.deployment_domain[0] ^= 1;
        }
        bad_requests.push(wrong);
        let mut wrong = request;
        if let PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) = &mut wrong.public {
            public.anchor_root[0] = public.anchor_root[0].add(M31::ONE);
        }
        bad_requests.push(wrong);
        let mut wrong = request;
        if let PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) = &mut wrong.public {
            public.asset_id = public.asset_id.add(M31::ONE);
        }
        bad_requests.push(wrong);
        for bad in bad_requests {
            let bad_instruction = encode_pool_v1_pair_forest_terminal_request_v1(&bad).unwrap();
            let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
            assert!(process_pair_forest_terminal_with_verifier_v1(
                &program_id,
                &infos,
                &bad_instruction,
                1,
                &mut NoCpi,
                |_, _, _, _, _, _, _, _, _, _| panic!("bad request reached verifier"),
                |_| {},
            )
            .is_err());
        }
        let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
        let mut no_cpi = NoCpi;
        process_pair_forest_terminal_with_verifier_v1(
            &program_id,
            &infos,
            &instruction,
            1,
            &mut no_cpi,
            |_, _, _, _, _, _, _, _, got, _| {
                assert_eq!(got, &request);
                Ok(AuthenticatedPairForestResultV1::for_test(result))
            },
            |_| {},
        )
        .unwrap();
        drop(infos);
        let written_lane =
            decode_pool_v1_pair_forest_lane_state_v1(&accounts[2].data, &POOL_V1_PAIR_EMPTY_ROOTS)
                .unwrap();
        assert_eq!(written_lane.tree, next_tree);
        assert!(accounts[4].data.iter().any(|byte| *byte != 0));
        assert_eq!(
            decode_pool_v1_pair_forest_master_v1(&accounts[0].data).unwrap(),
            master_state
        );

        let before = accounts
            .iter()
            .map(|account| account.data.clone())
            .collect::<Vec<_>>();
        let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
        assert!(process_pair_forest_terminal_with_verifier_v1(
            &program_id,
            &infos,
            &instruction,
            2,
            &mut no_cpi,
            |_, _, _, _, _, _, _, _, _, _| panic!("stale replay reached verifier"),
            |_| {},
        )
        .is_err());
        drop(infos);
        assert_eq!(
            accounts
                .iter()
                .map(|account| account.data.clone())
                .collect::<Vec<_>>(),
            before
        );
    }

    #[test]
    fn one_terminal_withdrawal_checks_custody_delta_and_failure_precedes_pool_writes() {
        let program_id = Pubkey::new_unique();
        let mint = Pubkey::new_unique();
        let (master_key, mut master_state) = master(program_id, mint);
        master_state.identity.asset_mint = mint.to_bytes();
        master_state.identity.token_program = LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes();
        master_state.has_checkpoint = true;
        master_state.next_checkpoint_sequence = 1;
        let nullifier = digest(2);
        let lane_id =
            aspis_statement::pool_v1::pool_v1_pair_forest_output_lane_v1(&nullifier).unwrap();
        let lane_key = pool_v1_pair_forest_lane_address(&program_id, &master_key, lane_id)
            .unwrap()
            .0;
        let lane = genesis_lane_state(&master_key, lane_id);
        let (next_tree, _) = lane
            .tree
            .append_one_with_empty_roots(digest(9_100), &POOL_V1_PAIR_EMPTY_ROOTS)
            .unwrap();
        let checkpoint = PoolV1PairForestCheckpointV1 {
            master: master_key.to_bytes(),
            deployment_domain: master_state.identity.deployment_domain,
            checkpoint_sequence: 0,
            global_root: digest(7_100),
            lane_sequences: [0; 8],
        };
        let checkpoint_key = pool_v1_pair_forest_checkpoint_address(&program_id, &master_key, 0).0;
        let destination = Pubkey::new_unique();
        let request = PoolV1PairForestTerminalRequestV1 {
            verifier_profile: [41; 32],
            verifier_release: [42; 32],
            pool_program: program_id.to_bytes(),
            public: PoolV1PairForestTerminalPaymentV1::Withdrawal(PoolV1WithdrawalPublicV1 {
                pool: master_key.to_bytes(),
                deployment_domain: master_state.identity.deployment_domain,
                anchor_sequence: 0,
                anchor_root: checkpoint.global_root,
                nullifier,
                asset_id: master_state.identity.asset_id,
                amount: 25,
                destination_token_account: destination.to_bytes(),
                change_commitment: digest(300),
            }),
        };
        let result = PoolV1PairForestTerminalResultV1 {
            transition_kind: PoolV1TransitionKind::Withdrawal,
            master_account: master_key.to_bytes(),
            selected_lane_account: lane_key.to_bytes(),
            output_lane: lane_id,
            nullifier,
            verified_afterstate: PoolV1PairVerifiedAfterstateV1 {
                next_pair_index: next_tree.next_leaf_index,
                next_root: next_tree.root,
                next_frontier: next_tree.frontier,
            },
        };
        let marker_key = crate::pool_v1_nullifier_marker_address(
            &program_id,
            &master_key,
            &aspis_statement::encode_digest_canonical(&nullifier),
        )
        .unwrap()
        .0;
        let mut accounts = terminal_base_accounts(
            program_id,
            master_key,
            &master_state,
            checkpoint_key,
            &checkpoint,
            lane_key,
            &lane,
            marker_key,
        );
        let authority = crate::pool_v1_vault_authority_address(&program_id, &master_key).0;
        accounts.extend([
            TestAccount {
                key: mint,
                owner: LEGACY_SPL_TOKEN_PROGRAM_ID,
                lamports: 1,
                data: initialized_mint_data(),
                signer: false,
                writable: false,
                executable: false,
            },
            TestAccount {
                key: crate::pool_v1_vault_token_account_address(&program_id, &master_key).0,
                owner: LEGACY_SPL_TOKEN_PROGRAM_ID,
                lamports: 1,
                data: initialized_token_data(mint, authority, 100),
                signer: false,
                writable: true,
                executable: false,
            },
            TestAccount {
                key: destination,
                owner: LEGACY_SPL_TOKEN_PROGRAM_ID,
                lamports: 1,
                data: initialized_token_data(mint, Pubkey::new_unique(), 10),
                signer: false,
                writable: true,
                executable: false,
            },
            TestAccount {
                key: authority,
                owner: system_program::id(),
                lamports: 0,
                data: vec![],
                signer: false,
                writable: false,
                executable: false,
            },
            TestAccount {
                key: LEGACY_SPL_TOKEN_PROGRAM_ID,
                owner: native_loader::id(),
                lamports: 1,
                data: vec![],
                signer: false,
                writable: false,
                executable: true,
            },
        ]);
        let instruction = encode_pool_v1_pair_forest_terminal_request_v1(&request).unwrap();
        let before = accounts
            .iter()
            .map(|account| account.data.clone())
            .collect::<Vec<_>>();
        let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
        let mut failing = WithdrawalCpi {
            fail: true,
            calls: 0,
        };
        assert!(process_pair_forest_terminal_with_verifier_v1(
            &program_id,
            &infos,
            &instruction,
            1,
            &mut failing,
            |_, _, _, _, _, _, _, _, _, _| Ok(AuthenticatedPairForestResultV1::for_test(result)),
            |_| {},
        )
        .is_err());
        drop(infos);
        assert_eq!(failing.calls, 1);
        assert_eq!(
            accounts.iter().map(|a| a.data.clone()).collect::<Vec<_>>(),
            before
        );

        let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
        let mut success = WithdrawalCpi {
            fail: false,
            calls: 0,
        };
        process_pair_forest_terminal_with_verifier_v1(
            &program_id,
            &infos,
            &instruction,
            1,
            &mut success,
            |_, _, _, _, _, _, _, _, _, _| Ok(AuthenticatedPairForestResultV1::for_test(result)),
            |_| {},
        )
        .unwrap();
        drop(infos);
        assert_eq!(success.calls, 1);
        assert_eq!(
            u64::from_le_bytes(accounts[10].data[64..72].try_into().unwrap()),
            75
        );
        assert_eq!(
            u64::from_le_bytes(accounts[11].data[64..72].try_into().unwrap()),
            35
        );
        assert!(accounts[4].data.iter().any(|byte| *byte != 0));
    }
}
