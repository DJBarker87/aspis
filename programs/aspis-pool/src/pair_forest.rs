//! Production-inactive Solana account plumbing for the eight-lane pair forest.
//!
//! This module is compiled only under the explicit
//! `pair-forest-account-evidence` feature. It defines exact initialization and
//! permissionless checkpoint instructions, but no spend instruction. The
//! checkpoint reads all eight lane PDAs in one invocation and computes the
//! seven frozen Pool Poseidon parents internally.

extern crate alloc;

use alloc::{boxed::Box, vec::Vec};

use aspis_statement::{
    pool_v1::{
        decode_pool_v1_pair_forest_checkpoint_v1, decode_pool_v1_pair_forest_lane_state_v1,
        decode_pool_v1_pair_forest_master_v1, encode_pool_v1_pair_forest_checkpoint_v1,
        encode_pool_v1_pair_forest_lane_state_v1, encode_pool_v1_pair_forest_master_v1,
        plan_pool_v1_pair_forest_checkpoint_v1, pool_v1_tree_parent, IncrementalMerkleTreeV1,
        PoolIdentityV1, PoolV1PairForestCheckpointV1, PoolV1PairForestLaneStateV1,
        PoolV1PairForestMasterV1, POOL_V1_DIGEST_ENCODING_VERSION,
        POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES, POOL_V1_PAIR_FOREST_LANE_COUNT,
        POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES, POOL_V1_PAIR_TREE_DEPTH,
    },
    poseidon2::Digest,
};
use solana_program::{
    account_info::AccountInfo, entrypoint::ProgramResult, program_error::ProgramError,
    pubkey::Pubkey, rent::Rent,
};

use crate::{
    empty_roots::POOL_V1_PAIR_EMPTY_ROOTS,
    error::PoolV1ProgramError,
    history::{pool_v1_root_page_address, require_program_account},
    instruction::{
        decode_initialize_instruction_v1, encode_initialize_instruction_v1,
        PoolInstructionFormatErrorV1, POOL_V1_INITIALIZE_INSTRUCTION_BYTES,
        POOL_V1_INITIALIZE_INSTRUCTION_MAGIC, POOL_V1_INSTRUCTION_VERSION,
    },
    processor::{
        create_or_allocate_pda, plan_fresh_program_pda, require_payer_and_system_program,
        require_unique_accounts, FreshPdaPreparationV1, PoolCpiRuntimeV1,
    },
    state::PoolInitializationV1,
    vault::{
        parse_legacy_mint_v1, LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES, LEGACY_SPL_TOKEN_PROGRAM_ID,
    },
};

pub const POOL_V1_PAIR_FOREST_MASTER_SEED: &[u8] = b"aspis-pair-forest-master-v1";
pub const POOL_V1_PAIR_FOREST_LANE_SEED: &[u8] = b"aspis-pair-forest-lane-v1";
pub const POOL_V1_PAIR_FOREST_CHECKPOINT_SEED: &[u8] = b"aspis-pair-forest-checkpoint-v1";

pub const POOL_V1_PAIR_FOREST_INITIALIZE_INSTRUCTION_MAGIC: [u8; 4] = *b"AS8I";
pub const POOL_V1_PAIR_FOREST_CHECKPOINT_INSTRUCTION_MAGIC: [u8; 4] = *b"AS8C";
pub const POOL_V1_PAIR_FOREST_CHECKPOINT_INSTRUCTION_BYTES: usize = 8;
pub const POOL_V1_PAIR_FOREST_INITIALIZE_ACCOUNT_COUNT: usize = 12;
pub const POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_COUNT: usize = 12;

const FOREST_MASTER_ACCOUNT_INDEX: usize = 0;
const FOREST_FIRST_LANE_ACCOUNT_INDEX: usize = 1;
const FOREST_MINT_OR_CHECKPOINT_ACCOUNT_INDEX: usize = 9;
const FOREST_PAYER_ACCOUNT_INDEX: usize = 10;
const FOREST_SYSTEM_ACCOUNT_INDEX: usize = 11;

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
) -> Result<PoolV1PairForestLaneStateV1, ProgramError> {
    require_program_account(account, program_id, false)?;
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

/// Initialize `[master, lane_0, ..., lane_7, mint, payer, system_program]`.
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
    let payer = &accounts[FOREST_PAYER_ACCOUNT_INDEX];
    let system_program_account = &accounts[FOREST_SYSTEM_ACCOUNT_INDEX];
    require_payer_and_system_program(payer, system_program_account)?;
    require_forest_mint_account(&initialization, mint)?;

    let (expected_master, master_bump) = pool_v1_pair_forest_master_address(program_id, mint.key);
    let master_preparation = plan_fresh_program_pda(
        master,
        program_id,
        &expected_master,
        POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES,
    )?;
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

    // Acquire every mutable borrow before the first write. Runtime rollback
    // remains the outer atomicity boundary for preceding System CPIs.
    let mut master_data = master.try_borrow_mut_data()?;
    let mut lane_data = Vec::with_capacity(POOL_V1_PAIR_FOREST_LANE_COUNT);
    for lane in lanes {
        lane_data.push(lane.try_borrow_mut_data()?);
    }
    master_data.copy_from_slice(&master_image);
    for lane in 0..POOL_V1_PAIR_FOREST_LANE_COUNT {
        let image = encode_pool_v1_pair_forest_lane_state_v1(
            &genesis_lane_state(&expected_master, lane as u8),
            &POOL_V1_PAIR_EMPTY_ROOTS,
        )
        .map_err(|_| PoolV1ProgramError::StateHistoryMismatch)?;
        lane_data[lane].copy_from_slice(&image);
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
    let payer = &accounts[FOREST_PAYER_ACCOUNT_INDEX];
    let system_program_account = &accounts[FOREST_SYSTEM_ACCOUNT_INDEX];
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
        encode_pool_v1_pair_forest_lane_state_v1, encode_pool_v1_pair_forest_master_v1,
        IncrementalMerkleTreeV1, PoolIdentityV1, VerifierPolicyV1,
        POOL_V1_PAIR_FOREST_ALL_LANES_MASK, POOL_V1_PAIR_TREE_DEPTH,
    };
    use solana_program::{clock::Epoch, instruction::Instruction};
    use solana_sdk_ids::{native_loader, system_program};

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

    fn rent_lamports(bytes: usize) -> u64 {
        Rent::default().minimum_balance(bytes).max(1)
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
        checkpoint_accounts.push(initialized[10].clone());
        checkpoint_accounts.push(initialized[11].clone());
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
}
