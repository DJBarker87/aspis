//! Production-inactive Solana account plumbing for the eight-lane pair forest.
//!
//! This module exposes no instruction and is compiled only under the explicit
//! `pair-forest-account-evidence` feature.  It authenticates canonical master,
//! lane and immutable-checkpoint PDAs, then returns byte-exact write plans.  A
//! separately reviewed caller must supply the forest global root.

use aspis_statement::{
    pool_v1::{
        decode_pool_v1_pair_forest_checkpoint_v1, decode_pool_v1_pair_forest_lane_state_v1,
        decode_pool_v1_pair_forest_master_v1, encode_pool_v1_pair_forest_checkpoint_v1,
        encode_pool_v1_pair_forest_master_v1, plan_pool_v1_pair_forest_checkpoint_v1,
        PoolV1PairForestCheckpointV1, PoolV1PairForestLaneStateV1, PoolV1PairForestMasterV1,
        POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES, POOL_V1_PAIR_FOREST_LANE_COUNT,
        POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES,
    },
    poseidon2::Digest,
};
use solana_program::{account_info::AccountInfo, program_error::ProgramError, pubkey::Pubkey};

use crate::{
    empty_roots::POOL_V1_PAIR_EMPTY_ROOTS,
    error::PoolV1ProgramError,
    history::{pool_v1_root_page_address, require_program_account},
};

pub const POOL_V1_PAIR_FOREST_MASTER_SEED: &[u8] = b"aspis-pair-forest-master-v1";
pub const POOL_V1_PAIR_FOREST_LANE_SEED: &[u8] = b"aspis-pair-forest-lane-v1";
pub const POOL_V1_PAIR_FOREST_CHECKPOINT_SEED: &[u8] = b"aspis-pair-forest-checkpoint-v1";

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
    global_root: Digest,
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
    let first_lane = decode_lane_account(program_id, master_account.key, 0, &lane_accounts[0])?;
    let mut lane_states: [PoolV1PairForestLaneStateV1; POOL_V1_PAIR_FOREST_LANE_COUNT] =
        [first_lane; POOL_V1_PAIR_FOREST_LANE_COUNT];
    for lane in 1..POOL_V1_PAIR_FOREST_LANE_COUNT {
        lane_states[lane] = decode_lane_account(
            program_id,
            master_account.key,
            lane as u8,
            &lane_accounts[lane],
        )?;
    }
    let pure = plan_pool_v1_pair_forest_checkpoint_v1(&master, &lane_states, global_root)
        .map_err(|_| PoolV1ProgramError::StateHistoryMismatch)?;
    let expected_checkpoint = pool_v1_pair_forest_checkpoint_address(
        program_id,
        master_account.key,
        pure.checkpoint.checkpoint_sequence,
    )
    .0;
    require_program_account(checkpoint_account, program_id, true)?;
    if checkpoint_account.is_signer || checkpoint_account.key != &expected_checkpoint {
        return Err(PoolV1ProgramError::InvalidFreshAccount.into());
    }
    let checkpoint_data = checkpoint_account.try_borrow_data()?;
    if checkpoint_data.len() != POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES
        || checkpoint_data.iter().any(|byte| *byte != 0)
    {
        return Err(PoolV1ProgramError::InvalidFreshAccount.into());
    }
    drop(checkpoint_data);
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
    use solana_program::clock::Epoch;

    use super::*;

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
            digest(100),
        )
        .unwrap();
        assert_eq!(plan.master, master_key);
        assert_eq!(plan.checkpoint, *checkpoint_info.key);
        assert_eq!(plan.lane_sequences, [0u64; 8]);
        assert_eq!(
            decode_pool_v1_pair_forest_checkpoint_v1(&plan.checkpoint_image)
                .unwrap()
                .global_root,
            digest(100)
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
            &checkpoint_info,
            digest(1)
        )
        .is_err());

        let mut aliased = lane_infos.clone();
        aliased[1] = aliased[0].clone();
        assert_eq!(
            plan_pair_forest_checkpoint_accounts_v1(
                &program_id,
                &master_info,
                &aliased,
                &checkpoint_info,
                digest(1)
            ),
            Err(ProgramError::InvalidArgument)
        );

        let mut writable = lane_infos.clone();
        writable[0].is_writable = true;
        assert!(plan_pair_forest_checkpoint_accounts_v1(
            &program_id,
            &master_info,
            &writable,
            &checkpoint_info,
            digest(1)
        )
        .is_err());

        let mut wrong_pda = lane_infos.clone();
        let wrong_key = Pubkey::new_unique();
        wrong_pda[0].key = &wrong_key;
        assert!(plan_pair_forest_checkpoint_accounts_v1(
            &program_id,
            &master_info,
            &wrong_pda,
            &checkpoint_info,
            digest(1)
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
            &checkpoint_info,
            digest(1)
        )
        .is_err());
        drop((master_info, lane_infos, checkpoint_info));
        assert_eq!(checkpoint.data, before);
    }
}
