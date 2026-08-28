//! Default-off client builders for the committed eight-lane Pool instructions.
//!
//! Every wire is produced by the Pool crate's exact encoder and every
//! Pool-owned account is derived from the caller-pinned program id.  This
//! module deliberately stops before the unresolved proof-verifier CPI: the
//! profile selector only authenticates the finalized registry inputs a future
//! spend builder must consume.

use std::collections::BTreeSet;

use aspis_pool::{
    deposit::DepositRequestV1, deposit_transport::DepositInstructionFormatErrorV1,
    encode_pair_forest_checkpoint_instruction_v1, encode_pair_forest_deposit_instruction_v1,
    encode_pair_forest_initialize_instruction_v1, pool_v1_pair_forest_checkpoint_address,
    pool_v1_pair_forest_lane_address, pool_v1_pair_forest_lane_root_page_address,
    pool_v1_pair_forest_master_address, pool_v1_vault_token_account_address, PoolInitializationV1,
    PoolInstructionFormatErrorV1, LEGACY_SPL_TOKEN_PROGRAM_ID,
};
use aspis_registry::{pool_v1_verifier_entry_address, pool_v1_verifier_registry_address};
use aspis_statement::pool_v1::{
    decode_verifier_registry_entry_v1, decode_verifier_registry_v1, pool_v1_note_commitment,
    pool_v1_pair_forest_deposit_lane_v1, root_history_location, PoolV1PairForestLaneStateV1,
    PoolV1PairForestMasterV1, PoolV1VerifierRegistryFormatError, VerifierRegistryEntryV1,
    VerifierRegistryV1, POOL_V1_PAIR_CAPACITY,
};
use solana_program::{
    instruction::{AccountMeta, Instruction},
    pubkey::Pubkey,
};
use solana_sdk_ids::system_program;

use crate::{
    finalized_indexer::SolanaRpcCommitmentV1, lane_forest_rpc_v2::FinalizedForestAccountV2,
    scan_state::FinalizedChainPointV1,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PairForestClientErrorV2 {
    UnpinnedProgram,
    ZeroAccount,
    AccountAlias,
    WrongMaster,
    WrongLane,
    WrongSequence,
    TreeFull,
    MissingPayer,
    UnexpectedPayer,
    WrongAccountOwner,
    ExecutableAccount,
    WrongRegistry,
    RegistryPaused,
    ProfileInactive,
    ProfileMismatch,
    NotFinalized,
    ContextTooOld,
    ProviderMismatch,
    PoolFormat(PoolInstructionFormatErrorV1),
    DepositFormat(DepositInstructionFormatErrorV1),
    RegistryFormat(PoolV1VerifierRegistryFormatError),
}

impl From<PoolInstructionFormatErrorV1> for PairForestClientErrorV2 {
    fn from(error: PoolInstructionFormatErrorV1) -> Self {
        Self::PoolFormat(error)
    }
}

impl From<DepositInstructionFormatErrorV1> for PairForestClientErrorV2 {
    fn from(error: DepositInstructionFormatErrorV1) -> Self {
        Self::DepositFormat(error)
    }
}

impl From<PoolV1VerifierRegistryFormatError> for PairForestClientErrorV2 {
    fn from(error: PoolV1VerifierRegistryFormatError) -> Self {
        Self::RegistryFormat(error)
    }
}

fn require_program_v2(program_id: Pubkey) -> Result<(), PairForestClientErrorV2> {
    if program_id == Pubkey::default() {
        Err(PairForestClientErrorV2::UnpinnedProgram)
    } else {
        Ok(())
    }
}

fn require_nonzero_v2(address: Pubkey) -> Result<(), PairForestClientErrorV2> {
    if address == Pubkey::default() {
        Err(PairForestClientErrorV2::ZeroAccount)
    } else {
        Ok(())
    }
}

fn require_unique_v2(accounts: &[AccountMeta]) -> Result<(), PairForestClientErrorV2> {
    let mut seen = BTreeSet::new();
    if accounts
        .iter()
        .all(|account| seen.insert(account.pubkey.to_bytes()))
    {
        Ok(())
    } else {
        Err(PairForestClientErrorV2::AccountAlias)
    }
}

fn exact_master_address_v2(
    program_id: Pubkey,
    master: &PoolV1PairForestMasterV1,
) -> Result<Pubkey, PairForestClientErrorV2> {
    let mint = Pubkey::new_from_array(master.identity.asset_mint);
    let expected = pool_v1_pair_forest_master_address(&program_id, &mint).0;
    if master.identity.pool != expected.to_bytes() {
        return Err(PairForestClientErrorV2::WrongMaster);
    }
    Ok(expected)
}

/// Exact `AS8I` instruction:
/// `[master, lane_0..lane_7, mint, vault, token, payer, system]`.
pub fn build_pair_forest_initialize_instruction_v2(
    program_id: Pubkey,
    payer: Pubkey,
    initialization: &PoolInitializationV1,
) -> Result<Instruction, PairForestClientErrorV2> {
    require_program_v2(program_id)?;
    require_nonzero_v2(payer)?;
    if initialization.token_program != LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes() {
        return Err(PairForestClientErrorV2::WrongMaster);
    }
    let mint = Pubkey::new_from_array(initialization.asset_mint);
    require_nonzero_v2(mint)?;
    let master = pool_v1_pair_forest_master_address(&program_id, &mint).0;
    let mut accounts = Vec::with_capacity(14);
    accounts.push(AccountMeta::new(master, false));
    for lane_id in 0..8u8 {
        accounts.push(AccountMeta::new(
            pool_v1_pair_forest_lane_address(&program_id, &master, lane_id)
                .map_err(|_| PairForestClientErrorV2::WrongLane)?
                .0,
            false,
        ));
    }
    accounts.extend([
        AccountMeta::new_readonly(mint, false),
        AccountMeta::new(
            pool_v1_vault_token_account_address(&program_id, &master).0,
            false,
        ),
        AccountMeta::new_readonly(LEGACY_SPL_TOKEN_PROGRAM_ID, false),
        AccountMeta::new(payer, true),
        AccountMeta::new_readonly(system_program::id(), false),
    ]);
    require_unique_v2(&accounts)?;
    Ok(Instruction {
        program_id,
        accounts,
        data: encode_pair_forest_initialize_instruction_v1(initialization)?.to_vec(),
    })
}

/// Exact permissionless `AS8C` instruction:
/// `[master, lane_0..lane_7, checkpoint, payer, system]`.
pub fn build_pair_forest_checkpoint_instruction_v2(
    program_id: Pubkey,
    payer: Pubkey,
    master: &PoolV1PairForestMasterV1,
) -> Result<Instruction, PairForestClientErrorV2> {
    require_program_v2(program_id)?;
    require_nonzero_v2(payer)?;
    let master_address = exact_master_address_v2(program_id, master)?;
    let mut accounts = Vec::with_capacity(12);
    accounts.push(AccountMeta::new(master_address, false));
    for lane_id in 0..8u8 {
        accounts.push(AccountMeta::new_readonly(
            pool_v1_pair_forest_lane_address(&program_id, &master_address, lane_id)
                .map_err(|_| PairForestClientErrorV2::WrongLane)?
                .0,
            false,
        ));
    }
    accounts.extend([
        AccountMeta::new(
            pool_v1_pair_forest_checkpoint_address(
                &program_id,
                &master_address,
                master.next_checkpoint_sequence,
            )
            .0,
            false,
        ),
        AccountMeta::new(payer, true),
        AccountMeta::new_readonly(system_program::id(), false),
    ]);
    require_unique_v2(&accounts)?;
    Ok(Instruction {
        program_id,
        accounts,
        data: encode_pair_forest_checkpoint_instruction_v1().to_vec(),
    })
}

/// Exact `AS8D` builder. The authenticated lane state selects the fixed
/// same-page, genesis-page or rollover account layout.
#[allow(clippy::too_many_arguments)]
pub fn build_pair_forest_deposit_instruction_v2(
    program_id: Pubkey,
    master: &PoolV1PairForestMasterV1,
    lane: &PoolV1PairForestLaneStateV1,
    source_token_account: Pubkey,
    source_authority: Pubkey,
    page_payer: Option<Pubkey>,
    request: &DepositRequestV1<'_>,
) -> Result<Instruction, PairForestClientErrorV2> {
    require_program_v2(program_id)?;
    require_nonzero_v2(source_token_account)?;
    require_nonzero_v2(source_authority)?;
    let master_address = exact_master_address_v2(program_id, master)?;
    if lane.master != master_address.to_bytes()
        || usize::from(lane.lane_id) >= 8
        || lane.tree.next_leaf_index >= POOL_V1_PAIR_CAPACITY
    {
        return Err(if lane.tree.next_leaf_index >= POOL_V1_PAIR_CAPACITY {
            PairForestClientErrorV2::TreeFull
        } else {
            PairForestClientErrorV2::WrongLane
        });
    }
    let commitment = pool_v1_note_commitment(
        &request.owner_key,
        request.amount,
        master.identity.asset_id,
        &request.salt,
    );
    let expected_lane = pool_v1_pair_forest_deposit_lane_v1(&commitment)
        .map_err(|_| PairForestClientErrorV2::WrongLane)?;
    if expected_lane != lane.lane_id {
        return Err(PairForestClientErrorV2::WrongLane);
    }
    let next_sequence = lane
        .tree
        .next_leaf_index
        .checked_add(1)
        .ok_or(PairForestClientErrorV2::WrongSequence)?;
    let current_location = root_history_location(lane.tree.next_leaf_index);
    let next_location = root_history_location(next_sequence);
    let lane_address = pool_v1_pair_forest_lane_address(&program_id, &master_address, lane.lane_id)
        .map_err(|_| PairForestClientErrorV2::WrongLane)?
        .0;
    let current_page = pool_v1_pair_forest_lane_root_page_address(
        &program_id,
        &master_address,
        lane.lane_id,
        current_location.page_number,
    )
    .map_err(|_| PairForestClientErrorV2::WrongLane)?
    .0;
    let mint = Pubkey::new_from_array(master.identity.asset_mint);
    let vault = pool_v1_vault_token_account_address(&program_id, &master_address).0;
    let mut accounts = vec![
        AccountMeta::new_readonly(master_address, false),
        AccountMeta::new(lane_address, false),
    ];
    if lane.tree.next_leaf_index == 0 {
        let payer = page_payer.ok_or(PairForestClientErrorV2::MissingPayer)?;
        accounts.extend([
            AccountMeta::new(current_page, false),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new(source_token_account, false),
            AccountMeta::new_readonly(source_authority, true),
            AccountMeta::new(vault, false),
            AccountMeta::new_readonly(LEGACY_SPL_TOKEN_PROGRAM_ID, false),
            AccountMeta::new(payer, true),
            AccountMeta::new_readonly(system_program::id(), false),
        ]);
    } else if current_location.page_number == next_location.page_number {
        if page_payer.is_some() {
            return Err(PairForestClientErrorV2::UnexpectedPayer);
        }
        accounts.extend([
            AccountMeta::new(current_page, false),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new(source_token_account, false),
            AccountMeta::new_readonly(source_authority, true),
            AccountMeta::new(vault, false),
            AccountMeta::new_readonly(LEGACY_SPL_TOKEN_PROGRAM_ID, false),
        ]);
    } else {
        let payer = page_payer.ok_or(PairForestClientErrorV2::MissingPayer)?;
        let next_page = pool_v1_pair_forest_lane_root_page_address(
            &program_id,
            &master_address,
            lane.lane_id,
            next_location.page_number,
        )
        .map_err(|_| PairForestClientErrorV2::WrongLane)?
        .0;
        accounts.extend([
            AccountMeta::new_readonly(current_page, false),
            AccountMeta::new(next_page, false),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new(source_token_account, false),
            AccountMeta::new_readonly(source_authority, true),
            AccountMeta::new(vault, false),
            AccountMeta::new_readonly(LEGACY_SPL_TOKEN_PROGRAM_ID, false),
            AccountMeta::new(payer, true),
            AccountMeta::new_readonly(system_program::id(), false),
        ]);
    }
    require_unique_v2(&accounts)?;
    Ok(Instruction {
        program_id,
        accounts,
        data: encode_pair_forest_deposit_instruction_v1(request)?,
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PairForestSpendProfileRequestV2 {
    pub profile_binding: [u8; 32],
    pub release_binding: [u8; 32],
    pub statement_version: u8,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PairForestSpendProfileSelectionV2 {
    pub finalized_point: FinalizedChainPointV1,
    pub provider_set_digest: [u8; 32],
    pub registry_program: [u8; 32],
    pub registry_address: [u8; 32],
    pub registry_generation: u64,
    pub entry_address: [u8; 32],
    pub verifier_program: [u8; 32],
    pub profile_binding: [u8; 32],
    pub release_binding: [u8; 32],
    pub statement_version: u8,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalizedPairForestProfileAccountsV2 {
    pub point: FinalizedChainPointV1,
    pub context_slot: u64,
    pub commitment: SolanaRpcCommitmentV1,
    pub provider_set_digest: [u8; 32],
    pub registry: FinalizedForestAccountV2,
    pub entry: FinalizedForestAccountV2,
}

fn require_registry_account_v2(
    account: &FinalizedForestAccountV2,
    registry_program: Pubkey,
) -> Result<(), PairForestClientErrorV2> {
    if account.owner != registry_program.to_bytes() {
        return Err(PairForestClientErrorV2::WrongAccountOwner);
    }
    if account.executable {
        return Err(PairForestClientErrorV2::ExecutableAccount);
    }
    Ok(())
}

/// Authenticate exactly which finalized registry entry a future pair-forest
/// spend builder may use. No verifier CPI accounts or transport are created.
#[allow(clippy::too_many_arguments)]
pub fn select_pair_forest_spend_profile_v2(
    registry_program: Pubkey,
    master: &PoolV1PairForestMasterV1,
    request: PairForestSpendProfileRequestV2,
    accounts: &FinalizedPairForestProfileAccountsV2,
) -> Result<PairForestSpendProfileSelectionV2, PairForestClientErrorV2> {
    require_program_v2(registry_program)?;
    if accounts.commitment != SolanaRpcCommitmentV1::Finalized {
        return Err(PairForestClientErrorV2::NotFinalized);
    }
    if accounts.context_slot < accounts.point.slot() {
        return Err(PairForestClientErrorV2::ContextTooOld);
    }
    if accounts.provider_set_digest == [0u8; 32] {
        return Err(PairForestClientErrorV2::ProviderMismatch);
    }
    let pool = Pubkey::new_from_array(master.identity.pool);
    if master.verifier_policy.registry_program != registry_program.to_bytes()
        || request.profile_binding == [0u8; 32]
        || request.release_binding == [0u8; 32]
        || request.statement_version == 0
    {
        return Err(PairForestClientErrorV2::ProfileMismatch);
    }
    let registry_address = pool_v1_verifier_registry_address(&registry_program, &pool).0;
    let entry_address = pool_v1_verifier_entry_address(
        &registry_program,
        &pool,
        &request.profile_binding,
        &request.release_binding,
    )
    .0;
    if accounts.registry.address != registry_address.to_bytes()
        || accounts.entry.address != entry_address.to_bytes()
    {
        return Err(PairForestClientErrorV2::WrongRegistry);
    }
    require_registry_account_v2(&accounts.registry, registry_program)?;
    require_registry_account_v2(&accounts.entry, registry_program)?;
    let registry: VerifierRegistryV1 = decode_verifier_registry_v1(&accounts.registry.data)?;
    let entry: VerifierRegistryEntryV1 = decode_verifier_registry_entry_v1(&accounts.entry.data)?;
    if registry.pool != master.identity.pool
        || registry.policy_binding != master.verifier_policy.policy_binding
        || registry.authority != master.verifier_policy.registry_authority
        || entry.pool != master.identity.pool
        || entry.policy_binding != master.verifier_policy.policy_binding
    {
        return Err(PairForestClientErrorV2::ProfileMismatch);
    }
    if registry.is_paused() {
        return Err(PairForestClientErrorV2::RegistryPaused);
    }
    if !entry.is_active_at(accounts.point.slot()) {
        return Err(PairForestClientErrorV2::ProfileInactive);
    }
    if entry.profile_binding != request.profile_binding
        || entry.release_binding != request.release_binding
        || entry.statement_version != request.statement_version
    {
        return Err(PairForestClientErrorV2::ProfileMismatch);
    }
    Ok(PairForestSpendProfileSelectionV2 {
        finalized_point: accounts.point,
        provider_set_digest: accounts.provider_set_digest,
        registry_program: registry_program.to_bytes(),
        registry_address: registry_address.to_bytes(),
        registry_generation: registry.generation,
        entry_address: entry_address.to_bytes(),
        verifier_program: entry.verifier_program,
        profile_binding: entry.profile_binding,
        release_binding: entry.release_binding,
        statement_version: entry.statement_version,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::M31;
    use aspis_pool::{
        decode_pair_forest_checkpoint_instruction_v1, decode_pair_forest_deposit_instruction_v1,
        decode_pair_forest_initialize_instruction_v1, POOL_V1_PAIR_EMPTY_ROOTS,
    };
    use aspis_statement::pool_v1::{
        encode_verifier_registry_entry_v1, encode_verifier_registry_v1, IncrementalMerkleTreeV1,
        PoolIdentityV1, VerifierEntryStatusV1, VerifierPolicyV1,
        POOL_V1_PAIR_FOREST_ALL_LANES_MASK, POOL_V1_PAIR_TREE_DEPTH,
        POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
    };

    fn key(seed: u8) -> Pubkey {
        Pubkey::new_from_array([seed; 32])
    }

    fn initialization(mint: Pubkey, registry_program: Pubkey) -> PoolInitializationV1 {
        PoolInitializationV1 {
            asset_mint: mint.to_bytes(),
            token_program: LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes(),
            asset_id: M31(9),
            deployment_domain: [10; 32],
            verifier_policy: VerifierPolicyV1 {
                flags: 0,
                registry_program: registry_program.to_bytes(),
                registry_authority: [12; 32],
                policy_binding: [13; 32],
            },
        }
    }

    fn master(program: Pubkey, mint: Pubkey, registry_program: Pubkey) -> PoolV1PairForestMasterV1 {
        let init = initialization(mint, registry_program);
        PoolV1PairForestMasterV1 {
            identity: PoolIdentityV1 {
                pool: pool_v1_pair_forest_master_address(&program, &mint)
                    .0
                    .to_bytes(),
                asset_mint: init.asset_mint,
                token_program: init.token_program,
                asset_id: init.asset_id,
                deployment_domain: init.deployment_domain,
            },
            verifier_policy: init.verifier_policy,
            initialized_lane_mask: POOL_V1_PAIR_FOREST_ALL_LANES_MASK,
            has_checkpoint: false,
            next_checkpoint_sequence: 0,
            last_checkpoint_lane_sequences: [0; 8],
        }
    }

    fn lane(
        master: &PoolV1PairForestMasterV1,
        lane_id: u8,
        sequence: u64,
    ) -> PoolV1PairForestLaneStateV1 {
        let mut tree = IncrementalMerkleTreeV1 {
            next_leaf_index: 0,
            root: POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH],
            frontier: core::array::from_fn(|level| POOL_V1_PAIR_EMPTY_ROOTS[level]),
        };
        for seed in 0..sequence {
            tree = tree
                .append_one_with_empty_roots(
                    core::array::from_fn(|index| M31((seed as u32 + 2) * 17 + index as u32)),
                    &POOL_V1_PAIR_EMPTY_ROOTS,
                )
                .unwrap()
                .0;
        }
        PoolV1PairForestLaneStateV1 {
            master: master.identity.pool,
            lane_id,
            tree,
        }
    }

    #[test]
    fn init_and_checkpoint_freeze_exact_wires_pdas_and_privileges() {
        let program = key(1);
        let payer = key(2);
        let mint = key(3);
        let registry_program = key(4);
        let init = initialization(mint, registry_program);
        let initialize =
            build_pair_forest_initialize_instruction_v2(program, payer, &init).unwrap();
        assert_eq!(
            decode_pair_forest_initialize_instruction_v1(&initialize.data),
            Ok(init)
        );
        assert_eq!(initialize.accounts.len(), 14);
        assert_eq!(
            initialize.accounts[0],
            AccountMeta::new(pool_v1_pair_forest_master_address(&program, &mint).0, false)
        );
        assert_eq!(initialize.accounts[12], AccountMeta::new(payer, true));
        assert_eq!(
            initialize.accounts[13],
            AccountMeta::new_readonly(system_program::id(), false)
        );

        let state = master(program, mint, registry_program);
        let checkpoint =
            build_pair_forest_checkpoint_instruction_v2(program, payer, &state).unwrap();
        assert!(decode_pair_forest_checkpoint_instruction_v1(&checkpoint.data).is_ok());
        assert_eq!(checkpoint.accounts.len(), 12);
        assert_eq!(
            checkpoint.accounts[9],
            AccountMeta::new(
                pool_v1_pair_forest_checkpoint_address(
                    &program,
                    &Pubkey::new_from_array(state.identity.pool),
                    0
                )
                .0,
                false
            )
        );
        assert!(checkpoint.accounts[1..9]
            .iter()
            .all(|meta| !meta.is_writable && !meta.is_signer));
    }

    #[test]
    fn deposit_freezes_genesis_same_page_and_rollover_layouts() {
        let program = key(20);
        let mint = key(21);
        let registry_program = key(22);
        let master = master(program, mint, registry_program);
        let request = DepositRequestV1 {
            owner_key: [M31(23); 8],
            amount: 7,
            salt: [M31(24); 8],
            encrypted_note_payload: &[],
        };
        let commitment = pool_v1_note_commitment(
            &request.owner_key,
            request.amount,
            master.identity.asset_id,
            &request.salt,
        );
        let lane_id = pool_v1_pair_forest_deposit_lane_v1(&commitment).unwrap();
        let genesis = build_pair_forest_deposit_instruction_v2(
            program,
            &master,
            &lane(&master, lane_id, 0),
            key(25),
            key(26),
            Some(key(27)),
            &request,
        )
        .unwrap();
        assert_eq!(genesis.accounts.len(), 10);
        assert_eq!(
            decode_pair_forest_deposit_instruction_v1(&genesis.data).unwrap(),
            request
        );

        let same = build_pair_forest_deposit_instruction_v2(
            program,
            &master,
            &lane(&master, lane_id, 1),
            key(25),
            key(26),
            None,
            &request,
        )
        .unwrap();
        assert_eq!(same.accounts.len(), 8);

        let boundary_sequence = aspis_statement::pool_v1::POOL_V1_ROOT_HISTORY_CAPACITY as u64 - 1;
        let rollover = build_pair_forest_deposit_instruction_v2(
            program,
            &master,
            &lane(&master, lane_id, boundary_sequence),
            key(25),
            key(26),
            Some(key(27)),
            &request,
        )
        .unwrap();
        assert_eq!(rollover.accounts.len(), 11);
        assert!(!rollover.accounts[2].is_writable);
        assert!(rollover.accounts[3].is_writable);
    }

    #[test]
    fn deposit_rejects_wrong_lane_aliases_and_wrong_payer_shape() {
        let program = key(30);
        let mint = key(31);
        let registry_program = key(32);
        let master = master(program, mint, registry_program);
        let request = DepositRequestV1 {
            owner_key: [M31(33); 8],
            amount: 1,
            salt: [M31(34); 8],
            encrypted_note_payload: &[],
        };
        let commitment = pool_v1_note_commitment(
            &request.owner_key,
            request.amount,
            master.identity.asset_id,
            &request.salt,
        );
        let lane_id = pool_v1_pair_forest_deposit_lane_v1(&commitment).unwrap();
        assert_eq!(
            build_pair_forest_deposit_instruction_v2(
                program,
                &master,
                &lane(&master, (lane_id + 1) & 7, 0),
                key(35),
                key(36),
                Some(key(37)),
                &request
            ),
            Err(PairForestClientErrorV2::WrongLane)
        );
        assert_eq!(
            build_pair_forest_deposit_instruction_v2(
                program,
                &master,
                &lane(&master, lane_id, 0),
                key(35),
                key(36),
                None,
                &request
            ),
            Err(PairForestClientErrorV2::MissingPayer)
        );
        assert_eq!(
            build_pair_forest_deposit_instruction_v2(
                program,
                &master,
                &lane(&master, lane_id, 1),
                key(35),
                key(36),
                Some(key(37)),
                &request
            ),
            Err(PairForestClientErrorV2::UnexpectedPayer)
        );
    }

    #[test]
    fn finalized_registry_selection_is_exact_and_does_not_invent_spend_transport() {
        let program = key(40);
        let mint = key(41);
        let registry_program = key(42);
        let master = master(program, mint, registry_program);
        let pool = Pubkey::new_from_array(master.identity.pool);
        let request = PairForestSpendProfileRequestV2 {
            profile_binding: [43; 32],
            release_binding: [44; 32],
            statement_version: 1,
        };
        let registry = VerifierRegistryV1 {
            flags: 0,
            pool: master.identity.pool,
            authority: master.verifier_policy.registry_authority,
            policy_binding: master.verifier_policy.policy_binding,
            generation: 7,
            minimum_activation_delay_slots: 10,
        };
        let entry = VerifierRegistryEntryV1 {
            status: VerifierEntryStatusV1::Active,
            statement_version: 1,
            pool: master.identity.pool,
            verifier_program: [45; 32],
            profile_binding: request.profile_binding,
            release_binding: request.release_binding,
            activation_slot: 50,
            retirement_slot: POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
            policy_binding: master.verifier_policy.policy_binding,
        };
        let registry_account = FinalizedForestAccountV2 {
            address: pool_v1_verifier_registry_address(&registry_program, &pool)
                .0
                .to_bytes(),
            owner: registry_program.to_bytes(),
            executable: false,
            data: encode_verifier_registry_v1(&registry).unwrap().to_vec(),
        };
        let entry_account = FinalizedForestAccountV2 {
            address: pool_v1_verifier_entry_address(
                &registry_program,
                &pool,
                &request.profile_binding,
                &request.release_binding,
            )
            .0
            .to_bytes(),
            owner: registry_program.to_bytes(),
            executable: false,
            data: encode_verifier_registry_entry_v1(&entry).unwrap().to_vec(),
        };
        let point = FinalizedChainPointV1::new(60, [46; 32]).unwrap();
        let accounts = FinalizedPairForestProfileAccountsV2 {
            point,
            context_slot: 60,
            commitment: SolanaRpcCommitmentV1::Finalized,
            provider_set_digest: [47; 32],
            registry: registry_account,
            entry: entry_account,
        };
        let selected =
            select_pair_forest_spend_profile_v2(registry_program, &master, request, &accounts)
                .unwrap();
        assert_eq!(selected.registry_generation, 7);
        assert_eq!(selected.verifier_program, [45; 32]);
        assert_eq!(selected.provider_set_digest, [47; 32]);

        let mut paused = registry;
        paused.flags = aspis_statement::pool_v1::POOL_V1_VERIFIER_REGISTRY_FLAG_PAUSED;
        let paused_accounts = FinalizedPairForestProfileAccountsV2 {
            registry: FinalizedForestAccountV2 {
                data: encode_verifier_registry_v1(&paused).unwrap().to_vec(),
                ..accounts.registry.clone()
            },
            ..accounts.clone()
        };
        assert_eq!(
            select_pair_forest_spend_profile_v2(
                registry_program,
                &master,
                request,
                &paused_accounts,
            ),
            Err(PairForestClientErrorV2::RegistryPaused)
        );

        let nonfinal_accounts = FinalizedPairForestProfileAccountsV2 {
            commitment: SolanaRpcCommitmentV1::Confirmed,
            ..accounts
        };
        assert_eq!(
            select_pair_forest_spend_profile_v2(
                registry_program,
                &master,
                request,
                &nonfinal_accounts,
            ),
            Err(PairForestClientErrorV2::NotFinalized)
        );
    }
}
