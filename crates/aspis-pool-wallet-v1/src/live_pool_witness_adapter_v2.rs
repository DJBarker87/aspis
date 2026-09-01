//! Fail-closed host adapter from finalized eight-lane Pool state and a local
//! authenticated note path to the exact Tag-73 witness and terminal wires.
//!
//! This module does not prove, sign, submit, or accept verifier output. It
//! constructs the values consumed by the production prover and independently
//! derives the only ASR8 value that may be accepted for the statement.

use aspis_pool::{
    pool_v1_pair_forest_lane_address, pool_v1_pair_forest_master_address,
    pool_v1_vault_authority_address, pool_v1_vault_token_account_address,
    LEGACY_SPL_TOKEN_ACCOUNT_BYTES, LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES,
    LEGACY_SPL_TOKEN_PROGRAM_ID,
};
use aspis_registry::{
    pool_v1_verifier_entry_address, pool_v1_verifier_entry_v2_address,
    pool_v1_verifier_registry_address, pool_v1_verifier_registry_v2_address,
};
use aspis_statement::{
    decode_digest_canonical, derive_owner_key, encode_digest_canonical,
    pool_v1::{
        compile_pool_v1_pair_forest_private_transfer_merged_c1_v1,
        compile_pool_v1_pair_forest_withdrawal_merged_c1_v1,
        decode_pool_v1_pair_forest_terminal_request_v1,
        decode_pool_v1_pair_forest_terminal_result_v1,
        decode_pool_v1_pair_forest_terminal_statement_v1,
        encode_pool_v1_pair_forest_terminal_request_v1,
        encode_pool_v1_pair_forest_terminal_result_v1,
        encode_pool_v1_pair_forest_terminal_statement_v1, pair_trace::PoolV1PairInputNoteWitnessV1,
        pool_v1_note_commitment, pool_v1_pair_forest_output_lane_v1, pool_v1_tree_parent,
        v7_pool_pair_forest_tag73_statement_digest_v1,
        validate_pool_v1_pair_forest_terminal_result_against_statement_v1,
        PoolV1MembershipWitnessV1, PoolV1OutputNoteWitnessV1, PoolV1PairForestInputNoteWitnessV1,
        PoolV1PairForestLaneStateV1, PoolV1PairForestMasterV1,
        PoolV1PairForestPrivateTransferWitnessV1, PoolV1PairForestTerminalCommonV1,
        PoolV1PairForestTerminalPaymentV1, PoolV1PairForestTerminalRequestV1,
        PoolV1PairForestTerminalResultV1, PoolV1PairForestTerminalStatementV1,
        PoolV1PairForestWithdrawalWitnessV1, PoolV1PairLatePublicStatementV1,
        PoolV1PairLeafWitnessV1, PoolV1PairLiveSnapshotV1, PoolV1PaymentRuntimeBindingV1,
        PoolV1PrivateTransferPublicV1, PoolV1TransitionKind, PoolV1WithdrawalPublicV1,
        POOL_V1_PAIR_FOREST_ALL_LANES_MASK, POOL_V1_PAIR_FOREST_LANE_COUNT,
        POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES, POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES,
        POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES, POOL_V1_PAIR_FOREST_TERMINAL_VERSION,
        POOL_V1_PAIR_TREE_DEPTH, POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT,
        V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING, V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
    },
    poseidon2::Digest,
};
use sha2::{Digest as _, Sha256};
use solana_program::pubkey::Pubkey;

use crate::{
    lane_forest_client_v2::{
        PairForestSpendProfileSelectionV2, PairForestVerifierRegistryFamilyV2,
    },
    lane_forest_durable_v2::{
        authenticate_forest_checkpoint_account_v2, authenticate_forest_lane_account_v2,
        authenticate_forest_master_account_v2, AuthenticatedForestCheckpointAccountV2,
        AuthenticatedForestLaneAccountV2, AuthenticatedForestMasterAccountV2,
        AuthenticatedForestSpendMembershipV2,
    },
    lane_forest_rpc_v2::FinalizedForestAccountV2,
    lane_forest_v2::{lane_forest_global_root_v2, LaneIdV2, PairSlotV2},
    recompute_note_commitment_v1,
    scan_state::FinalizedChainPointV1,
    wallet_transition::derive_note_nullifier_v1,
    NoteOpeningV1,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LivePoolWitnessAdapterErrorV2 {
    NotFinalized,
    ContextMismatch,
    WrongOwner,
    ExecutableAccount,
    Master,
    Lane,
    Checkpoint,
    Profile,
    InvalidProofAccount,
    InvalidMembership,
    NoteOpening,
    SelectedSlotEmpty,
    ValueConservation,
    CandidateAfterstate,
    CanonicalWire,
    WithdrawalCustody,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AuthenticatedLivePairForestSnapshotV2 {
    pub program_id: [u8; 32],
    pub point: FinalizedChainPointV1,
    pub provider_set_digest: [u8; 32],
    pub master: AuthenticatedForestMasterAccountV2,
    pub lanes: [AuthenticatedForestLaneAccountV2; POOL_V1_PAIR_FOREST_LANE_COUNT],
    pub checkpoint: AuthenticatedForestCheckpointAccountV2,
    pub profile: PairForestSpendProfileSelectionV2,
}

/// Wallet-maintained membership material for one note at one retained global
/// checkpoint. All digests are canonical wire encodings. `second_commitment`
/// being `None` means the pair's second slot is algebraically empty; `Some`
/// constructs the occupied=1/inverse witness through the canonical helper.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LivePairForestMembershipSourceV2 {
    pub checkpoint_point: FinalizedChainPointV1,
    pub checkpoint_address: [u8; 32],
    pub checkpoint_sequence: u64,
    pub input_lane: LaneIdV2,
    pub pair_leaf_index: u64,
    pub slot: PairSlotV2,
    pub first_commitment: [u8; 32],
    pub second_commitment: Option<[u8; 32]>,
    pub pair_siblings: [[u8; 32]; POOL_V1_PAIR_TREE_DEPTH],
    pub checkpoint_lane_roots: [[u8; 32]; POOL_V1_PAIR_FOREST_LANE_COUNT],
}

impl From<AuthenticatedForestSpendMembershipV2> for LivePairForestMembershipSourceV2 {
    fn from(value: AuthenticatedForestSpendMembershipV2) -> Self {
        Self {
            checkpoint_point: value.checkpoint_point,
            checkpoint_address: value.checkpoint_address,
            checkpoint_sequence: value.checkpoint_sequence,
            input_lane: value.input_lane,
            pair_leaf_index: value.pair_leaf_index,
            slot: value.slot,
            first_commitment: value.first_commitment,
            second_commitment: value.second_commitment,
            pair_siblings: value.pair_siblings,
            checkpoint_lane_roots: value.checkpoint_lane_roots,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LivePairForestTransferPlanV2 {
    pub attempt_id: [u8; 32],
    pub verifier_program: [u8; 32],
    pub output_lane: u8,
    pub selected_lane: PoolV1PairForestLaneStateV1,
    pub witness: PoolV1PairForestPrivateTransferWitnessV1,
    pub public: PoolV1PrivateTransferPublicV1,
    pub runtime_binding: PoolV1PaymentRuntimeBindingV1,
    pub transition: PoolV1PairLatePublicStatementV1,
    pub request: PoolV1PairForestTerminalRequestV1,
    pub statement: PoolV1PairForestTerminalStatementV1,
    pub expected_result: PoolV1PairForestTerminalResultV1,
    pub asq8: [u8; POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES],
    pub asf8: [u8; POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES],
    pub expected_asr8: [u8; POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES],
    pub statement_digest: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LivePairForestWithdrawalPlanV2 {
    pub attempt_id: [u8; 32],
    pub verifier_program: [u8; 32],
    pub output_lane: u8,
    pub selected_lane: PoolV1PairForestLaneStateV1,
    pub witness: PoolV1PairForestWithdrawalWitnessV1,
    pub public: PoolV1WithdrawalPublicV1,
    pub runtime_binding: PoolV1PaymentRuntimeBindingV1,
    pub transition: PoolV1PairLatePublicStatementV1,
    pub request: PoolV1PairForestTerminalRequestV1,
    pub statement: PoolV1PairForestTerminalStatementV1,
    pub expected_result: PoolV1PairForestTerminalResultV1,
    pub asq8: [u8; POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES],
    pub asf8: [u8; POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES],
    pub expected_asr8: [u8; POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES],
    pub statement_digest: [u8; 32],
    pub vault_amount_before: u64,
    pub destination_amount_before: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LiveWithdrawalCustodyAccountsV2<'a> {
    pub mint: &'a FinalizedForestAccountV2,
    pub vault: &'a FinalizedForestAccountV2,
    pub destination: &'a FinalizedForestAccountV2,
}

fn require_pool_account(
    account: &FinalizedForestAccountV2,
    owner: [u8; 32],
) -> Result<(), LivePoolWitnessAdapterErrorV2> {
    if account.owner != owner {
        return Err(LivePoolWitnessAdapterErrorV2::WrongOwner);
    }
    if account.executable {
        return Err(LivePoolWitnessAdapterErrorV2::ExecutableAccount);
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub fn authenticate_live_pair_forest_snapshot_v2(
    program_id: [u8; 32],
    point: FinalizedChainPointV1,
    provider_set_digest: [u8; 32],
    master_account: &FinalizedForestAccountV2,
    lane_accounts: &[FinalizedForestAccountV2],
    checkpoint_account: &FinalizedForestAccountV2,
    profile: PairForestSpendProfileSelectionV2,
) -> Result<AuthenticatedLivePairForestSnapshotV2, LivePoolWitnessAdapterErrorV2> {
    if program_id == [0; 32] || provider_set_digest == [0; 32] {
        return Err(LivePoolWitnessAdapterErrorV2::NotFinalized);
    }
    require_pool_account(master_account, program_id)?;
    require_pool_account(checkpoint_account, program_id)?;
    if lane_accounts.len() != POOL_V1_PAIR_FOREST_LANE_COUNT {
        return Err(LivePoolWitnessAdapterErrorV2::Lane);
    }
    let master = authenticate_forest_master_account_v2(
        program_id,
        master_account.address,
        &master_account.data,
    )
    .map_err(|_| LivePoolWitnessAdapterErrorV2::Master)?;
    if master.value.initialized_lane_mask != POOL_V1_PAIR_FOREST_ALL_LANES_MASK
        || !master.value.has_checkpoint
    {
        return Err(LivePoolWitnessAdapterErrorV2::Master);
    }
    let mut lanes = Vec::with_capacity(POOL_V1_PAIR_FOREST_LANE_COUNT);
    for (index, account) in lane_accounts.iter().enumerate() {
        require_pool_account(account, program_id)?;
        let lane_id =
            LaneIdV2::new(index as u8).map_err(|_| LivePoolWitnessAdapterErrorV2::Lane)?;
        lanes.push(
            authenticate_forest_lane_account_v2(
                program_id,
                master.address,
                lane_id,
                account.address,
                &account.data,
            )
            .map_err(|_| LivePoolWitnessAdapterErrorV2::Lane)?,
        );
    }
    let lanes: [AuthenticatedForestLaneAccountV2; POOL_V1_PAIR_FOREST_LANE_COUNT] = lanes
        .try_into()
        .map_err(|_| LivePoolWitnessAdapterErrorV2::Lane)?;
    let checkpoint = authenticate_forest_checkpoint_account_v2(
        program_id,
        master.address,
        master.value.identity.deployment_domain,
        checkpoint_account.address,
        &checkpoint_account.data,
    )
    .map_err(|_| LivePoolWitnessAdapterErrorV2::Checkpoint)?;
    if checkpoint.value.checkpoint_sequence.checked_add(1)
        != Some(master.value.next_checkpoint_sequence)
        || checkpoint.value.lane_sequences != master.value.last_checkpoint_lane_sequences
        || lanes.iter().enumerate().any(|(index, lane)| {
            lane.value.tree.next_leaf_index < checkpoint.value.lane_sequences[index]
        })
    {
        return Err(LivePoolWitnessAdapterErrorV2::Checkpoint);
    }
    if profile.finalized_point != point
        || profile.provider_set_digest != provider_set_digest
        || profile.registry_program != master.value.verifier_policy.registry_program
        || profile.profile_binding != V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING
        || profile.release_binding != V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING
        || profile.statement_version != POOL_V1_PAIR_FOREST_TERMINAL_VERSION
        || profile.verifier_program == [0; 32]
    {
        return Err(LivePoolWitnessAdapterErrorV2::Profile);
    }
    let expected_family = if master.value.verifier_policy.flags
        & POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT
        != 0
    {
        PairForestVerifierRegistryFamilyV2::ImmutableDeploymentV2
    } else {
        PairForestVerifierRegistryFamilyV2::LegacyV1
    };
    if profile.registry_family != expected_family {
        return Err(LivePoolWitnessAdapterErrorV2::Profile);
    }
    let registry_program = Pubkey::new_from_array(profile.registry_program);
    let pool = Pubkey::new_from_array(master.address);
    let (expected_registry, expected_entry) = match profile.registry_family {
        PairForestVerifierRegistryFamilyV2::LegacyV1 => (
            pool_v1_verifier_registry_address(&registry_program, &pool).0,
            pool_v1_verifier_entry_address(
                &registry_program,
                &pool,
                &profile.profile_binding,
                &profile.release_binding,
            )
            .0,
        ),
        PairForestVerifierRegistryFamilyV2::ImmutableDeploymentV2 => (
            pool_v1_verifier_registry_v2_address(&registry_program, &pool).0,
            pool_v1_verifier_entry_v2_address(
                &registry_program,
                &pool,
                &profile.profile_binding,
                &profile.release_binding,
            )
            .0,
        ),
    };
    if profile.registry_address != expected_registry.to_bytes()
        || profile.entry_address != expected_entry.to_bytes()
    {
        return Err(LivePoolWitnessAdapterErrorV2::Profile);
    }
    Ok(AuthenticatedLivePairForestSnapshotV2 {
        program_id,
        point,
        provider_set_digest,
        master,
        lanes,
        checkpoint,
        profile,
    })
}

fn sha256_parts(parts: &[&[u8]]) -> [u8; 32] {
    let mut hash = Sha256::new();
    for part in parts {
        hash.update(part);
    }
    hash.finalize().into()
}

fn output_note(
    note: &NoteOpeningV1,
) -> Result<PoolV1OutputNoteWitnessV1, LivePoolWitnessAdapterErrorV2> {
    Ok(PoolV1OutputNoteWitnessV1 {
        owner_key: decode_digest_canonical(note.owner_key())
            .map_err(|_| LivePoolWitnessAdapterErrorV2::NoteOpening)?,
        salt: decode_digest_canonical(note.salt())
            .map_err(|_| LivePoolWitnessAdapterErrorV2::NoteOpening)?,
        value: note.value(),
    })
}

fn pair_path_root(
    index: u64,
    leaf: Digest,
    siblings: &[Digest; POOL_V1_PAIR_TREE_DEPTH],
) -> Digest {
    siblings
        .iter()
        .enumerate()
        .fold(leaf, |current, (level, sibling)| {
            if (index >> level) & 1 == 0 {
                pool_v1_tree_parent(&current, sibling)
            } else {
                pool_v1_tree_parent(sibling, &current)
            }
        })
}

fn super_root_path(
    lane_roots: &[Digest; POOL_V1_PAIR_FOREST_LANE_COUNT],
    lane: usize,
) -> ([Digest; 3], [bool; 3], Digest) {
    let level_one = core::array::from_fn::<_, 4, _>(|index| {
        pool_v1_tree_parent(&lane_roots[2 * index], &lane_roots[2 * index + 1])
    });
    let level_two = [
        pool_v1_tree_parent(&level_one[0], &level_one[1]),
        pool_v1_tree_parent(&level_one[2], &level_one[3]),
    ];
    (
        [
            lane_roots[lane ^ 1],
            level_one[(lane >> 1) ^ 1],
            level_two[(lane >> 2) ^ 1],
        ],
        [(lane & 1) != 0, (lane & 2) != 0, (lane & 4) != 0],
        pool_v1_tree_parent(&level_two[0], &level_two[1]),
    )
}

fn input_witness(
    snapshot: &AuthenticatedLivePairForestSnapshotV2,
    source: &LivePairForestMembershipSourceV2,
    note: &NoteOpeningV1,
    nullifier_key_bytes: &[u8; 32],
) -> Result<(PoolV1PairForestInputNoteWitnessV1, Digest), LivePoolWitnessAdapterErrorV2> {
    if source.checkpoint_point != snapshot.point
        || source.checkpoint_address != snapshot.checkpoint.address
        || source.checkpoint_sequence != snapshot.checkpoint.value.checkpoint_sequence
        || note.asset_id() != snapshot.master.value.identity.asset_id.0
        || source.pair_leaf_index > u64::from(u32::MAX)
        || source.pair_leaf_index
            >= snapshot.checkpoint.value.lane_sequences[source.input_lane.index()]
    {
        return Err(LivePoolWitnessAdapterErrorV2::InvalidMembership);
    }
    let first = decode_digest_canonical(&source.first_commitment)
        .map_err(|_| LivePoolWitnessAdapterErrorV2::InvalidMembership)?;
    let pair_leaf = match source.second_commitment {
        Some(second) => PoolV1PairLeafWitnessV1::two_outputs(
            first,
            decode_digest_canonical(&second)
                .map_err(|_| LivePoolWitnessAdapterErrorV2::InvalidMembership)?,
        ),
        None => PoolV1PairLeafWitnessV1::single_output(first),
    }
    .map_err(|_| LivePoolWitnessAdapterErrorV2::InvalidMembership)?;
    let selected_second = source.slot == PairSlotV2::Second;
    pair_leaf
        .require_selected_spendable(selected_second)
        .map_err(|_| LivePoolWitnessAdapterErrorV2::SelectedSlotEmpty)?;
    let note_commitment = recompute_note_commitment_v1(note)
        .map_err(|_| LivePoolWitnessAdapterErrorV2::NoteOpening)?;
    if encode_digest_canonical(pair_leaf.selected_commitment(selected_second)) != note_commitment {
        return Err(LivePoolWitnessAdapterErrorV2::NoteOpening);
    }
    let siblings: [Digest; POOL_V1_PAIR_TREE_DEPTH] = source
        .pair_siblings
        .map(|value| decode_digest_canonical(&value))
        .into_iter()
        .collect::<Result<Vec<_>, _>>()
        .map_err(|_| LivePoolWitnessAdapterErrorV2::InvalidMembership)?
        .try_into()
        .map_err(|_| LivePoolWitnessAdapterErrorV2::InvalidMembership)?;
    let lane_roots: [Digest; POOL_V1_PAIR_FOREST_LANE_COUNT] = source
        .checkpoint_lane_roots
        .map(|value| decode_digest_canonical(&value))
        .into_iter()
        .collect::<Result<Vec<_>, _>>()
        .map_err(|_| LivePoolWitnessAdapterErrorV2::InvalidMembership)?
        .try_into()
        .map_err(|_| LivePoolWitnessAdapterErrorV2::InvalidMembership)?;
    if pair_path_root(
        source.pair_leaf_index,
        pair_leaf
            .leaf_digest()
            .map_err(|_| LivePoolWitnessAdapterErrorV2::InvalidMembership)?,
        &siblings,
    ) != lane_roots[source.input_lane.index()]
        || lane_forest_global_root_v2(&source.checkpoint_lane_roots)
            .map_err(|_| LivePoolWitnessAdapterErrorV2::InvalidMembership)?
            != encode_digest_canonical(&snapshot.checkpoint.value.global_root)
    {
        return Err(LivePoolWitnessAdapterErrorV2::InvalidMembership);
    }
    let (super_root_siblings, super_root_directions, root) =
        super_root_path(&lane_roots, source.input_lane.index());
    if root != snapshot.checkpoint.value.global_root {
        return Err(LivePoolWitnessAdapterErrorV2::Checkpoint);
    }
    let nullifier = decode_digest_canonical(
        &derive_note_nullifier_v1(note, nullifier_key_bytes)
            .map_err(|_| LivePoolWitnessAdapterErrorV2::NoteOpening)?,
    )
    .map_err(|_| LivePoolWitnessAdapterErrorV2::NoteOpening)?;
    let nullifier_key = decode_digest_canonical(nullifier_key_bytes)
        .map_err(|_| LivePoolWitnessAdapterErrorV2::NoteOpening)?;
    if derive_owner_key(&nullifier_key)
        != decode_digest_canonical(note.owner_key())
            .map_err(|_| LivePoolWitnessAdapterErrorV2::NoteOpening)?
    {
        return Err(LivePoolWitnessAdapterErrorV2::NoteOpening);
    }
    Ok((
        PoolV1PairForestInputNoteWitnessV1 {
            pair: PoolV1PairInputNoteWitnessV1 {
                nullifier_key,
                salt: decode_digest_canonical(note.salt())
                    .map_err(|_| LivePoolWitnessAdapterErrorV2::NoteOpening)?,
                value: note.value(),
                pair_leaf,
                selected_second,
                membership: PoolV1MembershipWitnessV1 {
                    siblings,
                    index: source.pair_leaf_index as u32,
                },
            },
            super_root_siblings,
            super_root_directions,
        },
        nullifier,
    ))
}

fn selected_lane(
    snapshot: &AuthenticatedLivePairForestSnapshotV2,
    nullifier: &Digest,
) -> Result<(u8, PoolV1PairForestLaneStateV1, [u8; 32]), LivePoolWitnessAdapterErrorV2> {
    let output_lane = pool_v1_pair_forest_output_lane_v1(nullifier)
        .map_err(|_| LivePoolWitnessAdapterErrorV2::Lane)?;
    let lane = snapshot.lanes[usize::from(output_lane)].value;
    let expected = pool_v1_pair_forest_lane_address(
        &Pubkey::new_from_array(snapshot.program_id),
        &Pubkey::new_from_array(snapshot.master.address),
        output_lane,
    )
    .map_err(|_| LivePoolWitnessAdapterErrorV2::Lane)?
    .0
    .to_bytes();
    if snapshot.lanes[usize::from(output_lane)].address != expected {
        return Err(LivePoolWitnessAdapterErrorV2::Lane);
    }
    Ok((output_lane, lane, expected))
}

fn live_snapshot(
    master: &PoolV1PairForestMasterV1,
    lane: PoolV1PairForestLaneStateV1,
) -> PoolV1PairLiveSnapshotV1 {
    PoolV1PairLiveSnapshotV1 {
        pool: master.identity.pool,
        deployment_domain: master.identity.deployment_domain,
        sequence: lane.tree.next_leaf_index,
        next_pair_index: lane.tree.next_leaf_index,
        current_root: lane.tree.root,
        frontier: lane.tree.frontier,
    }
}

fn terminal_values(
    snapshot: &AuthenticatedLivePairForestSnapshotV2,
    proof_account: [u8; 32],
    output_lane: u8,
    selected_lane_account: [u8; 32],
    public: PoolV1PairForestTerminalPaymentV1,
    transition: PoolV1PairLatePublicStatementV1,
) -> Result<
    (
        PoolV1PairForestTerminalRequestV1,
        PoolV1PairForestTerminalStatementV1,
        PoolV1PairForestTerminalResultV1,
        [u8; POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES],
        [u8; POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES],
        [u8; POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES],
        [u8; 32],
    ),
    LivePoolWitnessAdapterErrorV2,
> {
    if proof_account == [0; 32] {
        return Err(LivePoolWitnessAdapterErrorV2::InvalidProofAccount);
    }
    let common = PoolV1PairForestTerminalCommonV1 {
        master_account: snapshot.master.address,
        checkpoint_account: snapshot.checkpoint.address,
        selected_lane_account,
        output_lane,
        checkpoint_sequence: snapshot.checkpoint.value.checkpoint_sequence,
        historical_global_anchor: snapshot.checkpoint.value.global_root,
        lane_transition: transition,
    };
    let (statement, kind, nullifier) = match public {
        PoolV1PairForestTerminalPaymentV1::PrivateTransfer(value) => (
            PoolV1PairForestTerminalStatementV1::PrivateTransfer {
                common,
                public: value,
            },
            PoolV1TransitionKind::PrivateTransfer,
            value.nullifier,
        ),
        PoolV1PairForestTerminalPaymentV1::Withdrawal(value) => (
            PoolV1PairForestTerminalStatementV1::Withdrawal {
                common,
                public: value,
            },
            PoolV1TransitionKind::Withdrawal,
            value.nullifier,
        ),
    };
    let request = PoolV1PairForestTerminalRequestV1 {
        verifier_profile: snapshot.profile.profile_binding,
        verifier_release: snapshot.profile.release_binding,
        pool_program: snapshot.program_id,
        public,
    };
    let result = PoolV1PairForestTerminalResultV1 {
        transition_kind: kind,
        master_account: snapshot.master.address,
        selected_lane_account,
        output_lane,
        nullifier,
        verified_afterstate: transition.candidate_afterstate,
    };
    let asq8 = encode_pool_v1_pair_forest_terminal_request_v1(&request)
        .map_err(|_| LivePoolWitnessAdapterErrorV2::CanonicalWire)?;
    let asf8 = encode_pool_v1_pair_forest_terminal_statement_v1(&statement)
        .map_err(|_| LivePoolWitnessAdapterErrorV2::CanonicalWire)?;
    let asr8 = encode_pool_v1_pair_forest_terminal_result_v1(&result)
        .map_err(|_| LivePoolWitnessAdapterErrorV2::CanonicalWire)?;
    if decode_pool_v1_pair_forest_terminal_request_v1(&asq8) != Ok(request)
        || decode_pool_v1_pair_forest_terminal_statement_v1(&asf8) != Ok(statement)
        || decode_pool_v1_pair_forest_terminal_result_v1(&asr8) != Ok(result)
        || validate_pool_v1_pair_forest_terminal_result_against_statement_v1(&statement, &result)
            .is_err()
    {
        return Err(LivePoolWitnessAdapterErrorV2::CanonicalWire);
    }
    let digest = v7_pool_pair_forest_tag73_statement_digest_v1(&asf8, sha256_parts);
    Ok((request, statement, result, asq8, asf8, asr8, digest))
}

#[allow(clippy::too_many_arguments)]
pub fn build_live_pair_forest_transfer_plan_v2(
    snapshot: &AuthenticatedLivePairForestSnapshotV2,
    source: &LivePairForestMembershipSourceV2,
    input_note: &NoteOpeningV1,
    nullifier_key: &[u8; 32],
    recipient_note: &NoteOpeningV1,
    change_note: &NoteOpeningV1,
    proof_account: [u8; 32],
) -> Result<LivePairForestTransferPlanV2, LivePoolWitnessAdapterErrorV2> {
    let (input, nullifier) = input_witness(snapshot, source, input_note, nullifier_key)?;
    if recipient_note.asset_id() != input_note.asset_id()
        || change_note.asset_id() != input_note.asset_id()
        || recipient_note.value().checked_add(change_note.value()) != Some(input_note.value())
    {
        return Err(LivePoolWitnessAdapterErrorV2::ValueConservation);
    }
    let recipient = output_note(recipient_note)?;
    let change = output_note(change_note)?;
    let public = PoolV1PrivateTransferPublicV1 {
        pool: snapshot.master.address,
        deployment_domain: snapshot.master.value.identity.deployment_domain,
        anchor_sequence: snapshot.checkpoint.value.checkpoint_sequence,
        anchor_root: snapshot.checkpoint.value.global_root,
        nullifier,
        asset_id: snapshot.master.value.identity.asset_id,
        recipient_commitment: pool_v1_note_commitment(
            &recipient.owner_key,
            recipient.value,
            snapshot.master.value.identity.asset_id,
            &recipient.salt,
        ),
        change_commitment: pool_v1_note_commitment(
            &change.owner_key,
            change.value,
            snapshot.master.value.identity.asset_id,
            &change.salt,
        ),
    };
    let witness = PoolV1PairForestPrivateTransferWitnessV1 {
        input,
        recipient,
        change,
    };
    let (output_lane, selected_lane, selected_lane_account) = selected_lane(snapshot, &nullifier)?;
    let runtime_binding = PoolV1PaymentRuntimeBindingV1 {
        pool: snapshot.master.address,
        deployment_domain: snapshot.master.value.identity.deployment_domain,
        anchor_sequence: snapshot.checkpoint.value.checkpoint_sequence,
        anchor_root: snapshot.checkpoint.value.global_root,
        asset_id: snapshot.master.value.identity.asset_id,
    };
    let compiled = compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(
        &public,
        &witness,
        aspis_statement::pool_v1::PoolV1PaymentRelationContextV1 {
            runtime_binding,
            spent_nullifiers: &[],
        },
        live_snapshot(&snapshot.master.value, selected_lane),
    )
    .map_err(|_| LivePoolWitnessAdapterErrorV2::CandidateAfterstate)?;
    let transition = compiled.public_statement;
    let (request, statement, expected_result, asq8, asf8, expected_asr8, statement_digest) =
        terminal_values(
            snapshot,
            proof_account,
            output_lane,
            selected_lane_account,
            PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public),
            transition,
        )?;
    Ok(LivePairForestTransferPlanV2 {
        attempt_id: proof_account,
        verifier_program: snapshot.profile.verifier_program,
        output_lane,
        selected_lane,
        witness,
        public,
        runtime_binding,
        transition,
        request,
        statement,
        expected_result,
        asq8,
        asf8,
        expected_asr8,
        statement_digest,
    })
}

fn token_account(
    account: &FinalizedForestAccountV2,
    mint: [u8; 32],
) -> Result<([u8; 32], u64), LivePoolWitnessAdapterErrorV2> {
    if account.owner != LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes()
        || account.executable
        || account.data.len() != LEGACY_SPL_TOKEN_ACCOUNT_BYTES
        || account.data[..32] != mint
        || account.data[108] != 1
    {
        return Err(LivePoolWitnessAdapterErrorV2::WithdrawalCustody);
    }
    Ok((
        account.data[32..64].try_into().unwrap(),
        u64::from_le_bytes(account.data[64..72].try_into().unwrap()),
    ))
}

#[allow(clippy::too_many_arguments)]
pub fn build_live_pair_forest_withdrawal_plan_v2(
    snapshot: &AuthenticatedLivePairForestSnapshotV2,
    source: &LivePairForestMembershipSourceV2,
    input_note: &NoteOpeningV1,
    nullifier_key: &[u8; 32],
    amount: u32,
    destination_token_account: [u8; 32],
    change_note: &NoteOpeningV1,
    custody: LiveWithdrawalCustodyAccountsV2<'_>,
    proof_account: [u8; 32],
) -> Result<LivePairForestWithdrawalPlanV2, LivePoolWitnessAdapterErrorV2> {
    if amount == 0
        || change_note.asset_id() != input_note.asset_id()
        || amount.checked_add(change_note.value()) != Some(input_note.value())
        || destination_token_account != custody.destination.address
        || custody.mint.address != snapshot.master.value.identity.asset_mint
        || custody.mint.owner != LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes()
        || custody.mint.executable
        || custody.mint.data.len() != LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES
        || custody.mint.data[45] != 1
    {
        return Err(LivePoolWitnessAdapterErrorV2::WithdrawalCustody);
    }
    let master_key = Pubkey::new_from_array(snapshot.master.address);
    let program = Pubkey::new_from_array(snapshot.program_id);
    if pool_v1_pair_forest_master_address(
        &program,
        &Pubkey::new_from_array(snapshot.master.value.identity.asset_mint),
    )
    .0
    .to_bytes()
        != snapshot.master.address
        || pool_v1_vault_token_account_address(&program, &master_key)
            .0
            .to_bytes()
            != custody.vault.address
    {
        return Err(LivePoolWitnessAdapterErrorV2::WithdrawalCustody);
    }
    let (vault_authority, vault_amount_before) =
        token_account(custody.vault, snapshot.master.value.identity.asset_mint)?;
    let (_, destination_amount_before) = token_account(
        custody.destination,
        snapshot.master.value.identity.asset_mint,
    )?;
    if vault_authority
        != pool_v1_vault_authority_address(&program, &master_key)
            .0
            .to_bytes()
        || vault_amount_before < u64::from(amount)
    {
        return Err(LivePoolWitnessAdapterErrorV2::WithdrawalCustody);
    }
    let (input, nullifier) = input_witness(snapshot, source, input_note, nullifier_key)?;
    let change = output_note(change_note)?;
    let public = PoolV1WithdrawalPublicV1 {
        pool: snapshot.master.address,
        deployment_domain: snapshot.master.value.identity.deployment_domain,
        anchor_sequence: snapshot.checkpoint.value.checkpoint_sequence,
        anchor_root: snapshot.checkpoint.value.global_root,
        nullifier,
        asset_id: snapshot.master.value.identity.asset_id,
        amount,
        destination_token_account,
        change_commitment: pool_v1_note_commitment(
            &change.owner_key,
            change.value,
            snapshot.master.value.identity.asset_id,
            &change.salt,
        ),
    };
    let witness = PoolV1PairForestWithdrawalWitnessV1 { input, change };
    let (output_lane, selected_lane, selected_lane_account) = selected_lane(snapshot, &nullifier)?;
    let runtime_binding = PoolV1PaymentRuntimeBindingV1 {
        pool: snapshot.master.address,
        deployment_domain: snapshot.master.value.identity.deployment_domain,
        anchor_sequence: snapshot.checkpoint.value.checkpoint_sequence,
        anchor_root: snapshot.checkpoint.value.global_root,
        asset_id: snapshot.master.value.identity.asset_id,
    };
    let compiled = compile_pool_v1_pair_forest_withdrawal_merged_c1_v1(
        &public,
        &witness,
        aspis_statement::pool_v1::PoolV1PaymentRelationContextV1 {
            runtime_binding,
            spent_nullifiers: &[],
        },
        live_snapshot(&snapshot.master.value, selected_lane),
    )
    .map_err(|_| LivePoolWitnessAdapterErrorV2::CandidateAfterstate)?;
    let transition = compiled.public_statement;
    let (request, statement, expected_result, asq8, asf8, expected_asr8, statement_digest) =
        terminal_values(
            snapshot,
            proof_account,
            output_lane,
            selected_lane_account,
            PoolV1PairForestTerminalPaymentV1::Withdrawal(public),
            transition,
        )?;
    Ok(LivePairForestWithdrawalPlanV2 {
        attempt_id: proof_account,
        verifier_program: snapshot.profile.verifier_program,
        output_lane,
        selected_lane,
        witness,
        public,
        runtime_binding,
        transition,
        request,
        statement,
        expected_result,
        asq8,
        asf8,
        expected_asr8,
        statement_digest,
        vault_amount_before,
        destination_amount_before,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::M31;
    use aspis_pool::{pool_v1_pair_forest_checkpoint_address, POOL_V1_PAIR_EMPTY_ROOTS};
    use aspis_statement::pool_v1::{
        encode_pool_v1_pair_forest_checkpoint_v1, encode_pool_v1_pair_forest_lane_state_v1,
        encode_pool_v1_pair_forest_master_v1, IncrementalMerkleTreeV1, PoolIdentityV1,
        PoolV1PairForestCheckpointV1, VerifierPolicyV1,
    };

    struct Fixture {
        snapshot: AuthenticatedLivePairForestSnapshotV2,
        source: LivePairForestMembershipSourceV2,
        input: NoteOpeningV1,
        nullifier_key: [u8; 32],
        mint: FinalizedForestAccountV2,
        vault: FinalizedForestAccountV2,
        destination: FinalizedForestAccountV2,
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32 + 1))
    }

    fn note(nullifier_key: Digest, value: u32, asset_id: u32, salt: Digest) -> NoteOpeningV1 {
        NoteOpeningV1::new(
            encode_digest_canonical(&derive_owner_key(&nullifier_key)),
            value,
            asset_id,
            encode_digest_canonical(&salt),
        )
        .unwrap()
    }

    fn fixture() -> Fixture {
        let program = Pubkey::new_unique();
        let mint_key = Pubkey::new_unique();
        let registry = Pubkey::new_unique();
        let verifier = Pubkey::new_unique();
        let master_key = pool_v1_pair_forest_master_address(&program, &mint_key).0;
        let nullifier_key_digest = digest(100);
        let nullifier_key = encode_digest_canonical(&nullifier_key_digest);
        let input = note(nullifier_key_digest, 1_000, 77, digest(200));
        let commitment = recompute_note_commitment_v1(&input).unwrap();
        let commitment_digest = decode_digest_canonical(&commitment).unwrap();
        let input_lane = LaneIdV2::new(commitment[0] & 7).unwrap();
        let pair_leaf = PoolV1PairLeafWitnessV1::single_output(commitment_digest)
            .unwrap()
            .leaf_digest()
            .unwrap();
        let empty_tree = IncrementalMerkleTreeV1::from_parts_with_empty_roots(
            0,
            POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH],
            core::array::from_fn(|level| POOL_V1_PAIR_EMPTY_ROOTS[level]),
            &POOL_V1_PAIR_EMPTY_ROOTS,
        )
        .unwrap();
        let mut lane_values = core::array::from_fn::<_, POOL_V1_PAIR_FOREST_LANE_COUNT, _>(|id| {
            PoolV1PairForestLaneStateV1 {
                master: master_key.to_bytes(),
                lane_id: id as u8,
                tree: empty_tree,
            }
        });
        lane_values[input_lane.index()].tree = empty_tree
            .append_one_with_empty_roots(pair_leaf, &POOL_V1_PAIR_EMPTY_ROOTS)
            .unwrap()
            .0;
        let lane_sequences = lane_values.each_ref().map(|lane| lane.tree.next_leaf_index);
        let lane_roots = lane_values
            .each_ref()
            .map(|lane| encode_digest_canonical(&lane.tree.root));
        let global_root =
            decode_digest_canonical(&lane_forest_global_root_v2(&lane_roots).unwrap()).unwrap();
        let master_value = PoolV1PairForestMasterV1 {
            identity: PoolIdentityV1 {
                pool: master_key.to_bytes(),
                asset_mint: mint_key.to_bytes(),
                token_program: LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes(),
                asset_id: M31(77),
                deployment_domain: [5; 32],
            },
            verifier_policy: VerifierPolicyV1 {
                flags: 0,
                registry_program: registry.to_bytes(),
                registry_authority: [6; 32],
                policy_binding: [7; 32],
            },
            initialized_lane_mask: POOL_V1_PAIR_FOREST_ALL_LANES_MASK,
            has_checkpoint: true,
            next_checkpoint_sequence: 1,
            last_checkpoint_lane_sequences: lane_sequences,
        };
        let checkpoint_value = PoolV1PairForestCheckpointV1 {
            master: master_key.to_bytes(),
            deployment_domain: master_value.identity.deployment_domain,
            checkpoint_sequence: 0,
            global_root,
            lane_sequences,
        };
        let checkpoint_key = pool_v1_pair_forest_checkpoint_address(&program, &master_key, 0).0;
        let master_account = FinalizedForestAccountV2 {
            address: master_key.to_bytes(),
            owner: program.to_bytes(),
            executable: false,
            data: encode_pool_v1_pair_forest_master_v1(&master_value)
                .unwrap()
                .to_vec(),
        };
        let lane_accounts = lane_values
            .iter()
            .enumerate()
            .map(|(id, lane)| FinalizedForestAccountV2 {
                address: pool_v1_pair_forest_lane_address(&program, &master_key, id as u8)
                    .unwrap()
                    .0
                    .to_bytes(),
                owner: program.to_bytes(),
                executable: false,
                data: encode_pool_v1_pair_forest_lane_state_v1(lane, &POOL_V1_PAIR_EMPTY_ROOTS)
                    .unwrap()
                    .to_vec(),
            })
            .collect::<Vec<_>>();
        let checkpoint_account = FinalizedForestAccountV2 {
            address: checkpoint_key.to_bytes(),
            owner: program.to_bytes(),
            executable: false,
            data: encode_pool_v1_pair_forest_checkpoint_v1(&checkpoint_value)
                .unwrap()
                .to_vec(),
        };
        let point = FinalizedChainPointV1::new(50, [51; 32]).unwrap();
        let provider_set_digest = [52; 32];
        let profile = PairForestSpendProfileSelectionV2 {
            registry_family: PairForestVerifierRegistryFamilyV2::LegacyV1,
            finalized_point: point,
            provider_set_digest,
            registry_program: registry.to_bytes(),
            registry_address: pool_v1_verifier_registry_address(&registry, &master_key)
                .0
                .to_bytes(),
            registry_generation: 4,
            entry_address: pool_v1_verifier_entry_address(
                &registry,
                &master_key,
                &V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,
                &V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
            )
            .0
            .to_bytes(),
            verifier_program: verifier.to_bytes(),
            profile_binding: V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,
            release_binding: V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
            statement_version: POOL_V1_PAIR_FOREST_TERMINAL_VERSION,
        };
        let snapshot = authenticate_live_pair_forest_snapshot_v2(
            program.to_bytes(),
            point,
            provider_set_digest,
            &master_account,
            &lane_accounts,
            &checkpoint_account,
            profile,
        )
        .unwrap();
        let source = LivePairForestMembershipSourceV2 {
            checkpoint_point: point,
            checkpoint_address: checkpoint_key.to_bytes(),
            checkpoint_sequence: 0,
            input_lane,
            pair_leaf_index: 0,
            slot: PairSlotV2::First,
            first_commitment: commitment,
            second_commitment: None,
            pair_siblings: core::array::from_fn(|level| {
                encode_digest_canonical(&POOL_V1_PAIR_EMPTY_ROOTS[level])
            }),
            checkpoint_lane_roots: lane_roots,
        };
        let vault_key = pool_v1_vault_token_account_address(&program, &master_key).0;
        let vault_authority = pool_v1_vault_authority_address(&program, &master_key)
            .0
            .to_bytes();
        let destination_key = Pubkey::new_unique();
        let token_account = |address: Pubkey, authority: [u8; 32], amount: u64| {
            let mut data = vec![0u8; LEGACY_SPL_TOKEN_ACCOUNT_BYTES];
            data[..32].copy_from_slice(&mint_key.to_bytes());
            data[32..64].copy_from_slice(&authority);
            data[64..72].copy_from_slice(&amount.to_le_bytes());
            data[108] = 1;
            FinalizedForestAccountV2 {
                address: address.to_bytes(),
                owner: LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes(),
                executable: false,
                data,
            }
        };
        let mut mint_data = vec![0u8; LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES];
        mint_data[45] = 1;
        Fixture {
            snapshot,
            source,
            input,
            nullifier_key,
            mint: FinalizedForestAccountV2 {
                address: mint_key.to_bytes(),
                owner: LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes(),
                executable: false,
                data: mint_data,
            },
            vault: token_account(vault_key, vault_authority, 1_000),
            destination: token_account(destination_key, Pubkey::new_unique().to_bytes(), 0),
        }
    }

    #[test]
    fn independently_generated_live_snapshot_builds_exact_transfer_and_withdrawal_wires() {
        let fixture = fixture();
        let recipient = note(digest(300), 600, 77, digest(400));
        let transfer_change = note(digest(500), 400, 77, digest(600));
        let transfer = build_live_pair_forest_transfer_plan_v2(
            &fixture.snapshot,
            &fixture.source,
            &fixture.input,
            &fixture.nullifier_key,
            &recipient,
            &transfer_change,
            [61; 32],
        )
        .unwrap();
        assert_eq!(transfer.attempt_id, [61; 32]);
        assert_eq!(
            transfer.witness.input.pair.pair_leaf.second_occupied,
            M31::ZERO
        );
        assert_eq!(
            decode_pool_v1_pair_forest_terminal_request_v1(&transfer.asq8),
            Ok(transfer.request)
        );
        assert_eq!(
            decode_pool_v1_pair_forest_terminal_statement_v1(&transfer.asf8),
            Ok(transfer.statement)
        );
        assert_eq!(
            decode_pool_v1_pair_forest_terminal_result_v1(&transfer.expected_asr8),
            Ok(transfer.expected_result)
        );

        let withdrawal_change = note(digest(700), 750, 77, digest(800));
        let withdrawal = build_live_pair_forest_withdrawal_plan_v2(
            &fixture.snapshot,
            &fixture.source,
            &fixture.input,
            &fixture.nullifier_key,
            250,
            fixture.destination.address,
            &withdrawal_change,
            LiveWithdrawalCustodyAccountsV2 {
                mint: &fixture.mint,
                vault: &fixture.vault,
                destination: &fixture.destination,
            },
            [62; 32],
        )
        .unwrap();
        assert_eq!(withdrawal.vault_amount_before, 1_000);
        assert_eq!(withdrawal.destination_amount_before, 0);
        assert_eq!(withdrawal.public.amount, 250);
        assert_eq!(
            decode_pool_v1_pair_forest_terminal_result_v1(&withdrawal.expected_asr8),
            Ok(withdrawal.expected_result)
        );
    }

    #[test]
    fn live_adapter_rejects_checkpoint_note_occupancy_profile_and_custody_mismatch() {
        let fixture = fixture();
        let recipient = note(digest(300), 600, 77, digest(400));
        let change = note(digest(500), 400, 77, digest(600));
        let mut wrong_checkpoint = fixture.source;
        wrong_checkpoint.checkpoint_sequence = 1;
        assert_eq!(
            build_live_pair_forest_transfer_plan_v2(
                &fixture.snapshot,
                &wrong_checkpoint,
                &fixture.input,
                &fixture.nullifier_key,
                &recipient,
                &change,
                [61; 32],
            ),
            Err(LivePoolWitnessAdapterErrorV2::InvalidMembership)
        );
        let mut empty_second = fixture.source;
        empty_second.slot = PairSlotV2::Second;
        assert_eq!(
            build_live_pair_forest_transfer_plan_v2(
                &fixture.snapshot,
                &empty_second,
                &fixture.input,
                &fixture.nullifier_key,
                &recipient,
                &change,
                [61; 32],
            ),
            Err(LivePoolWitnessAdapterErrorV2::SelectedSlotEmpty)
        );
        let mut wrong_root = fixture.source;
        wrong_root.checkpoint_lane_roots[0] = encode_digest_canonical(&digest(999));
        assert_eq!(
            build_live_pair_forest_transfer_plan_v2(
                &fixture.snapshot,
                &wrong_root,
                &fixture.input,
                &fixture.nullifier_key,
                &recipient,
                &change,
                [61; 32],
            ),
            Err(LivePoolWitnessAdapterErrorV2::InvalidMembership)
        );
        let mut bad_vault = fixture.vault.clone();
        bad_vault.data[64..72].copy_from_slice(&100u64.to_le_bytes());
        let withdrawal_change = note(digest(700), 750, 77, digest(800));
        assert_eq!(
            build_live_pair_forest_withdrawal_plan_v2(
                &fixture.snapshot,
                &fixture.source,
                &fixture.input,
                &fixture.nullifier_key,
                250,
                fixture.destination.address,
                &withdrawal_change,
                LiveWithdrawalCustodyAccountsV2 {
                    mint: &fixture.mint,
                    vault: &bad_vault,
                    destination: &fixture.destination,
                },
                [62; 32],
            ),
            Err(LivePoolWitnessAdapterErrorV2::WithdrawalCustody)
        );
    }
}
