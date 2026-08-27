//! Production-inactive one-terminal proof-carried afterstate prototype.
//!
//! There are no prepared authorization or settlement accounts. The selected
//! verifier authenticates the staged proof and returns the exact next pair
//! index, root and frontier.  The Pool performs no Poseidon call: it validates
//! the opaque immediate-CPI result and atomically writes state, history and the
//! one-shot nullifier marker.  The dispatcher remains disabled until the real
//! seven-C2-lane verifier constructs this result.

extern crate alloc;

use alloc::{boxed::Box, vec};

use aspis_core::transcript::HashFn;
use aspis_statement::{
    encode_digest_canonical,
    pool_v1::{
        root_history_location, PoolV1NullifierMarkerV1, PoolV1TransitionKind,
        POOL_V1_ROOT_HISTORY_CAPACITY,
    },
};
use solana_program::{
    account_info::AccountInfo, entrypoint::ProgramResult, program_error::ProgramError,
    pubkey::Pubkey,
};

use crate::{
    error::PoolV1ProgramError,
    history::{
        append_roots_unchecked, read_retained_root, require_program_account, require_program_owned,
        require_root_page_address, validate_new_page_account, validate_root_page_bytes,
        write_new_page_unchecked,
    },
    instruction::{
        decode_pair_private_transfer_instruction_v1, encode_transition_receipt_v1,
        TransitionReceiptV1,
    },
    nullifier::{plan_nullifier_marker_consumption_v1, NullifierMarkerPreparationV1},
    pair_dispatch::AuthenticatedPairAfterstateV1,
    pair_state::{CanonicalPairPoolStateV1, PairPoolStateV1, POOL_V1_PAIR_STATE_ACCOUNT_BYTES},
};

#[inline(always)]
fn pair_cu_checkpoint(label: &str) {
    #[cfg(feature = "pair-afterstate-profile")]
    {
        solana_program::log::sol_log(label);
        solana_program::log::sol_log_compute_units();
    }
    #[cfg(not(feature = "pair-afterstate-profile"))]
    let _ = label;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PairSpendLayoutV1 {
    anchor_index: usize,
    current_index: usize,
    next_index: Option<usize>,
    marker_index: usize,
    registry_start: usize,
    verifier_index: usize,
    proof_index: usize,
}

fn require_unique(accounts: &[AccountInfo<'_>]) -> ProgramResult {
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

fn plan_layout(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    state: &PairPoolStateV1,
    anchor_sequence: u64,
) -> Result<PairSpendLayoutV1, ProgramError> {
    if state.current_root_sequence() >= aspis_statement::pool_v1::POOL_V1_PAIR_CAPACITY {
        return Err(PoolV1ProgramError::TreeFull.into());
    }
    if anchor_sequence > state.current_root_sequence() {
        return Err(PoolV1ProgramError::HistoricalAnchorInFuture.into());
    }
    let pool = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    let anchor_page_number = root_history_location(anchor_sequence).page_number;
    let current_page_number = root_history_location(state.current_root_sequence()).page_number;
    let next_page_number = root_history_location(state.current_root_sequence() + 1).page_number;
    if next_page_number > current_page_number.saturating_add(1) {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }

    let anchor_key = crate::pool_v1_root_page_address(program_id, pool.key, anchor_page_number).0;
    let current_key = crate::pool_v1_root_page_address(program_id, pool.key, current_page_number).0;
    let anchor_index = 1;
    if accounts
        .get(anchor_index)
        .ok_or(ProgramError::NotEnoughAccountKeys)?
        .key
        != &anchor_key
    {
        return Err(PoolV1ProgramError::InvalidRootPageAddress.into());
    }
    let mut cursor = 2;
    let current_index = if anchor_key == current_key {
        anchor_index
    } else {
        let index = cursor;
        cursor += 1;
        if accounts
            .get(index)
            .ok_or(ProgramError::NotEnoughAccountKeys)?
            .key
            != &current_key
        {
            return Err(PoolV1ProgramError::InvalidRootPageAddress.into());
        }
        index
    };
    let next_index = if next_page_number != current_page_number {
        let index = cursor;
        cursor += 1;
        if accounts
            .get(index)
            .ok_or(ProgramError::NotEnoughAccountKeys)?
            .key
            != &crate::pool_v1_root_page_address(program_id, pool.key, next_page_number).0
        {
            return Err(PoolV1ProgramError::InvalidRootPageAddress.into());
        }
        Some(index)
    } else {
        None
    };
    let layout = PairSpendLayoutV1 {
        anchor_index,
        current_index,
        next_index,
        marker_index: cursor,
        registry_start: cursor + 1,
        verifier_index: cursor + 3,
        proof_index: cursor + 4,
    };
    let expected = cursor + 5;
    if accounts.len() != expected {
        return Err(if accounts.len() < expected {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    }
    Ok(layout)
}

fn validate_history(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    state: &PairPoolStateV1,
    layout: PairSpendLayoutV1,
    anchor_sequence: u64,
    anchor_root: &aspis_statement::poseidon2::Digest,
) -> ProgramResult {
    let pool = &accounts[0];
    let anchor = &accounts[layout.anchor_index];
    let current_location = root_history_location(state.current_root_sequence());
    let current_writable = layout.next_index.is_none();

    // The historical membership anchor and live append root often occupy the
    // same chronological page.  Parse that canonical page once and check both
    // slots under the stricter live-page mutability rule.  This removes a full
    // duplicate 8,256-byte page scan without weakening either root role.
    if layout.anchor_index == layout.current_index {
        require_program_account(anchor, program_id, current_writable)?;
        if anchor.is_signer {
            return Err(ProgramError::InvalidAccountData);
        }
        require_root_page_address(program_id, pool.key, current_location.page_number, anchor)?;
        let data = anchor.try_borrow_data()?;
        let header = validate_root_page_bytes(&data, pool.key, current_location.page_number)?;
        if read_retained_root(&data, header, anchor_sequence)? != *anchor_root
            || header.filled != current_location.slot + 1
            || read_retained_root(&data, header, state.current_root_sequence())? != state.tree.root
            || (layout.next_index.is_some()
                && usize::from(header.filled) != POOL_V1_ROOT_HISTORY_CAPACITY)
        {
            return Err(PoolV1ProgramError::StateHistoryMismatch.into());
        }
        drop(data);
        if let Some(next_index) = layout.next_index {
            let next_location = root_history_location(state.current_root_sequence() + 1);
            validate_new_page_account(
                program_id,
                pool.key,
                next_location.page_number,
                &accounts[next_index],
            )?;
        }
        return Ok(());
    }

    require_program_owned(anchor, program_id)?;
    if anchor.is_signer {
        return Err(ProgramError::InvalidAccountData);
    }
    let anchor_location = root_history_location(anchor_sequence);
    require_root_page_address(program_id, pool.key, anchor_location.page_number, anchor)?;
    let anchor_data = anchor.try_borrow_data()?;
    let anchor_header =
        validate_root_page_bytes(&anchor_data, pool.key, anchor_location.page_number)?;
    if read_retained_root(&anchor_data, anchor_header, anchor_sequence)? != *anchor_root {
        return Err(PoolV1ProgramError::HistoricalAnchorRootMismatch.into());
    }
    drop(anchor_data);

    let current = &accounts[layout.current_index];
    require_program_account(current, program_id, current_writable)?;
    if current.is_signer {
        return Err(ProgramError::InvalidAccountData);
    }
    require_root_page_address(program_id, pool.key, current_location.page_number, current)?;
    let current_data = current.try_borrow_data()?;
    let current_header =
        validate_root_page_bytes(&current_data, pool.key, current_location.page_number)?;
    if current_header.filled != current_location.slot + 1
        || read_retained_root(&current_data, current_header, state.current_root_sequence())?
            != state.tree.root
    {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    if layout.next_index.is_some()
        && usize::from(current_header.filled) != POOL_V1_ROOT_HISTORY_CAPACITY
    {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    drop(current_data);

    if let Some(next_index) = layout.next_index {
        let next_location = root_history_location(state.current_root_sequence() + 1);
        validate_new_page_account(
            program_id,
            pool.key,
            next_location.page_number,
            &accounts[next_index],
        )?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn process_pair_private_transfer_with_verifier_v1<'info, V, S>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'info>],
    instruction_data: &[u8],
    current_slot: u64,
    hash: HashFn,
    verify: V,
    set_return_data: S,
) -> ProgramResult
where
    V: FnOnce(
        &Pubkey,
        &[u8; 32],
        &aspis_statement::pool_v1::VerifierPolicyV1,
        &[AccountInfo<'info>],
        &AccountInfo<'info>,
        &AccountInfo<'info>,
        &aspis_statement::pool_v1::HistoricalAnchorEnvelopeV1,
        &[u8],
        u64,
        HashFn,
    ) -> Result<AuthenticatedPairAfterstateV1, ProgramError>,
    S: FnOnce(&[u8]),
{
    pair_cu_checkpoint("aspis-pair-cu:handler_entry");
    let decoded = decode_pair_private_transfer_instruction_v1(instruction_data)?;
    let pool = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    let state = CanonicalPairPoolStateV1::decode_account_from_program_invariant(program_id, pool)?;
    state.require_same_account(program_id, pool)?;
    if decoded.statement.pool != pool.key.to_bytes()
        || decoded.statement.deployment_domain != state.identity.deployment_domain
        || decoded.statement.asset_id != state.identity.asset_id
        || decoded.envelope.transition_kind != PoolV1TransitionKind::PrivateTransfer
    {
        return Err(PoolV1ProgramError::VerifierDispatchIdentityMismatch.into());
    }
    pair_cu_checkpoint("aspis-pair-cu:state_and_statement_validated");
    let layout = plan_layout(
        program_id,
        accounts,
        &state,
        decoded.statement.anchor_sequence,
    )?;
    require_unique(accounts)?;
    pair_cu_checkpoint("aspis-pair-cu:layout_validated");
    validate_history(
        program_id,
        accounts,
        &state,
        layout,
        decoded.statement.anchor_sequence,
        &decoded.statement.anchor_root,
    )?;
    pair_cu_checkpoint("aspis-pair-cu:history_validated");

    let marker = &accounts[layout.marker_index];
    let planned_marker = plan_nullifier_marker_consumption_v1(
        program_id,
        marker,
        PoolV1NullifierMarkerV1::from_historical_anchor(&decoded.envelope),
    )?;
    if planned_marker.preparation() != NullifierMarkerPreparationV1::PopulateProgramOwnedZeroed {
        return Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into());
    }
    pair_cu_checkpoint("aspis-pair-cu:marker_preflight_complete");

    let verified_afterstate = verify(
        pool.key,
        &state.identity.deployment_domain,
        &state.verifier_policy,
        &accounts[layout.registry_start..layout.registry_start + 2],
        &accounts[layout.verifier_index],
        &accounts[layout.proof_index],
        &decoded.envelope,
        decoded.statement_payload,
        current_slot,
        hash,
    )?;
    pair_cu_checkpoint("aspis-pair-cu:afterstate_authenticated");
    let (next_state, append) =
        state.apply_authenticated_afterstate_from_program_invariant(&verified_afterstate)?;
    pair_cu_checkpoint("aspis-pair-cu:afterstate_applied");

    let receipt = encode_transition_receipt_v1(&TransitionReceiptV1 {
        transition_kind: PoolV1TransitionKind::PrivateTransfer,
        pool: pool.key.to_bytes(),
        nullifier: decoded.statement.nullifier,
        first_output: decoded.statement.recipient_commitment,
        second_output_or_destination: encode_digest_canonical(&decoded.statement.change_commitment),
        withdrawal_amount: 0,
        first_leaf_index: append.first_note_index,
        second_leaf_index: append.second_note_index,
        root_sequence: append.root_sequence,
        root: append.root,
    })?;
    let next_image: Box<[u8]> = vec![0u8; POOL_V1_PAIR_STATE_ACCOUNT_BYTES].into_boxed_slice();
    let mut next_image: Box<[u8; POOL_V1_PAIR_STATE_ACCOUNT_BYTES]> = next_image
        .try_into()
        .map_err(|_| ProgramError::InvalidAccountData)?;
    next_state.write_encoding_prevalidated(&mut next_image);
    pair_cu_checkpoint("aspis-pair-cu:receipt_and_state_image_ready");

    if let Some(next_index) = layout.next_index {
        let location = root_history_location(append.root_sequence);
        write_new_page_unchecked(
            &mut accounts[next_index].try_borrow_mut_data()?,
            pool.key,
            location.page_number,
            location.page_number * POOL_V1_ROOT_HISTORY_CAPACITY as u64,
            &[append.root],
        );
    } else {
        let current = &accounts[layout.current_index];
        let mut current_data = current.try_borrow_mut_data()?;
        let current_location = root_history_location(state.current_root_sequence());
        let header =
            validate_root_page_bytes(&current_data, pool.key, current_location.page_number)?;
        append_roots_unchecked(&mut current_data, header, &[append.root]);
    }
    pair_cu_checkpoint("aspis-pair-cu:history_written");
    pool.try_borrow_mut_data()?
        .copy_from_slice(next_image.as_ref());
    pair_cu_checkpoint("aspis-pair-cu:pool_state_written");
    marker
        .try_borrow_mut_data()?
        .copy_from_slice(&planned_marker.encoded_marker());
    pair_cu_checkpoint("aspis-pair-cu:marker_written");
    set_return_data(&receipt);
    pair_cu_checkpoint("aspis-pair-cu:receipt_returned");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::M31;
    use aspis_statement::{
        pool_v1::{
            encode_pool_v1_pair_verified_afterstate_v1, HistoricalAnchorEnvelopeV1,
            PoolV1PairVerifiedAfterstateV1, VerifierPolicyV1,
            POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
        },
        poseidon2::Digest,
    };
    use sha2::{Digest as _, Sha256};
    use solana_program::clock::Epoch;
    use std::{cell::RefCell, vec::Vec};

    use crate::{
        instruction::{encode_pair_private_transfer_instruction_v1, PrivateTransferStatementV1},
        nullifier::pool_v1_nullifier_marker_address,
        pair_state::{pool_v1_pair_state_address, PairPoolStateV1},
        state::PoolInitializationV1,
        vault::LEGACY_SPL_TOKEN_PROGRAM_ID,
    };

    fn sha256(parts: &[&[u8]]) -> [u8; 32] {
        let mut hash = Sha256::new();
        for part in parts {
            hash.update(part);
        }
        hash.finalize().into()
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|lane| M31(seed + 17 * lane as u32 + 1))
    }

    fn authenticated_afterstate(
        state: &PairPoolStateV1,
        verifier: &Pubkey,
    ) -> AuthenticatedPairAfterstateV1 {
        let bytes = encode_pool_v1_pair_verified_afterstate_v1(&PoolV1PairVerifiedAfterstateV1 {
            next_pair_index: state.tree.next_leaf_index,
            next_root: state.tree.root,
            next_frontier: state.tree.frontier,
        })
        .unwrap();
        crate::pair_dispatch::authenticate_pair_verified_afterstate_return_v1(
            verifier, verifier, &bytes,
        )
        .unwrap()
    }

    fn account<'a>(
        key: &'a Pubkey,
        owner: &'a Pubkey,
        lamports: &'a mut u64,
        data: &'a mut [u8],
        writable: bool,
        executable: bool,
    ) -> AccountInfo<'a> {
        AccountInfo::new(
            key,
            false,
            writable,
            lamports,
            data,
            owner,
            executable,
            Epoch::default(),
        )
    }

    fn instruction(
        pool: Pubkey,
        domain: [u8; 32],
        anchor_sequence: u64,
        anchor_root: Digest,
        nullifier: Digest,
        first: Digest,
        second: Digest,
    ) -> [u8; crate::instruction::POOL_V1_SPEND_INSTRUCTION_BYTES] {
        let envelope = HistoricalAnchorEnvelopeV1 {
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            pool: pool.to_bytes(),
            deployment_domain: domain,
            anchor_sequence,
            anchor_root,
            nullifier,
            verifier_profile: [9u8; 32],
            verifier_release: [10u8; 32],
        };
        encode_pair_private_transfer_instruction_v1(
            &envelope,
            &PrivateTransferStatementV1 {
                pool: pool.to_bytes(),
                deployment_domain: domain,
                anchor_sequence,
                anchor_root,
                nullifier,
                asset_id: M31(4),
                recipient_commitment: first,
                change_commitment: second,
            },
        )
        .unwrap()
    }

    #[test]
    fn proof_carried_afterstate_updates_bytes_and_stale_replay_or_failure_roll_back() {
        let program_id = Pubkey::new_unique();
        let mint = Pubkey::new_unique();
        let pool_key = pool_v1_pair_state_address(&program_id, &mint).0;
        let domain = [5u8; 32];
        let policy = VerifierPolicyV1 {
            flags: 0,
            registry_program: [6u8; 32],
            registry_authority: [7u8; 32],
            policy_binding: [8u8; 32],
        };
        let genesis = PairPoolStateV1::genesis(
            &pool_key,
            PoolInitializationV1 {
                asset_mint: mint.to_bytes(),
                token_program: LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes(),
                asset_id: M31(4),
                deployment_domain: domain,
                verifier_policy: policy,
            },
        )
        .unwrap();
        let genesis_root = genesis.tree.root;
        let mut pool_data = genesis.encode().unwrap();
        let history_key = crate::pool_v1_root_page_address(&program_id, &pool_key, 0).0;
        let mut history_data = [0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        write_new_page_unchecked(&mut history_data, &pool_key, 0, 0, &[genesis_root]);
        let registry_key = Pubkey::new_unique();
        let entry_key = Pubkey::new_unique();
        let verifier_key = Pubkey::new_unique();
        let proof_key = Pubkey::new_unique();
        let loader = solana_sdk_ids::bpf_loader::id();
        let mut registry_data = [];
        let mut entry_data = [];
        let mut verifier_data = [];
        let mut proof_data = [];
        let mut pool_lamports = 1;
        let mut history_lamports = 1;
        let mut registry_lamports = 1;
        let mut entry_lamports = 1;
        let mut verifier_lamports = 1;
        let mut proof_lamports = 1;

        let first_a = digest(100);
        let second_a = digest(200);
        let pair_a = aspis_statement::pool_v1::pool_v1_tree_parent(&first_a, &second_a);
        let expected_a = genesis
            .append_verified_pair_from_program_invariant(pair_a)
            .unwrap()
            .0;
        let nullifier_a = digest(300);
        let instruction_a = instruction(
            pool_key,
            domain,
            0,
            genesis_root,
            nullifier_a,
            first_a,
            second_a,
        );
        let marker_a = PoolV1NullifierMarkerV1::from_historical_anchor(
            &decode_pair_private_transfer_instruction_v1(&instruction_a)
                .unwrap()
                .envelope,
        );
        let marker_a_key = pool_v1_nullifier_marker_address(
            &program_id,
            &pool_key,
            &marker_a.canonical_nullifier_encoding(),
        )
        .unwrap()
        .0;
        let mut marker_a_data =
            [0u8; aspis_statement::pool_v1::POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES];
        let mut marker_a_lamports = 1;
        let returned = RefCell::new(Vec::new());
        {
            let accounts = vec![
                account(
                    &pool_key,
                    &program_id,
                    &mut pool_lamports,
                    &mut pool_data,
                    true,
                    false,
                ),
                account(
                    &history_key,
                    &program_id,
                    &mut history_lamports,
                    &mut history_data,
                    true,
                    false,
                ),
                account(
                    &marker_a_key,
                    &program_id,
                    &mut marker_a_lamports,
                    &mut marker_a_data,
                    true,
                    false,
                ),
                account(
                    &registry_key,
                    &program_id,
                    &mut registry_lamports,
                    &mut registry_data,
                    false,
                    false,
                ),
                account(
                    &entry_key,
                    &program_id,
                    &mut entry_lamports,
                    &mut entry_data,
                    false,
                    false,
                ),
                account(
                    &verifier_key,
                    &loader,
                    &mut verifier_lamports,
                    &mut verifier_data,
                    false,
                    true,
                ),
                account(
                    &proof_key,
                    &verifier_key,
                    &mut proof_lamports,
                    &mut proof_data,
                    false,
                    false,
                ),
            ];
            process_pair_private_transfer_with_verifier_v1(
                &program_id,
                &accounts,
                &instruction_a,
                20,
                sha256,
                |_, _, _, _, _, _, _, _, _, _| {
                    Ok(authenticated_afterstate(&expected_a, &verifier_key))
                },
                |bytes| returned.borrow_mut().extend_from_slice(bytes),
            )
            .unwrap();
        }
        assert_eq!(returned.borrow().len(), 200);
        assert!(marker_a_data.iter().any(|byte| *byte != 0));
        let after_a =
            PairPoolStateV1::decode_from_program_invariant(&pool_data, &pool_key).unwrap();
        assert_eq!(after_a.current_root_sequence(), 1);

        // Historical membership still uses retained genesis, while the
        // proof-carried append suffix is completed against the live state
        // produced by A.  The two root roles remain deliberately distinct.
        let first_b = digest(400);
        let second_b = digest(500);
        let pair_b = aspis_statement::pool_v1::pool_v1_tree_parent(&first_b, &second_b);
        let expected_b = expected_a
            .append_verified_pair_from_program_invariant(pair_b)
            .unwrap()
            .0;
        let nullifier_b = digest(600);
        let instruction_b = instruction(
            pool_key,
            domain,
            0,
            genesis_root,
            nullifier_b,
            first_b,
            second_b,
        );
        let marker_b = PoolV1NullifierMarkerV1::from_historical_anchor(
            &decode_pair_private_transfer_instruction_v1(&instruction_b)
                .unwrap()
                .envelope,
        );
        let marker_b_key = pool_v1_nullifier_marker_address(
            &program_id,
            &pool_key,
            &marker_b.canonical_nullifier_encoding(),
        )
        .unwrap()
        .0;
        let mut marker_b_data =
            [0u8; aspis_statement::pool_v1::POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES];
        let mut marker_b_lamports = 1;
        {
            let accounts = vec![
                account(
                    &pool_key,
                    &program_id,
                    &mut pool_lamports,
                    &mut pool_data,
                    true,
                    false,
                ),
                account(
                    &history_key,
                    &program_id,
                    &mut history_lamports,
                    &mut history_data,
                    true,
                    false,
                ),
                account(
                    &marker_b_key,
                    &program_id,
                    &mut marker_b_lamports,
                    &mut marker_b_data,
                    true,
                    false,
                ),
                account(
                    &registry_key,
                    &program_id,
                    &mut registry_lamports,
                    &mut registry_data,
                    false,
                    false,
                ),
                account(
                    &entry_key,
                    &program_id,
                    &mut entry_lamports,
                    &mut entry_data,
                    false,
                    false,
                ),
                account(
                    &verifier_key,
                    &loader,
                    &mut verifier_lamports,
                    &mut verifier_data,
                    false,
                    true,
                ),
                account(
                    &proof_key,
                    &verifier_key,
                    &mut proof_lamports,
                    &mut proof_data,
                    false,
                    false,
                ),
            ];
            process_pair_private_transfer_with_verifier_v1(
                &program_id,
                &accounts,
                &instruction_b,
                21,
                sha256,
                |_, _, _, _, _, _, _, _, _, _| {
                    Ok(authenticated_afterstate(&expected_b, &verifier_key))
                },
                |_| {},
            )
            .unwrap();
        }
        let after_b =
            PairPoolStateV1::decode_from_program_invariant(&pool_data, &pool_key).unwrap();
        assert_eq!(after_b.current_root_sequence(), 2);
        assert_eq!(
            u16::from_le_bytes(history_data[56..58].try_into().unwrap()),
            3
        );

        // Exact replay rejects before verifier dispatch and changes nothing.
        let pool_before = pool_data;
        let history_before = history_data;
        let marker_before = marker_b_data;
        {
            let accounts = vec![
                account(
                    &pool_key,
                    &program_id,
                    &mut pool_lamports,
                    &mut pool_data,
                    true,
                    false,
                ),
                account(
                    &history_key,
                    &program_id,
                    &mut history_lamports,
                    &mut history_data,
                    true,
                    false,
                ),
                account(
                    &marker_b_key,
                    &program_id,
                    &mut marker_b_lamports,
                    &mut marker_b_data,
                    true,
                    false,
                ),
                account(
                    &registry_key,
                    &program_id,
                    &mut registry_lamports,
                    &mut registry_data,
                    false,
                    false,
                ),
                account(
                    &entry_key,
                    &program_id,
                    &mut entry_lamports,
                    &mut entry_data,
                    false,
                    false,
                ),
                account(
                    &verifier_key,
                    &loader,
                    &mut verifier_lamports,
                    &mut verifier_data,
                    false,
                    true,
                ),
                account(
                    &proof_key,
                    &verifier_key,
                    &mut proof_lamports,
                    &mut proof_data,
                    false,
                    false,
                ),
            ];
            assert_eq!(
                process_pair_private_transfer_with_verifier_v1(
                    &program_id,
                    &accounts,
                    &instruction_b,
                    22,
                    sha256,
                    |_, _, _, _, _, _, _, _, _, _| panic!("replay reached verifier"),
                    |_| {},
                ),
                Err(PoolV1ProgramError::NullifierAlreadyConsumed.into())
            );
        }
        assert_eq!(pool_data, pool_before);
        assert_eq!(history_data, history_before);
        assert_eq!(marker_b_data, marker_before);

        // A stale proof-carried afterstate with a fresh marker leaves all
        // state byte-exact.
        let nullifier_c = digest(700);
        let instruction_c = instruction(
            pool_key,
            domain,
            0,
            genesis_root,
            nullifier_c,
            digest(800),
            digest(900),
        );
        let marker_c = PoolV1NullifierMarkerV1::from_historical_anchor(
            &decode_pair_private_transfer_instruction_v1(&instruction_c)
                .unwrap()
                .envelope,
        );
        let marker_c_key = pool_v1_nullifier_marker_address(
            &program_id,
            &pool_key,
            &marker_c.canonical_nullifier_encoding(),
        )
        .unwrap()
        .0;
        let mut marker_c_data =
            [0u8; aspis_statement::pool_v1::POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES];
        let mut marker_c_lamports = 1;
        {
            let accounts = vec![
                account(
                    &pool_key,
                    &program_id,
                    &mut pool_lamports,
                    &mut pool_data,
                    true,
                    false,
                ),
                account(
                    &history_key,
                    &program_id,
                    &mut history_lamports,
                    &mut history_data,
                    true,
                    false,
                ),
                account(
                    &marker_c_key,
                    &program_id,
                    &mut marker_c_lamports,
                    &mut marker_c_data,
                    true,
                    false,
                ),
                account(
                    &registry_key,
                    &program_id,
                    &mut registry_lamports,
                    &mut registry_data,
                    false,
                    false,
                ),
                account(
                    &entry_key,
                    &program_id,
                    &mut entry_lamports,
                    &mut entry_data,
                    false,
                    false,
                ),
                account(
                    &verifier_key,
                    &loader,
                    &mut verifier_lamports,
                    &mut verifier_data,
                    false,
                    true,
                ),
                account(
                    &proof_key,
                    &verifier_key,
                    &mut proof_lamports,
                    &mut proof_data,
                    false,
                    false,
                ),
            ];
            assert_eq!(
                process_pair_private_transfer_with_verifier_v1(
                    &program_id,
                    &accounts,
                    &instruction_c,
                    23,
                    sha256,
                    |_, _, _, _, _, _, _, _, _, _| {
                        Ok(authenticated_afterstate(&expected_a, &verifier_key))
                    },
                    |_| {},
                ),
                Err(PoolV1ProgramError::StateHistoryMismatch.into())
            );
        }
        assert_eq!(pool_data, pool_before);
        assert_eq!(history_data, history_before);
        assert!(marker_c_data.iter().all(|byte| *byte == 0));
    }
}
