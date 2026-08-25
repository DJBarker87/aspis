//! Authenticated initialization and internal atomic tree/history transitions.
//!
//! There is deliberately no public raw-append API. The native instruction
//! processor calls these crate-private functions only after backing or proof
//! authorization has succeeded.

extern crate alloc;

use alloc::boxed::Box;

use aspis_core::field::M31;
#[cfg(test)]
use aspis_statement::pool_v1::{IncrementalMerkleTreeV1, POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES};
use aspis_statement::{
    pool_v1::{
        root_history_location, AppendOneV1, PoolV1TreeError, POOL_V1_LEAF_CAPACITY,
        POOL_V1_ROOT_HISTORY_CAPACITY,
    },
    poseidon2::{Digest, DIGEST_ELEMS},
};
use solana_program::{account_info::AccountInfo, program_error::ProgramError, pubkey::Pubkey};

use crate::{
    anchor::PrevalidatedHistoricalAnchorV1,
    empty_roots::POOL_V1_EMPTY_ROOTS,
    error::PoolV1ProgramError,
    history::{
        append_roots_unchecked, digest_is_canonical, read_retained_root, require_program_account,
        require_program_owned, require_root_page_address, validate_new_page_account,
        validate_root_page_bytes, write_new_page_unchecked, RootPageHeaderV1,
    },
    state::{
        pool_v1_state_address, CanonicalPoolStateV1, PoolInitializationV1, PoolStateV1,
        POOL_V1_STATE_ACCOUNT_BYTES,
    },
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum AuthorizedAppendV1 {
    One(Digest),
    Two(Digest, Digest),
}

impl AuthorizedAppendV1 {
    fn count(self) -> u64 {
        match self {
            Self::One(_) => 1,
            Self::Two(_, _) => 2,
        }
    }

    fn validate_leaves(self) -> Result<(), ProgramError> {
        let valid = match self {
            Self::One(leaf) => digest_is_canonical(&leaf),
            Self::Two(first, second) => digest_is_canonical(&first) && digest_is_canonical(&second),
        };
        if !valid {
            return Err(PoolV1ProgramError::NonCanonicalLeaf.into());
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct AuthorizedAppendReceiptV1 {
    pub first: AppendOneV1,
    pub second: Option<AppendOneV1>,
}

/// Sealed evidence that the current root-history page passed one complete
/// canonical validation for one exact Pool state.  It can only be created
/// before verifier dispatch, while the Pool/current-page accounts are not
/// exposed to any CPI, and is identity-bound again at append consumption.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct PrevalidatedCurrentHistoryV1 {
    program_id: Pubkey,
    pool: Pubkey,
    history_page: Pubkey,
    sequence: u64,
    root: Digest,
    header: RootPageHeaderV1,
}

impl PrevalidatedCurrentHistoryV1 {
    fn require_matches(
        self,
        program_id: &Pubkey,
        pool_account: &AccountInfo,
        history_account: &AccountInfo,
        state: &PoolStateV1,
    ) -> Result<RootPageHeaderV1, ProgramError> {
        require_program_owned(history_account, program_id)?;
        let location = root_history_location(state.current_root_sequence());
        require_root_page_address(
            program_id,
            pool_account.key,
            location.page_number,
            history_account,
        )?;
        if self.program_id != *program_id
            || self.pool != *pool_account.key
            || self.history_page != *history_account.key
            || self.sequence != state.current_root_sequence()
            || self.root != state.tree.root
            || self.header.pool != *pool_account.key
            || self.header.page_number != location.page_number
            || self.header.filled != location.slot + 1
        {
            return Err(PoolV1ProgramError::StateHistoryMismatch.into());
        }
        Ok(self.header)
    }
}

/// A transition whose output tree was produced by the checked incremental
/// append kernel. Its fields are private so persistence cannot receive an
/// arbitrary, unchecked next-state image.
#[derive(Clone, Debug, PartialEq, Eq)]
struct PreparedAuthorizedAppendV1 {
    next_state: Box<PoolStateV1>,
    receipt: AuthorizedAppendReceiptV1,
}

#[derive(Clone, Copy)]
enum AuthorizedSourceStateV1<'a> {
    /// The processor's sealed result of one complete account decode/PDA check.
    Canonical(&'a CanonicalPoolStateV1),
    /// The compatibility wrapper's locally decoded state. This path retains
    /// its historical extra whole-state validation below.
    Standalone(&'a PoolStateV1),
}

impl<'a> AuthorizedSourceStateV1<'a> {
    fn as_state(self) -> &'a PoolStateV1 {
        match self {
            Self::Canonical(state) => state.as_state(),
            Self::Standalone(state) => state,
        }
    }

    fn prepare(
        self,
        request: AuthorizedAppendV1,
    ) -> Result<PreparedAuthorizedAppendV1, ProgramError> {
        let source = self.as_state();
        let prepared = match self {
            Self::Canonical(state) => prepare_append_from_validated_tree(state, request)?,
            Self::Standalone(_) => {
                let prepared = prepare_checked_append(source, request)?;
                prepared.next_state.validate_encoding()?;
                prepared
            }
        };
        prepared.validate_inherited_state_and_cursor(source, request)?;
        Ok(prepared)
    }
}

impl PreparedAuthorizedAppendV1 {
    /// The checked append already validates its produced tree. For a sealed
    /// canonical source, the only remaining Pool-state invariants are that
    /// immutable identity/policy fields were inherited and the exact cursor /
    /// receipt progression agrees with the requested append count.
    fn validate_inherited_state_and_cursor(
        &self,
        source: &PoolStateV1,
        request: AuthorizedAppendV1,
    ) -> Result<(), ProgramError> {
        let first_sequence = source
            .current_root_sequence()
            .checked_add(1)
            .ok_or(PoolV1ProgramError::ArithmeticOverflow)?;
        let final_sequence = source
            .current_root_sequence()
            .checked_add(request.count())
            .ok_or(PoolV1ProgramError::ArithmeticOverflow)?;
        let receipt_shape_is_exact = self.receipt.first.leaf_index
            == source.current_root_sequence()
            && self.receipt.first.root_sequence == first_sequence
            && match (request, self.receipt.second) {
                (AuthorizedAppendV1::One(_), None) => {
                    self.receipt.first.root == self.next_state.tree.root
                }
                (AuthorizedAppendV1::Two(_, _), Some(second)) => {
                    second.leaf_index == first_sequence
                        && second.root_sequence == final_sequence
                        && second.root == self.next_state.tree.root
                }
                _ => false,
            };
        if self.next_state.identity != source.identity
            || self.next_state.verifier_policy != source.verifier_policy
            || self.next_state.current_root_sequence() != final_sequence
            || !receipt_shape_is_exact
        {
            return Err(ProgramError::InvalidAccountData);
        }
        Ok(())
    }
}

fn map_tree_error(error: PoolV1TreeError) -> ProgramError {
    match error {
        PoolV1TreeError::TreeFull => PoolV1ProgramError::TreeFull.into(),
        PoolV1TreeError::InsufficientCapacity => {
            PoolV1ProgramError::InsufficientTreeCapacity.into()
        }
        _ => ProgramError::InvalidAccountData,
    }
}

#[inline(never)]
fn prepare_checked_append(
    state: &PoolStateV1,
    request: AuthorizedAppendV1,
) -> Result<PreparedAuthorizedAppendV1, ProgramError> {
    let mut next_state = Box::new(*state);
    let (tree, receipt) = match request {
        AuthorizedAppendV1::One(leaf) => {
            let (tree, receipt) = next_state
                .tree
                .append_one_with_empty_roots(leaf, &POOL_V1_EMPTY_ROOTS)
                .map_err(map_tree_error)?;
            (
                tree,
                AuthorizedAppendReceiptV1 {
                    first: receipt,
                    second: None,
                },
            )
        }
        AuthorizedAppendV1::Two(first, second) => {
            let (tree, receipts) = next_state
                .tree
                .append_two_with_empty_roots(first, second, &POOL_V1_EMPTY_ROOTS)
                .map_err(map_tree_error)?;
            (
                tree,
                AuthorizedAppendReceiptV1 {
                    first: receipts.first,
                    second: Some(receipts.second),
                },
            )
        }
    };
    next_state.tree = tree;
    Ok(PreparedAuthorizedAppendV1 {
        next_state,
        receipt,
    })
}

#[inline(never)]
fn prepare_append_from_validated_tree(
    state: &CanonicalPoolStateV1,
    request: AuthorizedAppendV1,
) -> Result<PreparedAuthorizedAppendV1, ProgramError> {
    if state.as_state().tree != *state.validated_tree().as_tree() {
        return Err(ProgramError::InvalidAccountData);
    }
    let mut next_state = Box::new(*state.as_state());
    let (tree, receipt) = match request {
        AuthorizedAppendV1::One(leaf) => {
            let (tree, receipt) = state
                .validated_tree()
                .append_one(leaf)
                .map_err(map_tree_error)?;
            (
                tree.into_inner(),
                AuthorizedAppendReceiptV1 {
                    first: receipt,
                    second: None,
                },
            )
        }
        AuthorizedAppendV1::Two(first, second) => {
            let (tree, receipts) = state
                .validated_tree()
                .append_two(first, second)
                .map_err(map_tree_error)?;
            (
                tree.into_inner(),
                AuthorizedAppendReceiptV1 {
                    first: receipts.first,
                    second: Some(receipts.second),
                },
            )
        }
    };
    next_state.tree = tree;
    Ok(PreparedAuthorizedAppendV1 {
        next_state,
        receipt,
    })
}

pub(crate) fn validate_current_history(
    program_id: &Pubkey,
    pool_account: &AccountInfo,
    history_account: &AccountInfo,
    state: &PoolStateV1,
) -> Result<RootPageHeaderV1, ProgramError> {
    let sequence = state.current_root_sequence();
    let location = root_history_location(sequence);
    require_program_owned(history_account, program_id)?;
    require_root_page_address(
        program_id,
        pool_account.key,
        location.page_number,
        history_account,
    )?;
    let data = history_account.try_borrow_data()?;
    let header = validate_root_page_bytes(&data, pool_account.key, location.page_number)?;
    if header.filled != location.slot + 1 {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    let retained = read_retained_root(&data, header, sequence)?;
    if retained != state.tree.root {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    if sequence == POOL_V1_LEAF_CAPACITY {
        state
            .tree
            .validate_terminal_root_against_history_with_empty_roots(
                &retained,
                &POOL_V1_EMPTY_ROOTS,
            )
            .map_err(map_tree_error)?;
    }
    Ok(header)
}

/// Validate the current page exactly once after historical-anchor
/// authentication.  When the anchor and current root live in the same page,
/// reuse the anchor's sealed full-page validation and re-read only the exact
/// current root.  Distinct historical/current pages retain one complete
/// validation each.
pub(crate) fn validate_current_history_after_prevalidated_anchor_v1(
    program_id: &Pubkey,
    pool_account: &AccountInfo,
    history_account: &AccountInfo,
    state: &CanonicalPoolStateV1,
    anchor: PrevalidatedHistoricalAnchorV1,
) -> Result<PrevalidatedCurrentHistoryV1, ProgramError> {
    state.require_same_writable_account(program_id, pool_account)?;
    let sequence = state.current_root_sequence();
    let location = root_history_location(sequence);
    let authenticated = anchor.authenticated();
    if authenticated.pool != pool_account.key.to_bytes()
        || authenticated.pool != state.identity.pool
        || authenticated.anchor_sequence > sequence
    {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }

    let header = if anchor.history_page() == *history_account.key
        && anchor.header().page_number == location.page_number
    {
        require_program_owned(history_account, program_id)?;
        require_root_page_address(
            program_id,
            pool_account.key,
            location.page_number,
            history_account,
        )?;
        let header = anchor.header();
        if header.pool != *pool_account.key || header.filled != location.slot + 1 {
            return Err(PoolV1ProgramError::StateHistoryMismatch.into());
        }
        let data = history_account.try_borrow_data()?;
        let retained = read_retained_root(&data, header, sequence)?;
        if retained != state.tree.root {
            return Err(PoolV1ProgramError::StateHistoryMismatch.into());
        }
        if sequence == POOL_V1_LEAF_CAPACITY {
            state
                .tree
                .validate_terminal_root_against_history_with_empty_roots(
                    &retained,
                    &POOL_V1_EMPTY_ROOTS,
                )
                .map_err(map_tree_error)?;
        }
        header
    } else {
        validate_current_history(program_id, pool_account, history_account, state.as_state())?
    };

    Ok(PrevalidatedCurrentHistoryV1 {
        program_id: *program_id,
        pool: *pool_account.key,
        history_page: *history_account.key,
        sequence,
        root: state.tree.root,
        header,
    })
}

/// Initialize exactly `[pool_state, root_page_0]`.
///
/// The pool account must be the writable canonical per-mint Pool V1 PDA,
/// already owned by this Pool program. It need not be a transaction signer:
/// the entrypoint initializer creates it with `invoke_signed`. The page must
/// be the canonical writable page-zero PDA. Both accounts must have their
/// exact lengths and contain only zero bytes. This kernel performs no
/// system-program CPI.
pub(crate) fn initialize_pool_accounts_v1(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    initialization: PoolInitializationV1,
) -> Result<(), ProgramError> {
    let [pool_account, page_zero_account] = accounts else {
        return Err(ProgramError::NotEnoughAccountKeys);
    };
    require_program_account(pool_account, program_id, true)?;
    let asset_mint = Pubkey::new_from_array(initialization.asset_mint);
    if pool_account.key != &pool_v1_state_address(program_id, &asset_mint).0 {
        return Err(PoolV1ProgramError::InvalidPoolStateAddress.into());
    }
    validate_new_page_account(program_id, pool_account.key, 0, page_zero_account)?;
    if pool_account.key == page_zero_account.key {
        return Err(ProgramError::InvalidAccountData);
    }
    {
        let pool_data = pool_account.try_borrow_data()?;
        if pool_data.len() != POOL_V1_STATE_ACCOUNT_BYTES || pool_data.iter().any(|byte| *byte != 0)
        {
            return Err(ProgramError::InvalidAccountData);
        }
    }
    let state = PoolStateV1::genesis_boxed(pool_account.key, initialization)?;
    state.validate_encoding()?;

    // Acquire every mutable borrow before the first write. Borrow failure
    // therefore cannot leave a partially initialized account pair.
    let mut pool_data = pool_account.try_borrow_mut_data()?;
    let pool_image: &mut [u8; POOL_V1_STATE_ACCOUNT_BYTES] = (&mut **pool_data)
        .try_into()
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let mut page_data = page_zero_account.try_borrow_mut_data()?;
    state.write_encoding_prevalidated(pool_image);
    write_new_page_unchecked(
        &mut page_data,
        pool_account.key,
        0,
        0,
        &[POOL_V1_EMPTY_ROOTS[aspis_statement::pool_v1::POOL_V1_TREE_DEPTH]],
    );
    Ok(())
}

/// Apply an already-authorized append to exactly the required accounts.
///
/// Account order is `[pool_state, current_root_page]` without rollover and
/// `[pool_state, current_root_page, zeroed_next_root_page]` with rollover.
/// This function is crate-private and is reachable only after the entrypoint's
/// deposit/proof/vault authorization path has completed its preflight.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn apply_authorized_append_after_checked_state_v1<F>(
    program_id: &Pubkey,
    pool_account: &AccountInfo,
    current_page_account: &AccountInfo,
    supplied_next_page: Option<&AccountInfo>,
    source: AuthorizedSourceStateV1<'_>,
    prevalidated_history: Option<PrevalidatedCurrentHistoryV1>,
    request: AuthorizedAppendV1,
    before_persist: F,
) -> Result<AuthorizedAppendReceiptV1, ProgramError>
where
    F: FnOnce() -> Result<(), ProgramError>,
{
    let state = source.as_state();
    let current_header = match prevalidated_history {
        Some(history) => {
            history.require_matches(program_id, pool_account, current_page_account, state)?
        }
        None => validate_current_history(program_id, pool_account, current_page_account, state)?,
    };

    let count = request.count();
    let remaining = POOL_V1_LEAF_CAPACITY
        .checked_sub(state.current_root_sequence())
        .ok_or(PoolV1ProgramError::StateHistoryMismatch)?;
    if remaining == 0 {
        return Err(PoolV1ProgramError::TreeFull.into());
    }
    if remaining < count {
        return Err(PoolV1ProgramError::InsufficientTreeCapacity.into());
    }

    let first_location = root_history_location(state.current_root_sequence() + 1);
    let last_location = root_history_location(state.current_root_sequence() + count);
    let current_page_number = current_header.page_number;
    if first_location.page_number < current_page_number
        || last_location.page_number > current_page_number + 1
    {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    let roots_in_current = if first_location.page_number == current_page_number {
        if last_location.page_number == current_page_number {
            count as usize
        } else {
            1
        }
    } else {
        0
    };
    let roots_in_next = count as usize - roots_in_current;
    let mutate_current = roots_in_current != 0;
    if current_page_account.is_writable != mutate_current {
        return Err(ProgramError::InvalidAccountData);
    }
    let next_page = match (roots_in_next != 0, supplied_next_page) {
        (false, None) => None,
        (true, Some(next)) => {
            let next_page_number = current_page_number
                .checked_add(1)
                .ok_or(PoolV1ProgramError::ArithmeticOverflow)?;
            let first_sequence = next_page_number
                .checked_mul(POOL_V1_ROOT_HISTORY_CAPACITY as u64)
                .ok_or(PoolV1ProgramError::ArithmeticOverflow)?;
            validate_new_page_account(program_id, pool_account.key, next_page_number, next)?;
            if next.key == pool_account.key || next.key == current_page_account.key {
                return Err(ProgramError::InvalidAccountData);
            }
            Some((next, next_page_number, first_sequence))
        }
        _ => return Err(PoolV1ProgramError::UnexpectedRootPage.into()),
    };
    let next_page_metadata =
        next_page.map(|(_, page_number, first_sequence)| (page_number, first_sequence));
    if pool_account.key == current_page_account.key {
        return Err(ProgramError::InvalidAccountData);
    }

    let plan = source.prepare(request)?;
    let mut current_roots = [[M31::ZERO; DIGEST_ELEMS]; 2];
    let mut next_roots = [[M31::ZERO; DIGEST_ELEMS]; 2];
    let first = plan.receipt.first.root;
    let second = plan.receipt.second.map(|receipt| receipt.root);
    if roots_in_current == 0 {
        next_roots[0] = first;
        if let Some(root) = second {
            next_roots[1] = root;
        }
    } else {
        current_roots[0] = first;
        if roots_in_current == 2 {
            current_roots[1] = second.ok_or(ProgramError::InvalidAccountData)?;
        } else if let Some(root) = second {
            next_roots[0] = root;
        }
    }
    if usize::from(current_header.filled) + roots_in_current > POOL_V1_ROOT_HISTORY_CAPACITY {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    // Acquire every mutable Pool-state borrow before the backing or proof
    // action. A deposit uses `before_persist` for its token CPI and exact
    // post-CPI balance-delta check. If it fails, no Pool bytes have changed;
    // if it succeeds, persistence below contains no fallible operation.
    let mut pool_data = pool_account.try_borrow_mut_data()?;
    let pool_image: &mut [u8; POOL_V1_STATE_ACCOUNT_BYTES] = (&mut **pool_data)
        .try_into()
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let mut current_data = if mutate_current {
        Some(current_page_account.try_borrow_mut_data()?)
    } else {
        None
    };
    let mut next_data = match next_page {
        Some((next, _, _)) => Some(next.try_borrow_mut_data()?),
        None => None,
    };
    before_persist()?;
    plan.next_state.write_encoding_prevalidated(pool_image);
    if let Some(data) = current_data.as_mut() {
        append_roots_unchecked(data, current_header, &current_roots[..roots_in_current]);
    }
    if let (Some(data), Some((page_number, first_sequence))) =
        (next_data.as_mut(), next_page_metadata)
    {
        write_new_page_unchecked(
            data,
            pool_account.key,
            page_number,
            first_sequence,
            &next_roots[..roots_in_next],
        );
    }
    Ok(plan.receipt)
}

/// Apply an append using the processor's one canonical decoded-state token.
/// Account/PDA identity and leaf canonicality are re-checked, but the Pool
/// image and depth-20 root are not decoded or reconstructed again.
#[inline(never)]
pub(crate) fn apply_authorized_append_after_prevalidated_v1<F>(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    state: &CanonicalPoolStateV1,
    request: AuthorizedAppendV1,
    before_persist: F,
) -> Result<AuthorizedAppendReceiptV1, ProgramError>
where
    F: FnOnce() -> Result<(), ProgramError>,
{
    let (pool_account, current_page_account, supplied_next_page) = match accounts {
        [pool, current] => (pool, current, None),
        [pool, current, next] => (pool, current, Some(next)),
        _ => return Err(ProgramError::NotEnoughAccountKeys),
    };
    state.require_same_writable_account(program_id, pool_account)?;
    request.validate_leaves()?;
    apply_authorized_append_after_checked_state_v1(
        program_id,
        pool_account,
        current_page_account,
        supplied_next_page,
        AuthorizedSourceStateV1::Canonical(state),
        None,
        request,
        before_persist,
    )
}

/// Consume both the processor's sealed Pool decode and its sealed current-page
/// validation.  No intervening CPI receives either account, so this skips
/// only a duplicate full-page scan while retaining cheap identity binding.
#[inline(never)]
pub(crate) fn apply_authorized_append_after_prevalidated_history_v1<F>(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    state: &CanonicalPoolStateV1,
    history: PrevalidatedCurrentHistoryV1,
    request: AuthorizedAppendV1,
    before_persist: F,
) -> Result<AuthorizedAppendReceiptV1, ProgramError>
where
    F: FnOnce() -> Result<(), ProgramError>,
{
    let (pool_account, current_page_account, supplied_next_page) = match accounts {
        [pool, current] => (pool, current, None),
        [pool, current, next] => (pool, current, Some(next)),
        _ => return Err(ProgramError::NotEnoughAccountKeys),
    };
    state.require_same_writable_account(program_id, pool_account)?;
    request.validate_leaves()?;
    apply_authorized_append_after_checked_state_v1(
        program_id,
        pool_account,
        current_page_account,
        supplied_next_page,
        AuthorizedSourceStateV1::Canonical(state),
        Some(history),
        request,
        before_persist,
    )
}

#[inline(never)]
pub(crate) fn apply_authorized_append_after_v1<F>(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    request: AuthorizedAppendV1,
    before_persist: F,
) -> Result<AuthorizedAppendReceiptV1, ProgramError>
where
    F: FnOnce() -> Result<(), ProgramError>,
{
    let (pool_account, current_page_account, supplied_next_page) = match accounts {
        [pool, current] => (pool, current, None),
        [pool, current, next] => (pool, current, Some(next)),
        _ => return Err(ProgramError::NotEnoughAccountKeys),
    };
    require_program_account(pool_account, program_id, true)?;
    request.validate_leaves()?;
    let state = {
        let data = pool_account.try_borrow_data()?;
        PoolStateV1::decode_boxed(&data, pool_account.key)?
    };
    let asset_mint = Pubkey::new_from_array(state.identity.asset_mint);
    if pool_account.key != &pool_v1_state_address(program_id, &asset_mint).0 {
        return Err(PoolV1ProgramError::InvalidPoolStateAddress.into());
    }
    apply_authorized_append_after_checked_state_v1(
        program_id,
        pool_account,
        current_page_account,
        supplied_next_page,
        AuthorizedSourceStateV1::Standalone(&state),
        None,
        request,
        before_persist,
    )
}

#[cfg(test)]
fn apply_authorized_append_v1(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    request: AuthorizedAppendV1,
) -> Result<AuthorizedAppendReceiptV1, ProgramError> {
    apply_authorized_append_after_v1(program_id, accounts, request, || Ok(()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::P;
    use aspis_statement::pool_v1::{
        encode_historical_anchor_envelope_v1, pool_v1_tree_parent, HistoricalAnchorEnvelopeV1,
        PoolV1TransitionKind, RootHistoryPageV1, POOL_V1_TREE_DEPTH,
    };
    use solana_program::{clock::Epoch, program_error::ProgramError};
    use std::{cell::Cell, vec};

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31((seed + 101 * index as u32) % P))
    }

    fn initialization() -> PoolInitializationV1 {
        PoolInitializationV1 {
            asset_mint: [2u8; 32],
            token_program: crate::LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes(),
            asset_id: M31(4),
            deployment_domain: [5u8; 32],
            verifier_policy: aspis_statement::pool_v1::VerifierPolicyV1 {
                flags: 0,
                registry_program: [6u8; 32],
                registry_authority: [7u8; 32],
                policy_binding: [8u8; 32],
            },
        }
    }

    fn canonical_pool_key(program_id: &Pubkey) -> Pubkey {
        let asset_mint = Pubkey::new_from_array(initialization().asset_mint);
        pool_v1_state_address(program_id, &asset_mint).0
    }

    fn account<'a>(
        key: &'a Pubkey,
        owner: &'a Pubkey,
        lamports: &'a mut u64,
        data: &'a mut [u8],
        signer: bool,
        writable: bool,
    ) -> AccountInfo<'a> {
        AccountInfo::new(
            key,
            signer,
            writable,
            lamports,
            data,
            owner,
            false,
            Epoch::default(),
        )
    }

    fn initialize_fixture(
        program_id: &Pubkey,
        pool_key: &Pubkey,
        page_key: &Pubkey,
        pool_data: &mut [u8],
        page_data: &mut [u8],
        pool_lamports: &mut u64,
        page_lamports: &mut u64,
    ) {
        let pool = account(pool_key, program_id, pool_lamports, pool_data, false, true);
        let page = account(page_key, program_id, page_lamports, page_data, false, true);
        initialize_pool_accounts_v1(program_id, &[pool, page], initialization()).unwrap();
    }

    #[test]
    fn genesis_accepts_canonical_pool_pda_without_signer() {
        let program_id = Pubkey::new_unique();
        let pool_key = canonical_pool_key(&program_id);
        let page_key = crate::pool_v1_root_page_address(&program_id, &pool_key, 0).0;
        let mut pool_data = [0u8; POOL_V1_STATE_ACCOUNT_BYTES];
        let mut page_data = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        let mut pool_lamports = 1;
        let mut page_lamports = 1;
        initialize_fixture(
            &program_id,
            &pool_key,
            &page_key,
            &mut pool_data,
            &mut page_data,
            &mut pool_lamports,
            &mut page_lamports,
        );
        let state = PoolStateV1::decode(&pool_data, &pool_key).unwrap();
        assert_eq!(state.current_root_sequence(), 0);
        let header = validate_root_page_bytes(&page_data, &pool_key, 0).unwrap();
        assert_eq!(header.filled, 1);
        assert_eq!(
            read_retained_root(&page_data, header, 0).unwrap(),
            POOL_V1_EMPTY_ROOTS[POOL_V1_TREE_DEPTH]
        );
    }

    #[test]
    fn genesis_rejects_noncanonical_pool_address_without_writes() {
        let program_id = Pubkey::new_unique();
        let wrong_pool_key = Pubkey::new_unique();
        let page_key = crate::pool_v1_root_page_address(&program_id, &wrong_pool_key, 0).0;
        let mut pool_data = [0u8; POOL_V1_STATE_ACCOUNT_BYTES];
        let mut page_data = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        let mut pool_lamports = 1;
        let mut page_lamports = 1;
        let pool = account(
            &wrong_pool_key,
            &program_id,
            &mut pool_lamports,
            &mut pool_data,
            false,
            true,
        );
        let page = account(
            &page_key,
            &program_id,
            &mut page_lamports,
            &mut page_data,
            false,
            true,
        );
        assert_eq!(
            initialize_pool_accounts_v1(&program_id, &[pool, page], initialization()),
            Err(PoolV1ProgramError::InvalidPoolStateAddress.into())
        );
        assert!(pool_data.iter().all(|byte| *byte == 0));
        assert!(page_data.iter().all(|byte| *byte == 0));
    }

    #[test]
    fn genesis_rejects_wrong_page_address_and_nonzero_account_without_writes() {
        let program_id = Pubkey::new_unique();
        let pool_key = canonical_pool_key(&program_id);
        let correct_page_key = crate::pool_v1_root_page_address(&program_id, &pool_key, 0).0;
        let wrong_page_key = Pubkey::new_unique();
        let mut pool_data = [0u8; POOL_V1_STATE_ACCOUNT_BYTES];
        let mut page_data = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        let mut pool_lamports = 1;
        let mut page_lamports = 1;
        let pool = account(
            &pool_key,
            &program_id,
            &mut pool_lamports,
            &mut pool_data,
            true,
            true,
        );
        let page = account(
            &wrong_page_key,
            &program_id,
            &mut page_lamports,
            &mut page_data,
            false,
            true,
        );
        assert_eq!(
            initialize_pool_accounts_v1(&program_id, &[pool, page], initialization()),
            Err(PoolV1ProgramError::InvalidRootPageAddress.into())
        );
        assert!(pool_data.iter().all(|byte| *byte == 0));
        assert!(page_data.iter().all(|byte| *byte == 0));

        page_data[17] = 1;
        let before_page = page_data.clone();
        let pool = account(
            &pool_key,
            &program_id,
            &mut pool_lamports,
            &mut pool_data,
            true,
            true,
        );
        let page = account(
            &correct_page_key,
            &program_id,
            &mut page_lamports,
            &mut page_data,
            false,
            true,
        );
        assert_eq!(
            initialize_pool_accounts_v1(&program_id, &[pool, page], initialization()),
            Err(ProgramError::InvalidAccountData)
        );
        assert!(pool_data.iter().all(|byte| *byte == 0));
        assert_eq!(page_data, before_page);
    }

    #[test]
    fn one_and_two_leaf_transitions_persist_matching_roots() {
        let program_id = Pubkey::new_unique();
        let pool_key = canonical_pool_key(&program_id);
        let page_key = crate::pool_v1_root_page_address(&program_id, &pool_key, 0).0;
        let mut pool_data = [0u8; POOL_V1_STATE_ACCOUNT_BYTES];
        let mut page_data = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        let mut pool_lamports = 1;
        let mut page_lamports = 1;
        initialize_fixture(
            &program_id,
            &pool_key,
            &page_key,
            &mut pool_data,
            &mut page_data,
            &mut pool_lamports,
            &mut page_lamports,
        );

        let pool = account(
            &pool_key,
            &program_id,
            &mut pool_lamports,
            &mut pool_data,
            false,
            true,
        );
        let page = account(
            &page_key,
            &program_id,
            &mut page_lamports,
            &mut page_data,
            false,
            true,
        );
        let one = apply_authorized_append_v1(
            &program_id,
            &[pool, page],
            AuthorizedAppendV1::One(digest(1)),
        )
        .unwrap();
        assert_eq!(one.first.root_sequence, 1);
        assert_eq!(one.second, None);

        let pool = account(
            &pool_key,
            &program_id,
            &mut pool_lamports,
            &mut pool_data,
            false,
            true,
        );
        let page = account(
            &page_key,
            &program_id,
            &mut page_lamports,
            &mut page_data,
            false,
            true,
        );
        let two = apply_authorized_append_v1(
            &program_id,
            &[pool, page],
            AuthorizedAppendV1::Two(digest(2), digest(3)),
        )
        .unwrap();
        assert_eq!(two.first.root_sequence, 2);
        assert_eq!(two.second.unwrap().root_sequence, 3);

        let state = PoolStateV1::decode(&pool_data, &pool_key).unwrap();
        assert_eq!(state.current_root_sequence(), 3);
        let header = validate_root_page_bytes(&page_data, &pool_key, 0).unwrap();
        assert_eq!(header.filled, 4);
        assert_eq!(
            read_retained_root(&page_data, header, 3).unwrap(),
            state.tree.root
        );
    }

    #[test]
    fn prevalidated_append_is_byte_exact_and_rejects_pool_substitution_before_callback() {
        let program_id = Pubkey::new_unique();
        let pool_key = canonical_pool_key(&program_id);
        let page_key = crate::pool_v1_root_page_address(&program_id, &pool_key, 0).0;
        let mut initial_pool_data = [0u8; POOL_V1_STATE_ACCOUNT_BYTES];
        let mut initial_page_data = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        let mut initial_pool_lamports = 1;
        let mut initial_page_lamports = 1;
        initialize_fixture(
            &program_id,
            &pool_key,
            &page_key,
            &mut initial_pool_data,
            &mut initial_page_data,
            &mut initial_pool_lamports,
            &mut initial_page_lamports,
        );

        let mut standalone_pool_data = initial_pool_data;
        let mut standalone_page_data = initial_page_data.clone();
        let mut standalone_pool_lamports = 1;
        let mut standalone_page_lamports = 1;
        let standalone_receipt = {
            let pool = account(
                &pool_key,
                &program_id,
                &mut standalone_pool_lamports,
                &mut standalone_pool_data,
                false,
                true,
            );
            let page = account(
                &page_key,
                &program_id,
                &mut standalone_page_lamports,
                &mut standalone_page_data,
                false,
                true,
            );
            apply_authorized_append_after_v1(
                &program_id,
                &[pool, page],
                AuthorizedAppendV1::Two(digest(4_001), digest(4_002)),
                || Ok(()),
            )
            .unwrap()
        };

        let mut prevalidated_pool_data = initial_pool_data;
        let mut prevalidated_page_data = initial_page_data.clone();
        let mut prevalidated_pool_lamports = 1;
        let mut prevalidated_page_lamports = 1;
        let canonical = {
            let pool = account(
                &pool_key,
                &program_id,
                &mut prevalidated_pool_lamports,
                &mut prevalidated_pool_data,
                false,
                true,
            );
            CanonicalPoolStateV1::decode_account(&program_id, &pool).unwrap()
        };
        let anchor_envelope = HistoricalAnchorEnvelopeV1 {
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            pool: pool_key.to_bytes(),
            deployment_domain: canonical.identity.deployment_domain,
            anchor_sequence: canonical.current_root_sequence(),
            anchor_root: canonical.tree.root,
            nullifier: digest(3_999),
            verifier_profile: [9u8; 32],
            verifier_release: [10u8; 32],
        };
        let encoded_anchor = encode_historical_anchor_envelope_v1(&anchor_envelope).unwrap();
        let history = {
            let pool = account(
                &pool_key,
                &program_id,
                &mut prevalidated_pool_lamports,
                &mut prevalidated_pool_data,
                false,
                true,
            );
            let page = account(
                &page_key,
                &program_id,
                &mut prevalidated_page_lamports,
                &mut prevalidated_page_data,
                false,
                true,
            );
            let anchor = crate::anchor::authenticate_historical_anchor_after_prevalidated_state_v1(
                &program_id,
                &pool,
                &page,
                &encoded_anchor,
                crate::anchor::HistoricalAnchorAuthorizationV1 {
                    transition_kind: PoolV1TransitionKind::PrivateTransfer,
                    verifier_profile: anchor_envelope.verifier_profile,
                    verifier_release: anchor_envelope.verifier_release,
                },
                &canonical,
            )
            .unwrap();
            validate_current_history_after_prevalidated_anchor_v1(
                &program_id,
                &pool,
                &page,
                &canonical,
                anchor,
            )
            .unwrap()
        };
        let callback_called = Cell::new(false);
        let prevalidated_receipt = {
            let pool = account(
                &pool_key,
                &program_id,
                &mut prevalidated_pool_lamports,
                &mut prevalidated_pool_data,
                false,
                true,
            );
            let page = account(
                &page_key,
                &program_id,
                &mut prevalidated_page_lamports,
                &mut prevalidated_page_data,
                false,
                true,
            );
            apply_authorized_append_after_prevalidated_history_v1(
                &program_id,
                &[pool, page],
                &canonical,
                history,
                AuthorizedAppendV1::Two(digest(4_001), digest(4_002)),
                || {
                    callback_called.set(true);
                    Ok(())
                },
            )
            .unwrap()
        };
        assert!(callback_called.get());
        assert_eq!(prevalidated_receipt, standalone_receipt);
        assert_eq!(prevalidated_pool_data, standalone_pool_data);
        assert_eq!(prevalidated_page_data, standalone_page_data);

        let substituted_pool_key = Pubkey::new_unique();
        let mut substituted_pool_data = initial_pool_data;
        let mut untouched_page_data = initial_page_data.clone();
        let before_pool = substituted_pool_data;
        let before_page = untouched_page_data.clone();
        let mut substituted_pool_lamports = 1;
        let mut untouched_page_lamports = 1;
        let callback_called = Cell::new(false);
        let result = {
            let pool = account(
                &substituted_pool_key,
                &program_id,
                &mut substituted_pool_lamports,
                &mut substituted_pool_data,
                false,
                true,
            );
            let page = account(
                &page_key,
                &program_id,
                &mut untouched_page_lamports,
                &mut untouched_page_data,
                false,
                true,
            );
            apply_authorized_append_after_prevalidated_history_v1(
                &program_id,
                &[pool, page],
                &canonical,
                history,
                AuthorizedAppendV1::One(digest(4_002)),
                || {
                    callback_called.set(true);
                    Ok(())
                },
            )
        };
        assert_eq!(result, Err(ProgramError::InvalidAccountData));
        assert!(!callback_called.get());
        assert_eq!(substituted_pool_data, before_pool);
        assert_eq!(untouched_page_data, before_page);
    }

    fn state_and_history_at(
        pool_key: &Pubkey,
        leaf_count: u64,
    ) -> (PoolStateV1, std::vec::Vec<u8>) {
        let mut state = PoolStateV1::genesis(pool_key, initialization()).unwrap();
        let page_number = root_history_location(leaf_count).page_number;
        let first_sequence = page_number * POOL_V1_ROOT_HISTORY_CAPACITY as u64;
        let mut roots = RootHistoryPageV1::new(pool_key.to_bytes(), page_number).unwrap();
        if page_number == 0 {
            roots
                .push(0, POOL_V1_EMPTY_ROOTS[POOL_V1_TREE_DEPTH])
                .unwrap();
        }
        for index in 0..leaf_count {
            let (next_tree, receipt) = state
                .tree
                .append_one_with_empty_roots(digest(index as u32 + 1), &POOL_V1_EMPTY_ROOTS)
                .unwrap();
            state.tree = next_tree;
            if receipt.root_sequence >= first_sequence {
                roots.push(receipt.root_sequence, receipt.root).unwrap();
            }
        }
        (state, roots.encode().unwrap().to_vec())
    }

    #[test]
    fn page_rollover_is_exact_and_failure_before_next_page_is_atomic() {
        let program_id = Pubkey::new_unique();
        let pool_key = canonical_pool_key(&program_id);
        let (state, mut page_data) = state_and_history_at(&pool_key, 255);
        let mut pool_data = state.encode().unwrap();
        let current_key = crate::pool_v1_root_page_address(&program_id, &pool_key, 0).0;
        let next_key = crate::pool_v1_root_page_address(&program_id, &pool_key, 1).0;
        let mut next_data = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        let mut pool_lamports = 1;
        let mut current_lamports = 1;
        let mut next_lamports = 1;

        let before_pool = pool_data;
        let before_current = page_data.clone();
        let pool = account(
            &pool_key,
            &program_id,
            &mut pool_lamports,
            &mut pool_data,
            false,
            true,
        );
        let current = account(
            &current_key,
            &program_id,
            &mut current_lamports,
            &mut page_data,
            false,
            false,
        );
        assert_eq!(
            apply_authorized_append_v1(
                &program_id,
                &[pool, current],
                AuthorizedAppendV1::One(digest(999))
            ),
            Err(PoolV1ProgramError::UnexpectedRootPage.into())
        );
        assert_eq!(pool_data, before_pool);
        assert_eq!(page_data, before_current);

        let pool = account(
            &pool_key,
            &program_id,
            &mut pool_lamports,
            &mut pool_data,
            false,
            true,
        );
        let current = account(
            &current_key,
            &program_id,
            &mut current_lamports,
            &mut page_data,
            false,
            false,
        );
        let next = account(
            &next_key,
            &program_id,
            &mut next_lamports,
            &mut next_data,
            false,
            true,
        );
        apply_authorized_append_v1(
            &program_id,
            &[pool, current, next],
            AuthorizedAppendV1::One(digest(999)),
        )
        .unwrap();
        let state = PoolStateV1::decode(&pool_data, &pool_key).unwrap();
        assert_eq!(state.current_root_sequence(), 256);
        assert_eq!(page_data, before_current);
        let header = validate_root_page_bytes(&next_data, &pool_key, 1).unwrap();
        assert_eq!(header.filled, 1);
        assert_eq!(
            read_retained_root(&next_data, header, 256).unwrap(),
            state.tree.root
        );
    }

    #[test]
    fn two_leaf_append_splits_exactly_across_page_boundary() {
        let program_id = Pubkey::new_unique();
        let pool_key = canonical_pool_key(&program_id);
        let (state, mut current_data) = state_and_history_at(&pool_key, 254);
        let mut pool_data = state.encode().unwrap();
        let current_key = crate::pool_v1_root_page_address(&program_id, &pool_key, 0).0;
        let next_key = crate::pool_v1_root_page_address(&program_id, &pool_key, 1).0;
        let mut next_data = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        let mut pool_lamports = 1;
        let mut current_lamports = 1;
        let mut next_lamports = 1;
        let pool = account(
            &pool_key,
            &program_id,
            &mut pool_lamports,
            &mut pool_data,
            false,
            true,
        );
        let current = account(
            &current_key,
            &program_id,
            &mut current_lamports,
            &mut current_data,
            false,
            true,
        );
        let next = account(
            &next_key,
            &program_id,
            &mut next_lamports,
            &mut next_data,
            false,
            true,
        );
        let receipt = apply_authorized_append_v1(
            &program_id,
            &[pool, current, next],
            AuthorizedAppendV1::Two(digest(700), digest(701)),
        )
        .unwrap();
        assert_eq!(receipt.first.root_sequence, 255);
        assert_eq!(receipt.second.unwrap().root_sequence, 256);
        let state = PoolStateV1::decode(&pool_data, &pool_key).unwrap();
        assert_eq!(state.current_root_sequence(), 256);
        let current_header = validate_root_page_bytes(&current_data, &pool_key, 0).unwrap();
        let next_header = validate_root_page_bytes(&next_data, &pool_key, 1).unwrap();
        assert_eq!(current_header.filled, 256);
        assert_eq!(next_header.filled, 1);
        assert_eq!(
            read_retained_root(&current_data, current_header, 255).unwrap(),
            receipt.first.root
        );
        assert_eq!(
            read_retained_root(&next_data, next_header, 256).unwrap(),
            state.tree.root
        );
    }

    fn one_slot_remaining_state(pool_key: &Pubkey) -> PoolStateV1 {
        let frontier = core::array::from_fn(|level| digest(50_000 + level as u32));
        let mut node = POOL_V1_EMPTY_ROOTS[0];
        for sibling in frontier.iter().take(POOL_V1_TREE_DEPTH) {
            node = pool_v1_tree_parent(sibling, &node);
        }
        let tree = IncrementalMerkleTreeV1::from_parts_with_empty_roots(
            POOL_V1_LEAF_CAPACITY - 1,
            node,
            frontier,
            &POOL_V1_EMPTY_ROOTS,
        )
        .unwrap();
        PoolStateV1 {
            tree,
            ..PoolStateV1::genesis(pool_key, initialization()).unwrap()
        }
    }

    fn terminal_current_page(pool_key: &Pubkey, root: Digest) -> std::vec::Vec<u8> {
        let page_number = root_history_location(POOL_V1_LEAF_CAPACITY - 1).page_number;
        let first = page_number * POOL_V1_ROOT_HISTORY_CAPACITY as u64;
        let mut page = RootHistoryPageV1::new(pool_key.to_bytes(), page_number).unwrap();
        for sequence in first..=POOL_V1_LEAF_CAPACITY - 1 {
            let value = if sequence == POOL_V1_LEAF_CAPACITY - 1 {
                root
            } else {
                digest(sequence as u32)
            };
            page.push(sequence, value).unwrap();
        }
        page.encode().unwrap().to_vec()
    }

    #[test]
    fn final_append_reaches_full_tree_and_future_append_fails_closed() {
        let program_id = Pubkey::new_unique();
        let pool_key = canonical_pool_key(&program_id);
        let state = one_slot_remaining_state(&pool_key);
        let mut pool_data = state.encode().unwrap();
        let current_page_number = root_history_location(POOL_V1_LEAF_CAPACITY - 1).page_number;
        let current_key =
            crate::pool_v1_root_page_address(&program_id, &pool_key, current_page_number).0;
        let next_key =
            crate::pool_v1_root_page_address(&program_id, &pool_key, current_page_number + 1).0;
        let mut current_data = terminal_current_page(&pool_key, state.tree.root);
        let mut next_data = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        let mut pool_lamports = 1;
        let mut current_lamports = 1;
        let mut next_lamports = 1;

        let before_pool = pool_data;
        let before_current = current_data.clone();
        let pool = account(
            &pool_key,
            &program_id,
            &mut pool_lamports,
            &mut pool_data,
            false,
            true,
        );
        let current = account(
            &current_key,
            &program_id,
            &mut current_lamports,
            &mut current_data,
            false,
            false,
        );
        assert_eq!(
            apply_authorized_append_v1(
                &program_id,
                &[pool, current],
                AuthorizedAppendV1::Two(digest(1233), digest(1234))
            ),
            Err(PoolV1ProgramError::InsufficientTreeCapacity.into())
        );
        assert_eq!(pool_data, before_pool);
        assert_eq!(current_data, before_current);

        let pool = account(
            &pool_key,
            &program_id,
            &mut pool_lamports,
            &mut pool_data,
            false,
            true,
        );
        let current = account(
            &current_key,
            &program_id,
            &mut current_lamports,
            &mut current_data,
            false,
            false,
        );
        let next = account(
            &next_key,
            &program_id,
            &mut next_lamports,
            &mut next_data,
            false,
            true,
        );
        let receipt = apply_authorized_append_v1(
            &program_id,
            &[pool, current, next],
            AuthorizedAppendV1::One(digest(1234)),
        )
        .unwrap();
        assert_eq!(receipt.first.root_sequence, POOL_V1_LEAF_CAPACITY);
        let full = PoolStateV1::decode(&pool_data, &pool_key).unwrap();
        assert_eq!(full.current_root_sequence(), POOL_V1_LEAF_CAPACITY);
        let header =
            validate_root_page_bytes(&next_data, &pool_key, current_page_number + 1).unwrap();
        assert_eq!(header.filled, 1);
        assert_eq!(
            read_retained_root(&next_data, header, POOL_V1_LEAF_CAPACITY).unwrap(),
            full.tree.root
        );

        let before_pool = pool_data;
        let before_page = next_data.clone();
        let pool = account(
            &pool_key,
            &program_id,
            &mut pool_lamports,
            &mut pool_data,
            false,
            true,
        );
        let current = account(
            &next_key,
            &program_id,
            &mut next_lamports,
            &mut next_data,
            false,
            false,
        );
        assert_eq!(
            apply_authorized_append_v1(
                &program_id,
                &[pool, current],
                AuthorizedAppendV1::One(digest(1235))
            ),
            Err(PoolV1ProgramError::TreeFull.into())
        );
        assert_eq!(pool_data, before_pool);
        assert_eq!(next_data, before_page);
    }
}
