//! Distinct pair-leaf Pool state and append transition experiments.
//!
//! The stable Tag-73 proof authorizes the two occupied output commitments.  It
//! does not bind a soon-to-be-stale live append frontier.  After the selected
//! verifier returns successfully, the Pool compresses those commitments into
//! one pair leaf and performs the exact depth-20 append against its locked
//! current state. That measured route is production-inactive. The conservative
//! path consumes an opaque proof-carried afterstate and performs no Pool-side
//! Poseidon call.

extern crate alloc;

use alloc::boxed::Box;

use aspis_core::field::M31;
use aspis_statement::{
    decode_digest_canonical, encode_digest_canonical,
    pool_v1::{
        decode_pool_identity_v1, decode_verifier_policy_v1, encode_pool_identity_v1,
        root_history_location, validate_verifier_policy_v1, IncrementalMerkleTreeV1,
        PoolIdentityV1, PoolV1PairLeafWitnessV1, VerifierPolicyV1, POOL_V1_DIGEST_ENCODING_VERSION,
        POOL_V1_PAIR_CAPACITY, POOL_V1_PAIR_TREE_DEPTH, POOL_V1_PAIR_TREE_FORMAT_BINDING,
        POOL_V1_ROOT_HISTORY_CAPACITY_LOG2, POOL_V1_TREE_HASH_VERSION,
        POOL_V1_TREE_STATE_ACCOUNT_BYTES, POOL_V1_VERIFIER_POLICY_BYTES,
        POOL_V1_VERIFIER_POLICY_MAGIC, POOL_V1_VERIFIER_POLICY_VERSION,
    },
    poseidon2::Digest,
};
use solana_program::{account_info::AccountInfo, program_error::ProgramError, pubkey::Pubkey};

use crate::{
    empty_roots::POOL_V1_PAIR_EMPTY_ROOTS, error::PoolV1ProgramError,
    history::require_program_account, pair_dispatch::AuthenticatedPairAfterstateV1,
    state::PoolInitializationV1, vault::LEGACY_SPL_TOKEN_PROGRAM_ID,
};

pub const POOL_V1_PAIR_STATE_ACCOUNT_MAGIC: [u8; 4] = *b"ASPJ";
pub const POOL_V1_PAIR_STATE_ACCOUNT_VERSION: u8 = 1;
pub const POOL_V1_PAIR_STATE_SEED: &[u8] = b"aspis-pair-pool-state-v1";
pub const POOL_V1_PAIR_TREE_STATE_MAGIC: [u8; 4] = *b"ASJT";
pub const POOL_V1_PAIR_TREE_STATE_VERSION: u8 = 1;
pub const POOL_V1_PAIR_STATE_HEADER_BYTES: usize = 64;
pub const POOL_V1_PAIR_STATE_IDENTITY_OFFSET: usize = POOL_V1_PAIR_STATE_HEADER_BYTES;
pub const POOL_V1_PAIR_STATE_POLICY_OFFSET: usize = POOL_V1_PAIR_STATE_IDENTITY_OFFSET + 144;
pub const POOL_V1_PAIR_STATE_TREE_OFFSET: usize =
    POOL_V1_PAIR_STATE_POLICY_OFFSET + POOL_V1_VERIFIER_POLICY_BYTES;
pub const POOL_V1_PAIR_STATE_ACCOUNT_BYTES: usize =
    POOL_V1_PAIR_STATE_TREE_OFFSET + POOL_V1_TREE_STATE_ACCOUNT_BYTES;

const STATE_SEQUENCE_OFFSET: usize = 40;
const STATE_PAGE_OFFSET: usize = 48;
const STATE_SLOT_OFFSET: usize = 56;

const _: () = assert!(POOL_V1_PAIR_STATE_ACCOUNT_BYTES == 1_000);

fn exact<const N: usize>(bytes: &[u8]) -> Result<[u8; N], ProgramError> {
    bytes
        .try_into()
        .map_err(|_| ProgramError::InvalidAccountData)
}

pub fn pool_v1_pair_state_address(program_id: &Pubkey, asset_mint: &Pubkey) -> (Pubkey, u8) {
    Pubkey::find_program_address(&[POOL_V1_PAIR_STATE_SEED, asset_mint.as_ref()], program_id)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PairPoolStateV1 {
    pub identity: PoolIdentityV1,
    pub verifier_policy: VerifierPolicyV1,
    /// `next_leaf_index` is the next pair index and also the root sequence.
    pub tree: IncrementalMerkleTreeV1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PairAppendReceiptV1 {
    pub pair_index: u64,
    pub first_note_index: u64,
    pub second_note_index: u64,
    pub root_sequence: u64,
    pub pair_leaf: Digest,
    pub root: Digest,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PairVerifiedAfterstateReceiptV1 {
    pub pair_index: u64,
    pub first_note_index: u64,
    pub second_note_index: u64,
    pub root_sequence: u64,
    pub root: Digest,
}

/// Private evidence that the exact writable pair-state PDA has passed the
/// complete byte/PDA/cursor/canonicality checks.  The active frontier/root
/// relation is the one explicit inductive source invariant.
pub(crate) struct CanonicalPairPoolStateV1 {
    program_id: Pubkey,
    pool: Pubkey,
    state: Box<PairPoolStateV1>,
}

impl core::ops::Deref for CanonicalPairPoolStateV1 {
    type Target = PairPoolStateV1;

    fn deref(&self) -> &Self::Target {
        &self.state
    }
}

impl CanonicalPairPoolStateV1 {
    pub(crate) fn decode_account_from_program_invariant(
        program_id: &Pubkey,
        account: &AccountInfo<'_>,
    ) -> Result<Self, ProgramError> {
        require_program_account(account, program_id, true)?;
        if account.is_signer {
            return Err(ProgramError::InvalidAccountData);
        }
        let state = Box::new(PairPoolStateV1::decode_from_program_invariant(
            &account.try_borrow_data()?,
            account.key,
        )?);
        let mint = Pubkey::new_from_array(state.identity.asset_mint);
        if account.key != &pool_v1_pair_state_address(program_id, &mint).0 {
            return Err(PoolV1ProgramError::InvalidPoolStateAddress.into());
        }
        Ok(Self {
            program_id: *program_id,
            pool: *account.key,
            state,
        })
    }

    pub(crate) fn require_same_account(
        &self,
        program_id: &Pubkey,
        account: &AccountInfo<'_>,
    ) -> Result<(), ProgramError> {
        require_program_account(account, program_id, true)?;
        if account.is_signer
            || self.program_id != *program_id
            || self.pool != *account.key
            || self.state.identity.pool != account.key.to_bytes()
        {
            return Err(ProgramError::InvalidAccountData);
        }
        Ok(())
    }
}

impl PairPoolStateV1 {
    pub fn genesis(
        pool: &Pubkey,
        initialization: PoolInitializationV1,
    ) -> Result<Self, ProgramError> {
        if initialization.asset_id.0 >= aspis_core::field::P {
            return Err(ProgramError::InvalidInstructionData);
        }
        if initialization.token_program != LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes() {
            return Err(PoolV1ProgramError::InvalidTokenProgram.into());
        }
        validate_verifier_policy_v1(&initialization.verifier_policy)
            .map_err(|_| ProgramError::InvalidInstructionData)?;
        Ok(Self {
            identity: PoolIdentityV1 {
                pool: pool.to_bytes(),
                asset_mint: initialization.asset_mint,
                token_program: initialization.token_program,
                asset_id: initialization.asset_id,
                deployment_domain: initialization.deployment_domain,
            },
            verifier_policy: initialization.verifier_policy,
            tree: IncrementalMerkleTreeV1 {
                next_leaf_index: 0,
                root: POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH],
                frontier: core::array::from_fn(|level| POOL_V1_PAIR_EMPTY_ROOTS[level]),
            },
        })
    }

    pub fn current_root_sequence(&self) -> u64 {
        self.tree.next_leaf_index
    }

    /// Apply the exact state returned by the selected proof verifier without
    /// evaluating Poseidon in the Pool.  The opaque token can only be created
    /// by the immediate return-data authenticator in `pair_dispatch`.
    pub(crate) fn apply_authenticated_afterstate_from_program_invariant(
        &self,
        authenticated: &AuthenticatedPairAfterstateV1,
    ) -> Result<(Self, PairVerifiedAfterstateReceiptV1), ProgramError> {
        let afterstate = authenticated.value();
        if self.tree.next_leaf_index >= POOL_V1_PAIR_CAPACITY
            || self.tree.next_leaf_index.checked_add(1) != Some(afterstate.next_pair_index)
        {
            return Err(PoolV1ProgramError::StateHistoryMismatch.into());
        }
        for (level, node) in afterstate.next_frontier.iter().enumerate() {
            if (afterstate.next_pair_index >> level) & 1 == 0
                && *node != POOL_V1_PAIR_EMPTY_ROOTS[level]
            {
                return Err(PoolV1ProgramError::StateHistoryMismatch.into());
            }
        }
        let pair_index = self.tree.next_leaf_index;
        let next = Self {
            identity: self.identity,
            verifier_policy: self.verifier_policy,
            tree: IncrementalMerkleTreeV1 {
                next_leaf_index: afterstate.next_pair_index,
                root: afterstate.next_root,
                frontier: afterstate.next_frontier,
            },
        };
        Ok((
            next,
            PairVerifiedAfterstateReceiptV1 {
                pair_index,
                first_note_index: pair_index
                    .checked_mul(2)
                    .ok_or(PoolV1ProgramError::ArithmeticOverflow)?,
                second_note_index: pair_index
                    .checked_mul(2)
                    .and_then(|index| index.checked_add(1))
                    .ok_or(PoolV1ProgramError::ArithmeticOverflow)?,
                root_sequence: afterstate.next_pair_index,
                root: afterstate.next_root,
            },
        ))
    }

    /// Stable-proof execution-time append.  The proof-authorized output
    /// commitments are pair-compressed once, then exactly 20 parents are
    /// computed from the current locked frontier.
    pub fn append_occupied_pair_from_program_invariant(
        &self,
        first: Digest,
        second: Digest,
    ) -> Result<(Self, PairAppendReceiptV1), ProgramError> {
        if self.tree.next_leaf_index >= POOL_V1_PAIR_CAPACITY {
            return Err(PoolV1ProgramError::TreeFull.into());
        }
        let pair_leaf = PoolV1PairLeafWitnessV1::two_outputs(first, second)
            .and_then(|witness| witness.leaf_digest())
            .map_err(|_| PoolV1ProgramError::NonCanonicalLeaf)?;
        self.append_verified_pair_from_program_invariant(pair_leaf)
    }

    /// Consume a pair digest returned by the selected verifier. Its equality
    /// to the two occupied statement outputs was already checked by the
    /// stable proof, so the Pool must not repeat that Poseidon compression.
    pub fn append_verified_pair_from_program_invariant(
        &self,
        pair_leaf: Digest,
    ) -> Result<(Self, PairAppendReceiptV1), ProgramError> {
        if self.tree.next_leaf_index >= POOL_V1_PAIR_CAPACITY {
            return Err(PoolV1ProgramError::TreeFull.into());
        }
        if pair_leaf.iter().any(|limb| limb.0 >= aspis_core::field::P) {
            return Err(PoolV1ProgramError::NonCanonicalLeaf.into());
        }
        let pair_index = self.tree.next_leaf_index;
        let mut frontier = self.tree.frontier;
        let mut carry = pair_leaf;
        let mut carry_level = 0usize;
        while carry_level < POOL_V1_PAIR_TREE_DEPTH && (pair_index >> carry_level) & 1 == 1 {
            carry = aspis_statement::pool_v1::pool_v1_tree_parent(&frontier[carry_level], &carry);
            frontier[carry_level] = POOL_V1_PAIR_EMPTY_ROOTS[carry_level];
            carry_level += 1;
        }
        let next_pair_index = pair_index
            .checked_add(1)
            .ok_or(PoolV1ProgramError::ArithmeticOverflow)?;
        let root = if carry_level == POOL_V1_PAIR_TREE_DEPTH {
            carry
        } else {
            frontier[carry_level] = carry;
            let mut node = POOL_V1_PAIR_EMPTY_ROOTS[carry_level];
            for level in carry_level..POOL_V1_PAIR_TREE_DEPTH {
                node = if (next_pair_index >> level) & 1 == 0 {
                    aspis_statement::pool_v1::pool_v1_tree_parent(
                        &node,
                        &POOL_V1_PAIR_EMPTY_ROOTS[level],
                    )
                } else {
                    aspis_statement::pool_v1::pool_v1_tree_parent(&frontier[level], &node)
                };
            }
            node
        };
        let next = Self {
            identity: self.identity,
            verifier_policy: self.verifier_policy,
            tree: IncrementalMerkleTreeV1 {
                next_leaf_index: next_pair_index,
                root,
                frontier,
            },
        };
        Ok((
            next,
            PairAppendReceiptV1 {
                pair_index,
                first_note_index: pair_index
                    .checked_mul(2)
                    .ok_or(PoolV1ProgramError::ArithmeticOverflow)?,
                second_note_index: pair_index
                    .checked_mul(2)
                    .and_then(|index| index.checked_add(1))
                    .ok_or(PoolV1ProgramError::ArithmeticOverflow)?,
                root_sequence: next_pair_index,
                pair_leaf,
                root,
            },
        ))
    }

    pub(crate) fn write_encoding_prevalidated(
        &self,
        output: &mut [u8; POOL_V1_PAIR_STATE_ACCOUNT_BYTES],
    ) {
        output.fill(0);
        output[..4].copy_from_slice(&POOL_V1_PAIR_STATE_ACCOUNT_MAGIC);
        output[4] = POOL_V1_PAIR_STATE_ACCOUNT_VERSION;
        output[5] = 1;
        output[6] = POOL_V1_PAIR_TREE_DEPTH as u8;
        output[7] = POOL_V1_ROOT_HISTORY_CAPACITY_LOG2;
        output[8..40].copy_from_slice(&POOL_V1_PAIR_TREE_FORMAT_BINDING);
        let sequence = self.current_root_sequence();
        let location = root_history_location(sequence);
        output[STATE_SEQUENCE_OFFSET..STATE_PAGE_OFFSET].copy_from_slice(&sequence.to_le_bytes());
        output[STATE_PAGE_OFFSET..STATE_SLOT_OFFSET]
            .copy_from_slice(&location.page_number.to_le_bytes());
        output[STATE_SLOT_OFFSET..58].copy_from_slice(&location.slot.to_le_bytes());
        output[POOL_V1_PAIR_STATE_IDENTITY_OFFSET..POOL_V1_PAIR_STATE_POLICY_OFFSET]
            .copy_from_slice(&encode_pool_identity_v1(&self.identity));
        let policy = &mut output[POOL_V1_PAIR_STATE_POLICY_OFFSET..POOL_V1_PAIR_STATE_TREE_OFFSET];
        policy[..4].copy_from_slice(&POOL_V1_VERIFIER_POLICY_MAGIC);
        policy[4] = POOL_V1_VERIFIER_POLICY_VERSION;
        policy[5] = self.verifier_policy.flags;
        policy[8..40].copy_from_slice(&self.verifier_policy.registry_program);
        policy[40..72].copy_from_slice(&self.verifier_policy.registry_authority);
        policy[72..104].copy_from_slice(&self.verifier_policy.policy_binding);
        let tree = &mut output[POOL_V1_PAIR_STATE_TREE_OFFSET..];
        tree[..4].copy_from_slice(&POOL_V1_PAIR_TREE_STATE_MAGIC);
        tree[4] = POOL_V1_PAIR_TREE_STATE_VERSION;
        tree[5] = POOL_V1_PAIR_TREE_DEPTH as u8;
        tree[6] = POOL_V1_TREE_HASH_VERSION;
        tree[7] = POOL_V1_DIGEST_ENCODING_VERSION;
        tree[8..16].copy_from_slice(&self.tree.next_leaf_index.to_le_bytes());
        tree[16..48].copy_from_slice(&encode_digest_canonical(&self.tree.root));
        for (level, node) in self.tree.frontier.iter().enumerate() {
            let start = 48 + 32 * level;
            tree[start..start + 32].copy_from_slice(&encode_digest_canonical(node));
        }
    }

    pub fn encode(&self) -> Result<[u8; POOL_V1_PAIR_STATE_ACCOUNT_BYTES], ProgramError> {
        self.tree
            .validate_with_empty_roots(&POOL_V1_PAIR_EMPTY_ROOTS)
            .map_err(|_| ProgramError::InvalidAccountData)?;
        validate_verifier_policy_v1(&self.verifier_policy)
            .map_err(|_| ProgramError::InvalidAccountData)?;
        let mut output = [0u8; POOL_V1_PAIR_STATE_ACCOUNT_BYTES];
        self.write_encoding_prevalidated(&mut output);
        Ok(output)
    }

    pub(crate) fn decode_from_program_invariant(
        data: &[u8],
        expected_pool: &Pubkey,
    ) -> Result<Self, ProgramError> {
        if data.len() != POOL_V1_PAIR_STATE_ACCOUNT_BYTES
            || data[..4] != POOL_V1_PAIR_STATE_ACCOUNT_MAGIC
            || data[4] != POOL_V1_PAIR_STATE_ACCOUNT_VERSION
            || data[5] != 1
            || data[6] != POOL_V1_PAIR_TREE_DEPTH as u8
            || data[7] != POOL_V1_ROOT_HISTORY_CAPACITY_LOG2
            || data[8..40] != POOL_V1_PAIR_TREE_FORMAT_BINDING
            || data[58..64] != [0u8; 6]
        {
            return Err(PoolV1ProgramError::InvalidAccountType.into());
        }
        let identity = decode_pool_identity_v1(
            &data[POOL_V1_PAIR_STATE_IDENTITY_OFFSET..POOL_V1_PAIR_STATE_POLICY_OFFSET],
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;
        if identity.pool != expected_pool.to_bytes() {
            return Err(PoolV1ProgramError::StateHistoryMismatch.into());
        }
        let verifier_policy = decode_verifier_policy_v1(
            &data[POOL_V1_PAIR_STATE_POLICY_OFFSET..POOL_V1_PAIR_STATE_TREE_OFFSET],
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;
        let tree_bytes = &data[POOL_V1_PAIR_STATE_TREE_OFFSET..];
        if tree_bytes.len() != POOL_V1_TREE_STATE_ACCOUNT_BYTES
            || tree_bytes[..4] != POOL_V1_PAIR_TREE_STATE_MAGIC
            || tree_bytes[4] != POOL_V1_PAIR_TREE_STATE_VERSION
            || tree_bytes[5] != POOL_V1_PAIR_TREE_DEPTH as u8
            || tree_bytes[6] != POOL_V1_TREE_HASH_VERSION
            || tree_bytes[7] != POOL_V1_DIGEST_ENCODING_VERSION
        {
            return Err(ProgramError::InvalidAccountData);
        }
        let next_pair_index = u64::from_le_bytes(exact(&tree_bytes[8..16])?);
        if next_pair_index > POOL_V1_PAIR_CAPACITY {
            return Err(ProgramError::InvalidAccountData);
        }
        let root = decode_digest_canonical(&exact(&tree_bytes[16..48])?)
            .map_err(|_| ProgramError::InvalidAccountData)?;
        let mut frontier = [[M31::ZERO; 8]; POOL_V1_PAIR_TREE_DEPTH];
        for (level, node) in frontier.iter_mut().enumerate() {
            let start = 48 + 32 * level;
            *node = decode_digest_canonical(&exact(&tree_bytes[start..start + 32])?)
                .map_err(|_| ProgramError::InvalidAccountData)?;
            if (next_pair_index >> level) & 1 == 0 && *node != POOL_V1_PAIR_EMPTY_ROOTS[level] {
                return Err(ProgramError::InvalidAccountData);
            }
        }
        if next_pair_index == 0 && root != POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH] {
            return Err(ProgramError::InvalidAccountData);
        }
        let sequence = u64::from_le_bytes(exact(&data[STATE_SEQUENCE_OFFSET..STATE_PAGE_OFFSET])?);
        let page_number = u64::from_le_bytes(exact(&data[STATE_PAGE_OFFSET..STATE_SLOT_OFFSET])?);
        let slot = u16::from_le_bytes(exact(&data[STATE_SLOT_OFFSET..58])?);
        let location = root_history_location(next_pair_index);
        if sequence != next_pair_index
            || page_number != location.page_number
            || slot != location.slot
        {
            return Err(PoolV1ProgramError::StateHistoryMismatch.into());
        }
        Ok(Self {
            identity,
            verifier_policy,
            tree: IncrementalMerkleTreeV1 {
                next_leaf_index: next_pair_index,
                root,
                frontier,
            },
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_statement::pool_v1::{
        encode_pool_v1_pair_verified_afterstate_v1, PoolV1PairVerifiedAfterstateV1,
    };

    use crate::pair_dispatch::authenticate_pair_verified_afterstate_return_v1;

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|lane| M31(seed + lane as u32 + 1))
    }

    fn initialization() -> PoolInitializationV1 {
        PoolInitializationV1 {
            asset_mint: [2u8; 32],
            token_program: LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes(),
            asset_id: M31(4),
            deployment_domain: [5u8; 32],
            verifier_policy: VerifierPolicyV1 {
                flags: 0,
                registry_program: [6u8; 32],
                registry_authority: [7u8; 32],
                policy_binding: [8u8; 32],
            },
        }
    }

    #[test]
    fn pair_state_roundtrip_and_exact_live_append_match_generic_tree() {
        let program_id = Pubkey::new_unique();
        let mint = Pubkey::new_from_array([2u8; 32]);
        let pool = pool_v1_pair_state_address(&program_id, &mint).0;
        let state = PairPoolStateV1::genesis(&pool, initialization()).unwrap();
        let encoded = state.encode().unwrap();
        assert_eq!(encoded.len(), 1_000);
        assert_eq!(
            PairPoolStateV1::decode_from_program_invariant(&encoded, &pool),
            Ok(state)
        );

        let first = digest(100);
        let second = digest(200);
        let pair = aspis_statement::pool_v1::pool_v1_tree_parent(&first, &second);
        let (expected_tree, expected_receipt) = state
            .tree
            .append_one_with_empty_roots(pair, &POOL_V1_PAIR_EMPTY_ROOTS)
            .unwrap();
        let (next, receipt) = state
            .append_occupied_pair_from_program_invariant(first, second)
            .unwrap();
        assert_eq!(next.tree, expected_tree);
        assert_eq!(receipt.pair_index, expected_receipt.leaf_index);
        assert_eq!(receipt.first_note_index, 0);
        assert_eq!(receipt.second_note_index, 1);
        assert_eq!(receipt.root, expected_receipt.root);
        assert_eq!(next.encode().unwrap().len(), 1_000);
    }

    #[test]
    fn stale_state_and_empty_second_output_fail_closed() {
        let program_id = Pubkey::new_unique();
        let mint = Pubkey::new_from_array([2u8; 32]);
        let pool = pool_v1_pair_state_address(&program_id, &mint).0;
        let state = PairPoolStateV1::genesis(&pool, initialization()).unwrap();
        assert_eq!(
            state.append_occupied_pair_from_program_invariant(digest(1), [M31::ZERO; 8]),
            Err(PoolV1ProgramError::NonCanonicalLeaf.into())
        );
        let mut stale = state.encode().unwrap();
        stale[STATE_SEQUENCE_OFFSET] = 1;
        assert_eq!(
            PairPoolStateV1::decode_from_program_invariant(&stale, &pool),
            Err(PoolV1ProgramError::StateHistoryMismatch.into())
        );
    }

    #[test]
    fn authenticated_proof_carried_afterstate_matches_append_without_pool_poseidon() {
        let program_id = Pubkey::new_unique();
        let verifier = Pubkey::new_unique();
        let mint = Pubkey::new_from_array([2u8; 32]);
        let pool = pool_v1_pair_state_address(&program_id, &mint).0;
        let state = PairPoolStateV1::genesis(&pool, initialization()).unwrap();
        let pair = aspis_statement::pool_v1::pool_v1_tree_parent(&digest(100), &digest(200));
        let (expected, _) = state
            .append_verified_pair_from_program_invariant(pair)
            .unwrap();
        let bytes = encode_pool_v1_pair_verified_afterstate_v1(&PoolV1PairVerifiedAfterstateV1 {
            next_pair_index: expected.tree.next_leaf_index,
            next_root: expected.tree.root,
            next_frontier: expected.tree.frontier,
        })
        .unwrap();
        let authenticated =
            authenticate_pair_verified_afterstate_return_v1(&verifier, &verifier, &bytes).unwrap();
        let (actual, receipt) = state
            .apply_authenticated_afterstate_from_program_invariant(&authenticated)
            .unwrap();
        assert_eq!(actual, expected);
        assert_eq!(receipt.pair_index, 0);
        assert_eq!(receipt.first_note_index, 0);
        assert_eq!(receipt.second_note_index, 1);
        assert_eq!(receipt.root_sequence, 1);
        assert_eq!(receipt.root, expected.tree.root);

        assert_eq!(
            expected.apply_authenticated_afterstate_from_program_invariant(&authenticated),
            Err(PoolV1ProgramError::StateHistoryMismatch.into())
        );
    }

    #[test]
    fn afterstate_wrong_program_or_nonempty_zero_bit_frontier_fails_closed() {
        let program_id = Pubkey::new_unique();
        let verifier = Pubkey::new_unique();
        let wrong = Pubkey::new_unique();
        let mint = Pubkey::new_from_array([2u8; 32]);
        let pool = pool_v1_pair_state_address(&program_id, &mint).0;
        let state = PairPoolStateV1::genesis(&pool, initialization()).unwrap();
        let mut afterstate = PoolV1PairVerifiedAfterstateV1 {
            next_pair_index: 1,
            next_root: digest(300),
            next_frontier: POOL_V1_PAIR_EMPTY_ROOTS[..POOL_V1_PAIR_TREE_DEPTH]
                .try_into()
                .unwrap(),
        };
        afterstate.next_frontier[0] = digest(400);
        let valid_bytes = encode_pool_v1_pair_verified_afterstate_v1(&afterstate).unwrap();
        assert!(
            authenticate_pair_verified_afterstate_return_v1(&verifier, &wrong, &valid_bytes)
                .is_err()
        );

        afterstate.next_frontier[1] = digest(500);
        let invalid_frontier_bytes =
            encode_pool_v1_pair_verified_afterstate_v1(&afterstate).unwrap();
        let authenticated = authenticate_pair_verified_afterstate_return_v1(
            &verifier,
            &verifier,
            &invalid_frontier_bytes,
        )
        .unwrap();
        assert_eq!(
            state.apply_authenticated_afterstate_from_program_invariant(&authenticated),
            Err(PoolV1ProgramError::StateHistoryMismatch.into())
        );
    }
}
