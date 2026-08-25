//! Exact Pool V1 state account image.

extern crate alloc;

use alloc::boxed::Box;

use aspis_core::field::M31;
use aspis_statement::pool_v1::{
    decode_pool_identity_v1, decode_verifier_policy_v1, encode_pool_identity_v1,
    root_history_location, validate_verifier_policy_v1, IncrementalMerkleTreeV1, PoolIdentityV1,
    ValidatedIncrementalMerkleTreeV1, VerifierPolicyV1, POOL_V1_FORMAT_BINDING,
    POOL_V1_FORMAT_VERSION, POOL_V1_IDENTITY_BYTES, POOL_V1_ROOT_HISTORY_CAPACITY_LOG2,
    POOL_V1_TREE_DEPTH, POOL_V1_TREE_HASH_VERSION, POOL_V1_TREE_STATE_ACCOUNT_BYTES,
    POOL_V1_TREE_STATE_MAGIC, POOL_V1_TREE_STATE_VERSION, POOL_V1_VERIFIER_POLICY_BYTES,
    POOL_V1_VERIFIER_POLICY_MAGIC, POOL_V1_VERIFIER_POLICY_VERSION,
};
use solana_program::{program_error::ProgramError, pubkey::Pubkey};

use crate::{
    empty_roots::POOL_V1_EMPTY_ROOTS, error::PoolV1ProgramError, history::require_program_account,
    vault::LEGACY_SPL_TOKEN_PROGRAM_ID,
};

pub const POOL_V1_STATE_ACCOUNT_MAGIC: [u8; 4] = *b"ASPK";
/// Revision two is intentionally incompatible with the never-deployed
/// revision-one image that embedded one exact verifier release.
pub const POOL_V1_STATE_ACCOUNT_VERSION: u8 = 2;
pub const POOL_V1_STATE_SEED: &[u8] = b"aspis-pool-state-v1";
pub const POOL_V1_STATE_HEADER_BYTES: usize = 64;
pub const POOL_V1_STATE_IDENTITY_OFFSET: usize = POOL_V1_STATE_HEADER_BYTES;
pub const POOL_V1_STATE_POLICY_OFFSET: usize =
    POOL_V1_STATE_IDENTITY_OFFSET + POOL_V1_IDENTITY_BYTES;
pub const POOL_V1_STATE_TREE_OFFSET: usize =
    POOL_V1_STATE_POLICY_OFFSET + POOL_V1_VERIFIER_POLICY_BYTES;
pub const POOL_V1_STATE_ACCOUNT_BYTES: usize =
    POOL_V1_STATE_TREE_OFFSET + POOL_V1_TREE_STATE_ACCOUNT_BYTES;

const STATE_SEQUENCE_OFFSET: usize = 40;
const STATE_PAGE_OFFSET: usize = 48;
const STATE_SLOT_OFFSET: usize = 56;

fn exact_state_array<const N: usize>(bytes: &[u8]) -> Result<[u8; N], ProgramError> {
    bytes
        .try_into()
        .map_err(|_| ProgramError::InvalidAccountData)
}

/// One canonical Pool V1 state PDA per asset mint and program deployment.
pub fn pool_v1_state_address(program_id: &Pubkey, asset_mint: &Pubkey) -> (Pubkey, u8) {
    Pubkey::find_program_address(&[POOL_V1_STATE_SEED, asset_mint.as_ref()], program_id)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolInitializationV1 {
    pub asset_mint: [u8; 32],
    pub token_program: [u8; 32],
    pub asset_id: M31,
    pub deployment_domain: [u8; 32],
    pub verifier_policy: VerifierPolicyV1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolStateV1 {
    pub identity: PoolIdentityV1,
    pub verifier_policy: VerifierPolicyV1,
    pub tree: IncrementalMerkleTreeV1,
}

/// One state image that has passed the complete canonical account decoder and
/// canonical per-mint PDA check at the native instruction boundary.
///
/// The fields are private so downstream kernels cannot manufacture this token
/// from an unchecked `PoolStateV1`. They may cheaply re-check that the same
/// runtime account/program pair is still being used, without reparsing the
/// 1,000-byte image or reconstructing its depth-20 root.
pub(crate) struct CanonicalPoolStateV1 {
    program_id: Pubkey,
    pool: Pubkey,
    state: Box<PoolStateV1>,
    validated_tree: Box<ValidatedIncrementalMerkleTreeV1<'static>>,
}

impl CanonicalPoolStateV1 {
    pub(crate) fn decode_account(
        program_id: &Pubkey,
        pool_account: &solana_program::account_info::AccountInfo<'_>,
    ) -> Result<Self, ProgramError> {
        require_program_account(pool_account, program_id, true)?;
        if pool_account.is_signer {
            return Err(ProgramError::InvalidAccountData);
        }
        let (state, validated_tree) = PoolStateV1::decode_boxed_with_validated_tree(
            &pool_account.try_borrow_data()?,
            pool_account.key,
        )?;
        let mint = Pubkey::new_from_array(state.identity.asset_mint);
        if pool_account.key != &pool_v1_state_address(program_id, &mint).0 {
            return Err(PoolV1ProgramError::InvalidPoolStateAddress.into());
        }
        Ok(Self {
            program_id: *program_id,
            pool: *pool_account.key,
            state,
            validated_tree,
        })
    }

    pub(crate) fn require_same_writable_account(
        &self,
        program_id: &Pubkey,
        pool_account: &solana_program::account_info::AccountInfo<'_>,
    ) -> Result<(), ProgramError> {
        require_program_account(pool_account, program_id, true)?;
        // `decode_account` already proved that `(self.program_id, self.pool)`
        // is the canonical per-mint PDA. Exact equality with that sealed pair
        // carries the PDA proof forward without another address derivation.
        if pool_account.is_signer
            || self.program_id != *program_id
            || self.pool != *pool_account.key
            || self.state.identity.pool != pool_account.key.to_bytes()
        {
            return Err(ProgramError::InvalidAccountData);
        }
        Ok(())
    }

    pub(crate) fn as_state(&self) -> &PoolStateV1 {
        &self.state
    }

    pub(crate) fn validated_tree(&self) -> &ValidatedIncrementalMerkleTreeV1<'static> {
        &self.validated_tree
    }
}

impl core::ops::Deref for CanonicalPoolStateV1 {
    type Target = PoolStateV1;

    fn deref(&self) -> &Self::Target {
        self.as_state()
    }
}

impl PoolStateV1 {
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
        // The Pool binary pins and KAT-checks this exact recursive empty-root
        // table.  Constructing sequence zero directly is therefore equivalent
        // to asking the generic tree constructor to recompute twenty
        // Poseidon parents, but avoids paying for that proof repeatedly in the
        // initialization instruction.
        let tree = IncrementalMerkleTreeV1 {
            next_leaf_index: 0,
            root: POOL_V1_EMPTY_ROOTS[POOL_V1_TREE_DEPTH],
            frontier: core::array::from_fn(|level| POOL_V1_EMPTY_ROOTS[level]),
        };
        Ok(Self {
            identity: PoolIdentityV1 {
                pool: pool.to_bytes(),
                asset_mint: initialization.asset_mint,
                token_program: initialization.token_program,
                asset_id: initialization.asset_id,
                deployment_domain: initialization.deployment_domain,
            },
            verifier_policy: initialization.verifier_policy,
            tree,
        })
    }

    pub fn current_root_sequence(&self) -> u64 {
        self.tree.next_leaf_index
    }

    /// Construct genesis state on the heap so SBF callers do not reserve the
    /// complete 1,000-byte state image in an already-busy instruction frame.
    pub(crate) fn genesis_boxed(
        pool: &Pubkey,
        initialization: PoolInitializationV1,
    ) -> Result<Box<Self>, ProgramError> {
        Ok(Box::new(Self::genesis(pool, initialization)?))
    }

    /// Decode state on the heap for the same SBF stack reason. The canonical
    /// decoder remains the only parser; this changes storage, not semantics.
    pub(crate) fn decode_boxed(
        data: &[u8],
        expected_pool: &Pubkey,
    ) -> Result<Box<Self>, ProgramError> {
        Ok(Box::new(Self::decode(data, expected_pool)?))
    }

    pub(crate) fn decode_boxed_with_validated_tree(
        data: &[u8],
        expected_pool: &Pubkey,
    ) -> Result<(Box<Self>, Box<ValidatedIncrementalMerkleTreeV1<'static>>), ProgramError> {
        let (state, validated_tree) = Self::decode_with_validated_tree(data, expected_pool)?;
        Ok((Box::new(state), Box::new(validated_tree)))
    }

    /// Perform every fallible check required by the canonical encoder.
    /// Callers may then write through `write_encoding_prevalidated` after an
    /// irreversible CPI without introducing a new error path.
    pub(crate) fn validate_encoding(&self) -> Result<(), ProgramError> {
        if self.tree.next_leaf_index == 0 {
            // Sequence zero has one canonical image.  Exact comparison with
            // the pinned table is the fail-closed specialization of generic
            // root reconstruction for genesis; every non-genesis state still
            // takes the complete validation path below.
            if self.tree.root != POOL_V1_EMPTY_ROOTS[POOL_V1_TREE_DEPTH]
                || self
                    .tree
                    .frontier
                    .iter()
                    .enumerate()
                    .any(|(level, node)| *node != POOL_V1_EMPTY_ROOTS[level])
            {
                return Err(ProgramError::InvalidAccountData);
            }
        } else {
            self.tree
                .validate_with_empty_roots(&POOL_V1_EMPTY_ROOTS)
                .map_err(|_| ProgramError::InvalidAccountData)?;
        }
        validate_verifier_policy_v1(&self.verifier_policy)
            .map_err(|_| ProgramError::InvalidAccountData)
    }

    /// Write the exact state image after `validate_encoding` has succeeded.
    /// The fixed-size destination makes this phase infallible and avoids a
    /// second 1,000-byte stack allocation in the transition frame.
    pub(crate) fn write_encoding_prevalidated(
        &self,
        output: &mut [u8; POOL_V1_STATE_ACCOUNT_BYTES],
    ) {
        output.fill(0);
        output[..4].copy_from_slice(&POOL_V1_STATE_ACCOUNT_MAGIC);
        output[4] = POOL_V1_STATE_ACCOUNT_VERSION;
        output[5] = POOL_V1_FORMAT_VERSION;
        output[6] = POOL_V1_TREE_DEPTH as u8;
        output[7] = POOL_V1_ROOT_HISTORY_CAPACITY_LOG2;
        output[8..40].copy_from_slice(&POOL_V1_FORMAT_BINDING);
        let sequence = self.current_root_sequence();
        let location = root_history_location(sequence);
        output[STATE_SEQUENCE_OFFSET..STATE_PAGE_OFFSET].copy_from_slice(&sequence.to_le_bytes());
        output[STATE_PAGE_OFFSET..STATE_SLOT_OFFSET]
            .copy_from_slice(&location.page_number.to_le_bytes());
        output[STATE_SLOT_OFFSET..58].copy_from_slice(&location.slot.to_le_bytes());

        let identity = encode_pool_identity_v1(&self.identity);
        output[POOL_V1_STATE_IDENTITY_OFFSET..POOL_V1_STATE_POLICY_OFFSET]
            .copy_from_slice(&identity);
        let policy = &mut output[POOL_V1_STATE_POLICY_OFFSET..POOL_V1_STATE_TREE_OFFSET];
        policy[..4].copy_from_slice(&POOL_V1_VERIFIER_POLICY_MAGIC);
        policy[4] = POOL_V1_VERIFIER_POLICY_VERSION;
        policy[5] = self.verifier_policy.flags;
        policy[8..40].copy_from_slice(&self.verifier_policy.registry_program);
        policy[40..72].copy_from_slice(&self.verifier_policy.registry_authority);
        policy[72..104].copy_from_slice(&self.verifier_policy.policy_binding);

        let tree = &mut output[POOL_V1_STATE_TREE_OFFSET..];
        tree[..4].copy_from_slice(&POOL_V1_TREE_STATE_MAGIC);
        tree[4] = POOL_V1_TREE_STATE_VERSION;
        tree[5] = POOL_V1_TREE_DEPTH as u8;
        tree[6] = POOL_V1_TREE_HASH_VERSION;
        tree[7] = aspis_statement::pool_v1::POOL_V1_DIGEST_ENCODING_VERSION;
        tree[8..16].copy_from_slice(&self.tree.next_leaf_index.to_le_bytes());
        tree[16..48].copy_from_slice(&aspis_statement::encode_digest_canonical(&self.tree.root));
        for (level, node) in self.tree.frontier.iter().enumerate() {
            let start = 48 + level * 32;
            tree[start..start + 32]
                .copy_from_slice(&aspis_statement::encode_digest_canonical(node));
        }
    }

    #[inline(never)]
    pub fn encode(&self) -> Result<[u8; POOL_V1_STATE_ACCOUNT_BYTES], ProgramError> {
        self.validate_encoding()?;
        let mut output = [0u8; POOL_V1_STATE_ACCOUNT_BYTES];
        self.write_encoding_prevalidated(&mut output);
        Ok(output)
    }

    fn decode_with_validated_tree(
        data: &[u8],
        expected_pool: &Pubkey,
    ) -> Result<(Self, ValidatedIncrementalMerkleTreeV1<'static>), ProgramError> {
        if data.len() != POOL_V1_STATE_ACCOUNT_BYTES
            || data[..4] != POOL_V1_STATE_ACCOUNT_MAGIC
            || data[4] != POOL_V1_STATE_ACCOUNT_VERSION
            || data[5] != POOL_V1_FORMAT_VERSION
            || data[6] != POOL_V1_TREE_DEPTH as u8
            || data[7] != POOL_V1_ROOT_HISTORY_CAPACITY_LOG2
            || data[8..40] != POOL_V1_FORMAT_BINDING
            || data[58..64] != [0u8; 6]
        {
            return Err(PoolV1ProgramError::InvalidAccountType.into());
        }
        let identity = decode_pool_identity_v1(
            &data[POOL_V1_STATE_IDENTITY_OFFSET..POOL_V1_STATE_POLICY_OFFSET],
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;
        if identity.pool != expected_pool.to_bytes() {
            return Err(PoolV1ProgramError::StateHistoryMismatch.into());
        }
        let verifier_policy = decode_verifier_policy_v1(
            &data[POOL_V1_STATE_POLICY_OFFSET..POOL_V1_STATE_TREE_OFFSET],
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;
        let validated_tree = ValidatedIncrementalMerkleTreeV1::decode(
            &data[POOL_V1_STATE_TREE_OFFSET..],
            &POOL_V1_EMPTY_ROOTS,
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;
        let tree = *validated_tree.as_tree();
        let sequence = u64::from_le_bytes(exact_state_array(
            &data[STATE_SEQUENCE_OFFSET..STATE_PAGE_OFFSET],
        )?);
        let page_number = u64::from_le_bytes(exact_state_array(
            &data[STATE_PAGE_OFFSET..STATE_SLOT_OFFSET],
        )?);
        let slot = u16::from_le_bytes(exact_state_array(&data[STATE_SLOT_OFFSET..58])?);
        let expected_location = root_history_location(tree.next_leaf_index);
        if sequence != tree.next_leaf_index
            || page_number != expected_location.page_number
            || slot != expected_location.slot
        {
            return Err(PoolV1ProgramError::StateHistoryMismatch.into());
        }
        Ok((
            Self {
                identity,
                verifier_policy,
                tree,
            },
            validated_tree,
        ))
    }

    pub fn decode(data: &[u8], expected_pool: &Pubkey) -> Result<Self, ProgramError> {
        Self::decode_with_validated_tree(data, expected_pool).map(|(state, _)| state)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
    fn exact_state_image_roundtrips_and_rejects_type_reserved_cursor_and_pool_confusion() {
        let pool = Pubkey::new_unique();
        let state = PoolStateV1::genesis(&pool, initialization()).unwrap();
        let encoded = state.encode().unwrap();
        assert_eq!(encoded.len(), 1_000);
        assert_eq!(
            &encoded[POOL_V1_STATE_IDENTITY_OFFSET..POOL_V1_STATE_POLICY_OFFSET],
            &aspis_statement::pool_v1::encode_pool_identity_v1(&state.identity)
        );
        assert_eq!(
            &encoded[POOL_V1_STATE_POLICY_OFFSET..POOL_V1_STATE_TREE_OFFSET],
            &aspis_statement::pool_v1::encode_verifier_policy_v1(&state.verifier_policy).unwrap()
        );
        assert_eq!(
            &encoded[POOL_V1_STATE_TREE_OFFSET..],
            &state
                .tree
                .encode_with_empty_roots(&POOL_V1_EMPTY_ROOTS)
                .unwrap()
        );
        assert_eq!(PoolStateV1::decode(&encoded, &pool), Ok(state));

        let mut wrong_version = encoded;
        wrong_version[4] = 1;
        assert_eq!(
            PoolStateV1::decode(&wrong_version, &pool),
            Err(PoolV1ProgramError::InvalidAccountType.into())
        );

        let mut reserved = encoded;
        reserved[63] = 1;
        assert_eq!(
            PoolStateV1::decode(&reserved, &pool),
            Err(PoolV1ProgramError::InvalidAccountType.into())
        );

        let mut cursor = encoded;
        cursor[STATE_SEQUENCE_OFFSET] = 1;
        assert_eq!(
            PoolStateV1::decode(&cursor, &pool),
            Err(PoolV1ProgramError::StateHistoryMismatch.into())
        );

        assert_eq!(
            PoolStateV1::decode(&encoded, &Pubkey::new_unique()),
            Err(PoolV1ProgramError::StateHistoryMismatch.into())
        );

        assert_eq!(
            PoolStateV1::genesis(
                &pool,
                PoolInitializationV1 {
                    token_program: [3u8; 32],
                    ..initialization()
                }
            ),
            Err(PoolV1ProgramError::InvalidTokenProgram.into())
        );
    }

    #[test]
    fn specialized_genesis_is_exactly_the_generic_checked_tree_and_fails_closed() {
        let pool = Pubkey::new_unique();
        let state = PoolStateV1::genesis(&pool, initialization()).unwrap();
        let checked_tree = IncrementalMerkleTreeV1::from_parts_with_empty_roots(
            0,
            POOL_V1_EMPTY_ROOTS[POOL_V1_TREE_DEPTH],
            core::array::from_fn(|level| POOL_V1_EMPTY_ROOTS[level]),
            &POOL_V1_EMPTY_ROOTS,
        )
        .unwrap();
        assert_eq!(state.tree, checked_tree);
        assert_eq!(state.validate_encoding(), Ok(()));

        let mut corrupt_root = state;
        corrupt_root.tree.root[0] = M31(1);
        assert_eq!(
            corrupt_root.validate_encoding(),
            Err(ProgramError::InvalidAccountData)
        );

        let mut corrupt_frontier = state;
        corrupt_frontier.tree.frontier[7][3] = M31(1);
        assert_eq!(
            corrupt_frontier.validate_encoding(),
            Err(ProgramError::InvalidAccountData)
        );
    }
}
