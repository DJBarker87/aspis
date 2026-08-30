//! Injectable monotonic commitment boundary for the default-off V2 wallet.
//!
//! The wallet's checksummed local image detects corruption, but it cannot by
//! itself distinguish the latest image from an older, internally valid copy.
//! A production implementation of [`WalletMonotonicStoreV2`] must therefore
//! place its current commitment in a persistence mechanism which an attacker
//! rolling back the wallet image cannot also roll back. This module specifies
//! that boundary; it does not claim protection when every trusted persistence
//! mechanism is restored together.

use sha2::{Digest as _, Sha256};

use crate::scan_state::FinalizedChainPointV1;

const MONOTONIC_COMMITMENT_DOMAIN_V2: &[u8] =
    b"aspis:pool-v1:wallet-monotonic-commitment:sha256:v2";
const MONOTONIC_QUALIFICATION_DOMAIN_V2: &[u8] =
    b"aspis:pool-v1:wallet-monotonic-store-qualification:sha256:v2";

/// Operator-qualified identity for a rollback-independent production backend.
///
/// The backend supplies this attestation through the injected trait. The
/// wallet binds it to the exact ASL2 protection ID but cannot independently
/// prove the backend's durability; deployment qualification remains an
/// explicit external trust boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WalletMonotonicStoreQualificationV2 {
    backend_identity: [u8; 32],
    protection_id: [u8; 32],
    configuration_digest: [u8; 32],
}

impl WalletMonotonicStoreQualificationV2 {
    pub fn new_v2(
        backend_identity: [u8; 32],
        protection_id: [u8; 32],
        configuration_digest: [u8; 32],
    ) -> Result<Self, WalletMonotonicStoreErrorV2> {
        if backend_identity == [0u8; 32]
            || protection_id == [0u8; 32]
            || configuration_digest == [0u8; 32]
        {
            return Err(WalletMonotonicStoreErrorV2::InvalidQualification);
        }
        Ok(Self {
            backend_identity,
            protection_id,
            configuration_digest,
        })
    }

    pub fn protection_id(&self) -> &[u8; 32] {
        &self.protection_id
    }

    pub fn qualification_digest_v2(&self) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(MONOTONIC_QUALIFICATION_DOMAIN_V2);
        hasher.update(self.backend_identity);
        hasher.update(self.protection_id);
        hasher.update(self.configuration_digest);
        hasher.finalize().into()
    }
}

/// One externally anchored commitment to an authoritative wallet generation.
///
/// Generation zero is the only valid genesis and has a zero predecessor.
/// Every later generation names the exact commitment digest of its immediate
/// predecessor. The finalized point may stay unchanged while other durable
/// wallet state advances, but it may never regress or change hash at one slot.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct WalletMonotonicCommitmentV2 {
    generation: u64,
    finalized_point: FinalizedChainPointV1,
    predecessor_commitment: [u8; 32],
    state_digest: [u8; 32],
}

impl core::fmt::Debug for WalletMonotonicCommitmentV2 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("WalletMonotonicCommitmentV2")
            .field("generation", &self.generation)
            .field("finalized_point", &self.finalized_point)
            .field("commitment_material", &"[REDACTED]")
            .finish()
    }
}

impl WalletMonotonicCommitmentV2 {
    pub fn new_v2(
        generation: u64,
        finalized_point: FinalizedChainPointV1,
        predecessor_commitment: [u8; 32],
        state_digest: [u8; 32],
    ) -> Result<Self, WalletMonotonicStoreErrorV2> {
        if state_digest == [0u8; 32]
            || (generation == 0 && predecessor_commitment != [0u8; 32])
            || (generation != 0 && predecessor_commitment == [0u8; 32])
        {
            return Err(WalletMonotonicStoreErrorV2::InvalidCommitment);
        }
        Ok(Self {
            generation,
            finalized_point,
            predecessor_commitment,
            state_digest,
        })
    }

    pub fn generation(&self) -> u64 {
        self.generation
    }

    pub fn finalized_point(&self) -> FinalizedChainPointV1 {
        self.finalized_point
    }

    pub fn predecessor_commitment(&self) -> &[u8; 32] {
        &self.predecessor_commitment
    }

    pub fn state_digest(&self) -> &[u8; 32] {
        &self.state_digest
    }

    /// Domain-separated digest named by the immediate successor.
    pub fn commitment_digest_v2(&self) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(MONOTONIC_COMMITMENT_DOMAIN_V2);
        hasher.update(self.generation.to_le_bytes());
        hasher.update(self.finalized_point.slot().to_le_bytes());
        hasher.update(self.finalized_point.block_hash());
        hasher.update(self.predecessor_commitment);
        hasher.update(self.state_digest);
        hasher.finalize().into()
    }

    fn expected_predecessor_v2(&self) -> Option<[u8; 32]> {
        (self.generation != 0).then_some(self.predecessor_commitment)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WalletMonotonicAdvanceV2 {
    Advanced,
    AlreadyCurrent,
}

/// Fail-closed outcomes shared by deterministic and production stores.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WalletMonotonicStoreErrorV2 {
    InvalidCommitment,
    InvalidQualification,
    BackendUnavailable,
    CompareMismatch,
    CommitmentConflict,
    GenerationRegression,
    GenerationGap,
    PredecessorMismatch,
    FinalizedPointRegression,
    FinalizedPointConflict,
}

/// External rollback-protection boundary used by ASL2 activation and commits.
///
/// `expected_predecessor` is the compare-and-swap expectation used when the
/// candidate was constructed: `None` for generation zero, otherwise the exact
/// digest stored in `candidate.predecessor_commitment()`. Implementations must
/// make comparison and advancement one atomic durable operation.
pub trait WalletMonotonicStoreV2 {
    /// Return `Some` only for a deployment-qualified, rollback-independent
    /// production backend. Volatile/test stores must return `None`.
    fn production_qualification_v2(&self) -> Option<WalletMonotonicStoreQualificationV2> {
        None
    }

    fn current_commitment_v2(
        &self,
    ) -> Result<Option<WalletMonotonicCommitmentV2>, WalletMonotonicStoreErrorV2>;

    fn compare_and_advance_v2(
        &mut self,
        expected_predecessor: Option<[u8; 32]>,
        candidate: WalletMonotonicCommitmentV2,
    ) -> Result<WalletMonotonicAdvanceV2, WalletMonotonicStoreErrorV2>;
}

/// Deterministic test implementation. It models an atomic trusted store but is
/// deliberately not durable and is not suitable as a production rollback
/// anchor.
#[derive(Clone, Debug, Default)]
pub struct InMemoryWalletMonotonicStoreV2 {
    current: Option<WalletMonotonicCommitmentV2>,
}

impl InMemoryWalletMonotonicStoreV2 {
    pub fn new_v2() -> Self {
        Self::default()
    }
}

impl WalletMonotonicStoreV2 for InMemoryWalletMonotonicStoreV2 {
    fn current_commitment_v2(
        &self,
    ) -> Result<Option<WalletMonotonicCommitmentV2>, WalletMonotonicStoreErrorV2> {
        Ok(self.current)
    }

    fn compare_and_advance_v2(
        &mut self,
        expected_predecessor: Option<[u8; 32]>,
        candidate: WalletMonotonicCommitmentV2,
    ) -> Result<WalletMonotonicAdvanceV2, WalletMonotonicStoreErrorV2> {
        if candidate.state_digest == [0u8; 32]
            || candidate.expected_predecessor_v2() != expected_predecessor
        {
            return Err(if candidate.state_digest == [0u8; 32] {
                WalletMonotonicStoreErrorV2::InvalidCommitment
            } else {
                WalletMonotonicStoreErrorV2::CompareMismatch
            });
        }

        let Some(current) = self.current else {
            if candidate.generation != 0 || candidate.predecessor_commitment != [0u8; 32] {
                return Err(WalletMonotonicStoreErrorV2::GenerationGap);
            }
            self.current = Some(candidate);
            return Ok(WalletMonotonicAdvanceV2::Advanced);
        };

        if candidate == current {
            return Ok(WalletMonotonicAdvanceV2::AlreadyCurrent);
        }
        if candidate.generation < current.generation {
            return Err(WalletMonotonicStoreErrorV2::GenerationRegression);
        }
        if candidate.generation == current.generation {
            return Err(WalletMonotonicStoreErrorV2::CommitmentConflict);
        }
        let next_generation = current
            .generation
            .checked_add(1)
            .ok_or(WalletMonotonicStoreErrorV2::GenerationGap)?;
        if candidate.generation != next_generation {
            return Err(WalletMonotonicStoreErrorV2::GenerationGap);
        }
        let current_digest = current.commitment_digest_v2();
        if expected_predecessor != Some(current_digest)
            || candidate.predecessor_commitment != current_digest
        {
            return Err(WalletMonotonicStoreErrorV2::PredecessorMismatch);
        }
        if candidate.finalized_point.slot() < current.finalized_point.slot() {
            return Err(WalletMonotonicStoreErrorV2::FinalizedPointRegression);
        }
        if candidate.finalized_point.slot() == current.finalized_point.slot()
            && candidate.finalized_point != current.finalized_point
        {
            return Err(WalletMonotonicStoreErrorV2::FinalizedPointConflict);
        }

        self.current = Some(candidate);
        Ok(WalletMonotonicAdvanceV2::Advanced)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn point(slot: u64, seed: u8) -> FinalizedChainPointV1 {
        FinalizedChainPointV1::new(slot, [seed; 32]).unwrap()
    }

    fn genesis() -> WalletMonotonicCommitmentV2 {
        WalletMonotonicCommitmentV2::new_v2(0, point(10, 1), [0u8; 32], [0x31; 32]).unwrap()
    }

    fn successor(
        previous: WalletMonotonicCommitmentV2,
        generation: u64,
        finalized_point: FinalizedChainPointV1,
        state_seed: u8,
    ) -> WalletMonotonicCommitmentV2 {
        WalletMonotonicCommitmentV2::new_v2(
            generation,
            finalized_point,
            previous.commitment_digest_v2(),
            [state_seed; 32],
        )
        .unwrap()
    }

    #[test]
    fn genesis_and_exact_replay_are_atomic_and_idempotent() {
        let mut store = InMemoryWalletMonotonicStoreV2::new_v2();
        assert_eq!(store.production_qualification_v2(), None);
        let first = genesis();
        assert_eq!(
            store.compare_and_advance_v2(None, first),
            Ok(WalletMonotonicAdvanceV2::Advanced)
        );
        assert_eq!(
            store.compare_and_advance_v2(None, first),
            Ok(WalletMonotonicAdvanceV2::AlreadyCurrent)
        );
        assert_eq!(store.current_commitment_v2(), Ok(Some(first)));
    }

    #[test]
    fn same_generation_conflict_and_stale_generation_fail_closed() {
        let mut store = InMemoryWalletMonotonicStoreV2::new_v2();
        let first = genesis();
        store.compare_and_advance_v2(None, first).unwrap();
        let conflicting =
            WalletMonotonicCommitmentV2::new_v2(0, first.finalized_point(), [0u8; 32], [0x32; 32])
                .unwrap();
        assert_eq!(
            store.compare_and_advance_v2(None, conflicting),
            Err(WalletMonotonicStoreErrorV2::CommitmentConflict)
        );
        let second = successor(first, 1, point(11, 2), 0x33);
        store
            .compare_and_advance_v2(Some(first.commitment_digest_v2()), second)
            .unwrap();
        assert_eq!(
            store.compare_and_advance_v2(None, first),
            Err(WalletMonotonicStoreErrorV2::GenerationRegression)
        );
        assert_eq!(store.current_commitment_v2(), Ok(Some(second)));
    }

    #[test]
    fn predecessor_mismatch_and_generation_gap_fail_closed() {
        let mut store = InMemoryWalletMonotonicStoreV2::new_v2();
        let first = genesis();
        store.compare_and_advance_v2(None, first).unwrap();

        let wrong_predecessor =
            WalletMonotonicCommitmentV2::new_v2(1, point(11, 2), [0x91; 32], [0x41; 32]).unwrap();
        assert_eq!(
            store.compare_and_advance_v2(Some([0x91; 32]), wrong_predecessor),
            Err(WalletMonotonicStoreErrorV2::PredecessorMismatch)
        );

        let gap = successor(first, 2, point(12, 3), 0x42);
        assert_eq!(
            store.compare_and_advance_v2(Some(first.commitment_digest_v2()), gap),
            Err(WalletMonotonicStoreErrorV2::GenerationGap)
        );
        assert_eq!(store.current_commitment_v2(), Ok(Some(first)));
    }

    #[test]
    fn finalized_point_regression_and_same_slot_conflict_fail_closed() {
        let mut store = InMemoryWalletMonotonicStoreV2::new_v2();
        let first = genesis();
        store.compare_and_advance_v2(None, first).unwrap();
        let predecessor = Some(first.commitment_digest_v2());

        let regression = successor(first, 1, point(9, 2), 0x51);
        assert_eq!(
            store.compare_and_advance_v2(predecessor, regression),
            Err(WalletMonotonicStoreErrorV2::FinalizedPointRegression)
        );
        let conflict = successor(first, 1, point(10, 2), 0x52);
        assert_eq!(
            store.compare_and_advance_v2(predecessor, conflict),
            Err(WalletMonotonicStoreErrorV2::FinalizedPointConflict)
        );
        let unchanged_point = successor(first, 1, first.finalized_point(), 0x53);
        assert_eq!(
            store.compare_and_advance_v2(predecessor, unchanged_point),
            Ok(WalletMonotonicAdvanceV2::Advanced)
        );
    }

    #[test]
    fn malformed_commitments_and_wrong_compare_expectation_are_rejected() {
        assert_eq!(
            WalletMonotonicCommitmentV2::new_v2(0, point(1, 1), [1u8; 32], [2u8; 32]),
            Err(WalletMonotonicStoreErrorV2::InvalidCommitment)
        );
        assert_eq!(
            WalletMonotonicCommitmentV2::new_v2(1, point(1, 1), [0u8; 32], [2u8; 32]),
            Err(WalletMonotonicStoreErrorV2::InvalidCommitment)
        );
        assert_eq!(
            WalletMonotonicCommitmentV2::new_v2(0, point(1, 1), [0u8; 32], [0u8; 32]),
            Err(WalletMonotonicStoreErrorV2::InvalidCommitment)
        );

        let mut store = InMemoryWalletMonotonicStoreV2::new_v2();
        let first = genesis();
        assert_eq!(
            store.compare_and_advance_v2(Some([0x71; 32]), first),
            Err(WalletMonotonicStoreErrorV2::CompareMismatch)
        );
        assert_eq!(store.current_commitment_v2(), Ok(None));
    }

    #[test]
    fn recovery_replay_and_restored_older_commitments_are_deterministic() {
        let mut store = InMemoryWalletMonotonicStoreV2::new_v2();
        let first = genesis();
        store.compare_and_advance_v2(None, first).unwrap();
        let first_digest = first.commitment_digest_v2();
        let second = successor(first, 1, point(11, 2), 0x81);
        store
            .compare_and_advance_v2(Some(first_digest), second)
            .unwrap();

        // Recovery after an externally anchored advance may repeat without
        // changing the trusted commitment.
        for _ in 0..2 {
            assert_eq!(
                store.compare_and_advance_v2(Some(first_digest), second),
                Ok(WalletMonotonicAdvanceV2::AlreadyCurrent)
            );
            assert_eq!(store.current_commitment_v2(), Ok(Some(second)));
        }

        // A checksummed but older local image and a conflicting image at the
        // current generation both fail closed and cannot disturb the anchor.
        for _ in 0..2 {
            assert_eq!(
                store.compare_and_advance_v2(None, first),
                Err(WalletMonotonicStoreErrorV2::GenerationRegression)
            );
        }
        let conflicting_second = successor(first, 1, point(11, 2), 0x82);
        assert_eq!(
            store.compare_and_advance_v2(Some(first_digest), conflicting_second),
            Err(WalletMonotonicStoreErrorV2::CommitmentConflict)
        );
        assert_eq!(store.current_commitment_v2(), Ok(Some(second)));

        // A caller cannot advance using a stale or invented CAS expectation.
        let third = successor(second, 2, point(12, 3), 0x83);
        assert_eq!(
            store.compare_and_advance_v2(Some(first_digest), third),
            Err(WalletMonotonicStoreErrorV2::CompareMismatch)
        );
        assert_eq!(store.current_commitment_v2(), Ok(Some(second)));
        assert_eq!(
            store.compare_and_advance_v2(Some(second.commitment_digest_v2()), third),
            Ok(WalletMonotonicAdvanceV2::Advanced)
        );
    }
}
