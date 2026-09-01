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
use std::sync::{Arc, Mutex};

use crate::scan_state::FinalizedChainPointV1;

const MONOTONIC_COMMITMENT_DOMAIN_V2: &[u8] =
    b"aspis:pool-v1:wallet-monotonic-commitment:sha256:v2";
const MONOTONIC_QUALIFICATION_DOMAIN_V2: &[u8] =
    b"aspis:pool-v1:wallet-monotonic-store-qualification:sha256:v2";
const MONOTONIC_PREPARED_NEXT_DOMAIN_V2: &[u8] =
    b"aspis:pool-v1:wallet-monotonic-prepared-next:sha256:v2";

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
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WalletMonotonicAdvanceV2 {
    Advanced,
    AlreadyCurrent,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WalletMonotonicPrepareV2 {
    Prepared,
    AlreadyPrepared,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WalletMonotonicAbortV2 {
    Aborted,
    AlreadyAbsent,
}

/// Exact externally authenticated reservation for one ASL2 replacement.
///
/// The next commitment binds the generation and canonical ASL2 content. The
/// additional image digest binds the physical checksummed file, while the
/// wallet, activation, protection, cipher and operation identities prevent a
/// reservation from being replayed across security domains.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct WalletMonotonicPreparedNextV2 {
    expected_current: Option<WalletMonotonicCommitmentV2>,
    next: WalletMonotonicCommitmentV2,
    next_image_digest: [u8; 32],
    wallet_identity: [u8; 32],
    activation_identity: [u8; 32],
    protection_id: [u8; 32],
    note_cipher_id: [u8; 32],
    operation_identity: [u8; 32],
}

impl core::fmt::Debug for WalletMonotonicPreparedNextV2 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("WalletMonotonicPreparedNextV2")
            .field("next_generation", &self.next.generation())
            .field("bindings", &"[REDACTED]")
            .finish()
    }
}

impl WalletMonotonicPreparedNextV2 {
    #[allow(clippy::too_many_arguments)]
    pub fn new_v2(
        expected_current: Option<WalletMonotonicCommitmentV2>,
        next: WalletMonotonicCommitmentV2,
        next_image_digest: [u8; 32],
        wallet_identity: [u8; 32],
        activation_identity: [u8; 32],
        protection_id: [u8; 32],
        note_cipher_id: [u8; 32],
        operation_identity: [u8; 32],
    ) -> Result<Self, WalletMonotonicStoreErrorV2> {
        if [
            next_image_digest,
            wallet_identity,
            activation_identity,
            protection_id,
            note_cipher_id,
            operation_identity,
        ]
        .contains(&[0u8; 32])
        {
            return Err(WalletMonotonicStoreErrorV2::InvalidPreparation);
        }
        match expected_current {
            None if next.generation() == 0 && next.predecessor_commitment() == &[0u8; 32] => {}
            Some(current)
                if current
                    .generation()
                    .checked_add(1)
                    .is_some_and(|generation| generation == next.generation())
                    && next.predecessor_commitment() == &current.commitment_digest_v2()
                    && next.finalized_point().slot() >= current.finalized_point().slot()
                    && (next.finalized_point().slot() != current.finalized_point().slot()
                        || next.finalized_point() == current.finalized_point()) => {}
            _ => return Err(WalletMonotonicStoreErrorV2::InvalidPreparation),
        }
        Ok(Self {
            expected_current,
            next,
            next_image_digest,
            wallet_identity,
            activation_identity,
            protection_id,
            note_cipher_id,
            operation_identity,
        })
    }

    pub fn expected_current_v2(&self) -> Option<WalletMonotonicCommitmentV2> {
        self.expected_current
    }

    pub fn next_commitment_v2(&self) -> WalletMonotonicCommitmentV2 {
        self.next
    }

    pub fn next_image_digest_v2(&self) -> &[u8; 32] {
        &self.next_image_digest
    }

    pub fn protection_id_v2(&self) -> &[u8; 32] {
        &self.protection_id
    }

    pub fn prepared_identity_v2(&self) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(MONOTONIC_PREPARED_NEXT_DOMAIN_V2);
        match self.expected_current {
            Some(current) => {
                hasher.update([1]);
                hasher.update(current.commitment_digest_v2());
            }
            None => hasher.update([0]),
        }
        hasher.update(self.next.commitment_digest_v2());
        hasher.update(self.next_image_digest);
        hasher.update(self.wallet_identity);
        hasher.update(self.activation_identity);
        hasher.update(self.protection_id);
        hasher.update(self.note_cipher_id);
        hasher.update(self.operation_identity);
        hasher.finalize().into()
    }
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
    InvalidPreparation,
    PreparationRequired,
    PreparationConflict,
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

    fn prepared_next_v2(
        &self,
    ) -> Result<Option<WalletMonotonicPreparedNextV2>, WalletMonotonicStoreErrorV2>;

    /// Atomically reserve one exact successor while the trusted current value
    /// still equals `prepared.expected_current_v2()`.
    fn compare_and_prepare_next_v2(
        &mut self,
        prepared: WalletMonotonicPreparedNextV2,
    ) -> Result<WalletMonotonicPrepareV2, WalletMonotonicStoreErrorV2>;

    /// Atomically advance current to the exact prepared successor and consume
    /// the reservation. A response lost after the CAS is safe to replay.
    /// Implementations must retain enough authenticated identity to
    /// distinguish that exact replay from a different preparation naming the
    /// same logical successor.
    fn compare_and_commit_prepared_v2(
        &mut self,
        prepared: WalletMonotonicPreparedNextV2,
    ) -> Result<WalletMonotonicAdvanceV2, WalletMonotonicStoreErrorV2>;

    /// Atomically discard a reservation only while its predecessor is still
    /// current. This recovers a crash after prepare but before local replace
    /// to the exact pre-write state. Exact lost-response replay is idempotent;
    /// a different absent preparation must not be reported as that replay.
    fn compare_and_abort_prepared_v2(
        &mut self,
        prepared: WalletMonotonicPreparedNextV2,
    ) -> Result<WalletMonotonicAbortV2, WalletMonotonicStoreErrorV2>;
}

/// Deterministic test implementation. It models an atomic trusted store but is
/// deliberately not durable and is not suitable as a production rollback
/// anchor.
#[derive(Clone, Debug, Default)]
pub struct InMemoryWalletMonotonicStoreV2 {
    current: Option<WalletMonotonicCommitmentV2>,
    prepared: Option<WalletMonotonicPreparedNextV2>,
    last_committed: Option<WalletMonotonicPreparedNextV2>,
    last_aborted: Option<WalletMonotonicPreparedNextV2>,
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

    fn prepared_next_v2(
        &self,
    ) -> Result<Option<WalletMonotonicPreparedNextV2>, WalletMonotonicStoreErrorV2> {
        Ok(self.prepared)
    }

    fn compare_and_prepare_next_v2(
        &mut self,
        prepared: WalletMonotonicPreparedNextV2,
    ) -> Result<WalletMonotonicPrepareV2, WalletMonotonicStoreErrorV2> {
        if self.current != prepared.expected_current {
            return Err(WalletMonotonicStoreErrorV2::CompareMismatch);
        }
        match self.prepared {
            Some(existing) if existing == prepared => Ok(WalletMonotonicPrepareV2::AlreadyPrepared),
            Some(_) => Err(WalletMonotonicStoreErrorV2::PreparationConflict),
            None => {
                self.prepared = Some(prepared);
                self.last_aborted = None;
                Ok(WalletMonotonicPrepareV2::Prepared)
            }
        }
    }

    fn compare_and_commit_prepared_v2(
        &mut self,
        prepared: WalletMonotonicPreparedNextV2,
    ) -> Result<WalletMonotonicAdvanceV2, WalletMonotonicStoreErrorV2> {
        if self.current == Some(prepared.next) && self.prepared.is_none() {
            return if self.last_committed == Some(prepared) {
                Ok(WalletMonotonicAdvanceV2::AlreadyCurrent)
            } else {
                Err(WalletMonotonicStoreErrorV2::PreparationConflict)
            };
        }
        if self.current != prepared.expected_current {
            return Err(WalletMonotonicStoreErrorV2::CompareMismatch);
        }
        match self.prepared {
            Some(existing) if existing == prepared => {
                self.current = Some(prepared.next);
                self.prepared = None;
                self.last_committed = Some(prepared);
                self.last_aborted = None;
                Ok(WalletMonotonicAdvanceV2::Advanced)
            }
            Some(_) => Err(WalletMonotonicStoreErrorV2::PreparationConflict),
            None => Err(WalletMonotonicStoreErrorV2::PreparationRequired),
        }
    }

    fn compare_and_abort_prepared_v2(
        &mut self,
        prepared: WalletMonotonicPreparedNextV2,
    ) -> Result<WalletMonotonicAbortV2, WalletMonotonicStoreErrorV2> {
        if self.current != prepared.expected_current {
            return Err(WalletMonotonicStoreErrorV2::CompareMismatch);
        }
        match self.prepared {
            Some(existing) if existing == prepared => {
                self.prepared = None;
                self.last_aborted = Some(prepared);
                Ok(WalletMonotonicAbortV2::Aborted)
            }
            Some(_) => Err(WalletMonotonicStoreErrorV2::PreparationConflict),
            None if self.last_aborted == Some(prepared) => {
                Ok(WalletMonotonicAbortV2::AlreadyAbsent)
            }
            None if self.last_aborted.is_some() => {
                Err(WalletMonotonicStoreErrorV2::PreparationConflict)
            }
            None => Err(WalletMonotonicStoreErrorV2::PreparationRequired),
        }
    }
}

/// One externally observable protocol boundary used by deterministic crash
/// tests. `After*` faults apply the atomic trusted mutation and then lose the
/// response, modelling a process or transport failure after durable CAS.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WalletMonotonicFaultPointV2 {
    CurrentRead,
    PreparedRead,
    BeforePrepare,
    AfterPrepare,
    BeforeCommit,
    AfterCommit,
    BeforeAbort,
    AfterAbort,
}

/// Shared, fault-injectable reference service for deterministic tests.
///
/// This type is volatile by construction and can never return a production
/// qualification. Clones share the same simulated trusted state so restart
/// tests can inject a fresh coordinator without losing the external anchor.
#[derive(Clone, Default)]
pub struct FaultInjectableWalletMonotonicStoreV2 {
    state: Arc<Mutex<InMemoryWalletMonotonicStoreV2>>,
    next_fault: Arc<Mutex<Option<WalletMonotonicFaultPointV2>>>,
    stale_current_once: Arc<Mutex<Option<Option<WalletMonotonicCommitmentV2>>>>,
}

impl core::fmt::Debug for FaultInjectableWalletMonotonicStoreV2 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("FaultInjectableWalletMonotonicStoreV2")
            .field("production_qualified", &false)
            .field("state", &"[REDACTED]")
            .finish()
    }
}

impl FaultInjectableWalletMonotonicStoreV2 {
    pub fn new_v2() -> Self {
        Self::default()
    }

    pub fn inject_once_v2(
        &self,
        point: WalletMonotonicFaultPointV2,
    ) -> Result<(), WalletMonotonicStoreErrorV2> {
        let mut fault = self
            .next_fault
            .lock()
            .map_err(|_| WalletMonotonicStoreErrorV2::BackendUnavailable)?;
        if fault.is_some() {
            return Err(WalletMonotonicStoreErrorV2::BackendUnavailable);
        }
        *fault = Some(point);
        Ok(())
    }

    /// Return one caller-supplied stale current value, then resume exact
    /// service reads. This is test-only evidence that a stale provider
    /// response cannot make the local image acceptable or mutate the service.
    pub fn inject_stale_current_once_v2(
        &self,
        response: Option<WalletMonotonicCommitmentV2>,
    ) -> Result<(), WalletMonotonicStoreErrorV2> {
        let mut stale = self
            .stale_current_once
            .lock()
            .map_err(|_| WalletMonotonicStoreErrorV2::BackendUnavailable)?;
        if stale.is_some() {
            return Err(WalletMonotonicStoreErrorV2::BackendUnavailable);
        }
        *stale = Some(response);
        Ok(())
    }

    fn take_fault_v2(
        &self,
        point: WalletMonotonicFaultPointV2,
    ) -> Result<bool, WalletMonotonicStoreErrorV2> {
        let mut fault = self
            .next_fault
            .lock()
            .map_err(|_| WalletMonotonicStoreErrorV2::BackendUnavailable)?;
        if *fault == Some(point) {
            *fault = None;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    fn with_state_v2<T>(
        &self,
        apply: impl FnOnce(&mut InMemoryWalletMonotonicStoreV2) -> T,
    ) -> Result<T, WalletMonotonicStoreErrorV2> {
        let mut state = self
            .state
            .lock()
            .map_err(|_| WalletMonotonicStoreErrorV2::BackendUnavailable)?;
        Ok(apply(&mut state))
    }
}

impl WalletMonotonicStoreV2 for FaultInjectableWalletMonotonicStoreV2 {
    fn current_commitment_v2(
        &self,
    ) -> Result<Option<WalletMonotonicCommitmentV2>, WalletMonotonicStoreErrorV2> {
        if let Some(stale) = self
            .stale_current_once
            .lock()
            .map_err(|_| WalletMonotonicStoreErrorV2::BackendUnavailable)?
            .take()
        {
            return Ok(stale);
        }
        if self.take_fault_v2(WalletMonotonicFaultPointV2::CurrentRead)? {
            return Err(WalletMonotonicStoreErrorV2::BackendUnavailable);
        }
        self.with_state_v2(|state| state.current_commitment_v2())?
    }

    fn prepared_next_v2(
        &self,
    ) -> Result<Option<WalletMonotonicPreparedNextV2>, WalletMonotonicStoreErrorV2> {
        if self.take_fault_v2(WalletMonotonicFaultPointV2::PreparedRead)? {
            return Err(WalletMonotonicStoreErrorV2::BackendUnavailable);
        }
        self.with_state_v2(|state| state.prepared_next_v2())?
    }

    fn compare_and_prepare_next_v2(
        &mut self,
        prepared: WalletMonotonicPreparedNextV2,
    ) -> Result<WalletMonotonicPrepareV2, WalletMonotonicStoreErrorV2> {
        if self.take_fault_v2(WalletMonotonicFaultPointV2::BeforePrepare)? {
            return Err(WalletMonotonicStoreErrorV2::BackendUnavailable);
        }
        let result = self.with_state_v2(|state| state.compare_and_prepare_next_v2(prepared))??;
        if self.take_fault_v2(WalletMonotonicFaultPointV2::AfterPrepare)? {
            Err(WalletMonotonicStoreErrorV2::BackendUnavailable)
        } else {
            Ok(result)
        }
    }

    fn compare_and_commit_prepared_v2(
        &mut self,
        prepared: WalletMonotonicPreparedNextV2,
    ) -> Result<WalletMonotonicAdvanceV2, WalletMonotonicStoreErrorV2> {
        if self.take_fault_v2(WalletMonotonicFaultPointV2::BeforeCommit)? {
            return Err(WalletMonotonicStoreErrorV2::BackendUnavailable);
        }
        let result =
            self.with_state_v2(|state| state.compare_and_commit_prepared_v2(prepared))??;
        if self.take_fault_v2(WalletMonotonicFaultPointV2::AfterCommit)? {
            Err(WalletMonotonicStoreErrorV2::BackendUnavailable)
        } else {
            Ok(result)
        }
    }

    fn compare_and_abort_prepared_v2(
        &mut self,
        prepared: WalletMonotonicPreparedNextV2,
    ) -> Result<WalletMonotonicAbortV2, WalletMonotonicStoreErrorV2> {
        if self.take_fault_v2(WalletMonotonicFaultPointV2::BeforeAbort)? {
            return Err(WalletMonotonicStoreErrorV2::BackendUnavailable);
        }
        let result =
            self.with_state_v2(|state| state.compare_and_abort_prepared_v2(prepared))??;
        if self.take_fault_v2(WalletMonotonicFaultPointV2::AfterAbort)? {
            Err(WalletMonotonicStoreErrorV2::BackendUnavailable)
        } else {
            Ok(result)
        }
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

    fn prepared(
        current: Option<WalletMonotonicCommitmentV2>,
        next: WalletMonotonicCommitmentV2,
        seed: u8,
    ) -> WalletMonotonicPreparedNextV2 {
        WalletMonotonicPreparedNextV2::new_v2(
            current, next, [seed; 32], [0x11; 32], [0x12; 32], [0x13; 32], [0x14; 32], [0x15; 32],
        )
        .unwrap()
    }

    fn commit_genesis(store: &mut InMemoryWalletMonotonicStoreV2) -> WalletMonotonicCommitmentV2 {
        let first = genesis();
        let reservation = prepared(None, first, 0x21);
        store.compare_and_prepare_next_v2(reservation).unwrap();
        store.compare_and_commit_prepared_v2(reservation).unwrap();
        first
    }

    #[test]
    fn prepare_commit_and_exact_replay_are_atomic_and_idempotent() {
        let mut store = InMemoryWalletMonotonicStoreV2::new_v2();
        assert_eq!(store.production_qualification_v2(), None);
        let first = genesis();
        let reservation = prepared(None, first, 0x21);
        assert_eq!(
            store.compare_and_prepare_next_v2(reservation),
            Ok(WalletMonotonicPrepareV2::Prepared)
        );
        assert_eq!(
            store.compare_and_prepare_next_v2(reservation),
            Ok(WalletMonotonicPrepareV2::AlreadyPrepared)
        );
        assert_eq!(
            store.compare_and_commit_prepared_v2(reservation),
            Ok(WalletMonotonicAdvanceV2::Advanced)
        );
        assert_eq!(
            store.compare_and_commit_prepared_v2(reservation),
            Ok(WalletMonotonicAdvanceV2::AlreadyCurrent)
        );
        let same_successor_different_binding = prepared(None, first, 0x22);
        assert_eq!(
            store.compare_and_commit_prepared_v2(same_successor_different_binding),
            Err(WalletMonotonicStoreErrorV2::PreparationConflict)
        );
        assert_eq!(store.current_commitment_v2(), Ok(Some(first)));
        assert_eq!(store.prepared_next_v2(), Ok(None));
    }

    #[test]
    fn conflicting_preparation_and_hash_substitution_change_nothing() {
        let mut store = InMemoryWalletMonotonicStoreV2::new_v2();
        let first = genesis();
        let reservation = prepared(None, first, 0x21);
        store.compare_and_prepare_next_v2(reservation).unwrap();
        let substitution = prepared(None, first, 0x22);
        assert_eq!(
            store.compare_and_prepare_next_v2(substitution),
            Err(WalletMonotonicStoreErrorV2::PreparationConflict)
        );
        assert_eq!(
            store.compare_and_commit_prepared_v2(substitution),
            Err(WalletMonotonicStoreErrorV2::PreparationConflict)
        );
        assert_eq!(store.current_commitment_v2(), Ok(None));
        assert_eq!(store.prepared_next_v2(), Ok(Some(reservation)));
    }

    #[test]
    fn successor_requires_exact_preparation_and_current() {
        let mut store = InMemoryWalletMonotonicStoreV2::new_v2();
        let first = commit_genesis(&mut store);
        let second = successor(first, 1, point(11, 2), 0x33);
        let reservation = prepared(Some(first), second, 0x31);
        assert_eq!(
            store.compare_and_commit_prepared_v2(reservation),
            Err(WalletMonotonicStoreErrorV2::PreparationRequired)
        );
        store.compare_and_prepare_next_v2(reservation).unwrap();
        store.compare_and_commit_prepared_v2(reservation).unwrap();
        let stale = prepared(Some(first), second, 0x31);
        assert_eq!(
            store.compare_and_prepare_next_v2(stale),
            Err(WalletMonotonicStoreErrorV2::CompareMismatch)
        );
        assert_eq!(store.current_commitment_v2(), Ok(Some(second)));
    }

    #[test]
    fn malformed_generation_point_and_zero_bindings_are_rejected() {
        let first = genesis();
        let wrong_predecessor =
            WalletMonotonicCommitmentV2::new_v2(1, point(11, 2), [0x91; 32], [0x41; 32]).unwrap();
        assert_eq!(
            WalletMonotonicPreparedNextV2::new_v2(
                Some(first),
                wrong_predecessor,
                [1; 32],
                [2; 32],
                [3; 32],
                [4; 32],
                [5; 32],
                [6; 32],
            ),
            Err(WalletMonotonicStoreErrorV2::InvalidPreparation)
        );
        let skipped_generation = WalletMonotonicCommitmentV2::new_v2(
            2,
            point(11, 2),
            first.commitment_digest_v2(),
            [0x43; 32],
        )
        .unwrap();
        assert_eq!(
            WalletMonotonicPreparedNextV2::new_v2(
                Some(first),
                skipped_generation,
                [1; 32],
                [2; 32],
                [3; 32],
                [4; 32],
                [5; 32],
                [6; 32],
            ),
            Err(WalletMonotonicStoreErrorV2::InvalidPreparation)
        );
        let point_conflict = successor(first, 1, point(10, 9), 0x42);
        assert_eq!(
            WalletMonotonicPreparedNextV2::new_v2(
                Some(first),
                point_conflict,
                [1; 32],
                [2; 32],
                [3; 32],
                [4; 32],
                [5; 32],
                [6; 32],
            ),
            Err(WalletMonotonicStoreErrorV2::InvalidPreparation)
        );
        assert_eq!(
            WalletMonotonicPreparedNextV2::new_v2(
                None, first, [0; 32], [2; 32], [3; 32], [4; 32], [5; 32], [6; 32],
            ),
            Err(WalletMonotonicStoreErrorV2::InvalidPreparation)
        );
    }

    #[test]
    fn abort_returns_to_exact_pre_state_and_replays() {
        let mut store = InMemoryWalletMonotonicStoreV2::new_v2();
        let first = genesis();
        let reservation = prepared(None, first, 0x51);
        store.compare_and_prepare_next_v2(reservation).unwrap();
        assert_eq!(
            store.compare_and_abort_prepared_v2(reservation),
            Ok(WalletMonotonicAbortV2::Aborted)
        );
        assert_eq!(
            store.compare_and_abort_prepared_v2(reservation),
            Ok(WalletMonotonicAbortV2::AlreadyAbsent)
        );
        let substitution = prepared(None, first, 0x52);
        assert_eq!(
            store.compare_and_abort_prepared_v2(substitution),
            Err(WalletMonotonicStoreErrorV2::PreparationConflict)
        );
        assert_eq!(store.current_commitment_v2(), Ok(None));
        assert_eq!(store.prepared_next_v2(), Ok(None));
    }

    #[test]
    fn preparation_identity_binds_every_security_domain() {
        let first = genesis();
        let original = prepared(None, first, 0x61);
        let bindings = [
            ([0x99; 32], [0x12; 32], [0x13; 32], [0x14; 32], [0x15; 32]),
            ([0x11; 32], [0x99; 32], [0x13; 32], [0x14; 32], [0x15; 32]),
            ([0x11; 32], [0x12; 32], [0x99; 32], [0x14; 32], [0x15; 32]),
            ([0x11; 32], [0x12; 32], [0x13; 32], [0x99; 32], [0x15; 32]),
            ([0x11; 32], [0x12; 32], [0x13; 32], [0x14; 32], [0x99; 32]),
        ];
        for (wallet, activation, protection, cipher, operation) in bindings {
            let substituted = WalletMonotonicPreparedNextV2::new_v2(
                None, first, [0x61; 32], wallet, activation, protection, cipher, operation,
            )
            .unwrap();
            assert_ne!(
                original.prepared_identity_v2(),
                substituted.prepared_identity_v2()
            );
        }

        let changed_image = prepared(None, first, 0x62);
        assert_ne!(
            original.prepared_identity_v2(),
            changed_image.prepared_identity_v2()
        );
        let forked_genesis =
            WalletMonotonicCommitmentV2::new_v2(0, first.finalized_point(), [0u8; 32], [0x77; 32])
                .unwrap();
        let changed_state = prepared(None, forked_genesis, 0x61);
        assert_ne!(
            original.prepared_identity_v2(),
            changed_state.prepared_identity_v2()
        );
    }

    #[test]
    fn fault_backend_models_every_trusted_protocol_boundary() {
        let first = genesis();
        let reservation = prepared(None, first, 0x71);

        for point in [
            WalletMonotonicFaultPointV2::CurrentRead,
            WalletMonotonicFaultPointV2::PreparedRead,
        ] {
            let store = FaultInjectableWalletMonotonicStoreV2::new_v2();
            store.inject_once_v2(point).unwrap();
            let result = match point {
                WalletMonotonicFaultPointV2::CurrentRead => {
                    store.current_commitment_v2().map(|_| ())
                }
                WalletMonotonicFaultPointV2::PreparedRead => store.prepared_next_v2().map(|_| ()),
                _ => unreachable!(),
            };
            assert_eq!(result, Err(WalletMonotonicStoreErrorV2::BackendUnavailable));
        }

        for point in [
            WalletMonotonicFaultPointV2::BeforePrepare,
            WalletMonotonicFaultPointV2::AfterPrepare,
        ] {
            let service = FaultInjectableWalletMonotonicStoreV2::new_v2();
            let mut client = service.clone();
            service.inject_once_v2(point).unwrap();
            assert_eq!(
                client.compare_and_prepare_next_v2(reservation),
                Err(WalletMonotonicStoreErrorV2::BackendUnavailable)
            );
            let expected =
                (point == WalletMonotonicFaultPointV2::AfterPrepare).then_some(reservation);
            assert_eq!(service.prepared_next_v2(), Ok(expected));
            assert_eq!(service.current_commitment_v2(), Ok(None));
            assert!(client.compare_and_prepare_next_v2(reservation).is_ok());
        }

        for point in [
            WalletMonotonicFaultPointV2::BeforeCommit,
            WalletMonotonicFaultPointV2::AfterCommit,
        ] {
            let service = FaultInjectableWalletMonotonicStoreV2::new_v2();
            let mut client = service.clone();
            client.compare_and_prepare_next_v2(reservation).unwrap();
            service.inject_once_v2(point).unwrap();
            assert_eq!(
                client.compare_and_commit_prepared_v2(reservation),
                Err(WalletMonotonicStoreErrorV2::BackendUnavailable)
            );
            if point == WalletMonotonicFaultPointV2::AfterCommit {
                assert_eq!(service.current_commitment_v2(), Ok(Some(first)));
                assert_eq!(service.prepared_next_v2(), Ok(None));
            } else {
                assert_eq!(service.current_commitment_v2(), Ok(None));
                assert_eq!(service.prepared_next_v2(), Ok(Some(reservation)));
            }
            assert!(client.compare_and_commit_prepared_v2(reservation).is_ok());
            assert_eq!(service.current_commitment_v2(), Ok(Some(first)));
        }

        for point in [
            WalletMonotonicFaultPointV2::BeforeAbort,
            WalletMonotonicFaultPointV2::AfterAbort,
        ] {
            let service = FaultInjectableWalletMonotonicStoreV2::new_v2();
            let mut client = service.clone();
            client.compare_and_prepare_next_v2(reservation).unwrap();
            service.inject_once_v2(point).unwrap();
            assert_eq!(
                client.compare_and_abort_prepared_v2(reservation),
                Err(WalletMonotonicStoreErrorV2::BackendUnavailable)
            );
            let expected =
                (point == WalletMonotonicFaultPointV2::BeforeAbort).then_some(reservation);
            assert_eq!(service.prepared_next_v2(), Ok(expected));
            assert!(client.compare_and_abort_prepared_v2(reservation).is_ok());
            assert_eq!(service.prepared_next_v2(), Ok(None));
            assert_eq!(service.current_commitment_v2(), Ok(None));
        }
    }

    #[test]
    fn stale_current_response_is_one_shot_and_never_mutates_the_service() {
        let service = FaultInjectableWalletMonotonicStoreV2::new_v2();
        let mut client = service.clone();
        let first = genesis();
        let first_prepared = prepared(None, first, 0x81);
        client.compare_and_prepare_next_v2(first_prepared).unwrap();
        client
            .compare_and_commit_prepared_v2(first_prepared)
            .unwrap();
        let second = successor(first, 1, point(11, 2), 0x82);
        let second_prepared = prepared(Some(first), second, 0x83);
        client.compare_and_prepare_next_v2(second_prepared).unwrap();
        client
            .compare_and_commit_prepared_v2(second_prepared)
            .unwrap();

        service.inject_stale_current_once_v2(Some(first)).unwrap();
        assert_eq!(client.current_commitment_v2(), Ok(Some(first)));
        assert_eq!(client.current_commitment_v2(), Ok(Some(second)));
        assert_eq!(client.prepared_next_v2(), Ok(None));
    }
}
