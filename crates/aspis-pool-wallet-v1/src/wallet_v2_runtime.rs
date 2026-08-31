//! Permit-gated authoritative V2 wallet runtime.
//!
//! This is the only runtime facade which exposes scanner/finality mutations
//! after production activation. Startup reconstructs every prerequisite from
//! the live ASL2 image, ASMG/ASRT ownership receipt and monotonic service, then
//! compares a newly evaluated permit with the caller-supplied permit. It never
//! falls back to V1 after a requested V2 startup fails.

use crate::{
    durable_state::LocalSpendAuthenticatorV1,
    lane_forest_durable_v2::ForestFinalizedAppendEventV2,
    lane_forest_rpc_v2::{
        derive_finalized_pair_forest_terminal_intent_v2,
        derive_finalized_pair_forest_terminal_intent_with_carrier_notes_v2,
        FinalizedPairForestTerminalObservationV2, LaneForestRpcErrorV2,
    },
    lane_forest_wallet_txn_v2::{
        EmptyV1LaneForestWalletActivationV2, LaneForestWalletCheckpointBindingV2,
        LaneForestWalletCommittedStateV2, LaneForestWalletEmptyFinalizedBlockV2,
        LaneForestWalletNoteBindingV2, LaneForestWalletSpendBindingV2,
        LaneForestWalletTentativeCommitmentV2, LaneForestWalletTentativeUpdateV2,
        LaneForestWalletTxnCoordinatorV2, LaneForestWalletTxnErrorV2, LaneForestWalletTxnIntentV2,
        LaneForestWalletTxnPrepareV2, LaneForestWalletTxnRecoveryV2,
    },
    note_store_crypto::{LocalNullifierKeyStoreV1, NoteStoreCipherV1},
    relayer_execution_journal::DurableRelayerExecutionJournalV1,
    tx_v1_finalized_rpc_v2::{
        AgreedFinalizedTxV1BlockV2, AgreedFinalizedTxV1RootPageV2, FinalizedTxV1RpcErrorV2,
    },
    wallet_monotonic_v2::WalletMonotonicStoreV2,
    wallet_store_migration_v2::WalletStoreMigrationReceiptV2,
    wallet_v2_activation::{
        evaluate_wallet_v2_activation, permit_matches_mode_configuration_v2,
        WalletV2ActivationClass, WalletV2ActivationError, WalletV2ActivationMode,
        WalletV2ActivationPermit, WalletV2ActivationPrerequisites,
    },
};
use hpke::rand_core::CryptoRng;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WalletV2RuntimeError {
    MissingPermit,
    PermitMismatch,
    AmbiguousRuntimeMode,
    RuntimePolicyMismatch,
    Activation(WalletV2ActivationError),
    Transaction(LaneForestWalletTxnErrorV2),
    FinalizedSource(LaneForestRpcErrorV2),
    FinalizedTxV1Source(FinalizedTxV1RpcErrorV2),
}

impl From<LaneForestRpcErrorV2> for WalletV2RuntimeError {
    fn from(error: LaneForestRpcErrorV2) -> Self {
        Self::FinalizedSource(error)
    }
}

impl From<FinalizedTxV1RpcErrorV2> for WalletV2RuntimeError {
    fn from(error: FinalizedTxV1RpcErrorV2) -> Self {
        Self::FinalizedTxV1Source(error)
    }
}

impl From<WalletV2ActivationError> for WalletV2RuntimeError {
    fn from(error: WalletV2ActivationError) -> Self {
        Self::Activation(error)
    }
}

impl From<LaneForestWalletTxnErrorV2> for WalletV2RuntimeError {
    fn from(error: LaneForestWalletTxnErrorV2) -> Self {
        Self::Transaction(error)
    }
}

/// Runtime-observed provider/finality identities. These values are rechecked
/// against the activation permit on every startup and relevant scanner call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WalletV2RuntimePolicyBindings {
    startup_receipt_digest: [u8; 32],
    provider_set_digest: [u8; 32],
    finality_policy_digest: [u8; 32],
    reference_service_digest: Option<[u8; 32]>,
}

impl WalletV2RuntimePolicyBindings {
    pub fn production_v2(
        startup_receipt_digest: [u8; 32],
        provider_set_digest: [u8; 32],
        finality_policy_digest: [u8; 32],
    ) -> Result<Self, WalletV2RuntimeError> {
        Self::new_v2(
            startup_receipt_digest,
            provider_set_digest,
            finality_policy_digest,
            None,
        )
    }

    #[cfg(feature = "wallet-v2-reference-tests")]
    pub fn reference_only_v2(
        startup_receipt_digest: [u8; 32],
        provider_set_digest: [u8; 32],
        finality_policy_digest: [u8; 32],
        reference_service_digest: [u8; 32],
    ) -> Result<Self, WalletV2RuntimeError> {
        Self::new_v2(
            startup_receipt_digest,
            provider_set_digest,
            finality_policy_digest,
            Some(reference_service_digest),
        )
    }

    fn new_v2(
        startup_receipt_digest: [u8; 32],
        provider_set_digest: [u8; 32],
        finality_policy_digest: [u8; 32],
        reference_service_digest: Option<[u8; 32]>,
    ) -> Result<Self, WalletV2RuntimeError> {
        if [
            startup_receipt_digest,
            provider_set_digest,
            finality_policy_digest,
        ]
        .contains(&[0u8; 32])
            || reference_service_digest == Some([0u8; 32])
        {
            return Err(WalletV2RuntimeError::RuntimePolicyMismatch);
        }
        Ok(Self {
            startup_receipt_digest,
            provider_set_digest,
            finality_policy_digest,
            reference_service_digest,
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WalletV2FinalizedApply {
    pub prepare: LaneForestWalletTxnPrepareV2,
    pub recovery: LaneForestWalletTxnRecoveryV2,
}

/// Live authoritative runtime. The coordinator is intentionally private, so a
/// caller that selected V2 cannot bypass permit and provider checks through
/// this handle.
pub struct ActivatedWalletRuntimeV2 {
    coordinator: LaneForestWalletTxnCoordinatorV2,
    permit: WalletV2ActivationPermit,
    policy: WalletV2RuntimePolicyBindings,
}

impl core::fmt::Debug for ActivatedWalletRuntimeV2 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("ActivatedWalletRuntimeV2")
            .field("activation", &"[REDACTED]")
            .finish()
    }
}

impl ActivatedWalletRuntimeV2 {
    /// Open and recover ASL2, reconstruct the activation predicate from live
    /// state, and consume an exact permit. `None`, disabled mode, copied
    /// permits and stale provider bindings all fail without scanner mutation.
    #[allow(clippy::too_many_arguments)]
    pub fn start_v2(
        path: impl AsRef<std::path::Path>,
        activation: EmptyV1LaneForestWalletActivationV2,
        cipher: &NoteStoreCipherV1,
        protection_id: [u8; 32],
        monotonic_store: Box<dyn WalletMonotonicStoreV2>,
        ownership: WalletStoreMigrationReceiptV2,
        mode: &WalletV2ActivationMode,
        supplied_permit: Option<&WalletV2ActivationPermit>,
        policy: WalletV2RuntimePolicyBindings,
    ) -> Result<Self, WalletV2RuntimeError> {
        let supplied_permit = supplied_permit.ok_or(WalletV2RuntimeError::MissingPermit)?;
        let requested_migration = activation
            .migration_genesis()
            .ok_or(WalletV2RuntimeError::PermitMismatch)?;
        if !permit_matches_mode_configuration_v2(mode, supplied_permit)
            || supplied_permit.wallet_id_v2() != activation.wallet_identity_sha256()
            || supplied_permit.note_cipher_id_v2() != &cipher.cipher_id()
            || supplied_permit.migration_id_v2() != requested_migration.migration_id()
            || supplied_permit.ownership_id_v2() != ownership.migration_id()
            || supplied_permit.migration_target_digest_v2() != ownership.target_digest()
            || supplied_permit.migration_target_path_digest_v2() != ownership.target_path_digest()
            || supplied_permit.monotonic_protection_id_v2() != &protection_id
            || supplied_permit.qualified_startup_digest_v2() != &policy.startup_receipt_digest
            || supplied_permit.qualified_provider_digest_v2() != &policy.provider_set_digest
            || supplied_permit.qualified_finality_digest_v2() != &policy.finality_policy_digest
        {
            return Err(WalletV2RuntimeError::PermitMismatch);
        }
        let mut coordinator = LaneForestWalletTxnCoordinatorV2::open_or_create_protected_v2(
            path,
            activation,
            cipher,
            protection_id,
            monotonic_store,
        )?;
        coordinator.recover_to_committed_v2()?;
        let stored_activation = coordinator.activation_v2()?;
        let stored_migration = stored_activation
            .migration_genesis()
            .ok_or(WalletV2RuntimeError::PermitMismatch)?;
        if supplied_permit.wallet_id_v2() != stored_activation.wallet_identity_sha256()
            || supplied_permit.note_cipher_id_v2() != &cipher.cipher_id()
            || supplied_permit.migration_id_v2() != stored_migration.migration_id()
        {
            return Err(WalletV2RuntimeError::PermitMismatch);
        }
        let prerequisites = match mode {
            WalletV2ActivationMode::Disabled => {
                return Err(WalletV2ActivationError::Disabled.into())
            }
            WalletV2ActivationMode::Production(_) => {
                if policy.reference_service_digest.is_some() {
                    return Err(WalletV2RuntimeError::AmbiguousRuntimeMode);
                }
                WalletV2ActivationPrerequisites::from_authoritative_state_v2(
                    &coordinator,
                    ownership,
                    vec![policy.startup_receipt_digest],
                    vec![policy.provider_set_digest],
                    vec![policy.finality_policy_digest],
                )?
            }
            #[cfg(feature = "wallet-v2-reference-tests")]
            WalletV2ActivationMode::ReferenceOnly(_) => {
                let reference = policy
                    .reference_service_digest
                    .ok_or(WalletV2RuntimeError::AmbiguousRuntimeMode)?;
                WalletV2ActivationPrerequisites::from_authoritative_state_reference_only_v2(
                    &coordinator,
                    ownership,
                    reference,
                    vec![policy.startup_receipt_digest],
                    vec![policy.provider_set_digest],
                    vec![policy.finality_policy_digest],
                )?
            }
        };
        let fresh_permit = evaluate_wallet_v2_activation(mode, &prerequisites)?;
        if &fresh_permit != supplied_permit {
            return Err(WalletV2RuntimeError::PermitMismatch);
        }
        let expected_class = match mode {
            WalletV2ActivationMode::Disabled => unreachable!("disabled returned above"),
            WalletV2ActivationMode::Production(_) => WalletV2ActivationClass::Production,
            #[cfg(feature = "wallet-v2-reference-tests")]
            WalletV2ActivationMode::ReferenceOnly(_) => WalletV2ActivationClass::ReferenceOnly,
        };
        if fresh_permit.activation_class_v2() != expected_class
            || fresh_permit.wallet_id_v2() != coordinator.activation_v2()?.wallet_identity_sha256()
            || fresh_permit.note_cipher_id_v2() != &cipher.cipher_id()
            || fresh_permit.monotonic_protection_id_v2() != &protection_id
            || fresh_permit.qualified_startup_digest_v2() != &policy.startup_receipt_digest
            || fresh_permit.qualified_provider_digest_v2() != &policy.provider_set_digest
            || fresh_permit.qualified_finality_digest_v2() != &policy.finality_policy_digest
        {
            return Err(WalletV2RuntimeError::PermitMismatch);
        }
        Ok(Self {
            coordinator,
            permit: fresh_permit,
            policy,
        })
    }

    pub fn committed_state_v2(
        &self,
    ) -> Result<&LaneForestWalletCommittedStateV2, WalletV2RuntimeError> {
        Ok(self.coordinator.committed_state()?)
    }

    pub fn apply_finalized_event_v2<A: LocalSpendAuthenticatorV1>(
        &mut self,
        intent: LaneForestWalletTxnIntentV2,
        cipher: &NoteStoreCipherV1,
        authenticator: &A,
    ) -> Result<WalletV2FinalizedApply, WalletV2RuntimeError> {
        if intent.note_cipher_id() != self.permit.note_cipher_id_v2()
            || intent
                .finalized_relayer_observation()
                .is_some_and(|observation| {
                    observation.provider_set_digest() != &self.policy.provider_set_digest
                })
        {
            return Err(WalletV2RuntimeError::RuntimePolicyMismatch);
        }
        let prepare = self
            .coordinator
            .prepare_finalized_v2(intent, cipher, authenticator)?;
        let recovery = self.coordinator.recover_to_committed_v2()?;
        Ok(WalletV2FinalizedApply { prepare, recovery })
    }

    /// Consume one exact finalized-success ASRJ record and commit its Pool
    /// event, note/spend updates and relayer correlation through the same
    /// authoritative ASL2 transaction.
    ///
    /// This is the production handoff for relayed transactions. Unknown,
    /// pending, terminal-failure, finalized-failure, wrong-signature,
    /// wrong-point and wrong-provider records fail before an ASL2 mutation.
    /// A crash after ASL2 preparation is recovered by normal runtime startup;
    /// retrying the same immutable ASRJ record is idempotent.
    pub fn apply_finalized_journal_event_v2<A: LocalSpendAuthenticatorV1>(
        &mut self,
        intent: LaneForestWalletTxnIntentV2,
        journal: &DurableRelayerExecutionJournalV1,
        request_id: [u8; 32],
        cipher: &NoteStoreCipherV1,
        authenticator: &A,
    ) -> Result<WalletV2FinalizedApply, WalletV2RuntimeError> {
        let intent = intent.bind_finalized_relayer_journal_v2(journal, request_id)?;
        self.apply_finalized_event_v2(intent, cipher, authenticator)
    }

    /// Compatibility/reference Pool V2 scanner-to-wallet handoff. It derives
    /// the event from an already authenticated observation, but its caller
    /// supplies note bindings. Production finalized TxV1 ingestion must use
    /// `apply_agreed_finalized_tx_v1_terminal_journal_v2`, which derives notes
    /// only from the signed and quorum-agreed carrier.
    #[allow(clippy::too_many_arguments)]
    pub fn apply_finalized_pool_terminal_journal_v2<A: LocalSpendAuthenticatorV1>(
        &mut self,
        observation: &FinalizedPairForestTerminalObservationV2,
        notes: Vec<LaneForestWalletNoteBindingV2>,
        spends: Vec<LaneForestWalletSpendBindingV2>,
        checkpoint: Option<LaneForestWalletCheckpointBindingV2>,
        journal: &DurableRelayerExecutionJournalV1,
        request_id: [u8; 32],
        cipher: &NoteStoreCipherV1,
        authenticator: &A,
    ) -> Result<WalletV2FinalizedApply, WalletV2RuntimeError> {
        let intent = derive_finalized_pair_forest_terminal_intent_v2(
            self.committed_state_v2()?,
            observation,
            notes,
            spends,
            checkpoint,
        )?;
        self.apply_finalized_journal_event_v2(intent, journal, request_id, cipher, authenticator)
    }

    /// Production-owned RPC path. Only a constructor-sealed, two-provider
    /// finalized TxV1 block plus its independently agreed exact root-history
    /// entry can enter the ASQ8/ASR8-derived terminal path. Exact transaction-array
    /// order is committed into ASL2 and survives restart; signature ordering
    /// is never used as a ledger-order surrogate.
    #[allow(clippy::too_many_arguments)]
    pub fn apply_agreed_finalized_tx_v1_terminal_journal_v2<
        A: LocalSpendAuthenticatorV1,
        K: LocalNullifierKeyStoreV1,
        R: CryptoRng,
    >(
        &mut self,
        block: &AgreedFinalizedTxV1BlockV2,
        terminal_index: usize,
        root_page: &AgreedFinalizedTxV1RootPageV2,
        rng: &mut R,
        viewing_secret: &crate::ViewingSecretKeyV1,
        local_keys: &K,
        spends: Vec<LaneForestWalletSpendBindingV2>,
        checkpoint: Option<LaneForestWalletCheckpointBindingV2>,
        journal: &DurableRelayerExecutionJournalV1,
        request_id: [u8; 32],
        cipher: &NoteStoreCipherV1,
        authenticator: &A,
    ) -> Result<WalletV2FinalizedApply, WalletV2RuntimeError> {
        if block.provider_set_digest_v2() != &self.policy.provider_set_digest
            || block.startup_receipt_digest_v2() != &self.policy.startup_receipt_digest
        {
            return Err(WalletV2RuntimeError::RuntimePolicyMismatch);
        }
        let point = block.block_v2().point();
        let previous_transaction_index = if self.committed_state_v2()?.finalized_head() == point {
            let (previous_point, previous_position) = self
                .coordinator
                .last_finalized_ledger_position_v2()?
                .ok_or(FinalizedTxV1RpcErrorV2::TerminalOrder)?;
            if previous_point != point {
                return Err(FinalizedTxV1RpcErrorV2::TerminalOrder.into());
            }
            Some(previous_position.transaction_index_v2())
        } else {
            None
        };
        block.validate_terminal_progress_v2(terminal_index, previous_transaction_index)?;
        let observation = block.terminal_observation_v2(terminal_index, root_page)?;
        let intent = derive_finalized_pair_forest_terminal_intent_with_carrier_notes_v2(
            rng,
            self.committed_state_v2()?,
            &observation,
            viewing_secret,
            local_keys,
            cipher,
            spends,
            checkpoint,
        )?;
        self.apply_finalized_journal_event_v2(intent, journal, request_id, cipher, authenticator)
    }

    pub fn apply_empty_finalized_block_v2(
        &mut self,
        empty: LaneForestWalletEmptyFinalizedBlockV2,
    ) -> Result<WalletV2FinalizedApply, WalletV2RuntimeError> {
        if empty.startup_receipt_sha256() != &self.policy.startup_receipt_digest
            || empty.provider_set_sha256() != &self.policy.provider_set_digest
        {
            return Err(WalletV2RuntimeError::RuntimePolicyMismatch);
        }
        let prepare = self.coordinator.prepare_empty_finalized_block_v2(empty)?;
        let recovery = self.coordinator.recover_to_committed_v2()?;
        Ok(WalletV2FinalizedApply { prepare, recovery })
    }

    pub fn observe_tentative_v2(
        &mut self,
        event: ForestFinalizedAppendEventV2,
        commitment: LaneForestWalletTentativeCommitmentV2,
        provider_set_digest: [u8; 32],
    ) -> Result<LaneForestWalletTentativeUpdateV2, WalletV2RuntimeError> {
        if provider_set_digest != self.policy.provider_set_digest {
            return Err(WalletV2RuntimeError::RuntimePolicyMismatch);
        }
        Ok(self
            .coordinator
            .observe_tentative_v2(event, commitment, provider_set_digest)?)
    }

    pub fn reorg_tentative_v2(
        &mut self,
        event: &ForestFinalizedAppendEventV2,
        reorg_evidence_sha256: [u8; 32],
        provider_set_digest: [u8; 32],
    ) -> Result<LaneForestWalletTentativeUpdateV2, WalletV2RuntimeError> {
        if provider_set_digest != self.policy.provider_set_digest {
            return Err(WalletV2RuntimeError::RuntimePolicyMismatch);
        }
        Ok(self.coordinator.reorg_tentative_v2(
            event,
            reorg_evidence_sha256,
            provider_set_digest,
        )?)
    }

    pub fn recover_v2(&mut self) -> Result<LaneForestWalletTxnRecoveryV2, WalletV2RuntimeError> {
        Ok(self.coordinator.recover_to_committed_v2()?)
    }

    /// Clean shutdown completes any ASL2 phase and requires exact agreement
    /// with the external commitment before releasing the process lock.
    pub fn shutdown_v2(mut self) -> Result<(), WalletV2RuntimeError> {
        self.coordinator.recover_to_committed_v2()?;
        self.coordinator
            .externally_anchored_monotonic_commitment_v2()?;
        Ok(())
    }
}
