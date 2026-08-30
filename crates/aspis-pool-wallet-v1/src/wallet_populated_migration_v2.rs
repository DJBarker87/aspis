//! Read-only validation and canonical capture of a populated V1 -> ASL2
//! migration source set.
//!
//! This module does not make an authority decision or write any target. Every
//! supplied durable handle already owns its per-file lock. The ownership
//! journal consumes the validated snapshot only after all checks below have
//! succeeded, so malformed or mutually inconsistent legacy stores cannot
//! cause partial target mutation.

use std::{
    collections::{HashMap, HashSet},
    io,
    path::{Path, PathBuf},
};

use aspis_statement::{decode_digest_canonical, encode_digest_canonical};
use sha2::{Digest as _, Sha256};

use crate::{
    durable_state::{
        DurableRelayerStateV1, DurableStateErrorV1, DurableWalletStateV1,
        LocalSpendAuthenticatorV1, SealedNoteAccessV1, StoredSealedNoteV1,
    },
    durable_witness_state::{DurableWalletWitnessStateV1, DurableWitnessErrorV1},
    lane_forest_durable_v2::{
        encode_lane_forest_durable_state_v2, DurableLaneForestWalletFileV2,
        ForestFinalizedAppendKindV2, LaneForestDurableErrorV2, LaneForestDurableStateV2,
    },
    lane_forest_wallet_txn_v2::LaneForestWalletActivationPolicyV2,
    lane_forest_wallet_txn_v2::{
        prepare_protected_initial_image_v2, reconcile_protected_image_monotonic_v2,
        validated_protected_activation_from_image_v2, EmptyV1LaneForestWalletActivationV2,
        LaneForestWalletTxnErrorV2,
    },
    note_store_crypto::{open_note_opening_v1, NoteStoreCipherV1, POOL_V1_NOTE_STORE_HEADER_BYTES},
    recompute_note_commitment_v1,
    relayer_execution_journal::{
        validate_relayer_execution_archive_v1, DurableRelayerExecutionJournalV1,
        RelayerExecutionJournalErrorV1,
    },
    scan_state::{DepositScanIdentityV1, FinalizedChainPointV1},
    wallet_monotonic_v2::WalletMonotonicStoreV2,
    wallet_store_migration_v2::{
        wallet_store_migration_authority_path_v2, DurableWalletStoreMigrationJournalV2,
        WalletStoreMigrationErrorV2, WalletStoreMigrationFaultInjectorV2,
        WalletStoreMigrationPhaseV2, WalletStoreMigrationPlanV2, WalletStoreMigrationReceiptV2,
        WalletStoreSourceDescriptorV2, WalletStoreSourceRoleV2,
    },
};

const POPULATED_MIGRATION_DOMAIN_V2: &[u8] = b"aspis:pool-v1:wallet-populated-migration:sha256:v2";
const SOURCE_MANIFEST_DOMAIN_V2: &[u8] =
    b"aspis:pool-v1:wallet-migration-source-manifest:sha256:v2";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum WalletMigrationSourceRoleV2 {
    Wallet = 1,
    Witness = 2,
    LaneForest = 3,
    RelayerAdmission = 4,
    RelayerExecution = 5,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WalletMigrationSourceDescriptorV2 {
    role: WalletMigrationSourceRoleV2,
    magic: [u8; 4],
    version: u8,
    length: u64,
    image_sha256: [u8; 32],
}

impl WalletMigrationSourceDescriptorV2 {
    fn from_image_v2(
        role: WalletMigrationSourceRoleV2,
        bytes: &[u8],
    ) -> Result<Self, PopulatedWalletMigrationErrorV2> {
        if bytes.len() < 5 {
            return Err(PopulatedWalletMigrationErrorV2::MalformedSource);
        }
        Ok(Self {
            role,
            magic: bytes[..4]
                .try_into()
                .map_err(|_| PopulatedWalletMigrationErrorV2::MalformedSource)?,
            version: bytes[4],
            length: u64::try_from(bytes.len())
                .map_err(|_| PopulatedWalletMigrationErrorV2::CountOverflow)?,
            image_sha256: Sha256::digest(bytes).into(),
        })
    }

    pub fn role(&self) -> WalletMigrationSourceRoleV2 {
        self.role
    }

    pub fn magic(&self) -> &[u8; 4] {
        &self.magic
    }

    pub fn version(&self) -> u8 {
        self.version
    }

    pub fn length(&self) -> u64 {
        self.length
    }

    pub fn image_sha256(&self) -> &[u8; 32] {
        &self.image_sha256
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PopulatedWalletMigrationErrorV2 {
    Durable(DurableStateErrorV1),
    Witness(DurableWitnessErrorV1),
    Lane(LaneForestDurableErrorV2),
    Relayer(RelayerExecutionJournalErrorV1),
    Io(io::ErrorKind),
    PathMismatch,
    PathAlias,
    MalformedSource,
    SourceConflict,
    IdentityMismatch,
    CursorMismatch,
    WitnessMismatch,
    UnsupportedHistory,
    PreparedPlanHistory,
    RelayerAdmissionNotEmpty,
    RelayerExecutionNotQuiescent,
    NoteCipherMismatch,
    InvalidNote,
    MissingLaneWitness,
    DuplicateNote,
    DuplicateNonce,
    InvalidSpend,
    CountOverflow,
    Transaction(LaneForestWalletTxnErrorV2),
    Handoff(WalletStoreMigrationErrorV2),
}

impl From<DurableStateErrorV1> for PopulatedWalletMigrationErrorV2 {
    fn from(error: DurableStateErrorV1) -> Self {
        Self::Durable(error)
    }
}

impl From<DurableWitnessErrorV1> for PopulatedWalletMigrationErrorV2 {
    fn from(error: DurableWitnessErrorV1) -> Self {
        Self::Witness(error)
    }
}

impl From<LaneForestDurableErrorV2> for PopulatedWalletMigrationErrorV2 {
    fn from(error: LaneForestDurableErrorV2) -> Self {
        Self::Lane(error)
    }
}

impl From<RelayerExecutionJournalErrorV1> for PopulatedWalletMigrationErrorV2 {
    fn from(error: RelayerExecutionJournalErrorV1) -> Self {
        Self::Relayer(error)
    }
}

impl From<io::Error> for PopulatedWalletMigrationErrorV2 {
    fn from(error: io::Error) -> Self {
        Self::Io(error.kind())
    }
}

impl From<LaneForestWalletTxnErrorV2> for PopulatedWalletMigrationErrorV2 {
    fn from(error: LaneForestWalletTxnErrorV2) -> Self {
        Self::Transaction(error)
    }
}

impl From<WalletStoreMigrationErrorV2> for PopulatedWalletMigrationErrorV2 {
    fn from(error: WalletStoreMigrationErrorV2) -> Self {
        Self::Handoff(error)
    }
}

/// Complete, prevalidated migration genesis. Private fields prevent callers
/// from fabricating a note/lane/source association after validation.
#[derive(Clone, PartialEq, Eq)]
pub struct PopulatedWalletMigrationV2 {
    migration_id: [u8; 32],
    source_manifest_sha256: [u8; 32],
    source_descriptors: [WalletMigrationSourceDescriptorV2; 5],
    wallet_identity_sha256: [u8; 32],
    note_cipher_id: [u8; 32],
    finalized_head: FinalizedChainPointV1,
    notes: Vec<StoredSealedNoteV1>,
    lane_state: LaneForestDurableStateV2,
    relayer_execution_archive: Vec<u8>,
    source_images: [Vec<u8>; 5],
    source_paths: [PathBuf; 5],
}

/// Five simultaneously locked legacy stores. Holding this value proves that a
/// migration can validate every source before ASMG `Prepared` fences future
/// legacy constructors. The value is consumed by the one-way handoff.
pub struct LockedLegacyWalletStoresV2 {
    pub wallet: DurableWalletStateV1,
    pub witness: DurableWalletWitnessStateV1,
    pub lane_forest: DurableLaneForestWalletFileV2,
    pub relayer_admission: DurableRelayerStateV1,
    pub relayer_execution: DurableRelayerExecutionJournalV1,
}

impl core::fmt::Debug for LockedLegacyWalletStoresV2 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("LockedLegacyWalletStoresV2")
            .field("source_count", &5)
            .field("private_store_state", &"[REDACTED]")
            .finish()
    }
}

pub type WalletLegacySourcePathsV2 = [(WalletStoreSourceRoleV2, PathBuf); 5];

impl core::fmt::Debug for PopulatedWalletMigrationV2 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("PopulatedWalletMigrationV2")
            .field("finalized_head", &self.finalized_head)
            .field("note_count", &self.notes.len())
            .field("source_count", &self.source_descriptors.len())
            .field("private_state_and_digests", &"[REDACTED]")
            .finish()
    }
}

impl PopulatedWalletMigrationV2 {
    #[allow(clippy::too_many_arguments)]
    pub fn from_locked_v1<A: LocalSpendAuthenticatorV1>(
        wallet: &DurableWalletStateV1,
        witness: &DurableWalletWitnessStateV1,
        relayer_admission: &DurableRelayerStateV1,
        relayer_execution: &DurableRelayerExecutionJournalV1,
        lane_file: &DurableLaneForestWalletFileV2,
        cipher: &NoteStoreCipherV1,
        spend_authenticator: &A,
        activation_policy: &impl LaneForestWalletActivationPolicyV2,
    ) -> Result<Self, PopulatedWalletMigrationErrorV2> {
        let source_paths = validate_paths_v2(&[
            wallet.migration_source_path_v1(),
            witness.migration_source_path_v1(),
            lane_file.migration_source_path_v2(),
            relayer_admission.migration_source_path_v1(),
            relayer_execution.migration_source_path_v1(),
        ])?;

        let wallet_image = wallet.migration_source_image_v1()?;
        let witness_image = witness.migration_source_image_v1()?;
        let lane_image = lane_file.migration_source_image_v2()?;
        let relayer_admission_image = relayer_admission.migration_source_image_v1()?;
        let relayer_execution_image = relayer_execution.migration_source_image_v1()?;
        validate_relayer_execution_archive_v1(&relayer_execution_image)?;
        let source_descriptors = [
            WalletMigrationSourceDescriptorV2::from_image_v2(
                WalletMigrationSourceRoleV2::Wallet,
                &wallet_image,
            )?,
            WalletMigrationSourceDescriptorV2::from_image_v2(
                WalletMigrationSourceRoleV2::Witness,
                &witness_image,
            )?,
            WalletMigrationSourceDescriptorV2::from_image_v2(
                WalletMigrationSourceRoleV2::LaneForest,
                &lane_image,
            )?,
            WalletMigrationSourceDescriptorV2::from_image_v2(
                WalletMigrationSourceRoleV2::RelayerAdmission,
                &relayer_admission_image,
            )?,
            WalletMigrationSourceDescriptorV2::from_image_v2(
                WalletMigrationSourceRoleV2::RelayerExecution,
                &relayer_execution_image,
            )?,
        ];
        validate_source_magics_v2(&source_descriptors)?;

        if wallet.has_prepared_plan_history_v1() {
            return Err(PopulatedWalletMigrationErrorV2::PreparedPlanHistory);
        }
        if !relayer_admission.entries().is_empty() || relayer_admission.rate_window() != (0, 0) {
            return Err(PopulatedWalletMigrationErrorV2::RelayerAdmissionNotEmpty);
        }
        // ASL2 preserves the exact ASRJ image as a forensic archive, but does
        // not yet continue a signed/submitted legacy request. Retiring ASRJ
        // with an unsettled record would strand authority, so migration is
        // deliberately limited to a quiescent execution journal.
        if relayer_execution
            .records()
            .iter()
            .any(|record| record.outcome.is_none())
        {
            return Err(PopulatedWalletMigrationErrorV2::RelayerExecutionNotQuiescent);
        }
        if cipher.cipher_id() != *wallet.note_cipher_id() {
            return Err(PopulatedWalletMigrationErrorV2::NoteCipherMismatch);
        }

        validate_scan_witness_v2(wallet, witness)?;
        let lane_state = lane_file.state();
        lane_state.validate_migration_tracking_v2()?;
        let finalized_head = lane_state
            .finalized_head_v2()
            .ok_or(PopulatedWalletMigrationErrorV2::CursorMismatch)?;
        if finalized_head != wallet.scan_state().head() {
            return Err(PopulatedWalletMigrationErrorV2::CursorMismatch);
        }
        for event in lane_state.migration_events_v2() {
            if !wallet.scan_state().retains_chain_point_v1(event.point()) {
                return Err(PopulatedWalletMigrationErrorV2::UnsupportedHistory);
            }
        }
        for point in lane_state.migration_checkpoint_points_v2() {
            if !wallet.scan_state().retains_chain_point_v1(point) {
                return Err(PopulatedWalletMigrationErrorV2::UnsupportedHistory);
            }
        }
        validate_scan_lane_history_v2(wallet, lane_state)?;

        let identity = wallet.scan_state().identity();
        let lane_identity = lane_state.master().value.identity;
        if *identity.asset_mint() != lane_identity.asset_mint
            || *identity.deployment_domain() != lane_identity.deployment_domain
            || identity.asset_id() != lane_identity.asset_id.0
            || !activation_policy.approves_topology_transition_v2(
                identity.pool(),
                identity.vault_token_account(),
                &lane_state.master().address,
                &lane_identity.pool,
                &lane_identity.token_program,
            )
        {
            return Err(PopulatedWalletMigrationErrorV2::IdentityMismatch);
        }

        validate_notes_v2(wallet, witness, lane_state, cipher, spend_authenticator)?;
        let mut notes = wallet.notes().to_vec();
        notes.sort_by_key(|note| encode_event_id_v2(note.event_id));
        let wallet_identity_sha256 = wallet_identity_sha256_v2(identity);
        let source_manifest_sha256 = source_manifest_sha256_v2(&source_descriptors);
        let lane_state_image = encode_lane_forest_durable_state_v2(lane_state)?;
        let migration_id = migration_id_v2(
            wallet_identity_sha256,
            *wallet.note_cipher_id(),
            finalized_head,
            source_manifest_sha256,
            &lane_state_image,
            &notes,
            &relayer_execution_image,
        );
        Ok(Self {
            migration_id,
            source_manifest_sha256,
            source_descriptors,
            wallet_identity_sha256,
            note_cipher_id: *wallet.note_cipher_id(),
            finalized_head,
            notes,
            lane_state: lane_state.clone(),
            relayer_execution_archive: relayer_execution_image.clone(),
            source_images: [
                wallet_image,
                witness_image,
                lane_image,
                relayer_admission_image,
                relayer_execution_image,
            ],
            source_paths,
        })
    }

    pub fn migration_id(&self) -> &[u8; 32] {
        &self.migration_id
    }

    pub fn source_manifest_sha256(&self) -> &[u8; 32] {
        &self.source_manifest_sha256
    }

    pub fn source_descriptors(&self) -> &[WalletMigrationSourceDescriptorV2; 5] {
        &self.source_descriptors
    }

    pub fn wallet_identity_sha256(&self) -> &[u8; 32] {
        &self.wallet_identity_sha256
    }

    pub fn note_cipher_id(&self) -> &[u8; 32] {
        &self.note_cipher_id
    }

    pub fn finalized_head(&self) -> FinalizedChainPointV1 {
        self.finalized_head
    }

    pub fn notes(&self) -> &[StoredSealedNoteV1] {
        &self.notes
    }

    pub fn lane_state(&self) -> &LaneForestDurableStateV2 {
        &self.lane_state
    }

    pub fn relayer_execution_archive(&self) -> &[u8] {
        &self.relayer_execution_archive
    }

    pub fn legacy_source_paths_v2(&self) -> WalletLegacySourcePathsV2 {
        source_path_pairs_v2(&self.source_paths)
    }

    fn handoff_plan_v2(
        &self,
        target_path: &Path,
        target_bytes: Vec<u8>,
    ) -> Result<WalletStoreMigrationPlanV2, PopulatedWalletMigrationErrorV2> {
        let mut sources = Vec::with_capacity(self.source_images.len());
        for ((role, path), bytes) in source_path_pairs_v2(&self.source_paths)
            .into_iter()
            .zip(&self.source_images)
        {
            sources.push(WalletStoreSourceDescriptorV2::from_exact_path_and_bytes_v2(
                role, path, bytes,
            )?);
        }
        Ok(WalletStoreMigrationPlanV2::new_v2(
            sources,
            target_path,
            target_bytes,
        )?)
    }
}

/// Validate all populated legacy stores while their locks are held, durably
/// prepare ASMG, install and externally anchor the protected ASL2 genesis,
/// commit ownership, then replace every legacy source with a bound ASRT
/// tombstone. An injected interruption poisons the current phase handle; the
/// caller must drop it and use [`recover_populated_wallet_handoff_v2`].
#[allow(clippy::too_many_arguments)]
pub fn migrate_locked_legacy_wallet_to_asl2_v2<
    A: LocalSpendAuthenticatorV1,
    F: WalletStoreMigrationFaultInjectorV2,
>(
    stores: LockedLegacyWalletStoresV2,
    target_path: impl AsRef<Path>,
    cipher: &NoteStoreCipherV1,
    spend_authenticator: &A,
    activation_policy: &impl LaneForestWalletActivationPolicyV2,
    protection_id: [u8; 32],
    monotonic_store: &mut dyn WalletMonotonicStoreV2,
    faults: &mut F,
) -> Result<WalletStoreMigrationReceiptV2, PopulatedWalletMigrationErrorV2> {
    let migration = PopulatedWalletMigrationV2::from_locked_v1(
        &stores.wallet,
        &stores.witness,
        &stores.relayer_admission,
        &stores.relayer_execution,
        &stores.lane_forest,
        cipher,
        spend_authenticator,
        activation_policy,
    )?;
    let activation = EmptyV1LaneForestWalletActivationV2::from_populated_migration_v2(&migration)?;
    let target_bytes = prepare_protected_initial_image_v2(&activation, cipher, protection_id)?;
    let source_paths = migration.legacy_source_paths_v2();
    let plan = migration.handoff_plan_v2(target_path.as_ref(), target_bytes)?;
    let authority_path = wallet_store_migration_authority_path_v2(&source_paths[0].1)?;

    // This is the logical cutover. All five source locks are still held while
    // ASMG Prepared becomes durable, closing the scanner/migration race.
    let (journal, _) = DurableWalletStoreMigrationJournalV2::open_or_prepare_with_faults_v2(
        authority_path,
        plan,
        faults,
    )?;
    drop(stores);
    drop(migration);
    resume_populated_wallet_handoff_v2(
        journal,
        target_path.as_ref(),
        &source_paths,
        cipher,
        Some(&activation),
        protection_id,
        monotonic_store,
        faults,
    )
}

/// Deterministically roll a durable ASMG `Prepared` or later phase forward.
/// The canonical protected activation is recovered from the journal's exact
/// target bytes, because legacy constructors are correctly unavailable after
/// `Prepared`. Repeating this function is an exact idempotent recovery.
#[allow(clippy::too_many_arguments)]
pub fn recover_populated_wallet_handoff_v2<F: WalletStoreMigrationFaultInjectorV2>(
    authority_path: impl AsRef<Path>,
    target_path: impl AsRef<Path>,
    source_paths: &WalletLegacySourcePathsV2,
    cipher: &NoteStoreCipherV1,
    protection_id: [u8; 32],
    monotonic_store: &mut dyn WalletMonotonicStoreV2,
    faults: &mut F,
) -> Result<WalletStoreMigrationReceiptV2, PopulatedWalletMigrationErrorV2> {
    let journal = DurableWalletStoreMigrationJournalV2::open_existing_v2(authority_path)?;
    resume_populated_wallet_handoff_v2(
        journal,
        target_path.as_ref(),
        source_paths,
        cipher,
        None,
        protection_id,
        monotonic_store,
        faults,
    )
}

#[allow(clippy::too_many_arguments)]
fn resume_populated_wallet_handoff_v2<F: WalletStoreMigrationFaultInjectorV2>(
    mut journal: DurableWalletStoreMigrationJournalV2,
    target_path: &Path,
    source_paths: &WalletLegacySourcePathsV2,
    cipher: &NoteStoreCipherV1,
    expected_activation: Option<&EmptyV1LaneForestWalletActivationV2>,
    protection_id: [u8; 32],
    monotonic_store: &mut dyn WalletMonotonicStoreV2,
    faults: &mut F,
) -> Result<WalletStoreMigrationReceiptV2, PopulatedWalletMigrationErrorV2> {
    let phase = journal.state_v2()?.phase();
    if phase == WalletStoreMigrationPhaseV2::LegacyRetired {
        let current_target = journal.read_bound_target_v2(target_path)?;
        let activation = validated_protected_activation_from_image_v2(&current_target, cipher)?;
        validate_expected_activation_v2(expected_activation, &activation)?;
        reconcile_protected_image_monotonic_v2(
            &current_target,
            &activation,
            cipher,
            protection_id,
            monotonic_store,
        )?;
        journal.verify_completed_legacy_retirement_v2(source_paths)?;
        return Ok(journal.receipt_v2()?);
    }

    if phase < WalletStoreMigrationPhaseV2::OwnershipCommitted {
        journal.install_target_with_faults_v2(target_path, faults)?;
    }
    let prepared_target = journal.target_bytes_v2()?.to_vec();
    let activation = validated_protected_activation_from_image_v2(&prepared_target, cipher)?;
    validate_expected_activation_v2(expected_activation, &activation)?;
    reconcile_protected_image_monotonic_v2(
        &prepared_target,
        &activation,
        cipher,
        protection_id,
        monotonic_store,
    )?;
    journal.commit_ownership_and_retire_with_target_guard_v2(target_path, source_paths, faults)?;
    Ok(journal.receipt_v2()?)
}

fn validate_expected_activation_v2(
    expected: Option<&EmptyV1LaneForestWalletActivationV2>,
    actual: &EmptyV1LaneForestWalletActivationV2,
) -> Result<(), PopulatedWalletMigrationErrorV2> {
    if expected.is_some_and(|expected| expected.activation_id() != actual.activation_id()) {
        return Err(PopulatedWalletMigrationErrorV2::Transaction(
            LaneForestWalletTxnErrorV2::ActivationMismatch,
        ));
    }
    Ok(())
}

fn source_path_pairs_v2(paths: &[PathBuf; 5]) -> WalletLegacySourcePathsV2 {
    [
        (WalletStoreSourceRoleV2::WalletState, paths[0].clone()),
        (WalletStoreSourceRoleV2::WitnessState, paths[1].clone()),
        (WalletStoreSourceRoleV2::LaneForestState, paths[2].clone()),
        (
            WalletStoreSourceRoleV2::RelayerAdmissionState,
            paths[3].clone(),
        ),
        (
            WalletStoreSourceRoleV2::RelayerExecutionJournal,
            paths[4].clone(),
        ),
    ]
}

fn validate_source_magics_v2(
    sources: &[WalletMigrationSourceDescriptorV2; 5],
) -> Result<(), PopulatedWalletMigrationErrorV2> {
    const EXPECTED: [[u8; 4]; 5] = [*b"ASDW", *b"ASWJ", *b"ASD8", *b"ASRQ", *b"ASRJ"];
    if sources
        .iter()
        .zip(EXPECTED)
        .any(|(source, expected)| source.magic != expected || source.version == 0)
    {
        return Err(PopulatedWalletMigrationErrorV2::MalformedSource);
    }
    Ok(())
}

fn validate_scan_witness_v2(
    wallet: &DurableWalletStateV1,
    witness: &DurableWalletWitnessStateV1,
) -> Result<(), PopulatedWalletMigrationErrorV2> {
    if witness.anchor_point() != wallet.scan_state().anchor()
        || witness.current_state().tree().next_leaf_index != wallet.scan_state().next_leaf_index()
        || encode_digest_canonical(&witness.current_state().tree().root)
            != *wallet.scan_state().root()
    {
        return Err(PopulatedWalletMigrationErrorV2::WitnessMismatch);
    }
    let scan_blocks = wallet.scan_state().migration_blocks_v1();
    let witness_blocks = witness.migration_blocks_v1();
    if scan_blocks.len() != witness_blocks.len() {
        return Err(PopulatedWalletMigrationErrorV2::WitnessMismatch);
    }
    for (scan, witness) in scan_blocks.iter().zip(witness_blocks) {
        if scan.block.point() != witness.point
            || scan.block.parent() != witness.parent
            || scan.events.len() != witness.appends.len()
        {
            return Err(PopulatedWalletMigrationErrorV2::WitnessMismatch);
        }
        for (scan_event, append) in scan.events.iter().zip(&witness.appends) {
            if scan_event.event_id != append.event_id
                || scan_event.leaf_index != append.leaf_index
                || append.root_sequence != append.leaf_index.saturating_add(1)
                || scan_event.note_commitment != append.note_commitment
                || scan_event.root != append.root
            {
                return Err(PopulatedWalletMigrationErrorV2::WitnessMismatch);
            }
        }
        let append_ids = witness
            .appends
            .iter()
            .map(|append| append.event_id)
            .collect::<HashSet<_>>();
        if witness
            .tracked
            .iter()
            .any(|event| !append_ids.contains(event))
        {
            return Err(PopulatedWalletMigrationErrorV2::WitnessMismatch);
        }
    }
    Ok(())
}

/// Require the public append history retained by ASDW/ASWJ to be exactly the
/// output history retained by ASD8. Merely sharing chain points is
/// insufficient: a partial or spliced store could otherwise migrate a note
/// and a forest witness from different canonical events at the same slot.
fn validate_scan_lane_history_v2(
    wallet: &DurableWalletStateV1,
    lane_state: &LaneForestDurableStateV2,
) -> Result<(), PopulatedWalletMigrationErrorV2> {
    let mut scan_outputs = HashMap::new();
    for block in wallet.scan_state().migration_blocks_v1() {
        for event in block.events {
            if scan_outputs
                .insert(event.event_id, event.note_commitment)
                .is_some()
            {
                return Err(PopulatedWalletMigrationErrorV2::SourceConflict);
            }
        }
    }

    let mut lane_outputs = HashMap::new();
    for event in lane_state.migration_events_v2() {
        let outputs = match &event.kind {
            ForestFinalizedAppendKindV2::Deposit {
                event_id,
                commitment,
                ..
            } => vec![(*event_id, *commitment)],
            ForestFinalizedAppendKindV2::PrivateTransfer {
                recipient_event_id,
                change_event_id,
                recipient_commitment,
                change_commitment,
                ..
            } => vec![
                (*recipient_event_id, *recipient_commitment),
                (*change_event_id, *change_commitment),
            ],
            ForestFinalizedAppendKindV2::Withdrawal {
                event_id,
                change_commitment,
                ..
            } => vec![(*event_id, *change_commitment)],
        };
        for (event_id, commitment) in outputs {
            if lane_outputs.insert(event_id, commitment).is_some() {
                return Err(PopulatedWalletMigrationErrorV2::SourceConflict);
            }
        }
    }
    if scan_outputs != lane_outputs {
        return Err(PopulatedWalletMigrationErrorV2::UnsupportedHistory);
    }
    Ok(())
}

fn validate_notes_v2<A: LocalSpendAuthenticatorV1>(
    wallet: &DurableWalletStateV1,
    witness: &DurableWalletWitnessStateV1,
    lane_state: &LaneForestDurableStateV2,
    cipher: &NoteStoreCipherV1,
    spend_authenticator: &A,
) -> Result<(), PopulatedWalletMigrationErrorV2> {
    let mut note_ids = HashSet::new();
    let mut nonces = HashSet::new();
    let mut nullifiers = HashSet::new();
    for note in wallet.notes() {
        if !note_ids.insert(note.event_id)
            || note.sealed_note.len() < POOL_V1_NOTE_STORE_HEADER_BYTES
        {
            return Err(PopulatedWalletMigrationErrorV2::DuplicateNote);
        }
        let nonce: [u8; 24] = note.sealed_note[8..POOL_V1_NOTE_STORE_HEADER_BYTES]
            .try_into()
            .map_err(|_| PopulatedWalletMigrationErrorV2::InvalidNote)?;
        if !nonces.insert(nonce) {
            return Err(PopulatedWalletMigrationErrorV2::DuplicateNonce);
        }
        let opening = open_note_opening_v1(cipher, note.event_id, note.access, &note.sealed_note)
            .map_err(|_| PopulatedWalletMigrationErrorV2::InvalidNote)?;
        let commitment = recompute_note_commitment_v1(&opening)
            .map_err(|_| PopulatedWalletMigrationErrorV2::InvalidNote)?;
        let tracked = lane_state
            .migration_tracked_output_v2(note.event_id)
            .ok_or(PopulatedWalletMigrationErrorV2::MissingLaneWitness)?;
        if tracked.commitment != commitment {
            return Err(PopulatedWalletMigrationErrorV2::MissingLaneWitness);
        }
        if let Some(spent) = note.spent {
            if note.access != SealedNoteAccessV1::Spendable
                || decode_digest_canonical(&spent.nullifier).is_err()
                || !nullifiers.insert(spent.nullifier)
                || !spend_authenticator.authenticates_spend_v1(
                    note.event_id,
                    &note.sealed_note,
                    &spent.nullifier,
                )
            {
                return Err(PopulatedWalletMigrationErrorV2::InvalidSpend);
            }
            let transition = lane_state
                .retained_event_v2(spent.transition_output_id)
                .ok_or(PopulatedWalletMigrationErrorV2::InvalidSpend)?;
            let matching = match transition.kind {
                ForestFinalizedAppendKindV2::PrivateTransfer {
                    recipient_event_id,
                    nullifier,
                    ..
                }
                | ForestFinalizedAppendKindV2::Withdrawal {
                    event_id: recipient_event_id,
                    nullifier,
                    ..
                } => {
                    recipient_event_id == spent.transition_output_id && nullifier == spent.nullifier
                }
                ForestFinalizedAppendKindV2::Deposit { .. } => false,
            };
            if !matching {
                return Err(PopulatedWalletMigrationErrorV2::InvalidSpend);
            }
        }
    }
    let tracked_ids = lane_state
        .migration_tracked_outputs_v2()
        .map(|tracked| tracked.output_event_id)
        .collect::<HashSet<_>>();
    if tracked_ids != note_ids {
        return Err(PopulatedWalletMigrationErrorV2::MissingLaneWitness);
    }
    let legacy_tracked_ids = witness
        .current_state()
        .tracked()
        .iter()
        .map(|tracked| tracked.event_id())
        .collect::<HashSet<_>>();
    if legacy_tracked_ids != note_ids {
        return Err(PopulatedWalletMigrationErrorV2::WitnessMismatch);
    }
    Ok(())
}

fn validate_paths_v2(paths: &[&Path; 5]) -> Result<[PathBuf; 5], PopulatedWalletMigrationErrorV2> {
    let parent = paths[0]
        .parent()
        .ok_or(PopulatedWalletMigrationErrorV2::PathMismatch)?;
    let mut canonical = HashSet::new();
    let mut canonical_paths = Vec::with_capacity(paths.len());
    for path in paths {
        if path.parent() != Some(parent) {
            return Err(PopulatedWalletMigrationErrorV2::PathMismatch);
        }
        let path = std::fs::canonicalize(path)?;
        if !canonical.insert(path.clone()) {
            return Err(PopulatedWalletMigrationErrorV2::PathAlias);
        }
        canonical_paths.push(path);
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        let mut inodes = HashSet::new();
        for path in paths {
            let metadata = std::fs::metadata(path)?;
            if metadata.nlink() != 1 || !inodes.insert((metadata.dev(), metadata.ino())) {
                return Err(PopulatedWalletMigrationErrorV2::PathAlias);
            }
        }
    }
    canonical_paths
        .try_into()
        .map_err(|_| PopulatedWalletMigrationErrorV2::CountOverflow)
}

fn wallet_identity_sha256_v2(identity: &DepositScanIdentityV1) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"aspis:pool-v1:lane-forest-wallet-scan-identity:sha256:v2");
    hasher.update(identity.pool());
    hasher.update(identity.deployment_domain());
    hasher.update(identity.asset_mint());
    hasher.update(identity.vault_token_account());
    hasher.update(identity.asset_id().to_le_bytes());
    hasher.finalize().into()
}

fn source_manifest_sha256_v2(sources: &[WalletMigrationSourceDescriptorV2; 5]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(SOURCE_MANIFEST_DOMAIN_V2);
    hasher.update((sources.len() as u64).to_le_bytes());
    for source in sources {
        hasher.update([source.role as u8]);
        hasher.update(source.magic);
        hasher.update([source.version]);
        hasher.update(source.length.to_le_bytes());
        hasher.update(source.image_sha256);
    }
    hasher.finalize().into()
}

fn encode_event_id_v2(event_id: crate::scan_state::DepositEventIdV1) -> [u8; 108] {
    let mut bytes = [0u8; 108];
    bytes[..8].copy_from_slice(&event_id.point().slot().to_le_bytes());
    bytes[8..40].copy_from_slice(event_id.point().block_hash());
    bytes[40..104].copy_from_slice(event_id.transaction_signature());
    bytes[104..106].copy_from_slice(&event_id.instruction_index().to_le_bytes());
    bytes[106..108].copy_from_slice(&event_id.event_index().to_le_bytes());
    bytes
}

#[allow(clippy::too_many_arguments)]
fn migration_id_v2(
    wallet_identity_sha256: [u8; 32],
    note_cipher_id: [u8; 32],
    finalized_head: FinalizedChainPointV1,
    source_manifest_sha256: [u8; 32],
    lane_image: &[u8],
    notes: &[StoredSealedNoteV1],
    relayer_archive: &[u8],
) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(POPULATED_MIGRATION_DOMAIN_V2);
    hasher.update(wallet_identity_sha256);
    hasher.update(note_cipher_id);
    hasher.update(finalized_head.slot().to_le_bytes());
    hasher.update(finalized_head.block_hash());
    hasher.update(source_manifest_sha256);
    hasher.update((lane_image.len() as u64).to_le_bytes());
    hasher.update(Sha256::digest(lane_image));
    hasher.update((notes.len() as u64).to_le_bytes());
    for note in notes {
        hasher.update(encode_event_id_v2(note.event_id));
        hasher.update([match note.access {
            SealedNoteAccessV1::ViewOnly => 1,
            SealedNoteAccessV1::Spendable => 2,
        }]);
        hasher.update((note.sealed_note.len() as u64).to_le_bytes());
        hasher.update(Sha256::digest(&note.sealed_note));
        match note.spent {
            None => hasher.update([0]),
            Some(spent) => {
                hasher.update([1]);
                hasher.update(encode_event_id_v2(spent.transition_output_id));
                hasher.update(spent.nullifier);
            }
        }
    }
    hasher.update((relayer_archive.len() as u64).to_le_bytes());
    hasher.update(Sha256::digest(relayer_archive));
    hasher.finalize().into()
}
