//! Crash-safe wallet/indexer and relayer state.
//!
//! The finalized indexer intentionally mutates an in-memory candidate first.
//! This module commits that candidate, opaque caller-encrypted note records,
//! rollback reconciliation, relayer queue entries and rate counters in one
//! checksummed same-directory rename.  A per-state OS lock prevents two
//! processes from independently advancing the same cursor.

use std::{
    collections::HashSet,
    ffi::OsString,
    fs::{self, File, OpenOptions, TryLockError},
    io::{self, Read, Write},
    path::{Path, PathBuf},
};

use aspis_statement::encode_digest_canonical;
use sha2::{Digest as _, Sha256};
use solana_program::{instruction::AccountMeta, instruction::Instruction, pubkey::Pubkey};
use subtle::ConstantTimeEq;

use crate::{
    finalized_indexer::{FinalizedBlockIngestResultV1, FinalizedPreparedSettlementLifecycleV1},
    pool_transport::{
        AuthenticatedCancelledSettlementV1, AuthenticatedPreparedSettlementPlanIdentityV1,
        AuthenticatedPreparedSettlementV1,
    },
    relayer::{
        admit_relayer_plan_v1, prepare_permissionless_prepared_relayer_plan_v1,
        prepare_permissionless_relayer_plan_v1, relayer_policy_id_v1, RelayerAdmissionContextV1,
        RelayerAdmissionErrorV1, RelayerAdmissionV1, RelayerEnqueueOutcomeV1, RelayerErrorV1,
        RelayerPlanV1, RelayerPolicyV1, RelayerRequestKindV1,
    },
    scan_state::{
        decode_scan_state_v1, encode_scan_state_v1, DepositEventIdV1, DepositScanOutcomeV1,
        FinalizedBlockAdvanceV1, FinalizedChainPointV1, PruneSummaryV1, PublicOutputScanOutcomeV1,
        ScanStateErrorV1, ScanStateV1,
    },
};

const WALLET_MAGIC: [u8; 4] = *b"ASDW";
const RELAYER_MAGIC: [u8; 4] = *b"ASRQ";
const DURABLE_VERSION: u8 = 1;
const WALLET_HEADER_BYTES: usize = 88;
const WALLET_RECORD_HEADER_BYTES: usize = 256;
const PLAN_LIFECYCLE_HEADER_BYTES: usize = 16;
const PLAN_LIFECYCLE_RECORD_BYTES: usize = 428;
const RELAYER_HEADER_BYTES: usize = 88;
const RELAYER_RECORD_HEADER_BYTES: usize = 276;
const RELAYER_PREPARED_PLAN_CONTEXT_BYTES: usize = 240;
const CHECKSUM_OFFSET: usize = 56;

const MAX_DURABLE_IMAGE_BYTES: usize = 64 * 1024 * 1024;
const MAX_SEALED_NOTE_BYTES: usize = 1024 * 1024;
const MAX_NOTE_RECORDS: usize = 1_000_000;
const MAX_RELAYER_RECORDS: usize = 100_000;
const MAX_PLAN_LIFECYCLE_RECORDS: usize = 1_000_000;
const MAX_RELAYER_ACCOUNTS: usize = 256;
const MAX_RELAYER_INSTRUCTION_BYTES: usize = 1024 * 1024;

const WALLET_CHECKSUM_DOMAIN: &[u8] = b"aspis:pool-v1:durable-wallet-state:sha256:v1";
const RELAYER_CHECKSUM_DOMAIN: &[u8] = b"aspis:pool-v1:durable-relayer-state:sha256:v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DurableStateErrorV1 {
    InvalidPath,
    UnsafePath,
    InsecurePermissions,
    AlreadyLocked,
    Io(io::ErrorKind),
    ImageTooLarge,
    WrongMagic,
    WrongVersion,
    NonZeroReserved,
    ChecksumMismatch,
    Truncated,
    TrailingBytes,
    CountOverflow,
    DuplicateRecord,
    NonCanonicalOrder,
    IdentityMismatch,
    CipherMismatch,
    CipherRotationMismatch,
    InvalidCipherId,
    InvalidSealedNote,
    MissingRecoveredNote,
    UnexpectedRecoveredNote,
    RecoveredAccessMismatch,
    CandidateStateMismatch,
    InvalidRollback,
    InvalidSpendUpdate,
    InvalidPlanLifecycle,
    SpendNotAuthorized,
    AlreadySpentDifferently,
    PolicyMismatch,
    InvalidRelayerState,
    InvalidQueueTransition,
    ScanState(ScanStateErrorV1),
    Relayer(RelayerErrorV1),
    Admission(RelayerAdmissionErrorV1),
}

impl From<io::Error> for DurableStateErrorV1 {
    fn from(error: io::Error) -> Self {
        Self::Io(error.kind())
    }
}

impl From<ScanStateErrorV1> for DurableStateErrorV1 {
    fn from(error: ScanStateErrorV1) -> Self {
        Self::ScanState(error)
    }
}

impl From<RelayerErrorV1> for DurableStateErrorV1 {
    fn from(error: RelayerErrorV1) -> Self {
        Self::Relayer(error)
    }
}

impl From<RelayerAdmissionErrorV1> for DurableStateErrorV1 {
    fn from(error: RelayerAdmissionErrorV1) -> Self {
        Self::Admission(error)
    }
}

struct AtomicStateFileV1 {
    path: PathBuf,
    _lock: File,
}

impl AtomicStateFileV1 {
    fn acquire(path: &Path) -> Result<Self, DurableStateErrorV1> {
        let file_name = path.file_name().ok_or(DurableStateErrorV1::InvalidPath)?;
        if file_name.is_empty() {
            return Err(DurableStateErrorV1::InvalidPath);
        }
        let parent = path.parent().ok_or(DurableStateErrorV1::InvalidPath)?;
        let parent_meta = fs::symlink_metadata(parent)?;
        if parent_meta.file_type().is_symlink() || !parent_meta.is_dir() {
            return Err(DurableStateErrorV1::UnsafePath);
        }
        validate_regular_private_file_v1(path, true)?;

        let lock_path = sibling_path_v1(path, ".lock")?;
        validate_regular_private_file_v1(&lock_path, true)?;
        let mut options = OpenOptions::new();
        options.read(true).write(true).create(true);
        #[cfg(unix)]
        {
            use std::os::unix::fs::OpenOptionsExt as _;
            options.mode(0o600);
        }
        let lock = options.open(&lock_path)?;
        set_private_permissions_v1(&lock)?;
        match lock.try_lock() {
            Ok(()) => {}
            Err(TryLockError::WouldBlock) => return Err(DurableStateErrorV1::AlreadyLocked),
            Err(TryLockError::Error(error)) => return Err(error.into()),
        }
        validate_regular_private_file_v1(&lock_path, false)?;
        Ok(Self {
            path: path.to_owned(),
            _lock: lock,
        })
    }

    fn read_optional(&self) -> Result<Option<Vec<u8>>, DurableStateErrorV1> {
        let mut file = match File::open(&self.path) {
            Ok(file) => file,
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
            Err(error) => return Err(error.into()),
        };
        let metadata = file.metadata()?;
        if !metadata.is_file() {
            return Err(DurableStateErrorV1::UnsafePath);
        }
        if metadata.len() > MAX_DURABLE_IMAGE_BYTES as u64 {
            return Err(DurableStateErrorV1::ImageTooLarge);
        }
        let mut bytes = Vec::with_capacity(metadata.len() as usize);
        file.read_to_end(&mut bytes)?;
        if bytes.len() > MAX_DURABLE_IMAGE_BYTES {
            return Err(DurableStateErrorV1::ImageTooLarge);
        }
        Ok(Some(bytes))
    }

    fn replace(&self, bytes: &[u8]) -> Result<(), DurableStateErrorV1> {
        if bytes.len() > MAX_DURABLE_IMAGE_BYTES {
            return Err(DurableStateErrorV1::ImageTooLarge);
        }
        let temporary = sibling_path_v1(&self.path, ".tmp")?;
        validate_regular_private_file_v1(&temporary, true)?;
        let mut options = OpenOptions::new();
        options.write(true).create(true).truncate(true);
        #[cfg(unix)]
        {
            use std::os::unix::fs::OpenOptionsExt as _;
            options.mode(0o600);
        }
        let mut file = options.open(&temporary)?;
        set_private_permissions_v1(&file)?;
        file.write_all(bytes)?;
        file.sync_all()?;
        drop(file);
        fs::rename(&temporary, &self.path)?;
        validate_regular_private_file_v1(&self.path, false)?;
        File::open(self.path.parent().ok_or(DurableStateErrorV1::InvalidPath)?)?.sync_all()?;
        Ok(())
    }
}

fn sibling_path_v1(path: &Path, suffix: &str) -> Result<PathBuf, DurableStateErrorV1> {
    let name = path.file_name().ok_or(DurableStateErrorV1::InvalidPath)?;
    let mut suffixed = OsString::from(name);
    suffixed.push(suffix);
    Ok(path.with_file_name(suffixed))
}

fn validate_regular_private_file_v1(
    path: &Path,
    allow_missing: bool,
) -> Result<(), DurableStateErrorV1> {
    let metadata = match fs::symlink_metadata(path) {
        Ok(metadata) => metadata,
        Err(error) if allow_missing && error.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(error.into()),
    };
    if metadata.file_type().is_symlink() || !metadata.is_file() {
        return Err(DurableStateErrorV1::UnsafePath);
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        if metadata.permissions().mode() & 0o077 != 0 {
            return Err(DurableStateErrorV1::InsecurePermissions);
        }
    }
    Ok(())
}

fn set_private_permissions_v1(file: &File) -> Result<(), DurableStateErrorV1> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        file.set_permissions(fs::Permissions::from_mode(0o600))?;
    }
    Ok(())
}

fn checksum_image_v1(domain: &[u8], bytes: &[u8]) -> Result<[u8; 32], DurableStateErrorV1> {
    if bytes.len() < RELAYER_HEADER_BYTES {
        return Err(DurableStateErrorV1::Truncated);
    }
    let length = u64::try_from(bytes.len()).map_err(|_| DurableStateErrorV1::CountOverflow)?;
    let mut hasher = Sha256::new();
    hasher.update(domain);
    hasher.update(length.to_le_bytes());
    hasher.update(&bytes[..CHECKSUM_OFFSET]);
    hasher.update([0u8; 32]);
    hasher.update(&bytes[CHECKSUM_OFFSET + 32..]);
    Ok(hasher.finalize().into())
}

fn finish_checksum_v1(domain: &[u8], bytes: &mut [u8]) -> Result<(), DurableStateErrorV1> {
    let checksum = checksum_image_v1(domain, bytes)?;
    bytes[CHECKSUM_OFFSET..CHECKSUM_OFFSET + 32].copy_from_slice(&checksum);
    Ok(())
}

fn verify_checksum_v1(domain: &[u8], bytes: &[u8]) -> Result<(), DurableStateErrorV1> {
    let encoded: [u8; 32] = read_array_v1(bytes, CHECKSUM_OFFSET)?;
    let expected = checksum_image_v1(domain, bytes)?;
    if !bool::from(encoded.ct_eq(&expected)) {
        return Err(DurableStateErrorV1::ChecksumMismatch);
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SealedNoteAccessV1 {
    ViewOnly,
    Spendable,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SealedRecoveredNoteV1 {
    pub event_id: DepositEventIdV1,
    pub access: SealedNoteAccessV1,
    /// Opaque output of the caller's authenticated at-rest encryption. The
    /// durable state never accepts or serializes a `NoteOpeningV1`.
    pub sealed_note: Vec<u8>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SpentNoteMarkerV1 {
    pub transition_output_id: DepositEventIdV1,
    pub nullifier: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StoredSealedNoteV1 {
    pub event_id: DepositEventIdV1,
    pub access: SealedNoteAccessV1,
    pub sealed_note: Vec<u8>,
    pub spent: Option<SpentNoteMarkerV1>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AuthenticatedSpentNoteUpdateV1 {
    pub input_event_id: DepositEventIdV1,
    pub transition_output_id: DepositEventIdV1,
    pub nullifier: [u8; 32],
}

/// Secret-bearing wallet implementations prove that the public nullifier in
/// a finalized transition belongs to the referenced locally sealed input.
/// The durable layer calls this before marking a note spent and never receives
/// the spending key itself.
pub trait LocalSpendAuthenticatorV1 {
    fn authenticates_spend_v1(
        &self,
        input_event_id: DepositEventIdV1,
        sealed_note: &[u8],
        nullifier: &[u8; 32],
    ) -> bool;
}

pub struct DurableWalletStateV1 {
    file: AtomicStateFileV1,
    scan_state: ScanStateV1,
    note_cipher_id: [u8; 32],
    notes: Vec<StoredSealedNoteV1>,
    base_prepared_plans: Vec<AuthenticatedPreparedSettlementV1>,
    prepared_plan_lifecycle: Vec<FinalizedPreparedSettlementLifecycleV1>,
    active_prepared_plans: Vec<AuthenticatedPreparedSettlementV1>,
}

impl DurableWalletStateV1 {
    pub fn open_or_create_v1(
        path: impl AsRef<Path>,
        initial_scan_state: ScanStateV1,
        note_cipher_id: [u8; 32],
    ) -> Result<Self, DurableStateErrorV1> {
        if note_cipher_id == [0u8; 32] {
            return Err(DurableStateErrorV1::InvalidCipherId);
        }
        let file = AtomicStateFileV1::acquire(path.as_ref())?;
        if let Some(bytes) = file.read_optional()? {
            let (scan_state, stored_cipher_id, notes, base_prepared_plans, lifecycle) =
                decode_wallet_image_v1(&bytes)?;
            if scan_state.identity() != initial_scan_state.identity() {
                return Err(DurableStateErrorV1::IdentityMismatch);
            }
            if stored_cipher_id != note_cipher_id {
                return Err(DurableStateErrorV1::CipherMismatch);
            }
            let active_prepared_plans =
                replay_prepared_plan_lifecycle_v1(&base_prepared_plans, &lifecycle)?;
            return Ok(Self {
                file,
                scan_state,
                note_cipher_id,
                notes,
                base_prepared_plans,
                prepared_plan_lifecycle: lifecycle,
                active_prepared_plans,
            });
        }
        let bytes = encode_wallet_image_v1(&initial_scan_state, note_cipher_id, &[], &[], &[])?;
        file.replace(&bytes)?;
        Ok(Self {
            file,
            scan_state: initial_scan_state,
            note_cipher_id,
            notes: Vec::new(),
            base_prepared_plans: Vec::new(),
            prepared_plan_lifecycle: Vec::new(),
            active_prepared_plans: Vec::new(),
        })
    }

    pub fn scan_state(&self) -> &ScanStateV1 {
        &self.scan_state
    }

    pub fn note_cipher_id(&self) -> &[u8; 32] {
        &self.note_cipher_id
    }

    pub fn notes(&self) -> &[StoredSealedNoteV1] {
        &self.notes
    }

    /// Atomically replace every opaque note ciphertext and advance the
    /// cipher/key-generation identifier.  This crate-internal primitive is
    /// exposed only through the authenticated `note_store_crypto` rotation,
    /// which opens every old ciphertext and seals every replacement before
    /// this all-or-nothing state transition is attempted.
    pub(crate) fn replace_note_cipher_v1(
        &mut self,
        expected_old_cipher_id: [u8; 32],
        new_cipher_id: [u8; 32],
        replacements: &[SealedRecoveredNoteV1],
    ) -> Result<(), DurableStateErrorV1> {
        if self.note_cipher_id != expected_old_cipher_id {
            return Err(DurableStateErrorV1::CipherMismatch);
        }
        if new_cipher_id == [0u8; 32] || new_cipher_id == expected_old_cipher_id {
            return Err(DurableStateErrorV1::InvalidCipherId);
        }
        if replacements.len() != self.notes.len() {
            return Err(DurableStateErrorV1::CipherRotationMismatch);
        }
        let mut notes = self.notes.clone();
        let mut supplied = HashSet::with_capacity(replacements.len());
        for replacement in replacements {
            validate_sealed_note_v1(replacement)?;
            if !supplied.insert(replacement.event_id) {
                return Err(DurableStateErrorV1::CipherRotationMismatch);
            }
            let note = notes
                .iter_mut()
                .find(|note| note.event_id == replacement.event_id)
                .ok_or(DurableStateErrorV1::CipherRotationMismatch)?;
            if note.access != replacement.access {
                return Err(DurableStateErrorV1::CipherRotationMismatch);
            }
            note.sealed_note.clone_from(&replacement.sealed_note);
        }
        let bytes = encode_wallet_image_v1(
            &self.scan_state,
            new_cipher_id,
            &notes,
            &self.base_prepared_plans,
            &self.prepared_plan_lifecycle,
        )?;
        self.file.replace(&bytes)?;
        self.note_cipher_id = new_cipher_id;
        self.notes = notes;
        Ok(())
    }

    /// Finalized prepared plans not yet closed by a successful `ASPF` or
    /// `ASPX`. All fields are public account/reconciliation metadata.
    pub fn active_prepared_plans(&self) -> &[AuthenticatedPreparedSettlementV1] {
        &self.active_prepared_plans
    }

    /// Advance the rollback anchor and durably commit it without deleting
    /// wallet notes. Deliveries for an event must be reconciled before its
    /// block is pruned because the compact cursor no longer retains that ID.
    pub fn prune_finalized_history_through_v1(
        &mut self,
        ancestor: FinalizedChainPointV1,
    ) -> Result<PruneSummaryV1, DurableStateErrorV1> {
        let mut candidate = self.scan_state.clone();
        let summary = candidate.prune_finalized_history_through_v1(ancestor)?;
        let mut base_prepared_plans = self.base_prepared_plans.clone();
        let mut lifecycle = Vec::new();
        for event in &self.prepared_plan_lifecycle {
            if candidate.retains_chain_point_v1(plan_lifecycle_event_id_v1(event).point()) {
                lifecycle.push(*event);
            } else {
                apply_prepared_plan_lifecycle_event_v1(&mut base_prepared_plans, event)?;
            }
        }
        let active_prepared_plans =
            replay_prepared_plan_lifecycle_v1(&base_prepared_plans, &lifecycle)?;
        let bytes = encode_wallet_image_v1(
            &candidate,
            self.note_cipher_id,
            &self.notes,
            &base_prepared_plans,
            &lifecycle,
        )?;
        self.file.replace(&bytes)?;
        self.scan_state = candidate;
        self.base_prepared_plans = base_prepared_plans;
        self.prepared_plan_lifecycle = lifecycle;
        self.active_prepared_plans = active_prepared_plans;
        Ok(summary)
    }

    /// Commit the exact candidate produced by finalized ingestion together
    /// with its opaque recovered-note outputs and authenticated spent-input
    /// updates. Every validation happens on clones before the atomic rename.
    pub fn commit_finalized_ingest_v1(
        &mut self,
        candidate_scan_state: ScanStateV1,
        result: &FinalizedBlockIngestResultV1,
        recovered_notes: &[SealedRecoveredNoteV1],
        spent_updates: &[AuthenticatedSpentNoteUpdateV1],
        spend_authenticator: &impl LocalSpendAuthenticatorV1,
    ) -> Result<(), DurableStateErrorV1> {
        validate_candidate_transition_v1(&self.scan_state, &candidate_scan_state, result)?;
        let mut notes = self.notes.clone();
        if let Some(rollback) = &result.rollback {
            let removed: HashSet<_> = rollback.removed_events.iter().copied().collect();
            if rollback.head != candidate_scan_state.anchor()
                && !candidate_scan_state.retains_chain_point_v1(rollback.head)
            {
                return Err(DurableStateErrorV1::InvalidRollback);
            }
            notes.retain(|note| !removed.contains(&note.event_id));
            for note in &mut notes {
                if note
                    .spent
                    .is_some_and(|spent| removed.contains(&spent.transition_output_id))
                {
                    note.spent = None;
                }
            }
        }

        let mut required_deposits = Vec::new();
        for (event_id, outcome) in result
            .deposit_event_ids
            .iter()
            .copied()
            .zip(&result.deposit_outcomes)
        {
            if !candidate_scan_state
                .retained_event_ids_in_block_v1(event_id.point())
                .contains(&event_id)
            {
                return Err(DurableStateErrorV1::CandidateStateMismatch);
            }
            match outcome {
                DepositScanOutcomeV1::ViewOnly(_) => {
                    required_deposits.push((event_id, SealedNoteAccessV1::ViewOnly));
                }
                DepositScanOutcomeV1::Spendable(_) => {
                    required_deposits.push((event_id, SealedNoteAccessV1::Spendable));
                }
                DepositScanOutcomeV1::Duplicate
                | DepositScanOutcomeV1::NotForViewingKey
                | DepositScanOutcomeV1::InvalidEncryptedPayload(_)
                | DepositScanOutcomeV1::InconsistentRecoveredNote(_) => {}
            }
        }

        let transition_ids: Vec<_> = result
            .transition_evidence
            .iter()
            .flat_map(|evidence| evidence.output_ids.iter().copied())
            .collect();
        if transition_ids.len() != result.transition_outcomes.len() {
            return Err(DurableStateErrorV1::CandidateStateMismatch);
        }
        let advanced_transition_ids: HashSet<_> = transition_ids
            .iter()
            .copied()
            .zip(&result.transition_outcomes)
            .filter_map(|(id, outcome)| {
                (*outcome == PublicOutputScanOutcomeV1::Advanced).then_some(id)
            })
            .collect();

        let mut supplied = HashSet::new();
        for recovered in recovered_notes {
            validate_sealed_note_v1(recovered)?;
            if !supplied.insert(recovered.event_id) {
                return Err(DurableStateErrorV1::DuplicateRecord);
            }
            let required_access = required_deposits
                .iter()
                .find_map(|(id, access)| (*id == recovered.event_id).then_some(*access));
            if let Some(access) = required_access {
                if access != recovered.access {
                    return Err(DurableStateErrorV1::RecoveredAccessMismatch);
                }
            } else if !advanced_transition_ids.contains(&recovered.event_id) {
                return Err(DurableStateErrorV1::UnexpectedRecoveredNote);
            }
            insert_sealed_note_v1(&mut notes, recovered)?;
        }
        if required_deposits
            .iter()
            .any(|(id, _)| !supplied.contains(id))
        {
            return Err(DurableStateErrorV1::MissingRecoveredNote);
        }

        for update in spent_updates {
            let evidence = result
                .transition_evidence
                .iter()
                .find(|evidence| evidence.output_ids.contains(&update.transition_output_id))
                .ok_or(DurableStateErrorV1::InvalidSpendUpdate)?;
            if encode_digest_canonical(&evidence.receipt.nullifier) != update.nullifier {
                return Err(DurableStateErrorV1::InvalidSpendUpdate);
            }
            let note = notes
                .iter_mut()
                .find(|note| note.event_id == update.input_event_id)
                .ok_or(DurableStateErrorV1::InvalidSpendUpdate)?;
            if note.access != SealedNoteAccessV1::Spendable {
                return Err(DurableStateErrorV1::InvalidSpendUpdate);
            }
            if !spend_authenticator.authenticates_spend_v1(
                note.event_id,
                &note.sealed_note,
                &update.nullifier,
            ) {
                return Err(DurableStateErrorV1::SpendNotAuthorized);
            }
            let marker = SpentNoteMarkerV1 {
                transition_output_id: update.transition_output_id,
                nullifier: update.nullifier,
            };
            match note.spent {
                None => note.spent = Some(marker),
                Some(existing) if existing == marker => {}
                Some(_) => return Err(DurableStateErrorV1::AlreadySpentDifferently),
            }
        }

        validate_reported_plan_lifecycle_v1(result)?;
        let mut lifecycle = self.prepared_plan_lifecycle.clone();
        if result.rollback.is_some() {
            lifecycle.retain(|event| {
                candidate_scan_state
                    .retains_chain_point_v1(plan_lifecycle_event_id_v1(event).point())
            });
        }
        for event in &result.plan_lifecycle {
            if !candidate_scan_state
                .retains_chain_point_v1(plan_lifecycle_event_id_v1(event).point())
            {
                return Err(DurableStateErrorV1::CandidateStateMismatch);
            }
            if let Some(existing) = lifecycle.iter().find(|existing| {
                plan_lifecycle_event_id_v1(existing) == plan_lifecycle_event_id_v1(event)
            }) {
                if existing != event {
                    return Err(DurableStateErrorV1::InvalidPlanLifecycle);
                }
                continue;
            }
            lifecycle.push(*event);
        }
        if lifecycle.len() > MAX_PLAN_LIFECYCLE_RECORDS {
            return Err(DurableStateErrorV1::CountOverflow);
        }
        let active_prepared_plans =
            replay_prepared_plan_lifecycle_v1(&self.base_prepared_plans, &lifecycle)?;
        let bytes = encode_wallet_image_v1(
            &candidate_scan_state,
            self.note_cipher_id,
            &notes,
            &self.base_prepared_plans,
            &lifecycle,
        )?;
        self.file.replace(&bytes)?;
        self.scan_state = candidate_scan_state;
        self.notes = notes;
        self.prepared_plan_lifecycle = lifecycle;
        self.active_prepared_plans = active_prepared_plans;
        Ok(())
    }

    /// Attach a separately authenticated recipient delivery for an output
    /// already present in the finalized cursor, then durably commit it.
    pub fn store_authenticated_delivery_v1(
        &mut self,
        recovered: &SealedRecoveredNoteV1,
    ) -> Result<RelayerEnqueueOutcomeV1, DurableStateErrorV1> {
        validate_sealed_note_v1(recovered)?;
        if !self
            .scan_state
            .retained_event_ids_in_block_v1(recovered.event_id.point())
            .contains(&recovered.event_id)
        {
            return Err(DurableStateErrorV1::UnexpectedRecoveredNote);
        }
        if let Some(existing) = self
            .notes
            .iter()
            .find(|note| note.event_id == recovered.event_id)
        {
            return if existing.access == recovered.access
                && existing.sealed_note == recovered.sealed_note
            {
                Ok(RelayerEnqueueOutcomeV1::AlreadyPresent)
            } else {
                Err(DurableStateErrorV1::DuplicateRecord)
            };
        }
        let mut notes = self.notes.clone();
        insert_sealed_note_v1(&mut notes, recovered)?;
        let bytes = encode_wallet_image_v1(
            &self.scan_state,
            self.note_cipher_id,
            &notes,
            &self.base_prepared_plans,
            &self.prepared_plan_lifecycle,
        )?;
        self.file.replace(&bytes)?;
        self.notes = notes;
        Ok(RelayerEnqueueOutcomeV1::Inserted)
    }
}

fn validate_candidate_transition_v1(
    previous: &ScanStateV1,
    candidate: &ScanStateV1,
    result: &FinalizedBlockIngestResultV1,
) -> Result<(), DurableStateErrorV1> {
    if candidate.identity() != previous.identity()
        || result.deposit_event_ids.len() != result.deposit_outcomes.len()
    {
        return Err(DurableStateErrorV1::CandidateStateMismatch);
    }
    let transition_ids: Vec<_> = result
        .transition_evidence
        .iter()
        .flat_map(|evidence| evidence.output_ids.iter().copied())
        .collect();
    if transition_ids.len() != result.transition_outcomes.len() {
        return Err(DurableStateErrorV1::CandidateStateMismatch);
    }
    let mut reported_ids = result.deposit_event_ids.clone();
    reported_ids.extend(transition_ids);
    let reported_set: HashSet<_> = reported_ids.iter().copied().collect();
    if reported_set.len() != reported_ids.len() {
        return Err(DurableStateErrorV1::CandidateStateMismatch);
    }
    let root_ids: HashSet<_> = result
        .root_evidence
        .iter()
        .map(|evidence| evidence.event_id)
        .collect();
    if root_ids.len() != result.root_evidence.len() || root_ids != reported_set {
        return Err(DurableStateErrorV1::CandidateStateMismatch);
    }
    let append_ids: HashSet<_> = result
        .append_evidence
        .iter()
        .map(|evidence| evidence.event_id)
        .collect();
    if append_ids.len() != result.append_evidence.len()
        || append_ids != reported_set
        || result.append_evidence.iter().any(|append| {
            !result.root_evidence.iter().any(|root| {
                root.event_id == append.event_id
                    && root.root_sequence == append.root_sequence
                    && root.root == append.root
            })
        })
    {
        return Err(DurableStateErrorV1::CandidateStateMismatch);
    }

    let expected_ids = match (&result.advance, &result.rollback) {
        (FinalizedBlockAdvanceV1::AlreadyCurrent, None) => {
            if candidate != previous {
                return Err(DurableStateErrorV1::CandidateStateMismatch);
            }
            previous.retained_event_ids_in_block_v1(previous.head())
        }
        (FinalizedBlockAdvanceV1::Advanced, None) => {
            if candidate.retained_block_count() != previous.retained_block_count() + 1 {
                return Err(DurableStateErrorV1::CandidateStateMismatch);
            }
            let mut reduced = candidate.clone();
            let added = reduced
                .rollback_to_v1(previous.head())
                .map_err(|_| DurableStateErrorV1::CandidateStateMismatch)?;
            if reduced != *previous {
                return Err(DurableStateErrorV1::CandidateStateMismatch);
            }
            added.removed_events
        }
        (FinalizedBlockAdvanceV1::Advanced, Some(rollback)) => {
            let mut previous_base = previous.clone();
            let expected_rollback = previous_base
                .rollback_to_v1(rollback.head)
                .map_err(|_| DurableStateErrorV1::InvalidRollback)?;
            if expected_rollback != *rollback
                || candidate.retained_block_count() != previous_base.retained_block_count() + 1
            {
                return Err(DurableStateErrorV1::InvalidRollback);
            }
            let mut candidate_base = candidate.clone();
            let added = candidate_base
                .rollback_to_v1(rollback.head)
                .map_err(|_| DurableStateErrorV1::CandidateStateMismatch)?;
            if candidate_base != previous_base {
                return Err(DurableStateErrorV1::CandidateStateMismatch);
            }
            added.removed_events
        }
        (FinalizedBlockAdvanceV1::AlreadyCurrent, Some(_)) => {
            return Err(DurableStateErrorV1::InvalidRollback)
        }
    };
    let expected_set: HashSet<_> = expected_ids.iter().copied().collect();
    if expected_set.len() != expected_ids.len() || expected_set != reported_set {
        return Err(DurableStateErrorV1::CandidateStateMismatch);
    }
    if result
        .append_evidence
        .iter()
        .map(|evidence| evidence.event_id)
        .ne(expected_ids.iter().copied())
    {
        return Err(DurableStateErrorV1::CandidateStateMismatch);
    }
    Ok(())
}

fn plan_lifecycle_event_id_v1(event: &FinalizedPreparedSettlementLifecycleV1) -> DepositEventIdV1 {
    match event {
        FinalizedPreparedSettlementLifecycleV1::Prepared(plan) => plan.id,
        FinalizedPreparedSettlementLifecycleV1::Settled { id, .. } => *id,
        FinalizedPreparedSettlementLifecycleV1::Cancelled(cancelled) => cancelled.id,
    }
}

fn prepared_plan_identity_v1(
    plan: &AuthenticatedPreparedSettlementV1,
) -> AuthenticatedPreparedSettlementPlanIdentityV1 {
    AuthenticatedPreparedSettlementPlanIdentityV1 {
        plan_authority: plan.plan_authority,
        core_plan: plan.core_plan,
        rollover_shard: plan.rollover_shard,
    }
}

fn validate_reported_plan_lifecycle_v1(
    result: &FinalizedBlockIngestResultV1,
) -> Result<(), DurableStateErrorV1> {
    let prepared: Vec<_> = result
        .plan_lifecycle
        .iter()
        .filter_map(|event| match event {
            FinalizedPreparedSettlementLifecycleV1::Prepared(plan) => Some(*plan),
            _ => None,
        })
        .collect();
    let cancelled: Vec<_> = result
        .plan_lifecycle
        .iter()
        .filter_map(|event| match event {
            FinalizedPreparedSettlementLifecycleV1::Cancelled(plan) => Some(*plan),
            _ => None,
        })
        .collect();
    let settled: Vec<_> = result
        .plan_lifecycle
        .iter()
        .filter_map(|event| match event {
            FinalizedPreparedSettlementLifecycleV1::Settled { id, plan } => Some((*id, *plan)),
            _ => None,
        })
        .collect();
    let expected_settled: Vec<_> = result
        .transition_evidence
        .iter()
        .filter_map(|evidence| {
            evidence
                .settled_plan
                .map(|plan| (evidence.output_ids.first().copied(), plan))
        })
        .map(|(id, plan)| {
            id.map(|id| (id, plan))
                .ok_or(DurableStateErrorV1::InvalidPlanLifecycle)
        })
        .collect::<Result<_, _>>()?;
    if prepared != result.prepared_settlements
        || cancelled != result.cancelled_settlements
        || settled != expected_settled
    {
        return Err(DurableStateErrorV1::InvalidPlanLifecycle);
    }
    let mut ids = HashSet::new();
    if !result
        .plan_lifecycle
        .iter()
        .all(|event| ids.insert(plan_lifecycle_event_id_v1(event)))
    {
        return Err(DurableStateErrorV1::InvalidPlanLifecycle);
    }
    Ok(())
}

fn apply_prepared_plan_lifecycle_event_v1(
    active: &mut Vec<AuthenticatedPreparedSettlementV1>,
    event: &FinalizedPreparedSettlementLifecycleV1,
) -> Result<(), DurableStateErrorV1> {
    match event {
        FinalizedPreparedSettlementLifecycleV1::Prepared(plan) => {
            if plan.plan_authority == [0u8; 32]
                || plan.authorization_receipt == [0u8; 32]
                || plan.verifier_registry == [0u8; 32]
                || plan.verifier_entry == [0u8; 32]
                || plan.core_plan == [0u8; 32]
                || plan.expires_at_slot < plan.not_before_slot
                || plan.rollover_page.is_some() != plan.rollover_shard.is_some()
            {
                return Err(DurableStateErrorV1::InvalidPlanLifecycle);
            }
            if active
                .iter()
                .any(|existing| existing.core_plan == plan.core_plan)
            {
                return Err(DurableStateErrorV1::InvalidPlanLifecycle);
            }
            active.push(*plan);
        }
        FinalizedPreparedSettlementLifecycleV1::Settled { plan, .. } => {
            close_prepared_plan_v1(active, *plan)?;
        }
        FinalizedPreparedSettlementLifecycleV1::Cancelled(cancelled) => {
            close_prepared_plan_v1(
                active,
                AuthenticatedPreparedSettlementPlanIdentityV1 {
                    plan_authority: cancelled.plan_authority,
                    core_plan: cancelled.core_plan,
                    rollover_shard: cancelled.rollover_shard,
                },
            )?;
        }
    }
    Ok(())
}

fn close_prepared_plan_v1(
    active: &mut Vec<AuthenticatedPreparedSettlementV1>,
    identity: AuthenticatedPreparedSettlementPlanIdentityV1,
) -> Result<(), DurableStateErrorV1> {
    if identity.plan_authority == [0u8; 32] || identity.core_plan == [0u8; 32] {
        return Err(DurableStateErrorV1::InvalidPlanLifecycle);
    }
    let Some(index) = active
        .iter()
        .position(|plan| plan.core_plan == identity.core_plan)
    else {
        // A wallet may begin scanning after the corresponding ASPP. The
        // authenticated closure is still retained in the rollback journal.
        return Ok(());
    };
    if prepared_plan_identity_v1(&active[index]) != identity {
        return Err(DurableStateErrorV1::InvalidPlanLifecycle);
    }
    active.remove(index);
    Ok(())
}

fn replay_prepared_plan_lifecycle_v1(
    base: &[AuthenticatedPreparedSettlementV1],
    lifecycle: &[FinalizedPreparedSettlementLifecycleV1],
) -> Result<Vec<AuthenticatedPreparedSettlementV1>, DurableStateErrorV1> {
    let mut active = base.to_vec();
    let mut cores = HashSet::new();
    if !active.iter().all(|plan| cores.insert(plan.core_plan)) {
        return Err(DurableStateErrorV1::DuplicateRecord);
    }
    let mut ids = HashSet::new();
    for event in lifecycle {
        if !ids.insert(plan_lifecycle_event_id_v1(event)) {
            return Err(DurableStateErrorV1::DuplicateRecord);
        }
        apply_prepared_plan_lifecycle_event_v1(&mut active, event)?;
    }
    active.sort_by_key(|plan| plan.core_plan);
    Ok(active)
}

fn validate_sealed_note_v1(note: &SealedRecoveredNoteV1) -> Result<(), DurableStateErrorV1> {
    if note.sealed_note.is_empty() || note.sealed_note.len() > MAX_SEALED_NOTE_BYTES {
        return Err(DurableStateErrorV1::InvalidSealedNote);
    }
    Ok(())
}

fn insert_sealed_note_v1(
    notes: &mut Vec<StoredSealedNoteV1>,
    recovered: &SealedRecoveredNoteV1,
) -> Result<(), DurableStateErrorV1> {
    if let Some(existing) = notes
        .iter()
        .find(|note| note.event_id == recovered.event_id)
    {
        return if existing.access == recovered.access
            && existing.sealed_note == recovered.sealed_note
        {
            Ok(())
        } else {
            Err(DurableStateErrorV1::DuplicateRecord)
        };
    }
    if notes.len() >= MAX_NOTE_RECORDS {
        return Err(DurableStateErrorV1::CountOverflow);
    }
    notes.push(StoredSealedNoteV1 {
        event_id: recovered.event_id,
        access: recovered.access,
        sealed_note: recovered.sealed_note.clone(),
        spent: None,
    });
    Ok(())
}

fn encode_plan_lifecycle_record_v1(
    event: &FinalizedPreparedSettlementLifecycleV1,
) -> Result<[u8; PLAN_LIFECYCLE_RECORD_BYTES], DurableStateErrorV1> {
    let mut bytes = [0u8; PLAN_LIFECYCLE_RECORD_BYTES];
    bytes[..108].copy_from_slice(&encode_event_id_v1(plan_lifecycle_event_id_v1(event)));
    match event {
        FinalizedPreparedSettlementLifecycleV1::Prepared(plan) => {
            bytes[108] = 1;
            bytes[109] = plan.transition_kind as u8;
            bytes[110] = u8::from(plan.rollover_page.is_some())
                | (u8::from(plan.rollover_shard.is_some()) << 1);
            bytes[116..124].copy_from_slice(&plan.source_root_sequence.to_le_bytes());
            bytes[124..132].copy_from_slice(&plan.not_before_slot.to_le_bytes());
            bytes[132..140].copy_from_slice(&plan.expires_at_slot.to_le_bytes());
            bytes[140..172].copy_from_slice(&plan.plan_authority);
            bytes[172..204].copy_from_slice(&plan.authorization_receipt);
            bytes[204..236].copy_from_slice(&plan.verifier_registry);
            bytes[236..268].copy_from_slice(&plan.verifier_entry);
            bytes[268..300].copy_from_slice(&plan.core_plan);
            if let Some(page) = plan.rollover_page {
                bytes[300..332].copy_from_slice(&page);
            }
            if let Some(shard) = plan.rollover_shard {
                bytes[332..364].copy_from_slice(&shard);
            }
            bytes[364..396].copy_from_slice(&plan.verifier_profile);
            bytes[396..428].copy_from_slice(&plan.verifier_release);
        }
        FinalizedPreparedSettlementLifecycleV1::Settled { plan, .. } => {
            bytes[108] = 2;
            bytes[110] = u8::from(plan.rollover_shard.is_some()) << 1;
            bytes[140..172].copy_from_slice(&plan.plan_authority);
            bytes[268..300].copy_from_slice(&plan.core_plan);
            if let Some(shard) = plan.rollover_shard {
                bytes[332..364].copy_from_slice(&shard);
            }
        }
        FinalizedPreparedSettlementLifecycleV1::Cancelled(cancelled) => {
            bytes[108] = 3;
            bytes[110] = u8::from(cancelled.rollover_shard.is_some()) << 1;
            bytes[140..172].copy_from_slice(&cancelled.plan_authority);
            bytes[268..300].copy_from_slice(&cancelled.core_plan);
            if let Some(shard) = cancelled.rollover_shard {
                bytes[332..364].copy_from_slice(&shard);
            }
        }
    }
    Ok(bytes)
}

fn decode_plan_lifecycle_record_v1(
    bytes: &[u8],
) -> Result<FinalizedPreparedSettlementLifecycleV1, DurableStateErrorV1> {
    if bytes.len() != PLAN_LIFECYCLE_RECORD_BYTES {
        return Err(DurableStateErrorV1::Truncated);
    }
    if bytes[111..116] != [0u8; 5] || bytes[110] & !3 != 0 {
        return Err(DurableStateErrorV1::NonZeroReserved);
    }
    let id = decode_event_id_v1(&read_array_v1(bytes, 0)?)?;
    let authority = read_array_v1(bytes, 140)?;
    let core = read_array_v1(bytes, 268)?;
    let page = (bytes[110] & 1 != 0)
        .then(|| read_array_v1(bytes, 300))
        .transpose()?;
    let shard = (bytes[110] & 2 != 0)
        .then(|| read_array_v1(bytes, 332))
        .transpose()?;
    match bytes[108] {
        1 => {
            let transition_kind = match bytes[109] {
                1 => aspis_statement::pool_v1::PoolV1TransitionKind::PrivateTransfer,
                2 => aspis_statement::pool_v1::PoolV1TransitionKind::Withdrawal,
                _ => return Err(DurableStateErrorV1::InvalidPlanLifecycle),
            };
            let plan = AuthenticatedPreparedSettlementV1 {
                id,
                transition_kind,
                source_root_sequence: read_u64_v1(bytes, 116)?,
                not_before_slot: read_u64_v1(bytes, 124)?,
                expires_at_slot: read_u64_v1(bytes, 132)?,
                plan_authority: authority,
                authorization_receipt: read_array_v1(bytes, 172)?,
                verifier_registry: read_array_v1(bytes, 204)?,
                verifier_entry: read_array_v1(bytes, 236)?,
                verifier_profile: read_array_v1(bytes, 364)?,
                verifier_release: read_array_v1(bytes, 396)?,
                core_plan: core,
                rollover_page: page,
                rollover_shard: shard,
            };
            let mut validation = Vec::new();
            apply_prepared_plan_lifecycle_event_v1(
                &mut validation,
                &FinalizedPreparedSettlementLifecycleV1::Prepared(plan),
            )?;
            Ok(FinalizedPreparedSettlementLifecycleV1::Prepared(plan))
        }
        2 | 3 => {
            if bytes[109] != 0
                || page.is_some()
                || bytes[116..140].iter().any(|byte| *byte != 0)
                || bytes[172..268].iter().any(|byte| *byte != 0)
                || bytes[300..332].iter().any(|byte| *byte != 0)
                || bytes[364..].iter().any(|byte| *byte != 0)
            {
                return Err(DurableStateErrorV1::NonZeroReserved);
            }
            let identity = AuthenticatedPreparedSettlementPlanIdentityV1 {
                plan_authority: authority,
                core_plan: core,
                rollover_shard: shard,
            };
            if authority == [0u8; 32] || core == [0u8; 32] {
                return Err(DurableStateErrorV1::InvalidPlanLifecycle);
            }
            if bytes[108] == 2 {
                Ok(FinalizedPreparedSettlementLifecycleV1::Settled { id, plan: identity })
            } else {
                Ok(FinalizedPreparedSettlementLifecycleV1::Cancelled(
                    AuthenticatedCancelledSettlementV1 {
                        id,
                        plan_authority: authority,
                        core_plan: core,
                        rollover_shard: shard,
                    },
                ))
            }
        }
        _ => Err(DurableStateErrorV1::InvalidPlanLifecycle),
    }
}

fn encode_wallet_image_v1(
    scan_state: &ScanStateV1,
    note_cipher_id: [u8; 32],
    notes: &[StoredSealedNoteV1],
    base_prepared_plans: &[AuthenticatedPreparedSettlementV1],
    lifecycle: &[FinalizedPreparedSettlementLifecycleV1],
) -> Result<Vec<u8>, DurableStateErrorV1> {
    if note_cipher_id == [0u8; 32] {
        return Err(DurableStateErrorV1::InvalidCipherId);
    }
    if notes.len() > MAX_NOTE_RECORDS {
        return Err(DurableStateErrorV1::CountOverflow);
    }
    if base_prepared_plans.len() > MAX_PLAN_LIFECYCLE_RECORDS
        || lifecycle.len() > MAX_PLAN_LIFECYCLE_RECORDS
        || base_prepared_plans.len().saturating_add(lifecycle.len()) > MAX_PLAN_LIFECYCLE_RECORDS
    {
        return Err(DurableStateErrorV1::CountOverflow);
    }
    replay_prepared_plan_lifecycle_v1(base_prepared_plans, lifecycle)?;
    let scan = encode_scan_state_v1(scan_state)?;
    let scan_length = u64::try_from(scan.len()).map_err(|_| DurableStateErrorV1::CountOverflow)?;
    let note_count = u32::try_from(notes.len()).map_err(|_| DurableStateErrorV1::CountOverflow)?;
    let mut ordered: Vec<_> = notes.iter().collect();
    ordered.sort_by_key(|note| encode_event_id_v1(note.event_id));
    let mut output = vec![0u8; WALLET_HEADER_BYTES];
    output[..4].copy_from_slice(&WALLET_MAGIC);
    output[4] = DURABLE_VERSION;
    output[8..40].copy_from_slice(&note_cipher_id);
    output[40..48].copy_from_slice(&scan_length.to_le_bytes());
    output[48..52].copy_from_slice(&note_count.to_le_bytes());
    output.extend_from_slice(&scan);
    for note in ordered {
        if note.sealed_note.is_empty() || note.sealed_note.len() > MAX_SEALED_NOTE_BYTES {
            return Err(DurableStateErrorV1::InvalidSealedNote);
        }
        let sealed_length = u32::try_from(note.sealed_note.len())
            .map_err(|_| DurableStateErrorV1::CountOverflow)?;
        let mut header = [0u8; WALLET_RECORD_HEADER_BYTES];
        header[..108].copy_from_slice(&encode_event_id_v1(note.event_id));
        header[108] = match note.access {
            SealedNoteAccessV1::ViewOnly => 0,
            SealedNoteAccessV1::Spendable => 1,
        };
        header[109] = u8::from(note.spent.is_some());
        header[112..116].copy_from_slice(&sealed_length.to_le_bytes());
        if let Some(spent) = note.spent {
            header[116..224].copy_from_slice(&encode_event_id_v1(spent.transition_output_id));
            header[224..256].copy_from_slice(&spent.nullifier);
        }
        output.extend_from_slice(&header);
        output.extend_from_slice(&note.sealed_note);
        if output.len() > MAX_DURABLE_IMAGE_BYTES {
            return Err(DurableStateErrorV1::ImageTooLarge);
        }
    }
    if !base_prepared_plans.is_empty() || !lifecycle.is_empty() {
        let record_count = base_prepared_plans
            .len()
            .checked_add(lifecycle.len())
            .ok_or(DurableStateErrorV1::CountOverflow)?;
        let lifecycle_bytes = PLAN_LIFECYCLE_HEADER_BYTES
            .checked_add(
                record_count
                    .checked_mul(PLAN_LIFECYCLE_RECORD_BYTES)
                    .ok_or(DurableStateErrorV1::CountOverflow)?,
            )
            .ok_or(DurableStateErrorV1::CountOverflow)?;
        output[52..56].copy_from_slice(
            &u32::try_from(lifecycle_bytes)
                .map_err(|_| DurableStateErrorV1::CountOverflow)?
                .to_le_bytes(),
        );
        let mut header = [0u8; PLAN_LIFECYCLE_HEADER_BYTES];
        header[..4].copy_from_slice(b"ASPL");
        header[4] = DURABLE_VERSION;
        header[8..12].copy_from_slice(
            &u32::try_from(base_prepared_plans.len())
                .map_err(|_| DurableStateErrorV1::CountOverflow)?
                .to_le_bytes(),
        );
        header[12..16].copy_from_slice(
            &u32::try_from(lifecycle.len())
                .map_err(|_| DurableStateErrorV1::CountOverflow)?
                .to_le_bytes(),
        );
        output.extend_from_slice(&header);
        let mut base_ordered = base_prepared_plans.to_vec();
        base_ordered.sort_by_key(|plan| plan.core_plan);
        for plan in base_ordered {
            output.extend_from_slice(&encode_plan_lifecycle_record_v1(
                &FinalizedPreparedSettlementLifecycleV1::Prepared(plan),
            )?);
        }
        for event in lifecycle {
            output.extend_from_slice(&encode_plan_lifecycle_record_v1(event)?);
        }
    }
    finish_checksum_v1(WALLET_CHECKSUM_DOMAIN, &mut output)?;
    Ok(output)
}

fn decode_wallet_image_v1(
    bytes: &[u8],
) -> Result<
    (
        ScanStateV1,
        [u8; 32],
        Vec<StoredSealedNoteV1>,
        Vec<AuthenticatedPreparedSettlementV1>,
        Vec<FinalizedPreparedSettlementLifecycleV1>,
    ),
    DurableStateErrorV1,
> {
    validate_header_v1(bytes, WALLET_MAGIC, WALLET_HEADER_BYTES)?;
    verify_checksum_v1(WALLET_CHECKSUM_DOMAIN, bytes)?;
    let cipher_id = read_array_v1(bytes, 8)?;
    if cipher_id == [0u8; 32] {
        return Err(DurableStateErrorV1::InvalidCipherId);
    }
    let lifecycle_length = read_u32_v1(bytes, 52)? as usize;
    let scan_length =
        usize::try_from(read_u64_v1(bytes, 40)?).map_err(|_| DurableStateErrorV1::CountOverflow)?;
    let note_count = read_u32_v1(bytes, 48)? as usize;
    if note_count > MAX_NOTE_RECORDS {
        return Err(DurableStateErrorV1::CountOverflow);
    }
    let scan_end = WALLET_HEADER_BYTES
        .checked_add(scan_length)
        .ok_or(DurableStateErrorV1::CountOverflow)?;
    let scan_bytes = bytes
        .get(WALLET_HEADER_BYTES..scan_end)
        .ok_or(DurableStateErrorV1::Truncated)?;
    let scan_state = decode_scan_state_v1(scan_bytes)?;
    let mut notes = Vec::with_capacity(note_count);
    let mut offset = scan_end;
    let mut previous_id = None;
    for _ in 0..note_count {
        let header_end = offset
            .checked_add(WALLET_RECORD_HEADER_BYTES)
            .ok_or(DurableStateErrorV1::CountOverflow)?;
        let header = bytes
            .get(offset..header_end)
            .ok_or(DurableStateErrorV1::Truncated)?;
        if header[110..112] != [0u8; 2] {
            return Err(DurableStateErrorV1::NonZeroReserved);
        }
        let encoded_id: [u8; 108] = read_array_v1(header, 0)?;
        if previous_id.is_some_and(|previous: [u8; 108]| previous >= encoded_id) {
            return Err(DurableStateErrorV1::NonCanonicalOrder);
        }
        previous_id = Some(encoded_id);
        let event_id = decode_event_id_v1(&encoded_id)?;
        let access = match header[108] {
            0 => SealedNoteAccessV1::ViewOnly,
            1 => SealedNoteAccessV1::Spendable,
            _ => return Err(DurableStateErrorV1::InvalidSealedNote),
        };
        let spent = match header[109] {
            0 => {
                if header[116..256].iter().any(|byte| *byte != 0) {
                    return Err(DurableStateErrorV1::NonZeroReserved);
                }
                None
            }
            1 => Some(SpentNoteMarkerV1 {
                transition_output_id: decode_event_id_v1(&read_array_v1::<108>(header, 116)?)?,
                nullifier: read_array_v1(header, 224)?,
            }),
            _ => return Err(DurableStateErrorV1::InvalidSealedNote),
        };
        let sealed_length = read_u32_v1(header, 112)? as usize;
        if sealed_length == 0 || sealed_length > MAX_SEALED_NOTE_BYTES {
            return Err(DurableStateErrorV1::InvalidSealedNote);
        }
        let sealed_end = header_end
            .checked_add(sealed_length)
            .ok_or(DurableStateErrorV1::CountOverflow)?;
        let sealed_note = bytes
            .get(header_end..sealed_end)
            .ok_or(DurableStateErrorV1::Truncated)?
            .to_vec();
        notes.push(StoredSealedNoteV1 {
            event_id,
            access,
            sealed_note,
            spent,
        });
        offset = sealed_end;
    }
    let lifecycle_end = offset
        .checked_add(lifecycle_length)
        .ok_or(DurableStateErrorV1::CountOverflow)?;
    if lifecycle_end != bytes.len() {
        return Err(if lifecycle_end < bytes.len() {
            DurableStateErrorV1::TrailingBytes
        } else {
            DurableStateErrorV1::Truncated
        });
    }
    if lifecycle_length == 0 {
        return Ok((scan_state, cipher_id, notes, Vec::new(), Vec::new()));
    }
    let header_end = offset
        .checked_add(PLAN_LIFECYCLE_HEADER_BYTES)
        .ok_or(DurableStateErrorV1::CountOverflow)?;
    let header = bytes
        .get(offset..header_end)
        .ok_or(DurableStateErrorV1::Truncated)?;
    if header[..4] != *b"ASPL" {
        return Err(DurableStateErrorV1::WrongMagic);
    }
    if header[4] != DURABLE_VERSION {
        return Err(DurableStateErrorV1::WrongVersion);
    }
    if header[5..8] != [0u8; 3] {
        return Err(DurableStateErrorV1::NonZeroReserved);
    }
    let base_count = read_u32_v1(header, 8)? as usize;
    let event_count = read_u32_v1(header, 12)? as usize;
    if base_count.saturating_add(event_count) > MAX_PLAN_LIFECYCLE_RECORDS
        || lifecycle_length
            != PLAN_LIFECYCLE_HEADER_BYTES
                + (base_count + event_count) * PLAN_LIFECYCLE_RECORD_BYTES
    {
        return Err(DurableStateErrorV1::CountOverflow);
    }
    offset = header_end;
    let mut base = Vec::with_capacity(base_count);
    let mut previous_core = None;
    for _ in 0..base_count {
        let end = offset + PLAN_LIFECYCLE_RECORD_BYTES;
        let event = decode_plan_lifecycle_record_v1(
            bytes
                .get(offset..end)
                .ok_or(DurableStateErrorV1::Truncated)?,
        )?;
        let FinalizedPreparedSettlementLifecycleV1::Prepared(plan) = event else {
            return Err(DurableStateErrorV1::InvalidPlanLifecycle);
        };
        if previous_core.is_some_and(|core| core >= plan.core_plan) {
            return Err(DurableStateErrorV1::NonCanonicalOrder);
        }
        previous_core = Some(plan.core_plan);
        base.push(plan);
        offset = end;
    }
    let mut lifecycle = Vec::with_capacity(event_count);
    for _ in 0..event_count {
        let end = offset + PLAN_LIFECYCLE_RECORD_BYTES;
        lifecycle.push(decode_plan_lifecycle_record_v1(
            bytes
                .get(offset..end)
                .ok_or(DurableStateErrorV1::Truncated)?,
        )?);
        offset = end;
    }
    replay_prepared_plan_lifecycle_v1(&base, &lifecycle)?;
    Ok((scan_state, cipher_id, notes, base, lifecycle))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DurableRelayerStatusV1 {
    Queued,
    Inflight,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DurableRelayerEntryV1 {
    pub plan: RelayerPlanV1,
    pub admission: RelayerAdmissionV1,
    pub status: DurableRelayerStatusV1,
}

pub struct DurableRelayerStateV1 {
    file: AtomicStateFileV1,
    policy_id: [u8; 32],
    rate_window_start_slot: u64,
    admissions_in_window: u32,
    entries: Vec<DurableRelayerEntryV1>,
}

impl DurableRelayerStateV1 {
    pub fn open_or_create_v1(
        path: impl AsRef<Path>,
        policy: RelayerPolicyV1,
    ) -> Result<Self, DurableStateErrorV1> {
        validate_policy_shape_v1(policy)?;
        let policy_id = relayer_policy_id_v1(policy);
        let file = AtomicStateFileV1::acquire(path.as_ref())?;
        if let Some(bytes) = file.read_optional()? {
            let (stored_policy_id, rate_window_start_slot, admissions_in_window, entries) =
                decode_relayer_image_v1(&bytes)?;
            if stored_policy_id != policy_id {
                return Err(DurableStateErrorV1::PolicyMismatch);
            }
            validate_relayer_state_v1(
                policy,
                rate_window_start_slot,
                admissions_in_window,
                &entries,
            )?;
            return Ok(Self {
                file,
                policy_id,
                rate_window_start_slot,
                admissions_in_window,
                entries,
            });
        }
        let bytes = encode_relayer_image_v1(policy_id, 0, 0, &[])?;
        file.replace(&bytes)?;
        Ok(Self {
            file,
            policy_id,
            rate_window_start_slot: 0,
            admissions_in_window: 0,
            entries: Vec::new(),
        })
    }

    pub fn entries(&self) -> &[DurableRelayerEntryV1] {
        &self.entries
    }

    pub fn rate_window(&self) -> (u64, u32) {
        (self.rate_window_start_slot, self.admissions_in_window)
    }

    /// Apply an operator-authenticated policy revision. Historical admission
    /// records retain the policy hash under which they entered the queue.
    pub fn update_policy_v1(
        &mut self,
        current_policy: RelayerPolicyV1,
        new_policy: RelayerPolicyV1,
    ) -> Result<(), DurableStateErrorV1> {
        if relayer_policy_id_v1(current_policy) != self.policy_id {
            return Err(DurableStateErrorV1::PolicyMismatch);
        }
        validate_policy_shape_v1(new_policy)?;
        validate_relayer_state_v1(
            new_policy,
            self.rate_window_start_slot,
            self.admissions_in_window,
            &self.entries,
        )?;
        let new_policy_id = relayer_policy_id_v1(new_policy);
        let bytes = encode_relayer_image_v1(
            new_policy_id,
            self.rate_window_start_slot,
            self.admissions_in_window,
            &self.entries,
        )?;
        self.file.replace(&bytes)?;
        self.policy_id = new_policy_id;
        Ok(())
    }

    pub fn admit_and_enqueue_v1(
        &mut self,
        policy: RelayerPolicyV1,
        now_slot: u64,
        estimated_fee_lamports: u64,
        fee_payer_balance_lamports: u64,
        plan: &RelayerPlanV1,
    ) -> Result<RelayerEnqueueOutcomeV1, DurableStateErrorV1> {
        if relayer_policy_id_v1(policy) != self.policy_id {
            return Err(DurableStateErrorV1::PolicyMismatch);
        }
        if policy.paused {
            return Err(DurableStateErrorV1::Admission(
                RelayerAdmissionErrorV1::Paused,
            ));
        }
        if let Some(existing) = self
            .entries
            .iter()
            .find(|entry| entry.plan.request_id == plan.request_id)
        {
            return if existing.plan == *plan {
                Ok(RelayerEnqueueOutcomeV1::AlreadyPresent)
            } else {
                Err(DurableStateErrorV1::DuplicateRecord)
            };
        }
        let queue_depth = self
            .entries
            .iter()
            .filter(|entry| entry.status == DurableRelayerStatusV1::Queued)
            .count();
        let inflight = self
            .entries
            .iter()
            .filter(|entry| entry.status == DurableRelayerStatusV1::Inflight)
            .count();
        let context = RelayerAdmissionContextV1 {
            now_slot,
            queue_depth: u32::try_from(queue_depth)
                .map_err(|_| DurableStateErrorV1::CountOverflow)?,
            inflight: u32::try_from(inflight).map_err(|_| DurableStateErrorV1::CountOverflow)?,
            rate_window_start_slot: self.rate_window_start_slot,
            admissions_in_window: self.admissions_in_window,
            estimated_fee_lamports,
            fee_payer_balance_lamports,
        };
        let admission = admit_relayer_plan_v1(policy, context, plan)?;
        if self.entries.len() >= MAX_RELAYER_RECORDS {
            return Err(DurableStateErrorV1::CountOverflow);
        }
        let mut entries = self.entries.clone();
        entries.push(DurableRelayerEntryV1 {
            plan: plan.clone(),
            admission,
            status: DurableRelayerStatusV1::Queued,
        });
        let bytes = encode_relayer_image_v1(
            self.policy_id,
            admission.rate_window_start_slot,
            admission.admissions_in_window_after,
            &entries,
        )?;
        self.file.replace(&bytes)?;
        self.rate_window_start_slot = admission.rate_window_start_slot;
        self.admissions_in_window = admission.admissions_in_window_after;
        self.entries = entries;
        Ok(RelayerEnqueueOutcomeV1::Inserted)
    }

    pub fn mark_inflight_v1(
        &mut self,
        policy: RelayerPolicyV1,
        request_id: [u8; 32],
        now_slot: u64,
        estimated_fee_lamports: u64,
        fee_payer_balance_lamports: u64,
    ) -> Result<(), DurableStateErrorV1> {
        if relayer_policy_id_v1(policy) != self.policy_id {
            return Err(DurableStateErrorV1::PolicyMismatch);
        }
        if policy.paused {
            return Err(DurableStateErrorV1::Admission(
                RelayerAdmissionErrorV1::Paused,
            ));
        }
        let inflight = self
            .entries
            .iter()
            .filter(|entry| entry.status == DurableRelayerStatusV1::Inflight)
            .count();
        if inflight >= policy.max_inflight as usize {
            return Err(DurableStateErrorV1::Admission(
                RelayerAdmissionErrorV1::InflightFull,
            ));
        }
        let mut entries = self.entries.clone();
        let entry = entries
            .iter_mut()
            .find(|entry| entry.plan.request_id == request_id)
            .ok_or(DurableStateErrorV1::InvalidQueueTransition)?;
        if entry.status != DurableRelayerStatusV1::Queued {
            return Err(DurableStateErrorV1::InvalidQueueTransition);
        }
        validate_execution_context_v1(
            policy,
            &entry.plan,
            now_slot,
            estimated_fee_lamports,
            fee_payer_balance_lamports,
        )?;
        entry.status = DurableRelayerStatusV1::Inflight;
        self.persist_entries_v1(entries)
    }

    pub fn cancel_queued_v1(&mut self, request_id: [u8; 32]) -> Result<(), DurableStateErrorV1> {
        let index = self
            .entries
            .iter()
            .position(|entry| entry.plan.request_id == request_id)
            .ok_or(DurableStateErrorV1::InvalidQueueTransition)?;
        if self.entries[index].status != DurableRelayerStatusV1::Queued {
            return Err(DurableStateErrorV1::InvalidQueueTransition);
        }
        let mut entries = self.entries.clone();
        entries.remove(index);
        self.persist_entries_v1(entries)
    }

    pub fn requeue_inflight_v1(&mut self, request_id: [u8; 32]) -> Result<(), DurableStateErrorV1> {
        let mut entries = self.entries.clone();
        let entry = entries
            .iter_mut()
            .find(|entry| entry.plan.request_id == request_id)
            .ok_or(DurableStateErrorV1::InvalidQueueTransition)?;
        if entry.status != DurableRelayerStatusV1::Inflight {
            return Err(DurableStateErrorV1::InvalidQueueTransition);
        }
        entry.status = DurableRelayerStatusV1::Queued;
        self.persist_entries_v1(entries)
    }

    pub fn complete_inflight_v1(
        &mut self,
        request_id: [u8; 32],
    ) -> Result<(), DurableStateErrorV1> {
        let index = self
            .entries
            .iter()
            .position(|entry| entry.plan.request_id == request_id)
            .ok_or(DurableStateErrorV1::InvalidQueueTransition)?;
        if self.entries[index].status != DurableRelayerStatusV1::Inflight {
            return Err(DurableStateErrorV1::InvalidQueueTransition);
        }
        let mut entries = self.entries.clone();
        entries.remove(index);
        self.persist_entries_v1(entries)
    }

    fn persist_entries_v1(
        &mut self,
        entries: Vec<DurableRelayerEntryV1>,
    ) -> Result<(), DurableStateErrorV1> {
        let bytes = encode_relayer_image_v1(
            self.policy_id,
            self.rate_window_start_slot,
            self.admissions_in_window,
            &entries,
        )?;
        self.file.replace(&bytes)?;
        self.entries = entries;
        Ok(())
    }
}

fn validate_relayer_state_v1(
    policy: RelayerPolicyV1,
    rate_window_start_slot: u64,
    admissions_in_window: u32,
    entries: &[DurableRelayerEntryV1],
) -> Result<(), DurableStateErrorV1> {
    if entries.len() > MAX_RELAYER_RECORDS
        || admissions_in_window > policy.max_admissions_per_window
    {
        return Err(DurableStateErrorV1::InvalidRelayerState);
    }
    let queue = entries
        .iter()
        .filter(|entry| entry.status == DurableRelayerStatusV1::Queued)
        .count();
    let inflight = entries.len() - queue;
    if queue > policy.max_queue_depth as usize || inflight > policy.max_inflight as usize {
        return Err(DurableStateErrorV1::InvalidRelayerState);
    }
    let mut ids = HashSet::with_capacity(entries.len());
    for entry in entries {
        if !ids.insert(entry.plan.request_id)
            || entry.admission.request_id != entry.plan.request_id
            || entry.admission.policy_id == [0u8; 32]
            || entry.admission.kind != entry.plan.kind
            || entry.admission.rate_window_start_slot > entry.admission.admitted_at_slot
            || entry.admission.admissions_in_window_after == 0
            || (entry.admission.rate_window_start_slot == rate_window_start_slot
                && entry.admission.admissions_in_window_after > admissions_in_window)
        {
            return Err(DurableStateErrorV1::InvalidRelayerState);
        }
        let rebuilt = match entry.plan.prepared_plan {
            Some(context) => prepare_permissionless_prepared_relayer_plan_v1(
                entry.plan.snapshot,
                entry.plan.fee_payer,
                &context,
                &entry.plan.instruction,
            )?,
            None => prepare_permissionless_relayer_plan_v1(
                entry.plan.snapshot,
                entry.plan.fee_payer,
                &entry.plan.instruction,
            )?,
        };
        if rebuilt != entry.plan {
            return Err(DurableStateErrorV1::InvalidRelayerState);
        }
    }
    Ok(())
}

fn policy_allows_kind_v1(policy: RelayerPolicyV1, kind: RelayerRequestKindV1) -> bool {
    match kind {
        RelayerRequestKindV1::Initialize => policy.allow_initialize,
        RelayerRequestKindV1::Deposit => policy.allow_deposit,
        RelayerRequestKindV1::PrepareSettlement => policy.allow_prepare_settlement,
        RelayerRequestKindV1::SettlePrepared => policy.allow_settle_prepared,
        RelayerRequestKindV1::CancelPrepared => policy.allow_cancel_prepared,
        RelayerRequestKindV1::PrivateTransfer => policy.allow_private_transfer,
        RelayerRequestKindV1::Withdrawal => policy.allow_withdrawal,
    }
}

fn validate_execution_context_v1(
    policy: RelayerPolicyV1,
    plan: &RelayerPlanV1,
    now_slot: u64,
    estimated_fee_lamports: u64,
    fee_payer_balance_lamports: u64,
) -> Result<(), DurableStateErrorV1> {
    if plan.fee_payer != policy.operator_fee_payer {
        return Err(DurableStateErrorV1::Admission(
            RelayerAdmissionErrorV1::WrongFeePayer,
        ));
    }
    if !policy_allows_kind_v1(policy, plan.kind) {
        return Err(DurableStateErrorV1::Admission(
            RelayerAdmissionErrorV1::InstructionKindDisabled,
        ));
    }
    if plan.snapshot.observed_slot > now_slot {
        return Err(DurableStateErrorV1::Admission(
            RelayerAdmissionErrorV1::FutureSnapshot,
        ));
    }
    if now_slot - plan.snapshot.observed_slot > policy.max_snapshot_age_slots {
        return Err(DurableStateErrorV1::Admission(
            RelayerAdmissionErrorV1::StaleSnapshot,
        ));
    }
    if estimated_fee_lamports > policy.max_estimated_fee_lamports {
        return Err(DurableStateErrorV1::Admission(
            RelayerAdmissionErrorV1::FeeEstimateTooHigh,
        ));
    }
    let required = policy
        .minimum_fee_payer_reserve_lamports
        .checked_add(estimated_fee_lamports)
        .ok_or(DurableStateErrorV1::Admission(
            RelayerAdmissionErrorV1::InsufficientFeeReserve,
        ))?;
    if fee_payer_balance_lamports < required {
        return Err(DurableStateErrorV1::Admission(
            RelayerAdmissionErrorV1::InsufficientFeeReserve,
        ));
    }
    if plan.kind != RelayerRequestKindV1::Deposit {
        let mut signers = plan
            .instruction
            .accounts
            .iter()
            .filter(|account| account.is_signer);
        if !matches!(signers.next(), Some(account) if account.pubkey == plan.fee_payer)
            || signers.next().is_some()
        {
            return Err(DurableStateErrorV1::Admission(
                RelayerAdmissionErrorV1::OperatorSignerMismatch,
            ));
        }
    }
    Ok(())
}

fn validate_policy_shape_v1(policy: RelayerPolicyV1) -> Result<(), DurableStateErrorV1> {
    if policy.operator_fee_payer == Pubkey::default()
        || policy.max_snapshot_age_slots == 0
        || policy.max_queue_depth == 0
        || policy.max_inflight == 0
        || policy.rate_window_slots == 0
        || policy.max_admissions_per_window == 0
    {
        return Err(DurableStateErrorV1::Admission(
            RelayerAdmissionErrorV1::InvalidPolicy,
        ));
    }
    Ok(())
}

fn encode_relayer_prepared_plan_context_v1(
    context: crate::transaction_builder::PreparedSettlementValidationContextV1,
) -> [u8; RELAYER_PREPARED_PLAN_CONTEXT_BYTES] {
    let mut bytes = [0u8; RELAYER_PREPARED_PLAN_CONTEXT_BYTES];
    bytes[0] = context.transition_kind as u8;
    bytes[1] =
        u8::from(context.rollover_shard.is_some()) | (u8::from(context.asset_mint.is_some()) << 1);
    bytes[8..16].copy_from_slice(&context.source_root_sequence.to_le_bytes());
    bytes[16..48].copy_from_slice(context.plan_authority.as_ref());
    bytes[48..80].copy_from_slice(context.authorization_receipt.as_ref());
    bytes[80..112].copy_from_slice(&context.verifier_profile);
    bytes[112..144].copy_from_slice(&context.verifier_release);
    bytes[144..176].copy_from_slice(context.core_plan.as_ref());
    if let Some(shard) = context.rollover_shard {
        bytes[176..208].copy_from_slice(shard.as_ref());
    }
    if let Some(mint) = context.asset_mint {
        bytes[208..240].copy_from_slice(mint.as_ref());
    }
    bytes
}

fn decode_relayer_prepared_plan_context_v1(
    bytes: &[u8],
) -> Result<crate::transaction_builder::PreparedSettlementValidationContextV1, DurableStateErrorV1>
{
    if bytes.len() != RELAYER_PREPARED_PLAN_CONTEXT_BYTES {
        return Err(DurableStateErrorV1::Truncated);
    }
    if bytes[1] & !3 != 0 || bytes[2..8].iter().any(|byte| *byte != 0) {
        return Err(DurableStateErrorV1::NonZeroReserved);
    }
    let transition_kind = match bytes[0] {
        1 => aspis_statement::pool_v1::PoolV1TransitionKind::PrivateTransfer,
        2 => aspis_statement::pool_v1::PoolV1TransitionKind::Withdrawal,
        _ => return Err(DurableStateErrorV1::InvalidRelayerState),
    };
    let rollover_shard = (bytes[1] & 1 != 0)
        .then(|| read_array_v1(bytes, 176).map(Pubkey::new_from_array))
        .transpose()?;
    let asset_mint = (bytes[1] & 2 != 0)
        .then(|| read_array_v1(bytes, 208).map(Pubkey::new_from_array))
        .transpose()?;
    if rollover_shard.is_none() && bytes[176..208].iter().any(|byte| *byte != 0)
        || asset_mint.is_none() && bytes[208..240].iter().any(|byte| *byte != 0)
    {
        return Err(DurableStateErrorV1::NonZeroReserved);
    }
    Ok(
        crate::transaction_builder::PreparedSettlementValidationContextV1 {
            transition_kind,
            source_root_sequence: read_u64_v1(bytes, 8)?,
            plan_authority: Pubkey::new_from_array(read_array_v1(bytes, 16)?),
            authorization_receipt: Pubkey::new_from_array(read_array_v1(bytes, 48)?),
            verifier_profile: read_array_v1(bytes, 80)?,
            verifier_release: read_array_v1(bytes, 112)?,
            core_plan: Pubkey::new_from_array(read_array_v1(bytes, 144)?),
            rollover_shard,
            asset_mint,
        },
    )
}

fn encode_relayer_image_v1(
    policy_id: [u8; 32],
    rate_window_start_slot: u64,
    admissions_in_window: u32,
    entries: &[DurableRelayerEntryV1],
) -> Result<Vec<u8>, DurableStateErrorV1> {
    let entry_count =
        u32::try_from(entries.len()).map_err(|_| DurableStateErrorV1::CountOverflow)?;
    let mut output = vec![0u8; RELAYER_HEADER_BYTES];
    output[..4].copy_from_slice(&RELAYER_MAGIC);
    output[4] = DURABLE_VERSION;
    output[8..40].copy_from_slice(&policy_id);
    output[40..48].copy_from_slice(&rate_window_start_slot.to_le_bytes());
    output[48..52].copy_from_slice(&admissions_in_window.to_le_bytes());
    output[52..56].copy_from_slice(&entry_count.to_le_bytes());
    for entry in entries {
        let account_count = u32::try_from(entry.plan.instruction.accounts.len())
            .map_err(|_| DurableStateErrorV1::CountOverflow)?;
        let data_length = u32::try_from(entry.plan.instruction.data.len())
            .map_err(|_| DurableStateErrorV1::CountOverflow)?;
        if account_count as usize > MAX_RELAYER_ACCOUNTS
            || data_length as usize > MAX_RELAYER_INSTRUCTION_BYTES
        {
            return Err(DurableStateErrorV1::InvalidRelayerState);
        }
        let mut header = [0u8; RELAYER_RECORD_HEADER_BYTES];
        header[..32].copy_from_slice(&entry.plan.request_id);
        header[32] = encode_kind_v1(entry.plan.kind);
        header[33] = match entry.status {
            DurableRelayerStatusV1::Queued => 0,
            DurableRelayerStatusV1::Inflight => 1,
        };
        header[34] = u8::from(entry.plan.prepared_plan.is_some());
        header[36..68].copy_from_slice(entry.plan.snapshot.pinned_program_id.as_ref());
        header[68..100].copy_from_slice(entry.plan.snapshot.registry_program.as_ref());
        header[100..108].copy_from_slice(&entry.plan.snapshot.current_root_sequence.to_le_bytes());
        header[108..116].copy_from_slice(&entry.plan.snapshot.observed_slot.to_le_bytes());
        header[116..148].copy_from_slice(&entry.plan.snapshot.pool_state_sha256);
        header[148..180].copy_from_slice(entry.plan.fee_payer.as_ref());
        header[180..212].copy_from_slice(entry.plan.instruction.program_id.as_ref());
        header[212..216].copy_from_slice(&account_count.to_le_bytes());
        header[216..220].copy_from_slice(&data_length.to_le_bytes());
        header[220..252].copy_from_slice(&entry.admission.policy_id);
        header[252..260].copy_from_slice(&entry.admission.admitted_at_slot.to_le_bytes());
        header[260..268].copy_from_slice(&entry.admission.rate_window_start_slot.to_le_bytes());
        header[268..272].copy_from_slice(&entry.admission.admissions_in_window_after.to_le_bytes());
        output.extend_from_slice(&header);
        for account in &entry.plan.instruction.accounts {
            output.extend_from_slice(account.pubkey.as_ref());
            output.push(u8::from(account.is_signer));
            output.push(u8::from(account.is_writable));
        }
        output.extend_from_slice(&entry.plan.instruction.data);
        if let Some(context) = entry.plan.prepared_plan {
            output.extend_from_slice(&encode_relayer_prepared_plan_context_v1(context));
        }
        if output.len() > MAX_DURABLE_IMAGE_BYTES {
            return Err(DurableStateErrorV1::ImageTooLarge);
        }
    }
    finish_checksum_v1(RELAYER_CHECKSUM_DOMAIN, &mut output)?;
    Ok(output)
}

fn decode_relayer_image_v1(
    bytes: &[u8],
) -> Result<([u8; 32], u64, u32, Vec<DurableRelayerEntryV1>), DurableStateErrorV1> {
    validate_header_v1(bytes, RELAYER_MAGIC, RELAYER_HEADER_BYTES)?;
    verify_checksum_v1(RELAYER_CHECKSUM_DOMAIN, bytes)?;
    let policy_id = read_array_v1(bytes, 8)?;
    let rate_window_start_slot = read_u64_v1(bytes, 40)?;
    let admissions_in_window = read_u32_v1(bytes, 48)?;
    let entry_count = read_u32_v1(bytes, 52)? as usize;
    if entry_count > MAX_RELAYER_RECORDS {
        return Err(DurableStateErrorV1::CountOverflow);
    }
    let mut offset = RELAYER_HEADER_BYTES;
    let mut entries = Vec::with_capacity(entry_count);
    for _ in 0..entry_count {
        let header_end = offset
            .checked_add(RELAYER_RECORD_HEADER_BYTES)
            .ok_or(DurableStateErrorV1::CountOverflow)?;
        let header = bytes
            .get(offset..header_end)
            .ok_or(DurableStateErrorV1::Truncated)?;
        let has_prepared_plan = match header[34] {
            0 => false,
            1 => true,
            _ => return Err(DurableStateErrorV1::InvalidRelayerState),
        };
        if header[35] != 0 || header[272..276] != [0u8; 4] {
            return Err(DurableStateErrorV1::NonZeroReserved);
        }
        let kind = decode_kind_v1(header[32])?;
        let status = match header[33] {
            0 => DurableRelayerStatusV1::Queued,
            1 => DurableRelayerStatusV1::Inflight,
            _ => return Err(DurableStateErrorV1::InvalidRelayerState),
        };
        let account_count = read_u32_v1(header, 212)? as usize;
        let data_length = read_u32_v1(header, 216)? as usize;
        if account_count > MAX_RELAYER_ACCOUNTS || data_length > MAX_RELAYER_INSTRUCTION_BYTES {
            return Err(DurableStateErrorV1::InvalidRelayerState);
        }
        let accounts_bytes = account_count
            .checked_mul(34)
            .ok_or(DurableStateErrorV1::CountOverflow)?;
        let record_end = header_end
            .checked_add(accounts_bytes)
            .and_then(|end| end.checked_add(data_length))
            .and_then(|end| {
                end.checked_add(if has_prepared_plan {
                    RELAYER_PREPARED_PLAN_CONTEXT_BYTES
                } else {
                    0
                })
            })
            .ok_or(DurableStateErrorV1::CountOverflow)?;
        let body = bytes
            .get(header_end..record_end)
            .ok_or(DurableStateErrorV1::Truncated)?;
        let mut accounts = Vec::with_capacity(account_count);
        for chunk in body[..accounts_bytes].chunks_exact(34) {
            let pubkey = Pubkey::new_from_array(read_array_v1(chunk, 0)?);
            let is_signer = decode_bool_v1(chunk[32])?;
            let is_writable = decode_bool_v1(chunk[33])?;
            accounts.push(match (is_signer, is_writable) {
                (true, true) => AccountMeta::new(pubkey, true),
                (true, false) => AccountMeta::new_readonly(pubkey, true),
                (false, true) => AccountMeta::new(pubkey, false),
                (false, false) => AccountMeta::new_readonly(pubkey, false),
            });
        }
        let snapshot = crate::relayer::RelayerSnapshotV1 {
            pinned_program_id: Pubkey::new_from_array(read_array_v1(header, 36)?),
            registry_program: Pubkey::new_from_array(read_array_v1(header, 68)?),
            current_root_sequence: read_u64_v1(header, 100)?,
            observed_slot: read_u64_v1(header, 108)?,
            pool_state_sha256: read_array_v1(header, 116)?,
        };
        let data_end = accounts_bytes + data_length;
        let prepared_plan = if has_prepared_plan {
            Some(decode_relayer_prepared_plan_context_v1(&body[data_end..])?)
        } else {
            None
        };
        let plan = RelayerPlanV1 {
            request_id: read_array_v1(header, 0)?,
            kind,
            snapshot,
            fee_payer: Pubkey::new_from_array(read_array_v1(header, 148)?),
            prepared_plan,
            instruction: Instruction {
                program_id: Pubkey::new_from_array(read_array_v1(header, 180)?),
                accounts,
                data: body[accounts_bytes..data_end].to_vec(),
            },
        };
        let admission = RelayerAdmissionV1 {
            request_id: plan.request_id,
            policy_id: read_array_v1(header, 220)?,
            kind,
            admitted_at_slot: read_u64_v1(header, 252)?,
            rate_window_start_slot: read_u64_v1(header, 260)?,
            admissions_in_window_after: read_u32_v1(header, 268)?,
        };
        entries.push(DurableRelayerEntryV1 {
            plan,
            admission,
            status,
        });
        offset = record_end;
    }
    if offset != bytes.len() {
        return Err(DurableStateErrorV1::TrailingBytes);
    }
    Ok((
        policy_id,
        rate_window_start_slot,
        admissions_in_window,
        entries,
    ))
}

fn validate_header_v1(
    bytes: &[u8],
    magic: [u8; 4],
    header_bytes: usize,
) -> Result<(), DurableStateErrorV1> {
    if bytes.len() < header_bytes {
        return Err(DurableStateErrorV1::Truncated);
    }
    if bytes[..4] != magic {
        return Err(DurableStateErrorV1::WrongMagic);
    }
    if bytes[4] != DURABLE_VERSION {
        return Err(DurableStateErrorV1::WrongVersion);
    }
    if bytes[5..8] != [0u8; 3] {
        return Err(DurableStateErrorV1::NonZeroReserved);
    }
    if bytes.len() > MAX_DURABLE_IMAGE_BYTES {
        return Err(DurableStateErrorV1::ImageTooLarge);
    }
    Ok(())
}

fn encode_kind_v1(kind: RelayerRequestKindV1) -> u8 {
    match kind {
        RelayerRequestKindV1::Initialize => 0,
        RelayerRequestKindV1::Deposit => 1,
        RelayerRequestKindV1::PrivateTransfer => 2,
        RelayerRequestKindV1::Withdrawal => 3,
        RelayerRequestKindV1::PrepareSettlement => 4,
        RelayerRequestKindV1::SettlePrepared => 5,
        RelayerRequestKindV1::CancelPrepared => 6,
    }
}

fn decode_kind_v1(byte: u8) -> Result<RelayerRequestKindV1, DurableStateErrorV1> {
    match byte {
        0 => Ok(RelayerRequestKindV1::Initialize),
        1 => Ok(RelayerRequestKindV1::Deposit),
        2 => Ok(RelayerRequestKindV1::PrivateTransfer),
        3 => Ok(RelayerRequestKindV1::Withdrawal),
        4 => Ok(RelayerRequestKindV1::PrepareSettlement),
        5 => Ok(RelayerRequestKindV1::SettlePrepared),
        6 => Ok(RelayerRequestKindV1::CancelPrepared),
        _ => Err(DurableStateErrorV1::InvalidRelayerState),
    }
}

fn decode_bool_v1(byte: u8) -> Result<bool, DurableStateErrorV1> {
    match byte {
        0 => Ok(false),
        1 => Ok(true),
        _ => Err(DurableStateErrorV1::InvalidRelayerState),
    }
}

fn encode_event_id_v1(id: DepositEventIdV1) -> [u8; 108] {
    let mut bytes = [0u8; 108];
    bytes[..8].copy_from_slice(&id.point().slot().to_le_bytes());
    bytes[8..40].copy_from_slice(id.point().block_hash());
    bytes[40..104].copy_from_slice(id.transaction_signature());
    bytes[104..106].copy_from_slice(&id.instruction_index().to_le_bytes());
    bytes[106..108].copy_from_slice(&id.event_index().to_le_bytes());
    bytes
}

fn decode_event_id_v1(bytes: &[u8; 108]) -> Result<DepositEventIdV1, DurableStateErrorV1> {
    let point = FinalizedChainPointV1::new(read_u64_v1(bytes, 0)?, read_array_v1(bytes, 8)?)?;
    Ok(DepositEventIdV1::new(
        point,
        read_array_v1(bytes, 40)?,
        read_u16_v1(bytes, 104)?,
        read_u16_v1(bytes, 106)?,
    )?)
}

fn read_u16_v1(bytes: &[u8], offset: usize) -> Result<u16, DurableStateErrorV1> {
    Ok(u16::from_le_bytes(read_array_v1(bytes, offset)?))
}

fn read_u32_v1(bytes: &[u8], offset: usize) -> Result<u32, DurableStateErrorV1> {
    Ok(u32::from_le_bytes(read_array_v1(bytes, offset)?))
}

fn read_u64_v1(bytes: &[u8], offset: usize) -> Result<u64, DurableStateErrorV1> {
    Ok(u64::from_le_bytes(read_array_v1(bytes, offset)?))
}

fn read_array_v1<const N: usize>(
    bytes: &[u8],
    offset: usize,
) -> Result<[u8; N], DurableStateErrorV1> {
    bytes
        .get(
            offset
                ..offset
                    .checked_add(N)
                    .ok_or(DurableStateErrorV1::CountOverflow)?,
        )
        .ok_or(DurableStateErrorV1::Truncated)?
        .try_into()
        .map_err(|_| DurableStateErrorV1::Truncated)
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::convert::Infallible;
    use std::{
        fs,
        path::PathBuf,
        sync::atomic::{AtomicU64, Ordering},
    };

    use aspis_core::field::M31;
    use aspis_pool::{
        deposit::DepositRequestV1, pool_v1_state_address, TransitionReceiptV1,
        WithdrawalStatementV1,
    };
    use aspis_statement::{
        encode_digest_canonical,
        pool_v1::{HistoricalAnchorEnvelopeV1, PoolV1TransitionKind},
        poseidon2::Digest,
    };
    use hpke::rand_core::{TryCryptoRng, TryRng};

    use crate::{
        finalized_indexer::{
            FinalizedAppendEvidenceV1, FinalizedTransitionEvidenceV1, HistoricalRootEvidenceV1,
        },
        note_store_crypto::{
            open_note_opening_v1, rotate_wallet_note_store_key_v1, seal_recovered_note_v1,
            NoteStoreCipherV1, NoteStoreCryptoErrorV1,
        },
        scan_state::{
            DepositScanIdentityV1, FinalizedBlockAdvanceV1, FinalizedBlockV1,
            FinalizedPublicOutputRecordV1,
        },
        transaction_builder::{
            build_deposit_instruction_v1, build_prepare_withdrawal_instruction_v1,
            build_settle_prepared_withdrawal_instruction_v1, PreparedSettlementRouteAccountsV1,
            PreparedSettlementValidationContextV1,
        },
        NoteOpeningV1,
    };

    static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

    struct FixedTestRng(u8);

    impl TryRng for FixedTestRng {
        type Error = Infallible;

        fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
            let mut bytes = [0u8; 4];
            self.try_fill_bytes(&mut bytes)?;
            Ok(u32::from_le_bytes(bytes))
        }

        fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
            let mut bytes = [0u8; 8];
            self.try_fill_bytes(&mut bytes)?;
            Ok(u64::from_le_bytes(bytes))
        }

        fn try_fill_bytes(&mut self, destination: &mut [u8]) -> Result<(), Self::Error> {
            for byte in destination {
                *byte = self.0;
                self.0 = self.0.wrapping_add(1);
            }
            Ok(())
        }
    }

    impl TryCryptoRng for FixedTestRng {}

    struct TestDirectory(PathBuf);

    impl TestDirectory {
        fn new() -> Self {
            let sequence = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "aspis-pool-wallet-v1-{}-{sequence}",
                std::process::id()
            ));
            fs::create_dir(&path).unwrap();
            Self(path)
        }

        fn path(&self, name: &str) -> PathBuf {
            self.0.join(name)
        }
    }

    impl Drop for TestDirectory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    struct RejectAllSpends;

    impl LocalSpendAuthenticatorV1 for RejectAllSpends {
        fn authenticates_spend_v1(&self, _: DepositEventIdV1, _: &[u8], _: &[u8; 32]) -> bool {
            false
        }
    }

    fn key(seed: u8) -> Pubkey {
        Pubkey::new_from_array([seed; 32])
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + index as u32))
    }

    fn scan_fixture() -> ScanStateV1 {
        let identity =
            DepositScanIdentityV1::new([0x11; 32], [0x22; 32], [0x33; 32], [0x44; 32], 9).unwrap();
        ScanStateV1::new(
            identity,
            FinalizedChainPointV1::new(100, [0xa0; 32]).unwrap(),
            0,
            encode_digest_canonical(&digest(10)),
        )
        .unwrap()
    }

    fn transition_result(
        output_id: DepositEventIdV1,
        pool: [u8; 32],
        advance: FinalizedBlockAdvanceV1,
    ) -> FinalizedBlockIngestResultV1 {
        FinalizedBlockIngestResultV1 {
            advance,
            rollback: None,
            deposit_event_ids: Vec::new(),
            deposit_outcomes: Vec::new(),
            transition_outcomes: vec![PublicOutputScanOutcomeV1::Advanced],
            transition_evidence: vec![FinalizedTransitionEvidenceV1 {
                receipt: TransitionReceiptV1 {
                    transition_kind: PoolV1TransitionKind::PrivateTransfer,
                    pool,
                    nullifier: digest(70),
                    first_output: digest(20),
                    second_output_or_destination: encode_digest_canonical(&digest(30)),
                    withdrawal_amount: 0,
                    first_leaf_index: 0,
                    second_leaf_index: 0,
                    root_sequence: 1,
                    root: digest(40),
                },
                output_ids: vec![output_id],
                authenticated_transport: vec![0x71, 0x72],
                settled_plan: None,
            }],
            append_evidence: vec![FinalizedAppendEvidenceV1 {
                event_id: output_id,
                leaf_index: 0,
                root_sequence: 1,
                note_commitment: encode_digest_canonical(&digest(20)),
                root: encode_digest_canonical(&digest(40)),
            }],
            prepared_settlements: Vec::new(),
            cancelled_settlements: Vec::new(),
            plan_lifecycle: Vec::new(),
            root_evidence: vec![HistoricalRootEvidenceV1 {
                event_id: output_id,
                root_sequence: 1,
                root: encode_digest_canonical(&digest(40)),
                page_number: 0,
                page_address: [0x81; 32],
                snapshot_context_slot: output_id.point().slot(),
            }],
            ignored_failed_pool_transactions: 0,
        }
    }

    #[test]
    fn wallet_state_is_atomic_locked_restart_safe_and_reorg_reconciled() {
        let directory = TestDirectory::new();
        let path = directory.path("wallet.state");
        let initial = scan_fixture();
        let mut store =
            DurableWalletStateV1::open_or_create_v1(&path, initial.clone(), [0xc1; 32]).unwrap();
        assert_eq!(
            DurableWalletStateV1::open_or_create_v1(&path, initial.clone(), [0xc1; 32]).err(),
            Some(DurableStateErrorV1::AlreadyLocked)
        );

        let mut candidate = initial.clone();
        let point = FinalizedChainPointV1::new(101, [0xa1; 32]).unwrap();
        candidate
            .advance_finalized_block_v1(FinalizedBlockV1::new(point, initial.head()).unwrap())
            .unwrap();
        let output_id = DepositEventIdV1::new(point, [0x51; 64], 0, 0).unwrap();
        let root = encode_digest_canonical(&digest(40));
        assert_eq!(
            candidate
                .ingest_finalized_public_output_v1(FinalizedPublicOutputRecordV1 {
                    id: output_id,
                    pool: *candidate.identity().pool(),
                    leaf_index: 0,
                    root_sequence: 1,
                    note_commitment: encode_digest_canonical(&digest(20)),
                    root,
                    authenticated_transport: &[0x71, 0x72],
                })
                .unwrap(),
            PublicOutputScanOutcomeV1::Advanced
        );
        let result = transition_result(
            output_id,
            *candidate.identity().pool(),
            FinalizedBlockAdvanceV1::Advanced,
        );
        let missing_recovered = FinalizedBlockIngestResultV1 {
            advance: FinalizedBlockAdvanceV1::Advanced,
            rollback: None,
            deposit_event_ids: vec![output_id],
            deposit_outcomes: vec![DepositScanOutcomeV1::ViewOnly(
                NoteOpeningV1::new([0x31; 32], 7, 9, [0x41; 32]).unwrap(),
            )],
            transition_outcomes: Vec::new(),
            transition_evidence: Vec::new(),
            append_evidence: result.append_evidence.clone(),
            prepared_settlements: Vec::new(),
            cancelled_settlements: Vec::new(),
            plan_lifecycle: Vec::new(),
            root_evidence: result.root_evidence.clone(),
            ignored_failed_pool_transactions: 0,
        };
        assert_eq!(
            store
                .commit_finalized_ingest_v1(
                    candidate.clone(),
                    &missing_recovered,
                    &[],
                    &[],
                    &RejectAllSpends,
                )
                .err(),
            Some(DurableStateErrorV1::MissingRecoveredNote)
        );
        assert_eq!(store.scan_state(), &initial);
        assert!(store.notes().is_empty());
        store
            .commit_finalized_ingest_v1(
                candidate.clone(),
                &result,
                &[SealedRecoveredNoteV1 {
                    event_id: output_id,
                    access: SealedNoteAccessV1::Spendable,
                    sealed_note: vec![0x91, 0x92, 0x93],
                }],
                &[],
                &RejectAllSpends,
            )
            .unwrap();
        assert_eq!(store.notes().len(), 1);
        drop(store);

        let mut reopened =
            DurableWalletStateV1::open_or_create_v1(&path, initial.clone(), [0xc1; 32]).unwrap();
        assert_eq!(reopened.scan_state().head(), point);
        assert_eq!(reopened.notes()[0].sealed_note, [0x91, 0x92, 0x93]);

        let mut replacement = reopened.scan_state().clone();
        let rollback = replacement.rollback_to_v1(initial.head()).unwrap();
        let replacement_point = FinalizedChainPointV1::new(102, [0xb2; 32]).unwrap();
        replacement
            .advance_finalized_block_v1(
                FinalizedBlockV1::new(replacement_point, initial.head()).unwrap(),
            )
            .unwrap();
        let rollback_result = FinalizedBlockIngestResultV1 {
            advance: FinalizedBlockAdvanceV1::Advanced,
            rollback: Some(rollback),
            deposit_event_ids: Vec::new(),
            deposit_outcomes: Vec::new(),
            transition_outcomes: Vec::new(),
            transition_evidence: Vec::new(),
            append_evidence: Vec::new(),
            prepared_settlements: Vec::new(),
            cancelled_settlements: Vec::new(),
            plan_lifecycle: Vec::new(),
            root_evidence: Vec::new(),
            ignored_failed_pool_transactions: 0,
        };
        reopened
            .commit_finalized_ingest_v1(replacement, &rollback_result, &[], &[], &RejectAllSpends)
            .unwrap();
        assert!(reopened.notes().is_empty());
        drop(reopened);

        let mut restarted =
            DurableWalletStateV1::open_or_create_v1(&path, initial.clone(), [0xc1; 32]).unwrap();
        assert_eq!(restarted.scan_state().head(), replacement_point);
        assert!(restarted.notes().is_empty());
        let prune = restarted
            .prune_finalized_history_through_v1(replacement_point)
            .unwrap();
        assert_eq!(prune.anchor, replacement_point);
        assert_eq!(restarted.scan_state().retained_block_count(), 0);
        drop(restarted);

        let mut bytes = fs::read(&path).unwrap();
        *bytes.last_mut().unwrap() ^= 1;
        fs::write(&path, bytes).unwrap();
        assert_eq!(
            DurableWalletStateV1::open_or_create_v1(&path, initial, [0xc1; 32]).err(),
            Some(DurableStateErrorV1::ChecksumMismatch)
        );
    }

    #[test]
    fn note_store_key_rotation_is_complete_atomic_and_restart_pinned() {
        let directory = TestDirectory::new();
        let path = directory.path("wallet-rotation.state");
        let initial = scan_fixture();
        let old_cipher = NoteStoreCipherV1::from_key_bytes([0x61; 32]).unwrap();
        let new_cipher = NoteStoreCipherV1::from_key_bytes([0x62; 32]).unwrap();
        let wrong_cipher = NoteStoreCipherV1::from_key_bytes([0x63; 32]).unwrap();
        let mut store =
            DurableWalletStateV1::open_or_create_v1(&path, initial.clone(), old_cipher.cipher_id())
                .unwrap();

        let mut candidate = initial.clone();
        let point = FinalizedChainPointV1::new(101, [0xa1; 32]).unwrap();
        candidate
            .advance_finalized_block_v1(FinalizedBlockV1::new(point, initial.head()).unwrap())
            .unwrap();
        let output_id = DepositEventIdV1::new(point, [0x51; 64], 0, 0).unwrap();
        candidate
            .ingest_finalized_public_output_v1(FinalizedPublicOutputRecordV1 {
                id: output_id,
                pool: *candidate.identity().pool(),
                leaf_index: 0,
                root_sequence: 1,
                note_commitment: encode_digest_canonical(&digest(20)),
                root: encode_digest_canonical(&digest(40)),
                authenticated_transport: &[0x71, 0x72],
            })
            .unwrap();
        let note = NoteOpeningV1::new([0x31; 32], 7, 9, [0x41; 32]).unwrap();
        let sealed = seal_recovered_note_v1(
            &mut FixedTestRng(0x10),
            &old_cipher,
            output_id,
            SealedNoteAccessV1::Spendable,
            &note,
        )
        .unwrap();
        store
            .commit_finalized_ingest_v1(
                candidate.clone(),
                &transition_result(
                    output_id,
                    *candidate.identity().pool(),
                    FinalizedBlockAdvanceV1::Advanced,
                ),
                &[sealed],
                &[],
                &RejectAllSpends,
            )
            .unwrap();
        let old_sealed = store.notes()[0].sealed_note.clone();

        assert_eq!(
            rotate_wallet_note_store_key_v1(
                &mut FixedTestRng(0x40),
                &mut store,
                &wrong_cipher,
                &new_cipher,
            )
            .err(),
            Some(NoteStoreCryptoErrorV1::Durable(
                DurableStateErrorV1::CipherMismatch
            ))
        );
        assert_eq!(store.note_cipher_id(), &old_cipher.cipher_id());
        assert_eq!(store.notes()[0].sealed_note, old_sealed);

        rotate_wallet_note_store_key_v1(
            &mut FixedTestRng(0x70),
            &mut store,
            &old_cipher,
            &new_cipher,
        )
        .unwrap();
        assert_eq!(store.note_cipher_id(), &new_cipher.cipher_id());
        assert_ne!(store.notes()[0].sealed_note, old_sealed);
        assert_eq!(
            open_note_opening_v1(
                &old_cipher,
                output_id,
                SealedNoteAccessV1::Spendable,
                &store.notes()[0].sealed_note,
            )
            .err(),
            Some(NoteStoreCryptoErrorV1::AuthenticationFailed)
        );
        let opened = open_note_opening_v1(
            &new_cipher,
            output_id,
            SealedNoteAccessV1::Spendable,
            &store.notes()[0].sealed_note,
        )
        .unwrap();
        assert_eq!(opened.owner_key(), note.owner_key());
        drop(store);

        assert_eq!(
            DurableWalletStateV1::open_or_create_v1(
                &path,
                initial.clone(),
                old_cipher.cipher_id(),
            )
            .err(),
            Some(DurableStateErrorV1::CipherMismatch)
        );
        let restarted =
            DurableWalletStateV1::open_or_create_v1(&path, initial, new_cipher.cipher_id())
                .unwrap();
        assert_eq!(restarted.notes().len(), 1);
    }

    #[test]
    fn prepared_plan_lifecycle_persists_closure_and_rolls_back_atomically() {
        let directory = TestDirectory::new();
        let path = directory.path("plans.state");
        let initial = scan_fixture();
        let mut store =
            DurableWalletStateV1::open_or_create_v1(&path, initial.clone(), [0xc1; 32]).unwrap();

        let prepared_point = FinalizedChainPointV1::new(101, [0xa1; 32]).unwrap();
        let mut prepared_state = initial.clone();
        prepared_state
            .advance_finalized_block_v1(
                FinalizedBlockV1::new(prepared_point, initial.head()).unwrap(),
            )
            .unwrap();
        let prepared_id = DepositEventIdV1::new(prepared_point, [0x51; 64], 0, 0).unwrap();
        let prepared = AuthenticatedPreparedSettlementV1 {
            id: prepared_id,
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            source_root_sequence: 0,
            not_before_slot: 101,
            expires_at_slot: 120,
            plan_authority: [0x21; 32],
            authorization_receipt: [0x22; 32],
            verifier_registry: [0x23; 32],
            verifier_entry: [0x24; 32],
            verifier_profile: [0x25; 32],
            verifier_release: [0x26; 32],
            core_plan: [0x27; 32],
            rollover_page: None,
            rollover_shard: None,
        };
        let prepared_result = FinalizedBlockIngestResultV1 {
            advance: FinalizedBlockAdvanceV1::Advanced,
            rollback: None,
            deposit_event_ids: Vec::new(),
            deposit_outcomes: Vec::new(),
            transition_outcomes: Vec::new(),
            transition_evidence: Vec::new(),
            append_evidence: Vec::new(),
            prepared_settlements: vec![prepared],
            cancelled_settlements: Vec::new(),
            plan_lifecycle: vec![FinalizedPreparedSettlementLifecycleV1::Prepared(prepared)],
            root_evidence: Vec::new(),
            ignored_failed_pool_transactions: 0,
        };
        store
            .commit_finalized_ingest_v1(
                prepared_state,
                &prepared_result,
                &[],
                &[],
                &RejectAllSpends,
            )
            .unwrap();
        assert_eq!(store.active_prepared_plans(), &[prepared]);
        drop(store);

        let mut store =
            DurableWalletStateV1::open_or_create_v1(&path, initial.clone(), [0xc1; 32]).unwrap();
        assert_eq!(store.active_prepared_plans(), &[prepared]);
        let cancelled_point = FinalizedChainPointV1::new(102, [0xa2; 32]).unwrap();
        let mut cancelled_state = store.scan_state().clone();
        cancelled_state
            .advance_finalized_block_v1(
                FinalizedBlockV1::new(cancelled_point, prepared_point).unwrap(),
            )
            .unwrap();
        let cancelled = AuthenticatedCancelledSettlementV1 {
            id: DepositEventIdV1::new(cancelled_point, [0x52; 64], 0, 0).unwrap(),
            plan_authority: prepared.plan_authority,
            core_plan: prepared.core_plan,
            rollover_shard: None,
        };
        let cancelled_result = FinalizedBlockIngestResultV1 {
            advance: FinalizedBlockAdvanceV1::Advanced,
            rollback: None,
            deposit_event_ids: Vec::new(),
            deposit_outcomes: Vec::new(),
            transition_outcomes: Vec::new(),
            transition_evidence: Vec::new(),
            append_evidence: Vec::new(),
            prepared_settlements: Vec::new(),
            cancelled_settlements: vec![cancelled],
            plan_lifecycle: vec![FinalizedPreparedSettlementLifecycleV1::Cancelled(cancelled)],
            root_evidence: Vec::new(),
            ignored_failed_pool_transactions: 0,
        };
        store
            .commit_finalized_ingest_v1(
                cancelled_state,
                &cancelled_result,
                &[],
                &[],
                &RejectAllSpends,
            )
            .unwrap();
        assert!(store.active_prepared_plans().is_empty());

        let mut replacement = store.scan_state().clone();
        let rollback = replacement.rollback_to_v1(prepared_point).unwrap();
        let replacement_point = FinalizedChainPointV1::new(103, [0xb3; 32]).unwrap();
        replacement
            .advance_finalized_block_v1(
                FinalizedBlockV1::new(replacement_point, prepared_point).unwrap(),
            )
            .unwrap();
        let rollback_result = FinalizedBlockIngestResultV1 {
            advance: FinalizedBlockAdvanceV1::Advanced,
            rollback: Some(rollback),
            deposit_event_ids: Vec::new(),
            deposit_outcomes: Vec::new(),
            transition_outcomes: Vec::new(),
            transition_evidence: Vec::new(),
            append_evidence: Vec::new(),
            prepared_settlements: Vec::new(),
            cancelled_settlements: Vec::new(),
            plan_lifecycle: Vec::new(),
            root_evidence: Vec::new(),
            ignored_failed_pool_transactions: 0,
        };
        store
            .commit_finalized_ingest_v1(replacement, &rollback_result, &[], &[], &RejectAllSpends)
            .unwrap();
        assert_eq!(store.active_prepared_plans(), &[prepared]);
        drop(store);
        let restarted =
            DurableWalletStateV1::open_or_create_v1(&path, initial, [0xc1; 32]).unwrap();
        assert_eq!(restarted.active_prepared_plans(), &[prepared]);
    }

    fn relayer_fixture(amount: u32) -> (RelayerPlanV1, RelayerPolicyV1) {
        let program = key(1);
        let mint = key(2);
        let pool = pool_v1_state_address(&program, &mint).0;
        let fee_payer = key(6);
        let instruction = build_deposit_instruction_v1(
            program,
            pool,
            mint,
            7,
            key(3),
            key(4),
            None,
            &DepositRequestV1 {
                owner_key: digest(10),
                amount,
                salt: digest(20),
                encrypted_note_payload: &[],
            },
        )
        .unwrap();
        let plan = prepare_permissionless_relayer_plan_v1(
            crate::relayer::RelayerSnapshotV1 {
                pinned_program_id: program,
                registry_program: key(5),
                current_root_sequence: 7,
                observed_slot: 900,
                pool_state_sha256: [0xab; 32],
            },
            fee_payer,
            &instruction,
        )
        .unwrap();
        let policy = RelayerPolicyV1 {
            paused: false,
            operator_fee_payer: fee_payer,
            allow_initialize: false,
            allow_deposit: true,
            allow_prepare_settlement: true,
            allow_settle_prepared: true,
            allow_cancel_prepared: true,
            allow_private_transfer: true,
            allow_withdrawal: true,
            max_snapshot_age_slots: 32,
            max_queue_depth: 4,
            max_inflight: 2,
            rate_window_slots: 16,
            max_admissions_per_window: 1,
            max_estimated_fee_lamports: 10_000,
            minimum_fee_payer_reserve_lamports: 1_000_000,
        };
        (plan, policy)
    }

    fn prepared_relayer_fixture() -> (RelayerPlanV1, RelayerPolicyV1) {
        let program = key(1);
        let mint = key(2);
        let pool = pool_v1_state_address(&program, &mint).0;
        let fee_payer = key(6);
        let envelope = HistoricalAnchorEnvelopeV1 {
            transition_kind: PoolV1TransitionKind::Withdrawal,
            pool: pool.to_bytes(),
            deployment_domain: [8; 32],
            anchor_sequence: 7,
            anchor_root: digest(30),
            nullifier: digest(40),
            verifier_profile: [11; 32],
            verifier_release: [12; 32],
        };
        let statement = WithdrawalStatementV1 {
            pool: envelope.pool,
            deployment_domain: envelope.deployment_domain,
            anchor_sequence: envelope.anchor_sequence,
            anchor_root: envelope.anchor_root,
            nullifier: envelope.nullifier,
            asset_id: M31(9),
            amount: 77,
            destination_token_account: [13; 32],
            change_commitment: digest(50),
        };
        let instruction = build_prepare_withdrawal_instruction_v1(
            program,
            7,
            &envelope,
            &statement,
            910,
            930,
            PreparedSettlementRouteAccountsV1 {
                plan_authority: fee_payer,
                registry_program: key(5),
                authorization_receipt: key(10),
            },
        )
        .unwrap();
        let plan = prepare_permissionless_relayer_plan_v1(
            crate::relayer::RelayerSnapshotV1 {
                pinned_program_id: program,
                registry_program: key(5),
                current_root_sequence: 7,
                observed_slot: 900,
                pool_state_sha256: [0xab; 32],
            },
            fee_payer,
            &instruction,
        )
        .unwrap();
        let policy = RelayerPolicyV1 {
            paused: false,
            operator_fee_payer: fee_payer,
            allow_initialize: false,
            allow_deposit: false,
            allow_prepare_settlement: true,
            allow_settle_prepared: true,
            allow_cancel_prepared: true,
            allow_private_transfer: false,
            allow_withdrawal: false,
            max_snapshot_age_slots: 32,
            max_queue_depth: 4,
            max_inflight: 2,
            rate_window_slots: 16,
            max_admissions_per_window: 2,
            max_estimated_fee_lamports: 10_000,
            minimum_fee_payer_reserve_lamports: 1_000_000,
        };
        (plan, policy)
    }

    fn prepared_finalization_relayer_fixture() -> (RelayerPlanV1, RelayerPolicyV1) {
        let program = key(1);
        let mint = key(2);
        let pool = pool_v1_state_address(&program, &mint).0;
        let fee_payer = key(6);
        let envelope = HistoricalAnchorEnvelopeV1 {
            transition_kind: PoolV1TransitionKind::Withdrawal,
            pool: pool.to_bytes(),
            deployment_domain: [8; 32],
            anchor_sequence: 7,
            anchor_root: digest(30),
            nullifier: digest(40),
            verifier_profile: [11; 32],
            verifier_release: [12; 32],
        };
        let statement = WithdrawalStatementV1 {
            pool: envelope.pool,
            deployment_domain: envelope.deployment_domain,
            anchor_sequence: envelope.anchor_sequence,
            anchor_root: envelope.anchor_root,
            nullifier: envelope.nullifier,
            asset_id: M31(9),
            amount: 77,
            destination_token_account: [13; 32],
            change_commitment: digest(50),
        };
        let instruction = build_settle_prepared_withdrawal_instruction_v1(
            program,
            7,
            mint,
            &envelope,
            &statement,
            PreparedSettlementRouteAccountsV1 {
                plan_authority: fee_payer,
                registry_program: key(5),
                authorization_receipt: key(10),
            },
        )
        .unwrap();
        let snapshot = crate::relayer::RelayerSnapshotV1 {
            pinned_program_id: program,
            registry_program: key(5),
            current_root_sequence: 7,
            observed_slot: 900,
            pool_state_sha256: [0xab; 32],
        };
        let context = PreparedSettlementValidationContextV1 {
            transition_kind: PoolV1TransitionKind::Withdrawal,
            source_root_sequence: 7,
            plan_authority: fee_payer,
            authorization_receipt: key(10),
            verifier_profile: envelope.verifier_profile,
            verifier_release: envelope.verifier_release,
            core_plan: instruction.accounts[7].pubkey,
            rollover_shard: None,
            asset_mint: Some(mint),
        };
        let plan = prepare_permissionless_prepared_relayer_plan_v1(
            snapshot,
            fee_payer,
            &context,
            &instruction,
        )
        .unwrap();
        let (_, policy) = prepared_relayer_fixture();
        (plan, policy)
    }

    #[test]
    fn prepared_settlement_queue_replay_is_idempotent_across_restart() {
        let directory = TestDirectory::new();
        let path = directory.path("prepared-relayer.state");
        let (plan, policy) = prepared_relayer_fixture();
        let mut store = DurableRelayerStateV1::open_or_create_v1(&path, policy).unwrap();
        assert_eq!(
            store
                .admit_and_enqueue_v1(policy, 910, 5_000, 1_005_000, &plan)
                .unwrap(),
            RelayerEnqueueOutcomeV1::Inserted
        );
        assert_eq!(
            store
                .admit_and_enqueue_v1(policy, 910, 5_000, 1_005_000, &plan)
                .unwrap(),
            RelayerEnqueueOutcomeV1::AlreadyPresent
        );
        drop(store);

        let mut restarted = DurableRelayerStateV1::open_or_create_v1(&path, policy).unwrap();
        assert_eq!(restarted.entries().len(), 1);
        assert_eq!(
            restarted.entries()[0].plan.kind,
            RelayerRequestKindV1::PrepareSettlement
        );
        assert_eq!(
            restarted.entries()[0].status,
            DurableRelayerStatusV1::Queued
        );
        assert_eq!(
            restarted
                .admit_and_enqueue_v1(policy, 911, 5_000, 1_005_000, &plan)
                .unwrap(),
            RelayerEnqueueOutcomeV1::AlreadyPresent
        );
    }

    #[test]
    fn prepared_finalization_queue_persists_exact_validation_context() {
        let directory = TestDirectory::new();
        let path = directory.path("finalization-relayer.state");
        let (plan, policy) = prepared_finalization_relayer_fixture();
        let mut store = DurableRelayerStateV1::open_or_create_v1(&path, policy).unwrap();
        store
            .admit_and_enqueue_v1(policy, 910, 5_000, 1_005_000, &plan)
            .unwrap();
        drop(store);
        let restarted = DurableRelayerStateV1::open_or_create_v1(&path, policy).unwrap();
        assert_eq!(restarted.entries().len(), 1);
        assert_eq!(restarted.entries()[0].plan, plan);
        assert!(restarted.entries()[0].plan.prepared_plan.is_some());
    }

    #[test]
    fn relayer_queue_persists_policy_rate_fee_reserve_and_lifecycle() {
        let directory = TestDirectory::new();
        let path = directory.path("relayer.state");
        let (first, policy) = relayer_fixture(77);
        let (second, _) = relayer_fixture(78);
        let mut store = DurableRelayerStateV1::open_or_create_v1(&path, policy).unwrap();
        assert_eq!(
            store
                .admit_and_enqueue_v1(policy, 910, 5_000, 1_005_000, &first)
                .unwrap(),
            RelayerEnqueueOutcomeV1::Inserted
        );
        assert_eq!(
            store
                .admit_and_enqueue_v1(policy, 910, 5_000, 1_005_000, &first)
                .unwrap(),
            RelayerEnqueueOutcomeV1::AlreadyPresent
        );
        store
            .mark_inflight_v1(policy, first.request_id, 910, 5_000, 1_005_000)
            .unwrap();
        drop(store);

        let mut restarted = DurableRelayerStateV1::open_or_create_v1(&path, policy).unwrap();
        assert_eq!(restarted.rate_window(), (910, 1));
        assert_eq!(restarted.entries().len(), 1);
        assert_eq!(
            restarted.entries()[0].status,
            DurableRelayerStatusV1::Inflight
        );
        assert_eq!(
            restarted
                .admit_and_enqueue_v1(policy, 911, 10_001, 2_000_000, &second)
                .err(),
            Some(DurableStateErrorV1::Admission(
                RelayerAdmissionErrorV1::FeeEstimateTooHigh
            ))
        );
        assert_eq!(
            restarted
                .admit_and_enqueue_v1(policy, 911, 5_000, 1_004_999, &second)
                .err(),
            Some(DurableStateErrorV1::Admission(
                RelayerAdmissionErrorV1::InsufficientFeeReserve
            ))
        );
        assert_eq!(
            restarted
                .admit_and_enqueue_v1(policy, 911, 5_000, 1_005_000, &second)
                .err(),
            Some(DurableStateErrorV1::Admission(
                RelayerAdmissionErrorV1::RateLimited
            ))
        );
        restarted.complete_inflight_v1(first.request_id).unwrap();
        assert!(restarted.entries().is_empty());
        let paused = RelayerPolicyV1 {
            paused: true,
            ..policy
        };
        restarted.update_policy_v1(policy, paused).unwrap();
        assert_eq!(
            restarted
                .admit_and_enqueue_v1(paused, 911, 5_000, 1_005_000, &second)
                .err(),
            Some(DurableStateErrorV1::Admission(
                RelayerAdmissionErrorV1::Paused
            ))
        );
        drop(restarted);

        assert_eq!(
            DurableRelayerStateV1::open_or_create_v1(
                &path,
                RelayerPolicyV1 {
                    max_queue_depth: 5,
                    ..paused
                }
            )
            .err(),
            Some(DurableStateErrorV1::PolicyMismatch)
        );

        let mut bytes = fs::read(&path).unwrap();
        bytes[40] ^= 1;
        fs::write(&path, bytes).unwrap();
        assert_eq!(
            DurableRelayerStateV1::open_or_create_v1(&path, paused).err(),
            Some(DurableStateErrorV1::ChecksumMismatch)
        );
    }
}
