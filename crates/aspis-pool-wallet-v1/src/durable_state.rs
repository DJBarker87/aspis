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
    finalized_indexer::FinalizedBlockIngestResultV1,
    relayer::{
        admit_relayer_plan_v1, prepare_permissionless_relayer_plan_v1, relayer_policy_id_v1,
        RelayerAdmissionContextV1, RelayerAdmissionErrorV1, RelayerAdmissionV1,
        RelayerEnqueueOutcomeV1, RelayerErrorV1, RelayerPlanV1, RelayerPolicyV1,
        RelayerRequestKindV1,
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
const RELAYER_HEADER_BYTES: usize = 88;
const RELAYER_RECORD_HEADER_BYTES: usize = 276;
const CHECKSUM_OFFSET: usize = 56;

const MAX_DURABLE_IMAGE_BYTES: usize = 64 * 1024 * 1024;
const MAX_SEALED_NOTE_BYTES: usize = 1024 * 1024;
const MAX_NOTE_RECORDS: usize = 1_000_000;
const MAX_RELAYER_RECORDS: usize = 100_000;
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
    InvalidCipherId,
    InvalidSealedNote,
    MissingRecoveredNote,
    UnexpectedRecoveredNote,
    RecoveredAccessMismatch,
    CandidateStateMismatch,
    InvalidRollback,
    InvalidSpendUpdate,
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
            let (scan_state, stored_cipher_id, notes) = decode_wallet_image_v1(&bytes)?;
            if scan_state.identity() != initial_scan_state.identity() {
                return Err(DurableStateErrorV1::IdentityMismatch);
            }
            if stored_cipher_id != note_cipher_id {
                return Err(DurableStateErrorV1::CipherMismatch);
            }
            return Ok(Self {
                file,
                scan_state,
                note_cipher_id,
                notes,
            });
        }
        let bytes = encode_wallet_image_v1(&initial_scan_state, note_cipher_id, &[])?;
        file.replace(&bytes)?;
        Ok(Self {
            file,
            scan_state: initial_scan_state,
            note_cipher_id,
            notes: Vec::new(),
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

    /// Advance the rollback anchor and durably commit it without deleting
    /// wallet notes. Deliveries for an event must be reconciled before its
    /// block is pruned because the compact cursor no longer retains that ID.
    pub fn prune_finalized_history_through_v1(
        &mut self,
        ancestor: FinalizedChainPointV1,
    ) -> Result<PruneSummaryV1, DurableStateErrorV1> {
        let mut candidate = self.scan_state.clone();
        let summary = candidate.prune_finalized_history_through_v1(ancestor)?;
        let bytes = encode_wallet_image_v1(&candidate, self.note_cipher_id, &self.notes)?;
        self.file.replace(&bytes)?;
        self.scan_state = candidate;
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

        let bytes = encode_wallet_image_v1(&candidate_scan_state, self.note_cipher_id, &notes)?;
        self.file.replace(&bytes)?;
        self.scan_state = candidate_scan_state;
        self.notes = notes;
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
        let bytes = encode_wallet_image_v1(&self.scan_state, self.note_cipher_id, &notes)?;
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
    Ok(())
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

fn encode_wallet_image_v1(
    scan_state: &ScanStateV1,
    note_cipher_id: [u8; 32],
    notes: &[StoredSealedNoteV1],
) -> Result<Vec<u8>, DurableStateErrorV1> {
    if note_cipher_id == [0u8; 32] {
        return Err(DurableStateErrorV1::InvalidCipherId);
    }
    if notes.len() > MAX_NOTE_RECORDS {
        return Err(DurableStateErrorV1::CountOverflow);
    }
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
    finish_checksum_v1(WALLET_CHECKSUM_DOMAIN, &mut output)?;
    Ok(output)
}

fn decode_wallet_image_v1(
    bytes: &[u8],
) -> Result<(ScanStateV1, [u8; 32], Vec<StoredSealedNoteV1>), DurableStateErrorV1> {
    validate_header_v1(bytes, WALLET_MAGIC, WALLET_HEADER_BYTES)?;
    verify_checksum_v1(WALLET_CHECKSUM_DOMAIN, bytes)?;
    let cipher_id = read_array_v1(bytes, 8)?;
    if cipher_id == [0u8; 32] {
        return Err(DurableStateErrorV1::InvalidCipherId);
    }
    if bytes[52..56] != [0u8; 4] {
        return Err(DurableStateErrorV1::NonZeroReserved);
    }
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
    if offset != bytes.len() {
        return Err(DurableStateErrorV1::TrailingBytes);
    }
    Ok((scan_state, cipher_id, notes))
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
        let rebuilt = prepare_permissionless_relayer_plan_v1(
            entry.plan.snapshot,
            entry.plan.fee_payer,
            &entry.plan.instruction,
        )?;
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
        if header[34..36] != [0u8; 2] || header[272..276] != [0u8; 4] {
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
        let plan = RelayerPlanV1 {
            request_id: read_array_v1(header, 0)?,
            kind,
            snapshot,
            fee_payer: Pubkey::new_from_array(read_array_v1(header, 148)?),
            instruction: Instruction {
                program_id: Pubkey::new_from_array(read_array_v1(header, 180)?),
                accounts,
                data: body[accounts_bytes..].to_vec(),
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
    }
}

fn decode_kind_v1(byte: u8) -> Result<RelayerRequestKindV1, DurableStateErrorV1> {
    match byte {
        0 => Ok(RelayerRequestKindV1::Initialize),
        1 => Ok(RelayerRequestKindV1::Deposit),
        2 => Ok(RelayerRequestKindV1::PrivateTransfer),
        3 => Ok(RelayerRequestKindV1::Withdrawal),
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
    use std::{
        fs,
        path::PathBuf,
        sync::atomic::{AtomicU64, Ordering},
    };

    use aspis_core::field::M31;
    use aspis_pool::{deposit::DepositRequestV1, pool_v1_state_address, TransitionReceiptV1};
    use aspis_statement::{
        encode_digest_canonical, pool_v1::PoolV1TransitionKind, poseidon2::Digest,
    };

    use crate::{
        finalized_indexer::{FinalizedTransitionEvidenceV1, HistoricalRootEvidenceV1},
        scan_state::{
            DepositScanIdentityV1, FinalizedBlockAdvanceV1, FinalizedBlockV1,
            FinalizedPublicOutputRecordV1,
        },
        transaction_builder::build_deposit_instruction_v1,
        NoteOpeningV1,
    };

    static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

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
            }],
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
