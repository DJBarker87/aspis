//! Crash-safe recovery journal for the reviewed Spend mainnet executor.
//!
//! This module deliberately contains no RPC client and no transaction submission
//! path.  Its only job is to make the local signing boundary fail closed:
//!
//! * a run owns an advisory lock before reading or changing recovery state;
//! * the journal and signed-wire spools are private, non-symlink files;
//! * every journal append is hash chained and synchronously persisted;
//! * a signed wire is fully persisted before it can be marked submit-ready; and
//! * cleanup-only mode can be entered, but cannot be exited for that run.

use std::{
    collections::BTreeMap,
    fs::{self, DirBuilder, File, OpenOptions},
    io::{Read, Seek, SeekFrom, Write},
    os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt},
    path::{Component, Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use anyhow::{bail, ensure, Context, Result};
use chrono::{DateTime, SecondsFormat, Utc};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use sha2::{Digest, Sha256};

pub const JOURNAL_SCHEMA: &str = "aspis-spend-mainnet-recovery-journal/v1";
pub const LOCK_ANCHOR_SCHEMA: &str = "aspis-spend-mainnet-recovery-head/v1";
pub const JOURNAL_FILE_NAME: &str = "recovery.jsonl";
pub const LOCK_FILE_NAME: &str = "run.lock";
pub const SPOOL_DIRECTORY_NAME: &str = "signed-wires";

const PRIVATE_DIRECTORY_MODE: u32 = 0o700;
const PRIVATE_FILE_MODE: u32 = 0o600;
const ZERO_HASH: &str = "0000000000000000000000000000000000000000000000000000000000000000";
const MAX_JOURNAL_BYTES: usize = 16 * 1024 * 1024;
const MAX_ENTRY_BYTES: usize = 1024 * 1024;
const MAX_SIGNED_WIRE_BYTES: usize = 1024 * 1024;
const MAX_IDENTIFIER_BYTES: usize = 96;
const MAX_TEXT_BYTES: usize = 16 * 1024;

// `OpenOptionsExt` exposes the flags interface but std does not expose
// O_NOFOLLOW.  These are the platform ABI values on the two supported build
// families.  Pre- and post-open inode checks are also performed below.
#[cfg(any(target_os = "linux", target_os = "android"))]
const O_NOFOLLOW: i32 = 0o400000;
#[cfg(any(
    target_os = "macos",
    target_os = "ios",
    target_os = "freebsd",
    target_os = "openbsd",
    target_os = "netbsd",
    target_os = "dragonfly"
))]
const O_NOFOLLOW: i32 = 0x0100;
#[cfg(not(any(
    target_os = "linux",
    target_os = "android",
    target_os = "macos",
    target_os = "ios",
    target_os = "freebsd",
    target_os = "openbsd",
    target_os = "netbsd",
    target_os = "dragonfly"
)))]
compile_error!("Spend mainnet recovery storage requires a supported O_NOFOLLOW Unix ABI");

static SPOOL_NONCE: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum TransactionClass {
    Forward,
    Cleanup,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "type", rename_all = "snake_case", deny_unknown_fields)]
pub enum JournalBody {
    RunStarted {
        run_id: String,
    },
    Checkpoint {
        name: String,
        details: Value,
    },
    CleanupOnlyEntered {
        reason: String,
    },
    SignedWireSubmitReady {
        wire_id: String,
        transaction_class: TransactionClass,
        spool_file: String,
        wire_len: u64,
        wire_sha256: String,
    },
    SubmissionRecorded {
        wire_id: String,
        signature: String,
    },
    FinalizationRecorded {
        wire_id: String,
        slot: u64,
    },
    RunCompleted {
        outcome: String,
    },
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct JournalEntry {
    pub schema: String,
    pub seq: u64,
    pub prev_hash: String,
    pub timestamp_utc: String,
    pub body: JournalBody,
    pub entry_hash: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RunMode {
    Forward,
    CleanupOnly {
        entered_sequence: u64,
        reason: String,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReadyWire {
    pub wire_id: String,
    pub transaction_class: TransactionClass,
    pub spool_file: String,
    pub wire_len: u64,
    pub wire_sha256: String,
    pub ready_sequence: u64,
    pub submitted_signature: Option<String>,
    pub finalized_slot: Option<u64>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RecoveryState {
    pub run_id: Option<String>,
    pub mode: RunMode,
    pub ready_wires: BTreeMap<String, ReadyWire>,
    pub completed_outcome: Option<String>,
}

impl Default for RecoveryState {
    fn default() -> Self {
        Self {
            run_id: None,
            mode: RunMode::Forward,
            ready_wires: BTreeMap::new(),
            completed_outcome: None,
        }
    }
}

#[derive(Serialize)]
struct HashMaterial<'a> {
    schema: &'a str,
    seq: u64,
    prev_hash: &'a str,
    timestamp_utc: &'a str,
    body: &'a JournalBody,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct LockAnchor {
    schema: String,
    last_sequence: u64,
    last_entry_hash: String,
}

struct ValidatedJournal {
    state: RecoveryState,
    next_sequence: u64,
    last_hash: String,
}

/// An exclusively locked, validated recovery journal for one mainnet run.
#[derive(Debug)]
pub struct RecoveryJournal {
    run_directory: PathBuf,
    spool_directory: PathBuf,
    journal_path: PathBuf,
    journal: File,
    // The advisory lock is intentionally held for the lifetime of this value.
    lock: File,
    state: RecoveryState,
    next_sequence: u64,
    last_hash: String,
}

impl RecoveryJournal {
    /// Creates a fresh private run directory and a new journal.
    ///
    /// `run_directory` must not exist. Its direct parent must already be a
    /// private (0700), real directory. This prevents accidentally placing
    /// signing material in a shared or symlinked location.
    pub fn create(run_directory: impl AsRef<Path>, run_id: impl Into<String>) -> Result<Self> {
        let run_directory = run_directory.as_ref().to_path_buf();
        let run_id = run_id.into();
        validate_identifier("run_id", &run_id)?;
        ensure_absent_path(&run_directory)?;
        let parent = run_directory
            .parent()
            .context("run directory must have a parent")?;
        validate_secure_directory(parent)?;

        let mut builder = DirBuilder::new();
        builder.mode(PRIVATE_DIRECTORY_MODE);
        builder
            .create(&run_directory)
            .with_context(|| format!("create run directory {}", run_directory.display()))?;
        validate_secure_directory(&run_directory)?;
        fsync_directory(parent)?;

        let lock_path = run_directory.join(LOCK_FILE_NAME);
        let mut lock = create_private_file(&lock_path, false)?;
        lock.try_lock()
            .with_context(|| format!("acquire exclusive run lock {}", lock_path.display()))?;
        lock.sync_all()
            .with_context(|| format!("sync lock file {}", lock_path.display()))?;
        fsync_directory(&run_directory)?;

        let spool_directory = run_directory.join(SPOOL_DIRECTORY_NAME);
        builder
            .create(&spool_directory)
            .with_context(|| format!("create spool directory {}", spool_directory.display()))?;
        validate_secure_directory(&spool_directory)?;
        fsync_directory(&run_directory)?;

        let journal_path = run_directory.join(JOURNAL_FILE_NAME);
        let mut journal = create_private_file(&journal_path, true)?;
        let mut state = RecoveryState::default();
        let body = JournalBody::RunStarted { run_id };
        reduce(&mut state, 0, &body)?;
        let initial = make_entry(0, ZERO_HASH, body)?;
        write_entry(&mut journal, &initial)?;
        write_lock_anchor(&mut lock, initial.seq, &initial.entry_hash)?;
        fsync_directory(&run_directory)?;

        Ok(Self {
            run_directory,
            spool_directory,
            journal_path,
            journal,
            lock,
            state,
            next_sequence: 1,
            last_hash: initial.entry_hash,
        })
    }

    /// Reopens an existing run, acquiring its exclusive lock and validating
    /// the complete chain and every submit-ready spool before returning.
    pub fn reopen(run_directory: impl AsRef<Path>) -> Result<Self> {
        let run_directory = run_directory.as_ref().to_path_buf();
        let parent = run_directory
            .parent()
            .context("run directory must have a parent")?;
        validate_secure_directory(parent)?;
        validate_secure_directory(&run_directory)?;

        let lock_path = run_directory.join(LOCK_FILE_NAME);
        let mut lock = open_private_file(&lock_path, false)?;
        lock.try_lock()
            .with_context(|| format!("acquire exclusive run lock {}", lock_path.display()))?;

        let spool_directory = run_directory.join(SPOOL_DIRECTORY_NAME);
        validate_secure_directory(&spool_directory)?;
        let journal_path = run_directory.join(JOURNAL_FILE_NAME);
        let mut journal = open_private_file(&journal_path, true)?;
        let validated = validate_open_journal(&mut journal, &journal_path, &spool_directory)?;
        validate_lock_anchor(&mut lock, &lock_path, &validated)?;

        Ok(Self {
            run_directory,
            spool_directory,
            journal_path,
            journal,
            lock,
            state: validated.state,
            next_sequence: validated.next_sequence,
            last_hash: validated.last_hash,
        })
    }

    pub fn run_directory(&self) -> &Path {
        &self.run_directory
    }

    pub fn journal_path(&self) -> &Path {
        &self.journal_path
    }

    pub fn state(&self) -> &RecoveryState {
        &self.state
    }

    pub fn next_sequence(&self) -> u64 {
        self.next_sequence
    }

    /// Adds a non-signing recovery checkpoint.
    pub fn record_checkpoint(
        &mut self,
        name: impl Into<String>,
        details: Value,
    ) -> Result<JournalEntry> {
        let name = name.into();
        validate_text("checkpoint name", &name)?;
        self.append_body(JournalBody::Checkpoint { name, details })
    }

    /// Durably and irreversibly enters cleanup-only mode for this run.
    pub fn enter_cleanup_only(&mut self, reason: impl Into<String>) -> Result<JournalEntry> {
        let reason = reason.into();
        validate_text("cleanup-only reason", &reason)?;
        self.append_body(JournalBody::CleanupOnlyEntered { reason })
    }

    /// Persists a complete signed wire before appending its submit-ready entry.
    ///
    /// The ordering is strict: create-new 0600 spool, write full bytes, fsync
    /// spool, fsync spool directory, then append and fsync the journal entry.
    /// An interrupted attempt may leave an unreferenced spool, but no journal
    /// state will authorize that orphan for submission.
    pub fn spool_signed_wire_submit_ready(
        &mut self,
        wire_id: impl Into<String>,
        transaction_class: TransactionClass,
        wire: &[u8],
    ) -> Result<JournalEntry> {
        let wire_id = wire_id.into();
        validate_identifier("wire_id", &wire_id)?;
        ensure!(!wire.is_empty(), "signed wire must not be empty");
        ensure!(
            wire.len() <= MAX_SIGNED_WIRE_BYTES,
            "signed wire exceeds {MAX_SIGNED_WIRE_BYTES} bytes"
        );

        self.refresh()?;
        ensure!(
            !self.state.ready_wires.contains_key(&wire_id),
            "wire_id is already submit-ready: {wire_id}"
        );
        ensure_class_allowed(&self.state, transaction_class)?;

        let wire_sha256 = sha256(wire);
        let (spool_file, mut spool) = self.create_spool(&wire_id, &wire_sha256)?;
        spool
            .write_all(wire)
            .with_context(|| format!("write signed-wire spool {spool_file}"))?;
        spool
            .sync_all()
            .with_context(|| format!("sync signed-wire spool {spool_file}"))?;
        fsync_directory(&self.spool_directory)?;
        drop(spool);

        self.append_body(JournalBody::SignedWireSubmitReady {
            wire_id,
            transaction_class,
            spool_file,
            wire_len: wire.len() as u64,
            wire_sha256,
        })
    }

    /// Returns exact bytes only for a currently submit-ready wire. Forward
    /// wires become unavailable immediately after cleanup-only is entered.
    pub fn load_submit_ready_wire(&mut self, wire_id: &str) -> Result<Vec<u8>> {
        self.refresh()?;
        let ready = self
            .state
            .ready_wires
            .get(wire_id)
            .with_context(|| format!("wire is not submit-ready: {wire_id}"))?;
        ensure_class_allowed(&self.state, ready.transaction_class)?;
        ensure!(
            ready.submitted_signature.is_none(),
            "wire already has a recorded submission: {wire_id}"
        );
        read_and_validate_spool(&self.spool_directory, ready)
    }

    /// Records a submission observed by a separate executor. This method does
    /// not submit anything and cannot record a forward submission in
    /// cleanup-only mode.
    pub fn record_submission(
        &mut self,
        wire_id: impl Into<String>,
        signature: impl Into<String>,
    ) -> Result<JournalEntry> {
        let wire_id = wire_id.into();
        let signature = signature.into();
        validate_identifier("wire_id", &wire_id)?;
        validate_text("signature", &signature)?;
        self.append_body(JournalBody::SubmissionRecorded { wire_id, signature })
    }

    pub fn record_finalization(
        &mut self,
        wire_id: impl Into<String>,
        slot: u64,
    ) -> Result<JournalEntry> {
        let wire_id = wire_id.into();
        validate_identifier("wire_id", &wire_id)?;
        self.append_body(JournalBody::FinalizationRecorded { wire_id, slot })
    }

    pub fn complete(&mut self, outcome: impl Into<String>) -> Result<JournalEntry> {
        let outcome = outcome.into();
        validate_text("run outcome", &outcome)?;
        self.append_body(JournalBody::RunCompleted { outcome })
    }

    fn create_spool(&self, wire_id: &str, wire_sha256: &str) -> Result<(String, File)> {
        validate_secure_directory(&self.spool_directory)?;
        let now = Utc::now().timestamp_nanos_opt().unwrap_or_default();
        let process = std::process::id();
        for _ in 0..128 {
            let nonce = SPOOL_NONCE.fetch_add(1, Ordering::Relaxed);
            let spool_file = format!(
                "wire-{:020}-{wire_id}-{wire_sha256}-{now}-{process}-{nonce}.bin",
                self.next_sequence
            );
            validate_spool_file_name(&spool_file)?;
            let path = self.spool_directory.join(&spool_file);
            match create_private_file(&path, false) {
                Ok(file) => return Ok((spool_file, file)),
                Err(error) if path.exists() => {
                    let _ = error;
                }
                Err(error) => return Err(error),
            }
        }
        bail!("could not reserve a unique signed-wire spool path")
    }

    fn append_body(&mut self, body: JournalBody) -> Result<JournalEntry> {
        self.refresh()?;
        self.append_body_without_refresh(body)
    }

    fn append_body_without_refresh(&mut self, body: JournalBody) -> Result<JournalEntry> {
        let mut next_state = self.state.clone();
        reduce(&mut next_state, self.next_sequence, &body)?;
        let entry = make_entry(self.next_sequence, &self.last_hash, body)?;
        write_entry(&mut self.journal, &entry)?;
        write_lock_anchor(&mut self.lock, entry.seq, &entry.entry_hash)?;
        self.state = next_state;
        self.next_sequence = self
            .next_sequence
            .checked_add(1)
            .context("journal sequence overflow")?;
        self.last_hash.clone_from(&entry.entry_hash);
        Ok(entry)
    }

    fn refresh(&mut self) -> Result<()> {
        let validated =
            validate_open_journal(&mut self.journal, &self.journal_path, &self.spool_directory)?;
        let lock_path = self.run_directory.join(LOCK_FILE_NAME);
        validate_lock_anchor(&mut self.lock, &lock_path, &validated)?;
        ensure!(
            validated.next_sequence == self.next_sequence
                && validated.last_hash == self.last_hash
                && validated.state == self.state,
            "journal changed outside the locked recovery handle"
        );
        Ok(())
    }
}

fn make_entry(seq: u64, prev_hash: &str, body: JournalBody) -> Result<JournalEntry> {
    validate_hash("previous hash", prev_hash)?;
    let timestamp_utc = Utc::now().to_rfc3339_opts(SecondsFormat::Nanos, true);
    let entry_hash = hash_material(seq, prev_hash, &timestamp_utc, &body)?;
    Ok(JournalEntry {
        schema: JOURNAL_SCHEMA.to_owned(),
        seq,
        prev_hash: prev_hash.to_owned(),
        timestamp_utc,
        body,
        entry_hash,
    })
}

fn hash_material(
    seq: u64,
    prev_hash: &str,
    timestamp_utc: &str,
    body: &JournalBody,
) -> Result<String> {
    let material = HashMaterial {
        schema: JOURNAL_SCHEMA,
        seq,
        prev_hash,
        timestamp_utc,
        body,
    };
    Ok(sha256(&serde_json::to_vec(&material)?))
}

fn write_entry(file: &mut File, entry: &JournalEntry) -> Result<()> {
    let mut bytes = serde_json::to_vec(entry)?;
    ensure!(
        bytes.len() <= MAX_ENTRY_BYTES,
        "journal entry exceeds {MAX_ENTRY_BYTES} bytes"
    );
    bytes.push(b'\n');
    file.write_all(&bytes).context("append recovery journal")?;
    file.sync_all().context("fsync recovery journal")?;
    Ok(())
}

fn write_lock_anchor(lock: &mut File, last_sequence: u64, last_entry_hash: &str) -> Result<()> {
    validate_hash("lock anchor hash", last_entry_hash)?;
    let anchor = LockAnchor {
        schema: LOCK_ANCHOR_SCHEMA.to_owned(),
        last_sequence,
        last_entry_hash: last_entry_hash.to_owned(),
    };
    let mut bytes = serde_json::to_vec(&anchor)?;
    bytes.push(b'\n');
    lock.set_len(0).context("truncate recovery lock anchor")?;
    lock.seek(SeekFrom::Start(0))
        .context("seek recovery lock anchor")?;
    lock.write_all(&bytes)
        .context("write recovery lock anchor")?;
    lock.sync_all().context("fsync recovery lock anchor")?;
    Ok(())
}

fn validate_lock_anchor(
    lock: &mut File,
    lock_path: &Path,
    journal: &ValidatedJournal,
) -> Result<()> {
    validate_open_file(lock_path, lock)?;
    lock.seek(SeekFrom::Start(0))
        .context("seek recovery lock anchor")?;
    let mut bytes = Vec::new();
    lock.take(4097)
        .read_to_end(&mut bytes)
        .context("read recovery lock anchor")?;
    ensure!(
        !bytes.is_empty() && bytes.len() <= 4096 && bytes.last() == Some(&b'\n'),
        "recovery lock anchor is empty, oversized, or truncated"
    );
    ensure!(
        !bytes[..bytes.len() - 1].contains(&b'\n'),
        "recovery lock anchor contains multiple records"
    );
    let anchor: LockAnchor =
        serde_json::from_slice(&bytes[..bytes.len() - 1]).context("decode recovery lock anchor")?;
    ensure!(
        anchor.schema == LOCK_ANCHOR_SCHEMA,
        "unknown recovery lock anchor schema: {}",
        anchor.schema
    );
    validate_hash("lock anchor hash", &anchor.last_entry_hash)?;
    let expected_sequence = journal
        .next_sequence
        .checked_sub(1)
        .context("cannot anchor an empty recovery journal")?;
    ensure!(
        anchor.last_sequence == expected_sequence && anchor.last_entry_hash == journal.last_hash,
        "recovery journal is truncated or diverges from its durable lock anchor"
    );
    Ok(())
}

fn validate_open_journal(
    journal: &mut File,
    journal_path: &Path,
    spool_directory: &Path,
) -> Result<ValidatedJournal> {
    validate_open_file(journal_path, journal)?;
    journal
        .seek(SeekFrom::Start(0))
        .context("seek recovery journal")?;
    let mut bytes = Vec::new();
    journal
        .take((MAX_JOURNAL_BYTES + 1) as u64)
        .read_to_end(&mut bytes)
        .context("read recovery journal")?;
    ensure!(
        bytes.len() <= MAX_JOURNAL_BYTES,
        "recovery journal exceeds {MAX_JOURNAL_BYTES} bytes"
    );
    validate_journal_bytes(&bytes, spool_directory)
}

fn validate_journal_bytes(bytes: &[u8], spool_directory: &Path) -> Result<ValidatedJournal> {
    ensure!(!bytes.is_empty(), "recovery journal is empty");
    ensure!(
        bytes.last() == Some(&b'\n'),
        "recovery journal is truncated: final newline is absent"
    );

    let mut state = RecoveryState::default();
    let mut expected_prev = ZERO_HASH.to_owned();
    let mut next_sequence = 0_u64;

    for (line_index, line) in bytes[..bytes.len() - 1]
        .split(|byte| *byte == b'\n')
        .enumerate()
    {
        ensure!(!line.is_empty(), "empty journal line at index {line_index}");
        ensure!(
            line.len() <= MAX_ENTRY_BYTES,
            "journal line {line_index} exceeds {MAX_ENTRY_BYTES} bytes"
        );
        let entry: JournalEntry = serde_json::from_slice(line)
            .with_context(|| format!("decode journal line {line_index}"))?;
        ensure!(
            entry.schema == JOURNAL_SCHEMA,
            "unknown recovery journal schema on line {line_index}: {}",
            entry.schema
        );
        ensure!(
            entry.seq == next_sequence,
            "non-contiguous journal sequence on line {line_index}: expected {next_sequence}, got {}",
            entry.seq
        );
        ensure!(
            entry.prev_hash == expected_prev,
            "journal hash-chain predecessor mismatch on line {line_index}"
        );
        validate_hash("entry hash", &entry.entry_hash)?;
        validate_timestamp(&entry.timestamp_utc)?;
        let recomputed = hash_material(
            entry.seq,
            &entry.prev_hash,
            &entry.timestamp_utc,
            &entry.body,
        )?;
        ensure!(
            entry.entry_hash == recomputed,
            "journal entry hash mismatch on line {line_index}"
        );
        reduce(&mut state, entry.seq, &entry.body)
            .with_context(|| format!("reduce journal line {line_index}"))?;
        if let JournalBody::SignedWireSubmitReady { wire_id, .. } = &entry.body {
            let ready = state
                .ready_wires
                .get(wire_id)
                .context("reducer omitted submit-ready wire")?;
            let _ = read_and_validate_spool(spool_directory, ready)
                .with_context(|| format!("validate submit-ready spool for {wire_id}"))?;
        }
        expected_prev = entry.entry_hash;
        next_sequence = next_sequence
            .checked_add(1)
            .context("journal sequence overflow")?;
    }

    ensure!(
        state.run_id.is_some(),
        "recovery journal omitted initial run_started entry"
    );
    Ok(ValidatedJournal {
        state,
        next_sequence,
        last_hash: expected_prev,
    })
}

fn reduce(state: &mut RecoveryState, seq: u64, body: &JournalBody) -> Result<()> {
    match body {
        JournalBody::RunStarted { run_id } => {
            validate_identifier("run_id", run_id)?;
            ensure!(seq == 0, "run_started must be journal sequence zero");
            ensure!(state.run_id.is_none(), "duplicate run_started entry");
            state.run_id = Some(run_id.clone());
            return Ok(());
        }
        _ => ensure!(state.run_id.is_some(), "journal event precedes run_started"),
    }
    ensure!(
        state.completed_outcome.is_none(),
        "journal event follows run_completed"
    );

    match body {
        JournalBody::RunStarted { .. } => unreachable!("handled above"),
        JournalBody::Checkpoint { name, .. } => validate_text("checkpoint name", name),
        JournalBody::CleanupOnlyEntered { reason } => {
            validate_text("cleanup-only reason", reason)?;
            ensure!(
                matches!(state.mode, RunMode::Forward),
                "cleanup-only mode is already active and cannot be reset or re-entered"
            );
            state.mode = RunMode::CleanupOnly {
                entered_sequence: seq,
                reason: reason.clone(),
            };
            Ok(())
        }
        JournalBody::SignedWireSubmitReady {
            wire_id,
            transaction_class,
            spool_file,
            wire_len,
            wire_sha256,
        } => {
            validate_identifier("wire_id", wire_id)?;
            validate_spool_file_name(spool_file)?;
            validate_hash("wire sha256", wire_sha256)?;
            ensure!(*wire_len > 0, "submit-ready wire length is zero");
            ensure!(
                *wire_len <= MAX_SIGNED_WIRE_BYTES as u64,
                "submit-ready wire exceeds maximum length"
            );
            ensure_class_allowed(state, *transaction_class)?;
            ensure!(
                !state.ready_wires.contains_key(wire_id),
                "duplicate submit-ready wire_id: {wire_id}"
            );
            ensure!(
                !state
                    .ready_wires
                    .values()
                    .any(|wire| wire.spool_file == *spool_file),
                "signed-wire spool is referenced more than once"
            );
            state.ready_wires.insert(
                wire_id.clone(),
                ReadyWire {
                    wire_id: wire_id.clone(),
                    transaction_class: *transaction_class,
                    spool_file: spool_file.clone(),
                    wire_len: *wire_len,
                    wire_sha256: wire_sha256.clone(),
                    ready_sequence: seq,
                    submitted_signature: None,
                    finalized_slot: None,
                },
            );
            Ok(())
        }
        JournalBody::SubmissionRecorded { wire_id, signature } => {
            validate_identifier("wire_id", wire_id)?;
            validate_text("signature", signature)?;
            let transaction_class = state
                .ready_wires
                .get(wire_id)
                .with_context(|| format!("submission has no submit-ready wire: {wire_id}"))?
                .transaction_class;
            ensure_class_allowed(state, transaction_class)?;
            let ready = state
                .ready_wires
                .get_mut(wire_id)
                .expect("wire existence checked above");
            ensure!(
                ready.submitted_signature.is_none(),
                "duplicate submission record for wire: {wire_id}"
            );
            ready.submitted_signature = Some(signature.clone());
            Ok(())
        }
        JournalBody::FinalizationRecorded { wire_id, slot } => {
            validate_identifier("wire_id", wire_id)?;
            ensure!(*slot > 0, "finalized slot must be nonzero");
            let ready = state
                .ready_wires
                .get_mut(wire_id)
                .with_context(|| format!("finalization has no submit-ready wire: {wire_id}"))?;
            ensure!(
                ready.submitted_signature.is_some(),
                "finalization precedes submission record for wire: {wire_id}"
            );
            ensure!(
                ready.finalized_slot.is_none(),
                "duplicate finalization record for wire: {wire_id}"
            );
            ready.finalized_slot = Some(*slot);
            Ok(())
        }
        JournalBody::RunCompleted { outcome } => {
            validate_text("run outcome", outcome)?;
            state.completed_outcome = Some(outcome.clone());
            Ok(())
        }
    }
}

fn ensure_class_allowed(state: &RecoveryState, class: TransactionClass) -> Result<()> {
    if matches!(state.mode, RunMode::CleanupOnly { .. }) {
        ensure!(
            class == TransactionClass::Cleanup,
            "forward transaction is forbidden after cleanup-only mode is entered"
        );
    }
    Ok(())
}

fn read_and_validate_spool(spool_directory: &Path, ready: &ReadyWire) -> Result<Vec<u8>> {
    validate_secure_directory(spool_directory)?;
    validate_spool_file_name(&ready.spool_file)?;
    let path = spool_directory.join(&ready.spool_file);
    let file = open_private_file(&path, false)?;
    let mut bytes = Vec::new();
    file.take(MAX_SIGNED_WIRE_BYTES as u64 + 1)
        .read_to_end(&mut bytes)
        .with_context(|| format!("read signed-wire spool {}", path.display()))?;
    ensure!(
        bytes.len() <= MAX_SIGNED_WIRE_BYTES,
        "signed-wire spool exceeds maximum length: {}",
        path.display()
    );
    ensure!(
        bytes.len() as u64 == ready.wire_len,
        "signed-wire spool length mismatch: {}",
        path.display()
    );
    ensure!(
        sha256(&bytes) == ready.wire_sha256,
        "signed-wire spool hash mismatch: {}",
        path.display()
    );
    Ok(bytes)
}

fn create_private_file(path: &Path, append: bool) -> Result<File> {
    let parent = path.parent().context("private file must have a parent")?;
    validate_secure_directory(parent)?;
    ensure_absent_path(path)?;
    let mut options = OpenOptions::new();
    options.read(true).create_new(true).mode(PRIVATE_FILE_MODE);
    if append {
        options.append(true);
    } else {
        options.write(true);
    }
    options.custom_flags(O_NOFOLLOW);
    let file = options
        .open(path)
        .with_context(|| format!("create private file {}", path.display()))?;
    validate_open_file(path, &file)?;
    Ok(file)
}

fn open_private_file(path: &Path, append: bool) -> Result<File> {
    let parent = path.parent().context("private file must have a parent")?;
    validate_secure_directory(parent)?;
    validate_private_file_path(path)?;
    let mut options = OpenOptions::new();
    options.read(true);
    if append {
        options.append(true);
    } else {
        options.write(true);
    }
    options.custom_flags(O_NOFOLLOW);
    let file = options
        .open(path)
        .with_context(|| format!("open private file {}", path.display()))?;
    validate_open_file(path, &file)?;
    Ok(file)
}

fn validate_open_file(path: &Path, file: &File) -> Result<()> {
    let path_metadata = validate_private_file_path(path)?;
    let opened = file
        .metadata()
        .with_context(|| format!("inspect opened file {}", path.display()))?;
    ensure!(
        opened.is_file(),
        "opened path is not a regular file: {}",
        path.display()
    );
    ensure!(
        opened.mode() & 0o7777 == PRIVATE_FILE_MODE,
        "private file mode must be exactly 0600: {}",
        path.display()
    );
    ensure!(
        opened.nlink() == 1,
        "private file must have exactly one hard link: {}",
        path.display()
    );
    ensure!(
        opened.dev() == path_metadata.dev() && opened.ino() == path_metadata.ino(),
        "private file changed during open: {}",
        path.display()
    );
    Ok(())
}

fn validate_private_file_path(path: &Path) -> Result<fs::Metadata> {
    let parent = path.parent().context("private file must have a parent")?;
    let parent_metadata = validate_secure_directory(parent)?;
    let metadata = fs::symlink_metadata(path)
        .with_context(|| format!("inspect private file {}", path.display()))?;
    ensure!(
        metadata.file_type().is_file() && !metadata.file_type().is_symlink(),
        "private path must be a regular non-symlink file: {}",
        path.display()
    );
    ensure!(
        metadata.mode() & 0o7777 == PRIVATE_FILE_MODE,
        "private file mode must be exactly 0600: {}",
        path.display()
    );
    ensure!(
        metadata.nlink() == 1,
        "private file must have exactly one hard link: {}",
        path.display()
    );
    ensure!(
        metadata.uid() == parent_metadata.uid(),
        "private file owner differs from its directory owner: {}",
        path.display()
    );
    Ok(metadata)
}

fn validate_secure_directory(path: &Path) -> Result<fs::Metadata> {
    validate_no_symlink_components(path)?;
    let metadata = fs::symlink_metadata(path)
        .with_context(|| format!("inspect secure directory {}", path.display()))?;
    ensure!(
        metadata.file_type().is_dir() && !metadata.file_type().is_symlink(),
        "secure path must be a real directory, not a symlink: {}",
        path.display()
    );
    ensure!(
        metadata.mode() & 0o7777 == PRIVATE_DIRECTORY_MODE,
        "secure directory mode must be exactly 0700: {}",
        path.display()
    );
    Ok(metadata)
}

fn validate_no_symlink_components(path: &Path) -> Result<()> {
    ensure!(
        path.is_absolute(),
        "security-sensitive recovery paths must be absolute: {}",
        path.display()
    );
    let mut current = PathBuf::new();
    for component in path.components() {
        match component {
            Component::RootDir => current.push(Path::new("/")),
            Component::Normal(name) => {
                current.push(name);
                let metadata = fs::symlink_metadata(&current)
                    .with_context(|| format!("inspect path component {}", current.display()))?;
                ensure!(
                    !metadata.file_type().is_symlink(),
                    "security-sensitive path contains a symlink component: {}",
                    current.display()
                );
            }
            Component::CurDir | Component::ParentDir | Component::Prefix(_) => bail!(
                "security-sensitive path contains a non-normal component: {}",
                path.display()
            ),
        }
    }
    Ok(())
}

fn fsync_directory(path: &Path) -> Result<()> {
    let before = validate_secure_directory(path)?;
    let mut options = OpenOptions::new();
    options.read(true).custom_flags(O_NOFOLLOW);
    let directory = options
        .open(path)
        .with_context(|| format!("open directory for fsync {}", path.display()))?;
    let opened = directory
        .metadata()
        .with_context(|| format!("inspect opened directory {}", path.display()))?;
    ensure!(
        opened.is_dir() && opened.dev() == before.dev() && opened.ino() == before.ino(),
        "secure directory changed during open: {}",
        path.display()
    );
    directory
        .sync_all()
        .with_context(|| format!("fsync directory {}", path.display()))
}

fn ensure_absent_path(path: &Path) -> Result<()> {
    match fs::symlink_metadata(path) {
        Ok(_) => bail!("path already exists: {}", path.display()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(error).with_context(|| format!("inspect path {}", path.display())),
    }
}

fn validate_identifier(label: &str, value: &str) -> Result<()> {
    ensure!(!value.is_empty(), "{label} must not be empty");
    ensure!(
        value.len() <= MAX_IDENTIFIER_BYTES,
        "{label} exceeds {MAX_IDENTIFIER_BYTES} bytes"
    );
    ensure!(
        value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_')),
        "{label} may contain only ASCII letters, digits, '-' and '_'"
    );
    Ok(())
}

fn validate_text(label: &str, value: &str) -> Result<()> {
    ensure!(!value.trim().is_empty(), "{label} must not be empty");
    ensure!(
        value.len() <= MAX_TEXT_BYTES,
        "{label} exceeds {MAX_TEXT_BYTES} bytes"
    );
    ensure!(!value.contains('\0'), "{label} contains a NUL byte");
    Ok(())
}

fn validate_hash(label: &str, value: &str) -> Result<()> {
    ensure!(
        value.len() == 64
            && value
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
        "{label} must be 64 lowercase hexadecimal characters"
    );
    Ok(())
}

fn validate_timestamp(value: &str) -> Result<()> {
    ensure!(
        value.ends_with('Z'),
        "journal timestamp must use an explicit UTC Z suffix"
    );
    let parsed = DateTime::parse_from_rfc3339(value).context("invalid journal timestamp")?;
    ensure!(
        parsed.offset().local_minus_utc() == 0,
        "journal timestamp is not UTC"
    );
    Ok(())
}

fn validate_spool_file_name(value: &str) -> Result<()> {
    ensure!(!value.is_empty(), "spool filename must not be empty");
    let path = Path::new(value);
    ensure!(
        path.components().count() == 1
            && matches!(path.components().next(), Some(Component::Normal(_))),
        "spool filename must be one normal path component"
    );
    ensure!(
        value.starts_with("wire-") && value.ends_with(".bin"),
        "spool filename does not match the signed-wire namespace"
    );
    ensure!(
        value
            .bytes()
            .all(|byte| { byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.') }),
        "spool filename contains an unsafe character"
    );
    Ok(())
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        io::Write,
        os::unix::fs::{symlink, PermissionsExt},
        sync::atomic::{AtomicU64, Ordering},
    };

    static TEST_NONCE: AtomicU64 = AtomicU64::new(0);

    struct TestRoot {
        path: PathBuf,
    }

    impl TestRoot {
        fn new() -> Self {
            let base = fs::canonicalize(std::env::temp_dir()).expect("canonical temp directory");
            for _ in 0..128 {
                let nonce = TEST_NONCE.fetch_add(1, Ordering::Relaxed);
                let path = base.join(format!(
                    "aspis-mainnet-journal-test-{}-{nonce}",
                    std::process::id()
                ));
                let mut builder = DirBuilder::new();
                builder.mode(PRIVATE_DIRECTORY_MODE);
                match builder.create(&path) {
                    Ok(()) => return Self { path },
                    Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
                    Err(error) => panic!("create test directory: {error}"),
                }
            }
            panic!("could not reserve test directory")
        }

        fn run(&self) -> PathBuf {
            self.path.join("run")
        }
    }

    impl Drop for TestRoot {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.path);
        }
    }

    fn rewrite(path: &Path, bytes: &[u8]) {
        let mut file = OpenOptions::new()
            .write(true)
            .truncate(true)
            .open(path)
            .expect("open rewrite target");
        file.write_all(bytes).expect("rewrite bytes");
        file.sync_all().expect("sync rewrite");
    }

    fn journal_lines(path: &Path) -> Vec<Value> {
        let bytes = fs::read(path).expect("read journal");
        String::from_utf8(bytes)
            .expect("UTF-8 journal")
            .lines()
            .map(|line| serde_json::from_str(line).expect("JSON journal line"))
            .collect()
    }

    fn serialize_lines(lines: &[Value]) -> Vec<u8> {
        let mut bytes = Vec::new();
        for line in lines {
            serde_json::to_writer(&mut bytes, line).expect("serialize line");
            bytes.push(b'\n');
        }
        bytes
    }

    #[test]
    fn create_append_reopen_round_trip() {
        let root = TestRoot::new();
        let run = root.run();
        let mut journal = RecoveryJournal::create(&run, "mainnet_run_1").unwrap();
        journal
            .record_checkpoint("preflight_green", serde_json::json!({"gates": 37}))
            .unwrap();
        assert_eq!(journal.next_sequence(), 2);
        assert_eq!(journal.state().run_id.as_deref(), Some("mainnet_run_1"));
        assert_eq!(
            fs::metadata(journal.journal_path())
                .unwrap()
                .permissions()
                .mode()
                & 0o7777,
            0o600
        );
        assert_eq!(
            fs::metadata(run.join(LOCK_FILE_NAME))
                .unwrap()
                .permissions()
                .mode()
                & 0o7777,
            0o600
        );
        for directory in [&run, &run.join(SPOOL_DIRECTORY_NAME)] {
            assert_eq!(
                fs::metadata(directory).unwrap().permissions().mode() & 0o7777,
                0o700
            );
        }
        drop(journal);

        let reopened = RecoveryJournal::reopen(&run).unwrap();
        assert_eq!(reopened.next_sequence(), 2);
        assert_eq!(reopened.state().run_id.as_deref(), Some("mainnet_run_1"));
    }

    #[test]
    fn run_lock_is_exclusive() {
        let root = TestRoot::new();
        let run = root.run();
        let _first = RecoveryJournal::create(&run, "locked_run").unwrap();
        let error = RecoveryJournal::reopen(&run).unwrap_err();
        assert!(error.to_string().contains("exclusive run lock"));
    }

    #[test]
    fn signed_wire_is_private_persisted_and_recoverable() {
        let root = TestRoot::new();
        let run = root.run();
        let wire = b"complete signed transaction wire";
        let mut journal = RecoveryJournal::create(&run, "wire_run").unwrap();
        let entry = journal
            .spool_signed_wire_submit_ready("deploy_1", TransactionClass::Forward, wire)
            .unwrap();
        let spool_file = match entry.body {
            JournalBody::SignedWireSubmitReady { spool_file, .. } => spool_file,
            _ => panic!("unexpected entry type"),
        };
        let spool_path = run.join(SPOOL_DIRECTORY_NAME).join(spool_file);
        assert_eq!(fs::read(&spool_path).unwrap(), wire);
        assert_eq!(
            fs::metadata(&spool_path).unwrap().permissions().mode() & 0o7777,
            0o600
        );
        assert_eq!(journal.load_submit_ready_wire("deploy_1").unwrap(), wire);
        drop(journal);

        let mut reopened = RecoveryJournal::reopen(&run).unwrap();
        assert_eq!(reopened.load_submit_ready_wire("deploy_1").unwrap(), wire);
    }

    #[test]
    fn cleanup_only_is_irreversible_and_blocks_pending_forward_wire() {
        let root = TestRoot::new();
        let run = root.run();
        let mut journal = RecoveryJournal::create(&run, "cleanup_run").unwrap();
        journal
            .spool_signed_wire_submit_ready("forward_wire", TransactionClass::Forward, b"forward")
            .unwrap();
        journal.enter_cleanup_only("quote expired").unwrap();
        assert!(journal.load_submit_ready_wire("forward_wire").is_err());
        assert!(journal
            .spool_signed_wire_submit_ready(
                "another_forward",
                TransactionClass::Forward,
                b"forbidden",
            )
            .is_err());
        journal
            .spool_signed_wire_submit_ready("close_program", TransactionClass::Cleanup, b"cleanup")
            .unwrap();
        assert_eq!(
            journal.load_submit_ready_wire("close_program").unwrap(),
            b"cleanup"
        );
        assert!(journal.enter_cleanup_only("cannot reset").is_err());
        drop(journal);

        let reopened = RecoveryJournal::reopen(&run).unwrap();
        assert!(matches!(reopened.state().mode, RunMode::CleanupOnly { .. }));
    }

    #[test]
    fn reducer_rejects_forward_submission_after_cleanup_entry() {
        let root = TestRoot::new();
        let run = root.run();
        let mut journal = RecoveryJournal::create(&run, "submission_run").unwrap();
        journal
            .spool_signed_wire_submit_ready("forward", TransactionClass::Forward, b"wire")
            .unwrap();
        journal.enter_cleanup_only("fee gate failed").unwrap();
        assert!(journal.record_submission("forward", "signature").is_err());
    }

    #[test]
    fn reopen_rejects_truncated_journal() {
        let root = TestRoot::new();
        let run = root.run();
        let journal = RecoveryJournal::create(&run, "truncated_run").unwrap();
        let path = journal.journal_path().to_path_buf();
        drop(journal);
        let mut bytes = fs::read(&path).unwrap();
        assert_eq!(bytes.pop(), Some(b'\n'));
        rewrite(&path, &bytes);
        let error = RecoveryJournal::reopen(&run).unwrap_err();
        assert!(error.to_string().contains("truncated"));
    }

    #[test]
    fn durable_lock_anchor_rejects_clean_suffix_truncation() {
        let root = TestRoot::new();
        let run = root.run();
        let mut journal = RecoveryJournal::create(&run, "suffix_truncated_run").unwrap();
        journal
            .record_checkpoint("durable_tail", serde_json::json!({"value": 7}))
            .unwrap();
        let path = journal.journal_path().to_path_buf();
        drop(journal);

        let bytes = fs::read(&path).unwrap();
        let prior_newline = bytes[..bytes.len() - 1]
            .iter()
            .rposition(|byte| *byte == b'\n')
            .unwrap();
        rewrite(&path, &bytes[..=prior_newline]);
        let error = RecoveryJournal::reopen(&run).unwrap_err();
        assert!(error.to_string().contains("durable lock anchor"));
    }

    #[test]
    fn reopen_rejects_entry_tamper() {
        let root = TestRoot::new();
        let run = root.run();
        let mut journal = RecoveryJournal::create(&run, "tamper_run").unwrap();
        journal
            .record_checkpoint("before", serde_json::json!({"value": 1}))
            .unwrap();
        let path = journal.journal_path().to_path_buf();
        drop(journal);
        let mut lines = journal_lines(&path);
        lines[1]["body"]["details"]["value"] = serde_json::json!(2);
        rewrite(&path, &serialize_lines(&lines));
        let error = RecoveryJournal::reopen(&run).unwrap_err();
        assert!(error.to_string().contains("entry hash mismatch"));
    }

    #[test]
    fn reopen_rejects_unknown_schema_and_body_type() {
        let root = TestRoot::new();
        let run = root.run();
        let journal = RecoveryJournal::create(&run, "schema_run").unwrap();
        let path = journal.journal_path().to_path_buf();
        drop(journal);
        let original = journal_lines(&path);

        let mut unknown_schema = original.clone();
        unknown_schema[0]["schema"] = serde_json::json!("future/v99");
        rewrite(&path, &serialize_lines(&unknown_schema));
        let error = RecoveryJournal::reopen(&run).unwrap_err();
        assert!(error
            .to_string()
            .contains("unknown recovery journal schema"));

        let mut unknown_body = original;
        unknown_body[0]["body"]["type"] = serde_json::json!("leave_cleanup_only");
        rewrite(&path, &serialize_lines(&unknown_body));
        let error = RecoveryJournal::reopen(&run).unwrap_err();
        assert!(error.to_string().contains("decode journal line"));
    }

    #[test]
    fn reopen_rejects_spool_tamper_or_loss() {
        let root = TestRoot::new();
        let run = root.run();
        let mut journal = RecoveryJournal::create(&run, "spool_tamper_run").unwrap();
        let entry = journal
            .spool_signed_wire_submit_ready("wire", TransactionClass::Forward, b"original")
            .unwrap();
        let spool = match entry.body {
            JournalBody::SignedWireSubmitReady { spool_file, .. } => {
                run.join(SPOOL_DIRECTORY_NAME).join(spool_file)
            }
            _ => unreachable!(),
        };
        drop(journal);

        rewrite(&spool, b"tampered");
        let error = RecoveryJournal::reopen(&run).unwrap_err();
        assert!(format!("{error:#}").contains("spool hash mismatch"));

        fs::remove_file(&spool).unwrap();
        let error = RecoveryJournal::reopen(&run).unwrap_err();
        assert!(format!("{error:#}").contains("validate submit-ready spool"));
    }

    #[test]
    fn modes_and_symlinks_fail_closed() {
        let root = TestRoot::new();
        let insecure_parent = root.path.join("insecure");
        fs::create_dir(&insecure_parent).unwrap();
        fs::set_permissions(&insecure_parent, fs::Permissions::from_mode(0o755)).unwrap();
        assert!(RecoveryJournal::create(insecure_parent.join("run"), "bad_parent").is_err());

        let real_parent = root.path.join("real-parent");
        let mut builder = DirBuilder::new();
        builder.mode(PRIVATE_DIRECTORY_MODE);
        builder.create(&real_parent).unwrap();
        let linked_parent = root.path.join("linked-parent");
        symlink(&real_parent, &linked_parent).unwrap();
        let error =
            RecoveryJournal::create(linked_parent.join("run"), "linked_parent").unwrap_err();
        assert!(error.to_string().contains("symlink component"));

        let run = root.run();
        let journal = RecoveryJournal::create(&run, "mode_run").unwrap();
        let journal_path = journal.journal_path().to_path_buf();
        drop(journal);
        fs::set_permissions(&journal_path, fs::Permissions::from_mode(0o644)).unwrap();
        assert!(RecoveryJournal::reopen(&run).is_err());
        fs::set_permissions(&journal_path, fs::Permissions::from_mode(0o600)).unwrap();

        let real_journal = run.join("real-journal");
        fs::rename(&journal_path, &real_journal).unwrap();
        symlink(&real_journal, &journal_path).unwrap();
        let error = RecoveryJournal::reopen(&run).unwrap_err();
        assert!(error.to_string().contains("non-symlink"));
    }

    #[test]
    fn unsafe_identifiers_and_event_order_are_rejected() {
        let root = TestRoot::new();
        assert!(RecoveryJournal::create(root.run(), "../escape").is_err());

        let run = root.path.join("second-run");
        let mut journal = RecoveryJournal::create(&run, "safe_run").unwrap();
        assert!(journal
            .spool_signed_wire_submit_ready("../escape", TransactionClass::Forward, b"wire")
            .is_err());
        assert!(journal.record_submission("unknown", "signature").is_err());
        journal.complete("cancelled before signing").unwrap();
        assert!(journal
            .record_checkpoint("too_late", serde_json::json!({}))
            .is_err());
    }

    #[test]
    fn every_append_revalidates_external_changes() {
        let root = TestRoot::new();
        let run = root.run();
        let mut journal = RecoveryJournal::create(&run, "live_tamper_run").unwrap();
        let path = journal.journal_path().to_path_buf();
        let mut lines = journal_lines(&path);
        lines[0]["body"]["run_id"] = serde_json::json!("changed_run");
        rewrite(&path, &serialize_lines(&lines));
        let error = journal
            .record_checkpoint("must_fail", serde_json::json!({}))
            .unwrap_err();
        assert!(error.to_string().contains("entry hash mismatch"));
    }
}
