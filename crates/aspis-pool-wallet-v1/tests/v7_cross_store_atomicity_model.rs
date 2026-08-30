//! Executable reference model for the V2 cross-store commit protocol.
//!
//! This deliberately does not share implementation code with the durable V2
//! coordinator.  Production tests can project each durable store into
//! [`StoreSet`] and compare it with `transition` after every injected crash.
//! The model's recovery decision is monotone: once `Prepared` is durably
//! renamed, every phase rolls forward to `post`. Before that rename, the
//! authoritative state remains exactly `pre`.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::{Arc, Mutex},
    thread,
};

const LOCAL_KEY_ID: u32 = 7;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct EventIdentity {
    lane: u8,
    sequence: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct NoteRecord {
    event: EventIdentity,
    note_id: u64,
    key_id: u32,
    nonce: [u8; 4],
    ciphertext: Vec<u8>,
    authenticated: bool,
    spent_by: Option<u64>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CanonicalEvent {
    id: EventIdentity,
    content: u64,
    finalized_cursor: u64,
    checkpoint: u64,
    output: Option<NoteRecord>,
    spend: Option<(u64, u64)>,
    relayer_request: u64,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd)]
enum Finality {
    Unfinalized,
    Confirmed,
    Finalized,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct RelayerObservation {
    event: CanonicalEvent,
    finality: Finality,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Checkpoint {
    id: u64,
    finalized_cursor: u64,
    lane_sequences: BTreeMap<u8, u64>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Action {
    Observe(CanonicalEvent, Finality),
    Finalize(CanonicalEvent),
    Reorg(EventIdentity),
    Checkpoint(Checkpoint),
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct NoteStore {
    generation: u64,
    records: BTreeMap<u64, NoteRecord>,
    used_nonces: BTreeSet<(u32, [u8; 4])>,
    legacy_notes: BTreeSet<u64>,
    legacy_spent: BTreeMap<u64, u64>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct ForestStore {
    generation: u64,
    events: BTreeMap<EventIdentity, CanonicalEvent>,
    lane_sequences: BTreeMap<u8, u64>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CursorStore {
    generation: u64,
    finalized_cursor: u64,
    current_checkpoint: u64,
    checkpoints: BTreeMap<u64, Checkpoint>,
}

impl Default for CursorStore {
    fn default() -> Self {
        let genesis = Checkpoint {
            id: 0,
            finalized_cursor: 0,
            lane_sequences: BTreeMap::new(),
        };
        Self {
            generation: 0,
            finalized_cursor: 0,
            current_checkpoint: 0,
            checkpoints: BTreeMap::from([(0, genesis)]),
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct SpendStore {
    generation: u64,
    nullifiers: BTreeMap<u64, u64>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct RelayerStore {
    generation: u64,
    observations: BTreeMap<EventIdentity, RelayerObservation>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct StoreSet {
    notes: NoteStore,
    forest: ForestStore,
    cursor: CursorStore,
    spends: SpendStore,
    relayer: RelayerStore,
}

impl StoreSet {
    fn generation(&self) -> Option<u64> {
        let generations = [
            self.notes.generation,
            self.forest.generation,
            self.cursor.generation,
            self.spends.generation,
            self.relayer.generation,
        ];
        generations
            .iter()
            .all(|generation| *generation == generations[0])
            .then_some(generations[0])
    }

    fn is_coherent(&self) -> bool {
        if self.generation().is_none() {
            return false;
        }
        let Some(checkpoint) = self.cursor.checkpoints.get(&self.cursor.current_checkpoint) else {
            return false;
        };
        if checkpoint.finalized_cursor > self.cursor.finalized_cursor {
            return false;
        }
        if checkpoint.lane_sequences.iter().any(|(lane, sequence)| {
            self.forest.lane_sequences.get(lane).copied().unwrap_or(0) < *sequence
        }) {
            return false;
        }
        let mut event_lane_sequences = BTreeMap::new();
        let mut supported_cursor = checkpoint.finalized_cursor;
        for (identity, event) in &self.forest.events {
            if event.id != *identity {
                return false;
            }
            supported_cursor = supported_cursor.max(event.finalized_cursor);
            let sequence = event_lane_sequences.entry(identity.lane).or_insert(0);
            *sequence = (*sequence).max(identity.sequence);
        }
        if event_lane_sequences != self.forest.lane_sequences
            || supported_cursor != self.cursor.finalized_cursor
        {
            return false;
        }
        if self.forest.lane_sequences.iter().any(|(lane, maximum)| {
            (1..=*maximum).any(|sequence| {
                !self.forest.events.contains_key(&EventIdentity {
                    lane: *lane,
                    sequence,
                })
            })
        }) {
            return false;
        }
        if self.forest.events.iter().any(|(identity, event)| {
            self.relayer
                .observations
                .get(identity)
                .is_none_or(|observation| {
                    observation.finality != Finality::Finalized || observation.event != *event
                })
        }) || self
            .relayer
            .observations
            .iter()
            .any(|(identity, observation)| {
                observation.finality == Finality::Finalized
                    && self.forest.events.get(identity) != Some(&observation.event)
            })
        {
            return false;
        }
        if self.notes.records.values().any(|note| {
            !note.authenticated
                || note.key_id != LOCAL_KEY_ID
                || note.nonce == [0; 4]
                || note.ciphertext.is_empty()
                || !self.notes.used_nonces.contains(&(note.key_id, note.nonce))
                || self.forest.events.get(&note.event).is_none_or(|event| {
                    event.output.as_ref().map(|output| output.note_id) != Some(note.note_id)
                })
        }) {
            return false;
        }
        if self.spends.nullifiers.iter().any(|(nullifier, note_id)| {
            self.notes
                .records
                .get(note_id)
                .map(|note| note.spent_by != Some(*nullifier))
                .unwrap_or_else(|| self.notes.legacy_spent.get(nullifier) != Some(note_id))
        }) {
            return false;
        }
        self.notes.records.values().all(|note| {
            note.spent_by.is_none_or(|nullifier| {
                self.spends.nullifiers.get(&nullifier) == Some(&note.note_id)
            })
        })
    }

    fn advance_generation(&mut self) -> Result<(), ModelError> {
        let next = self
            .generation()
            .ok_or(ModelError::MixedStoreGeneration)?
            .checked_add(1)
            .ok_or(ModelError::GenerationOverflow)?;
        self.notes.generation = next;
        self.forest.generation = next;
        self.cursor.generation = next;
        self.spends.generation = next;
        self.relayer.generation = next;
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Outcome {
    Applied,
    Noop,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ModelError {
    Busy,
    Conflict,
    CorruptCiphertext,
    CorruptJournal,
    CorruptStore,
    DuplicateNote,
    FinalizedRollback,
    GenerationOverflow,
    IncompleteMigration,
    MixedStoreGeneration,
    NonceCollision,
    OutOfOrder,
    PendingJournal,
    StaleCheckpoint,
    UnknownCheckpoint,
    UnknownNote,
    WrongKeyId,
}

fn transition(state: &StoreSet, action: &Action) -> Result<(StoreSet, Outcome), ModelError> {
    if !state.is_coherent() {
        return Err(ModelError::CorruptStore);
    }
    let mut post = state.clone();
    let changed = match action {
        Action::Observe(event, finality) => observe(&mut post, event, *finality)?,
        Action::Finalize(event) => finalize(&mut post, event)?,
        Action::Reorg(identity) => reorg(&mut post, *identity)?,
        Action::Checkpoint(point) => checkpoint(&mut post, point)?,
    };
    if !changed {
        return Ok((state.clone(), Outcome::Noop));
    }
    post.advance_generation()?;
    if !post.is_coherent() {
        return Err(ModelError::CorruptStore);
    }
    Ok((post, Outcome::Applied))
}

fn observe(
    state: &mut StoreSet,
    event: &CanonicalEvent,
    finality: Finality,
) -> Result<bool, ModelError> {
    if let Some(committed) = state.forest.events.get(&event.id) {
        if committed != event {
            return Err(ModelError::Conflict);
        }
        return Ok(false);
    }
    match state.relayer.observations.get_mut(&event.id) {
        Some(observation) if observation.event != *event => Err(ModelError::Conflict),
        Some(observation) if observation.finality >= finality => Ok(false),
        Some(observation) => {
            observation.finality = finality;
            Ok(true)
        }
        None => {
            state.relayer.observations.insert(
                event.id,
                RelayerObservation {
                    event: event.clone(),
                    finality,
                },
            );
            Ok(true)
        }
    }
}

fn finalize(state: &mut StoreSet, event: &CanonicalEvent) -> Result<bool, ModelError> {
    if let Some(committed) = state.forest.events.get(&event.id) {
        return if committed == event {
            Ok(false)
        } else {
            Err(ModelError::Conflict)
        };
    }
    if let Some(observation) = state.relayer.observations.get(&event.id) {
        if observation.event != *event {
            return Err(ModelError::Conflict);
        }
    }
    match state.cursor.checkpoints.get(&event.checkpoint) {
        None => return Err(ModelError::UnknownCheckpoint),
        Some(_) if event.checkpoint != state.cursor.current_checkpoint => {
            return Err(ModelError::StaleCheckpoint);
        }
        Some(_) => {}
    }
    let expected_sequence = state
        .forest
        .lane_sequences
        .get(&event.id.lane)
        .copied()
        .unwrap_or(0)
        .checked_add(1)
        .ok_or(ModelError::OutOfOrder)?;
    if event.id.sequence != expected_sequence
        || event.finalized_cursor <= state.cursor.finalized_cursor
    {
        return Err(ModelError::OutOfOrder);
    }
    if let Some(output) = &event.output {
        validate_output(state, event.id, output)?;
    }
    if let Some((note_id, nullifier)) = event.spend {
        let note = state
            .notes
            .records
            .get(&note_id)
            .ok_or(ModelError::UnknownNote)?;
        if note.spent_by.is_some() || state.spends.nullifiers.contains_key(&nullifier) {
            return Err(ModelError::Conflict);
        }
    }

    if let Some((note_id, nullifier)) = event.spend {
        state.notes.records.get_mut(&note_id).unwrap().spent_by = Some(nullifier);
        state.spends.nullifiers.insert(nullifier, note_id);
    }
    if let Some(output) = &event.output {
        state
            .notes
            .used_nonces
            .insert((output.key_id, output.nonce));
        state.notes.records.insert(output.note_id, output.clone());
    }
    state.forest.events.insert(event.id, event.clone());
    state
        .forest
        .lane_sequences
        .insert(event.id.lane, event.id.sequence);
    state.cursor.finalized_cursor = event.finalized_cursor;
    state.relayer.observations.insert(
        event.id,
        RelayerObservation {
            event: event.clone(),
            finality: Finality::Finalized,
        },
    );
    Ok(true)
}

fn validate_output(
    state: &StoreSet,
    event: EventIdentity,
    output: &NoteRecord,
) -> Result<(), ModelError> {
    if output.event != event {
        return Err(ModelError::CorruptCiphertext);
    }
    if output.key_id != LOCAL_KEY_ID {
        return Err(ModelError::WrongKeyId);
    }
    if !output.authenticated || output.ciphertext.is_empty() {
        return Err(ModelError::CorruptCiphertext);
    }
    if output.nonce == [0; 4]
        || state
            .notes
            .used_nonces
            .contains(&(output.key_id, output.nonce))
    {
        return Err(ModelError::NonceCollision);
    }
    if state.notes.records.contains_key(&output.note_id)
        || state.notes.legacy_notes.contains(&output.note_id)
    {
        return Err(ModelError::DuplicateNote);
    }
    Ok(())
}

fn reorg(state: &mut StoreSet, identity: EventIdentity) -> Result<bool, ModelError> {
    if state.forest.events.contains_key(&identity)
        || state
            .relayer
            .observations
            .get(&identity)
            .is_some_and(|observation| observation.finality == Finality::Finalized)
    {
        return Err(ModelError::FinalizedRollback);
    }
    Ok(state.relayer.observations.remove(&identity).is_some())
}

fn checkpoint(state: &mut StoreSet, checkpoint: &Checkpoint) -> Result<bool, ModelError> {
    if let Some(existing) = state.cursor.checkpoints.get(&checkpoint.id) {
        return if existing == checkpoint {
            Ok(false)
        } else {
            Err(ModelError::Conflict)
        };
    }
    if checkpoint.id != state.cursor.current_checkpoint + 1
        || checkpoint.finalized_cursor < state.cursor.finalized_cursor
        || checkpoint.lane_sequences != state.forest.lane_sequences
    {
        return Err(ModelError::StaleCheckpoint);
    }
    state
        .cursor
        .checkpoints
        .insert(checkpoint.id, checkpoint.clone());
    state.cursor.current_checkpoint = checkpoint.id;
    state.cursor.finalized_cursor = checkpoint.finalized_cursor;
    Ok(true)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Phase {
    Prepared,
    StoresApplied,
    Committed,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Journal {
    phase: Phase,
    action: Action,
    pre: StoreSet,
    post: StoreSet,
    checksum_valid: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum StoreKind {
    Notes,
    Forest,
    Cursor,
    Spends,
    Relayer,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Disk {
    stores: StoreSet,
    journal: Option<Journal>,
    journal_temp: Option<Journal>,
    store_temp: Option<StoreKind>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Boundary {
    PreparedWrite,
    PreparedFsync,
    PreparedRename,
    PreparedDirFsync,
    NotesWrite,
    NotesFsync,
    NotesRename,
    NotesDirFsync,
    ForestWrite,
    ForestFsync,
    ForestRename,
    ForestDirFsync,
    CursorWrite,
    CursorFsync,
    CursorRename,
    CursorDirFsync,
    SpendsWrite,
    SpendsFsync,
    SpendsRename,
    SpendsDirFsync,
    RelayerWrite,
    RelayerFsync,
    RelayerRename,
    RelayerDirFsync,
    StoresAppliedWrite,
    StoresAppliedFsync,
    StoresAppliedRename,
    StoresAppliedDirFsync,
    CommittedWrite,
    CommittedFsync,
    CommittedRename,
    CommittedDirFsync,
    JournalRemove,
    JournalRemoveDirFsync,
}

impl Boundary {
    const ALL: [Self; 34] = [
        Self::PreparedWrite,
        Self::PreparedFsync,
        Self::PreparedRename,
        Self::PreparedDirFsync,
        Self::NotesWrite,
        Self::NotesFsync,
        Self::NotesRename,
        Self::NotesDirFsync,
        Self::ForestWrite,
        Self::ForestFsync,
        Self::ForestRename,
        Self::ForestDirFsync,
        Self::CursorWrite,
        Self::CursorFsync,
        Self::CursorRename,
        Self::CursorDirFsync,
        Self::SpendsWrite,
        Self::SpendsFsync,
        Self::SpendsRename,
        Self::SpendsDirFsync,
        Self::RelayerWrite,
        Self::RelayerFsync,
        Self::RelayerRename,
        Self::RelayerDirFsync,
        Self::StoresAppliedWrite,
        Self::StoresAppliedFsync,
        Self::StoresAppliedRename,
        Self::StoresAppliedDirFsync,
        Self::CommittedWrite,
        Self::CommittedFsync,
        Self::CommittedRename,
        Self::CommittedDirFsync,
        Self::JournalRemove,
        Self::JournalRemoveDirFsync,
    ];

    fn recovery_selects_post(self) -> bool {
        Self::ALL
            .iter()
            .position(|boundary| *boundary == self)
            .unwrap()
            >= Self::ALL
                .iter()
                .position(|boundary| *boundary == Self::PreparedRename)
                .unwrap()
    }
}

impl Disk {
    fn apply_clean(&mut self, action: Action) -> Result<Outcome, ModelError> {
        self.apply_until(action, None)
    }

    fn apply_until(
        &mut self,
        action: Action,
        crash_after: Option<Boundary>,
    ) -> Result<Outcome, ModelError> {
        if self.journal.is_some() {
            return Err(ModelError::PendingJournal);
        }
        let (post, outcome) = transition(&self.stores, &action)?;
        if outcome == Outcome::Noop {
            return Ok(outcome);
        }
        let journal = Journal {
            phase: Phase::Prepared,
            action,
            pre: self.stores.clone(),
            post,
            checksum_valid: true,
        };
        for boundary in Boundary::ALL {
            self.cross(boundary, &journal);
            if crash_after == Some(boundary) {
                return Err(ModelError::Busy);
            }
        }
        Ok(Outcome::Applied)
    }

    fn cross(&mut self, boundary: Boundary, prepared: &Journal) {
        match boundary {
            Boundary::PreparedWrite => self.journal_temp = Some(prepared.clone()),
            Boundary::PreparedFsync | Boundary::PreparedDirFsync => {}
            Boundary::PreparedRename => {
                self.journal = self.journal_temp.take();
            }
            Boundary::NotesWrite => self.store_temp = Some(StoreKind::Notes),
            Boundary::NotesFsync | Boundary::NotesDirFsync => {}
            Boundary::NotesRename => {
                self.stores.notes = prepared.post.notes.clone();
                self.store_temp = None;
            }
            Boundary::ForestWrite => self.store_temp = Some(StoreKind::Forest),
            Boundary::ForestFsync | Boundary::ForestDirFsync => {}
            Boundary::ForestRename => {
                self.stores.forest = prepared.post.forest.clone();
                self.store_temp = None;
            }
            Boundary::CursorWrite => self.store_temp = Some(StoreKind::Cursor),
            Boundary::CursorFsync | Boundary::CursorDirFsync => {}
            Boundary::CursorRename => {
                self.stores.cursor = prepared.post.cursor.clone();
                self.store_temp = None;
            }
            Boundary::SpendsWrite => self.store_temp = Some(StoreKind::Spends),
            Boundary::SpendsFsync | Boundary::SpendsDirFsync => {}
            Boundary::SpendsRename => {
                self.stores.spends = prepared.post.spends.clone();
                self.store_temp = None;
            }
            Boundary::RelayerWrite => self.store_temp = Some(StoreKind::Relayer),
            Boundary::RelayerFsync | Boundary::RelayerDirFsync => {}
            Boundary::RelayerRename => {
                self.stores.relayer = prepared.post.relayer.clone();
                self.store_temp = None;
            }
            Boundary::StoresAppliedWrite => {
                let mut marker = self.journal.as_ref().unwrap().clone();
                marker.phase = Phase::StoresApplied;
                self.journal_temp = Some(marker);
            }
            Boundary::StoresAppliedFsync | Boundary::StoresAppliedDirFsync => {}
            Boundary::StoresAppliedRename => {
                self.journal = self.journal_temp.take();
            }
            Boundary::CommittedWrite => {
                let mut marker = self.journal.as_ref().unwrap().clone();
                marker.phase = Phase::Committed;
                self.journal_temp = Some(marker);
            }
            Boundary::CommittedFsync | Boundary::CommittedDirFsync => {}
            Boundary::CommittedRename => {
                self.journal = self.journal_temp.take();
            }
            Boundary::JournalRemove => self.journal = None,
            Boundary::JournalRemoveDirFsync => {}
        }
    }

    fn recover(&mut self) -> Result<(), ModelError> {
        self.journal_temp = None;
        self.store_temp = None;
        let Some(journal) = self.journal.as_ref() else {
            return self
                .stores
                .is_coherent()
                .then_some(())
                .ok_or(ModelError::CorruptStore);
        };
        if !journal.checksum_valid {
            return Err(ModelError::CorruptJournal);
        }
        let target = match journal.phase {
            Phase::Prepared | Phase::StoresApplied | Phase::Committed => &journal.post,
        };
        if !target.is_coherent() {
            return Err(ModelError::CorruptJournal);
        }
        self.stores = target.clone();
        self.journal = None;
        Ok(())
    }
}

fn event(
    lane: u8,
    sequence: u64,
    cursor: u64,
    checkpoint: u64,
    note_id: Option<u64>,
    spend: Option<(u64, u64)>,
) -> CanonicalEvent {
    let id = EventIdentity { lane, sequence };
    CanonicalEvent {
        id,
        content: 1_000 + cursor,
        finalized_cursor: cursor,
        checkpoint,
        output: note_id.map(|note_id| NoteRecord {
            event: id,
            note_id,
            key_id: LOCAL_KEY_ID,
            nonce: [lane + 1, sequence as u8, cursor as u8, note_id as u8],
            ciphertext: vec![0xa5, cursor as u8, note_id as u8],
            authenticated: true,
            spent_by: None,
        }),
        spend,
        relayer_request: 9_000 + cursor,
    }
}

fn finalized(disk: &mut Disk, event: CanonicalEvent) {
    assert_eq!(
        disk.apply_clean(Action::Finalize(event)),
        Ok(Outcome::Applied)
    );
}

#[test]
fn every_write_fsync_and_rename_boundary_recovers_to_exact_pre_or_post() {
    let mut baseline = Disk::default();
    finalized(&mut baseline, event(0, 1, 1, 0, Some(10), None));
    let next = Action::Finalize(event(1, 1, 2, 0, Some(11), Some((10, 700))));
    let pre = baseline.stores.clone();
    let post = transition(&pre, &next).unwrap().0;

    // A crash before the first journal write is trivially the exact pre-state.
    let mut before_first_write = baseline.clone();
    before_first_write.recover().unwrap();
    assert_eq!(before_first_write.stores, pre);

    for boundary in Boundary::ALL {
        let mut crashed = baseline.clone();
        assert_eq!(
            crashed.apply_until(next.clone(), Some(boundary)),
            Err(ModelError::Busy),
            "fault injection at {boundary:?}"
        );
        crashed.recover().unwrap();
        let expected = if boundary.recovery_selects_post() {
            &post
        } else {
            &pre
        };
        assert_eq!(&crashed.stores, expected, "recovery at {boundary:?}");
        let recovered_once = crashed.clone();
        crashed.recover().unwrap();
        assert_eq!(crashed, recovered_once, "repeated recovery at {boundary:?}");
        assert!(crashed.stores.is_coherent());
    }
}

#[test]
fn deterministic_crash_replay_sequences_match_the_pure_reference_transition() {
    let actions = vec![
        Action::Finalize(event(0, 1, 1, 0, Some(10), None)),
        Action::Finalize(event(1, 1, 2, 0, Some(11), None)),
        Action::Checkpoint(Checkpoint {
            id: 1,
            finalized_cursor: 3,
            lane_sequences: BTreeMap::from([(0, 1), (1, 1)]),
        }),
        Action::Finalize(event(0, 2, 4, 1, Some(12), Some((10, 700)))),
        Action::Finalize(event(1, 2, 5, 1, None, Some((11, 701)))),
    ];

    for seed in 0..128_u64 {
        let mut random = seed ^ 0x9e37_79b9_7f4a_7c15;
        let mut disk = Disk::default();
        let mut reference = StoreSet::default();
        for action in &actions {
            random = random
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let boundary = Boundary::ALL[(random as usize) % Boundary::ALL.len()];
            assert_eq!(
                disk.apply_until(action.clone(), Some(boundary)),
                Err(ModelError::Busy)
            );
            disk.recover().unwrap();
            disk.recover().unwrap();
            let (expected, _) = transition(&reference, action).unwrap();
            let outcome = disk.apply_clean(action.clone()).unwrap();
            assert!(matches!(outcome, Outcome::Applied | Outcome::Noop));
            assert_eq!(disk.stores, expected, "seed {seed}, action {action:?}");
            reference = expected;
        }
    }
}

#[test]
fn replay_conflict_lane_order_and_checkpoint_validation_are_fail_closed() {
    let mut disk = Disk::default();
    let first = event(0, 1, 1, 0, Some(10), None);
    finalized(&mut disk, first.clone());
    let committed = disk.clone();
    assert_eq!(
        disk.apply_clean(Action::Finalize(first.clone())),
        Ok(Outcome::Noop)
    );
    assert_eq!(disk, committed);

    let mut conflict = first.clone();
    conflict.content ^= 1;
    assert_eq!(
        disk.apply_clean(Action::Finalize(conflict)),
        Err(ModelError::Conflict)
    );
    assert_eq!(disk, committed);

    assert_eq!(
        disk.apply_clean(Action::Finalize(event(0, 3, 2, 0, None, None))),
        Err(ModelError::OutOfOrder)
    );
    assert_eq!(
        disk.apply_clean(Action::Finalize(event(1, 1, 2, 77, None, None))),
        Err(ModelError::UnknownCheckpoint)
    );
    assert_eq!(disk, committed);

    let checkpoint = Checkpoint {
        id: 1,
        finalized_cursor: 2,
        lane_sequences: BTreeMap::from([(0, 1)]),
    };
    assert_eq!(
        disk.apply_clean(Action::Checkpoint(checkpoint.clone())),
        Ok(Outcome::Applied)
    );
    let at_checkpoint = disk.clone();
    assert_eq!(
        disk.apply_clean(Action::Checkpoint(checkpoint)),
        Ok(Outcome::Noop)
    );
    assert_eq!(
        disk.apply_clean(Action::Finalize(event(1, 1, 3, 0, None, None))),
        Err(ModelError::StaleCheckpoint)
    );
    assert_eq!(disk, at_checkpoint);
    finalized(&mut disk, event(1, 1, 3, 1, None, None));
    finalized(&mut disk, event(0, 2, 4, 1, None, None));
    assert_eq!(
        disk.stores.forest.lane_sequences,
        BTreeMap::from([(0, 2), (1, 1)])
    );
}

#[test]
fn relayer_observations_do_not_promote_or_rollback_finalized_wallet_state() {
    let candidate = event(0, 1, 1, 0, Some(10), None);
    let mut disk = Disk::default();
    assert_eq!(
        disk.apply_clean(Action::Observe(candidate.clone(), Finality::Unfinalized)),
        Ok(Outcome::Applied)
    );
    assert!(disk.stores.notes.records.is_empty());
    assert!(disk.stores.forest.events.is_empty());
    assert_eq!(disk.stores.cursor.finalized_cursor, 0);

    // Lose power after the confirmed relayer store rename. A durable
    // `Prepared` record is authoritative, so recovery rolls every logical
    // store forward together.
    assert_eq!(
        disk.apply_until(
            Action::Observe(candidate.clone(), Finality::Confirmed),
            Some(Boundary::RelayerRename)
        ),
        Err(ModelError::Busy)
    );
    disk.recover().unwrap();
    assert_eq!(
        disk.apply_clean(Action::Observe(candidate.clone(), Finality::Confirmed)),
        Ok(Outcome::Noop)
    );
    assert!(disk.stores.notes.records.is_empty());
    assert_eq!(
        disk.apply_clean(Action::Reorg(candidate.id)),
        Ok(Outcome::Applied)
    );
    assert!(!disk.stores.relayer.observations.contains_key(&candidate.id));

    assert_eq!(
        disk.apply_clean(Action::Observe(candidate.clone(), Finality::Confirmed)),
        Ok(Outcome::Applied)
    );
    assert_eq!(
        disk.apply_until(
            Action::Finalize(candidate.clone()),
            Some(Boundary::StoresAppliedRename)
        ),
        Err(ModelError::Busy)
    );
    disk.recover().unwrap();
    assert_eq!(
        disk.stores.relayer.observations[&candidate.id].finality,
        Finality::Finalized
    );
    assert!(disk.stores.notes.records.contains_key(&10));
    let finalized_state = disk.clone();
    assert_eq!(
        disk.apply_clean(Action::Reorg(candidate.id)),
        Err(ModelError::FinalizedRollback)
    );
    assert_eq!(
        disk.apply_clean(Action::Observe(candidate, Finality::Confirmed)),
        Ok(Outcome::Noop)
    );
    assert_eq!(disk, finalized_state);

    let spender = event(0, 2, 2, 0, Some(11), Some((10, 700)));
    assert_eq!(
        disk.apply_clean(Action::Observe(spender.clone(), Finality::Confirmed)),
        Ok(Outcome::Applied)
    );
    finalized(&mut disk, spender.clone());
    let finalized_spend = disk.clone();
    assert_eq!(
        disk.apply_clean(Action::Reorg(spender.id)),
        Err(ModelError::FinalizedRollback)
    );
    assert_eq!(disk, finalized_spend);
    assert_eq!(disk.stores.notes.records[&10].spent_by, Some(700));
    assert_eq!(disk.stores.spends.nullifiers.get(&700), Some(&10));
    assert_eq!(disk.stores.cursor.finalized_cursor, 2);
    assert!(disk.stores.is_coherent());
}

#[test]
fn corruption_key_nonce_and_concurrent_duplicate_application_fail_closed() {
    let baseline = Disk::default();
    let valid = event(0, 1, 1, 0, Some(10), None);

    let mut wrong_key = valid.clone();
    wrong_key.output.as_mut().unwrap().key_id += 1;
    let mut disk = baseline.clone();
    assert_eq!(
        disk.apply_clean(Action::Finalize(wrong_key)),
        Err(ModelError::WrongKeyId)
    );
    assert_eq!(disk, baseline);

    let mut corrupt = valid.clone();
    corrupt.output.as_mut().unwrap().authenticated = false;
    assert_eq!(
        disk.apply_clean(Action::Finalize(corrupt)),
        Err(ModelError::CorruptCiphertext)
    );
    assert_eq!(disk, baseline);

    let mut wrong_event_metadata = valid.clone();
    wrong_event_metadata.output.as_mut().unwrap().event = EventIdentity {
        lane: 7,
        sequence: 99,
    };
    assert_eq!(
        disk.apply_clean(Action::Finalize(wrong_event_metadata)),
        Err(ModelError::CorruptCiphertext)
    );
    assert_eq!(disk, baseline);

    finalized(&mut disk, valid.clone());
    let after_first = disk.clone();
    let mut collision = event(1, 1, 2, 0, Some(11), None);
    collision.output.as_mut().unwrap().nonce = valid.output.as_ref().unwrap().nonce;
    assert_eq!(
        disk.apply_clean(Action::Finalize(collision)),
        Err(ModelError::NonceCollision)
    );
    assert_eq!(disk, after_first);

    let mut corrupt_store = disk.clone();
    corrupt_store
        .stores
        .notes
        .records
        .get_mut(&10)
        .unwrap()
        .authenticated = false;
    let corrupt_snapshot = corrupt_store.clone();
    assert_eq!(
        corrupt_store.apply_clean(Action::Finalize(event(1, 1, 2, 0, None, None))),
        Err(ModelError::CorruptStore)
    );
    assert_eq!(corrupt_store, corrupt_snapshot);

    // A torn, unrenamed journal is ignored.  A corrupt renamed journal is a
    // hard stop and never authorizes additional store writes.
    let mut torn = baseline.clone();
    assert_eq!(
        torn.apply_until(
            Action::Finalize(valid.clone()),
            Some(Boundary::PreparedFsync)
        ),
        Err(ModelError::Busy)
    );
    torn.recover().unwrap();
    assert_eq!(torn, baseline);
    let mut bad_journal = baseline.clone();
    assert_eq!(
        bad_journal.apply_until(
            Action::Finalize(valid.clone()),
            Some(Boundary::PreparedRename)
        ),
        Err(ModelError::Busy)
    );
    bad_journal.journal.as_mut().unwrap().checksum_valid = false;
    let before_recovery = bad_journal.stores.clone();
    assert_eq!(bad_journal.recover(), Err(ModelError::CorruptJournal));
    assert_eq!(bad_journal.stores, before_recovery);
    assert_eq!(
        bad_journal.apply_clean(Action::Finalize(valid.clone())),
        Err(ModelError::PendingJournal)
    );

    let shared = Arc::new(Mutex::new(Disk::default()));
    let workers: Vec<_> = (0..2)
        .map(|_| {
            let shared = Arc::clone(&shared);
            let event = valid.clone();
            thread::spawn(move || {
                shared
                    .lock()
                    .unwrap()
                    .apply_clean(Action::Finalize(event))
                    .unwrap()
            })
        })
        .collect();
    let mut outcomes: Vec<_> = workers
        .into_iter()
        .map(|worker| worker.join().unwrap())
        .collect();
    outcomes.sort_by_key(|outcome| match outcome {
        Outcome::Applied => 0,
        Outcome::Noop => 1,
    });
    assert_eq!(outcomes, vec![Outcome::Applied, Outcome::Noop]);
    let shared = shared.lock().unwrap();
    assert_eq!(shared.stores.forest.events.len(), 1);
    assert_eq!(shared.stores.notes.records.len(), 1);
    assert!(shared.stores.is_coherent());
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct V1State {
    note_ids: BTreeSet<u64>,
    spent: BTreeMap<u64, u64>,
    finalized_cursor: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Activation {
    source: V1State,
    candidate: Option<Disk>,
    enabled: bool,
}

impl Activation {
    fn new_default_off(source: V1State) -> Self {
        Self {
            source,
            candidate: None,
            enabled: false,
        }
    }

    fn prepare(&mut self) -> Result<(), ModelError> {
        // V1 does not retain the lane/pair locations or V2 witnesses needed
        // to import notes and spends. Without an authenticated V2 rescan, only
        // the mechanically provable empty/genesis source is activatable.
        if !self.source.note_ids.is_empty()
            || !self.source.spent.is_empty()
            || self.source.finalized_cursor != 0
        {
            return Err(ModelError::IncompleteMigration);
        }
        self.candidate = Some(Disk {
            stores: StoreSet::default(),
            ..Disk::default()
        });
        Ok(())
    }

    fn activate(&mut self) -> Result<(), ModelError> {
        let candidate = self
            .candidate
            .as_ref()
            .ok_or(ModelError::IncompleteMigration)?;
        if !self.source.note_ids.is_empty()
            || !self.source.spent.is_empty()
            || self.source.finalized_cursor != 0
            || candidate.stores != StoreSet::default()
            || !candidate.stores.is_coherent()
        {
            return Err(ModelError::IncompleteMigration);
        }
        self.enabled = true;
        Ok(())
    }

    fn rollback(&mut self) -> Result<V1State, ModelError> {
        if self
            .candidate
            .as_ref()
            .is_some_and(|candidate| !candidate.stores.forest.events.is_empty())
        {
            return Err(ModelError::FinalizedRollback);
        }
        self.enabled = false;
        self.candidate = None;
        Ok(self.source.clone())
    }
}

#[test]
fn v1_migration_is_default_off_verified_before_activation_and_not_rollbackable_after_v2() {
    let nonempty = V1State {
        note_ids: BTreeSet::from([40, 41]),
        spent: BTreeMap::from([(800, 40)]),
        finalized_cursor: 10,
    };
    let mut rejected = Activation::new_default_off(nonempty);
    assert_eq!(rejected.prepare(), Err(ModelError::IncompleteMigration));
    assert!(!rejected.enabled);
    assert!(rejected.candidate.is_none());

    let source = V1State {
        note_ids: BTreeSet::new(),
        spent: BTreeMap::new(),
        finalized_cursor: 0,
    };
    let mut activation = Activation::new_default_off(source.clone());
    assert!(!activation.enabled);
    assert!(activation.candidate.is_none());
    assert_eq!(activation.activate(), Err(ModelError::IncompleteMigration));

    activation.prepare().unwrap();
    activation
        .candidate
        .as_mut()
        .unwrap()
        .stores
        .notes
        .generation = 1;
    assert_eq!(activation.activate(), Err(ModelError::IncompleteMigration));
    activation.prepare().unwrap();
    activation.activate().unwrap();
    assert!(activation.enabled);

    let mut rollbackable = activation.clone();
    assert_eq!(rollbackable.rollback(), Ok(source.clone()));
    assert!(!rollbackable.enabled);
    assert!(rollbackable.candidate.is_none());

    finalized(
        activation.candidate.as_mut().unwrap(),
        event(0, 1, 1, 0, Some(42), None),
    );
    let committed = activation.clone();
    assert_eq!(activation.rollback(), Err(ModelError::FinalizedRollback));
    assert_eq!(activation, committed);
}
