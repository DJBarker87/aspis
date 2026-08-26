//! Crash-safe relayer simulation/signature/submission/finality journal.
//!
//! The durable queue marks a request inflight before this journal is used.
//! This second, append-preserving state machine ensures that a crash after
//! signing cannot cause the operator to build or sign a different transaction:
//! the exact signed wire and signature are persisted before submission. On
//! restart, signed/submitted records are queried or resubmitted byte-for-byte;
//! they are never rebuilt from a fresh blockhash.

use std::path::Path;

use bincode::Options as _;
use sha2::{Digest as _, Sha256};
use solana_program::pubkey::Pubkey;
use solana_transaction::versioned::VersionedTransaction;

use crate::scan_state::FinalizedChainPointV1;
use crate::{
    durable_state::{AtomicStateFileV1, DurableStateErrorV1},
    finalized_indexer::SolanaRpcCommitmentV1,
    relayer_transaction::AuthenticatedAddressLookupTableV1,
};

const RELAYER_EXECUTION_MAGIC_V1: [u8; 4] = *b"ASRJ";
const RELAYER_EXECUTION_VERSION_V1: u8 = 1;
const RELAYER_EXECUTION_HEADER_BYTES_V1: usize = 88;
const RELAYER_EXECUTION_RECORD_BYTES_V1: usize = 576;
const RELAYER_EXECUTION_CHECKSUM_OFFSET_V1: usize = 56;
const MAX_RELAYER_EXECUTION_IMAGE_BYTES_V1: usize = 64 * 1024 * 1024;
const MAX_RELAYER_EXECUTION_RECORDS_V1: usize = 100_000;
/// Supports present 1,232-byte transactions and the proposed 4 KiB class.
const MAX_SIGNED_TRANSACTION_WIRE_BYTES_V1: usize = 4096;
const RELAYER_LOOKUP_TABLE_HEADER_BYTES_V1: usize = 132;
const MAX_RELAYER_LOOKUP_TABLES_V1: usize = 256;
const MAX_RELAYER_LOOKUP_TABLE_DATA_BYTES_V1: usize = 56 + 256 * 32;
const RELAYER_EXECUTION_CHECKSUM_DOMAIN_V1: &[u8] =
    b"aspis:pool-v1:relayer-execution-journal:sha256:v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RelayerSimulationEvidenceV1 {
    pub simulated_at_slot: u64,
    pub recent_blockhash: [u8; 32],
    pub last_valid_block_height: u64,
    pub fee_payer: [u8; 32],
    pub unsigned_message_sha256: [u8; 32],
    /// Digest of the exact successful simulation result/error object.
    pub simulation_result_sha256: [u8; 32],
    pub simulation_accounts_sha256: [u8; 32],
    pub startup_receipt_digest: [u8; 32],
    pub compute_unit_limit: u32,
    /// Exact priority price instruction; zero means the canonical transaction
    /// omits `SetComputeUnitPrice` entirely.
    pub compute_unit_price_micro_lamports: u64,
    pub compute_units_consumed: u64,
    pub estimated_fee_lamports: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelayerSignedWireV1 {
    pub transaction_signature: [u8; 64],
    pub signed_wire: Vec<u8>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RelayerSubmissionEvidenceV1 {
    pub submitted_at_slot: u64,
    pub provider_set_digest: [u8; 32],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RelayerFinalizedEvidenceV1 {
    pub point: FinalizedChainPointV1,
    pub fee_lamports: u64,
    pub compute_units_consumed: u64,
    /// Digest of the exact finalized RPC status/error object. A successful
    /// result still has a nonzero canonical digest.
    pub execution_result_sha256: [u8; 32],
    pub poststate_sha256: [u8; 32],
    pub provider_set_digest: [u8; 32],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RelayerTerminalFailureEvidenceV1 {
    pub observed_block_height: u64,
    pub failure_code: u32,
    pub evidence_sha256: [u8; 32],
    pub provider_set_digest: [u8; 32],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelayerExecutionOutcomeV1 {
    Finalized(RelayerFinalizedEvidenceV1),
    TerminalFailure(RelayerTerminalFailureEvidenceV1),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelayerExecutionRecordV1 {
    pub request_id: [u8; 32],
    pub policy_id: [u8; 32],
    pub simulation: RelayerSimulationEvidenceV1,
    /// Exact finalized ALT images used by the successful simulation. They are
    /// persisted before signing so restart never refetches mutable table state.
    pub simulation_lookup_tables: Vec<AuthenticatedAddressLookupTableV1>,
    pub signed: Option<RelayerSignedWireV1>,
    pub submission: Option<RelayerSubmissionEvidenceV1>,
    pub outcome: Option<RelayerExecutionOutcomeV1>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InspectedSignedTransactionV1 {
    pub transaction_signature: [u8; 64],
    pub fee_payer: [u8; 32],
    pub unsigned_message_sha256: [u8; 32],
}

/// Production implementations parse the exact legacy/v0 Solana transaction,
/// reject trailing bytes and verify its signatures before returning this
/// summary. The journal compares it to the accepted simulation before storing
/// any wire as signable/submittable.
pub trait SignedTransactionInspectorV1 {
    fn inspect_and_verify_signed_transaction_v1(
        &self,
        signed_wire: &[u8],
    ) -> Option<InspectedSignedTransactionV1>;
}

/// Strict production inspector for the currently deployed legacy/v0 Solana
/// transaction wire. It bounds allocation, rejects trailing aliases, applies
/// the SDK's structural sanitizer, and verifies every required Ed25519
/// signature over the exact serialized message before exposing the fee payer.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SolanaSdkSignedTransactionInspectorV1;

impl SignedTransactionInspectorV1 for SolanaSdkSignedTransactionInspectorV1 {
    fn inspect_and_verify_signed_transaction_v1(
        &self,
        signed_wire: &[u8],
    ) -> Option<InspectedSignedTransactionV1> {
        if signed_wire.is_empty() || signed_wire.len() > MAX_SIGNED_TRANSACTION_WIRE_BYTES_V1 {
            return None;
        }
        let transaction: VersionedTransaction = bincode::DefaultOptions::new()
            .with_fixint_encoding()
            .with_limit(MAX_SIGNED_TRANSACTION_WIRE_BYTES_V1 as u64)
            .reject_trailing_bytes()
            .deserialize(signed_wire)
            .ok()?;
        transaction.sanitize().ok()?;
        let unsigned_message = transaction.message.serialize();
        if transaction
            .signatures
            .iter()
            .zip(transaction.message.static_account_keys())
            .any(|(signature, pubkey)| !signature.verify(pubkey.as_ref(), &unsigned_message))
        {
            return None;
        }

        let transaction_signature = *transaction.signatures.first()?.as_array();
        let fee_payer = transaction
            .message
            .static_account_keys()
            .first()?
            .as_ref()
            .try_into()
            .ok()?;
        let unsigned_message_sha256 = Sha256::digest(&unsigned_message).into();
        Some(InspectedSignedTransactionV1 {
            transaction_signature,
            fee_payer,
            unsigned_message_sha256,
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelayerExecutionJournalErrorV1 {
    Durable(DurableStateErrorV1),
    InvalidRecord,
    InvalidTransition,
    DuplicateRequest,
    SignedWireTooLarge,
    SignedTransactionRejected,
    SignedTransactionMismatch,
    SubmissionMismatch,
    OutcomeMismatch,
    WrongLength,
    WrongMagic,
    WrongVersion,
    NonZeroReserved,
    ChecksumMismatch,
    CountOverflow,
    NonCanonicalOrder,
}

impl From<DurableStateErrorV1> for RelayerExecutionJournalErrorV1 {
    fn from(error: DurableStateErrorV1) -> Self {
        Self::Durable(error)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelayerExecutionJournalUpdateV1 {
    Inserted,
    AlreadyPresent,
}

pub struct DurableRelayerExecutionJournalV1 {
    file: AtomicStateFileV1,
    records: Vec<RelayerExecutionRecordV1>,
}

impl DurableRelayerExecutionJournalV1 {
    pub fn open_or_create_v1(
        path: impl AsRef<Path>,
    ) -> Result<Self, RelayerExecutionJournalErrorV1> {
        let file = AtomicStateFileV1::acquire(path.as_ref())?;
        let records = match file.read_optional()? {
            Some(bytes) => decode_execution_journal_v1(&bytes)?,
            None => {
                let bytes = encode_execution_journal_v1(&[])?;
                file.replace(&bytes)?;
                Vec::new()
            }
        };
        Ok(Self { file, records })
    }

    pub fn records(&self) -> &[RelayerExecutionRecordV1] {
        &self.records
    }

    pub fn record_v1(&self, request_id: [u8; 32]) -> Option<&RelayerExecutionRecordV1> {
        self.records
            .iter()
            .find(|record| record.request_id == request_id)
    }

    /// Persist successful exact-wire simulation before requesting a signature.
    pub fn record_simulation_v1(
        &mut self,
        request_id: [u8; 32],
        policy_id: [u8; 32],
        simulation: RelayerSimulationEvidenceV1,
        lookup_tables: &[AuthenticatedAddressLookupTableV1],
    ) -> Result<RelayerExecutionJournalUpdateV1, RelayerExecutionJournalErrorV1> {
        validate_simulation_v1(request_id, policy_id, simulation)?;
        validate_lookup_tables_v1(simulation, lookup_tables)?;
        if let Some(existing) = self.record_v1(request_id) {
            return if existing.policy_id == policy_id
                && existing.simulation == simulation
                && existing.simulation_lookup_tables == lookup_tables
            {
                Ok(RelayerExecutionJournalUpdateV1::AlreadyPresent)
            } else {
                Err(RelayerExecutionJournalErrorV1::DuplicateRequest)
            };
        }
        if self.records.len() >= MAX_RELAYER_EXECUTION_RECORDS_V1 {
            return Err(RelayerExecutionJournalErrorV1::CountOverflow);
        }
        let mut records = self.records.clone();
        records.push(RelayerExecutionRecordV1 {
            request_id,
            policy_id,
            simulation,
            simulation_lookup_tables: lookup_tables.to_vec(),
            signed: None,
            submission: None,
            outcome: None,
        });
        self.persist_v1(records)?;
        Ok(RelayerExecutionJournalUpdateV1::Inserted)
    }

    /// Inspect, verify and durably retain the exact signed transaction before
    /// any network submission. A different signature/wire under the same
    /// request is a terminal local inconsistency, never an overwrite.
    pub fn record_signed_wire_v1(
        &mut self,
        request_id: [u8; 32],
        signed_wire: &[u8],
        inspector: &impl SignedTransactionInspectorV1,
    ) -> Result<RelayerExecutionJournalUpdateV1, RelayerExecutionJournalErrorV1> {
        if signed_wire.is_empty() || signed_wire.len() > MAX_SIGNED_TRANSACTION_WIRE_BYTES_V1 {
            return Err(RelayerExecutionJournalErrorV1::SignedWireTooLarge);
        }
        let inspected = inspector
            .inspect_and_verify_signed_transaction_v1(signed_wire)
            .ok_or(RelayerExecutionJournalErrorV1::SignedTransactionRejected)?;
        if inspected.transaction_signature == [0u8; 64] {
            return Err(RelayerExecutionJournalErrorV1::SignedTransactionRejected);
        }
        let mut records = self.records.clone();
        let record = records
            .iter_mut()
            .find(|record| record.request_id == request_id)
            .ok_or(RelayerExecutionJournalErrorV1::InvalidTransition)?;
        if inspected.fee_payer != record.simulation.fee_payer
            || inspected.unsigned_message_sha256 != record.simulation.unsigned_message_sha256
        {
            return Err(RelayerExecutionJournalErrorV1::SignedTransactionMismatch);
        }
        let signed = RelayerSignedWireV1 {
            transaction_signature: inspected.transaction_signature,
            signed_wire: signed_wire.to_vec(),
        };
        if let Some(existing) = &record.signed {
            return if *existing == signed {
                Ok(RelayerExecutionJournalUpdateV1::AlreadyPresent)
            } else {
                Err(RelayerExecutionJournalErrorV1::SignedTransactionMismatch)
            };
        }
        if record.outcome.is_some() {
            return Err(RelayerExecutionJournalErrorV1::SignedTransactionMismatch);
        }
        record.signed = Some(signed);
        self.persist_v1(records)?;
        Ok(RelayerExecutionJournalUpdateV1::Inserted)
    }

    pub fn record_submission_v1(
        &mut self,
        request_id: [u8; 32],
        transaction_signature: [u8; 64],
        submission: RelayerSubmissionEvidenceV1,
    ) -> Result<RelayerExecutionJournalUpdateV1, RelayerExecutionJournalErrorV1> {
        if submission.provider_set_digest == [0u8; 32] {
            return Err(RelayerExecutionJournalErrorV1::InvalidRecord);
        }
        let mut records = self.records.clone();
        let record = records
            .iter_mut()
            .find(|record| record.request_id == request_id)
            .ok_or(RelayerExecutionJournalErrorV1::InvalidTransition)?;
        let signed = record
            .signed
            .as_ref()
            .ok_or(RelayerExecutionJournalErrorV1::InvalidTransition)?;
        if signed.transaction_signature != transaction_signature
            || submission.submitted_at_slot < record.simulation.simulated_at_slot
        {
            return Err(RelayerExecutionJournalErrorV1::SubmissionMismatch);
        }
        if let Some(existing) = record.submission {
            return if existing == submission {
                Ok(RelayerExecutionJournalUpdateV1::AlreadyPresent)
            } else {
                Err(RelayerExecutionJournalErrorV1::SubmissionMismatch)
            };
        }
        if record.outcome.is_some() {
            return Err(RelayerExecutionJournalErrorV1::SubmissionMismatch);
        }
        record.submission = Some(submission);
        self.persist_v1(records)?;
        Ok(RelayerExecutionJournalUpdateV1::Inserted)
    }

    /// Record a finalized status. This may follow `Signed` directly: the
    /// transaction can land between network send and durable submission log.
    pub fn record_finalized_v1(
        &mut self,
        request_id: [u8; 32],
        transaction_signature: [u8; 64],
        finalized: RelayerFinalizedEvidenceV1,
    ) -> Result<RelayerExecutionJournalUpdateV1, RelayerExecutionJournalErrorV1> {
        if finalized.execution_result_sha256 == [0u8; 32]
            || finalized.poststate_sha256 == [0u8; 32]
            || finalized.provider_set_digest == [0u8; 32]
        {
            return Err(RelayerExecutionJournalErrorV1::InvalidRecord);
        }
        let mut records = self.records.clone();
        let record = records
            .iter_mut()
            .find(|record| record.request_id == request_id)
            .ok_or(RelayerExecutionJournalErrorV1::InvalidTransition)?;
        let signed = record
            .signed
            .as_ref()
            .ok_or(RelayerExecutionJournalErrorV1::InvalidTransition)?;
        if signed.transaction_signature != transaction_signature
            || finalized.point.slot() < record.simulation.simulated_at_slot
        {
            return Err(RelayerExecutionJournalErrorV1::OutcomeMismatch);
        }
        let outcome = RelayerExecutionOutcomeV1::Finalized(finalized);
        if let Some(existing) = record.outcome {
            return if existing == outcome {
                Ok(RelayerExecutionJournalUpdateV1::AlreadyPresent)
            } else {
                Err(RelayerExecutionJournalErrorV1::OutcomeMismatch)
            };
        }
        record.outcome = Some(outcome);
        self.persist_v1(records)?;
        Ok(RelayerExecutionJournalUpdateV1::Inserted)
    }

    /// A signed transaction becomes terminally failed only after its blockhash
    /// validity window has passed under an authenticated multi-provider view.
    pub fn record_terminal_failure_v1(
        &mut self,
        request_id: [u8; 32],
        terminal: RelayerTerminalFailureEvidenceV1,
    ) -> Result<RelayerExecutionJournalUpdateV1, RelayerExecutionJournalErrorV1> {
        if terminal.failure_code == 0
            || terminal.evidence_sha256 == [0u8; 32]
            || terminal.provider_set_digest == [0u8; 32]
        {
            return Err(RelayerExecutionJournalErrorV1::InvalidRecord);
        }
        let mut records = self.records.clone();
        let record = records
            .iter_mut()
            .find(|record| record.request_id == request_id)
            .ok_or(RelayerExecutionJournalErrorV1::InvalidTransition)?;
        if record.signed.is_some()
            && terminal.observed_block_height <= record.simulation.last_valid_block_height
        {
            return Err(RelayerExecutionJournalErrorV1::OutcomeMismatch);
        }
        let outcome = RelayerExecutionOutcomeV1::TerminalFailure(terminal);
        if let Some(existing) = record.outcome {
            return if existing == outcome {
                Ok(RelayerExecutionJournalUpdateV1::AlreadyPresent)
            } else {
                Err(RelayerExecutionJournalErrorV1::OutcomeMismatch)
            };
        }
        record.outcome = Some(outcome);
        self.persist_v1(records)?;
        Ok(RelayerExecutionJournalUpdateV1::Inserted)
    }

    fn persist_v1(
        &mut self,
        records: Vec<RelayerExecutionRecordV1>,
    ) -> Result<(), RelayerExecutionJournalErrorV1> {
        let bytes = encode_execution_journal_v1(&records)?;
        self.file.replace(&bytes)?;
        self.records = records;
        Ok(())
    }
}

fn validate_simulation_v1(
    request_id: [u8; 32],
    policy_id: [u8; 32],
    simulation: RelayerSimulationEvidenceV1,
) -> Result<(), RelayerExecutionJournalErrorV1> {
    let minimum_priority_fee = u128::from(simulation.compute_unit_limit)
        .saturating_mul(u128::from(simulation.compute_unit_price_micro_lamports))
        .div_ceil(1_000_000);
    if request_id == [0u8; 32]
        || policy_id == [0u8; 32]
        || simulation.simulated_at_slot == 0
        || simulation.recent_blockhash == [0u8; 32]
        || simulation.last_valid_block_height == 0
        || simulation.fee_payer == [0u8; 32]
        || simulation.unsigned_message_sha256 == [0u8; 32]
        || simulation.simulation_result_sha256 == [0u8; 32]
        || simulation.simulation_accounts_sha256 == [0u8; 32]
        || simulation.startup_receipt_digest == [0u8; 32]
        || simulation.compute_unit_limit == 0
        || simulation.compute_units_consumed > u64::from(simulation.compute_unit_limit)
        || simulation.estimated_fee_lamports == 0
        || minimum_priority_fee > u128::from(simulation.estimated_fee_lamports)
    {
        return Err(RelayerExecutionJournalErrorV1::InvalidRecord);
    }
    Ok(())
}

fn validate_lookup_tables_v1(
    simulation: RelayerSimulationEvidenceV1,
    lookup_tables: &[AuthenticatedAddressLookupTableV1],
) -> Result<(), RelayerExecutionJournalErrorV1> {
    if lookup_tables.len() > MAX_RELAYER_LOOKUP_TABLES_V1 {
        return Err(RelayerExecutionJournalErrorV1::CountOverflow);
    }
    let mut previous = None;
    for table in lookup_tables {
        if previous.is_some_and(|address| address >= table.address())
            || table.observed_slot() != simulation.simulated_at_slot
            || table.owner() != solana_sdk_ids::address_lookup_table::id()
            || table.lamports() == 0
            || table.executable()
            || table.commitment() != SolanaRpcCommitmentV1::Finalized
            || table.provider_set_digest() == &[0u8; 32]
            || !(56..=MAX_RELAYER_LOOKUP_TABLE_DATA_BYTES_V1).contains(&table.account_data().len())
        {
            return Err(RelayerExecutionJournalErrorV1::InvalidRecord);
        }
        previous = Some(table.address());
    }
    Ok(())
}

fn encode_execution_journal_v1(
    records: &[RelayerExecutionRecordV1],
) -> Result<Vec<u8>, RelayerExecutionJournalErrorV1> {
    if records.len() > MAX_RELAYER_EXECUTION_RECORDS_V1 {
        return Err(RelayerExecutionJournalErrorV1::CountOverflow);
    }
    let mut ordered: Vec<_> = records.iter().collect();
    ordered.sort_by_key(|record| record.request_id);
    if ordered
        .windows(2)
        .any(|pair| pair[0].request_id == pair[1].request_id)
    {
        return Err(RelayerExecutionJournalErrorV1::DuplicateRequest);
    }
    let payloads = ordered.iter().try_fold(0usize, |total, record| {
        validate_record_v1(record)?;
        let lookup_length = encoded_lookup_tables_length_v1(&record.simulation_lookup_tables)?;
        let wire_length = record
            .signed
            .as_ref()
            .map_or(0, |signed| signed.signed_wire.len());
        total
            .checked_add(lookup_length)
            .and_then(|length| length.checked_add(wire_length))
            .ok_or(RelayerExecutionJournalErrorV1::CountOverflow)
    })?;
    let length = RELAYER_EXECUTION_HEADER_BYTES_V1
        .checked_add(
            records
                .len()
                .checked_mul(RELAYER_EXECUTION_RECORD_BYTES_V1)
                .ok_or(RelayerExecutionJournalErrorV1::CountOverflow)?,
        )
        .and_then(|value| value.checked_add(payloads))
        .ok_or(RelayerExecutionJournalErrorV1::CountOverflow)?;
    if length > MAX_RELAYER_EXECUTION_IMAGE_BYTES_V1 {
        return Err(RelayerExecutionJournalErrorV1::CountOverflow);
    }
    let mut bytes = vec![0u8; length];
    bytes[..4].copy_from_slice(&RELAYER_EXECUTION_MAGIC_V1);
    bytes[4] = RELAYER_EXECUTION_VERSION_V1;
    bytes[8..12].copy_from_slice(
        &u32::try_from(records.len())
            .map_err(|_| RelayerExecutionJournalErrorV1::CountOverflow)?
            .to_le_bytes(),
    );
    let mut offset = RELAYER_EXECUTION_HEADER_BYTES_V1;
    for record in ordered {
        let header = &mut bytes[offset..offset + RELAYER_EXECUTION_RECORD_BYTES_V1];
        encode_record_header_v1(record, header)?;
        offset += RELAYER_EXECUTION_RECORD_BYTES_V1;
        let lookup_bytes = encode_lookup_tables_v1(&record.simulation_lookup_tables)?;
        bytes[offset..offset + lookup_bytes.len()].copy_from_slice(&lookup_bytes);
        offset += lookup_bytes.len();
        if let Some(signed) = &record.signed {
            bytes[offset..offset + signed.signed_wire.len()].copy_from_slice(&signed.signed_wire);
            offset += signed.signed_wire.len();
        }
    }
    let checksum = execution_journal_checksum_v1(&bytes)?;
    bytes[RELAYER_EXECUTION_CHECKSUM_OFFSET_V1..RELAYER_EXECUTION_CHECKSUM_OFFSET_V1 + 32]
        .copy_from_slice(&checksum);
    Ok(bytes)
}

fn validate_record_v1(
    record: &RelayerExecutionRecordV1,
) -> Result<(), RelayerExecutionJournalErrorV1> {
    validate_simulation_v1(record.request_id, record.policy_id, record.simulation)?;
    validate_lookup_tables_v1(record.simulation, &record.simulation_lookup_tables)?;
    if record.submission.is_some() && record.signed.is_none()
        || record.signed.as_ref().is_some_and(|signed| {
            signed.transaction_signature == [0u8; 64]
                || signed.signed_wire.is_empty()
                || signed.signed_wire.len() > MAX_SIGNED_TRANSACTION_WIRE_BYTES_V1
        })
        || record.submission.is_some_and(|submission| {
            submission.provider_set_digest == [0u8; 32]
                || submission.submitted_at_slot < record.simulation.simulated_at_slot
        })
    {
        return Err(RelayerExecutionJournalErrorV1::InvalidRecord);
    }
    match record.outcome {
        Some(RelayerExecutionOutcomeV1::Finalized(finalized)) => {
            if record.signed.is_none()
                || finalized.execution_result_sha256 == [0u8; 32]
                || finalized.poststate_sha256 == [0u8; 32]
                || finalized.provider_set_digest == [0u8; 32]
                || finalized.point.slot() < record.simulation.simulated_at_slot
            {
                return Err(RelayerExecutionJournalErrorV1::InvalidRecord);
            }
        }
        Some(RelayerExecutionOutcomeV1::TerminalFailure(terminal)) => {
            if terminal.failure_code == 0
                || terminal.evidence_sha256 == [0u8; 32]
                || terminal.provider_set_digest == [0u8; 32]
                || record.signed.is_some()
                    && terminal.observed_block_height <= record.simulation.last_valid_block_height
            {
                return Err(RelayerExecutionJournalErrorV1::InvalidRecord);
            }
        }
        None => {}
    }
    Ok(())
}

fn encode_record_header_v1(
    record: &RelayerExecutionRecordV1,
    header: &mut [u8],
) -> Result<(), RelayerExecutionJournalErrorV1> {
    header[..32].copy_from_slice(&record.request_id);
    header[32..64].copy_from_slice(&record.policy_id);
    header[64..72].copy_from_slice(&record.simulation.simulated_at_slot.to_le_bytes());
    header[72..104].copy_from_slice(&record.simulation.recent_blockhash);
    header[104..112].copy_from_slice(&record.simulation.last_valid_block_height.to_le_bytes());
    header[112..144].copy_from_slice(&record.simulation.fee_payer);
    header[144..176].copy_from_slice(&record.simulation.unsigned_message_sha256);
    header[176..208].copy_from_slice(&record.simulation.simulation_result_sha256);
    header[208..240].copy_from_slice(&record.simulation.simulation_accounts_sha256);
    header[240..272].copy_from_slice(&record.simulation.startup_receipt_digest);
    header[272..276].copy_from_slice(&record.simulation.compute_unit_limit.to_le_bytes());
    header[556..564].copy_from_slice(
        &record
            .simulation
            .compute_unit_price_micro_lamports
            .to_le_bytes(),
    );
    header[276..284].copy_from_slice(&record.simulation.compute_units_consumed.to_le_bytes());
    header[284..292].copy_from_slice(&record.simulation.estimated_fee_lamports.to_le_bytes());
    header[564..566].copy_from_slice(
        &u16::try_from(record.simulation_lookup_tables.len())
            .map_err(|_| RelayerExecutionJournalErrorV1::CountOverflow)?
            .to_le_bytes(),
    );
    header[568..572].copy_from_slice(
        &u32::try_from(encoded_lookup_tables_length_v1(
            &record.simulation_lookup_tables,
        )?)
        .map_err(|_| RelayerExecutionJournalErrorV1::CountOverflow)?
        .to_le_bytes(),
    );
    if let Some(signed) = &record.signed {
        header[292] = 1;
        header[296..360].copy_from_slice(&signed.transaction_signature);
        header[360..364].copy_from_slice(
            &u32::try_from(signed.signed_wire.len())
                .map_err(|_| RelayerExecutionJournalErrorV1::CountOverflow)?
                .to_le_bytes(),
        );
    }
    if let Some(submission) = record.submission {
        header[293] = 1;
        header[364..372].copy_from_slice(&submission.submitted_at_slot.to_le_bytes());
        header[372..404].copy_from_slice(&submission.provider_set_digest);
    }
    match record.outcome {
        Some(RelayerExecutionOutcomeV1::Finalized(finalized)) => {
            header[294] = 1;
            encode_chain_point_v1(finalized.point, &mut header[404..444]);
            header[444..452].copy_from_slice(&finalized.fee_lamports.to_le_bytes());
            header[452..460].copy_from_slice(&finalized.compute_units_consumed.to_le_bytes());
            header[460..492].copy_from_slice(&finalized.execution_result_sha256);
            header[492..524].copy_from_slice(&finalized.poststate_sha256);
            header[524..556].copy_from_slice(&finalized.provider_set_digest);
        }
        Some(RelayerExecutionOutcomeV1::TerminalFailure(terminal)) => {
            header[294] = 2;
            header[404..412].copy_from_slice(&terminal.observed_block_height.to_le_bytes());
            header[412..416].copy_from_slice(&terminal.failure_code.to_le_bytes());
            header[416..448].copy_from_slice(&terminal.evidence_sha256);
            header[448..480].copy_from_slice(&terminal.provider_set_digest);
        }
        None => {}
    }
    Ok(())
}

fn encoded_lookup_tables_length_v1(
    lookup_tables: &[AuthenticatedAddressLookupTableV1],
) -> Result<usize, RelayerExecutionJournalErrorV1> {
    if lookup_tables.len() > MAX_RELAYER_LOOKUP_TABLES_V1 {
        return Err(RelayerExecutionJournalErrorV1::CountOverflow);
    }
    lookup_tables.iter().try_fold(0usize, |total, table| {
        total
            .checked_add(RELAYER_LOOKUP_TABLE_HEADER_BYTES_V1)
            .and_then(|length| length.checked_add(table.account_data().len()))
            .ok_or(RelayerExecutionJournalErrorV1::CountOverflow)
    })
}

fn encode_lookup_tables_v1(
    lookup_tables: &[AuthenticatedAddressLookupTableV1],
) -> Result<Vec<u8>, RelayerExecutionJournalErrorV1> {
    let length = encoded_lookup_tables_length_v1(lookup_tables)?;
    let mut bytes = Vec::with_capacity(length);
    for table in lookup_tables {
        let data_length = u32::try_from(table.account_data().len())
            .map_err(|_| RelayerExecutionJournalErrorV1::CountOverflow)?;
        bytes.extend_from_slice(table.address().as_ref());
        bytes.extend_from_slice(table.owner().as_ref());
        bytes.extend_from_slice(&table.observed_slot().to_le_bytes());
        bytes.extend_from_slice(&table.lamports().to_le_bytes());
        bytes.push(u8::from(table.executable()));
        bytes.push(match table.commitment() {
            SolanaRpcCommitmentV1::Processed => 0,
            SolanaRpcCommitmentV1::Confirmed => 1,
            SolanaRpcCommitmentV1::Finalized => 2,
        });
        bytes.extend_from_slice(&[0u8; 6]);
        bytes.extend_from_slice(&table.rent_epoch().to_le_bytes());
        bytes.extend_from_slice(table.provider_set_digest());
        bytes.extend_from_slice(&data_length.to_le_bytes());
        bytes.extend_from_slice(table.account_data());
    }
    Ok(bytes)
}

fn decode_lookup_tables_v1(
    bytes: &[u8],
    count: usize,
) -> Result<Vec<AuthenticatedAddressLookupTableV1>, RelayerExecutionJournalErrorV1> {
    if count > MAX_RELAYER_LOOKUP_TABLES_V1 {
        return Err(RelayerExecutionJournalErrorV1::CountOverflow);
    }
    let mut tables = Vec::with_capacity(count);
    let mut offset = 0usize;
    for _ in 0..count {
        let header_end = offset
            .checked_add(RELAYER_LOOKUP_TABLE_HEADER_BYTES_V1)
            .ok_or(RelayerExecutionJournalErrorV1::CountOverflow)?;
        let header = bytes
            .get(offset..header_end)
            .ok_or(RelayerExecutionJournalErrorV1::WrongLength)?;
        if header[82..88].iter().any(|byte| *byte != 0) || header[81] != 2 {
            return Err(RelayerExecutionJournalErrorV1::InvalidRecord);
        }
        let data_length = u32::from_le_bytes(header[128..132].try_into().unwrap()) as usize;
        if !(56..=MAX_RELAYER_LOOKUP_TABLE_DATA_BYTES_V1).contains(&data_length) {
            return Err(RelayerExecutionJournalErrorV1::InvalidRecord);
        }
        let data_end = header_end
            .checked_add(data_length)
            .ok_or(RelayerExecutionJournalErrorV1::CountOverflow)?;
        let account_data = bytes
            .get(header_end..data_end)
            .ok_or(RelayerExecutionJournalErrorV1::WrongLength)?
            .to_vec();
        let table = AuthenticatedAddressLookupTableV1::new(
            Pubkey::new_from_array(header[..32].try_into().unwrap()),
            Pubkey::new_from_array(header[32..64].try_into().unwrap()),
            u64::from_le_bytes(header[64..72].try_into().unwrap()),
            u64::from_le_bytes(header[72..80].try_into().unwrap()),
            match header[80] {
                0 => false,
                1 => true,
                _ => return Err(RelayerExecutionJournalErrorV1::InvalidRecord),
            },
            u64::from_le_bytes(header[88..96].try_into().unwrap()),
            SolanaRpcCommitmentV1::Finalized,
            header[96..128].try_into().unwrap(),
            account_data,
        )
        .map_err(|_| RelayerExecutionJournalErrorV1::InvalidRecord)?;
        tables.push(table);
        offset = data_end;
    }
    if offset != bytes.len() {
        return Err(RelayerExecutionJournalErrorV1::WrongLength);
    }
    Ok(tables)
}

fn decode_execution_journal_v1(
    bytes: &[u8],
) -> Result<Vec<RelayerExecutionRecordV1>, RelayerExecutionJournalErrorV1> {
    if bytes.len() < RELAYER_EXECUTION_HEADER_BYTES_V1
        || bytes.len() > MAX_RELAYER_EXECUTION_IMAGE_BYTES_V1
    {
        return Err(RelayerExecutionJournalErrorV1::WrongLength);
    }
    if bytes[..4] != RELAYER_EXECUTION_MAGIC_V1 {
        return Err(RelayerExecutionJournalErrorV1::WrongMagic);
    }
    if bytes[4] != RELAYER_EXECUTION_VERSION_V1 {
        return Err(RelayerExecutionJournalErrorV1::WrongVersion);
    }
    if bytes[5..8].iter().any(|byte| *byte != 0) || bytes[12..56].iter().any(|byte| *byte != 0) {
        return Err(RelayerExecutionJournalErrorV1::NonZeroReserved);
    }
    let encoded_checksum: [u8; 32] = bytes[56..88].try_into().unwrap();
    if encoded_checksum != execution_journal_checksum_v1(bytes)? {
        return Err(RelayerExecutionJournalErrorV1::ChecksumMismatch);
    }
    let count = u32::from_le_bytes(bytes[8..12].try_into().unwrap()) as usize;
    if count > MAX_RELAYER_EXECUTION_RECORDS_V1 {
        return Err(RelayerExecutionJournalErrorV1::CountOverflow);
    }
    let mut records = Vec::with_capacity(count);
    let mut offset = RELAYER_EXECUTION_HEADER_BYTES_V1;
    let mut previous_id = None;
    for _ in 0..count {
        let header_end = offset
            .checked_add(RELAYER_EXECUTION_RECORD_BYTES_V1)
            .ok_or(RelayerExecutionJournalErrorV1::CountOverflow)?;
        let header = bytes
            .get(offset..header_end)
            .ok_or(RelayerExecutionJournalErrorV1::WrongLength)?;
        let request_id: [u8; 32] = header[..32].try_into().unwrap();
        if previous_id.is_some_and(|previous| previous >= request_id) {
            return Err(RelayerExecutionJournalErrorV1::NonCanonicalOrder);
        }
        previous_id = Some(request_id);
        let signed_flag = decode_flag_v1(header[292])?;
        let submitted_flag = decode_flag_v1(header[293])?;
        let outcome_kind = header[294];
        if outcome_kind > 2
            || header[295] != 0
            || header[566..568].iter().any(|byte| *byte != 0)
            || header[572..].iter().any(|byte| *byte != 0)
        {
            return Err(RelayerExecutionJournalErrorV1::NonZeroReserved);
        }
        let wire_length = u32::from_le_bytes(header[360..364].try_into().unwrap()) as usize;
        let lookup_table_count = u16::from_le_bytes(header[564..566].try_into().unwrap()) as usize;
        let lookup_bytes_length = u32::from_le_bytes(header[568..572].try_into().unwrap()) as usize;
        if lookup_table_count > MAX_RELAYER_LOOKUP_TABLES_V1 {
            return Err(RelayerExecutionJournalErrorV1::CountOverflow);
        }
        if signed_flag != (wire_length != 0) || wire_length > MAX_SIGNED_TRANSACTION_WIRE_BYTES_V1 {
            return Err(RelayerExecutionJournalErrorV1::InvalidRecord);
        }
        let lookup_end = header_end
            .checked_add(lookup_bytes_length)
            .ok_or(RelayerExecutionJournalErrorV1::CountOverflow)?;
        let lookup_bytes = bytes
            .get(header_end..lookup_end)
            .ok_or(RelayerExecutionJournalErrorV1::WrongLength)?;
        let simulation_lookup_tables = decode_lookup_tables_v1(lookup_bytes, lookup_table_count)?;
        let wire_end = lookup_end
            .checked_add(wire_length)
            .ok_or(RelayerExecutionJournalErrorV1::CountOverflow)?;
        let signed_wire = bytes
            .get(lookup_end..wire_end)
            .ok_or(RelayerExecutionJournalErrorV1::WrongLength)?;
        let simulation = RelayerSimulationEvidenceV1 {
            simulated_at_slot: u64::from_le_bytes(header[64..72].try_into().unwrap()),
            recent_blockhash: header[72..104].try_into().unwrap(),
            last_valid_block_height: u64::from_le_bytes(header[104..112].try_into().unwrap()),
            fee_payer: header[112..144].try_into().unwrap(),
            unsigned_message_sha256: header[144..176].try_into().unwrap(),
            simulation_result_sha256: header[176..208].try_into().unwrap(),
            simulation_accounts_sha256: header[208..240].try_into().unwrap(),
            startup_receipt_digest: header[240..272].try_into().unwrap(),
            compute_unit_limit: u32::from_le_bytes(header[272..276].try_into().unwrap()),
            compute_unit_price_micro_lamports: u64::from_le_bytes(
                header[556..564].try_into().unwrap(),
            ),
            compute_units_consumed: u64::from_le_bytes(header[276..284].try_into().unwrap()),
            estimated_fee_lamports: u64::from_le_bytes(header[284..292].try_into().unwrap()),
        };
        let signed = signed_flag.then(|| RelayerSignedWireV1 {
            transaction_signature: header[296..360].try_into().unwrap(),
            signed_wire: signed_wire.to_vec(),
        });
        if !signed_flag && header[296..364].iter().any(|byte| *byte != 0)
            || !submitted_flag && header[364..404].iter().any(|byte| *byte != 0)
        {
            return Err(RelayerExecutionJournalErrorV1::NonZeroReserved);
        }
        let submission = submitted_flag.then(|| RelayerSubmissionEvidenceV1 {
            submitted_at_slot: u64::from_le_bytes(header[364..372].try_into().unwrap()),
            provider_set_digest: header[372..404].try_into().unwrap(),
        });
        let outcome = match outcome_kind {
            0 => {
                if header[404..556].iter().any(|byte| *byte != 0) {
                    return Err(RelayerExecutionJournalErrorV1::NonZeroReserved);
                }
                None
            }
            1 => Some(RelayerExecutionOutcomeV1::Finalized(
                RelayerFinalizedEvidenceV1 {
                    point: decode_chain_point_v1(&header[404..444])?,
                    fee_lamports: u64::from_le_bytes(header[444..452].try_into().unwrap()),
                    compute_units_consumed: u64::from_le_bytes(
                        header[452..460].try_into().unwrap(),
                    ),
                    execution_result_sha256: header[460..492].try_into().unwrap(),
                    poststate_sha256: header[492..524].try_into().unwrap(),
                    provider_set_digest: header[524..556].try_into().unwrap(),
                },
            )),
            2 => {
                if header[480..556].iter().any(|byte| *byte != 0) {
                    return Err(RelayerExecutionJournalErrorV1::NonZeroReserved);
                }
                Some(RelayerExecutionOutcomeV1::TerminalFailure(
                    RelayerTerminalFailureEvidenceV1 {
                        observed_block_height: u64::from_le_bytes(
                            header[404..412].try_into().unwrap(),
                        ),
                        failure_code: u32::from_le_bytes(header[412..416].try_into().unwrap()),
                        evidence_sha256: header[416..448].try_into().unwrap(),
                        provider_set_digest: header[448..480].try_into().unwrap(),
                    },
                ))
            }
            _ => unreachable!(),
        };
        let record = RelayerExecutionRecordV1 {
            request_id,
            policy_id: header[32..64].try_into().unwrap(),
            simulation,
            simulation_lookup_tables,
            signed,
            submission,
            outcome,
        };
        validate_record_v1(&record)?;
        records.push(record);
        offset = wire_end;
    }
    if offset != bytes.len() {
        return Err(RelayerExecutionJournalErrorV1::WrongLength);
    }
    Ok(records)
}

fn decode_flag_v1(byte: u8) -> Result<bool, RelayerExecutionJournalErrorV1> {
    match byte {
        0 => Ok(false),
        1 => Ok(true),
        _ => Err(RelayerExecutionJournalErrorV1::InvalidRecord),
    }
}

fn execution_journal_checksum_v1(bytes: &[u8]) -> Result<[u8; 32], RelayerExecutionJournalErrorV1> {
    if bytes.len() < RELAYER_EXECUTION_HEADER_BYTES_V1 {
        return Err(RelayerExecutionJournalErrorV1::WrongLength);
    }
    let length =
        u64::try_from(bytes.len()).map_err(|_| RelayerExecutionJournalErrorV1::CountOverflow)?;
    let mut hasher = Sha256::new();
    hasher.update(RELAYER_EXECUTION_CHECKSUM_DOMAIN_V1);
    hasher.update(length.to_le_bytes());
    hasher.update(&bytes[..RELAYER_EXECUTION_CHECKSUM_OFFSET_V1]);
    hasher.update([0u8; 32]);
    hasher.update(&bytes[RELAYER_EXECUTION_CHECKSUM_OFFSET_V1 + 32..]);
    Ok(hasher.finalize().into())
}

fn encode_chain_point_v1(point: FinalizedChainPointV1, bytes: &mut [u8]) {
    bytes[..8].copy_from_slice(&point.slot().to_le_bytes());
    bytes[8..40].copy_from_slice(point.block_hash());
}

fn decode_chain_point_v1(
    bytes: &[u8],
) -> Result<FinalizedChainPointV1, RelayerExecutionJournalErrorV1> {
    FinalizedChainPointV1::new(
        u64::from_le_bytes(bytes[..8].try_into().unwrap()),
        bytes[8..40].try_into().unwrap(),
    )
    .map_err(|_| RelayerExecutionJournalErrorV1::InvalidRecord)
}

#[cfg(test)]
mod tests {
    use std::{
        fs,
        sync::atomic::{AtomicU64, Ordering},
    };

    use super::*;

    static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

    struct TestDirectory(std::path::PathBuf);

    impl TestDirectory {
        fn new() -> Self {
            let serial = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "aspis-relayer-execution-{}-{}",
                std::process::id(),
                serial
            ));
            fs::create_dir(&path).unwrap();
            Self(path)
        }
    }

    impl Drop for TestDirectory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    struct Inspector;

    impl SignedTransactionInspectorV1 for Inspector {
        fn inspect_and_verify_signed_transaction_v1(
            &self,
            signed_wire: &[u8],
        ) -> Option<InspectedSignedTransactionV1> {
            (signed_wire == [1, 2, 3, 4]).then_some(InspectedSignedTransactionV1 {
                transaction_signature: [0x51; 64],
                fee_payer: [0x31; 32],
                unsigned_message_sha256: [0x41; 32],
            })
        }
    }

    fn simulation() -> RelayerSimulationEvidenceV1 {
        RelayerSimulationEvidenceV1 {
            simulated_at_slot: 100,
            recent_blockhash: [0x21; 32],
            last_valid_block_height: 500,
            fee_payer: [0x31; 32],
            unsigned_message_sha256: [0x41; 32],
            simulation_result_sha256: [0x44; 32],
            simulation_accounts_sha256: [0x42; 32],
            startup_receipt_digest: [0x43; 32],
            compute_unit_limit: 1_400_000,
            compute_unit_price_micro_lamports: 1,
            compute_units_consumed: 1_200_000,
            estimated_fee_lamports: 10_000,
        }
    }

    fn signed_wire(v0: bool) -> (Vec<u8>, [u8; 32], [u8; 32], [u8; 64]) {
        let fee_payer = [
            49, 222, 190, 85, 211, 124, 114, 39, 104, 177, 55, 19, 28, 170, 96, 135, 8, 11, 46, 11,
            96, 185, 75, 215, 133, 209, 69, 117, 207, 164, 152, 188,
        ];

        // One signer/writable fee payer, one readonly unsigned program, and
        // one empty instruction. All vector lengths are canonical short-vecs.
        let mut message = Vec::new();
        if v0 {
            message.push(0x80);
        }
        message.extend_from_slice(&[1, 0, 1]);
        message.push(2);
        message.extend_from_slice(&fee_payer);
        message.extend_from_slice(&[0x29; 32]);
        message.extend_from_slice(&[0x39; 32]);
        message.push(1);
        message.extend_from_slice(&[1, 1, 0, 0]);
        if v0 {
            message.push(0);
        }

        let signature = if v0 {
            [
                59, 70, 255, 237, 28, 139, 151, 182, 204, 237, 46, 64, 133, 164, 252, 29, 51, 114,
                17, 85, 57, 113, 135, 159, 202, 9, 190, 175, 173, 57, 106, 2, 57, 7, 91, 87, 184,
                48, 247, 115, 125, 224, 149, 161, 134, 190, 86, 246, 192, 31, 244, 48, 235, 254,
                232, 189, 221, 83, 97, 217, 251, 169, 207, 2,
            ]
        } else {
            [
                2, 0, 58, 29, 54, 47, 159, 159, 182, 228, 68, 52, 6, 68, 92, 201, 145, 37, 112,
                106, 212, 97, 236, 215, 222, 166, 5, 122, 85, 202, 178, 51, 233, 46, 100, 243, 212,
                11, 88, 51, 39, 138, 120, 228, 232, 127, 204, 152, 227, 118, 45, 118, 113, 67, 152,
                14, 170, 216, 59, 170, 209, 6, 116, 14,
            ]
        };
        let mut wire = Vec::with_capacity(1 + signature.len() + message.len());
        wire.push(1);
        wire.extend_from_slice(&signature);
        wire.extend_from_slice(&message);
        (wire, fee_payer, Sha256::digest(&message).into(), signature)
    }

    #[test]
    fn production_inspector_verifies_exact_legacy_wire_and_rejects_aliases() {
        let inspector = SolanaSdkSignedTransactionInspectorV1;
        let (wire, fee_payer, unsigned_message_sha256, signature) = signed_wire(false);
        assert_eq!(
            inspector.inspect_and_verify_signed_transaction_v1(&wire),
            Some(InspectedSignedTransactionV1 {
                transaction_signature: signature,
                fee_payer,
                unsigned_message_sha256,
            })
        );

        let mut trailing_alias = wire.clone();
        trailing_alias.push(0);
        assert_eq!(
            inspector.inspect_and_verify_signed_transaction_v1(&trailing_alias),
            None
        );

        let mut noncanonical_signature_count = Vec::with_capacity(wire.len() + 1);
        noncanonical_signature_count.extend_from_slice(&[0x81, 0]);
        noncanonical_signature_count.extend_from_slice(&wire[1..]);
        assert_eq!(
            inspector.inspect_and_verify_signed_transaction_v1(&noncanonical_signature_count),
            None
        );

        let mut changed_message = wire;
        *changed_message.last_mut().unwrap() = 1;
        assert_eq!(
            inspector.inspect_and_verify_signed_transaction_v1(&changed_message),
            None
        );

        let (v0_wire, v0_fee_payer, v0_message_sha256, v0_signature) = signed_wire(true);
        assert_eq!(
            inspector.inspect_and_verify_signed_transaction_v1(&v0_wire),
            Some(InspectedSignedTransactionV1 {
                transaction_signature: v0_signature,
                fee_payer: v0_fee_payer,
                unsigned_message_sha256: v0_message_sha256,
            })
        );
    }

    #[test]
    fn signed_wire_is_persisted_before_submission_and_reconciles_after_restart() {
        let directory = TestDirectory::new();
        let path = directory.0.join("execution.state");
        let request_id = [0x11; 32];
        let policy_id = [0x12; 32];
        let lookup_tables = vec![AuthenticatedAddressLookupTableV1::new(
            Pubkey::new_from_array([0x81; 32]),
            solana_sdk_ids::address_lookup_table::id(),
            simulation().simulated_at_slot,
            1_000_000,
            false,
            9,
            SolanaRpcCommitmentV1::Finalized,
            [0x82; 32],
            vec![0x83; 56],
        )
        .unwrap()];
        let mut journal = DurableRelayerExecutionJournalV1::open_or_create_v1(&path).unwrap();
        let mut impossible_priority_fee = simulation();
        impossible_priority_fee.compute_unit_price_micro_lamports = u64::MAX;
        assert_eq!(
            journal.record_simulation_v1([0x10; 32], policy_id, impossible_priority_fee, &[]),
            Err(RelayerExecutionJournalErrorV1::InvalidRecord)
        );
        assert_eq!(
            journal
                .record_simulation_v1(request_id, policy_id, simulation(), &lookup_tables)
                .unwrap(),
            RelayerExecutionJournalUpdateV1::Inserted
        );
        assert_eq!(
            journal
                .record_signed_wire_v1(request_id, &[1, 2, 3, 4], &Inspector)
                .unwrap(),
            RelayerExecutionJournalUpdateV1::Inserted
        );
        assert_eq!(
            journal
                .record_signed_wire_v1(request_id, &[4, 3, 2, 1], &Inspector)
                .err(),
            Some(RelayerExecutionJournalErrorV1::SignedTransactionRejected)
        );
        assert_eq!(journal.records()[0].submission, None);
        drop(journal);

        let mut journal = DurableRelayerExecutionJournalV1::open_or_create_v1(&path).unwrap();
        assert_eq!(journal.records()[0].simulation_lookup_tables, lookup_tables);
        assert_eq!(
            journal.records()[0].signed.as_ref().unwrap().signed_wire,
            [1, 2, 3, 4]
        );
        let submission = RelayerSubmissionEvidenceV1 {
            submitted_at_slot: 101,
            provider_set_digest: [0x61; 32],
        };
        journal
            .record_submission_v1(request_id, [0x51; 64], submission)
            .unwrap();
        let finalized = RelayerFinalizedEvidenceV1 {
            point: FinalizedChainPointV1::new(102, [0x71; 32]).unwrap(),
            fee_lamports: 10_000,
            compute_units_consumed: 1_200_000,
            execution_result_sha256: [0x72; 32],
            poststate_sha256: [0x73; 32],
            provider_set_digest: [0x61; 32],
        };
        journal
            .record_finalized_v1(request_id, [0x51; 64], finalized)
            .unwrap();
        drop(journal);

        let mut journal = DurableRelayerExecutionJournalV1::open_or_create_v1(&path).unwrap();
        assert_eq!(
            journal.records()[0].outcome,
            Some(RelayerExecutionOutcomeV1::Finalized(finalized))
        );
        assert_eq!(
            journal
                .record_signed_wire_v1(request_id, &[1, 2, 3, 4], &Inspector)
                .unwrap(),
            RelayerExecutionJournalUpdateV1::AlreadyPresent
        );
        assert_eq!(
            journal
                .record_submission_v1(request_id, [0x51; 64], submission)
                .unwrap(),
            RelayerExecutionJournalUpdateV1::AlreadyPresent
        );
    }
}
