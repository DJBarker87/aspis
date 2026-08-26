//! Exact Solana transaction binding for durable relayer plans.
//!
//! A successful simulation hash and a valid signature are insufficient if a
//! runtime port can substitute a different instruction or resolve a v0 lookup
//! against unauthenticated table contents. This module parses the signed wire,
//! authenticates every lookup table from its raw account image, reconstructs
//! the canonical legacy/v0 message from the durable [`RelayerPlanV1`], and
//! requires byte-for-byte message equality before the wire may be journaled.

use std::collections::HashSet;

use bincode::Options as _;
use sha2::{Digest as _, Sha256};
use solana_address_lookup_table_interface::state::AddressLookupTable;
use solana_compute_budget_interface::ComputeBudgetInstruction;
use solana_message::{legacy, v0, AddressLookupTableAccount, VersionedMessage};
use solana_program::{hash::Hash, pubkey::Pubkey};
use solana_transaction::versioned::VersionedTransaction;

use crate::{
    finalized_indexer::SolanaRpcCommitmentV1,
    operator_startup::OperatorStartupReceiptV1,
    relayer::{
        prepare_permissionless_prepared_relayer_plan_v1, prepare_permissionless_relayer_plan_v1,
        RelayerPlanV1,
    },
    relayer_execution_journal::{
        InspectedSignedTransactionV1, RelayerSimulationEvidenceV1, SignedTransactionInspectorV1,
        SolanaSdkSignedTransactionInspectorV1,
    },
};

pub const RELAYER_SIMULATION_ACCOUNTS_DOMAIN_V1: &[u8] =
    b"aspis:pool-v1:relayer-simulation-accounts:sha256:v1";

const MAX_SIGNED_TRANSACTION_WIRE_BYTES_V1: usize = 4096;
const MAX_LOOKUP_TABLES_V1: usize = 256;
const MAX_LOOKUP_TABLE_ACCOUNT_DATA_BYTES_V1: usize = 56 + 256 * 32;

/// Exact finalized account image used to resolve one v0 address lookup.
///
/// The simulation adapter must fetch this image at the same contextual slot
/// recorded in [`RelayerSimulationEvidenceV1`]. The owner and complete account
/// bytes are checked here; resolved caller-supplied addresses are never trusted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AuthenticatedAddressLookupTableV1 {
    address: Pubkey,
    owner: Pubkey,
    observed_slot: u64,
    lamports: u64,
    executable: bool,
    rent_epoch: u64,
    commitment: SolanaRpcCommitmentV1,
    provider_set_digest: [u8; 32],
    account_data: Vec<u8>,
}

impl AuthenticatedAddressLookupTableV1 {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        address: Pubkey,
        owner: Pubkey,
        observed_slot: u64,
        lamports: u64,
        executable: bool,
        rent_epoch: u64,
        commitment: SolanaRpcCommitmentV1,
        provider_set_digest: [u8; 32],
        account_data: Vec<u8>,
    ) -> Result<Self, RelayerTransactionErrorV1> {
        if address == Pubkey::default()
            || observed_slot == 0
            || lamports == 0
            || executable
            || commitment != SolanaRpcCommitmentV1::Finalized
            || provider_set_digest == [0u8; 32]
            || !(56..=MAX_LOOKUP_TABLE_ACCOUNT_DATA_BYTES_V1).contains(&account_data.len())
        {
            return Err(RelayerTransactionErrorV1::InvalidLookupTableAccount);
        }
        Ok(Self {
            address,
            owner,
            observed_slot,
            lamports,
            executable,
            rent_epoch,
            commitment,
            provider_set_digest,
            account_data,
        })
    }

    pub fn address(&self) -> Pubkey {
        self.address
    }

    pub fn observed_slot(&self) -> u64 {
        self.observed_slot
    }

    pub(crate) fn owner(&self) -> Pubkey {
        self.owner
    }

    pub(crate) fn lamports(&self) -> u64 {
        self.lamports
    }

    pub(crate) fn executable(&self) -> bool {
        self.executable
    }

    pub(crate) fn rent_epoch(&self) -> u64 {
        self.rent_epoch
    }

    pub(crate) fn commitment(&self) -> SolanaRpcCommitmentV1 {
        self.commitment
    }

    pub fn provider_set_digest(&self) -> &[u8; 32] {
        &self.provider_set_digest
    }

    pub fn account_data(&self) -> &[u8] {
        &self.account_data
    }
}

/// Exact signer output plus the authenticated lookup-table images retained
/// from the successful simulation. Legacy messages carry an empty table list.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelayerSignedTransactionArtifactV1 {
    pub signed_wire: Vec<u8>,
    pub lookup_tables: Vec<AuthenticatedAddressLookupTableV1>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ValidatedRelayerTransactionV1 {
    pub inspected: InspectedSignedTransactionV1,
    pub simulation_accounts_sha256: [u8; 32],
    pub lookup_table_count: u16,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactUnsignedRelayerMessageV1 {
    message: VersionedMessage,
    serialized_message: Vec<u8>,
    message_sha256: [u8; 32],
    simulation_accounts_sha256: [u8; 32],
    lookup_table_count: u16,
}

impl ExactUnsignedRelayerMessageV1 {
    pub fn message(&self) -> &VersionedMessage {
        &self.message
    }

    pub fn serialized_message(&self) -> &[u8] {
        &self.serialized_message
    }

    pub fn message_sha256(&self) -> &[u8; 32] {
        &self.message_sha256
    }

    pub fn simulation_accounts_sha256(&self) -> &[u8; 32] {
        &self.simulation_accounts_sha256
    }

    pub fn lookup_table_count(&self) -> u16 {
        self.lookup_table_count
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelayerTransactionErrorV1 {
    SignedWireTooLarge,
    SignedTransactionRejected,
    SignedMessageMismatch,
    WrongFeePayer,
    WrongRecentBlockhash,
    WrongSimulationAccountsDigest,
    InvalidDurablePlan,
    InvalidSimulationEvidence,
    StartupReceiptMismatch,
    ProviderSetMismatch,
    TooManyLookupTables,
    LookupTableCountMismatch,
    LookupTableOrderMismatch,
    DuplicateLookupTable,
    WrongLookupTableOwner,
    WrongLookupTableSlot,
    InvalidLookupTableAccount,
    InactiveLookupTable,
    SameSlotLookupTableExtension,
    DuplicateLookupTableAddress,
    MessageCompileFailed,
}

/// Canonical digest persisted with the simulation before signing.
///
/// Besides the exact ALT account images, the digest binds the durable request,
/// authenticated Pool snapshot and contextual simulation slot. The input table
/// order is significant and must equal the v0 message lookup order.
pub fn relayer_simulation_accounts_sha256_v1(
    plan: &RelayerPlanV1,
    simulated_at_slot: u64,
    provider_set_digest: [u8; 32],
    lookup_tables: &[AuthenticatedAddressLookupTableV1],
) -> Result<[u8; 32], RelayerTransactionErrorV1> {
    let count = u16::try_from(lookup_tables.len())
        .map_err(|_| RelayerTransactionErrorV1::TooManyLookupTables)?;
    if lookup_tables.len() > MAX_LOOKUP_TABLES_V1 {
        return Err(RelayerTransactionErrorV1::TooManyLookupTables);
    }

    if provider_set_digest == [0u8; 32] {
        return Err(RelayerTransactionErrorV1::ProviderSetMismatch);
    }
    let mut seen = HashSet::with_capacity(lookup_tables.len());
    let mut previous = None;
    let mut hasher = Sha256::new();
    hasher.update(RELAYER_SIMULATION_ACCOUNTS_DOMAIN_V1);
    hasher.update(plan.request_id);
    hasher.update(plan.snapshot.pinned_program_id.as_ref());
    hasher.update(plan.snapshot.registry_program.as_ref());
    hasher.update(plan.snapshot.current_root_sequence.to_le_bytes());
    hasher.update(plan.snapshot.observed_slot.to_le_bytes());
    hasher.update(plan.snapshot.pool_state_sha256);
    hasher.update(simulated_at_slot.to_le_bytes());
    hasher.update(provider_set_digest);
    hasher.update(count.to_le_bytes());
    for table in lookup_tables {
        if !seen.insert(table.address) {
            return Err(RelayerTransactionErrorV1::DuplicateLookupTable);
        }
        if table.observed_slot != simulated_at_slot {
            return Err(RelayerTransactionErrorV1::WrongLookupTableSlot);
        }
        if previous.is_some_and(|key| key >= table.address) {
            return Err(RelayerTransactionErrorV1::LookupTableOrderMismatch);
        }
        previous = Some(table.address);
        if table.provider_set_digest != provider_set_digest {
            return Err(RelayerTransactionErrorV1::ProviderSetMismatch);
        }
        if table.commitment != SolanaRpcCommitmentV1::Finalized
            || table.executable
            || table.lamports == 0
            || !(56..=MAX_LOOKUP_TABLE_ACCOUNT_DATA_BYTES_V1).contains(&table.account_data.len())
        {
            return Err(RelayerTransactionErrorV1::InvalidLookupTableAccount);
        }
        let data_len = u32::try_from(table.account_data.len())
            .map_err(|_| RelayerTransactionErrorV1::InvalidLookupTableAccount)?;
        hasher.update(table.address.as_ref());
        hasher.update(table.owner.as_ref());
        hasher.update(table.observed_slot.to_le_bytes());
        hasher.update(table.lamports.to_le_bytes());
        hasher.update([u8::from(table.executable)]);
        hasher.update(table.rent_epoch.to_le_bytes());
        hasher.update([commitment_byte_v1(table.commitment)]);
        hasher.update(table.provider_set_digest);
        hasher.update(data_len.to_le_bytes());
        hasher.update(&table.account_data);
    }
    Ok(hasher.finalize().into())
}

/// Verify signatures and prove that the signed legacy/v0 message is exactly
/// the canonical transaction for `plan` and the successful simulation.
pub fn assemble_exact_unsigned_relayer_message_v1(
    plan: &RelayerPlanV1,
    startup: &OperatorStartupReceiptV1,
    simulation: RelayerSimulationEvidenceV1,
    lookup_tables: &[AuthenticatedAddressLookupTableV1],
) -> Result<ExactUnsignedRelayerMessageV1, RelayerTransactionErrorV1> {
    validate_durable_plan_v1(plan)?;
    if simulation.simulated_at_slot < plan.snapshot.observed_slot
        || simulation.recent_blockhash == [0u8; 32]
        || simulation.last_valid_block_height == 0
        || simulation.fee_payer != plan.fee_payer.to_bytes()
        || simulation.compute_unit_limit == 0
        || simulation.compute_units_consumed > u64::from(simulation.compute_unit_limit)
        || simulation.estimated_fee_lamports == 0
        || minimum_priority_fee_lamports_v1(
            simulation.compute_unit_limit,
            simulation.compute_unit_price_micro_lamports,
        ) > u128::from(simulation.estimated_fee_lamports)
    {
        return Err(RelayerTransactionErrorV1::InvalidSimulationEvidence);
    }
    if simulation.startup_receipt_digest != *startup.receipt_digest() {
        return Err(RelayerTransactionErrorV1::StartupReceiptMismatch);
    }
    let accounts_digest = relayer_simulation_accounts_sha256_v1(
        plan,
        simulation.simulated_at_slot,
        *startup.provider_set_digest(),
        lookup_tables,
    )?;
    if accounts_digest != simulation.simulation_accounts_sha256 {
        return Err(RelayerTransactionErrorV1::WrongSimulationAccountsDigest);
    }

    let instructions = canonical_relayer_instructions_v1(plan, simulation);
    let recent_blockhash = Hash::new_from_array(simulation.recent_blockhash);
    let message = if lookup_tables.is_empty() {
        VersionedMessage::Legacy(legacy::Message::new_with_blockhash(
            &instructions,
            Some(&plan.fee_payer),
            &recent_blockhash,
        ))
    } else {
        let tables = resolve_lookup_tables_v1(simulation.simulated_at_slot, lookup_tables)?;
        let message =
            v0::Message::try_compile(&plan.fee_payer, &instructions, &tables, recent_blockhash)
                .map_err(|_| RelayerTransactionErrorV1::MessageCompileFailed)?;
        if message.address_table_lookups.len() != lookup_tables.len() {
            return Err(RelayerTransactionErrorV1::LookupTableCountMismatch);
        }
        VersionedMessage::V0(message)
    };
    let serialized_message = message.serialize();
    let message_sha256 = Sha256::digest(&serialized_message).into();
    if message_sha256 != simulation.unsigned_message_sha256 {
        return Err(RelayerTransactionErrorV1::SignedMessageMismatch);
    }

    Ok(ExactUnsignedRelayerMessageV1 {
        message,
        serialized_message,
        message_sha256,
        simulation_accounts_sha256: accounts_digest,
        lookup_table_count: u16::try_from(lookup_tables.len())
            .map_err(|_| RelayerTransactionErrorV1::TooManyLookupTables)?,
    })
}

/// Verify signatures and prove that the signed legacy/v0 message is exactly
/// the reconstructed transaction for `plan` and the persisted simulation.
pub fn validate_exact_relayer_transaction_v1(
    plan: &RelayerPlanV1,
    startup: &OperatorStartupReceiptV1,
    simulation: RelayerSimulationEvidenceV1,
    artifact: &RelayerSignedTransactionArtifactV1,
) -> Result<ValidatedRelayerTransactionV1, RelayerTransactionErrorV1> {
    let expected = assemble_exact_unsigned_relayer_message_v1(
        plan,
        startup,
        simulation,
        &artifact.lookup_tables,
    )?;
    if artifact.signed_wire.is_empty()
        || artifact.signed_wire.len() > MAX_SIGNED_TRANSACTION_WIRE_BYTES_V1
    {
        return Err(RelayerTransactionErrorV1::SignedWireTooLarge);
    }
    let transaction: VersionedTransaction = bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .with_limit(MAX_SIGNED_TRANSACTION_WIRE_BYTES_V1 as u64)
        .reject_trailing_bytes()
        .deserialize(&artifact.signed_wire)
        .map_err(|_| RelayerTransactionErrorV1::SignedTransactionRejected)?;
    transaction
        .sanitize()
        .map_err(|_| RelayerTransactionErrorV1::SignedTransactionRejected)?;
    let inspected = SolanaSdkSignedTransactionInspectorV1
        .inspect_and_verify_signed_transaction_v1(&artifact.signed_wire)
        .ok_or(RelayerTransactionErrorV1::SignedTransactionRejected)?;
    if inspected.fee_payer != plan.fee_payer.to_bytes() {
        return Err(RelayerTransactionErrorV1::WrongFeePayer);
    }
    if transaction.message != expected.message {
        return Err(RelayerTransactionErrorV1::SignedMessageMismatch);
    }

    Ok(ValidatedRelayerTransactionV1 {
        inspected,
        simulation_accounts_sha256: expected.simulation_accounts_sha256,
        lookup_table_count: expected.lookup_table_count,
    })
}

fn canonical_relayer_instructions_v1(
    plan: &RelayerPlanV1,
    simulation: RelayerSimulationEvidenceV1,
) -> Vec<solana_program::instruction::Instruction> {
    let mut instructions = Vec::with_capacity(3);
    instructions.push(ComputeBudgetInstruction::set_compute_unit_limit(
        simulation.compute_unit_limit,
    ));
    if canonical_relayer_instruction_index_v1(simulation) == 2 {
        instructions.push(ComputeBudgetInstruction::set_compute_unit_price(
            simulation.compute_unit_price_micro_lamports,
        ));
    }
    instructions.push(plan.instruction.clone());
    instructions
}

/// Zero-based top-level position of the sole Pool instruction in the exact
/// canonical relayer transaction.
pub fn canonical_relayer_instruction_index_v1(simulation: RelayerSimulationEvidenceV1) -> u16 {
    if simulation.compute_unit_price_micro_lamports == 0 {
        1
    } else {
        2
    }
}

fn resolve_lookup_tables_v1(
    simulated_at_slot: u64,
    authenticated: &[AuthenticatedAddressLookupTableV1],
) -> Result<Vec<AddressLookupTableAccount>, RelayerTransactionErrorV1> {
    if authenticated.len() > MAX_LOOKUP_TABLES_V1 {
        return Err(RelayerTransactionErrorV1::TooManyLookupTables);
    }
    let mut output = Vec::with_capacity(authenticated.len());
    let mut all_addresses = HashSet::new();
    let mut previous_key = None;
    for account in authenticated {
        if previous_key.is_some_and(|key| key >= account.address) {
            return Err(RelayerTransactionErrorV1::LookupTableOrderMismatch);
        }
        previous_key = Some(account.address);
        if account.owner != solana_sdk_ids::address_lookup_table::id() {
            return Err(RelayerTransactionErrorV1::WrongLookupTableOwner);
        }
        if account.observed_slot != simulated_at_slot {
            return Err(RelayerTransactionErrorV1::WrongLookupTableSlot);
        }
        if account.executable || account.account_data.len() > MAX_LOOKUP_TABLE_ACCOUNT_DATA_BYTES_V1
        {
            return Err(RelayerTransactionErrorV1::InvalidLookupTableAccount);
        }
        let table = AddressLookupTable::deserialize(&account.account_data)
            .map_err(|_| RelayerTransactionErrorV1::InvalidLookupTableAccount)?;
        if table.meta.deactivation_slot != u64::MAX {
            return Err(RelayerTransactionErrorV1::InactiveLookupTable);
        }
        if table.meta.last_extended_slot >= simulated_at_slot {
            return Err(RelayerTransactionErrorV1::SameSlotLookupTableExtension);
        }
        if usize::from(table.meta.last_extended_slot_start_index) > table.addresses.len() {
            return Err(RelayerTransactionErrorV1::InvalidLookupTableAccount);
        }
        if table
            .addresses
            .iter()
            .any(|address| !all_addresses.insert(*address))
        {
            return Err(RelayerTransactionErrorV1::DuplicateLookupTableAddress);
        }
        output.push(AddressLookupTableAccount {
            key: account.address,
            addresses: table.addresses.to_vec(),
        });
    }
    Ok(output)
}

fn validate_durable_plan_v1(plan: &RelayerPlanV1) -> Result<(), RelayerTransactionErrorV1> {
    let rebuilt = match plan.prepared_plan {
        Some(context) => prepare_permissionless_prepared_relayer_plan_v1(
            plan.snapshot,
            plan.fee_payer,
            &context,
            &plan.instruction,
        ),
        None => {
            prepare_permissionless_relayer_plan_v1(plan.snapshot, plan.fee_payer, &plan.instruction)
        }
    }
    .map_err(|_| RelayerTransactionErrorV1::InvalidDurablePlan)?;
    if rebuilt != *plan {
        return Err(RelayerTransactionErrorV1::InvalidDurablePlan);
    }
    Ok(())
}

fn commitment_byte_v1(commitment: SolanaRpcCommitmentV1) -> u8 {
    match commitment {
        SolanaRpcCommitmentV1::Processed => 0,
        SolanaRpcCommitmentV1::Confirmed => 1,
        SolanaRpcCommitmentV1::Finalized => 2,
    }
}

fn minimum_priority_fee_lamports_v1(compute_unit_limit: u32, micro_lamports: u64) -> u128 {
    const MICRO_LAMPORTS_PER_LAMPORT: u128 = 1_000_000;
    let numerator = u128::from(compute_unit_limit) * u128::from(micro_lamports);
    numerator.div_ceil(MICRO_LAMPORTS_PER_LAMPORT)
}

#[cfg(test)]
mod tests {
    use std::borrow::Cow;

    use aspis_core::field::M31;
    use aspis_pool::{deposit::DepositRequestV1, pool_v1_state_address};
    use aspis_statement::poseidon2::Digest;
    use solana_address_lookup_table_interface::state::LookupTableMeta;
    use solana_keypair::Keypair;
    use solana_signer::Signer;

    use super::*;
    use crate::{
        operator_startup::{FinalizedReleaseCheckpointV1, OperatorStartupReceiptV1},
        relayer::{prepare_permissionless_relayer_plan_v1, RelayerSnapshotV1},
        scan_state::FinalizedChainPointV1,
        transaction_builder::build_deposit_instruction_v1,
    };

    const SIMULATION_SLOT: u64 = 101;
    const COMPUTE_UNIT_LIMIT: u32 = 1_400_000;
    const COMPUTE_UNIT_PRICE: u64 = 7;

    fn key(seed: u8) -> Pubkey {
        Pubkey::new_from_array([seed; 32])
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn fixture() -> (Keypair, Keypair, RelayerPlanV1, OperatorStartupReceiptV1) {
        let fee_payer = Keypair::new();
        let source_authority = Keypair::new();
        let program_id = key(1);
        let mint = key(2);
        let pool = pool_v1_state_address(&program_id, &mint).0;
        let request = DepositRequestV1 {
            owner_key: digest(10),
            amount: 77,
            salt: digest(20),
            encrypted_note_payload: &[],
        };
        let instruction = build_deposit_instruction_v1(
            program_id,
            pool,
            mint,
            7,
            key(3),
            source_authority.pubkey(),
            None,
            &request,
        )
        .unwrap();
        let snapshot = RelayerSnapshotV1 {
            pinned_program_id: program_id,
            registry_program: key(5),
            current_root_sequence: 7,
            observed_slot: 90,
            pool_state_sha256: [0xab; 32],
        };
        let plan =
            prepare_permissionless_relayer_plan_v1(snapshot, fee_payer.pubkey(), &instruction)
                .unwrap();
        let checkpoint = FinalizedReleaseCheckpointV1 {
            point: FinalizedChainPointV1::new(90, [0x91; 32]).unwrap(),
            pool_state_sha256: snapshot.pool_state_sha256,
            root_sequence: snapshot.current_root_sequence,
            root: [0x92; 32],
        };
        let startup = OperatorStartupReceiptV1::test_only_v1([0x93; 32], [0x94; 32], checkpoint);
        (fee_payer, source_authority, plan, startup)
    }

    fn table_for_plan(
        plan: &RelayerPlanV1,
        startup: &OperatorStartupReceiptV1,
        meta: LookupTableMeta,
    ) -> AuthenticatedAddressLookupTableV1 {
        let mut addresses = Vec::new();
        for account in &plan.instruction.accounts {
            if !account.is_signer && !addresses.contains(&account.pubkey) {
                addresses.push(account.pubkey);
            }
        }
        let account_data = AddressLookupTable {
            meta,
            addresses: Cow::Owned(addresses),
        }
        .serialize_for_tests()
        .unwrap();
        AuthenticatedAddressLookupTableV1::new(
            key(240),
            solana_sdk_ids::address_lookup_table::id(),
            SIMULATION_SLOT,
            1_000_000,
            false,
            0,
            SolanaRpcCommitmentV1::Finalized,
            *startup.provider_set_digest(),
            account_data,
        )
        .unwrap()
    }

    fn signed_artifact(
        fee_payer: &Keypair,
        source_authority: &Keypair,
        plan: &RelayerPlanV1,
        startup: &OperatorStartupReceiptV1,
        lookup_tables: Vec<AuthenticatedAddressLookupTableV1>,
    ) -> (
        RelayerSimulationEvidenceV1,
        RelayerSignedTransactionArtifactV1,
    ) {
        let instructions = canonical_relayer_instructions_v1(
            plan,
            RelayerSimulationEvidenceV1 {
                simulated_at_slot: SIMULATION_SLOT,
                recent_blockhash: [0x39; 32],
                last_valid_block_height: 500,
                fee_payer: plan.fee_payer.to_bytes(),
                unsigned_message_sha256: [1; 32],
                simulation_result_sha256: [2; 32],
                simulation_accounts_sha256: [3; 32],
                startup_receipt_digest: *startup.receipt_digest(),
                compute_unit_limit: COMPUTE_UNIT_LIMIT,
                compute_unit_price_micro_lamports: COMPUTE_UNIT_PRICE,
                compute_units_consumed: 1_200_000,
                estimated_fee_lamports: 10_000,
            },
        );
        let recent_blockhash = Hash::new_from_array([0x39; 32]);
        let message = if lookup_tables.is_empty() {
            VersionedMessage::Legacy(legacy::Message::new_with_blockhash(
                &instructions,
                Some(&plan.fee_payer),
                &recent_blockhash,
            ))
        } else {
            let resolved: Vec<_> = lookup_tables
                .iter()
                .map(|table| {
                    let decoded = AddressLookupTable::deserialize(&table.account_data).unwrap();
                    AddressLookupTableAccount {
                        key: table.address,
                        addresses: decoded.addresses.to_vec(),
                    }
                })
                .collect();
            VersionedMessage::V0(
                v0::Message::try_compile(
                    &plan.fee_payer,
                    &instructions,
                    &resolved,
                    recent_blockhash,
                )
                .unwrap(),
            )
        };
        let unsigned_message_sha256 = Sha256::digest(message.serialize()).into();
        let transaction =
            VersionedTransaction::try_new(message, &[fee_payer, source_authority]).unwrap();
        let simulation_accounts_sha256 = relayer_simulation_accounts_sha256_v1(
            plan,
            SIMULATION_SLOT,
            *startup.provider_set_digest(),
            &lookup_tables,
        )
        .unwrap();
        let simulation = RelayerSimulationEvidenceV1 {
            simulated_at_slot: SIMULATION_SLOT,
            recent_blockhash: [0x39; 32],
            last_valid_block_height: 500,
            fee_payer: plan.fee_payer.to_bytes(),
            unsigned_message_sha256,
            simulation_result_sha256: [0xa1; 32],
            simulation_accounts_sha256,
            startup_receipt_digest: *startup.receipt_digest(),
            compute_unit_limit: COMPUTE_UNIT_LIMIT,
            compute_unit_price_micro_lamports: COMPUTE_UNIT_PRICE,
            compute_units_consumed: 1_200_000,
            estimated_fee_lamports: 10_000,
        };
        (
            simulation,
            RelayerSignedTransactionArtifactV1 {
                signed_wire: bincode::serialize(&transaction).unwrap(),
                lookup_tables,
            },
        )
    }

    #[test]
    fn exact_legacy_message_binds_plan_budget_priority_and_restart_inputs() {
        let (fee_payer, source_authority, plan, startup) = fixture();
        let (simulation, artifact) =
            signed_artifact(&fee_payer, &source_authority, &plan, &startup, vec![]);
        let validated =
            validate_exact_relayer_transaction_v1(&plan, &startup, simulation, &artifact).unwrap();
        assert_eq!(validated.lookup_table_count, 0);
        assert_eq!(validated.inspected.fee_payer, plan.fee_payer.to_bytes());

        let mut changed_budget = simulation;
        changed_budget.compute_unit_limit -= 1;
        assert_eq!(
            validate_exact_relayer_transaction_v1(&plan, &startup, changed_budget, &artifact,),
            Err(RelayerTransactionErrorV1::SignedMessageMismatch)
        );

        let mut changed_priority = simulation;
        changed_priority.compute_unit_price_micro_lamports += 1;
        assert_eq!(
            validate_exact_relayer_transaction_v1(&plan, &startup, changed_priority, &artifact,),
            Err(RelayerTransactionErrorV1::SignedMessageMismatch)
        );

        let mut forged_plan = plan.clone();
        forged_plan.instruction.data.push(0);
        assert_eq!(
            validate_exact_relayer_transaction_v1(&forged_plan, &startup, simulation, &artifact,),
            Err(RelayerTransactionErrorV1::InvalidDurablePlan)
        );
    }

    #[test]
    fn exact_v0_message_uses_finalized_raw_alt_and_rejects_state_substitution() {
        let (fee_payer, source_authority, plan, startup) = fixture();
        let table = table_for_plan(
            &plan,
            &startup,
            LookupTableMeta {
                last_extended_slot: 100,
                ..LookupTableMeta::default()
            },
        );
        let (simulation, artifact) =
            signed_artifact(&fee_payer, &source_authority, &plan, &startup, vec![table]);
        let validated =
            validate_exact_relayer_transaction_v1(&plan, &startup, simulation, &artifact).unwrap();
        assert_eq!(validated.lookup_table_count, 1);

        let mut wrong_owner = artifact.clone();
        wrong_owner.lookup_tables[0].owner = key(88);
        let mut wrong_owner_simulation = simulation;
        wrong_owner_simulation.simulation_accounts_sha256 = relayer_simulation_accounts_sha256_v1(
            &plan,
            SIMULATION_SLOT,
            *startup.provider_set_digest(),
            &wrong_owner.lookup_tables,
        )
        .unwrap();
        assert_eq!(
            validate_exact_relayer_transaction_v1(
                &plan,
                &startup,
                wrong_owner_simulation,
                &wrong_owner,
            ),
            Err(RelayerTransactionErrorV1::WrongLookupTableOwner)
        );

        let same_slot_table = table_for_plan(
            &plan,
            &startup,
            LookupTableMeta {
                last_extended_slot: SIMULATION_SLOT,
                ..LookupTableMeta::default()
            },
        );
        let mut same_slot = artifact.clone();
        same_slot.lookup_tables = vec![same_slot_table];
        let mut same_slot_simulation = simulation;
        same_slot_simulation.simulation_accounts_sha256 = relayer_simulation_accounts_sha256_v1(
            &plan,
            SIMULATION_SLOT,
            *startup.provider_set_digest(),
            &same_slot.lookup_tables,
        )
        .unwrap();
        assert_eq!(
            validate_exact_relayer_transaction_v1(
                &plan,
                &startup,
                same_slot_simulation,
                &same_slot,
            ),
            Err(RelayerTransactionErrorV1::SameSlotLookupTableExtension)
        );

        let mut changed_address = artifact;
        changed_address.lookup_tables[0].account_data[56] ^= 1;
        let mut changed_address_simulation = simulation;
        changed_address_simulation.simulation_accounts_sha256 =
            relayer_simulation_accounts_sha256_v1(
                &plan,
                SIMULATION_SLOT,
                *startup.provider_set_digest(),
                &changed_address.lookup_tables,
            )
            .unwrap();
        assert_eq!(
            validate_exact_relayer_transaction_v1(
                &plan,
                &startup,
                changed_address_simulation,
                &changed_address,
            ),
            Err(RelayerTransactionErrorV1::SignedMessageMismatch)
        );
    }
}
