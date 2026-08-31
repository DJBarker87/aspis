#![cfg(feature = "eight-lane-plumbing-v2")]

use aspis_core::field::M31;
use aspis_pool::{
    deposit::DepositRequestV1,
    instruction::{encode_transition_receipt_v1, TransitionReceiptV1},
    pool_v1_pair_forest_checkpoint_address, pool_v1_pair_forest_lane_address,
    pool_v1_pair_forest_master_address, pool_v1_root_page_address, pool_v1_state_address,
    pool_v1_vault_token_account_address, PrivateTransferStatementV1, POOL_V1_PAIR_EMPTY_ROOTS,
};
use aspis_pool_wallet_v1::{
    derive_viewing_keypair_v1,
    durable_state::{
        AuthenticatedSpentNoteUpdateV1, DurableRelayerStateV1, DurableStateErrorV1,
        DurableWalletStateV1, LocalSpendAuthenticatorV1, SealedNoteAccessV1,
    },
    durable_witness_state::{DurableWalletWitnessStateV1, DurableWitnessErrorV1},
    encrypt_note_v1,
    finalized_indexer::{
        ingest_finalized_rpc_block_v1, FinalizedBlockIngestResultV1, RootPageAddressBindingV1,
        SolanaRpcBlockV1, SolanaRpcCommitmentV1, SolanaRpcCompiledInstructionV1,
        SolanaRpcEncodedBinaryV1, SolanaRpcReturnDataV1, SolanaRpcRootPageAccountV1,
        SolanaRpcRootPageBatchV1, SolanaRpcTransactionV1, SolanaRpcTransactionVersionV1,
    },
    lane_forest_durable_v2::{
        canonical_lane_root_page_cursor_v2, DurableLaneForestWalletFileV2,
        ForestFinalizedAppendEventV2, ForestFinalizedAppendKindV2, ForestNoteAssociationOutcomeV2,
        LaneForestDurableErrorV2, LaneForestDurableStateV2,
    },
    lane_forest_rpc_v2::{
        derive_finalized_pair_forest_terminal_event_v2, FinalizedForestAccountV2,
        FinalizedForestRootPageV2, FinalizedPairForestTerminalObservationV2, LaneForestRpcErrorV2,
    },
    lane_forest_v2::{lane_forest_global_root_v2, LaneIdV2},
    lane_forest_wallet_txn_v2::{
        validated_protected_activation_from_image_v2, LaneForestWalletActivationPolicyV2,
        LaneForestWalletEmptyFinalizedBlockV2, LaneForestWalletTentativeCommitmentV2,
        LaneForestWalletTxnAtomicBoundaryV2, LaneForestWalletTxnAtomicFaultPointV2,
        LaneForestWalletTxnCoordinatorV2, LaneForestWalletTxnErrorV2,
        LaneForestWalletTxnFaultInjectorV2, LaneForestWalletTxnFaultPointV2,
    },
    note_store_crypto::{
        seal_recovered_note_v1, EncryptedLocalSpendAuthenticatorV1, LocalNullifierKeyStoreV1,
        NoteStoreCipherV1, NullifierKeyMaterialV1,
    },
    recompute_note_commitment_v1,
    relayer::{prepare_permissionless_relayer_plan_v1, RelayerPolicyV1, RelayerSnapshotV1},
    relayer_execution_journal::{
        DurableRelayerExecutionJournalV1, RelayerExecutionJournalErrorV1, RelayerExecutionOutcomeV1,
    },
    rpc_adapter::{
        DepositRpcBindingV1, POOL_V1_DEPOSIT_INSTRUCTION_HEADER_BYTES,
        POOL_V1_DEPOSIT_INSTRUCTION_MAGIC, POOL_V1_DEPOSIT_INSTRUCTION_VERSION,
    },
    scan_state::{
        encode_deposit_event_record_v1, DepositEventIdV1, DepositScanIdentityV1,
        DepositScanOutcomeV1, FinalizedBlockV1, FinalizedChainPointV1, LocalOwnerKeyStoreV1,
        ScanStateV1,
    },
    transaction_builder::{
        build_deposit_instruction_v1, build_private_transfer_instruction_v1,
        VerifierRouteAccountsV1,
    },
    wallet_monotonic_v2::{
        FaultInjectableWalletMonotonicStoreV2, WalletMonotonicFaultPointV2,
        WalletMonotonicPreparedNextV2, WalletMonotonicStoreV2,
    },
    wallet_populated_migration_v2::{
        migrate_locked_legacy_wallet_to_asl2_v2, recover_populated_wallet_handoff_v2,
        LockedLegacyWalletStoresV2, PopulatedWalletMigrationErrorV2, PopulatedWalletMigrationV2,
        WalletMigrationSourceRoleV2,
    },
    wallet_store_migration_v2::{
        wallet_store_migration_authority_path_v2, NoWalletStoreMigrationFaultsV2,
        WalletStoreMigrationAtomicFaultPointV2, WalletStoreMigrationFaultInjectorV2,
        WalletStoreMigrationLogicalBoundaryV2, WalletStoreMigrationLogicalFaultPointV2,
        WalletStoreMigrationPhaseV2, WalletStoreMigrationWriteV2, WalletStoreSourceRoleV2,
        WALLET_STORE_RETIREMENT_MAGIC_V2,
    },
    wallet_transition::derive_note_nullifier_v1,
    wallet_v2_activation::WalletV2ActivationPrerequisites,
    witness_state::WalletWitnessStateV1,
    NoteContextV1, NoteOpeningV1, ViewingPublicKeyV1, ViewingSecretKeyV1,
};
#[cfg(feature = "wallet-v2-reference-tests")]
use aspis_pool_wallet_v1::{
    wallet_v2_activation::{
        evaluate_wallet_v2_activation, WalletV2ActivationMode, WalletV2ProductionConfig,
    },
    wallet_v2_runtime::{
        ActivatedWalletRuntimeV2, WalletV2RuntimeError, WalletV2RuntimePolicyBindings,
    },
};
use aspis_statement::{
    decode_digest_canonical, derive_owner_key, encode_digest_canonical,
    pool_v1::{
        encode_pool_v1_pair_forest_checkpoint_v1, encode_pool_v1_pair_forest_lane_state_v1,
        encode_pool_v1_pair_forest_master_v1, encode_pool_v1_pair_forest_terminal_request_v1,
        encode_pool_v1_pair_forest_terminal_result_v1,
        root_history::initialize_root_history_page_bytes_v1, DepositEventV1, DepositReceiptV1,
        HistoricalAnchorEnvelopeV1, IncrementalMerkleTreeV1, PoolIdentityV1,
        PoolV1PairForestCheckpointV1, PoolV1PairForestLaneStateV1, PoolV1PairForestMasterV1,
        PoolV1PairForestTerminalPaymentV1, PoolV1PairForestTerminalRequestV1,
        PoolV1PairForestTerminalResultV1, PoolV1PairLeafWitnessV1, PoolV1PairVerifiedAfterstateV1,
        PoolV1PrivateTransferPublicV1, PoolV1TransitionKind, RootHistoryPageV1, VerifierPolicyV1,
        POOL_V1_PAIR_FOREST_ALL_LANES_MASK, POOL_V1_PAIR_TREE_DEPTH,
        POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
    },
    Digest,
};
use base64::{engine::general_purpose::STANDARD as BASE64_STANDARD, Engine as _};
use hpke::rand_core::{TryCryptoRng, TryRng};
use sha2::{Digest as _, Sha256};
use solana_program::pubkey::Pubkey;
#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;
use std::{
    convert::Infallible,
    fs,
    path::PathBuf,
    sync::{
        atomic::{AtomicU64, Ordering},
        mpsc::{Receiver, SyncSender},
    },
};

const LEGACY_PROGRAM: [u8; 32] = [0x91; 32];
const FOREST_PROGRAM: [u8; 32] = [0xb1; 32];
const ASRJ_CHECKSUM_DOMAIN: &[u8] = b"aspis:pool-v1:relayer-execution-journal:sha256:v1";
static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct IncrementingRng(u8);

impl TryRng for IncrementingRng {
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

impl TryCryptoRng for IncrementingRng {}

type SharedMonotonicStore = FaultInjectableWalletMonotonicStoreV2;

struct TestDirectory(PathBuf);

impl TestDirectory {
    fn new(label: &str) -> Self {
        let serial = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "aspis-v7-populated-migration-{label}-{}-{serial}",
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

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + 17 * index as u32))
}

fn point(slot: u64, byte: u8) -> FinalizedChainPointV1 {
    FinalizedChainPointV1::new(slot, [byte; 32]).unwrap()
}

fn identity() -> DepositScanIdentityV1 {
    let program = Pubkey::new_from_array(LEGACY_PROGRAM);
    let mint = Pubkey::new_from_array([0xb2; 32]);
    let pool = pool_v1_state_address(&program, &mint).0;
    let vault = pool_v1_vault_token_account_address(&program, &pool).0;
    DepositScanIdentityV1::new(
        pool.to_bytes(),
        [0xb4; 32],
        mint.to_bytes(),
        vault.to_bytes(),
        4,
    )
    .unwrap()
}

struct LocalKeys {
    owner_key: [u8; 32],
    nullifier_key: [u8; 32],
}

impl LocalOwnerKeyStoreV1 for LocalKeys {
    fn contains_owner_key_v1(&self, owner_key: &[u8; 32]) -> bool {
        owner_key == &self.owner_key
    }
}

impl LocalNullifierKeyStoreV1 for LocalKeys {
    fn nullifier_key_for_owner_v1(&self, owner_key: &[u8; 32]) -> Option<NullifierKeyMaterialV1> {
        (owner_key == &self.owner_key)
            .then(|| NullifierKeyMaterialV1::from_bytes(self.nullifier_key).unwrap())
    }
}

struct ApproveTopology;

impl LaneForestWalletActivationPolicyV2 for ApproveTopology {
    fn approves_topology_transition_v2(
        &self,
        legacy_pool: &[u8; 32],
        legacy_vault: &[u8; 32],
        forest_master: &[u8; 32],
        forest_identity_pool: &[u8; 32],
        forest_token_program: &[u8; 32],
    ) -> bool {
        legacy_pool != &[0; 32]
            && legacy_vault != &[0; 32]
            && forest_master != &[0; 32]
            && forest_identity_pool == forest_master
            && forest_token_program != &[0; 32]
    }
}

struct NeverAuthorize;

impl LocalSpendAuthenticatorV1 for NeverAuthorize {
    fn authenticates_spend_v1(&self, _: DepositEventIdV1, _: &[u8], _: &[u8; 32]) -> bool {
        false
    }
}

#[derive(Default)]
struct StopBeforeFirstLegacyTombstone {
    fired: bool,
}

impl WalletStoreMigrationFaultInjectorV2 for StopBeforeFirstLegacyTombstone {
    fn interrupt_logical_v2(&mut self, point: WalletStoreMigrationLogicalFaultPointV2) -> bool {
        let should_stop = !self.fired
            && point.boundary == WalletStoreMigrationLogicalBoundaryV2::BeforeWrite
            && matches!(point.write, WalletStoreMigrationWriteV2::LegacyTombstone(_));
        self.fired |= should_stop;
        should_stop
    }

    fn interrupt_atomic_v2(&mut self, _: WalletStoreMigrationAtomicFaultPointV2) -> bool {
        false
    }
}

struct StopAtAsl2AtomicBoundary {
    boundary: LaneForestWalletTxnAtomicBoundaryV2,
    fired: bool,
}

struct PauseBeforeJournalPrepare {
    entered: SyncSender<()>,
    release: Receiver<()>,
    paused: bool,
}

impl WalletStoreMigrationFaultInjectorV2 for PauseBeforeJournalPrepare {
    fn interrupt_logical_v2(&mut self, point: WalletStoreMigrationLogicalFaultPointV2) -> bool {
        if !self.paused
            && point.write == WalletStoreMigrationWriteV2::JournalPrepared
            && point.boundary == WalletStoreMigrationLogicalBoundaryV2::BeforeWrite
        {
            self.paused = true;
            self.entered.send(()).unwrap();
            self.release.recv().unwrap();
        }
        false
    }

    fn interrupt_atomic_v2(&mut self, _: WalletStoreMigrationAtomicFaultPointV2) -> bool {
        false
    }
}

impl LaneForestWalletTxnFaultInjectorV2 for StopAtAsl2AtomicBoundary {
    fn interrupt_v2(&mut self, _: LaneForestWalletTxnFaultPointV2) -> bool {
        false
    }

    fn interrupt_atomic_v2(&mut self, point: LaneForestWalletTxnAtomicFaultPointV2) -> bool {
        if !self.fired && point.boundary == self.boundary {
            self.fired = true;
            true
        } else {
            false
        }
    }
}

fn relayer_policy() -> RelayerPolicyV1 {
    RelayerPolicyV1 {
        paused: false,
        operator_fee_payer: Pubkey::new_from_array([0xd1; 32]),
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
        max_admissions_per_window: 2,
        max_estimated_fee_lamports: 10_000,
        minimum_fee_payer_reserve_lamports: 1_000_000,
    }
}

fn populate_relayer_admission(relayer: &mut DurableRelayerStateV1) {
    let program = Pubkey::new_from_array([0xe1; 32]);
    let mint = Pubkey::new_from_array([0xe2; 32]);
    let pool = pool_v1_state_address(&program, &mint).0;
    let instruction = build_deposit_instruction_v1(
        program,
        pool,
        mint,
        7,
        Pubkey::new_from_array([0xe3; 32]),
        Pubkey::new_from_array([0xe4; 32]),
        None,
        &DepositRequestV1 {
            owner_key: digest(810),
            amount: 9,
            salt: digest(811),
            encrypted_note_payload: &[],
        },
    )
    .unwrap();
    let plan = prepare_permissionless_relayer_plan_v1(
        RelayerSnapshotV1 {
            pinned_program_id: program,
            registry_program: Pubkey::new_from_array([0xe5; 32]),
            current_root_sequence: 7,
            observed_slot: 90,
            pool_state_sha256: [0xe6; 32],
        },
        relayer_policy().operator_fee_payer,
        &instruction,
    )
    .unwrap();
    relayer
        .admit_and_enqueue_v1(relayer_policy(), 91, 5_000, 1_005_000, &plan)
        .unwrap();
}

fn encode_base58(bytes: &[u8]) -> String {
    const ALPHABET: &[u8; 58] = b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
    let leading_zeroes = bytes.iter().take_while(|byte| **byte == 0).count();
    let mut digits = Vec::<u8>::new();
    for byte in &bytes[leading_zeroes..] {
        let mut carry = u32::from(*byte);
        for digit in &mut digits {
            let value = u32::from(*digit) * 256 + carry;
            *digit = (value % 58) as u8;
            carry = value / 58;
        }
        while carry != 0 {
            digits.push((carry % 58) as u8);
            carry /= 58;
        }
    }
    let mut output = String::with_capacity(leading_zeroes + digits.len());
    output.extend(core::iter::repeat_n('1', leading_zeroes));
    output.extend(
        digits
            .iter()
            .rev()
            .map(|digit| char::from(ALPHABET[usize::from(*digit)])),
    );
    output
}

fn ingest_one_finalized_deposit(
    scan: &mut ScanStateV1,
    note: &NoteOpeningV1,
    recipient: &ViewingPublicKeyV1,
    viewing_secret: &ViewingSecretKeyV1,
    local_keys: &LocalKeys,
    empty_tree: &IncrementalMerkleTreeV1,
) -> (FinalizedBlockIngestResultV1, IncrementalMerkleTreeV1) {
    let commitment = recompute_note_commitment_v1(note).unwrap();
    let (next_tree, _) = empty_tree
        .append_one(decode_digest_canonical(&commitment).unwrap())
        .unwrap();
    let context = NoteContextV1::new(*identity().pool(), [0xb4; 32], 0, commitment).unwrap();
    let payload = encrypt_note_v1(&mut IncrementingRng(0x10), recipient, &context, note).unwrap();

    let mut instruction = vec![0u8; POOL_V1_DEPOSIT_INSTRUCTION_HEADER_BYTES + payload.len()];
    instruction[..4].copy_from_slice(&POOL_V1_DEPOSIT_INSTRUCTION_MAGIC);
    instruction[4] = POOL_V1_DEPOSIT_INSTRUCTION_VERSION;
    instruction[6..8].copy_from_slice(&(payload.len() as u16).to_le_bytes());
    instruction[8..40].copy_from_slice(note.owner_key());
    instruction[40..44].copy_from_slice(&note.value().to_le_bytes());
    instruction[48..80].copy_from_slice(note.salt());
    instruction[80..].copy_from_slice(&payload);
    let instruction_data = encode_base58(&instruction);

    let receipt = DepositReceiptV1 {
        pool: *identity().pool(),
        asset_mint: *identity().asset_mint(),
        source_token_account: [0x55; 32],
        vault_token_account: *identity().vault_token_account(),
        amount: note.value(),
        encrypted_note_payload_bytes: payload.len() as u16,
        note_commitment: decode_digest_canonical(&commitment).unwrap(),
        leaf_index: 0,
        root_sequence: 1,
        root: next_tree.root,
    };
    let return_record = encode_deposit_event_record_v1(&DepositEventV1 {
        receipt,
        encrypted_note_payload: &payload,
    })
    .unwrap();
    let return_data = BASE64_STANDARD.encode(return_record);

    let root_page = pool_v1_root_page_address(
        &Pubkey::new_from_array(LEGACY_PROGRAM),
        &Pubkey::new_from_array(*identity().pool()),
        0,
    )
    .0
    .to_bytes();
    let encoded_keys = [
        encode_base58(&[0x61; 32]),
        encode_base58(identity().pool()),
        encode_base58(&root_page),
        encode_base58(identity().asset_mint()),
        encode_base58(&[0x55; 32]),
        encode_base58(&[0x56; 32]),
        encode_base58(identity().vault_token_account()),
        encode_base58(aspis_pool::LEGACY_SPL_TOKEN_PROGRAM_ID.as_ref()),
        encode_base58(&[0x62; 32]),
        encode_base58(&LEGACY_PROGRAM),
    ];
    let static_keys = encoded_keys.iter().map(String::as_str).collect::<Vec<_>>();
    let instruction_accounts = [1u16, 2, 3, 4, 5, 6, 7];
    let instructions = [SolanaRpcCompiledInstructionV1 {
        program_id_index: 9,
        account_indices: &instruction_accounts,
        data_base58: &instruction_data,
    }];
    let signature = encode_base58(&[0x41; 64]);
    let signatures = [signature.as_str()];
    let pool_program = encode_base58(&LEGACY_PROGRAM);
    let transactions = [SolanaRpcTransactionV1 {
        version: SolanaRpcTransactionVersionV1::Legacy,
        signatures_base58: &signatures,
        static_account_keys_base58: &static_keys,
        loaded_addresses: None,
        top_level_instructions: &instructions,
        succeeded: true,
        return_data: Some(SolanaRpcReturnDataV1 {
            program_id_base58: &pool_program,
            binary: SolanaRpcEncodedBinaryV1 {
                data: &return_data,
                encoding: "base64",
            },
        }),
    }];
    let block_hash = encode_base58(&[0xa1; 32]);
    let parent_hash = encode_base58(&[0xa0; 32]);
    let block = SolanaRpcBlockV1 {
        asserted_commitment: SolanaRpcCommitmentV1::Finalized,
        slot: 101,
        blockhash_base58: &block_hash,
        previous_blockhash_base58: &parent_hash,
        parent_slot: 100,
        transactions: &transactions,
    };

    let mut page_bytes = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
    initialize_root_history_page_bytes_v1(
        &mut page_bytes,
        *identity().pool(),
        0,
        &[empty_tree.root, next_tree.root],
    )
    .unwrap();
    let page_data = BASE64_STANDARD.encode(page_bytes);
    let page_address = encode_base58(&root_page);
    let page_owner = encode_base58(&LEGACY_PROGRAM);
    let accounts = [SolanaRpcRootPageAccountV1 {
        page_number: 0,
        address_base58: &page_address,
        owner_base58: &page_owner,
        executable: false,
        data: SolanaRpcEncodedBinaryV1 {
            data: &page_data,
            encoding: "base64",
        },
    }];
    let pages = SolanaRpcRootPageBatchV1 {
        asserted_commitment: SolanaRpcCommitmentV1::Finalized,
        context_slot: 101,
        accounts: &accounts,
    };
    let result = ingest_finalized_rpc_block_v1(
        scan,
        &DepositRpcBindingV1::new(LEGACY_PROGRAM).unwrap(),
        &[RootPageAddressBindingV1 {
            page_number: 0,
            address: root_page,
        }],
        &block,
        Some(&pages),
        viewing_secret,
        local_keys,
    )
    .unwrap();
    (result, next_tree)
}

struct PrivateTransferBlockSpec {
    slot: u64,
    block_hash_byte: u8,
    parent_slot: u64,
    parent_hash_byte: u8,
    signature_byte: u8,
    envelope: HistoricalAnchorEnvelopeV1,
    statement: PrivateTransferStatementV1,
    first_leaf_index: u64,
    intermediate_root: Digest,
    final_root: Digest,
    history_roots: Vec<Digest>,
}

fn ingest_finalized_private_transfer(
    state: &mut ScanStateV1,
    spec: &PrivateTransferBlockSpec,
    viewing_secret: &ViewingSecretKeyV1,
    local_keys: &impl LocalOwnerKeyStoreV1,
) -> FinalizedBlockIngestResultV1 {
    let built = build_private_transfer_instruction_v1(
        Pubkey::new_from_array(LEGACY_PROGRAM),
        spec.first_leaf_index,
        &spec.envelope,
        &spec.statement,
        VerifierRouteAccountsV1 {
            payer: Pubkey::new_from_array([0x63; 32]),
            registry_program: Pubkey::new_from_array([0x64; 32]),
            verifier_program: Pubkey::new_from_array([0x65; 32]),
            sealed_proof_account: Pubkey::new_from_array([0x66; 32]),
        },
    )
    .unwrap();
    let instruction_data = encode_base58(&built.data);
    let receipt = TransitionReceiptV1 {
        transition_kind: PoolV1TransitionKind::PrivateTransfer,
        pool: *identity().pool(),
        nullifier: spec.statement.nullifier,
        first_output: spec.statement.recipient_commitment,
        second_output_or_destination: encode_digest_canonical(&spec.statement.change_commitment),
        withdrawal_amount: 0,
        first_leaf_index: spec.first_leaf_index,
        second_leaf_index: spec.first_leaf_index + 1,
        root_sequence: spec.first_leaf_index + 2,
        root: spec.final_root,
    };
    let return_data = BASE64_STANDARD.encode(encode_transition_receipt_v1(&receipt).unwrap());

    let mut encoded_keys = Vec::with_capacity(built.accounts.len() + 1);
    encoded_keys.push(encode_base58(&LEGACY_PROGRAM));
    encoded_keys.extend(
        built
            .accounts
            .iter()
            .map(|account| encode_base58(account.pubkey.as_ref())),
    );
    let static_keys = encoded_keys.iter().map(String::as_str).collect::<Vec<_>>();
    let account_indices = (1..=built.accounts.len() as u16).collect::<Vec<_>>();
    let instructions = [SolanaRpcCompiledInstructionV1 {
        program_id_index: 0,
        account_indices: &account_indices,
        data_base58: &instruction_data,
    }];
    let signature = encode_base58(&[spec.signature_byte; 64]);
    let signatures = [signature.as_str()];
    let transactions = [SolanaRpcTransactionV1 {
        version: SolanaRpcTransactionVersionV1::Legacy,
        signatures_base58: &signatures,
        static_account_keys_base58: &static_keys,
        loaded_addresses: None,
        top_level_instructions: &instructions,
        succeeded: true,
        return_data: Some(SolanaRpcReturnDataV1 {
            program_id_base58: static_keys[0],
            binary: SolanaRpcEncodedBinaryV1 {
                data: &return_data,
                encoding: "base64",
            },
        }),
    }];
    let block_hash = encode_base58(&[spec.block_hash_byte; 32]);
    let parent_hash = encode_base58(&[spec.parent_hash_byte; 32]);
    let block = SolanaRpcBlockV1 {
        asserted_commitment: SolanaRpcCommitmentV1::Finalized,
        slot: spec.slot,
        blockhash_base58: &block_hash,
        previous_blockhash_base58: &parent_hash,
        parent_slot: spec.parent_slot,
        transactions: &transactions,
    };

    let mut roots = spec.history_roots.clone();
    roots[spec.first_leaf_index as usize + 1] = spec.intermediate_root;
    roots[spec.first_leaf_index as usize + 2] = spec.final_root;
    let mut page_bytes = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
    initialize_root_history_page_bytes_v1(&mut page_bytes, *identity().pool(), 0, &roots).unwrap();
    let page_data = BASE64_STANDARD.encode(page_bytes);
    let page_address_bytes = pool_v1_root_page_address(
        &Pubkey::new_from_array(LEGACY_PROGRAM),
        &Pubkey::new_from_array(*identity().pool()),
        0,
    )
    .0
    .to_bytes();
    let page_address = encode_base58(&page_address_bytes);
    let page_owner = encode_base58(&LEGACY_PROGRAM);
    let accounts = [SolanaRpcRootPageAccountV1 {
        page_number: 0,
        address_base58: &page_address,
        owner_base58: &page_owner,
        executable: false,
        data: SolanaRpcEncodedBinaryV1 {
            data: &page_data,
            encoding: "base64",
        },
    }];
    let pages = SolanaRpcRootPageBatchV1 {
        asserted_commitment: SolanaRpcCommitmentV1::Finalized,
        context_slot: spec.slot,
        accounts: &accounts,
    };
    ingest_finalized_rpc_block_v1(
        state,
        &DepositRpcBindingV1::new(LEGACY_PROGRAM).unwrap(),
        &[RootPageAddressBindingV1 {
            page_number: 0,
            address: page_address_bytes,
        }],
        &block,
        Some(&pages),
        viewing_secret,
        local_keys,
    )
    .unwrap()
}

fn forest_state(deployment_domain: [u8; 32]) -> LaneForestDurableStateV2 {
    let program = Pubkey::new_from_array(FOREST_PROGRAM);
    let mint = Pubkey::new_from_array([0xb2; 32]);
    let master = pool_v1_pair_forest_master_address(&program, &mint).0;
    let master_value = PoolV1PairForestMasterV1 {
        identity: PoolIdentityV1 {
            pool: master.to_bytes(),
            asset_mint: mint.to_bytes(),
            token_program: [0xb3; 32],
            asset_id: M31(4),
            deployment_domain,
        },
        verifier_policy: VerifierPolicyV1 {
            flags: 1,
            registry_program: [0xb5; 32],
            registry_authority: [0; 32],
            policy_binding: [0xb6; 32],
        },
        initialized_lane_mask: POOL_V1_PAIR_FOREST_ALL_LANES_MASK,
        has_checkpoint: false,
        next_checkpoint_sequence: 0,
        last_checkpoint_lane_sequences: [0; 8],
    };
    let master_image = encode_pool_v1_pair_forest_master_v1(&master_value).unwrap();
    let lanes = (0..8u8)
        .map(|lane_id| {
            let address = pool_v1_pair_forest_lane_address(&program, &master, lane_id)
                .unwrap()
                .0;
            let value = PoolV1PairForestLaneStateV1 {
                master: master.to_bytes(),
                lane_id,
                tree: IncrementalMerkleTreeV1 {
                    next_leaf_index: 0,
                    root: POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH],
                    frontier: core::array::from_fn(|level| POOL_V1_PAIR_EMPTY_ROOTS[level]),
                },
            };
            (
                address.to_bytes(),
                encode_pool_v1_pair_forest_lane_state_v1(&value, &POOL_V1_PAIR_EMPTY_ROOTS)
                    .unwrap()
                    .to_vec(),
            )
        })
        .collect::<Vec<_>>();
    LaneForestDurableStateV2::from_authenticated_accounts_v2(
        program.to_bytes(),
        master.to_bytes(),
        &master_image,
        &lanes,
        None,
    )
    .unwrap()
}

fn append_lane_deposit(
    state: &mut LaneForestDurableStateV2,
    event_id: DepositEventIdV1,
    note: &NoteOpeningV1,
    viewing_public: &ViewingPublicKeyV1,
    viewing_secret: Option<&ViewingSecretKeyV1>,
) {
    let commitment = recompute_note_commitment_v1(note).unwrap();
    let lane_id = LaneIdV2::new(commitment[0] & 7).unwrap();
    let pair_leaf =
        PoolV1PairLeafWitnessV1::single_output(decode_digest_canonical(&commitment).unwrap())
            .unwrap()
            .leaf_digest()
            .unwrap();
    let pair_leaf_index = state.lane(lane_id).0.value.tree.next_leaf_index;
    let context = NoteContextV1::new(
        state.master().address,
        state.master().value.identity.deployment_domain,
        pair_leaf_index,
        commitment,
    )
    .unwrap();
    let payload =
        encrypt_note_v1(&mut IncrementingRng(0x40), viewing_public, &context, note).unwrap();
    let current = *state.lane(lane_id).0;
    let next_tree = current
        .value
        .tree
        .append_one_with_empty_roots(pair_leaf, &POOL_V1_PAIR_EMPTY_ROOTS)
        .unwrap()
        .0;
    let next_lane = PoolV1PairForestLaneStateV1 {
        tree: next_tree,
        ..current.value
    };
    let event = ForestFinalizedAppendEventV2 {
        master: state.master().address,
        lane_id,
        pair_leaf_index,
        root_sequence: pair_leaf_index + 1,
        after_lane_address: current.address,
        after_lane_image: encode_pool_v1_pair_forest_lane_state_v1(
            &next_lane,
            &POOL_V1_PAIR_EMPTY_ROOTS,
        )
        .unwrap(),
        kind: ForestFinalizedAppendKindV2::Deposit {
            event_id,
            commitment,
            encrypted_note: Some(payload),
        },
    };
    let associations = state
        .ingest_finalized_append_v2(event, viewing_secret)
        .unwrap();
    if viewing_secret.is_some() {
        assert!(matches!(
            associations.as_slice(),
            [association]
                if matches!(association.outcome, ForestNoteAssociationOutcomeV2::Recovered(_))
        ));
    }
}

fn finalized_terminal_observation_without_notes(
    state: &LaneForestDurableStateV2,
    block: FinalizedBlockV1,
    transaction_signature: [u8; 64],
) -> FinalizedPairForestTerminalObservationV2 {
    let (nullifier, lane_id) = (1u32..10_000)
        .find_map(|seed| {
            let nullifier = digest(0x9a00 + seed);
            let lane_id = LaneIdV2::new(encode_digest_canonical(&nullifier)[0] & 7).unwrap();
            (state.lane(lane_id).0.value.tree.next_leaf_index == 0).then_some((nullifier, lane_id))
        })
        .expect("fixture retains at least one empty output lane");
    let recipient = digest(0x9b01);
    let change = digest(0x9b02);
    let public = PoolV1PrivateTransferPublicV1 {
        pool: state.master().address,
        deployment_domain: state.master().value.identity.deployment_domain,
        anchor_sequence: 0,
        anchor_root: digest(0x9b03),
        nullifier,
        asset_id: state.master().value.identity.asset_id,
        recipient_commitment: recipient,
        change_commitment: change,
    };
    let request = PoolV1PairForestTerminalRequestV1 {
        verifier_profile: [0x91; 32],
        verifier_release: [0x92; 32],
        pool_program: *state.program_id(),
        public: PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public),
    };
    let (lane, _) = state.lane(lane_id);
    let pair_leaf = PoolV1PairLeafWitnessV1::two_outputs(recipient, change)
        .unwrap()
        .leaf_digest()
        .unwrap();
    let next = lane
        .value
        .tree
        .append_one_with_empty_roots(pair_leaf, &POOL_V1_PAIR_EMPTY_ROOTS)
        .unwrap()
        .0;
    let result = PoolV1PairForestTerminalResultV1 {
        transition_kind: PoolV1TransitionKind::PrivateTransfer,
        master_account: state.master().address,
        selected_lane_account: lane.address,
        output_lane: lane_id.as_u8(),
        nullifier,
        verified_afterstate: PoolV1PairVerifiedAfterstateV1 {
            next_pair_index: next.next_leaf_index,
            next_root: next.root,
            next_frontier: next.frontier,
        },
    };
    let mut page = RootHistoryPageV1::genesis(
        lane.address,
        POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH],
    );
    page.push(next.next_leaf_index, next.root).unwrap();
    let cursor = canonical_lane_root_page_cursor_v2(
        *state.program_id(),
        state.master().address,
        lane_id,
        next.next_leaf_index,
    )
    .unwrap();
    FinalizedPairForestTerminalObservationV2 {
        asserted_commitment: SolanaRpcCommitmentV1::Finalized,
        accounts_asserted_commitment: SolanaRpcCommitmentV1::Finalized,
        block,
        account_context_slot: block.point().slot(),
        transaction_signature,
        transaction_succeeded: true,
        instruction_index: 2,
        top_level_instruction_count: 3,
        instruction_program: *state.program_id(),
        instruction_bytes: encode_pool_v1_pair_forest_terminal_request_v1(&request)
            .unwrap()
            .to_vec(),
        return_data_program: *state.program_id(),
        return_data: encode_pool_v1_pair_forest_terminal_result_v1(&result)
            .unwrap()
            .to_vec(),
        root_page: FinalizedForestRootPageV2 {
            lane_id,
            page_number: cursor.page_number,
            account: FinalizedForestAccountV2 {
                address: cursor.address,
                owner: *state.program_id(),
                executable: false,
                data: page.encode().unwrap().to_vec(),
            },
        },
    }
}

fn append_lane_private_transfer(
    state: &mut LaneForestDurableStateV2,
    recipient_event_id: DepositEventIdV1,
    change_event_id: DepositEventIdV1,
    nullifier: [u8; 32],
    recipient_commitment: [u8; 32],
    change_commitment: [u8; 32],
) {
    let lane_id = LaneIdV2::new(nullifier[0] & 7).unwrap();
    let pair_leaf = PoolV1PairLeafWitnessV1::two_outputs(
        decode_digest_canonical(&recipient_commitment).unwrap(),
        decode_digest_canonical(&change_commitment).unwrap(),
    )
    .unwrap()
    .leaf_digest()
    .unwrap();
    let current = *state.lane(lane_id).0;
    let pair_leaf_index = current.value.tree.next_leaf_index;
    let next_tree = current
        .value
        .tree
        .append_one_with_empty_roots(pair_leaf, &POOL_V1_PAIR_EMPTY_ROOTS)
        .unwrap()
        .0;
    let next_lane = PoolV1PairForestLaneStateV1 {
        tree: next_tree,
        ..current.value
    };
    let event = ForestFinalizedAppendEventV2 {
        master: state.master().address,
        lane_id,
        pair_leaf_index,
        root_sequence: pair_leaf_index + 1,
        after_lane_address: current.address,
        after_lane_image: encode_pool_v1_pair_forest_lane_state_v1(
            &next_lane,
            &POOL_V1_PAIR_EMPTY_ROOTS,
        )
        .unwrap(),
        kind: ForestFinalizedAppendKindV2::PrivateTransfer {
            recipient_event_id,
            change_event_id,
            nullifier,
            recipient_commitment,
            change_commitment,
            recipient_encrypted_note: None,
            change_encrypted_note: None,
        },
    };
    state.ingest_finalized_append_v2(event, None).unwrap();
}

fn ingest_checkpoint(
    state: &mut LaneForestDurableStateV2,
    checkpoint_point: FinalizedChainPointV1,
) {
    let checkpoint_sequence = state.master().value.next_checkpoint_sequence;
    let sequences: [u64; 8] = core::array::from_fn(|index| {
        state
            .lane(LaneIdV2::new(index as u8).unwrap())
            .0
            .value
            .tree
            .next_leaf_index
    });
    let roots: [[u8; 32]; 8] = core::array::from_fn(|index| {
        encode_digest_canonical(
            &state
                .lane(LaneIdV2::new(index as u8).unwrap())
                .0
                .value
                .tree
                .root,
        )
    });
    let checkpoint = PoolV1PairForestCheckpointV1 {
        master: state.master().address,
        deployment_domain: state.master().value.identity.deployment_domain,
        checkpoint_sequence,
        global_root: decode_digest_canonical(&lane_forest_global_root_v2(&roots).unwrap()).unwrap(),
        lane_sequences: sequences,
    };
    let program = Pubkey::new_from_array(*state.program_id());
    let master = Pubkey::new_from_array(state.master().address);
    let checkpoint_address =
        pool_v1_pair_forest_checkpoint_address(&program, &master, checkpoint_sequence)
            .0
            .to_bytes();
    let next_master = PoolV1PairForestMasterV1 {
        has_checkpoint: true,
        next_checkpoint_sequence: checkpoint_sequence + 1,
        last_checkpoint_lane_sequences: sequences,
        ..state.master().value
    };
    let lanes = (0..8)
        .map(|index| {
            let lane = state.lane(LaneIdV2::new(index).unwrap()).0;
            (lane.address, lane.image.to_vec())
        })
        .collect::<Vec<_>>();
    state
        .ingest_finalized_checkpoint_v2(
            checkpoint_point,
            state.master().address,
            &encode_pool_v1_pair_forest_master_v1(&next_master).unwrap(),
            &lanes,
            checkpoint_address,
            &encode_pool_v1_pair_forest_checkpoint_v1(&checkpoint).unwrap(),
        )
        .unwrap();
}

fn canonical_asrj(terminal: bool) -> Vec<u8> {
    const HEADER: usize = 88;
    const RECORD: usize = 576;
    let mut bytes = vec![0u8; HEADER + RECORD];
    bytes[..4].copy_from_slice(b"ASRJ");
    bytes[4] = 2;
    bytes[8..12].copy_from_slice(&1u32.to_le_bytes());
    let record = &mut bytes[HEADER..];
    record[..32].copy_from_slice(&[0x11; 32]);
    record[32..64].copy_from_slice(&[0x12; 32]);
    record[64..72].copy_from_slice(&90u64.to_le_bytes());
    record[72..104].copy_from_slice(&[0x13; 32]);
    record[104..112].copy_from_slice(&120u64.to_le_bytes());
    record[112..144].copy_from_slice(&[0x14; 32]);
    record[144..176].copy_from_slice(&[0x15; 32]);
    record[176..208].copy_from_slice(&[0x16; 32]);
    record[208..240].copy_from_slice(&[0x17; 32]);
    record[240..272].copy_from_slice(&[0x18; 32]);
    record[272..276].copy_from_slice(&1_000u32.to_le_bytes());
    record[276..284].copy_from_slice(&900u64.to_le_bytes());
    record[284..292].copy_from_slice(&5u64.to_le_bytes());
    if terminal {
        record[294] = 2;
        record[404..412].copy_from_slice(&121u64.to_le_bytes());
        record[412..416].copy_from_slice(&7u32.to_le_bytes());
        record[416..448].copy_from_slice(&[0x19; 32]);
        record[448..480].copy_from_slice(&[0x1a; 32]);
    }
    finish_asrj_checksum(&mut bytes);
    bytes
}

fn canonical_finalized_asrj(
    request_id: [u8; 32],
    point: FinalizedChainPointV1,
    transaction_signature: [u8; 64],
    provider_set_digest: [u8; 32],
) -> Vec<u8> {
    const HEADER: usize = 88;
    const RECORD: usize = 576;
    let signed_wire = [1u8, 2, 3, 4];
    let mut bytes = vec![0u8; HEADER + RECORD + signed_wire.len()];
    bytes[..4].copy_from_slice(b"ASRJ");
    bytes[4] = 2;
    bytes[8..12].copy_from_slice(&1u32.to_le_bytes());
    let record = &mut bytes[HEADER..HEADER + RECORD];
    record[..32].copy_from_slice(&request_id);
    record[32..64].copy_from_slice(&[0x12; 32]);
    record[64..72].copy_from_slice(&90u64.to_le_bytes());
    record[72..104].copy_from_slice(&[0x13; 32]);
    record[104..112].copy_from_slice(&120u64.to_le_bytes());
    record[112..144].copy_from_slice(&[0x14; 32]);
    record[144..176].copy_from_slice(&[0x15; 32]);
    record[176..208].copy_from_slice(&[0x16; 32]);
    record[208..240].copy_from_slice(&[0x17; 32]);
    record[240..272].copy_from_slice(&[0x18; 32]);
    record[272..276].copy_from_slice(&1_000u32.to_le_bytes());
    record[276..284].copy_from_slice(&900u64.to_le_bytes());
    record[284..292].copy_from_slice(&5u64.to_le_bytes());
    record[292] = 1;
    record[294] = 1;
    record[296..360].copy_from_slice(&transaction_signature);
    record[360..364].copy_from_slice(&(signed_wire.len() as u32).to_le_bytes());
    record[404..412].copy_from_slice(&point.slot().to_le_bytes());
    record[412..444].copy_from_slice(point.block_hash());
    record[444..452].copy_from_slice(&5u64.to_le_bytes());
    record[452..460].copy_from_slice(&850u64.to_le_bytes());
    record[460..492].copy_from_slice(&[0x19; 32]);
    record[492..524].copy_from_slice(&[0x1a; 32]);
    record[524..556].copy_from_slice(&provider_set_digest);
    bytes[HEADER + RECORD..].copy_from_slice(&signed_wire);
    finish_asrj_checksum(&mut bytes);
    bytes
}

fn finish_asrj_checksum(bytes: &mut [u8]) {
    let mut hasher = Sha256::new();
    hasher.update(ASRJ_CHECKSUM_DOMAIN);
    hasher.update((bytes.len() as u64).to_le_bytes());
    hasher.update(&bytes[..56]);
    hasher.update([0u8; 32]);
    hasher.update(&bytes[88..]);
    bytes[56..88].copy_from_slice(&hasher.finalize());
}

struct Fixture {
    directory: TestDirectory,
    wallet: DurableWalletStateV1,
    witness: DurableWalletWitnessStateV1,
    relayer_admission: DurableRelayerStateV1,
    relayer_execution: DurableRelayerExecutionJournalV1,
    lane_file: DurableLaneForestWalletFileV2,
    cipher: NoteStoreCipherV1,
    initial_scan: ScanStateV1,
    initial_witness: WalletWitnessStateV1,
    candidate_scan: ScanStateV1,
    ingest_result: FinalizedBlockIngestResultV1,
    event_id: DepositEventIdV1,
    asrj_image: Vec<u8>,
}

fn fixture(
    label: &str,
    track_lane_note: bool,
    checkpoint_point: FinalizedChainPointV1,
    forest_deployment: [u8; 32],
    terminal_relayer: bool,
) -> Fixture {
    let directory = TestDirectory::new(label);
    let cipher = NoteStoreCipherV1::from_key_bytes([0x71; 32]).unwrap();
    let initial_witness = WalletWitnessStateV1::empty();
    let initial_scan = ScanStateV1::new(
        identity(),
        point(100, 0xa0),
        0,
        encode_digest_canonical(&initial_witness.tree().root),
    )
    .unwrap();
    let mut wallet = DurableWalletStateV1::open_or_create_v1(
        directory.path("wallet.asdw"),
        initial_scan.clone(),
        cipher.cipher_id(),
    )
    .unwrap();
    let mut witness = DurableWalletWitnessStateV1::open_or_create_v1(
        directory.path("witness.aswj"),
        &initial_scan,
        initial_witness.clone(),
    )
    .unwrap();
    let nullifier_key = encode_digest_canonical(&digest(700));
    let owner_key = encode_digest_canonical(&derive_owner_key(
        &decode_digest_canonical(&nullifier_key).unwrap(),
    ));
    let local_keys = LocalKeys {
        owner_key,
        nullifier_key,
    };
    let note = NoteOpeningV1::new(owner_key, 77, 4, encode_digest_canonical(&digest(701))).unwrap();
    let (viewing_secret, viewing_public) = derive_viewing_keypair_v1(&[0x51; 32]).unwrap();
    let mut candidate_scan = initial_scan.clone();
    let (ingest_result, _) = ingest_one_finalized_deposit(
        &mut candidate_scan,
        &note,
        &viewing_public,
        &viewing_secret,
        &local_keys,
        initial_witness.tree(),
    );
    assert!(matches!(
        ingest_result.deposit_outcomes(),
        [DepositScanOutcomeV1::Spendable(_)]
    ));
    let event_id = ingest_result.deposit_event_ids()[0];
    let sealed = seal_recovered_note_v1(
        &mut IncrementingRng(0x60),
        &cipher,
        event_id,
        SealedNoteAccessV1::Spendable,
        &note,
    )
    .unwrap();
    wallet
        .commit_finalized_ingest_v1(
            candidate_scan.clone(),
            &ingest_result,
            &[sealed],
            &[],
            &EncryptedLocalSpendAuthenticatorV1::new(&cipher, &local_keys),
        )
        .unwrap();
    witness
        .commit_finalized_ingest_v1(&initial_scan, &candidate_scan, &ingest_result, &[event_id])
        .unwrap();

    let mut lane_state = forest_state(forest_deployment);
    append_lane_deposit(
        &mut lane_state,
        event_id,
        &note,
        &viewing_public,
        track_lane_note.then_some(&viewing_secret),
    );
    ingest_checkpoint(&mut lane_state, checkpoint_point);
    let lane_file =
        DurableLaneForestWalletFileV2::open_or_create_v2(directory.path("forest.asd8"), lane_state)
            .unwrap();
    let relayer_admission = DurableRelayerStateV1::open_or_create_v1(
        directory.path("admission.asrq"),
        relayer_policy(),
    )
    .unwrap();
    let asrj_image = canonical_asrj(terminal_relayer);
    let relayer_path = directory.path("execution.asrj");
    fs::write(&relayer_path, &asrj_image).unwrap();
    #[cfg(unix)]
    fs::set_permissions(&relayer_path, fs::Permissions::from_mode(0o600)).unwrap();
    let relayer_execution =
        DurableRelayerExecutionJournalV1::open_or_create_v1(relayer_path).unwrap();

    Fixture {
        directory,
        wallet,
        witness,
        relayer_admission,
        relayer_execution,
        lane_file,
        cipher,
        initial_scan,
        initial_witness,
        candidate_scan,
        ingest_result,
        event_id,
        asrj_image,
    }
}

fn migrate(
    fixture: &Fixture,
    cipher: &NoteStoreCipherV1,
) -> Result<PopulatedWalletMigrationV2, PopulatedWalletMigrationErrorV2> {
    PopulatedWalletMigrationV2::from_locked_v1(
        &fixture.wallet,
        &fixture.witness,
        &fixture.relayer_admission,
        &fixture.relayer_execution,
        &fixture.lane_file,
        cipher,
        &NeverAuthorize,
        &ApproveTopology,
    )
}

#[test]
fn populated_sources_validate_and_exact_replay_is_stable() {
    let fixture = fixture("clean", true, point(101, 0xa1), [0xb4; 32], true);
    assert_eq!(fixture.relayer_execution.records().len(), 1);
    assert!(matches!(
        fixture.relayer_execution.records()[0].outcome,
        Some(RelayerExecutionOutcomeV1::TerminalFailure(_))
    ));
    let before = [
        fs::read(fixture.directory.path("wallet.asdw")).unwrap(),
        fs::read(fixture.directory.path("witness.aswj")).unwrap(),
        fs::read(fixture.directory.path("forest.asd8")).unwrap(),
        fs::read(fixture.directory.path("admission.asrq")).unwrap(),
        fs::read(fixture.directory.path("execution.asrj")).unwrap(),
    ];

    let first = migrate(&fixture, &fixture.cipher).unwrap();
    let second = migrate(&fixture, &fixture.cipher).unwrap();
    assert_eq!(first, second);
    assert_eq!(first.finalized_head(), point(101, 0xa1));
    assert_eq!(first.notes().len(), 1);
    assert_eq!(first.notes()[0].event_id, fixture.event_id);
    assert_eq!(first.relayer_execution_archive(), fixture.asrj_image);
    assert_eq!(
        first
            .source_descriptors()
            .iter()
            .map(|source| source.role())
            .collect::<Vec<_>>(),
        vec![
            WalletMigrationSourceRoleV2::Wallet,
            WalletMigrationSourceRoleV2::Witness,
            WalletMigrationSourceRoleV2::LaneForest,
            WalletMigrationSourceRoleV2::RelayerAdmission,
            WalletMigrationSourceRoleV2::RelayerExecution,
        ]
    );

    assert_eq!(
        first
            .source_descriptors()
            .iter()
            .map(|source| *source.magic())
            .collect::<Vec<_>>(),
        vec![*b"ASDW", *b"ASWJ", *b"ASD8", *b"ASRQ", *b"ASRJ"]
    );
    let after = [
        fs::read(fixture.directory.path("wallet.asdw")).unwrap(),
        fs::read(fixture.directory.path("witness.aswj")).unwrap(),
        fs::read(fixture.directory.path("forest.asd8")).unwrap(),
        fs::read(fixture.directory.path("admission.asrq")).unwrap(),
        fs::read(fixture.directory.path("execution.asrj")).unwrap(),
    ];
    assert_eq!(before, after, "read-only validation mutated a source store");
}

#[test]
fn populated_v1_migration_preserves_a_finalized_note_and_finalized_spend() {
    std::thread::Builder::new()
        .name("v7-populated-finalized-spend".to_owned())
        .stack_size(16 * 1024 * 1024)
        .spawn(populated_v1_migration_finalized_spend_body)
        .unwrap()
        .join()
        .unwrap();
}

fn populated_v1_migration_finalized_spend_body() {
    let mut fixture = fixture("finalized-spend", true, point(101, 0xa1), [0xb4; 32], true);
    let unspent_wallet_image = fs::read(fixture.directory.path("wallet.asdw")).unwrap();
    let nullifier_key = encode_digest_canonical(&digest(700));
    let owner_key = encode_digest_canonical(&derive_owner_key(
        &decode_digest_canonical(&nullifier_key).unwrap(),
    ));
    let local_keys = LocalKeys {
        owner_key,
        nullifier_key,
    };
    let opening =
        NoteOpeningV1::new(owner_key, 77, 4, encode_digest_canonical(&digest(701))).unwrap();
    let nullifier_bytes = derive_note_nullifier_v1(&opening, &nullifier_key).unwrap();
    let nullifier = decode_digest_canonical(&nullifier_bytes).unwrap();
    let recipient_commitment = digest(901);
    let change_commitment = digest(902);
    let current_tree = fixture.witness.current_state().tree();
    assert_eq!(current_tree.next_leaf_index, 1);
    let (intermediate_tree, _) = current_tree.append_one(recipient_commitment).unwrap();
    let (final_tree, _) = intermediate_tree.append_one(change_commitment).unwrap();
    let transfer = PrivateTransferBlockSpec {
        slot: 102,
        block_hash_byte: 0xa2,
        parent_slot: 101,
        parent_hash_byte: 0xa1,
        signature_byte: 0x42,
        envelope: HistoricalAnchorEnvelopeV1 {
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            pool: *identity().pool(),
            deployment_domain: *identity().deployment_domain(),
            anchor_sequence: 1,
            anchor_root: current_tree.root,
            nullifier,
            verifier_profile: [0x81; 32],
            verifier_release: [0x82; 32],
        },
        statement: PrivateTransferStatementV1 {
            pool: *identity().pool(),
            deployment_domain: *identity().deployment_domain(),
            anchor_sequence: 1,
            anchor_root: current_tree.root,
            nullifier,
            asset_id: M31(identity().asset_id()),
            recipient_commitment,
            change_commitment,
        },
        first_leaf_index: 1,
        intermediate_root: intermediate_tree.root,
        final_root: final_tree.root,
        history_roots: vec![
            fixture.initial_witness.tree().root,
            current_tree.root,
            intermediate_tree.root,
            final_tree.root,
        ],
    };
    let previous_scan = fixture.wallet.scan_state().clone();
    let mut candidate_scan = previous_scan.clone();
    let result = ingest_finalized_private_transfer(
        &mut candidate_scan,
        &transfer,
        &derive_viewing_keypair_v1(&[0x51; 32]).unwrap().0,
        &local_keys,
    );
    let output_ids = result.transition_evidence()[0].output_ids.clone();
    let spend = AuthenticatedSpentNoteUpdateV1 {
        input_event_id: fixture.event_id,
        transition_output_id: output_ids[0],
        nullifier: nullifier_bytes,
    };
    fixture
        .wallet
        .commit_finalized_ingest_v1(
            candidate_scan.clone(),
            &result,
            &[],
            &[spend],
            &EncryptedLocalSpendAuthenticatorV1::new(&fixture.cipher, &local_keys),
        )
        .unwrap();
    fixture
        .witness
        .commit_finalized_ingest_v1(&previous_scan, &candidate_scan, &result, &[])
        .unwrap();

    let mut lane_state = fixture.lane_file.state().clone();
    append_lane_private_transfer(
        &mut lane_state,
        output_ids[0],
        output_ids[1],
        nullifier_bytes,
        encode_digest_canonical(&recipient_commitment),
        encode_digest_canonical(&change_commitment),
    );
    ingest_checkpoint(&mut lane_state, point(102, 0xa2));
    fixture.lane_file.replace_state_v2(lane_state).unwrap();

    let migrated = PopulatedWalletMigrationV2::from_locked_v1(
        &fixture.wallet,
        &fixture.witness,
        &fixture.relayer_admission,
        &fixture.relayer_execution,
        &fixture.lane_file,
        &fixture.cipher,
        &EncryptedLocalSpendAuthenticatorV1::new(&fixture.cipher, &local_keys),
        &ApproveTopology,
    )
    .unwrap();
    assert_eq!(migrated.finalized_head(), point(102, 0xa2));
    assert_eq!(migrated.notes().len(), 1);
    assert_eq!(migrated.notes()[0].event_id, fixture.event_id);
    assert_eq!(
        migrated.notes()[0].spent,
        Some(aspis_pool_wallet_v1::durable_state::SpentNoteMarkerV1 {
            transition_output_id: output_ids[0],
            nullifier: nullifier_bytes,
        })
    );

    let target_path = fixture.directory.path("wallet.asl2");
    let wallet_path = fixture.directory.path("wallet.asdw");
    let initial_scan = fixture.initial_scan.clone();
    let mut monotonic = SharedMonotonicStore::default();
    let mut faults = NoWalletStoreMigrationFaultsV2;
    let receipt = migrate_locked_legacy_wallet_to_asl2_v2(
        LockedLegacyWalletStoresV2 {
            wallet: fixture.wallet,
            witness: fixture.witness,
            lane_forest: fixture.lane_file,
            relayer_admission: fixture.relayer_admission,
            relayer_execution: fixture.relayer_execution,
        },
        &target_path,
        &fixture.cipher,
        &EncryptedLocalSpendAuthenticatorV1::new(&fixture.cipher, &local_keys),
        &ApproveTopology,
        [0xd5; 32],
        &mut monotonic,
        &mut faults,
    )
    .unwrap();
    assert_eq!(receipt.phase(), WalletStoreMigrationPhaseV2::LegacyRetired);
    let target_image = fs::read(&target_path).unwrap();
    let activation =
        validated_protected_activation_from_image_v2(&target_image, &fixture.cipher).unwrap();
    let coordinator = LaneForestWalletTxnCoordinatorV2::open_or_create_protected_v2(
        &target_path,
        activation,
        &fixture.cipher,
        [0xd5; 32],
        Box::new(monotonic),
    )
    .unwrap();
    assert!(coordinator.committed_state().unwrap().notes()[0].is_spent());
    assert_eq!(
        coordinator
            .committed_state()
            .unwrap()
            .spendable_unspent_notes_v2()
            .count(),
        0
    );
    drop(coordinator);

    // Rolling back only the retired local V1 note store to the exact pre-spend
    // image cannot reopen a writer because ASMG remains authoritative.
    fs::write(&wallet_path, unspent_wallet_image).unwrap();
    #[cfg(unix)]
    fs::set_permissions(&wallet_path, fs::Permissions::from_mode(0o600)).unwrap();
    assert_eq!(
        DurableWalletStateV1::open_or_create_v1(
            wallet_path,
            initial_scan,
            fixture.cipher.cipher_id(),
        )
        .err(),
        Some(DurableStateErrorV1::LegacyStoreRetired)
    );
}

#[test]
fn threaded_scanner_cannot_open_while_migration_holds_the_legacy_cutover_locks() {
    let Fixture {
        directory,
        wallet,
        witness,
        relayer_admission,
        relayer_execution,
        lane_file,
        cipher,
        initial_scan,
        ..
    } = fixture(
        "threaded-exclusion",
        true,
        point(101, 0xa1),
        [0xb4; 32],
        true,
    );
    let wallet_path = directory.path("wallet.asdw");
    let target_path = directory.path("wallet.asl2");
    let cipher_id = cipher.cipher_id();
    let (entered_tx, entered_rx) = std::sync::mpsc::sync_channel(0);
    let (release_tx, release_rx) = std::sync::mpsc::sync_channel(0);
    let mut faults = PauseBeforeJournalPrepare {
        entered: entered_tx,
        release: release_rx,
        paused: false,
    };

    std::thread::scope(|scope| {
        let migration = scope.spawn(move || {
            let mut monotonic = SharedMonotonicStore::default();
            migrate_locked_legacy_wallet_to_asl2_v2(
                LockedLegacyWalletStoresV2 {
                    wallet,
                    witness,
                    lane_forest: lane_file,
                    relayer_admission,
                    relayer_execution,
                },
                target_path,
                &cipher,
                &NeverAuthorize,
                &ApproveTopology,
                [0xd4; 32],
                &mut monotonic,
                &mut faults,
            )
        });
        entered_rx.recv().unwrap();
        let concurrent_error =
            DurableWalletStateV1::open_or_create_v1(&wallet_path, initial_scan, cipher_id).err();
        release_tx.send(()).unwrap();
        assert_eq!(
            migration.join().unwrap().unwrap().phase(),
            WalletStoreMigrationPhaseV2::LegacyRetired
        );
        assert_eq!(
            concurrent_error,
            Some(DurableStateErrorV1::MigrationInProgress)
        );
    });
}

#[test]
fn populated_handoff_is_one_way_recoverable_and_activation_stays_explicit() {
    std::thread::Builder::new()
        .name("v7-populated-handoff".to_owned())
        .stack_size(16 * 1024 * 1024)
        .spawn(populated_handoff_body)
        .unwrap()
        .join()
        .unwrap();
}

fn populated_handoff_body() {
    let Fixture {
        directory,
        wallet,
        witness,
        relayer_admission,
        relayer_execution,
        lane_file,
        cipher,
        initial_scan,
        initial_witness,
        ..
    } = fixture("handoff", true, point(101, 0xa1), [0xb4; 32], true);
    let source_paths = [
        (
            WalletStoreSourceRoleV2::WalletState,
            directory.path("wallet.asdw"),
        ),
        (
            WalletStoreSourceRoleV2::WitnessState,
            directory.path("witness.aswj"),
        ),
        (
            WalletStoreSourceRoleV2::LaneForestState,
            directory.path("forest.asd8"),
        ),
        (
            WalletStoreSourceRoleV2::RelayerAdmissionState,
            directory.path("admission.asrq"),
        ),
        (
            WalletStoreSourceRoleV2::RelayerExecutionJournal,
            directory.path("execution.asrj"),
        ),
    ];
    let authority_path = wallet_store_migration_authority_path_v2(&source_paths[0].1).unwrap();
    let target_path = directory.path("wallet.asl2");
    let protection_id = [0xd1; 32];
    let mut monotonic = SharedMonotonicStore::default();
    let mut faults = NoWalletStoreMigrationFaultsV2;
    let receipt = migrate_locked_legacy_wallet_to_asl2_v2(
        LockedLegacyWalletStoresV2 {
            wallet,
            witness,
            lane_forest: lane_file,
            relayer_admission,
            relayer_execution,
        },
        &target_path,
        &cipher,
        &NeverAuthorize,
        &ApproveTopology,
        protection_id,
        &mut monotonic,
        &mut faults,
    )
    .unwrap();
    assert_eq!(receipt.phase(), WalletStoreMigrationPhaseV2::LegacyRetired);
    for (_, path) in &source_paths {
        assert_eq!(
            &fs::read(path).unwrap()[..4],
            &WALLET_STORE_RETIREMENT_MAGIC_V2
        );
    }

    let replay = recover_populated_wallet_handoff_v2(
        &authority_path,
        &target_path,
        &source_paths,
        &cipher,
        protection_id,
        &mut monotonic,
        &mut faults,
    )
    .unwrap();
    assert_eq!(replay, receipt);

    // Every managed legacy constructor is fenced by ASMG/ASRT after handoff.
    assert!(matches!(
        DurableWalletStateV1::open_or_create_v1(
            &source_paths[0].1,
            initial_scan.clone(),
            cipher.cipher_id(),
        ),
        Err(DurableStateErrorV1::LegacyStoreRetired)
    ));
    assert!(matches!(
        DurableWalletWitnessStateV1::open_or_create_v1(
            &source_paths[1].1,
            &initial_scan,
            initial_witness,
        ),
        Err(DurableWitnessErrorV1::Durable(
            DurableStateErrorV1::LegacyStoreRetired
        ))
    ));
    assert!(matches!(
        DurableLaneForestWalletFileV2::open_or_create_v2(
            &source_paths[2].1,
            forest_state([0xb4; 32]),
        ),
        Err(LaneForestDurableErrorV2::Durable(
            DurableStateErrorV1::LegacyStoreRetired
        ))
    ));
    assert!(matches!(
        DurableRelayerStateV1::open_or_create_v1(&source_paths[3].1, relayer_policy()),
        Err(DurableStateErrorV1::LegacyStoreRetired)
    ));
    assert!(matches!(
        DurableRelayerExecutionJournalV1::open_or_create_v1(&source_paths[4].1),
        Err(RelayerExecutionJournalErrorV1::Durable(
            DurableStateErrorV1::LegacyStoreRetired
        ))
    ));

    let target_bytes = fs::read(&target_path).unwrap();
    let activation = validated_protected_activation_from_image_v2(&target_bytes, &cipher).unwrap();
    let old_target_image = target_bytes.clone();
    let mut coordinator = LaneForestWalletTxnCoordinatorV2::open_or_create_protected_v2(
        &target_path,
        activation.clone(),
        &cipher,
        protection_id,
        Box::new(monotonic.clone()),
    )
    .unwrap();
    coordinator
        .externally_anchored_monotonic_commitment_v2()
        .unwrap();
    assert!(matches!(
        coordinator.production_monotonic_qualification_v2(),
        Err(LaneForestWalletTxnErrorV2::MonotonicRequired)
    ));
    let startup = [0xe1; 32];
    let provider = [0xe2; 32];
    let finality = [0xe3; 32];
    assert_eq!(
        WalletV2ActivationPrerequisites::from_authoritative_state_v2(
        &coordinator,
        receipt,
        vec![startup],
        vec![provider],
        vec![finality],
    ),
        Err(aspis_pool_wallet_v1::wallet_v2_activation::WalletV2ActivationError::MonotonicUnqualified)
    );

    #[cfg(feature = "wallet-v2-reference-tests")]
    let (runtime_mode, runtime_permit, runtime_policy) = {
        let reference_service = [0xe4; 32];
        let prerequisites =
            WalletV2ActivationPrerequisites::from_authoritative_state_reference_only_v2(
                &coordinator,
                receipt,
                reference_service,
                vec![startup],
                vec![provider],
                vec![finality],
            )
            .unwrap();
        let config = WalletV2ProductionConfig::new_v2(
            *activation.wallet_identity_sha256(),
            *activation.note_cipher_id(),
            *activation.migration_genesis().unwrap().migration_id(),
            *receipt.migration_id(),
            *receipt.target_digest(),
            *receipt.target_path_digest(),
            protection_id,
            reference_service,
            startup,
            provider,
            finality,
        )
        .unwrap();
        let mode = WalletV2ActivationMode::ReferenceOnly(config);
        let permit = evaluate_wallet_v2_activation(&mode, &prerequisites).unwrap();
        let policy = WalletV2RuntimePolicyBindings::reference_only_v2(
            startup,
            provider,
            finality,
            reference_service,
        )
        .unwrap();
        (mode, permit, policy)
    };

    let genesis_commitment = coordinator
        .current_monotonic_commitment_v2()
        .unwrap()
        .unwrap();
    let mut parent = point(101, 0xa1);
    let mut forged_successor_image = None;
    for (offset, boundary) in [
        LaneForestWalletTxnAtomicBoundaryV2::TargetRename,
        LaneForestWalletTxnAtomicBoundaryV2::TemporaryWrite,
        LaneForestWalletTxnAtomicBoundaryV2::TemporaryFileSync,
        LaneForestWalletTxnAtomicBoundaryV2::ParentDirectorySync,
    ]
    .into_iter()
    .enumerate()
    {
        let next = point(102 + offset as u64, 0xa2 + offset as u8);
        let empty = LaneForestWalletEmptyFinalizedBlockV2::new_v2(
            FinalizedBlockV1::new(next, parent).unwrap(),
            [0xf1; 32],
            startup,
            provider,
        )
        .unwrap();
        let mut atomic_fault = StopAtAsl2AtomicBoundary {
            boundary,
            fired: false,
        };
        assert!(coordinator
            .prepare_empty_finalized_block_with_faults_v2(empty, &mut atomic_fault)
            .is_err());
        assert!(atomic_fault.fired);
        if boundary == LaneForestWalletTxnAtomicBoundaryV2::TargetRename {
            forged_successor_image = Some(fs::read(&target_path).unwrap());
        }
        drop(coordinator);
        coordinator = LaneForestWalletTxnCoordinatorV2::open_or_create_protected_v2(
            &target_path,
            activation.clone(),
            &cipher,
            protection_id,
            Box::new(monotonic.clone()),
        )
        .unwrap();
        coordinator.prepare_empty_finalized_block_v2(empty).unwrap();
        coordinator.recover_to_committed_v2().unwrap();
        assert_eq!(
            coordinator.committed_state().unwrap().finalized_head(),
            next
        );
        parent = next;
    }

    // A checksummed successor copied without its exact external preparation is
    // rejected even though its generation and predecessor are structurally
    // valid.
    let mut forged_anchor = FaultInjectableWalletMonotonicStoreV2::new_v2();
    let genesis_preparation = WalletMonotonicPreparedNextV2::new_v2(
        None,
        genesis_commitment,
        [0x71; 32],
        *activation.wallet_identity_sha256(),
        *activation.activation_id(),
        protection_id,
        *activation.note_cipher_id(),
        [0x72; 32],
    )
    .unwrap();
    forged_anchor
        .compare_and_prepare_next_v2(genesis_preparation)
        .unwrap();
    forged_anchor
        .compare_and_commit_prepared_v2(genesis_preparation)
        .unwrap();
    let forged_path = directory.path("forged-ahead.asl2");
    fs::write(&forged_path, forged_successor_image.unwrap()).unwrap();
    #[cfg(unix)]
    fs::set_permissions(&forged_path, fs::Permissions::from_mode(0o600)).unwrap();
    assert_eq!(
        LaneForestWalletTxnCoordinatorV2::open_or_create_protected_v2(
            &forged_path,
            activation.clone(),
            &cipher,
            protection_id,
            Box::new(forged_anchor),
        )
        .err(),
        Some(LaneForestWalletTxnErrorV2::MonotonicRollback)
    );

    // Once the externally anchored generation advances, restoring the exact
    // old populated image (which would also restore its note/spend/cursor
    // state) is rejected deterministically on every reopen.
    let empty = LaneForestWalletEmptyFinalizedBlockV2::new_v2(
        FinalizedBlockV1::new(point(106, 0xa6), parent).unwrap(),
        [0xf1; 32],
        startup,
        provider,
    )
    .unwrap();
    #[cfg(not(feature = "wallet-v2-reference-tests"))]
    {
        coordinator.prepare_empty_finalized_block_v2(empty).unwrap();
        coordinator.recover_to_committed_v2().unwrap();
        drop(coordinator);
    }
    #[cfg(feature = "wallet-v2-reference-tests")]
    {
        drop(coordinator);
        let preflight_image = fs::read(&target_path).unwrap();
        assert!(matches!(
            ActivatedWalletRuntimeV2::start_v2(
                &target_path,
                activation.clone(),
                &cipher,
                protection_id,
                Box::new(monotonic.clone()),
                receipt,
                &runtime_mode,
                None,
                runtime_policy,
            ),
            Err(WalletV2RuntimeError::MissingPermit)
        ));
        assert_eq!(fs::read(&target_path).unwrap(), preflight_image);
        let wrong_provider_policy = WalletV2RuntimePolicyBindings::reference_only_v2(
            startup, [0xee; 32], finality, [0xe4; 32],
        )
        .unwrap();
        assert!(ActivatedWalletRuntimeV2::start_v2(
            &target_path,
            activation.clone(),
            &cipher,
            protection_id,
            Box::new(monotonic.clone()),
            receipt,
            &runtime_mode,
            Some(&runtime_permit),
            wrong_provider_policy,
        )
        .is_err());
        assert_eq!(fs::read(&target_path).unwrap(), preflight_image);
        monotonic
            .inject_stale_current_once_v2(Some(genesis_commitment))
            .unwrap();
        assert!(ActivatedWalletRuntimeV2::start_v2(
            &target_path,
            activation.clone(),
            &cipher,
            protection_id,
            Box::new(monotonic.clone()),
            receipt,
            &runtime_mode,
            Some(&runtime_permit),
            runtime_policy,
        )
        .is_err());
        monotonic
            .inject_once_v2(WalletMonotonicFaultPointV2::CurrentRead)
            .unwrap();
        assert!(ActivatedWalletRuntimeV2::start_v2(
            &target_path,
            activation.clone(),
            &cipher,
            protection_id,
            Box::new(monotonic.clone()),
            receipt,
            &runtime_mode,
            Some(&runtime_permit),
            runtime_policy,
        )
        .is_err());

        let mut runtime = ActivatedWalletRuntimeV2::start_v2(
            &target_path,
            activation.clone(),
            &cipher,
            protection_id,
            Box::new(monotonic.clone()),
            receipt,
            &runtime_mode,
            Some(&runtime_permit),
            runtime_policy,
        )
        .unwrap();
        monotonic
            .inject_once_v2(WalletMonotonicFaultPointV2::AfterPrepare)
            .unwrap();
        assert!(runtime.apply_empty_finalized_block_v2(empty).is_err());
        drop(runtime);

        let mut runtime = ActivatedWalletRuntimeV2::start_v2(
            &target_path,
            activation.clone(),
            &cipher,
            protection_id,
            Box::new(monotonic.clone()),
            receipt,
            &runtime_mode,
            Some(&runtime_permit),
            runtime_policy,
        )
        .unwrap();
        assert_eq!(
            runtime.committed_state_v2().unwrap().finalized_head(),
            parent
        );
        monotonic
            .inject_once_v2(WalletMonotonicFaultPointV2::BeforeCommit)
            .unwrap();
        assert!(runtime.apply_empty_finalized_block_v2(empty).is_err());
        drop(runtime);

        let mut runtime = ActivatedWalletRuntimeV2::start_v2(
            &target_path,
            activation.clone(),
            &cipher,
            protection_id,
            Box::new(monotonic.clone()),
            receipt,
            &runtime_mode,
            Some(&runtime_permit),
            runtime_policy,
        )
        .unwrap();
        assert_eq!(
            runtime.committed_state_v2().unwrap().finalized_head(),
            point(106, 0xa6)
        );
        runtime.apply_empty_finalized_block_v2(empty).unwrap();

        let lost_commit_response = LaneForestWalletEmptyFinalizedBlockV2::new_v2(
            FinalizedBlockV1::new(point(107, 0xa7), point(106, 0xa6)).unwrap(),
            [0xf4; 32],
            startup,
            provider,
        )
        .unwrap();
        monotonic
            .inject_once_v2(WalletMonotonicFaultPointV2::AfterCommit)
            .unwrap();
        assert!(runtime
            .apply_empty_finalized_block_v2(lost_commit_response)
            .is_err());
        drop(runtime);

        let mut runtime = ActivatedWalletRuntimeV2::start_v2(
            &target_path,
            activation.clone(),
            &cipher,
            protection_id,
            Box::new(monotonic.clone()),
            receipt,
            &runtime_mode,
            Some(&runtime_permit),
            runtime_policy,
        )
        .unwrap();
        assert_eq!(
            runtime.committed_state_v2().unwrap().finalized_head(),
            point(107, 0xa7)
        );
        let clean = LaneForestWalletEmptyFinalizedBlockV2::new_v2(
            FinalizedBlockV1::new(point(108, 0xa8), point(107, 0xa7)).unwrap(),
            [0xf5; 32],
            startup,
            provider,
        )
        .unwrap();
        runtime.apply_empty_finalized_block_v2(clean).unwrap();

        let terminal_observation = finalized_terminal_observation_without_notes(
            runtime.committed_state_v2().unwrap().lane_state(),
            FinalizedBlockV1::new(point(109, 0xa9), point(108, 0xa8)).unwrap(),
            [0x49; 64],
        );
        let event = derive_finalized_pair_forest_terminal_event_v2(
            runtime.committed_state_v2().unwrap().lane_state(),
            &terminal_observation,
        )
        .unwrap();
        runtime
            .observe_tentative_v2(
                event.clone(),
                LaneForestWalletTentativeCommitmentV2::Confirmed,
                provider,
            )
            .unwrap();
        runtime
            .reorg_tentative_v2(&event, [0xfa; 32], provider)
            .unwrap();
        assert_eq!(
            runtime.committed_state_v2().unwrap().finalized_head(),
            point(108, 0xa8)
        );
        runtime
            .observe_tentative_v2(
                event.clone(),
                LaneForestWalletTentativeCommitmentV2::Confirmed,
                provider,
            )
            .unwrap();
        // V2 relayer execution starts in a fresh authority directory. The
        // migrated legacy directory is intentionally fenced by ASMG/ASRT and
        // cannot silently become writable again.
        let relayer_v2_directory = directory.path("v2-relayer");
        fs::create_dir(&relayer_v2_directory).unwrap();
        let request_id = [0x21; 32];
        let journal_path = relayer_v2_directory.join("exact.asrj");
        let journal_image =
            canonical_finalized_asrj(request_id, point(109, 0xa9), [0x49; 64], provider);
        fs::write(&journal_path, &journal_image).unwrap();
        #[cfg(unix)]
        fs::set_permissions(&journal_path, fs::Permissions::from_mode(0o600)).unwrap();
        let journal = DurableRelayerExecutionJournalV1::open_or_create_v1(&journal_path).unwrap();

        let before_failures = fs::read(&target_path).unwrap();
        let mut unfinalized_source = terminal_observation.clone();
        unfinalized_source.asserted_commitment = SolanaRpcCommitmentV1::Confirmed;
        assert_eq!(
            runtime
                .apply_finalized_pool_terminal_journal_v2(
                    &unfinalized_source,
                    Vec::new(),
                    Vec::new(),
                    None,
                    &journal,
                    request_id,
                    &cipher,
                    &NeverAuthorize,
                )
                .err(),
            Some(WalletV2RuntimeError::FinalizedSource(
                LaneForestRpcErrorV2::NotFinalized
            ))
        );
        assert!(matches!(
            runtime.apply_finalized_pool_terminal_journal_v2(
                &terminal_observation,
                Vec::new(),
                Vec::new(),
                None,
                &journal,
                [0xfe; 32],
                &cipher,
                &NeverAuthorize,
            ),
            Err(WalletV2RuntimeError::Transaction(
                LaneForestWalletTxnErrorV2::InvalidRelayerObservation
            ))
        ));

        let wrong_signature_path = relayer_v2_directory.join("wrong-signature.asrj");
        fs::write(
            &wrong_signature_path,
            canonical_finalized_asrj([0x22; 32], point(109, 0xa9), [0x4a; 64], provider),
        )
        .unwrap();
        #[cfg(unix)]
        fs::set_permissions(&wrong_signature_path, fs::Permissions::from_mode(0o600)).unwrap();
        let wrong_signature =
            DurableRelayerExecutionJournalV1::open_or_create_v1(&wrong_signature_path).unwrap();
        assert!(matches!(
            runtime.apply_finalized_pool_terminal_journal_v2(
                &terminal_observation,
                Vec::new(),
                Vec::new(),
                None,
                &wrong_signature,
                [0x22; 32],
                &cipher,
                &NeverAuthorize,
            ),
            Err(WalletV2RuntimeError::Transaction(
                LaneForestWalletTxnErrorV2::InvalidRelayerObservation
            ))
        ));

        let wrong_provider_path = relayer_v2_directory.join("wrong-provider.asrj");
        fs::write(
            &wrong_provider_path,
            canonical_finalized_asrj([0x23; 32], point(109, 0xa9), [0x49; 64], [0xee; 32]),
        )
        .unwrap();
        #[cfg(unix)]
        fs::set_permissions(&wrong_provider_path, fs::Permissions::from_mode(0o600)).unwrap();
        let wrong_provider =
            DurableRelayerExecutionJournalV1::open_or_create_v1(&wrong_provider_path).unwrap();
        assert_eq!(
            runtime
                .apply_finalized_pool_terminal_journal_v2(
                    &terminal_observation,
                    Vec::new(),
                    Vec::new(),
                    None,
                    &wrong_provider,
                    [0x23; 32],
                    &cipher,
                    &NeverAuthorize,
                )
                .err(),
            Some(WalletV2RuntimeError::RuntimePolicyMismatch)
        );
        assert_eq!(fs::read(&target_path).unwrap(), before_failures);

        // Model a lost runtime response after the external monotonic service
        // committed the exact ASL2 successor. Startup recovers that successor,
        // and the same immutable journal handoff then replays idempotently.
        monotonic
            .inject_once_v2(WalletMonotonicFaultPointV2::AfterCommit)
            .unwrap();
        assert!(runtime
            .apply_finalized_pool_terminal_journal_v2(
                &terminal_observation,
                Vec::new(),
                Vec::new(),
                None,
                &journal,
                request_id,
                &cipher,
                &NeverAuthorize,
            )
            .is_err());
        drop(runtime);
        assert_eq!(fs::read(&journal_path).unwrap(), journal_image);

        let mut runtime = ActivatedWalletRuntimeV2::start_v2(
            &target_path,
            activation.clone(),
            &cipher,
            protection_id,
            Box::new(monotonic.clone()),
            receipt,
            &runtime_mode,
            Some(&runtime_permit),
            runtime_policy,
        )
        .unwrap();
        assert_eq!(
            runtime.committed_state_v2().unwrap().finalized_head(),
            point(109, 0xa9)
        );
        runtime
            .apply_finalized_pool_terminal_journal_v2(
                &terminal_observation,
                Vec::new(),
                Vec::new(),
                None,
                &journal,
                request_id,
                &cipher,
                &NeverAuthorize,
            )
            .unwrap();

        // A second valid finalized journal record cannot relabel the already
        // committed Pool event with another request identity.
        let conflicting_path = relayer_v2_directory.join("conflicting-request.asrj");
        fs::write(
            &conflicting_path,
            canonical_finalized_asrj([0x24; 32], point(109, 0xa9), [0x49; 64], provider),
        )
        .unwrap();
        #[cfg(unix)]
        fs::set_permissions(&conflicting_path, fs::Permissions::from_mode(0o600)).unwrap();
        let conflicting =
            DurableRelayerExecutionJournalV1::open_or_create_v1(&conflicting_path).unwrap();
        assert!(matches!(
            runtime.apply_finalized_pool_terminal_journal_v2(
                &terminal_observation,
                Vec::new(),
                Vec::new(),
                None,
                &conflicting,
                [0x24; 32],
                &cipher,
                &NeverAuthorize,
            ),
            Err(WalletV2RuntimeError::Transaction(
                LaneForestWalletTxnErrorV2::EventConflict
            ))
        ));
        runtime.shutdown_v2().unwrap();
    }
    fs::write(&target_path, old_target_image).unwrap();
    assert!(matches!(
        LaneForestWalletTxnCoordinatorV2::open_or_create_protected_v2(
            &target_path,
            activation,
            &cipher,
            protection_id,
            Box::new(monotonic.clone()),
        ),
        Err(LaneForestWalletTxnErrorV2::MonotonicRollback)
    ));
    assert!(matches!(
        LaneForestWalletTxnCoordinatorV2::open_or_create_protected_v2(
            &target_path,
            validated_protected_activation_from_image_v2(
                &fs::read(&target_path).unwrap(),
                &cipher,
            )
            .unwrap(),
            &cipher,
            protection_id,
            Box::new(monotonic),
        ),
        Err(LaneForestWalletTxnErrorV2::MonotonicRollback)
    ));
}

#[test]
fn ownership_recovery_revalidates_target_cipher_and_monotonic_protection_before_retirement() {
    std::thread::Builder::new()
        .name("v7-ownership-recovery-guard".to_owned())
        .stack_size(16 * 1024 * 1024)
        .spawn(ownership_recovery_guard_body)
        .unwrap()
        .join()
        .unwrap();
}

fn ownership_recovery_guard_body() {
    let Fixture {
        directory,
        wallet,
        witness,
        relayer_admission,
        relayer_execution,
        lane_file,
        cipher,
        ..
    } = fixture(
        "ownership-recovery-guard",
        true,
        point(101, 0xa1),
        [0xb4; 32],
        true,
    );
    let source_paths = [
        (
            WalletStoreSourceRoleV2::WalletState,
            directory.path("wallet.asdw"),
        ),
        (
            WalletStoreSourceRoleV2::WitnessState,
            directory.path("witness.aswj"),
        ),
        (
            WalletStoreSourceRoleV2::LaneForestState,
            directory.path("forest.asd8"),
        ),
        (
            WalletStoreSourceRoleV2::RelayerAdmissionState,
            directory.path("admission.asrq"),
        ),
        (
            WalletStoreSourceRoleV2::RelayerExecutionJournal,
            directory.path("execution.asrj"),
        ),
    ];
    let source_images = source_paths
        .iter()
        .map(|(_, path)| fs::read(path).unwrap())
        .collect::<Vec<_>>();
    let authority_path = wallet_store_migration_authority_path_v2(&source_paths[0].1).unwrap();
    let target_path = directory.path("wallet.asl2");
    let protection_id = [0xd2; 32];
    let mut monotonic = SharedMonotonicStore::default();
    let mut stop = StopBeforeFirstLegacyTombstone::default();

    assert!(migrate_locked_legacy_wallet_to_asl2_v2(
        LockedLegacyWalletStoresV2 {
            wallet,
            witness,
            lane_forest: lane_file,
            relayer_admission,
            relayer_execution,
        },
        &target_path,
        &cipher,
        &NeverAuthorize,
        &ApproveTopology,
        protection_id,
        &mut monotonic,
        &mut stop,
    )
    .is_err());
    assert!(stop.fired);
    let target_image = fs::read(&target_path).unwrap();

    let assert_sources_unchanged = || {
        for ((_, path), expected) in source_paths.iter().zip(&source_images) {
            assert_eq!(&fs::read(path).unwrap(), expected);
        }
    };
    assert_sources_unchanged();

    let wrong_cipher = NoteStoreCipherV1::from_key_bytes([0x72; 32]).unwrap();
    assert!(recover_populated_wallet_handoff_v2(
        &authority_path,
        &target_path,
        &source_paths,
        &wrong_cipher,
        protection_id,
        &mut monotonic,
        &mut NoWalletStoreMigrationFaultsV2,
    )
    .is_err());
    assert_sources_unchanged();

    assert!(recover_populated_wallet_handoff_v2(
        &authority_path,
        &target_path,
        &source_paths,
        &cipher,
        [0xd3; 32],
        &mut monotonic,
        &mut NoWalletStoreMigrationFaultsV2,
    )
    .is_err());
    assert_sources_unchanged();

    fs::write(&source_paths[4].1, b"corrupt later legacy source").unwrap();
    assert!(recover_populated_wallet_handoff_v2(
        &authority_path,
        &target_path,
        &source_paths,
        &cipher,
        protection_id,
        &mut monotonic,
        &mut NoWalletStoreMigrationFaultsV2,
    )
    .is_err());
    for ((_, path), expected) in source_paths.iter().zip(&source_images).take(4) {
        assert_eq!(&fs::read(path).unwrap(), expected);
    }
    fs::write(&source_paths[4].1, &source_images[4]).unwrap();
    assert_sources_unchanged();

    fs::write(&target_path, b"corrupt ASL2 target").unwrap();
    assert!(recover_populated_wallet_handoff_v2(
        &authority_path,
        &target_path,
        &source_paths,
        &cipher,
        protection_id,
        &mut monotonic,
        &mut NoWalletStoreMigrationFaultsV2,
    )
    .is_err());
    assert_sources_unchanged();

    fs::write(&target_path, target_image).unwrap();
    let receipt = recover_populated_wallet_handoff_v2(
        &authority_path,
        &target_path,
        &source_paths,
        &cipher,
        protection_id,
        &mut monotonic,
        &mut NoWalletStoreMigrationFaultsV2,
    )
    .unwrap();
    assert_eq!(receipt.phase(), WalletStoreMigrationPhaseV2::LegacyRetired);
    let replay = recover_populated_wallet_handoff_v2(
        &authority_path,
        &target_path,
        &source_paths,
        &cipher,
        protection_id,
        &mut monotonic,
        &mut NoWalletStoreMigrationFaultsV2,
    )
    .unwrap();
    assert_eq!(replay, receipt);
}

#[test]
fn malformed_cross_store_sources_fail_closed_without_mutation() {
    let clean = fixture("negative", true, point(101, 0xa1), [0xb4; 32], true);
    let wallet_before = fs::read(clean.directory.path("wallet.asdw")).unwrap();

    let wrong_cipher = NoteStoreCipherV1::from_key_bytes([0x72; 32]).unwrap();
    assert_eq!(
        migrate(&clean, &wrong_cipher).unwrap_err(),
        PopulatedWalletMigrationErrorV2::NoteCipherMismatch
    );

    let untracked = fixture("untracked", false, point(101, 0xa1), [0xb4; 32], true);
    assert_eq!(
        migrate(&untracked, &untracked.cipher).unwrap_err(),
        PopulatedWalletMigrationErrorV2::MissingLaneWitness
    );

    let cursor = fixture("cursor", true, point(102, 0xa2), [0xb4; 32], true);
    assert_eq!(
        migrate(&cursor, &cursor.cipher).unwrap_err(),
        PopulatedWalletMigrationErrorV2::CursorMismatch
    );

    let wrong_identity = fixture("identity", true, point(101, 0xa1), [0xc4; 32], true);
    assert_eq!(
        migrate(&wrong_identity, &wrong_identity.cipher).unwrap_err(),
        PopulatedWalletMigrationErrorV2::IdentityMismatch
    );

    let unsettled = fixture("unsettled", true, point(101, 0xa1), [0xb4; 32], false);
    assert_eq!(
        migrate(&unsettled, &unsettled.cipher).unwrap_err(),
        PopulatedWalletMigrationErrorV2::RelayerExecutionNotQuiescent
    );

    let mut queued = fixture("queued", true, point(101, 0xa1), [0xb4; 32], true);
    populate_relayer_admission(&mut queued.relayer_admission);
    assert_eq!(queued.relayer_admission.entries().len(), 1);
    assert_eq!(
        migrate(&queued, &queued.cipher).unwrap_err(),
        PopulatedWalletMigrationErrorV2::RelayerAdmissionNotEmpty
    );

    let mut wrong_witness = DurableWalletWitnessStateV1::open_or_create_v1(
        clean.directory.path("wrong-tracking.aswj"),
        &clean.initial_scan,
        clean.initial_witness.clone(),
    )
    .unwrap();
    wrong_witness
        .commit_finalized_ingest_v1(
            &clean.initial_scan,
            &clean.candidate_scan,
            &clean.ingest_result,
            &[],
        )
        .unwrap();
    assert_eq!(
        PopulatedWalletMigrationV2::from_locked_v1(
            &clean.wallet,
            &wrong_witness,
            &clean.relayer_admission,
            &clean.relayer_execution,
            &clean.lane_file,
            &clean.cipher,
            &NeverAuthorize,
            &ApproveTopology,
        )
        .unwrap_err(),
        PopulatedWalletMigrationErrorV2::WitnessMismatch
    );

    let other_directory = TestDirectory::new("other-parent");
    let other_admission = DurableRelayerStateV1::open_or_create_v1(
        other_directory.path("admission.asrq"),
        relayer_policy(),
    )
    .unwrap();
    assert_eq!(
        PopulatedWalletMigrationV2::from_locked_v1(
            &clean.wallet,
            &clean.witness,
            &other_admission,
            &clean.relayer_execution,
            &clean.lane_file,
            &clean.cipher,
            &NeverAuthorize,
            &ApproveTopology,
        )
        .unwrap_err(),
        PopulatedWalletMigrationErrorV2::PathMismatch
    );

    assert_eq!(
        fs::read(clean.directory.path("wallet.asdw")).unwrap(),
        wallet_before,
        "failed validation mutated the wallet source"
    );
}
