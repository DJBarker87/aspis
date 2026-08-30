use std::{
    convert::Infallible,
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use aspis_core::field::M31;
use aspis_pool::{
    instruction::{encode_transition_receipt_v1, TransitionReceiptV1},
    pool_v1_root_page_address,
};
use aspis_pool_wallet_v1::{
    derive_viewing_keypair_v1,
    durable_state::{
        AuthenticatedSpentNoteUpdateV1, DurableStateErrorV1, DurableWalletStateV1,
        SealedNoteAccessV1, SealedRecoveredNoteV1,
    },
    durable_witness_state::{DurableWalletWitnessStateV1, DurableWitnessErrorV1},
    encrypt_note_v1,
    finalized_indexer::{
        ingest_finalized_rpc_block_v1, FinalizedBlockIngestResultV1, FinalizedIndexerErrorV1,
        RootPageAddressBindingV1, SolanaRpcBlockV1, SolanaRpcCommitmentV1,
        SolanaRpcCompiledInstructionV1, SolanaRpcEncodedBinaryV1, SolanaRpcReturnDataV1,
        SolanaRpcRootPageAccountV1, SolanaRpcRootPageBatchV1, SolanaRpcTransactionV1,
        SolanaRpcTransactionVersionV1,
    },
    note_store_crypto::{
        seal_recovered_note_v1, EncryptedLocalSpendAuthenticatorV1, LocalNullifierKeyStoreV1,
        NoteStoreCipherV1, NullifierKeyMaterialV1, POOL_V1_NOTE_STORE_SEALED_BYTES,
    },
    relayer::RelayerEnqueueOutcomeV1,
    rpc_adapter::{
        DepositRpcBindingV1, POOL_V1_DEPOSIT_INSTRUCTION_HEADER_BYTES,
        POOL_V1_DEPOSIT_INSTRUCTION_MAGIC, POOL_V1_DEPOSIT_INSTRUCTION_VERSION,
    },
    scan_state::{
        encode_deposit_event_record_v1, DepositScanIdentityV1, DepositScanOutcomeV1,
        FinalizedBlockAdvanceV1, FinalizedChainPointV1, LocalOwnerKeyStoreV1, ScanStateErrorV1,
        ScanStateV1,
    },
    transaction_builder::{build_private_transfer_instruction_v1, VerifierRouteAccountsV1},
    witness_state::WalletWitnessStateV1,
    NoteContextV1, NoteOpeningV1, ViewingPublicKeyV1, ViewingSecretKeyV1,
};
use aspis_statement::{
    decode_digest_canonical, derive_owner_key, encode_digest_canonical,
    pool_v1::{
        pool_v1_note_commitment, root_history::initialize_root_history_page_bytes_v1,
        DepositEventV1, DepositReceiptV1, HistoricalAnchorEnvelopeV1, PoolV1TransitionKind,
        POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
    },
    Digest,
};
use base64::{engine::general_purpose::STANDARD as BASE64_STANDARD, Engine as _};
use hpke::rand_core::{TryCryptoRng, TryRng};
use solana_program::pubkey::Pubkey;

const PROGRAM_ID: [u8; 32] = [0x91; 32];
static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

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
    fn new(label: &str) -> Self {
        let serial = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "aspis-v7-scanner-durable-{label}-{}-{serial}",
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

fn identity() -> DepositScanIdentityV1 {
    let program = Pubkey::new_from_array(PROGRAM_ID);
    let mint = Pubkey::new_from_array([0x33; 32]);
    let pool = aspis_pool::pool_v1_state_address(&program, &mint).0;
    let vault = aspis_pool::pool_v1_vault_token_account_address(&program, &pool).0;
    DepositScanIdentityV1::new(
        pool.to_bytes(),
        [0x22; 32],
        mint.to_bytes(),
        vault.to_bytes(),
        9,
    )
    .unwrap()
}

fn root_page_address() -> [u8; 32] {
    pool_v1_root_page_address(
        &Pubkey::new_from_array(PROGRAM_ID),
        &Pubkey::new_from_array(*identity().pool()),
        0,
    )
    .0
    .to_bytes()
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

#[derive(Clone)]
struct DepositBlockSpec {
    slot: u64,
    block_hash_byte: u8,
    parent_slot: u64,
    parent_hash_byte: u8,
    signature_byte: u8,
    owner_key: Digest,
    amount: u32,
    salt: Digest,
    payload: Vec<u8>,
    leaf_index: u64,
    root: Digest,
    history_roots: Vec<Digest>,
    commitment: SolanaRpcCommitmentV1,
}

fn ingest_deposit_block(
    state: &mut ScanStateV1,
    spec: &DepositBlockSpec,
    viewing_secret: &ViewingSecretKeyV1,
    local_keys: &impl LocalOwnerKeyStoreV1,
) -> Result<FinalizedBlockIngestResultV1, FinalizedIndexerErrorV1> {
    let mut instruction = vec![0u8; POOL_V1_DEPOSIT_INSTRUCTION_HEADER_BYTES + spec.payload.len()];
    instruction[..4].copy_from_slice(&POOL_V1_DEPOSIT_INSTRUCTION_MAGIC);
    instruction[4] = POOL_V1_DEPOSIT_INSTRUCTION_VERSION;
    instruction[6..8].copy_from_slice(&(spec.payload.len() as u16).to_le_bytes());
    instruction[8..40].copy_from_slice(&encode_digest_canonical(&spec.owner_key));
    instruction[40..44].copy_from_slice(&spec.amount.to_le_bytes());
    instruction[48..80].copy_from_slice(&encode_digest_canonical(&spec.salt));
    instruction[80..].copy_from_slice(&spec.payload);
    let instruction_data = encode_base58(&instruction);

    let receipt = DepositReceiptV1 {
        pool: *identity().pool(),
        asset_mint: *identity().asset_mint(),
        source_token_account: [0x55; 32],
        vault_token_account: *identity().vault_token_account(),
        amount: spec.amount,
        encrypted_note_payload_bytes: spec.payload.len() as u16,
        note_commitment: pool_v1_note_commitment(
            &spec.owner_key,
            spec.amount,
            M31(identity().asset_id()),
            &spec.salt,
        ),
        leaf_index: spec.leaf_index,
        root_sequence: spec.leaf_index + 1,
        root: spec.root,
    };
    let return_record = encode_deposit_event_record_v1(&DepositEventV1 {
        receipt,
        encrypted_note_payload: &spec.payload,
    })
    .unwrap();
    let return_data = BASE64_STANDARD.encode(return_record);

    let payer = encode_base58(&[0x61; 32]);
    let non_pool_program = encode_base58(&[0x62; 32]);
    let pool_program = encode_base58(&PROGRAM_ID);
    let pool = encode_base58(identity().pool());
    let current_page = encode_base58(&root_page_address());
    let mint = encode_base58(identity().asset_mint());
    let source = encode_base58(&[0x55; 32]);
    let source_owner = encode_base58(&[0x56; 32]);
    let vault = encode_base58(identity().vault_token_account());
    let token_program = encode_base58(aspis_pool::LEGACY_SPL_TOKEN_PROGRAM_ID.as_ref());
    let static_keys = [
        payer.as_str(),
        pool.as_str(),
        current_page.as_str(),
        mint.as_str(),
        source.as_str(),
        source_owner.as_str(),
        vault.as_str(),
        token_program.as_str(),
        non_pool_program.as_str(),
        pool_program.as_str(),
    ];
    let instruction_accounts = [1u16, 2, 3, 4, 5, 6, 7];
    let instructions = [SolanaRpcCompiledInstructionV1 {
        program_id_index: 9,
        account_indices: &instruction_accounts,
        data_base58: &instruction_data,
    }];
    let signature = encode_base58(&[spec.signature_byte; 64]);
    let signatures = [signature.as_str()];
    let transaction = SolanaRpcTransactionV1 {
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
    };
    let transactions = [transaction];
    let block_hash = encode_base58(&[spec.block_hash_byte; 32]);
    let parent_hash = encode_base58(&[spec.parent_hash_byte; 32]);
    let block = SolanaRpcBlockV1 {
        asserted_commitment: spec.commitment,
        slot: spec.slot,
        blockhash_base58: &block_hash,
        previous_blockhash_base58: &parent_hash,
        parent_slot: spec.parent_slot,
        transactions: &transactions,
    };

    let mut page_bytes = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
    initialize_root_history_page_bytes_v1(
        &mut page_bytes,
        *identity().pool(),
        0,
        &spec.history_roots,
    )
    .unwrap();
    let page_data = BASE64_STANDARD.encode(page_bytes);
    let page_address_bytes = root_page_address();
    let page_address = encode_base58(&page_address_bytes);
    let page_owner = encode_base58(&PROGRAM_ID);
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
    let root_batch = SolanaRpcRootPageBatchV1 {
        asserted_commitment: SolanaRpcCommitmentV1::Finalized,
        context_slot: spec.slot,
        accounts: &accounts,
    };
    ingest_finalized_rpc_block_v1(
        state,
        &DepositRpcBindingV1::new(PROGRAM_ID).unwrap(),
        &[RootPageAddressBindingV1 {
            page_number: 0,
            address: page_address_bytes,
        }],
        &block,
        Some(&root_batch),
        viewing_secret,
        local_keys,
    )
}

struct PrivateTransferBlockSpec {
    slot: u64,
    block_hash_byte: u8,
    parent_slot: u64,
    parent_hash_byte: u8,
    signature_byte: u8,
    envelope: HistoricalAnchorEnvelopeV1,
    statement: aspis_pool::PrivateTransferStatementV1,
    first_leaf_index: u64,
    intermediate_root: Digest,
    final_root: Digest,
    history_roots: Vec<Digest>,
}

fn ingest_private_transfer_block(
    state: &mut ScanStateV1,
    spec: &PrivateTransferBlockSpec,
    viewing_secret: &ViewingSecretKeyV1,
    local_keys: &impl LocalOwnerKeyStoreV1,
) -> Result<FinalizedBlockIngestResultV1, FinalizedIndexerErrorV1> {
    let built = build_private_transfer_instruction_v1(
        Pubkey::new_from_array(PROGRAM_ID),
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
    encoded_keys.push(encode_base58(&PROGRAM_ID));
    encoded_keys.extend(
        built
            .accounts
            .iter()
            .map(|account| encode_base58(account.pubkey.as_ref())),
    );
    let static_keys: Vec<_> = encoded_keys.iter().map(String::as_str).collect();
    let account_indices: Vec<_> = (1..=built.accounts.len() as u16).collect();
    let instructions = [SolanaRpcCompiledInstructionV1 {
        program_id_index: 0,
        account_indices: &account_indices,
        data_base58: &instruction_data,
    }];
    let signature = encode_base58(&[spec.signature_byte; 64]);
    let signatures = [signature.as_str()];
    let transaction = SolanaRpcTransactionV1 {
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
    };
    let transactions = [transaction];
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
    let page_address_bytes = root_page_address();
    let page_address = encode_base58(&page_address_bytes);
    let page_owner = encode_base58(&PROGRAM_ID);
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
    let root_batch = SolanaRpcRootPageBatchV1 {
        asserted_commitment: SolanaRpcCommitmentV1::Finalized,
        context_slot: spec.slot,
        accounts: &accounts,
    };
    ingest_finalized_rpc_block_v1(
        state,
        &DepositRpcBindingV1::new(PROGRAM_ID).unwrap(),
        &[RootPageAddressBindingV1 {
            page_number: 0,
            address: page_address_bytes,
        }],
        &block,
        Some(&root_batch),
        viewing_secret,
        local_keys,
    )
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

fn note(owner_key: [u8; 32], value: u32, salt_seed: u32) -> NoteOpeningV1 {
    NoteOpeningV1::new(
        owner_key,
        value,
        identity().asset_id(),
        encode_digest_canonical(&digest(salt_seed)),
    )
    .unwrap()
}

fn encrypted_payload(
    rng: &mut FixedTestRng,
    recipient: &ViewingPublicKeyV1,
    leaf_index: u64,
    note: &NoteOpeningV1,
) -> Vec<u8> {
    let commitment = aspis_pool_wallet_v1::recompute_note_commitment_v1(note).unwrap();
    let context = NoteContextV1::new(
        *identity().pool(),
        *identity().deployment_domain(),
        leaf_index,
        commitment,
    )
    .unwrap();
    encrypt_note_v1(rng, recipient, &context, note)
        .unwrap()
        .to_vec()
}

fn sealed_deposits(
    result: &FinalizedBlockIngestResultV1,
    rng: &mut FixedTestRng,
    cipher: &NoteStoreCipherV1,
) -> Vec<SealedRecoveredNoteV1> {
    result
        .deposit_event_ids()
        .iter()
        .copied()
        .zip(result.deposit_outcomes())
        .filter_map(|(event_id, outcome)| match outcome {
            DepositScanOutcomeV1::ViewOnly(note) => Some(
                seal_recovered_note_v1(rng, cipher, event_id, SealedNoteAccessV1::ViewOnly, note)
                    .unwrap(),
            ),
            DepositScanOutcomeV1::Spendable(note) => Some(
                seal_recovered_note_v1(rng, cipher, event_id, SealedNoteAccessV1::Spendable, note)
                    .unwrap(),
            ),
            _ => None,
        })
        .collect()
}

fn deposit_spec(
    point: (u64, u8, u64, u8),
    signature_byte: u8,
    leaf_index: u64,
    opening: &NoteOpeningV1,
    recipient: &ViewingPublicKeyV1,
    rng_seed: u8,
    history_roots: Vec<Digest>,
) -> DepositBlockSpec {
    let root = *history_roots
        .last()
        .expect("deposit history must include the finalized root");
    DepositBlockSpec {
        slot: point.0,
        block_hash_byte: point.1,
        parent_slot: point.2,
        parent_hash_byte: point.3,
        signature_byte,
        owner_key: decode_digest_canonical(opening.owner_key()).unwrap(),
        amount: opening.value(),
        salt: decode_digest_canonical(opening.salt()).unwrap(),
        payload: encrypted_payload(&mut FixedTestRng(rng_seed), recipient, leaf_index, opening),
        leaf_index,
        root,
        history_roots,
        commitment: SolanaRpcCommitmentV1::Finalized,
    }
}

#[test]
fn finalized_scanner_wallet_and_witness_restart_fail_closed_and_idempotent() {
    let directory = TestDirectory::new("linear");
    let wallet_path = directory.path("wallet.state");
    let witness_path = directory.path("witness.state");
    let empty_witness = WalletWitnessStateV1::empty();
    let initial_scan = ScanStateV1::new(
        identity(),
        FinalizedChainPointV1::new(100, [0xa0; 32]).unwrap(),
        0,
        encode_digest_canonical(&empty_witness.tree().root),
    )
    .unwrap();
    let (viewing_secret, viewing_public) = derive_viewing_keypair_v1(&[0x51; 32]).unwrap();
    let (_, unrelated_public) = derive_viewing_keypair_v1(&[0x52; 32]).unwrap();
    let nullifier_key = encode_digest_canonical(&digest(100));
    let owner_key = encode_digest_canonical(&derive_owner_key(
        &decode_digest_canonical(&nullifier_key).unwrap(),
    ));
    let local_keys = LocalKeys {
        owner_key,
        nullifier_key,
    };
    let cipher = NoteStoreCipherV1::from_key_bytes([0x71; 32]).unwrap();
    let mut wallet = DurableWalletStateV1::open_or_create_v1(
        &wallet_path,
        initial_scan.clone(),
        cipher.cipher_id(),
    )
    .unwrap();
    DurableWalletWitnessStateV1::open_or_create_v1(
        &witness_path,
        &initial_scan,
        empty_witness.clone(),
    )
    .unwrap();

    let spendable_opening = note(owner_key, 77, 200);
    let spendable_commitment = decode_digest_canonical(
        &aspis_pool_wallet_v1::recompute_note_commitment_v1(&spendable_opening).unwrap(),
    )
    .unwrap();
    let (tree_one, _) = empty_witness
        .tree()
        .append_one(spendable_commitment)
        .unwrap();
    let block_one = deposit_spec(
        (101, 0xa1, 100, 0xa0),
        0x41,
        0,
        &spendable_opening,
        &viewing_public,
        0x10,
        vec![empty_witness.tree().root, tree_one.root],
    );

    // Event received but neither cursor nor note store persisted.
    let mut discarded_candidate = wallet.scan_state().clone();
    let discarded_result = ingest_deposit_block(
        &mut discarded_candidate,
        &block_one,
        &viewing_secret,
        &local_keys,
    )
    .unwrap();
    let premature = sealed_deposits(&discarded_result, &mut FixedTestRng(0x20), &cipher);
    assert_eq!(premature.len(), 1);
    assert_eq!(
        wallet
            .store_authenticated_delivery_v1(&premature[0])
            .unwrap_err(),
        DurableStateErrorV1::UnexpectedRecoveredNote
    );
    assert_eq!(wallet.scan_state(), &initial_scan);
    assert!(wallet.notes().is_empty());
    drop(discarded_result);
    drop(discarded_candidate);

    // Commit the same finalized input. The wallet image advances the cursor
    // and stores the sealed note in one rename.
    let previous_scan = wallet.scan_state().clone();
    let mut candidate = previous_scan.clone();
    let result =
        ingest_deposit_block(&mut candidate, &block_one, &viewing_secret, &local_keys).unwrap();
    assert_eq!(result.advance(), FinalizedBlockAdvanceV1::Advanced);
    assert!(matches!(
        result.deposit_outcomes(),
        [DepositScanOutcomeV1::Spendable(_)]
    ));
    let spendable_id = result.deposit_event_ids()[0];
    assert_eq!(
        wallet
            .commit_finalized_ingest_v1(
                candidate.clone(),
                &result,
                &[],
                &[],
                &EncryptedLocalSpendAuthenticatorV1::new(&cipher, &local_keys),
            )
            .err(),
        Some(DurableStateErrorV1::MissingRecoveredNote)
    );
    assert_eq!(wallet.scan_state(), &previous_scan);
    assert!(wallet.notes().is_empty());
    let recovered = sealed_deposits(&result, &mut FixedTestRng(0x30), &cipher);
    assert_eq!(
        recovered[0].sealed_note.len(),
        POOL_V1_NOTE_STORE_SEALED_BYTES
    );
    assert_eq!(&recovered[0].sealed_note[..8], b"ASNS\x01\x00\x01\x00");
    let spendable_sealed = recovered[0].clone();
    wallet
        .commit_finalized_ingest_v1(
            candidate.clone(),
            &result,
            &recovered,
            &[],
            &EncryptedLocalSpendAuthenticatorV1::new(&cipher, &local_keys),
        )
        .unwrap();

    // A crash between the separate wallet and witness files is detected,
    // never accepted as a matching witness history. Replaying the retained
    // finalized result repairs the lagging journal deterministically.
    assert_eq!(
        DurableWalletWitnessStateV1::open_or_create_v1(
            &witness_path,
            &candidate,
            empty_witness.clone(),
        )
        .err(),
        Some(DurableWitnessErrorV1::ScanStateMismatch)
    );
    let mut witness = DurableWalletWitnessStateV1::open_or_create_v1(
        &witness_path,
        &previous_scan,
        empty_witness.clone(),
    )
    .unwrap();
    witness
        .commit_finalized_ingest_v1(&previous_scan, &candidate, &result, &[spendable_id])
        .unwrap();
    assert_eq!(witness.current_state().tracked().len(), 1);
    drop(witness);
    drop(wallet);

    let mut wallet = DurableWalletStateV1::open_or_create_v1(
        &wallet_path,
        initial_scan.clone(),
        cipher.cipher_id(),
    )
    .unwrap();
    let mut witness = DurableWalletWitnessStateV1::open_or_create_v1(
        &witness_path,
        wallet.scan_state(),
        empty_witness.clone(),
    )
    .unwrap();
    assert_eq!(wallet.scan_state().head().slot(), 101);
    assert_eq!(wallet.notes().len(), 1);

    // Replaying the exact finalized block from the durable head advances
    // nothing, produces no replacement ciphertext, and preserves one note.
    let replay_previous = wallet.scan_state().clone();
    let mut replay_candidate = replay_previous.clone();
    let replay = ingest_deposit_block(
        &mut replay_candidate,
        &block_one,
        &viewing_secret,
        &local_keys,
    )
    .unwrap();
    assert_eq!(replay.advance(), FinalizedBlockAdvanceV1::AlreadyCurrent);
    assert!(matches!(
        replay.deposit_outcomes(),
        [DepositScanOutcomeV1::Duplicate]
    ));
    assert_eq!(replay_candidate, replay_previous);
    wallet
        .commit_finalized_ingest_v1(
            replay_candidate.clone(),
            &replay,
            &[],
            &[],
            &EncryptedLocalSpendAuthenticatorV1::new(&cipher, &local_keys),
        )
        .unwrap();
    witness
        .commit_finalized_ingest_v1(&replay_previous, &replay_candidate, &replay, &[])
        .unwrap();
    assert_eq!(wallet.notes().len(), 1);

    // Same event identity with changed authenticated bytes is a conflict and
    // a non-finalized child is rejected before any candidate mutation.
    let mut conflicting = block_one.clone();
    conflicting.payload[0] ^= 1;
    let conflict_baseline = wallet.scan_state().clone();
    let mut conflict_candidate = conflict_baseline.clone();
    assert!(matches!(
        ingest_deposit_block(
            &mut conflict_candidate,
            &conflicting,
            &viewing_secret,
            &local_keys,
        ),
        Err(FinalizedIndexerErrorV1::ScanState(
            ScanStateErrorV1::EventIdentityConflict
        ))
    ));
    assert_eq!(conflict_candidate, conflict_baseline);

    let view_opening = note(encode_digest_canonical(&digest(301)), 31, 302);
    let view_commitment = decode_digest_canonical(
        &aspis_pool_wallet_v1::recompute_note_commitment_v1(&view_opening).unwrap(),
    )
    .unwrap();
    let (tree_two, _) = tree_one.append_one(view_commitment).unwrap();
    let block_two = deposit_spec(
        (103, 0xa2, 101, 0xa1),
        0x42,
        1,
        &view_opening,
        &viewing_public,
        0x40,
        vec![empty_witness.tree().root, tree_one.root, tree_two.root],
    );
    let mut nonfinal = block_two.clone();
    nonfinal.commitment = SolanaRpcCommitmentV1::Confirmed;
    let nonfinal_baseline = wallet.scan_state().clone();
    let mut nonfinal_candidate = nonfinal_baseline.clone();
    assert_eq!(
        ingest_deposit_block(
            &mut nonfinal_candidate,
            &nonfinal,
            &viewing_secret,
            &local_keys,
        )
        .err(),
        Some(FinalizedIndexerErrorV1::BlockNotFinalized)
    );
    assert_eq!(nonfinal_candidate, nonfinal_baseline);

    let previous = wallet.scan_state().clone();
    let mut candidate = previous.clone();
    let result =
        ingest_deposit_block(&mut candidate, &block_two, &viewing_secret, &local_keys).unwrap();
    assert!(matches!(
        result.deposit_outcomes(),
        [DepositScanOutcomeV1::ViewOnly(_)]
    ));
    let view_only_id = result.deposit_event_ids()[0];
    let recovered = sealed_deposits(&result, &mut FixedTestRng(0x50), &cipher);
    wallet
        .commit_finalized_ingest_v1(
            candidate.clone(),
            &result,
            &recovered,
            &[],
            &EncryptedLocalSpendAuthenticatorV1::new(&cipher, &local_keys),
        )
        .unwrap();
    witness
        .commit_finalized_ingest_v1(&previous, &candidate, &result, &[view_only_id])
        .unwrap();

    let unrelated_opening = note(encode_digest_canonical(&digest(401)), 23, 402);
    let unrelated_commitment = decode_digest_canonical(
        &aspis_pool_wallet_v1::recompute_note_commitment_v1(&unrelated_opening).unwrap(),
    )
    .unwrap();
    let (tree_three, _) = tree_two.append_one(unrelated_commitment).unwrap();
    let block_three = deposit_spec(
        (105, 0xa3, 103, 0xa2),
        0x43,
        2,
        &unrelated_opening,
        &unrelated_public,
        0x60,
        vec![
            empty_witness.tree().root,
            tree_one.root,
            tree_two.root,
            tree_three.root,
        ],
    );
    let previous = wallet.scan_state().clone();
    let mut candidate = previous.clone();
    let result =
        ingest_deposit_block(&mut candidate, &block_three, &viewing_secret, &local_keys).unwrap();
    assert!(matches!(
        result.deposit_outcomes(),
        [DepositScanOutcomeV1::NotForViewingKey]
    ));
    wallet
        .commit_finalized_ingest_v1(
            candidate.clone(),
            &result,
            &[],
            &[],
            &EncryptedLocalSpendAuthenticatorV1::new(&cipher, &local_keys),
        )
        .unwrap();
    witness
        .commit_finalized_ingest_v1(&previous, &candidate, &result, &[])
        .unwrap();
    assert_eq!(wallet.notes().len(), 2);
    assert!(wallet.notes().iter().all(|stored| {
        stored.sealed_note.len() == POOL_V1_NOTE_STORE_SEALED_BYTES
            && &stored.sealed_note[..8] == b"ASNS\x01\x00\x01\x00"
    }));
    assert_eq!(witness.current_state().tracked().len(), 2);

    // A finalized private transfer authenticated by the same mock RPC/root
    // path marks only the locally authenticated spendable input as spent.
    let recipient_commitment = digest(501);
    let change_commitment = digest(601);
    let (tree_four, _) = tree_three.append_one(recipient_commitment).unwrap();
    let (tree_five, _) = tree_four.append_one(change_commitment).unwrap();
    let nullifier = decode_digest_canonical(
        &aspis_pool_wallet_v1::wallet_transition::derive_note_nullifier_v1(
            &spendable_opening,
            &nullifier_key,
        )
        .unwrap(),
    )
    .unwrap();
    let transfer = PrivateTransferBlockSpec {
        slot: 107,
        block_hash_byte: 0xa4,
        parent_slot: 105,
        parent_hash_byte: 0xa3,
        signature_byte: 0x44,
        envelope: HistoricalAnchorEnvelopeV1 {
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            pool: *identity().pool(),
            deployment_domain: *identity().deployment_domain(),
            anchor_sequence: 3,
            anchor_root: tree_three.root,
            nullifier,
            verifier_profile: [0x81; 32],
            verifier_release: [0x82; 32],
        },
        statement: aspis_pool::PrivateTransferStatementV1 {
            pool: *identity().pool(),
            deployment_domain: *identity().deployment_domain(),
            anchor_sequence: 3,
            anchor_root: tree_three.root,
            nullifier,
            asset_id: M31(identity().asset_id()),
            recipient_commitment,
            change_commitment,
        },
        first_leaf_index: 3,
        intermediate_root: tree_four.root,
        final_root: tree_five.root,
        history_roots: vec![
            empty_witness.tree().root,
            tree_one.root,
            tree_two.root,
            tree_three.root,
            tree_four.root,
            tree_five.root,
        ],
    };
    let previous = wallet.scan_state().clone();
    let mut candidate = previous.clone();
    let result =
        ingest_private_transfer_block(&mut candidate, &transfer, &viewing_secret, &local_keys)
            .unwrap();
    assert_eq!(result.transition_outcomes().len(), 2);
    let transition_output_id = result.transition_evidence()[0].output_ids[0];
    let spend_update = AuthenticatedSpentNoteUpdateV1 {
        input_event_id: spendable_id,
        transition_output_id,
        nullifier: encode_digest_canonical(&nullifier),
    };
    wallet
        .commit_finalized_ingest_v1(
            candidate.clone(),
            &result,
            &[],
            &[spend_update],
            &EncryptedLocalSpendAuthenticatorV1::new(&cipher, &local_keys),
        )
        .unwrap();
    witness
        .commit_finalized_ingest_v1(&previous, &candidate, &result, &[])
        .unwrap();
    drop(witness);
    drop(wallet);

    let mut wallet = DurableWalletStateV1::open_or_create_v1(
        &wallet_path,
        initial_scan.clone(),
        cipher.cipher_id(),
    )
    .unwrap();
    let mut witness = DurableWalletWitnessStateV1::open_or_create_v1(
        &witness_path,
        wallet.scan_state(),
        empty_witness,
    )
    .unwrap();
    let spendable = wallet
        .notes()
        .iter()
        .find(|stored| stored.event_id == spendable_id)
        .unwrap();
    assert_eq!(spendable.access, SealedNoteAccessV1::Spendable);
    assert_eq!(
        spendable.spent.unwrap().transition_output_id,
        transition_output_id
    );
    let view_only = wallet
        .notes()
        .iter()
        .find(|stored| stored.event_id == view_only_id)
        .unwrap();
    assert_eq!(view_only.access, SealedNoteAccessV1::ViewOnly);
    assert!(view_only.spent.is_none());
    assert_eq!(wallet.scan_state().head().slot(), 107);
    assert_eq!(wallet.scan_state().next_leaf_index(), 5);
    assert_eq!(witness.current_state().tree().next_leaf_index, 5);
    assert_eq!(witness.current_state().tree().root, tree_five.root);
    assert!(witness
        .current_state()
        .tracked()
        .iter()
        .all(|tracked| tracked.root() == tree_five.root));

    // Losing the first finalized-status response and observing it again is
    // idempotent: the same spent marker is accepted, never upgraded from a
    // different or unfinalized event, and the note cannot reappear unspent.
    let replay_previous = wallet.scan_state().clone();
    let mut replay_candidate = replay_previous.clone();
    let replay = ingest_private_transfer_block(
        &mut replay_candidate,
        &transfer,
        &viewing_secret,
        &local_keys,
    )
    .unwrap();
    assert_eq!(replay.advance(), FinalizedBlockAdvanceV1::AlreadyCurrent);
    assert!(replay.transition_outcomes().iter().all(|outcome| *outcome
        == aspis_pool_wallet_v1::scan_state::PublicOutputScanOutcomeV1::Duplicate));
    wallet
        .commit_finalized_ingest_v1(
            replay_candidate.clone(),
            &replay,
            &[],
            &[spend_update],
            &EncryptedLocalSpendAuthenticatorV1::new(&cipher, &local_keys),
        )
        .unwrap();
    witness
        .commit_finalized_ingest_v1(&replay_previous, &replay_candidate, &replay, &[])
        .unwrap();
    assert_eq!(
        wallet
            .store_authenticated_delivery_v1(&spendable_sealed)
            .unwrap(),
        RelayerEnqueueOutcomeV1::AlreadyPresent
    );
    assert!(wallet
        .notes()
        .iter()
        .filter(|stored| stored.access == SealedNoteAccessV1::Spendable)
        .all(|stored| stored.spent.is_some()));
}

#[cfg(feature = "eight-lane-plumbing-v2")]
mod lane_forest_restart {
    use super::*;
    use aspis_pool::{
        pool_v1_pair_forest_checkpoint_address, pool_v1_pair_forest_lane_address,
        pool_v1_pair_forest_master_address, POOL_V1_PAIR_EMPTY_ROOTS,
    };
    use aspis_pool_wallet_v1::{
        lane_forest_durable_v2::{
            DurableLaneForestWalletFileV2, ForestFinalizedAppendEventV2,
            ForestFinalizedAppendKindV2, ForestNoteAssociationOutcomeV2, LaneForestDurableErrorV2,
            LaneForestDurableStateV2,
        },
        lane_forest_v2::{lane_forest_global_root_v2, LaneIdV2, PairSlotV2},
        recompute_note_commitment_v1,
        scan_state::DepositEventIdV1,
    };
    use aspis_statement::pool_v1::{
        encode_pool_v1_pair_forest_checkpoint_v1, encode_pool_v1_pair_forest_lane_state_v1,
        encode_pool_v1_pair_forest_master_v1, IncrementalMerkleTreeV1, PoolIdentityV1,
        PoolV1PairForestCheckpointV1, PoolV1PairForestLaneStateV1, PoolV1PairForestMasterV1,
        PoolV1PairLeafWitnessV1, VerifierPolicyV1, POOL_V1_PAIR_FOREST_ALL_LANES_MASK,
        POOL_V1_PAIR_TREE_DEPTH,
    };

    fn lane_event(
        slot: u64,
        signature_byte: u8,
        instruction_index: u16,
        event_index: u16,
    ) -> DepositEventIdV1 {
        DepositEventIdV1::new(
            FinalizedChainPointV1::new(slot, [signature_byte.wrapping_add(1); 32]).unwrap(),
            [signature_byte; 64],
            instruction_index,
            event_index,
        )
        .unwrap()
    }

    fn forest_fixture() -> (Pubkey, Pubkey, LaneForestDurableStateV2) {
        let program = Pubkey::new_from_array([0xb1; 32]);
        let mint = Pubkey::new_from_array([0xb2; 32]);
        let master = pool_v1_pair_forest_master_address(&program, &mint).0;
        let master_value = PoolV1PairForestMasterV1 {
            identity: PoolIdentityV1 {
                pool: master.to_bytes(),
                asset_mint: mint.to_bytes(),
                token_program: [0xb3; 32],
                asset_id: M31(4),
                deployment_domain: [0xb4; 32],
            },
            verifier_policy: VerifierPolicyV1 {
                flags: 1,
                registry_program: [0xb5; 32],
                registry_authority: [0u8; 32],
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
        let state = LaneForestDurableStateV2::from_authenticated_accounts_v2(
            program.to_bytes(),
            master.to_bytes(),
            &master_image,
            &lanes,
            None,
        )
        .unwrap();
        (program, master, state)
    }

    fn forest_note_for_lane(
        target: LaneIdV2,
        owner_seed: u32,
        value: u32,
        first_salt_seed: u32,
    ) -> (NoteOpeningV1, [u8; 32]) {
        for salt_seed in first_salt_seed..first_salt_seed + 10_000 {
            let opening = NoteOpeningV1::new(
                encode_digest_canonical(&digest(owner_seed)),
                value,
                4,
                encode_digest_canonical(&digest(salt_seed)),
            )
            .unwrap();
            let commitment = recompute_note_commitment_v1(&opening).unwrap();
            if commitment[0] & 7 == target.as_u8() {
                return (opening, commitment);
            }
        }
        panic!("deterministic note search did not reach target lane")
    }

    fn after_lane_for_pair_leaf(
        state: &LaneForestDurableStateV2,
        lane_id: LaneIdV2,
        pair_leaf: Digest,
    ) -> (
        [u8; 32],
        [u8; aspis_statement::pool_v1::POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES],
    ) {
        let account = *state.lane(lane_id).0;
        let next_tree = account
            .value
            .tree
            .append_one_with_empty_roots(pair_leaf, &POOL_V1_PAIR_EMPTY_ROOTS)
            .unwrap()
            .0;
        let value = PoolV1PairForestLaneStateV1 {
            tree: next_tree,
            ..account.value
        };
        (
            account.address,
            encode_pool_v1_pair_forest_lane_state_v1(&value, &POOL_V1_PAIR_EMPTY_ROOTS).unwrap(),
        )
    }

    fn forest_deposit_event(
        state: &LaneForestDurableStateV2,
        event_id: DepositEventIdV1,
        note: &NoteOpeningV1,
        commitment: [u8; 32],
        recipient: &ViewingPublicKeyV1,
        rng_seed: u8,
    ) -> ForestFinalizedAppendEventV2 {
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
            encrypt_note_v1(&mut FixedTestRng(rng_seed), recipient, &context, note).unwrap();
        let (after_lane_address, after_lane_image) =
            after_lane_for_pair_leaf(state, lane_id, pair_leaf);
        ForestFinalizedAppendEventV2 {
            master: state.master().address,
            lane_id,
            pair_leaf_index,
            root_sequence: pair_leaf_index + 1,
            after_lane_address,
            after_lane_image,
            kind: ForestFinalizedAppendKindV2::Deposit {
                event_id,
                commitment,
                encrypted_note: Some(payload),
            },
        }
    }

    fn forest_private_transfer_event(
        state: &LaneForestDurableStateV2,
        recipient_event_id: DepositEventIdV1,
        change_event_id: DepositEventIdV1,
        nullifier: [u8; 32],
        recipient: (&NoteOpeningV1, [u8; 32], &ViewingPublicKeyV1, u8),
        change: (&NoteOpeningV1, [u8; 32], &ViewingPublicKeyV1, u8),
    ) -> ForestFinalizedAppendEventV2 {
        let lane_id = LaneIdV2::new(nullifier[0] & 7).unwrap();
        let pair_leaf = PoolV1PairLeafWitnessV1::two_outputs(
            decode_digest_canonical(&recipient.1).unwrap(),
            decode_digest_canonical(&change.1).unwrap(),
        )
        .unwrap()
        .leaf_digest()
        .unwrap();
        let pair_leaf_index = state.lane(lane_id).0.value.tree.next_leaf_index;
        let recipient_context = NoteContextV1::new(
            state.master().address,
            state.master().value.identity.deployment_domain,
            pair_leaf_index,
            recipient.1,
        )
        .unwrap();
        let change_context = NoteContextV1::new(
            state.master().address,
            state.master().value.identity.deployment_domain,
            pair_leaf_index,
            change.1,
        )
        .unwrap();
        let recipient_payload = encrypt_note_v1(
            &mut FixedTestRng(recipient.3),
            recipient.2,
            &recipient_context,
            recipient.0,
        )
        .unwrap();
        let change_payload = encrypt_note_v1(
            &mut FixedTestRng(change.3),
            change.2,
            &change_context,
            change.0,
        )
        .unwrap();
        let (after_lane_address, after_lane_image) =
            after_lane_for_pair_leaf(state, lane_id, pair_leaf);
        ForestFinalizedAppendEventV2 {
            master: state.master().address,
            lane_id,
            pair_leaf_index,
            root_sequence: pair_leaf_index + 1,
            after_lane_address,
            after_lane_image,
            kind: ForestFinalizedAppendKindV2::PrivateTransfer {
                recipient_event_id,
                change_event_id,
                nullifier,
                recipient_commitment: recipient.1,
                change_commitment: change.1,
                recipient_encrypted_note: Some(recipient_payload),
                change_encrypted_note: Some(change_payload),
            },
        }
    }

    type CheckpointInputs = (
        [u8; 32],
        Vec<u8>,
        Vec<([u8; 32], Vec<u8>)>,
        [u8; 32],
        Vec<u8>,
    );

    fn checkpoint_inputs(state: &LaneForestDurableStateV2) -> CheckpointInputs {
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
            checkpoint_sequence: state.master().value.next_checkpoint_sequence,
            global_root: decode_digest_canonical(&lane_forest_global_root_v2(&roots).unwrap())
                .unwrap(),
            lane_sequences: sequences,
        };
        let checkpoint_address = pool_v1_pair_forest_checkpoint_address(
            &Pubkey::new_from_array(*state.program_id()),
            &Pubkey::new_from_array(state.master().address),
            checkpoint.checkpoint_sequence,
        )
        .0
        .to_bytes();
        let next_master = PoolV1PairForestMasterV1 {
            has_checkpoint: true,
            next_checkpoint_sequence: checkpoint.checkpoint_sequence + 1,
            last_checkpoint_lane_sequences: sequences,
            ..state.master().value
        };
        (
            state.master().address,
            encode_pool_v1_pair_forest_master_v1(&next_master)
                .unwrap()
                .to_vec(),
            (0..8)
                .map(|index| {
                    let lane = state.lane(LaneIdV2::new(index).unwrap()).0;
                    (lane.address, lane.image.to_vec())
                })
                .collect(),
            checkpoint_address,
            encode_pool_v1_pair_forest_checkpoint_v1(&checkpoint)
                .unwrap()
                .to_vec(),
        )
    }

    fn ingest_checkpoint(state: &mut LaneForestDurableStateV2, point: FinalizedChainPointV1) {
        let (master, master_image, lanes, checkpoint, checkpoint_image) = checkpoint_inputs(state);
        state
            .ingest_finalized_checkpoint_v2(
                point,
                master,
                &master_image,
                &lanes,
                checkpoint,
                &checkpoint_image,
            )
            .unwrap();
    }

    #[test]
    fn v7_multi_lane_checkpoint_restart_and_exact_replay_are_idempotent() {
        let directory = TestDirectory::new("forest");
        let path_a = directory.path("forest-a.state");
        let path_b = directory.path("forest-b.state");
        let (_, _, initial) = forest_fixture();
        let (secret_a, public_a) = derive_viewing_keypair_v1(&[0xc1; 32]).unwrap();
        let (secret_b, public_b) = derive_viewing_keypair_v1(&[0xc2; 32]).unwrap();
        let (_, public_c) = derive_viewing_keypair_v1(&[0xc3; 32]).unwrap();
        let lane_zero = LaneIdV2::new(0).unwrap();
        let lane_one = LaneIdV2::new(1).unwrap();
        let lane_two = LaneIdV2::new(2).unwrap();
        let lane_three = LaneIdV2::new(3).unwrap();
        let (note_a, commitment_a) = forest_note_for_lane(lane_zero, 1_000, 17, 2_000);
        let (note_b, commitment_b) = forest_note_for_lane(lane_one, 1_100, 19, 2_100);
        let (note_c, commitment_c) = forest_note_for_lane(lane_three, 1_200, 23, 2_200);
        let event_a = forest_deposit_event(
            &initial,
            lane_event(200, 0xd1, 0, 0),
            &note_a,
            commitment_a,
            &public_a,
            0x10,
        );

        let mut file_a =
            DurableLaneForestWalletFileV2::open_or_create_v2(&path_a, initial.clone()).unwrap();
        let mut file_b =
            DurableLaneForestWalletFileV2::open_or_create_v2(&path_b, initial.clone()).unwrap();

        // A received-but-unpersisted append disappears on restart.
        let mut interrupted = file_a.state().clone();
        assert!(matches!(
            interrupted
                .ingest_finalized_append_v2(event_a.clone(), Some(&secret_a))
                .unwrap()[0]
                .outcome,
            ForestNoteAssociationOutcomeV2::Recovered(_)
        ));
        assert_eq!(file_a.state(), &initial);

        // Both wallets consume the same canonical append sequence. Each
        // recovers only its own ciphertext; neither recovers recipient C.
        let mut candidate_a = file_a.state().clone();
        let mut candidate_b = file_b.state().clone();
        let a_observes_a = candidate_a
            .ingest_finalized_append_v2(event_a.clone(), Some(&secret_a))
            .unwrap();
        assert!(matches!(
            a_observes_a[0].outcome,
            ForestNoteAssociationOutcomeV2::Recovered(_)
        ));
        let b_observes_a = candidate_b
            .ingest_finalized_append_v2(event_a.clone(), Some(&secret_b))
            .unwrap();
        assert!(matches!(
            b_observes_a[0].outcome,
            ForestNoteAssociationOutcomeV2::NotForViewingKey
        ));

        let event_b = forest_deposit_event(
            &candidate_a,
            lane_event(201, 0xd2, 0, 0),
            &note_b,
            commitment_b,
            &public_b,
            0x30,
        );
        let a_observes_b = candidate_a
            .ingest_finalized_append_v2(event_b.clone(), Some(&secret_a))
            .unwrap();
        assert!(matches!(
            a_observes_b[0].outcome,
            ForestNoteAssociationOutcomeV2::NotForViewingKey
        ));
        let b_observes_b = candidate_b
            .ingest_finalized_append_v2(event_b.clone(), Some(&secret_b))
            .unwrap();
        assert!(matches!(
            b_observes_b[0].outcome,
            ForestNoteAssociationOutcomeV2::Recovered(_)
        ));

        let event_c = forest_deposit_event(
            &candidate_a,
            lane_event(202, 0xd3, 0, 0),
            &note_c,
            commitment_c,
            &public_c,
            0x50,
        );
        let a_observes_c = candidate_a
            .ingest_finalized_append_v2(event_c.clone(), Some(&secret_a))
            .unwrap();
        let b_observes_c = candidate_b
            .ingest_finalized_append_v2(event_c, Some(&secret_b))
            .unwrap();
        assert!(matches!(
            a_observes_c[0].outcome,
            ForestNoteAssociationOutcomeV2::NotForViewingKey
        ));
        assert!(matches!(
            b_observes_c[0].outcome,
            ForestNoteAssociationOutcomeV2::NotForViewingKey
        ));

        let checkpoint_zero_point = FinalizedChainPointV1::new(203, [0xd4; 32]).unwrap();
        assert_eq!(
            checkpoint_inputs(&candidate_a),
            checkpoint_inputs(&candidate_b)
        );
        ingest_checkpoint(&mut candidate_a, checkpoint_zero_point);
        ingest_checkpoint(&mut candidate_b, checkpoint_zero_point);
        file_a.replace_state_v2(candidate_a.clone()).unwrap();
        file_b.replace_state_v2(candidate_b.clone()).unwrap();
        drop(file_a);
        drop(file_b);

        let mut file_a =
            DurableLaneForestWalletFileV2::open_or_create_v2(&path_a, initial.clone()).unwrap();
        let mut file_b =
            DurableLaneForestWalletFileV2::open_or_create_v2(&path_b, initial.clone()).unwrap();
        assert_eq!(file_a.state().checkpoint_count(), 1);
        assert_eq!(file_b.state().checkpoint_count(), 1);
        assert_eq!(file_a.state().lane(lane_zero).1.tracked().len(), 1);
        assert!(file_a.state().lane(lane_one).1.tracked().is_empty());
        assert!(file_a.state().lane(lane_three).1.tracked().is_empty());
        assert!(file_b.state().lane(lane_zero).1.tracked().is_empty());
        assert_eq!(file_b.state().lane(lane_one).1.tracked().len(), 1);
        assert!(file_b.state().lane(lane_three).1.tracked().is_empty());

        let mut exact_replay_a = file_a.state().clone();
        assert!(exact_replay_a
            .ingest_finalized_append_v2(event_a.clone(), Some(&secret_a))
            .unwrap()
            .is_empty());
        assert_eq!(&exact_replay_a, file_a.state());
        let mut exact_replay_b = file_b.state().clone();
        assert!(exact_replay_b
            .ingest_finalized_append_v2(event_b.clone(), Some(&secret_b))
            .unwrap()
            .is_empty());
        assert_eq!(&exact_replay_b, file_b.state());

        let mut conflict = event_a.clone();
        match &mut conflict.kind {
            ForestFinalizedAppendKindV2::Deposit {
                encrypted_note: Some(payload),
                ..
            } => payload[0] ^= 1,
            _ => unreachable!(),
        }
        let conflict_baseline = file_a.state().clone();
        let mut conflict_candidate = conflict_baseline.clone();
        assert_eq!(
            conflict_candidate
                .ingest_finalized_append_v2(conflict, Some(&secret_a))
                .err(),
            Some(LaneForestDurableErrorV2::DuplicateEvent)
        );
        assert_eq!(conflict_candidate, conflict_baseline);

        let (out_of_order_note, out_of_order_commitment) =
            forest_note_for_lane(lane_three, 1_300, 11, 2_300);
        let out_of_order = forest_deposit_event(
            file_a.state(),
            lane_event(199, 0xd5, 0, 0),
            &out_of_order_note,
            out_of_order_commitment,
            &public_a,
            0x70,
        );
        let order_baseline = file_a.state().clone();
        let mut order_candidate = order_baseline.clone();
        assert_eq!(
            order_candidate
                .ingest_finalized_append_v2(out_of_order, Some(&secret_a))
                .err(),
            Some(LaneForestDurableErrorV2::EventOutsideFinalizedOrder)
        );
        assert_eq!(order_candidate, order_baseline);

        let mut candidate_a = file_a.state().clone();
        let mut candidate_b = file_b.state().clone();
        let (recipient_note, recipient_commitment) =
            forest_note_for_lane(lane_three, 1_400, 7, 2_400);
        let (change_note, change_commitment) = forest_note_for_lane(lane_zero, 1_500, 5, 2_500);
        let nullifier = encode_digest_canonical(&digest(3_002));
        assert_eq!(nullifier[0] & 7, lane_two.as_u8());
        let recipient_event_id = lane_event(204, 0xd6, 1, 0);
        let change_event_id = lane_event(204, 0xd6, 1, 1);
        let transfer = forest_private_transfer_event(
            &candidate_a,
            recipient_event_id,
            change_event_id,
            nullifier,
            (&recipient_note, recipient_commitment, &public_a, 0x90),
            (&change_note, change_commitment, &public_b, 0xb0),
        );
        let associations_a = candidate_a
            .ingest_finalized_append_v2(transfer.clone(), Some(&secret_a))
            .unwrap();
        assert_eq!(associations_a.len(), 2);
        assert_eq!(associations_a[0].slot, PairSlotV2::First);
        assert!(matches!(
            associations_a[0].outcome,
            ForestNoteAssociationOutcomeV2::Recovered(_)
        ));
        assert_eq!(associations_a[1].slot, PairSlotV2::Second);
        assert!(matches!(
            associations_a[1].outcome,
            ForestNoteAssociationOutcomeV2::NotForViewingKey
        ));
        let associations_b = candidate_b
            .ingest_finalized_append_v2(transfer.clone(), Some(&secret_b))
            .unwrap();
        assert_eq!(associations_b.len(), 2);
        assert_eq!(associations_b[0].slot, PairSlotV2::First);
        assert!(matches!(
            associations_b[0].outcome,
            ForestNoteAssociationOutcomeV2::NotForViewingKey
        ));
        assert_eq!(associations_b[1].slot, PairSlotV2::Second);
        assert!(matches!(
            associations_b[1].outcome,
            ForestNoteAssociationOutcomeV2::Recovered(_)
        ));

        let checkpoint_one_point = FinalizedChainPointV1::new(205, [0xd7; 32]).unwrap();
        assert_eq!(
            checkpoint_inputs(&candidate_a),
            checkpoint_inputs(&candidate_b)
        );
        ingest_checkpoint(&mut candidate_a, checkpoint_one_point);
        ingest_checkpoint(&mut candidate_b, checkpoint_one_point);
        file_a.replace_state_v2(candidate_a.clone()).unwrap();
        file_b.replace_state_v2(candidate_b.clone()).unwrap();
        drop(file_a);
        drop(file_b);

        let file_a =
            DurableLaneForestWalletFileV2::open_or_create_v2(&path_a, initial.clone()).unwrap();
        let file_b = DurableLaneForestWalletFileV2::open_or_create_v2(&path_b, initial).unwrap();
        assert_eq!(file_a.state().checkpoint_count(), 2);
        assert_eq!(file_b.state().checkpoint_count(), 2);
        assert_eq!(
            file_a.state().finalized_head_v2(),
            Some(checkpoint_one_point)
        );
        assert_eq!(
            file_b.state().finalized_head_v2(),
            Some(checkpoint_one_point)
        );
        assert_eq!(
            file_a
                .state()
                .retained_checkpoint_sequence_at_point_v2(checkpoint_zero_point),
            Some(0)
        );
        assert_eq!(
            file_a
                .state()
                .retained_checkpoint_sequence_at_point_v2(checkpoint_one_point),
            Some(1)
        );
        assert_eq!(
            file_b
                .state()
                .retained_checkpoint_sequence_at_point_v2(checkpoint_zero_point),
            Some(0)
        );
        assert_eq!(
            file_b
                .state()
                .retained_checkpoint_sequence_at_point_v2(checkpoint_one_point),
            Some(1)
        );
        assert_eq!(file_a.state().master(), file_b.state().master());
        for lane_index in 0..8 {
            let lane_id = LaneIdV2::new(lane_index).unwrap();
            assert_eq!(
                file_a.state().lane(lane_id).0,
                file_b.state().lane(lane_id).0
            );
        }

        assert_eq!(file_a.state().lane(lane_zero).1.tracked().len(), 1);
        assert!(file_a.state().lane(lane_one).1.tracked().is_empty());
        assert_eq!(file_a.state().lane(lane_two).1.tracked().len(), 1);
        assert!(file_a.state().lane(lane_three).1.tracked().is_empty());
        assert!(file_b.state().lane(lane_zero).1.tracked().is_empty());
        assert_eq!(file_b.state().lane(lane_one).1.tracked().len(), 1);
        assert_eq!(file_b.state().lane(lane_two).1.tracked().len(), 1);
        assert!(file_b.state().lane(lane_three).1.tracked().is_empty());

        assert_eq!(file_a.state().tracked_outputs(lane_two).len(), 1);
        assert_eq!(file_b.state().tracked_outputs(lane_two).len(), 1);
        assert_eq!(
            file_a.state().tracked_outputs(lane_two)[0].output_event_id,
            recipient_event_id
        );
        assert_eq!(
            file_b.state().tracked_outputs(lane_two)[0].output_event_id,
            change_event_id
        );
        assert!(file_a
            .state()
            .lane(lane_zero)
            .1
            .tracked()
            .iter()
            .all(|witness| witness.root() == file_a.state().lane(lane_zero).0.value.tree.root));
        assert!(file_a
            .state()
            .lane(lane_two)
            .1
            .tracked()
            .iter()
            .all(|witness| witness.root() == file_a.state().lane(lane_two).0.value.tree.root));
        assert!(file_b
            .state()
            .lane(lane_one)
            .1
            .tracked()
            .iter()
            .all(|witness| witness.root() == file_b.state().lane(lane_one).0.value.tree.root));
        assert!(file_b
            .state()
            .lane(lane_two)
            .1
            .tracked()
            .iter()
            .all(|witness| witness.root() == file_b.state().lane(lane_two).0.value.tree.root));

        let mut replay_a = file_a.state().clone();
        assert!(replay_a
            .ingest_finalized_append_v2(transfer.clone(), Some(&secret_a))
            .unwrap()
            .is_empty());
        assert_eq!(&replay_a, file_a.state());
        let mut replay_b = file_b.state().clone();
        assert!(replay_b
            .ingest_finalized_append_v2(transfer, Some(&secret_b))
            .unwrap()
            .is_empty());
        assert_eq!(&replay_b, file_b.state());

        let mut malformed = forest_deposit_event(
            file_a.state(),
            lane_event(206, 0xd8, 0, 0),
            &out_of_order_note,
            out_of_order_commitment,
            &public_a,
            0xd0,
        );
        malformed.after_lane_image[0] ^= 1;
        let malformed_baseline = file_a.state().clone();
        let mut malformed_candidate = malformed_baseline.clone();
        assert_eq!(
            malformed_candidate
                .ingest_finalized_append_v2(malformed, Some(&secret_a))
                .err(),
            Some(LaneForestDurableErrorV2::InvalidEvent)
        );
        assert_eq!(malformed_candidate, malformed_baseline);
    }
}
