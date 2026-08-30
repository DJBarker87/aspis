use aspis_core::field::P;
use aspis_pool_wallet_v1::{
    durable_state::{LocalSpendAuthenticatorV1, SealedNoteAccessV1},
    note_store_crypto::{
        open_note_opening_v1, seal_note_opening_v1, EncryptedLocalSpendAuthenticatorV1,
        LocalNullifierKeyStoreV1, NoteStoreCipherV1, NoteStoreCryptoErrorV1,
        NullifierKeyMaterialV1, POOL_V1_NOTE_STORE_ALGORITHM_XCHACHA20_POLY1305,
        POOL_V1_NOTE_STORE_FLAGS, POOL_V1_NOTE_STORE_HEADER_BYTES, POOL_V1_NOTE_STORE_MAGIC,
        POOL_V1_NOTE_STORE_NONCE_BYTES, POOL_V1_NOTE_STORE_SEALED_BYTES,
        POOL_V1_NOTE_STORE_VERSION,
    },
    scan_state::{DepositEventIdV1, FinalizedChainPointV1},
    wallet_transition::derive_note_nullifier_v1,
    NoteOpeningV1, PoolV1WalletError, POOL_V1_NOTE_DIGEST_ENCODING_VERSION,
    POOL_V1_NOTE_PLAINTEXT_BYTES, POOL_V1_NOTE_PLAINTEXT_MAGIC, POOL_V1_NOTE_PLAINTEXT_VERSION,
};
use aspis_statement::{
    decode_digest_canonical, derive_owner_key, encode_digest_canonical, VALUE_LIMIT,
};
use chacha20poly1305::{
    aead::{Aead, KeyInit, Payload},
    XChaCha20Poly1305, XNonce,
};
use core::{cell::Cell, convert::Infallible};
use hpke::rand_core::{TryCryptoRng, TryRng};

const NOTE_STORE_AAD_DOMAIN: &[u8] = b"aspis:pool-v1:note-store:xchacha20poly1305:aad:v1";

struct IncrementingTestRng(u8);

impl TryRng for IncrementingTestRng {
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

impl TryCryptoRng for IncrementingTestRng {}

struct BoundaryKeyStore {
    owner_key: [u8; 32],
    nullifier_key: [u8; 32],
    lookups: Cell<usize>,
}

impl LocalNullifierKeyStoreV1 for BoundaryKeyStore {
    fn nullifier_key_for_owner_v1(&self, owner_key: &[u8; 32]) -> Option<NullifierKeyMaterialV1> {
        self.lookups.set(self.lookups.get() + 1);
        (owner_key == &self.owner_key)
            .then(|| NullifierKeyMaterialV1::from_bytes(self.nullifier_key).unwrap())
    }
}

fn event(seed: u8) -> DepositEventIdV1 {
    DepositEventIdV1::new(
        FinalizedChainPointV1::new(1_000 + u64::from(seed), [seed; 32]).unwrap(),
        [seed.wrapping_add(1); 64],
        u16::from(seed),
        u16::from(seed) + 1,
    )
    .unwrap()
}

fn fixture() -> ([u8; 32], NoteOpeningV1) {
    let nullifier_key = [1u8; 32];
    let decoded = decode_digest_canonical(&nullifier_key).unwrap();
    let owner_key = encode_digest_canonical(&derive_owner_key(&decoded));
    (
        nullifier_key,
        NoteOpeningV1::new(owner_key, 77, 9, [2u8; 32]).unwrap(),
    )
}

fn event_bytes(event_id: DepositEventIdV1) -> [u8; 108] {
    let mut bytes = [0u8; 108];
    bytes[..8].copy_from_slice(&event_id.point().slot().to_le_bytes());
    bytes[8..40].copy_from_slice(event_id.point().block_hash());
    bytes[40..104].copy_from_slice(event_id.transaction_signature());
    bytes[104..106].copy_from_slice(&event_id.instruction_index().to_le_bytes());
    bytes[106..108].copy_from_slice(&event_id.event_index().to_le_bytes());
    bytes
}

fn store_aad(
    cipher: &NoteStoreCipherV1,
    event_id: DepositEventIdV1,
    access: SealedNoteAccessV1,
) -> Vec<u8> {
    let mut aad = Vec::with_capacity(NOTE_STORE_AAD_DOMAIN.len() + 32 + 108 + 1);
    aad.extend_from_slice(NOTE_STORE_AAD_DOMAIN);
    aad.extend_from_slice(&cipher.cipher_id());
    aad.extend_from_slice(&event_bytes(event_id));
    aad.push(match access {
        SealedNoteAccessV1::ViewOnly => 0,
        SealedNoteAccessV1::Spendable => 1,
    });
    aad
}

fn note_plaintext(note: &NoteOpeningV1) -> [u8; POOL_V1_NOTE_PLAINTEXT_BYTES] {
    let mut bytes = [0u8; POOL_V1_NOTE_PLAINTEXT_BYTES];
    bytes[..4].copy_from_slice(&POOL_V1_NOTE_PLAINTEXT_MAGIC);
    bytes[4] = POOL_V1_NOTE_PLAINTEXT_VERSION;
    bytes[5] = POOL_V1_NOTE_DIGEST_ENCODING_VERSION;
    bytes[8..40].copy_from_slice(note.owner_key());
    bytes[40..44].copy_from_slice(&note.value().to_le_bytes());
    bytes[44..48].copy_from_slice(&note.asset_id().to_le_bytes());
    bytes[48..80].copy_from_slice(note.salt());
    bytes
}

fn authenticated_envelope(
    raw_key: &[u8; 32],
    cipher: &NoteStoreCipherV1,
    event_id: DepositEventIdV1,
    access: SealedNoteAccessV1,
    nonce: [u8; POOL_V1_NOTE_STORE_NONCE_BYTES],
    plaintext: &[u8; POOL_V1_NOTE_PLAINTEXT_BYTES],
) -> Vec<u8> {
    let aead = XChaCha20Poly1305::new_from_slice(raw_key).unwrap();
    let ciphertext = aead
        .encrypt(
            &XNonce::from(nonce),
            Payload {
                msg: plaintext,
                aad: &store_aad(cipher, event_id, access),
            },
        )
        .unwrap();

    let mut sealed = Vec::with_capacity(POOL_V1_NOTE_STORE_SEALED_BYTES);
    sealed.extend_from_slice(&POOL_V1_NOTE_STORE_MAGIC);
    sealed.push(POOL_V1_NOTE_STORE_VERSION);
    sealed.push(POOL_V1_NOTE_STORE_FLAGS);
    sealed.push(POOL_V1_NOTE_STORE_ALGORITHM_XCHACHA20_POLY1305);
    sealed.push(0);
    sealed.extend_from_slice(&nonce);
    sealed.extend_from_slice(&ciphertext);
    assert!(sealed.len() == POOL_V1_NOTE_STORE_SEALED_BYTES);
    sealed
}

#[test]
fn local_keys_context_access_and_debug_are_fail_closed() {
    let (nullifier_key, note) = fixture();
    let id = event(7);
    let cipher = NoteStoreCipherV1::from_key_bytes([0x41; 32]).unwrap();
    let sealed = seal_note_opening_v1(
        &mut IncrementingTestRng(0x20),
        &cipher,
        id,
        SealedNoteAccessV1::Spendable,
        &note,
    )
    .unwrap();

    assert!(matches!(
        NoteStoreCipherV1::from_key_bytes([0u8; 32]),
        Err(NoteStoreCryptoErrorV1::InvalidKey)
    ));

    let wrong_cipher = NoteStoreCipherV1::from_key_bytes([0x42; 32]).unwrap();
    assert_eq!(
        open_note_opening_v1(&wrong_cipher, id, SealedNoteAccessV1::Spendable, &sealed).err(),
        Some(NoteStoreCryptoErrorV1::AuthenticationFailed)
    );
    assert_eq!(
        open_note_opening_v1(&cipher, event(8), SealedNoteAccessV1::Spendable, &sealed).err(),
        Some(NoteStoreCryptoErrorV1::AuthenticationFailed)
    );
    assert_eq!(
        open_note_opening_v1(&cipher, id, SealedNoteAccessV1::ViewOnly, &sealed).err(),
        Some(NoteStoreCryptoErrorV1::AuthenticationFailed)
    );

    let nullifier_material = NullifierKeyMaterialV1::from_bytes(nullifier_key).unwrap();
    assert!(format!("{cipher:?}") == "NoteStoreCipherV1([REDACTED])");
    assert!(format!("{nullifier_material:?}") == "NullifierKeyMaterialV1([REDACTED])");
    assert!(format!("{note:?}") == "NoteOpeningV1([REDACTED])");
}

#[test]
fn nullifier_key_is_requested_only_through_the_local_store_after_authentication() {
    let (nullifier_key, note) = fixture();
    let id = event(9);
    let cipher = NoteStoreCipherV1::from_key_bytes([0x49; 32]).unwrap();
    let expected_nullifier = derive_note_nullifier_v1(&note, &nullifier_key).unwrap();
    let spendable = seal_note_opening_v1(
        &mut IncrementingTestRng(0x30),
        &cipher,
        id,
        SealedNoteAccessV1::Spendable,
        &note,
    )
    .unwrap();
    let view_only = seal_note_opening_v1(
        &mut IncrementingTestRng(0x50),
        &cipher,
        id,
        SealedNoteAccessV1::ViewOnly,
        &note,
    )
    .unwrap();
    let store = BoundaryKeyStore {
        owner_key: *note.owner_key(),
        nullifier_key,
        lookups: Cell::new(0),
    };
    let authenticator = EncryptedLocalSpendAuthenticatorV1::new(&cipher, &store);

    assert!(authenticator.authenticates_spend_v1(id, &spendable, &expected_nullifier));
    assert!(store.lookups.get() == 1);

    assert!(!authenticator.authenticates_spend_v1(id, &view_only, &expected_nullifier));
    assert!(!authenticator.authenticates_spend_v1(event(10), &spendable, &expected_nullifier));
    assert!(store.lookups.get() == 1);
}

#[test]
fn framing_length_nonce_ciphertext_and_tag_tampering_are_rejected() {
    let (_, note) = fixture();
    let id = event(11);
    let cipher = NoteStoreCipherV1::from_key_bytes([0x51; 32]).unwrap();
    let sealed = seal_note_opening_v1(
        &mut IncrementingTestRng(0x60),
        &cipher,
        id,
        SealedNoteAccessV1::Spendable,
        &note,
    )
    .unwrap();

    for magic_index in 0..4 {
        let mut changed = sealed.clone();
        changed[magic_index] ^= 1;
        assert_eq!(
            open_note_opening_v1(&cipher, id, SealedNoteAccessV1::Spendable, &changed).err(),
            Some(NoteStoreCryptoErrorV1::WrongMagic)
        );
    }

    let framing_cases = [
        (4usize, NoteStoreCryptoErrorV1::WrongVersion),
        (5usize, NoteStoreCryptoErrorV1::WrongVersion),
        (6usize, NoteStoreCryptoErrorV1::WrongAlgorithm),
        (7usize, NoteStoreCryptoErrorV1::NonZeroReserved),
    ];
    for (index, expected) in framing_cases {
        let mut changed = sealed.clone();
        changed[index] ^= 1;
        assert_eq!(
            open_note_opening_v1(&cipher, id, SealedNoteAccessV1::Spendable, &changed).err(),
            Some(expected)
        );
    }

    for truncated_length in 0..sealed.len() {
        assert_eq!(
            open_note_opening_v1(
                &cipher,
                id,
                SealedNoteAccessV1::Spendable,
                &sealed[..truncated_length],
            )
            .err(),
            Some(NoteStoreCryptoErrorV1::WrongLength)
        );
    }
    let mut trailing = sealed.clone();
    trailing.push(0);
    assert_eq!(
        open_note_opening_v1(&cipher, id, SealedNoteAccessV1::Spendable, &trailing).err(),
        Some(NoteStoreCryptoErrorV1::WrongLength)
    );

    for index in 8..POOL_V1_NOTE_STORE_HEADER_BYTES {
        let mut changed = sealed.clone();
        changed[index] ^= 1;
        assert_eq!(
            open_note_opening_v1(&cipher, id, SealedNoteAccessV1::Spendable, &changed).err(),
            Some(NoteStoreCryptoErrorV1::AuthenticationFailed)
        );
    }
    for index in POOL_V1_NOTE_STORE_HEADER_BYTES..sealed.len() {
        let mut changed = sealed.clone();
        changed[index] ^= 1;
        assert_eq!(
            open_note_opening_v1(&cipher, id, SealedNoteAccessV1::Spendable, &changed).err(),
            Some(NoteStoreCryptoErrorV1::AuthenticationFailed)
        );
    }
}

#[test]
fn authenticated_noncanonical_plaintexts_are_rejected_after_opening() {
    let (_, note) = fixture();
    let id = event(21);
    let raw_key = [0x61; 32];
    let cipher = NoteStoreCipherV1::from_key_bytes(raw_key).unwrap();
    let base = note_plaintext(&note);

    let mut cases = Vec::new();

    let mut wrong_magic = base;
    wrong_magic[0] ^= 1;
    cases.push((
        wrong_magic,
        NoteStoreCryptoErrorV1::Wallet(PoolV1WalletError::InvalidPlaintext),
    ));

    let mut wrong_version = base;
    wrong_version[4] ^= 1;
    cases.push((
        wrong_version,
        NoteStoreCryptoErrorV1::Wallet(PoolV1WalletError::InvalidPlaintext),
    ));

    let mut wrong_digest_version = base;
    wrong_digest_version[5] ^= 1;
    cases.push((
        wrong_digest_version,
        NoteStoreCryptoErrorV1::Wallet(PoolV1WalletError::InvalidPlaintext),
    ));

    for reserved_index in 6..8 {
        let mut nonzero_reserved = base;
        nonzero_reserved[reserved_index] = 1;
        cases.push((
            nonzero_reserved,
            NoteStoreCryptoErrorV1::Wallet(PoolV1WalletError::InvalidPlaintext),
        ));
    }

    let mut noncanonical_owner = base;
    noncanonical_owner[8..12].copy_from_slice(&P.to_le_bytes());
    cases.push((
        noncanonical_owner,
        NoteStoreCryptoErrorV1::Wallet(PoolV1WalletError::NonCanonicalDigest),
    ));

    let mut out_of_range_value = base;
    out_of_range_value[40..44].copy_from_slice(&VALUE_LIMIT.to_le_bytes());
    cases.push((
        out_of_range_value,
        NoteStoreCryptoErrorV1::Wallet(PoolV1WalletError::ValueOutOfRange),
    ));

    let mut out_of_range_asset = base;
    out_of_range_asset[44..48].copy_from_slice(&P.to_le_bytes());
    cases.push((
        out_of_range_asset,
        NoteStoreCryptoErrorV1::Wallet(PoolV1WalletError::AssetIdOutOfRange),
    ));

    let mut noncanonical_salt = base;
    noncanonical_salt[48..52].copy_from_slice(&P.to_le_bytes());
    cases.push((
        noncanonical_salt,
        NoteStoreCryptoErrorV1::Wallet(PoolV1WalletError::NonCanonicalDigest),
    ));

    for (case_index, (plaintext, expected)) in cases.into_iter().enumerate() {
        let mut nonce = [0x80; POOL_V1_NOTE_STORE_NONCE_BYTES];
        nonce[POOL_V1_NOTE_STORE_NONCE_BYTES - 1] = case_index as u8;
        let sealed = authenticated_envelope(
            &raw_key,
            &cipher,
            id,
            SealedNoteAccessV1::Spendable,
            nonce,
            &plaintext,
        );
        assert_eq!(
            open_note_opening_v1(&cipher, id, SealedNoteAccessV1::Spendable, &sealed).err(),
            Some(expected)
        );
    }
}

#[test]
fn distinct_deterministic_nonces_produce_distinct_envelopes() {
    let (_, note) = fixture();
    let id = event(31);
    let cipher = NoteStoreCipherV1::from_key_bytes([0x71; 32]).unwrap();
    let mut rng = IncrementingTestRng(0xa0);
    let first =
        seal_note_opening_v1(&mut rng, &cipher, id, SealedNoteAccessV1::ViewOnly, &note).unwrap();
    let second =
        seal_note_opening_v1(&mut rng, &cipher, id, SealedNoteAccessV1::ViewOnly, &note).unwrap();

    assert!(
        first[8..POOL_V1_NOTE_STORE_HEADER_BYTES] != second[8..POOL_V1_NOTE_STORE_HEADER_BYTES]
    );
    assert!(first[POOL_V1_NOTE_STORE_HEADER_BYTES..] != second[POOL_V1_NOTE_STORE_HEADER_BYTES..]);
    assert!(first != second);
}
