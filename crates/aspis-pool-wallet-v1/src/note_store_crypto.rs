//! Authenticated encryption for note openings retained by the durable wallet.
//!
//! The durable image stores these bytes opaquely.  This module pins one exact
//! envelope and binds it to the finalized event identity and access class, so
//! copying a ciphertext between records or flipping `ViewOnly` to `Spendable`
//! fails authentication.  Nullifier keys remain in a caller-supplied local key
//! store and are borrowed only through a zeroizing value.

use aspis_statement::decode_digest_canonical;
use chacha20poly1305::{
    aead::{Aead, KeyInit, Payload},
    XChaCha20Poly1305, XNonce,
};
use hpke::rand_core::CryptoRng;
use sha2::{Digest as _, Sha256};
use subtle::ConstantTimeEq;
use zeroize::{Zeroize, ZeroizeOnDrop};

use crate::{
    decode_note_plaintext_v1,
    durable_state::{LocalSpendAuthenticatorV1, SealedNoteAccessV1, SealedRecoveredNoteV1},
    encode_note_plaintext_v1,
    scan_state::DepositEventIdV1,
    wallet_transition::derive_note_nullifier_v1,
    NoteOpeningV1, PoolV1WalletError, POOL_V1_NOTE_PLAINTEXT_BYTES,
};

pub const POOL_V1_NOTE_STORE_MAGIC: [u8; 4] = *b"ASNS";
pub const POOL_V1_NOTE_STORE_VERSION: u8 = 1;
pub const POOL_V1_NOTE_STORE_FLAGS: u8 = 0;
pub const POOL_V1_NOTE_STORE_ALGORITHM_XCHACHA20_POLY1305: u8 = 1;
pub const POOL_V1_NOTE_STORE_NONCE_BYTES: usize = 24;
pub const POOL_V1_NOTE_STORE_TAG_BYTES: usize = 16;
pub const POOL_V1_NOTE_STORE_HEADER_BYTES: usize = 32;
pub const POOL_V1_NOTE_STORE_SEALED_BYTES: usize =
    POOL_V1_NOTE_STORE_HEADER_BYTES + POOL_V1_NOTE_PLAINTEXT_BYTES + POOL_V1_NOTE_STORE_TAG_BYTES;

const NOTE_STORE_CIPHER_ID_DOMAIN: &[u8] = b"aspis:pool-v1:note-store:xchacha20poly1305:key-id:v1";
const NOTE_STORE_AAD_DOMAIN: &[u8] = b"aspis:pool-v1:note-store:xchacha20poly1305:aad:v1";
const NOTE_STORE_EVENT_ID_BYTES: usize = 108;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NoteStoreCryptoErrorV1 {
    InvalidKey,
    WrongLength,
    WrongMagic,
    WrongVersion,
    WrongAlgorithm,
    NonZeroReserved,
    AuthenticationFailed,
    InvalidNullifierKey,
    Wallet(PoolV1WalletError),
}

impl From<PoolV1WalletError> for NoteStoreCryptoErrorV1 {
    fn from(error: PoolV1WalletError) -> Self {
        Self::Wallet(error)
    }
}

/// Uniformly random local note-store key.  The key is consumed on creation and
/// zeroized on drop.  It is never serialized by this crate.
#[derive(Zeroize, ZeroizeOnDrop)]
pub struct NoteStoreCipherV1 {
    key: [u8; 32],
    cipher_id: [u8; 32],
}

impl NoteStoreCipherV1 {
    pub fn from_key_bytes(mut key: [u8; 32]) -> Result<Self, NoteStoreCryptoErrorV1> {
        if key == [0u8; 32] {
            key.zeroize();
            return Err(NoteStoreCryptoErrorV1::InvalidKey);
        }
        let mut hasher = Sha256::new();
        hasher.update(NOTE_STORE_CIPHER_ID_DOMAIN);
        hasher.update(&key);
        let cipher_id = hasher.finalize().into();
        Ok(Self { key, cipher_id })
    }

    /// Identifier stored in `DurableWalletStateV1`.  It binds both the exact
    /// cipher profile and one local key generation without exposing the key.
    pub fn cipher_id(&self) -> [u8; 32] {
        self.cipher_id
    }
}

impl core::fmt::Debug for NoteStoreCipherV1 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str("NoteStoreCipherV1([REDACTED])")
    }
}

/// Ephemeral nullifier-key material returned by a protected local key store.
/// It is validated as one canonical Pool digest and zeroized on drop.
#[derive(Zeroize, ZeroizeOnDrop)]
pub struct NullifierKeyMaterialV1([u8; 32]);

impl NullifierKeyMaterialV1 {
    pub fn from_bytes(mut bytes: [u8; 32]) -> Result<Self, NoteStoreCryptoErrorV1> {
        if decode_digest_canonical(&bytes).is_err() {
            bytes.zeroize();
            return Err(NoteStoreCryptoErrorV1::InvalidNullifierKey);
        }
        Ok(Self(bytes))
    }

    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }
}

impl core::fmt::Debug for NullifierKeyMaterialV1 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str("NullifierKeyMaterialV1([REDACTED])")
    }
}

/// HSM, OS-keystore or wallet-secret boundary.  Implementations look up a key
/// by its public owner digest and return only a zeroizing ephemeral copy.
pub trait LocalNullifierKeyStoreV1 {
    fn nullifier_key_for_owner_v1(&self, owner_key: &[u8; 32]) -> Option<NullifierKeyMaterialV1>;
}

fn encode_event_id_v1(id: DepositEventIdV1) -> [u8; NOTE_STORE_EVENT_ID_BYTES] {
    let mut bytes = [0u8; NOTE_STORE_EVENT_ID_BYTES];
    bytes[..8].copy_from_slice(&id.point().slot().to_le_bytes());
    bytes[8..40].copy_from_slice(id.point().block_hash());
    bytes[40..104].copy_from_slice(id.transaction_signature());
    bytes[104..106].copy_from_slice(&id.instruction_index().to_le_bytes());
    bytes[106..108].copy_from_slice(&id.event_index().to_le_bytes());
    bytes
}

fn access_byte_v1(access: SealedNoteAccessV1) -> u8 {
    match access {
        SealedNoteAccessV1::ViewOnly => 0,
        SealedNoteAccessV1::Spendable => 1,
    }
}

fn aad_v1(
    cipher: &NoteStoreCipherV1,
    event_id: DepositEventIdV1,
    access: SealedNoteAccessV1,
) -> Vec<u8> {
    let mut aad = Vec::with_capacity(NOTE_STORE_AAD_DOMAIN.len() + 32 + 108 + 1);
    aad.extend_from_slice(NOTE_STORE_AAD_DOMAIN);
    aad.extend_from_slice(&cipher.cipher_id);
    aad.extend_from_slice(&encode_event_id_v1(event_id));
    aad.push(access_byte_v1(access));
    aad
}

pub fn seal_note_opening_v1(
    rng: &mut impl CryptoRng,
    cipher: &NoteStoreCipherV1,
    event_id: DepositEventIdV1,
    access: SealedNoteAccessV1,
    note: &NoteOpeningV1,
) -> Result<Vec<u8>, NoteStoreCryptoErrorV1> {
    let mut nonce = [0u8; POOL_V1_NOTE_STORE_NONCE_BYTES];
    rng.fill_bytes(&mut nonce);
    let aead_nonce = XNonce::from(nonce);
    let aad = aad_v1(cipher, event_id, access);
    let mut plaintext = encode_note_plaintext_v1(note);
    let aead = XChaCha20Poly1305::new_from_slice(&cipher.key)
        .map_err(|_| NoteStoreCryptoErrorV1::InvalidKey)?;
    let ciphertext = aead
        .encrypt(
            &aead_nonce,
            Payload {
                msg: &plaintext,
                aad: &aad,
            },
        )
        .map_err(|_| NoteStoreCryptoErrorV1::AuthenticationFailed);
    plaintext.zeroize();
    let ciphertext = ciphertext?;
    if ciphertext.len() != POOL_V1_NOTE_PLAINTEXT_BYTES + POOL_V1_NOTE_STORE_TAG_BYTES {
        return Err(NoteStoreCryptoErrorV1::AuthenticationFailed);
    }
    let mut output = Vec::with_capacity(POOL_V1_NOTE_STORE_SEALED_BYTES);
    output.extend_from_slice(&POOL_V1_NOTE_STORE_MAGIC);
    output.push(POOL_V1_NOTE_STORE_VERSION);
    output.push(POOL_V1_NOTE_STORE_FLAGS);
    output.push(POOL_V1_NOTE_STORE_ALGORITHM_XCHACHA20_POLY1305);
    output.push(0);
    output.extend_from_slice(&nonce);
    output.extend_from_slice(&ciphertext);
    debug_assert_eq!(output.len(), POOL_V1_NOTE_STORE_SEALED_BYTES);
    Ok(output)
}

pub fn seal_recovered_note_v1(
    rng: &mut impl CryptoRng,
    cipher: &NoteStoreCipherV1,
    event_id: DepositEventIdV1,
    access: SealedNoteAccessV1,
    note: &NoteOpeningV1,
) -> Result<SealedRecoveredNoteV1, NoteStoreCryptoErrorV1> {
    Ok(SealedRecoveredNoteV1 {
        event_id,
        access,
        sealed_note: seal_note_opening_v1(rng, cipher, event_id, access, note)?,
    })
}

pub fn open_note_opening_v1(
    cipher: &NoteStoreCipherV1,
    event_id: DepositEventIdV1,
    access: SealedNoteAccessV1,
    sealed: &[u8],
) -> Result<NoteOpeningV1, NoteStoreCryptoErrorV1> {
    if sealed.len() != POOL_V1_NOTE_STORE_SEALED_BYTES {
        return Err(NoteStoreCryptoErrorV1::WrongLength);
    }
    if sealed[..4] != POOL_V1_NOTE_STORE_MAGIC {
        return Err(NoteStoreCryptoErrorV1::WrongMagic);
    }
    if sealed[4] != POOL_V1_NOTE_STORE_VERSION || sealed[5] != POOL_V1_NOTE_STORE_FLAGS {
        return Err(NoteStoreCryptoErrorV1::WrongVersion);
    }
    if sealed[6] != POOL_V1_NOTE_STORE_ALGORITHM_XCHACHA20_POLY1305 {
        return Err(NoteStoreCryptoErrorV1::WrongAlgorithm);
    }
    if sealed[7] != 0 {
        return Err(NoteStoreCryptoErrorV1::NonZeroReserved);
    }
    let nonce =
        <&XNonce>::try_from(&sealed[8..32]).map_err(|_| NoteStoreCryptoErrorV1::WrongLength)?;
    let aad = aad_v1(cipher, event_id, access);
    let aead = XChaCha20Poly1305::new_from_slice(&cipher.key)
        .map_err(|_| NoteStoreCryptoErrorV1::InvalidKey)?;
    let mut plaintext = aead
        .decrypt(
            nonce,
            Payload {
                msg: &sealed[POOL_V1_NOTE_STORE_HEADER_BYTES..],
                aad: &aad,
            },
        )
        .map_err(|_| NoteStoreCryptoErrorV1::AuthenticationFailed)?;
    let decoded = decode_note_plaintext_v1(&plaintext).map_err(NoteStoreCryptoErrorV1::Wallet);
    plaintext.zeroize();
    decoded
}

/// Concrete durable-state spend authenticator.  The note opening is decrypted
/// under its exact event/access AAD, then a protected key store supplies the
/// matching nullifier key only long enough to recompute the public nullifier.
pub struct EncryptedLocalSpendAuthenticatorV1<'a, Store> {
    cipher: &'a NoteStoreCipherV1,
    key_store: &'a Store,
}

impl<'a, Store> EncryptedLocalSpendAuthenticatorV1<'a, Store> {
    pub fn new(cipher: &'a NoteStoreCipherV1, key_store: &'a Store) -> Self {
        Self { cipher, key_store }
    }
}

impl<Store: LocalNullifierKeyStoreV1> LocalSpendAuthenticatorV1
    for EncryptedLocalSpendAuthenticatorV1<'_, Store>
{
    fn authenticates_spend_v1(
        &self,
        input_event_id: DepositEventIdV1,
        sealed_note: &[u8],
        nullifier: &[u8; 32],
    ) -> bool {
        let Ok(note) = open_note_opening_v1(
            self.cipher,
            input_event_id,
            SealedNoteAccessV1::Spendable,
            sealed_note,
        ) else {
            return false;
        };
        let Some(key) = self.key_store.nullifier_key_for_owner_v1(note.owner_key()) else {
            return false;
        };
        let Ok(expected) = derive_note_nullifier_v1(&note, key.as_bytes()) else {
            return false;
        };
        bool::from(expected.ct_eq(nullifier))
    }
}

const _: () = assert!(POOL_V1_NOTE_STORE_SEALED_BYTES == 128);

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_statement::{derive_owner_key, encode_digest_canonical};
    use core::convert::Infallible;
    use hpke::rand_core::{TryCryptoRng, TryRng};

    use crate::scan_state::FinalizedChainPointV1;

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

    fn digest(seed: u32) -> [u8; 32] {
        let mut bytes = [0u8; 32];
        for (index, limb) in bytes.chunks_exact_mut(4).enumerate() {
            limb.copy_from_slice(&(seed + index as u32 * 17).to_le_bytes());
        }
        bytes
    }

    fn event(seed: u8) -> DepositEventIdV1 {
        DepositEventIdV1::new(
            FinalizedChainPointV1::new(100 + u64::from(seed), [seed; 32]).unwrap(),
            [seed.wrapping_add(1); 64],
            u16::from(seed),
            u16::from(seed) + 1,
        )
        .unwrap()
    }

    fn fixture() -> ([u8; 32], NoteOpeningV1) {
        let nullifier_key = digest(100);
        let decoded = decode_digest_canonical(&nullifier_key).unwrap();
        let owner = encode_digest_canonical(&derive_owner_key(&decoded));
        (
            nullifier_key,
            NoteOpeningV1::new(owner, 77, 9, digest(300)).unwrap(),
        )
    }

    #[test]
    fn exact_store_envelope_roundtrips_and_binds_key_event_access_and_bytes() {
        let (_, note) = fixture();
        let cipher = NoteStoreCipherV1::from_key_bytes([0x41; 32]).unwrap();
        let id = event(7);
        let sealed = seal_note_opening_v1(
            &mut FixedTestRng(0x80),
            &cipher,
            id,
            SealedNoteAccessV1::Spendable,
            &note,
        )
        .unwrap();
        let sealed_sha256: [u8; 32] = Sha256::digest(&sealed).into();
        assert_eq!(
            sealed_sha256,
            [
                0xb8, 0xa1, 0xf2, 0x34, 0x38, 0xd9, 0xb2, 0x13, 0x99, 0x64, 0x8a, 0xc9, 0xc6, 0x03,
                0x76, 0xe6, 0x7b, 0x43, 0xf3, 0x2c, 0x9a, 0xd0, 0xba, 0x91, 0xeb, 0xb3, 0x49, 0x34,
                0xab, 0xe9, 0xdf, 0x00,
            ]
        );
        assert_eq!(sealed.len(), 128);
        assert_eq!(&sealed[..8], b"ASNS\x01\x00\x01\x00");
        assert_eq!(&sealed[8..32], &(0x80u8..=0x97).collect::<Vec<_>>());

        let opened =
            open_note_opening_v1(&cipher, id, SealedNoteAccessV1::Spendable, &sealed).unwrap();
        assert_eq!(opened.owner_key(), note.owner_key());
        assert_eq!(opened.value(), note.value());
        assert_eq!(opened.asset_id(), note.asset_id());
        assert_eq!(opened.salt(), note.salt());

        assert_eq!(
            open_note_opening_v1(&cipher, event(8), SealedNoteAccessV1::Spendable, &sealed).err(),
            Some(NoteStoreCryptoErrorV1::AuthenticationFailed)
        );
        assert_eq!(
            open_note_opening_v1(&cipher, id, SealedNoteAccessV1::ViewOnly, &sealed).err(),
            Some(NoteStoreCryptoErrorV1::AuthenticationFailed)
        );
        let wrong_cipher = NoteStoreCipherV1::from_key_bytes([0x42; 32]).unwrap();
        assert_ne!(cipher.cipher_id(), wrong_cipher.cipher_id());
        assert_eq!(
            open_note_opening_v1(&wrong_cipher, id, SealedNoteAccessV1::Spendable, &sealed).err(),
            Some(NoteStoreCryptoErrorV1::AuthenticationFailed)
        );
        let mut changed = sealed;
        changed[64] ^= 1;
        assert_eq!(
            open_note_opening_v1(&cipher, id, SealedNoteAccessV1::Spendable, &changed).err(),
            Some(NoteStoreCryptoErrorV1::AuthenticationFailed)
        );
    }

    struct OneKeyStore {
        owner: [u8; 32],
        key: [u8; 32],
    }

    impl LocalNullifierKeyStoreV1 for OneKeyStore {
        fn nullifier_key_for_owner_v1(
            &self,
            owner_key: &[u8; 32],
        ) -> Option<NullifierKeyMaterialV1> {
            bool::from(self.owner.ct_eq(owner_key))
                .then(|| NullifierKeyMaterialV1::from_bytes(self.key).unwrap())
        }
    }

    #[test]
    fn encrypted_spend_authenticator_uses_local_key_and_rejects_substitution() {
        let (nullifier_key, note) = fixture();
        let cipher = NoteStoreCipherV1::from_key_bytes([0x51; 32]).unwrap();
        let id = event(9);
        let sealed = seal_note_opening_v1(
            &mut FixedTestRng(0x20),
            &cipher,
            id,
            SealedNoteAccessV1::Spendable,
            &note,
        )
        .unwrap();
        let expected = derive_note_nullifier_v1(&note, &nullifier_key).unwrap();
        let store = OneKeyStore {
            owner: *note.owner_key(),
            key: nullifier_key,
        };
        let authenticator = EncryptedLocalSpendAuthenticatorV1::new(&cipher, &store);
        assert!(authenticator.authenticates_spend_v1(id, &sealed, &expected));

        let mut wrong_nullifier = expected;
        wrong_nullifier[0] ^= 1;
        assert!(!authenticator.authenticates_spend_v1(id, &sealed, &wrong_nullifier));
        assert!(!authenticator.authenticates_spend_v1(event(10), &sealed, &expected));
        let mut changed = sealed;
        changed[127] ^= 1;
        assert!(!authenticator.authenticates_spend_v1(id, &changed, &expected));
    }
}
