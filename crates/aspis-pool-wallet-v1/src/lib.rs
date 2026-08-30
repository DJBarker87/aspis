//! Pool V1 encrypted-note envelope, recipient scan and durable scan cursor.
//!
//! This host-only crate is deliberately isolated from the on-chain Pool and
//! frozen verifier workspaces. It uses RFC 9180 HPKE base mode with the fixed
//! suite DHKEM(X25519, HKDF-SHA256), HKDF-SHA256 and ChaCha20-Poly1305. It
//! neither changes nor interprets the frozen Tag-73 proof wire.
//!
//! A recipient scan authenticates the Pool address, deployment domain, leaf
//! index, Pool format binding and public note commitment. A successful scan is
//! returned only after the decrypted note recomputes that exact commitment.

#![forbid(unsafe_code)]

pub mod durable_state;
pub mod durable_witness_state;
pub mod finalized_indexer;
#[cfg(feature = "eight-lane-plumbing-v2")]
pub mod lane_forest_checkpoint_operator_v2;
#[cfg(feature = "eight-lane-plumbing-v2")]
pub mod lane_forest_client_v2;
#[cfg(feature = "eight-lane-plumbing-v2")]
pub mod lane_forest_durable_v2;
#[cfg(feature = "eight-lane-plumbing-v2")]
pub mod lane_forest_rpc_v2;
#[cfg(feature = "eight-lane-plumbing-v2")]
pub mod lane_forest_transaction_v1;
#[cfg(feature = "eight-lane-plumbing-v2")]
pub mod lane_forest_tx_v1_simulation_v2;
#[cfg(feature = "eight-lane-plumbing-v2")]
pub mod lane_forest_v2;
#[cfg(feature = "eight-lane-plumbing-v2")]
pub mod lane_forest_wallet_txn_v2;
pub mod note_store_crypto;
pub mod operator_execution;
pub mod operator_startup;
pub mod pool_transport;
pub mod registry_transaction_builder;
pub mod relayer;
pub mod relayer_execution_journal;
pub mod relayer_execution_port;
pub mod relayer_finality_join;
pub mod relayer_finalized_evidence;
pub mod relayer_https_rpc;
pub mod relayer_rpc_composition;
pub mod relayer_rpc_json;
pub mod relayer_rpc_quorum;
pub mod relayer_rpc_request_id;
pub mod relayer_transaction;
#[cfg(unix)]
pub mod relayer_unix_signer;
pub mod rpc_adapter;
pub mod rpc_https_transport;
pub mod rpc_json;
pub mod rpc_json_quorum;
pub mod rpc_wire;
pub mod scan_state;
pub mod transaction_builder;
pub mod verifier_transaction_builder;
#[cfg(feature = "eight-lane-plumbing-v2")]
pub mod wallet_monotonic_v2;
#[cfg(feature = "eight-lane-plumbing-v2")]
pub mod wallet_populated_migration_v2;
pub mod wallet_store_migration_v2;
pub mod wallet_transition;
#[cfg(feature = "eight-lane-plumbing-v2")]
pub mod wallet_v2_activation;
#[cfg(feature = "eight-lane-plumbing-v2")]
pub mod wallet_v2_runtime;
pub mod witness_state;

use aspis_core::field::{M31, P};
use aspis_statement::{
    decode_digest_canonical, derive_owner_key, encode_digest_canonical,
    pool_v1::{
        pool_v1_note_commitment, POOL_V1_ENCRYPTED_NOTE_PAYLOAD_MAX_BYTES, POOL_V1_FORMAT_BINDING,
        POOL_V1_LEAF_CAPACITY,
    },
    VALUE_LIMIT,
};
use hpke::{
    aead::ChaCha20Poly1305, kdf::HkdfSha256, kem::X25519HkdfSha256, rand_core::CryptoRng,
    setup_receiver, setup_sender_with_rng, Deserializable, Kem as KemTrait, OpModeR, OpModeS,
    Serializable,
};
use subtle::ConstantTimeEq;
use zeroize::{Zeroize, ZeroizeOnDrop};

type WalletKem = X25519HkdfSha256;
type WalletKdf = HkdfSha256;
type WalletAead = ChaCha20Poly1305;

/// Application-level HPKE domain separator. The RFC ciphersuite identifiers
/// are also carried in the canonical envelope header.
pub const POOL_V1_NOTE_HPKE_INFO: &[u8] =
    b"aspis:pool-v1:note-envelope:hpke-base:x25519-hkdf-sha256:chacha20poly1305:v1";

pub const POOL_V1_NOTE_ENVELOPE_MAGIC: [u8; 4] = *b"ASNE";
pub const POOL_V1_NOTE_ENVELOPE_VERSION: u8 = 1;
pub const POOL_V1_NOTE_ENVELOPE_FLAGS: u8 = 0;
pub const POOL_V1_NOTE_HPKE_KEM_ID: u16 = 0x0020;
pub const POOL_V1_NOTE_HPKE_KDF_ID: u16 = 0x0001;
pub const POOL_V1_NOTE_HPKE_AEAD_ID: u16 = 0x0003;

pub const POOL_V1_NOTE_ENVELOPE_HEADER_BYTES: usize = 48;
pub const POOL_V1_NOTE_ENCAPSULATED_KEY_BYTES: usize = 32;
pub const POOL_V1_NOTE_PLAINTEXT_BYTES: usize = 80;
pub const POOL_V1_NOTE_AEAD_TAG_BYTES: usize = 16;
pub const POOL_V1_NOTE_CIPHERTEXT_BYTES: usize =
    POOL_V1_NOTE_PLAINTEXT_BYTES + POOL_V1_NOTE_AEAD_TAG_BYTES;
pub const POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES: usize =
    POOL_V1_NOTE_ENVELOPE_HEADER_BYTES + POOL_V1_NOTE_CIPHERTEXT_BYTES;

pub const POOL_V1_NOTE_PLAINTEXT_MAGIC: [u8; 4] = *b"ASPN";
pub const POOL_V1_NOTE_PLAINTEXT_VERSION: u8 = 1;
pub const POOL_V1_NOTE_DIGEST_ENCODING_VERSION: u8 = 1;

pub const POOL_V1_NOTE_CONTEXT_MAGIC: [u8; 4] = *b"ASNC";
pub const POOL_V1_NOTE_CONTEXT_VERSION: u8 = 1;
pub const POOL_V1_NOTE_CONTEXT_BYTES: usize = 144;

const ENVELOPE_KEM_OFFSET: usize = 6;
const ENVELOPE_KDF_OFFSET: usize = 8;
const ENVELOPE_AEAD_OFFSET: usize = 10;
const ENVELOPE_CIPHERTEXT_LENGTH_OFFSET: usize = 12;
const ENVELOPE_ENCAPSULATED_KEY_OFFSET: usize = 16;
const ENVELOPE_CIPHERTEXT_OFFSET: usize = POOL_V1_NOTE_ENVELOPE_HEADER_BYTES;

const PLAINTEXT_OWNER_KEY_OFFSET: usize = 8;
const PLAINTEXT_VALUE_OFFSET: usize = 40;
const PLAINTEXT_ASSET_ID_OFFSET: usize = 44;
const PLAINTEXT_SALT_OFFSET: usize = 48;

/// Fail-closed format and cryptographic errors. Authentication failure is not
/// an error: it maps to [`ScanResultV1::NotForViewingKey`] so a wallet can scan
/// unrelated ciphertexts without an exceptional control path.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1WalletError {
    InvalidViewingKey,
    InvalidContext,
    WrongEnvelopeLength,
    WrongEnvelopeMagic,
    WrongEnvelopeVersion,
    WrongHpkeSuite,
    NonZeroReserved,
    WrongCiphertextLength,
    HpkeSealFailed,
    InvalidPlaintext,
    NonCanonicalDigest,
    ValueOutOfRange,
    AssetIdOutOfRange,
    CommitmentMismatch,
}

/// Canonical serialized HPKE viewing public key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ViewingPublicKeyV1([u8; 32]);

impl ViewingPublicKeyV1 {
    pub fn from_bytes(bytes: [u8; 32]) -> Result<Self, PoolV1WalletError> {
        <WalletKem as KemTrait>::PublicKey::from_bytes(&bytes)
            .map_err(|_| PoolV1WalletError::InvalidViewingKey)?;
        Ok(Self(bytes))
    }

    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }
}

/// Canonical serialized HPKE viewing secret key. Its backing bytes are
/// zeroized on drop. Callers must protect and back up the input IKM separately.
#[derive(Zeroize, ZeroizeOnDrop)]
pub struct ViewingSecretKeyV1([u8; 32]);

impl ViewingSecretKeyV1 {
    pub fn from_bytes(mut bytes: [u8; 32]) -> Result<Self, PoolV1WalletError> {
        if <WalletKem as KemTrait>::PrivateKey::from_bytes(&bytes).is_err() {
            bytes.zeroize();
            return Err(PoolV1WalletError::InvalidViewingKey);
        }
        Ok(Self(bytes))
    }

    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }

    pub fn public_key(&self) -> Result<ViewingPublicKeyV1, PoolV1WalletError> {
        let secret = <WalletKem as KemTrait>::PrivateKey::from_bytes(&self.0)
            .map_err(|_| PoolV1WalletError::InvalidViewingKey)?;
        let public = WalletKem::sk_to_pk(&secret);
        let bytes = public.to_bytes();
        let mut output = [0u8; 32];
        output.copy_from_slice(bytes.as_slice());
        Ok(ViewingPublicKeyV1(output))
    }
}

impl core::fmt::Debug for ViewingSecretKeyV1 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str("ViewingSecretKeyV1([REDACTED])")
    }
}

/// Derive the exact RFC 9180 X25519 HPKE keypair from 32 bytes of input keying
/// material. The caller is responsible for supplying uniformly random,
/// wallet-domain-separated IKM and zeroizing it after this call.
pub fn derive_viewing_keypair_v1(
    ikm: &[u8; 32],
) -> Result<(ViewingSecretKeyV1, ViewingPublicKeyV1), PoolV1WalletError> {
    let (secret, public) = WalletKem::derive_keypair(ikm);
    let mut secret_serialized = secret.to_bytes();
    let public_serialized = public.to_bytes();

    let mut secret_bytes = [0u8; 32];
    secret_bytes.copy_from_slice(secret_serialized.as_slice());
    secret_serialized.as_mut_slice().zeroize();

    let mut public_bytes = [0u8; 32];
    public_bytes.copy_from_slice(public_serialized.as_slice());
    Ok((
        ViewingSecretKeyV1::from_bytes(secret_bytes)?,
        ViewingPublicKeyV1::from_bytes(public_bytes)?,
    ))
}

/// The note opening carried to a recipient. The `owner_key` is the public
/// commitment input that an output creator knows; the corresponding
/// nullifier/spending key never leaves the recipient wallet. Opening bytes,
/// value and asset id are zeroized on drop. This type deliberately does not
/// implement `Clone` or a value-revealing `Debug` formatter.
#[derive(Zeroize, ZeroizeOnDrop)]
pub struct NoteOpeningV1 {
    owner_key: [u8; 32],
    value: u32,
    asset_id: u32,
    salt: [u8; 32],
}

impl NoteOpeningV1 {
    pub fn new(
        mut owner_key: [u8; 32],
        mut value: u32,
        mut asset_id: u32,
        mut salt: [u8; 32],
    ) -> Result<Self, PoolV1WalletError> {
        let validation = validate_note_fields(&owner_key, value, asset_id, &salt);
        if let Err(error) = validation {
            owner_key.zeroize();
            value.zeroize();
            asset_id.zeroize();
            salt.zeroize();
            return Err(error);
        }
        Ok(Self {
            owner_key,
            value,
            asset_id,
            salt,
        })
    }

    pub fn owner_key(&self) -> &[u8; 32] {
        &self.owner_key
    }

    pub fn value(&self) -> u32 {
        self.value
    }

    pub fn asset_id(&self) -> u32 {
        self.asset_id
    }

    pub fn salt(&self) -> &[u8; 32] {
        &self.salt
    }
}

impl core::fmt::Debug for NoteOpeningV1 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str("NoteOpeningV1([REDACTED])")
    }
}

/// Public metadata authenticated as HPKE AAD. This binds a ciphertext to one
/// exact append position without changing the on-chain note commitment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NoteContextV1 {
    pool: [u8; 32],
    deployment_domain: [u8; 32],
    leaf_index: u64,
    note_commitment: [u8; 32],
}

impl NoteContextV1 {
    pub fn new(
        pool: [u8; 32],
        deployment_domain: [u8; 32],
        leaf_index: u64,
        note_commitment: [u8; 32],
    ) -> Result<Self, PoolV1WalletError> {
        if pool == [0u8; 32]
            || deployment_domain == [0u8; 32]
            || leaf_index >= POOL_V1_LEAF_CAPACITY
            || decode_digest_canonical(&note_commitment).is_err()
        {
            return Err(PoolV1WalletError::InvalidContext);
        }
        Ok(Self {
            pool,
            deployment_domain,
            leaf_index,
            note_commitment,
        })
    }

    pub fn pool(&self) -> &[u8; 32] {
        &self.pool
    }

    pub fn deployment_domain(&self) -> &[u8; 32] {
        &self.deployment_domain
    }

    pub fn leaf_index(&self) -> u64 {
        self.leaf_index
    }

    pub fn note_commitment(&self) -> &[u8; 32] {
        &self.note_commitment
    }
}

/// Encode the exact 144-byte HPKE AAD image.
pub fn encode_note_context_v1(context: &NoteContextV1) -> [u8; POOL_V1_NOTE_CONTEXT_BYTES] {
    let mut bytes = [0u8; POOL_V1_NOTE_CONTEXT_BYTES];
    bytes[..4].copy_from_slice(&POOL_V1_NOTE_CONTEXT_MAGIC);
    bytes[4] = POOL_V1_NOTE_CONTEXT_VERSION;
    bytes[5] = POOL_V1_NOTE_DIGEST_ENCODING_VERSION;
    bytes[8..40].copy_from_slice(&POOL_V1_FORMAT_BINDING);
    bytes[40..72].copy_from_slice(&context.pool);
    bytes[72..104].copy_from_slice(&context.deployment_domain);
    bytes[104..112].copy_from_slice(&context.leaf_index.to_le_bytes());
    bytes[112..144].copy_from_slice(&context.note_commitment);
    bytes
}

/// Recompute the frozen Pool V1 note commitment from decrypted wallet fields.
pub fn recompute_note_commitment_v1(note: &NoteOpeningV1) -> Result<[u8; 32], PoolV1WalletError> {
    let mut owner_key = decode_digest_canonical(&note.owner_key)
        .map_err(|_| PoolV1WalletError::NonCanonicalDigest)?;
    let mut salt =
        decode_digest_canonical(&note.salt).map_err(|_| PoolV1WalletError::NonCanonicalDigest)?;
    if note.value >= VALUE_LIMIT {
        return Err(PoolV1WalletError::ValueOutOfRange);
    }
    if note.asset_id >= P {
        return Err(PoolV1WalletError::AssetIdOutOfRange);
    }
    let commitment = pool_v1_note_commitment(&owner_key, note.value, M31(note.asset_id), &salt);
    owner_key.fill(M31(0));
    salt.fill(M31(0));
    Ok(encode_digest_canonical(&commitment))
}

/// Check whether a recovered view belongs to one local SpendV0
/// nullifier/spending key. This is deliberately separate from HPKE scanning:
/// a decrypted opening remains view-only until this local-only check succeeds.
/// The secret key is never returned or serialized.
pub fn note_matches_spending_key_v1(
    note: &NoteOpeningV1,
    nullifier_key: &[u8; 32],
) -> Result<bool, PoolV1WalletError> {
    let mut nullifier_key = decode_digest_canonical(nullifier_key)
        .map_err(|_| PoolV1WalletError::NonCanonicalDigest)?;
    let mut derived_owner_key = derive_owner_key(&nullifier_key);
    let derived_owner_key_bytes = encode_digest_canonical(&derived_owner_key);
    nullifier_key.fill(M31(0));
    derived_owner_key.fill(M31(0));
    Ok(bool::from(derived_owner_key_bytes.ct_eq(&note.owner_key)))
}

fn validate_note_fields(
    owner_key: &[u8; 32],
    value: u32,
    asset_id: u32,
    salt: &[u8; 32],
) -> Result<(), PoolV1WalletError> {
    if !digest_bytes_are_canonical(owner_key) || !digest_bytes_are_canonical(salt) {
        return Err(PoolV1WalletError::NonCanonicalDigest);
    }
    if value >= VALUE_LIMIT {
        return Err(PoolV1WalletError::ValueOutOfRange);
    }
    if asset_id >= P {
        return Err(PoolV1WalletError::AssetIdOutOfRange);
    }
    Ok(())
}

fn digest_bytes_are_canonical(bytes: &[u8; 32]) -> bool {
    bytes
        .chunks_exact(4)
        .all(|limb| u32::from_le_bytes(limb.try_into().unwrap()) < P)
}

pub(crate) fn encode_note_plaintext_v1(note: &NoteOpeningV1) -> [u8; POOL_V1_NOTE_PLAINTEXT_BYTES] {
    let mut bytes = [0u8; POOL_V1_NOTE_PLAINTEXT_BYTES];
    bytes[..4].copy_from_slice(&POOL_V1_NOTE_PLAINTEXT_MAGIC);
    bytes[4] = POOL_V1_NOTE_PLAINTEXT_VERSION;
    bytes[5] = POOL_V1_NOTE_DIGEST_ENCODING_VERSION;
    bytes[PLAINTEXT_OWNER_KEY_OFFSET..PLAINTEXT_VALUE_OFFSET].copy_from_slice(&note.owner_key);
    bytes[PLAINTEXT_VALUE_OFFSET..PLAINTEXT_ASSET_ID_OFFSET]
        .copy_from_slice(&note.value.to_le_bytes());
    bytes[PLAINTEXT_ASSET_ID_OFFSET..PLAINTEXT_SALT_OFFSET]
        .copy_from_slice(&note.asset_id.to_le_bytes());
    bytes[PLAINTEXT_SALT_OFFSET..].copy_from_slice(&note.salt);
    bytes
}

pub(crate) fn decode_note_plaintext_v1(bytes: &[u8]) -> Result<NoteOpeningV1, PoolV1WalletError> {
    if bytes.len() != POOL_V1_NOTE_PLAINTEXT_BYTES
        || bytes[..4] != POOL_V1_NOTE_PLAINTEXT_MAGIC
        || bytes[4] != POOL_V1_NOTE_PLAINTEXT_VERSION
        || bytes[5] != POOL_V1_NOTE_DIGEST_ENCODING_VERSION
        || bytes[6..8] != [0u8; 2]
    {
        return Err(PoolV1WalletError::InvalidPlaintext);
    }
    NoteOpeningV1::new(
        bytes[PLAINTEXT_OWNER_KEY_OFFSET..PLAINTEXT_VALUE_OFFSET]
            .try_into()
            .map_err(|_| PoolV1WalletError::InvalidPlaintext)?,
        u32::from_le_bytes(
            bytes[PLAINTEXT_VALUE_OFFSET..PLAINTEXT_ASSET_ID_OFFSET]
                .try_into()
                .map_err(|_| PoolV1WalletError::InvalidPlaintext)?,
        ),
        u32::from_le_bytes(
            bytes[PLAINTEXT_ASSET_ID_OFFSET..PLAINTEXT_SALT_OFFSET]
                .try_into()
                .map_err(|_| PoolV1WalletError::InvalidPlaintext)?,
        ),
        bytes[PLAINTEXT_SALT_OFFSET..]
            .try_into()
            .map_err(|_| PoolV1WalletError::InvalidPlaintext)?,
    )
}

/// Validate only canonical public envelope framing. The on-chain Pool keeps
/// treating these bytes as opaque; wallets call this before HPKE scanning.
pub fn validate_encrypted_note_payload_v1(payload: &[u8]) -> Result<(), PoolV1WalletError> {
    if payload.len() != POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES {
        return Err(PoolV1WalletError::WrongEnvelopeLength);
    }
    if payload[..4] != POOL_V1_NOTE_ENVELOPE_MAGIC {
        return Err(PoolV1WalletError::WrongEnvelopeMagic);
    }
    if payload[4] != POOL_V1_NOTE_ENVELOPE_VERSION || payload[5] != POOL_V1_NOTE_ENVELOPE_FLAGS {
        return Err(PoolV1WalletError::WrongEnvelopeVersion);
    }
    if u16::from_be_bytes(
        payload[ENVELOPE_KEM_OFFSET..ENVELOPE_KDF_OFFSET]
            .try_into()
            .unwrap(),
    ) != POOL_V1_NOTE_HPKE_KEM_ID
        || u16::from_be_bytes(
            payload[ENVELOPE_KDF_OFFSET..ENVELOPE_AEAD_OFFSET]
                .try_into()
                .unwrap(),
        ) != POOL_V1_NOTE_HPKE_KDF_ID
        || u16::from_be_bytes(
            payload[ENVELOPE_AEAD_OFFSET..ENVELOPE_CIPHERTEXT_LENGTH_OFFSET]
                .try_into()
                .unwrap(),
        ) != POOL_V1_NOTE_HPKE_AEAD_ID
    {
        return Err(PoolV1WalletError::WrongHpkeSuite);
    }
    if usize::from(u16::from_be_bytes(
        payload[ENVELOPE_CIPHERTEXT_LENGTH_OFFSET..14]
            .try_into()
            .unwrap(),
    )) != POOL_V1_NOTE_CIPHERTEXT_BYTES
    {
        return Err(PoolV1WalletError::WrongCiphertextLength);
    }
    if payload[14..16] != [0u8; 2] {
        return Err(PoolV1WalletError::NonZeroReserved);
    }
    Ok(())
}

/// Encrypt one fixed-size note opening using RFC 9180 HPKE base mode.
///
/// The caller supplies a CSPRNG explicitly. Encryption fails before sealing if
/// the note does not open the commitment carried by `context`.
pub fn encrypt_note_v1(
    csprng: &mut impl CryptoRng,
    recipient: &ViewingPublicKeyV1,
    context: &NoteContextV1,
    note: &NoteOpeningV1,
) -> Result<[u8; POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES], PoolV1WalletError> {
    let recomputed = recompute_note_commitment_v1(note)?;
    if !bool::from(recomputed.ct_eq(&context.note_commitment)) {
        return Err(PoolV1WalletError::CommitmentMismatch);
    }

    let recipient = <WalletKem as KemTrait>::PublicKey::from_bytes(&recipient.0)
        .map_err(|_| PoolV1WalletError::InvalidViewingKey)?;
    let (encapped_key, mut sender) = setup_sender_with_rng::<WalletAead, WalletKdf, WalletKem>(
        &OpModeS::Base,
        &recipient,
        POOL_V1_NOTE_HPKE_INFO,
        csprng,
    )
    .map_err(|_| PoolV1WalletError::HpkeSealFailed)?;

    let mut plaintext = encode_note_plaintext_v1(note);
    let aad = encode_note_context_v1(context);
    let ciphertext_result = sender.seal(&plaintext, &aad);
    plaintext.zeroize();
    let ciphertext = ciphertext_result.map_err(|_| PoolV1WalletError::HpkeSealFailed)?;
    if ciphertext.len() != POOL_V1_NOTE_CIPHERTEXT_BYTES {
        return Err(PoolV1WalletError::HpkeSealFailed);
    }

    let encapped_key = encapped_key.to_bytes();
    if encapped_key.len() != POOL_V1_NOTE_ENCAPSULATED_KEY_BYTES {
        return Err(PoolV1WalletError::HpkeSealFailed);
    }

    let mut payload = [0u8; POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES];
    payload[..4].copy_from_slice(&POOL_V1_NOTE_ENVELOPE_MAGIC);
    payload[4] = POOL_V1_NOTE_ENVELOPE_VERSION;
    payload[5] = POOL_V1_NOTE_ENVELOPE_FLAGS;
    payload[ENVELOPE_KEM_OFFSET..ENVELOPE_KDF_OFFSET]
        .copy_from_slice(&POOL_V1_NOTE_HPKE_KEM_ID.to_be_bytes());
    payload[ENVELOPE_KDF_OFFSET..ENVELOPE_AEAD_OFFSET]
        .copy_from_slice(&POOL_V1_NOTE_HPKE_KDF_ID.to_be_bytes());
    payload[ENVELOPE_AEAD_OFFSET..ENVELOPE_CIPHERTEXT_LENGTH_OFFSET]
        .copy_from_slice(&POOL_V1_NOTE_HPKE_AEAD_ID.to_be_bytes());
    payload[ENVELOPE_CIPHERTEXT_LENGTH_OFFSET..14]
        .copy_from_slice(&(POOL_V1_NOTE_CIPHERTEXT_BYTES as u16).to_be_bytes());
    payload[ENVELOPE_ENCAPSULATED_KEY_OFFSET..ENVELOPE_CIPHERTEXT_OFFSET]
        .copy_from_slice(encapped_key.as_slice());
    payload[ENVELOPE_CIPHERTEXT_OFFSET..].copy_from_slice(&ciphertext);

    Ok(payload)
}

/// Result of scanning one canonical Pool V1 encrypted-note payload.
pub enum ScanResultV1 {
    /// HPKE decapsulation/authentication failed. This is the normal result for
    /// an event addressed to another wallet or for tampered AAD/ciphertext.
    NotForViewingKey,
    /// HPKE opened and the plaintext recomputed the exact public commitment.
    /// This is view-only until [`note_matches_spending_key_v1`] succeeds for a
    /// key held in the wallet's local spend-key store.
    RecoveredView(NoteOpeningV1),
}

impl core::fmt::Debug for ScanResultV1 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::NotForViewingKey => formatter.write_str("NotForViewingKey"),
            Self::RecoveredView(_) => formatter.write_str("RecoveredView([REDACTED])"),
        }
    }
}

/// Attempt recipient scanning for one event. Structural envelope errors fail
/// closed; HPKE failure is a normal negative result; successful HPKE opening is
/// accepted only after canonical plaintext parsing and commitment recomputation.
pub fn scan_note_v1(
    viewing_secret: &ViewingSecretKeyV1,
    context: &NoteContextV1,
    payload: &[u8],
) -> Result<ScanResultV1, PoolV1WalletError> {
    validate_encrypted_note_payload_v1(payload)?;

    let secret = <WalletKem as KemTrait>::PrivateKey::from_bytes(&viewing_secret.0)
        .map_err(|_| PoolV1WalletError::InvalidViewingKey)?;
    let encapped_key = match <WalletKem as KemTrait>::EncappedKey::from_bytes(
        &payload[ENVELOPE_ENCAPSULATED_KEY_OFFSET..ENVELOPE_CIPHERTEXT_OFFSET],
    ) {
        Ok(value) => value,
        Err(_) => return Ok(ScanResultV1::NotForViewingKey),
    };
    let mut receiver = match setup_receiver::<WalletAead, WalletKdf, WalletKem>(
        &OpModeR::Base,
        &secret,
        &encapped_key,
        POOL_V1_NOTE_HPKE_INFO,
    ) {
        Ok(value) => value,
        Err(_) => return Ok(ScanResultV1::NotForViewingKey),
    };
    let aad = encode_note_context_v1(context);
    let mut plaintext = match receiver.open(&payload[ENVELOPE_CIPHERTEXT_OFFSET..], &aad) {
        Ok(value) => value,
        Err(_) => return Ok(ScanResultV1::NotForViewingKey),
    };
    let decoded = decode_note_plaintext_v1(&plaintext);
    plaintext.zeroize();
    let note = decoded?;
    let recomputed = recompute_note_commitment_v1(&note)?;
    if !bool::from(recomputed.ct_eq(&context.note_commitment)) {
        return Err(PoolV1WalletError::CommitmentMismatch);
    }
    Ok(ScanResultV1::RecoveredView(note))
}

const _: () = assert!(POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES == 144);
const _: () =
    assert!(POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES <= POOL_V1_ENCRYPTED_NOTE_PAYLOAD_MAX_BYTES);

#[cfg(test)]
mod tests {
    use super::*;
    use core::convert::Infallible;
    use hpke::rand_core::{TryCryptoRng, TryRng};

    // Deterministic and deliberately test-only. Production callers must pass
    // a real CSPRNG; this fake marker exists solely to pin interoperability
    // bytes and negative behavior.
    struct FixedTestRng {
        next: u8,
    }

    impl FixedTestRng {
        fn new(next: u8) -> Self {
            Self { next }
        }
    }

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
                *byte = self.next;
                self.next = self.next.wrapping_add(1);
            }
            Ok(())
        }
    }

    impl TryCryptoRng for FixedTestRng {}

    fn digest_bytes(seed: u32) -> [u8; 32] {
        let mut bytes = [0u8; 32];
        for index in 0..8 {
            bytes[index * 4..index * 4 + 4]
                .copy_from_slice(&(seed + 17 * index as u32).to_le_bytes());
        }
        bytes
    }

    fn hex(bytes: &[u8]) -> String {
        let mut output = String::with_capacity(bytes.len() * 2);
        for byte in bytes {
            use core::fmt::Write as _;
            write!(&mut output, "{byte:02x}").unwrap();
        }
        output
    }

    fn fixture() -> (
        ViewingSecretKeyV1,
        ViewingPublicKeyV1,
        NoteOpeningV1,
        NoteContextV1,
    ) {
        let (viewing_secret, viewing_public) = derive_viewing_keypair_v1(&[0x42; 32]).unwrap();
        let nullifier_key = decode_digest_canonical(&digest_bytes(100)).unwrap();
        let owner_key = encode_digest_canonical(&derive_owner_key(&nullifier_key));
        let note = NoteOpeningV1::new(owner_key, 77, 9, digest_bytes(300)).unwrap();
        let commitment = recompute_note_commitment_v1(&note).unwrap();
        let context = NoteContextV1::new([0x11; 32], [0x22; 32], 7, commitment).unwrap();
        (viewing_secret, viewing_public, note, context)
    }

    #[test]
    fn fixed_suite_known_answer_roundtrips_and_recomputes_commitment() {
        let (secret, public, note, context) = fixture();
        let payload =
            encrypt_note_v1(&mut FixedTestRng::new(0x80), &public, &context, &note).unwrap();

        assert_eq!(
            hex(public.as_bytes()),
            "ae3bf1cd87c2d2ed25af4a1a239eed04a990f00e7403e4c8065927de010fd17a"
        );
        assert_eq!(
            hex(&encode_note_context_v1(&context)),
            concat!(
                "41534e4301010000415350504f4f4c3102020103011408010101010101000000",
                "0000000000000000111111111111111111111111111111111111111111111111",
                "1111111111111111222222222222222222222222222222222222222222222222",
                "2222222222222222070000000000000066e1fd7e169a544d2c95577e19638f53",
                "8ba8ac3e984c24402ed68c57c16d2533"
            )
        );
        assert_eq!(
            hex(&payload),
            concat!(
                "41534e450100002000010003006000007af03df159e2d75751c1a88eb5a9e879",
                "88f138dce7596ebda3ad7f0bb04a8734550b2eb59794864ffbb80ab6961c750b",
                "c1c71d6e21ec3887ea0c6ac414df647715bc024c2e1c525fba0d7409d4693a4b",
                "abf03b2617bbf2d56c097e92dccf4e2397b526013ab5450b6930db68a9cc6254",
                "000f152b6ed97ef341276e381ef2533a"
            )
        );

        assert_eq!(payload.len(), 144);
        assert_eq!(&payload[..4], b"ASNE");
        assert_eq!(&payload[6..12], &[0, 0x20, 0, 1, 0, 3]);
        assert_eq!(&payload[12..16], &[0, 96, 0, 0]);
        assert!(payload.len() <= POOL_V1_ENCRYPTED_NOTE_PAYLOAD_MAX_BYTES);

        let recovered = match scan_note_v1(&secret, &context, &payload).unwrap() {
            ScanResultV1::RecoveredView(note) => note,
            ScanResultV1::NotForViewingKey => panic!("recipient failed to recover its note"),
        };
        assert_eq!(recovered.owner_key(), note.owner_key());
        assert_eq!(recovered.value(), 77);
        assert_eq!(recovered.asset_id(), 9);
        assert_eq!(recovered.salt(), note.salt());
        assert!(note_matches_spending_key_v1(&recovered, &digest_bytes(100)).unwrap());
        assert!(!note_matches_spending_key_v1(&recovered, &digest_bytes(101)).unwrap());
        assert_eq!(
            recompute_note_commitment_v1(&recovered).unwrap(),
            *context.note_commitment()
        );
    }

    #[test]
    fn wrong_key_context_or_ciphertext_is_a_deterministic_negative_scan() {
        let (secret, public, note, context) = fixture();
        let payload =
            encrypt_note_v1(&mut FixedTestRng::new(0x80), &public, &context, &note).unwrap();

        let (wrong_secret, _) = derive_viewing_keypair_v1(&[0x43; 32]).unwrap();
        assert!(matches!(
            scan_note_v1(&wrong_secret, &context, &payload).unwrap(),
            ScanResultV1::NotForViewingKey
        ));

        let wrong_contexts = [
            NoteContextV1::new(
                [0x12; 32],
                *context.deployment_domain(),
                context.leaf_index(),
                *context.note_commitment(),
            )
            .unwrap(),
            NoteContextV1::new(
                *context.pool(),
                [0x23; 32],
                context.leaf_index(),
                *context.note_commitment(),
            )
            .unwrap(),
            NoteContextV1::new(
                *context.pool(),
                *context.deployment_domain(),
                context.leaf_index() + 1,
                *context.note_commitment(),
            )
            .unwrap(),
            NoteContextV1::new(
                *context.pool(),
                *context.deployment_domain(),
                context.leaf_index(),
                digest_bytes(900),
            )
            .unwrap(),
        ];
        for wrong_context in wrong_contexts {
            assert!(matches!(
                scan_note_v1(&secret, &wrong_context, &payload).unwrap(),
                ScanResultV1::NotForViewingKey
            ));
        }

        let mut tampered = payload;
        tampered[POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES - 1] ^= 1;
        assert!(matches!(
            scan_note_v1(&secret, &context, &tampered).unwrap(),
            ScanResultV1::NotForViewingKey
        ));
    }

    #[test]
    fn framing_and_note_fields_fail_closed() {
        let (_, public, note, context) = fixture();
        let payload =
            encrypt_note_v1(&mut FixedTestRng::new(0x80), &public, &context, &note).unwrap();

        assert_eq!(
            validate_encrypted_note_payload_v1(&payload[..143]),
            Err(PoolV1WalletError::WrongEnvelopeLength)
        );
        let mut changed = payload;
        changed[4] = 2;
        assert_eq!(
            validate_encrypted_note_payload_v1(&changed),
            Err(PoolV1WalletError::WrongEnvelopeVersion)
        );
        let mut changed = payload;
        changed[11] = 2;
        assert_eq!(
            validate_encrypted_note_payload_v1(&changed),
            Err(PoolV1WalletError::WrongHpkeSuite)
        );
        let mut changed = payload;
        changed[14] = 1;
        assert_eq!(
            validate_encrypted_note_payload_v1(&changed),
            Err(PoolV1WalletError::NonZeroReserved)
        );

        let mut noncanonical = digest_bytes(100);
        noncanonical[..4].copy_from_slice(&P.to_le_bytes());
        assert!(matches!(
            NoteOpeningV1::new(noncanonical, 1, 1, digest_bytes(300)),
            Err(PoolV1WalletError::NonCanonicalDigest)
        ));
        assert!(matches!(
            NoteOpeningV1::new(digest_bytes(100), VALUE_LIMIT, 1, digest_bytes(300)),
            Err(PoolV1WalletError::ValueOutOfRange)
        ));
        assert!(matches!(
            NoteOpeningV1::new(digest_bytes(100), 1, P, digest_bytes(300)),
            Err(PoolV1WalletError::AssetIdOutOfRange)
        ));
    }

    #[test]
    fn encryption_refuses_a_note_that_does_not_open_the_bound_commitment() {
        let (_, public, note, context) = fixture();
        let other_note = NoteOpeningV1::new(digest_bytes(101), 77, 9, digest_bytes(300)).unwrap();
        assert!(matches!(
            encrypt_note_v1(&mut FixedTestRng::new(0x80), &public, &context, &other_note,),
            Err(PoolV1WalletError::CommitmentMismatch)
        ));
        assert_eq!(
            recompute_note_commitment_v1(&note).unwrap(),
            *context.note_commitment()
        );
    }

    #[test]
    fn plaintext_serializes_owner_key_never_nullifier_spending_secret() {
        let nullifier_key_bytes = digest_bytes(100);
        let nullifier_key = decode_digest_canonical(&nullifier_key_bytes).unwrap();
        let owner_key = encode_digest_canonical(&derive_owner_key(&nullifier_key));
        assert_ne!(owner_key, nullifier_key_bytes);

        let note = NoteOpeningV1::new(owner_key, 77, 9, digest_bytes(300)).unwrap();
        let plaintext = encode_note_plaintext_v1(&note);
        assert_eq!(
            &plaintext[PLAINTEXT_OWNER_KEY_OFFSET..PLAINTEXT_VALUE_OFFSET],
            owner_key.as_slice()
        );
        assert!(!plaintext
            .windows(nullifier_key_bytes.len())
            .any(|window| window == nullifier_key_bytes));
        assert!(note_matches_spending_key_v1(&note, &nullifier_key_bytes).unwrap());
        assert!(!note_matches_spending_key_v1(&note, &digest_bytes(101)).unwrap());
    }
}
