//! Pool V1 semantic-format freeze.
//!
//! Pool V1 reuses the existing spendable note commitment, nullifier and
//! Merkle-node primitives byte-for-byte.  The constants below name those
//! already-versioned choices and provide fixed-width encodings for the asset
//! pool identity and stable verifier-registry policy.  They do not authorize a
//! verifier or mutate any program state by themselves.

use aspis_core::field::{M31, P};

use crate::{derive_nullifier, merkle_node_compress_v3, note_commitment, poseidon2::Digest};

use super::verifier_registry::{POOL_V1_VERIFIER_ENTRY_VERSION, POOL_V1_VERIFIER_REGISTRY_VERSION};

/// Format revision two replaces the never-deployed single-release verifier
/// binding with a stable multi-profile registry policy. Revision-one state
/// images must fail closed rather than be reinterpreted.
pub const POOL_V1_FORMAT_VERSION: u8 = 2;
/// Existing output/note format in which every output is an ordinary future
/// input leaf under the note domain.
pub const POOL_V1_NOTE_COMMITMENT_VERSION: u8 = 2;
/// Existing `DOMAIN_NULLIFIER` derivation used by the frozen spend relation.
pub const POOL_V1_NULLIFIER_FORMAT_VERSION: u8 = 1;
/// Existing fixed-arity Poseidon2-M31 node compression with the v3 tweak.
pub const POOL_V1_TREE_HASH_VERSION: u8 = 3;
/// Eight canonical little-endian M31 limbs in 32 bytes.
pub const POOL_V1_DIGEST_ENCODING_VERSION: u8 = 1;
pub const POOL_V1_TREE_DEPTH: usize = 20;
pub const POOL_V1_IDENTITY_VERSION: u8 = 1;
pub const POOL_V1_VERIFIER_POLICY_VERSION: u8 = 1;
pub const POOL_V1_ROOT_HISTORY_VERSION: u8 = 1;

/// Transcript/account-format record for the first Pool V1 slice.
///
/// Layout:
/// `magic[8] || pool || note || nullifier || tree-hash || digest || depth ||
/// history-log2 || identity || verifier-policy || registry || registry-entry
/// || tree-state || root-page || zero`.
/// Later protocol layers must use a new record rather than silently changing
/// one of these bytes.
pub const POOL_V1_FORMAT_BINDING: [u8; 32] = [
    b'A',
    b'S',
    b'P',
    b'P',
    b'O',
    b'O',
    b'L',
    b'1',
    POOL_V1_FORMAT_VERSION,
    POOL_V1_NOTE_COMMITMENT_VERSION,
    POOL_V1_NULLIFIER_FORMAT_VERSION,
    POOL_V1_TREE_HASH_VERSION,
    POOL_V1_DIGEST_ENCODING_VERSION,
    POOL_V1_TREE_DEPTH as u8,
    8, // log2(256 roots per history page)
    POOL_V1_IDENTITY_VERSION,
    POOL_V1_VERIFIER_POLICY_VERSION,
    POOL_V1_VERIFIER_REGISTRY_VERSION,
    POOL_V1_VERIFIER_ENTRY_VERSION,
    1, // incremental-tree state image version
    POOL_V1_ROOT_HISTORY_VERSION,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
];

pub const POOL_V1_IDENTITY_MAGIC: [u8; 4] = *b"ASPI";
pub const POOL_V1_IDENTITY_BYTES: usize = 144;
pub const POOL_V1_VERIFIER_POLICY_MAGIC: [u8; 4] = *b"ASPP";
pub const POOL_V1_VERIFIER_POLICY_BYTES: usize = 104;
pub const POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY: u8 = 1 << 0;
/// Select the distinct V2 registry/entry PDA family whose entries certify a
/// permanently immutable loader-v3 deployment and exact executable hash.
/// This bit was rejected by every earlier decoder, so accepting it does not
/// reinterpret any previously valid V1 policy image.
pub const POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT: u8 = 1 << 1;
pub const POOL_V1_VERIFIER_POLICY_FLAGS_MASK: u8 = POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY
    | POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1FormatError {
    WrongLength,
    WrongMagic,
    WrongVersion,
    NonZeroReserved,
    NonCanonicalAssetId,
    UnsupportedFlags,
    ZeroRequiredBinding,
    InvalidAuthorityMode,
}

/// Stable identity of one asset pool.
///
/// The M31 `asset_id` is the value already committed inside every note.  The
/// mint and token-program bytes pin the external asset represented by that
/// field element.  The pool address and deployment domain prevent the same
/// identity payload from being replayed into a sibling pool or deployment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolIdentityV1 {
    pub pool: [u8; 32],
    pub asset_mint: [u8; 32],
    pub token_program: [u8; 32],
    pub asset_id: M31,
    pub deployment_domain: [u8; 32],
}

/// Stable policy binding for a multi-profile verifier registry.
///
/// The Pool state never embeds one verifier release. `policy_binding` commits
/// the registry format, governance rules, statement fields and authenticated
/// verifier-result interface. Exact verifier/profile/release triples live in
/// canonical registry-entry accounts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifierPolicyV1 {
    pub flags: u8,
    pub registry_program: [u8; 32],
    pub registry_authority: [u8; 32],
    pub policy_binding: [u8; 32],
}

pub fn encode_pool_identity_v1(identity: &PoolIdentityV1) -> [u8; POOL_V1_IDENTITY_BYTES] {
    let mut output = [0u8; POOL_V1_IDENTITY_BYTES];
    output[..4].copy_from_slice(&POOL_V1_IDENTITY_MAGIC);
    output[4] = POOL_V1_IDENTITY_VERSION;
    output[8..40].copy_from_slice(&identity.pool);
    output[40..72].copy_from_slice(&identity.asset_mint);
    output[72..104].copy_from_slice(&identity.token_program);
    output[104..108].copy_from_slice(&identity.asset_id.to_le_bytes());
    output[112..144].copy_from_slice(&identity.deployment_domain);
    output
}

pub fn decode_pool_identity_v1(bytes: &[u8]) -> Result<PoolIdentityV1, PoolV1FormatError> {
    if bytes.len() != POOL_V1_IDENTITY_BYTES {
        return Err(PoolV1FormatError::WrongLength);
    }
    if bytes[..4] != POOL_V1_IDENTITY_MAGIC {
        return Err(PoolV1FormatError::WrongMagic);
    }
    if bytes[4] != POOL_V1_IDENTITY_VERSION {
        return Err(PoolV1FormatError::WrongVersion);
    }
    if bytes[5..8] != [0u8; 3] || bytes[108..112] != [0u8; 4] {
        return Err(PoolV1FormatError::NonZeroReserved);
    }
    let raw_asset_id = u32::from_le_bytes(bytes[104..108].try_into().unwrap());
    if raw_asset_id >= P {
        return Err(PoolV1FormatError::NonCanonicalAssetId);
    }
    Ok(PoolIdentityV1 {
        pool: bytes[8..40].try_into().unwrap(),
        asset_mint: bytes[40..72].try_into().unwrap(),
        token_program: bytes[72..104].try_into().unwrap(),
        asset_id: M31(raw_asset_id),
        deployment_domain: bytes[112..144].try_into().unwrap(),
    })
}

pub fn validate_verifier_policy_v1(policy: &VerifierPolicyV1) -> Result<(), PoolV1FormatError> {
    if policy.flags & !POOL_V1_VERIFIER_POLICY_FLAGS_MASK != 0 {
        return Err(PoolV1FormatError::UnsupportedFlags);
    }
    if policy.registry_program == [0u8; 32] || policy.policy_binding == [0u8; 32] {
        return Err(PoolV1FormatError::ZeroRequiredBinding);
    }
    let immutable = policy.flags & POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY != 0;
    let immutable_deployment =
        policy.flags & POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT != 0;
    if immutable_deployment && !immutable {
        return Err(PoolV1FormatError::InvalidAuthorityMode);
    }
    if immutable != (policy.registry_authority == [0u8; 32]) {
        return Err(PoolV1FormatError::InvalidAuthorityMode);
    }
    Ok(())
}

pub fn encode_verifier_policy_v1(
    policy: &VerifierPolicyV1,
) -> Result<[u8; POOL_V1_VERIFIER_POLICY_BYTES], PoolV1FormatError> {
    validate_verifier_policy_v1(policy)?;
    let mut output = [0u8; POOL_V1_VERIFIER_POLICY_BYTES];
    output[..4].copy_from_slice(&POOL_V1_VERIFIER_POLICY_MAGIC);
    output[4] = POOL_V1_VERIFIER_POLICY_VERSION;
    output[5] = policy.flags;
    output[8..40].copy_from_slice(&policy.registry_program);
    output[40..72].copy_from_slice(&policy.registry_authority);
    output[72..104].copy_from_slice(&policy.policy_binding);
    Ok(output)
}

pub fn decode_verifier_policy_v1(bytes: &[u8]) -> Result<VerifierPolicyV1, PoolV1FormatError> {
    if bytes.len() != POOL_V1_VERIFIER_POLICY_BYTES {
        return Err(PoolV1FormatError::WrongLength);
    }
    if bytes[..4] != POOL_V1_VERIFIER_POLICY_MAGIC {
        return Err(PoolV1FormatError::WrongMagic);
    }
    if bytes[4] != POOL_V1_VERIFIER_POLICY_VERSION {
        return Err(PoolV1FormatError::WrongVersion);
    }
    if bytes[6..8] != [0u8; 2] {
        return Err(PoolV1FormatError::NonZeroReserved);
    }
    let policy = VerifierPolicyV1 {
        flags: bytes[5],
        registry_program: bytes[8..40].try_into().unwrap(),
        registry_authority: bytes[40..72].try_into().unwrap(),
        policy_binding: bytes[72..104].try_into().unwrap(),
    };
    validate_verifier_policy_v1(&policy)?;
    Ok(policy)
}

/// Pool V1 note leaves are exactly the existing spendable note commitments.
pub fn pool_v1_note_commitment(
    owner_key: &Digest,
    value: u32,
    asset_id: M31,
    salt: &Digest,
) -> Digest {
    note_commitment(owner_key, value, asset_id, salt)
}

/// Pool V1 nullifiers are exactly the existing spend nullifier derivation.
pub fn pool_v1_nullifier(nullifier_key: &Digest, salt: &Digest) -> Digest {
    derive_nullifier(nullifier_key, salt)
}

/// Pool V1 internal nodes use the existing v3 fixed-arity compression.
#[inline]
pub fn pool_v1_tree_parent(left: &Digest, right: &Digest) -> Digest {
    merkle_node_compress_v3(left, right)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn identity() -> PoolIdentityV1 {
        PoolIdentityV1 {
            pool: [1u8; 32],
            asset_mint: [2u8; 32],
            token_program: [3u8; 32],
            asset_id: M31(4),
            deployment_domain: [5u8; 32],
        }
    }

    #[test]
    fn format_binding_pins_existing_primitives() {
        assert_eq!(&POOL_V1_FORMAT_BINDING[..8], b"ASPPOOL1");
        assert_eq!(
            POOL_V1_FORMAT_BINDING[8..21],
            [2, 2, 1, 3, 1, 20, 8, 1, 1, 1, 1, 1, 1]
        );

        let owner = digest(10);
        let salt = digest(100);
        let nullifier_key = digest(200);
        assert_eq!(
            pool_v1_note_commitment(&owner, 300, M31(400), &salt),
            note_commitment(&owner, 300, M31(400), &salt)
        );
        assert_eq!(
            pool_v1_nullifier(&nullifier_key, &salt),
            derive_nullifier(&nullifier_key, &salt)
        );
        assert_eq!(
            pool_v1_tree_parent(&owner, &salt),
            merkle_node_compress_v3(&owner, &salt)
        );
    }

    #[test]
    fn identity_encoding_is_fixed_width_canonical_and_fail_closed() {
        let original = identity();
        let encoded = encode_pool_identity_v1(&original);
        assert_eq!(encoded.len(), 144);
        assert_eq!(decode_pool_identity_v1(&encoded), Ok(original));

        let mut changed = encoded;
        changed[5] = 1;
        assert_eq!(
            decode_pool_identity_v1(&changed),
            Err(PoolV1FormatError::NonZeroReserved)
        );
        let mut changed = encoded;
        changed[104..108].copy_from_slice(&P.to_le_bytes());
        assert_eq!(
            decode_pool_identity_v1(&changed),
            Err(PoolV1FormatError::NonCanonicalAssetId)
        );
    }

    #[test]
    fn verifier_policy_is_fixed_width_canonical_and_rejects_old_binding_magic() {
        let policy = VerifierPolicyV1 {
            flags: 0,
            registry_program: [7u8; 32],
            registry_authority: [8u8; 32],
            policy_binding: [9u8; 32],
        };
        let encoded = encode_verifier_policy_v1(&policy).unwrap();
        assert_eq!(encoded.len(), 104);
        assert_eq!(decode_verifier_policy_v1(&encoded), Ok(policy));

        let mut old_binding_magic = encoded;
        old_binding_magic[..4].copy_from_slice(b"ASPV");
        assert_eq!(
            decode_verifier_policy_v1(&old_binding_magic),
            Err(PoolV1FormatError::WrongMagic)
        );

        let immutable = VerifierPolicyV1 {
            flags: POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY,
            registry_authority: [0u8; 32],
            ..policy
        };
        assert!(encode_verifier_policy_v1(&immutable).is_ok());
        assert!(encode_verifier_policy_v1(&VerifierPolicyV1 {
            flags: POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY
                | POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT,
            ..immutable
        })
        .is_ok());
        assert_eq!(
            encode_verifier_policy_v1(&VerifierPolicyV1 {
                flags: POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT,
                registry_authority: [8u8; 32],
                ..policy
            }),
            Err(PoolV1FormatError::InvalidAuthorityMode)
        );
        assert_eq!(
            encode_verifier_policy_v1(&VerifierPolicyV1 {
                registry_authority: [0u8; 32],
                ..policy
            }),
            Err(PoolV1FormatError::InvalidAuthorityMode)
        );
    }
}
