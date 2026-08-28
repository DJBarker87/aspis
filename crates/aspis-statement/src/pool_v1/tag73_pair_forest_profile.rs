//! Shared bindings for the production-inactive eight-lane Pool Tag-73 profile.
//!
//! The release string commits the exact compiled terminal/masking inventories
//! as well as the ASQ8 -> ASF8 -> ASR8 transport.  Merely exposing these
//! constants does not activate a verifier or registry entry.

use aspis_core::HashFn;

use super::POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES;

pub const V7_POOL_PAIR_FOREST_TAG73_STATEMENT_DIGEST_DOMAIN: &[u8] =
    b"aspis/pool-v1/pair-forest8/asf8-statement-digest/v1";

pub const V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING_PREIMAGE: &[u8] =
    b"aspis:pool-v1:verifier-profile:tag73-pair-forest8-v1:asq8-asf8-asr8-v1";
pub const V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING: [u8; 32] = [
    0xa1, 0x79, 0xf8, 0xd7, 0xe3, 0x70, 0x24, 0xeb, 0x54, 0xe3, 0xdb, 0x17, 0xf3, 0x96, 0xb3, 0x98,
    0xa1, 0xbe, 0xb2, 0xda, 0x0c, 0x8b, 0xfa, 0xf6, 0x2b, 0x33, 0x5f, 0x2b, 0xa4, 0xea, 0x5c, 0x26,
];

pub const V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING_PREIMAGE: &[u8] =
    b"aspis:v7:pool-v1-pair-forest8:tag73:26c1-3c2:b10:q16:digest208:cap203:work35-31-34:asq8-asf8-asr8:active-df394a5a8554d09c:schedule-480809b836778dc6:mask-f9daf3d54f4285d1:release-v1";
pub const V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING: [u8; 32] = [
    0xad, 0xd0, 0x96, 0x63, 0xc6, 0xa5, 0x48, 0x38, 0x0e, 0x1a, 0x7e, 0x53, 0x94, 0xc8, 0x42, 0x6e,
    0x6e, 0x48, 0xba, 0xc2, 0x4a, 0x8c, 0x53, 0x6a, 0x04, 0x5f, 0xbf, 0x9d, 0xbe, 0x9f, 0xba, 0x1c,
];

/// Exact transcript statement digest for the fixed-size canonical ASF8 wire.
/// The generic ASVQ digest is intentionally limited to 640-byte payloads and
/// therefore is not reused for this distinct 1,880-byte profile.
pub fn v7_pool_pair_forest_tag73_statement_digest_v1(
    statement: &[u8; POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES],
    hash: HashFn,
) -> [u8; 32] {
    let version = [1u8];
    let length = (POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES as u32).to_le_bytes();
    hash(&[
        V7_POOL_PAIR_FOREST_TAG73_STATEMENT_DIGEST_DOMAIN,
        &version,
        &V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,
        &V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
        &length,
        statement,
    ])
}

#[cfg(test)]
mod tests {
    use super::*;
    use sha2::{Digest, Sha256};

    fn sha256(parts: &[&[u8]]) -> [u8; 32] {
        let mut hash = Sha256::new();
        for part in parts {
            hash.update(part);
        }
        hash.finalize().into()
    }

    #[test]
    fn bindings_are_exact_sha256_preimages() {
        assert_eq!(
            sha256(&[V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING_PREIMAGE]),
            V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,
        );
        assert_eq!(
            sha256(&[V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING_PREIMAGE]),
            V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
        );
        let zero = [0u8; POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES];
        assert_eq!(
            v7_pool_pair_forest_tag73_statement_digest_v1(&zero, sha256),
            sha256(&[
                V7_POOL_PAIR_FOREST_TAG73_STATEMENT_DIGEST_DOMAIN,
                &[1],
                &V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,
                &V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
                &(POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES as u32).to_le_bytes(),
                &zero,
            ]),
        );
    }
}
