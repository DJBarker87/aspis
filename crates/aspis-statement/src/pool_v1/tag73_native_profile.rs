//! Shared wire constants for the native Pool V1 Tag-73 payment profile.
//!
//! These values are consumed by the prover, wallet/operator request builder,
//! verifier program and registry configuration. Keeping one neutral source
//! prevents a byte-valid proof from being wrapped under duplicated or stale
//! profile/release bytes.

use aspis_core::v7_onefold::{
    V7_COMPACT_BODY_WITHOUT_FRONTIERS, V7_COMPACT_DIGEST_BYTES, V7_COMPACT_FRONTIER_CAP_PER_TREE,
};

use super::{POOL_V1_PAYMENT_STATEMENT_BYTES, POOL_V1_VERIFIER_DISPATCH_BINDING_PREFIX_BYTES};

pub const V7_POOL_NATIVE_TAG73_PROFILE_BINDING_PREIMAGE: &[u8] =
    b"aspis:pool-v1:verifier-profile:tag73-native-payment-v1:asvq-v1";
pub const V7_POOL_NATIVE_TAG73_PROFILE_BINDING: [u8; 32] = [
    0x70, 0xa7, 0x85, 0xea, 0x72, 0x34, 0x69, 0xa1, 0x34, 0x97, 0x40, 0x71, 0x62, 0xff, 0x01, 0xb5,
    0x5b, 0x33, 0x26, 0x87, 0xfd, 0x9d, 0x0a, 0x8c, 0x89, 0xb8, 0x12, 0x59, 0xb2, 0xd1, 0x96, 0x3d,
];

pub const V7_POOL_NATIVE_TAG73_RELEASE_BINDING_PREIMAGE: &[u8] =
    b"aspis:v7:pool-v1-payment:26c1-3c2:b10:q16:digest208:cap203:full-c2:work35-31-34:release-v1";
pub const V7_POOL_NATIVE_TAG73_RELEASE_BINDING: [u8; 32] = [
    0x9a, 0x29, 0x16, 0xf7, 0x65, 0x7b, 0x7b, 0x85, 0xa3, 0x51, 0x2d, 0x85, 0xd5, 0xa0, 0x58, 0x9c,
    0x19, 0xe7, 0x55, 0xca, 0x5e, 0x60, 0xd9, 0x10, 0x71, 0xb8, 0x0c, 0x2a, 0xf6, 0x2d, 0x0d, 0xff,
];

pub const V7_POOL_NATIVE_TAG73_REQUEST_BYTES: usize =
    POOL_V1_VERIFIER_DISPATCH_BINDING_PREFIX_BYTES + POOL_V1_PAYMENT_STATEMENT_BYTES;
/// Smallest binary authentication frontier for 16 distinct leaves in a
/// depth-18 tree (the 16 leaves form one complete depth-four subtree).
pub const V7_POOL_NATIVE_TAG73_MIN_FRONTIER_NODES: usize = 14;

pub const fn v7_pool_native_tag73_proof_body_bytes(frontier_nodes: usize) -> Option<u32> {
    if frontier_nodes < V7_POOL_NATIVE_TAG73_MIN_FRONTIER_NODES
        || frontier_nodes > V7_COMPACT_FRONTIER_CAP_PER_TREE
    {
        return None;
    }
    let bytes = V7_COMPACT_BODY_WITHOUT_FRONTIERS + 2 * frontier_nodes * V7_COMPACT_DIGEST_BYTES;
    Some(bytes as u32)
}

const _: () = assert!(V7_POOL_NATIVE_TAG73_REQUEST_BYTES == 600);
const _: () = assert!(V7_POOL_NATIVE_TAG73_MIN_FRONTIER_NODES == 14);
