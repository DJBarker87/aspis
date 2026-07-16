//! Canonical public binding for the atomic same-private-path SpendV0 state
//! transition.
//!
//! Atomic-v4 proves that the spent input leaf and the output commitment use
//! one private Merkle path, taking `spend.anchor` to `output_anchor`. `sequence`
//! is the public pool-account revision checked by the eventual mutation path;
//! it is not the private leaf index. The public append-index construction
//! below is retained only as a separately rejected capacity candidate.

use aspis_core::{
    field::{M31, P},
    transcript::HashFn,
};

use crate::{
    poseidon2::{hash_merkle_node_sponge, Digest, DIGEST_ELEMS},
    spend::{SpendPublic, VALUE_LIMIT},
};

pub const ATOMIC_PAYMENT_TREE_DEPTH: usize = 20;
pub const ATOMIC_PAYMENT_STATEMENT_VERSION: u8 = 4;
pub const ATOMIC_PAYMENT_STATEMENT_PAYLOAD_BYTES: usize = 216;
pub const ATOMIC_PAYMENT_STATEMENT_DOMAIN: &[u8] = b"aspis/atomic-payment-statement/v4";
pub const ATOMIC_PAYMENT_EMPTY_LEAF: Digest = [M31::ZERO; DIGEST_ELEMS];
pub const ATOMIC_PAYMENT_STATEMENT_V4_KAT_EXPECTED: [u8; 32] = [
    0x47, 0x61, 0x3b, 0xf7, 0x1c, 0xb5, 0x3e, 0x9d, 0x99, 0xbf, 0x56, 0x48, 0x72, 0xde, 0xd5, 0xeb,
    0x38, 0x5b, 0x99, 0x59, 0x95, 0xde, 0xf6, 0x69, 0xfd, 0x5b, 0xe1, 0x29, 0x8e, 0x68, 0x90, 0x4f,
];
pub const ATOMIC_APPEND_CHAIN_DOMAIN: &[u8] = b"aspis/atomic-append-chain/v1";

/// Domain separator for the pool deployment-domain derivation:
/// `deployment_domain = sha256(DOMAIN || runtime_program_id || domain_tag)`.
pub const ATOMIC_DEPLOYMENT_DOMAIN_SEPARATOR: &[u8] = b"aspis-spend-deployment-domain-v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtomicPaymentStatementV4 {
    pub pool: [u8; 32],
    pub sequence: u64,
    pub spend: SpendPublic,
    pub output_anchor: Digest,
    /// The pool's deployment domain, `sha256(separator || runtime_program_id
    /// || domain_tag)`. Binding it into the statement digest makes every
    /// proof specific to one program deployment on one named cluster.
    pub deployment_domain: [u8; 32],
}

/// Compute the deployment domain bound by both the pool account and every
/// v4 statement: `sha256(separator || runtime_program_id || domain_tag)`.
pub fn atomic_deployment_domain(
    hash: HashFn,
    runtime_program_id: &[u8; 32],
    domain_tag: &[u8],
) -> [u8; 32] {
    hash(&[
        ATOMIC_DEPLOYMENT_DOMAIN_SEPARATOR,
        runtime_program_id,
        domain_tag,
    ])
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AtomicStatementError {
    NonCanonicalDigest,
    NonCanonicalAssetId,
    FeeOutOfRange,
    PathDepthMismatch,
    InsertionIndexOutOfRange,
    CurrentAnchorMismatch,
    OutputAnchorMismatch,
}

#[inline]
pub fn encode_digest_canonical(digest: &Digest) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    for (index, value) in digest.iter().enumerate() {
        bytes[index * 4..index * 4 + 4].copy_from_slice(&value.to_le_bytes());
    }
    bytes
}

pub fn decode_digest_canonical(bytes: &[u8; 32]) -> Result<Digest, AtomicStatementError> {
    let mut digest = [M31::ZERO; DIGEST_ELEMS];
    for (index, output) in digest.iter_mut().enumerate() {
        *output = M31::from_le_bytes(bytes[index * 4..index * 4 + 4].try_into().unwrap())
            .ok_or(AtomicStatementError::NonCanonicalDigest)?;
    }
    Ok(digest)
}

pub fn decode_asset_id_canonical(value: u32) -> Result<M31, AtomicStatementError> {
    if value >= P {
        return Err(AtomicStatementError::NonCanonicalAssetId);
    }
    Ok(M31(value))
}

#[inline]
fn merkle_parent(left: &Digest, right: &Digest) -> Digest {
    let mut input = [M31::ZERO; DIGEST_ELEMS * 2];
    input[..DIGEST_ELEMS].copy_from_slice(left);
    input[DIGEST_ELEMS..].copy_from_slice(right);
    hash_merkle_node_sponge(&input)
}

pub fn insertion_root(
    leaf: Digest,
    sequence: u64,
    siblings: &[Digest],
) -> Result<Digest, AtomicStatementError> {
    if siblings.len() != ATOMIC_PAYMENT_TREE_DEPTH {
        return Err(AtomicStatementError::PathDepthMismatch);
    }
    if sequence >= (1u64 << ATOMIC_PAYMENT_TREE_DEPTH) {
        return Err(AtomicStatementError::InsertionIndexOutOfRange);
    }
    let mut current = leaf;
    for (level, sibling) in siblings.iter().enumerate() {
        current = if (sequence >> level) & 1 == 0 {
            merkle_parent(&current, sibling)
        } else {
            merkle_parent(sibling, &current)
        };
    }
    Ok(current)
}

/// Rejected public-append candidate: check that `sequence` addresses an empty
/// leaf and replace it with `output_commitment`. Atomic-v4 does not call this;
/// its proof constrains a private same-path replacement instead.
pub fn verify_output_insertion(
    current_anchor: &Digest,
    output_commitment: &Digest,
    output_anchor: &Digest,
    sequence: u64,
    siblings: &[Digest],
) -> Result<(), AtomicStatementError> {
    if insertion_root(ATOMIC_PAYMENT_EMPTY_LEAF, sequence, siblings)? != *current_anchor {
        return Err(AtomicStatementError::CurrentAnchorMismatch);
    }
    if insertion_root(*output_commitment, sequence, siblings)? != *output_anchor {
        return Err(AtomicStatementError::OutputAnchorMismatch);
    }
    Ok(())
}

/// Fixed-width, canonical encoding hashed into the proof transcript.
///
/// Layout: `version || depth || zero[6] || pool || sequence_le || anchor ||
/// nullifier || output_commitment || output_anchor || asset_id_le || fee_le
/// || deployment_domain`.
pub fn encode_atomic_payment_statement_v4(
    statement: &AtomicPaymentStatementV4,
) -> Result<[u8; ATOMIC_PAYMENT_STATEMENT_PAYLOAD_BYTES], AtomicStatementError> {
    if statement.spend.asset_id.0 >= P {
        return Err(AtomicStatementError::NonCanonicalAssetId);
    }
    if statement.spend.fee >= VALUE_LIMIT {
        return Err(AtomicStatementError::FeeOutOfRange);
    }
    let mut output = [0u8; ATOMIC_PAYMENT_STATEMENT_PAYLOAD_BYTES];
    output[0] = ATOMIC_PAYMENT_STATEMENT_VERSION;
    output[1] = ATOMIC_PAYMENT_TREE_DEPTH as u8;
    output[8..40].copy_from_slice(&statement.pool);
    output[40..48].copy_from_slice(&statement.sequence.to_le_bytes());
    output[48..80].copy_from_slice(&encode_digest_canonical(&statement.spend.anchor));
    output[80..112].copy_from_slice(&encode_digest_canonical(&statement.spend.nullifier));
    output[112..144].copy_from_slice(&encode_digest_canonical(&statement.spend.output_commitment));
    output[144..176].copy_from_slice(&encode_digest_canonical(&statement.output_anchor));
    output[176..180].copy_from_slice(&statement.spend.asset_id.to_le_bytes());
    output[180..184].copy_from_slice(&statement.spend.fee.to_le_bytes());
    output[184..216].copy_from_slice(&statement.deployment_domain);
    Ok(output)
}

pub fn atomic_payment_statement_digest_v4(
    statement: &AtomicPaymentStatementV4,
    hash: HashFn,
) -> Result<[u8; 32], AtomicStatementError> {
    let payload = encode_atomic_payment_statement_v4(statement)?;
    Ok(hash(&[ATOMIC_PAYMENT_STATEMENT_DOMAIN, &payload]))
}

/// Constant-time append-chain control used only as a priced negative model.
///
/// It binds an append exactly, but by itself does not provide a logarithmic
/// membership witness for old leaves. It is therefore not a replacement for
/// the payment tree unless another hiding-preserving membership accumulator
/// is added.
pub fn atomic_append_chain_anchor(
    old_anchor: &[u8; 32],
    output_leaf: &Digest,
    index: u64,
    hash: HashFn,
) -> [u8; 32] {
    let leaf = encode_digest_canonical(output_leaf);
    let index = index.to_le_bytes();
    hash(&[ATOMIC_APPEND_CHAIN_DOMAIN, old_anchor, &leaf, &index])
}

#[cfg(test)]
mod tests {
    use sha2::{Digest as _, Sha256};

    use super::*;

    fn sha256(inputs: &[&[u8]]) -> [u8; 32] {
        let mut hash = Sha256::new();
        for input in inputs {
            hash.update(input);
        }
        hash.finalize().into()
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + index as u32 * 17))
    }

    fn statement() -> AtomicPaymentStatementV4 {
        AtomicPaymentStatementV4 {
            pool: [9u8; 32],
            sequence: 7,
            spend: SpendPublic {
                anchor: digest(10),
                nullifier: digest(20),
                output_commitment: digest(30),
                asset_id: M31(40),
                fee: 50,
            },
            output_anchor: digest(60),
            deployment_domain: [70u8; 32],
        }
    }

    #[test]
    fn canonical_digest_roundtrip_and_rejection() {
        let value = digest(123);
        assert_eq!(
            decode_digest_canonical(&encode_digest_canonical(&value)),
            Ok(value)
        );
        let mut bad = encode_digest_canonical(&value);
        bad[..4].copy_from_slice(&P.to_le_bytes());
        assert_eq!(
            decode_digest_canonical(&bad),
            Err(AtomicStatementError::NonCanonicalDigest)
        );
    }

    #[test]
    fn every_public_field_changes_the_statement_digest() {
        let original = statement();
        let expected = atomic_payment_statement_digest_v4(&original, sha256).unwrap();
        assert_eq!(expected, ATOMIC_PAYMENT_STATEMENT_V4_KAT_EXPECTED);
        let mut variants = alloc::vec::Vec::new();

        let mut changed = original.clone();
        changed.pool[0] ^= 1;
        variants.push(changed);
        let mut changed = original.clone();
        changed.sequence += 1;
        variants.push(changed);
        for selector in 0..4 {
            let mut changed = original.clone();
            let digest = match selector {
                0 => &mut changed.spend.anchor,
                1 => &mut changed.spend.nullifier,
                2 => &mut changed.spend.output_commitment,
                _ => &mut changed.output_anchor,
            };
            digest[0] = digest[0].add(M31::ONE);
            variants.push(changed);
        }
        let mut changed = original.clone();
        changed.spend.asset_id = changed.spend.asset_id.add(M31::ONE);
        variants.push(changed);
        let mut changed = original.clone();
        changed.spend.fee += 1;
        variants.push(changed);
        let mut changed = original;
        changed.deployment_domain[0] ^= 1;
        variants.push(changed);

        for variant in variants {
            assert_ne!(
                atomic_payment_statement_digest_v4(&variant, sha256).unwrap(),
                expected
            );
        }
    }

    #[test]
    fn empty_leaf_update_binds_both_roots() {
        let siblings: [Digest; ATOMIC_PAYMENT_TREE_DEPTH] =
            core::array::from_fn(|index| digest(1_000 + index as u32 * 31));
        let output = digest(777);
        let current = insertion_root(ATOMIC_PAYMENT_EMPTY_LEAF, 19, &siblings).unwrap();
        let next = insertion_root(output, 19, &siblings).unwrap();
        assert_eq!(
            verify_output_insertion(&current, &output, &next, 19, &siblings),
            Ok(())
        );
        let mut wrong = next;
        wrong[0] = wrong[0].add(M31::ONE);
        assert_eq!(
            verify_output_insertion(&current, &output, &wrong, 19, &siblings),
            Err(AtomicStatementError::OutputAnchorMismatch)
        );
    }

    #[test]
    fn output_is_a_future_input_leaf() {
        let owner = digest(2_001);
        let salt = digest(3_001);
        let value = 99;
        let asset = M31(7);
        assert_eq!(
            crate::note_commitment(&owner, value, asset, &salt),
            crate::output_commitment(&owner, value, asset, &salt),
            "atomic output leaves must be accepted by future input membership"
        );
    }

    #[test]
    fn append_chain_binds_old_root_leaf_and_index_but_not_membership() {
        let old = [0x42u8; 32];
        let leaf = digest(5_001);
        let anchor = atomic_append_chain_anchor(&old, &leaf, 9, sha256);
        let mut changed_old = old;
        changed_old[0] ^= 1;
        assert_ne!(
            atomic_append_chain_anchor(&changed_old, &leaf, 9, sha256),
            anchor
        );
        let mut changed_leaf = leaf;
        changed_leaf[0] = changed_leaf[0].add(M31::ONE);
        assert_ne!(
            atomic_append_chain_anchor(&old, &changed_leaf, 9, sha256),
            anchor
        );
        assert_ne!(atomic_append_chain_anchor(&old, &leaf, 10, sha256), anchor);

        // Recovering the final root for the first leaf requires replaying all
        // later leaves: the witness grows with the chain suffix, not log(n).
        let second = atomic_append_chain_anchor(&anchor, &digest(6_001), 10, sha256);
        let third = atomic_append_chain_anchor(&second, &digest(7_001), 11, sha256);
        assert_ne!(anchor, third);
        assert_eq!(
            atomic_append_chain_anchor(
                &atomic_append_chain_anchor(&anchor, &digest(6_001), 10, sha256),
                &digest(7_001),
                11,
                sha256,
            ),
            third
        );
    }
}
