//! Protocol-neutral radix-8 SHA-style Merkle primitives.
//!
//! This module is deliberately separate from the production radix-4 path.
//! A radix-8 tree has a different root and proof format: `binary_depth` must
//! be divisible by three, and every parent hashes eight ordered children in
//! one domain-separated invocation.

use alloc::vec::Vec;

use crate::transcript::HashFn;

/// Domain byte reserved for an eight-child Merkle parent.
///
/// This is distinct from the binary (`0x11`) and radix-4 (`0x12`) parent
/// domains. Changing arity therefore cannot silently reinterpret an existing
/// commitment root.
pub const DOM_NODE8: u8 = 0x13;

/// Hash eight ordered child digests as one radix-8 parent.
///
/// Packing the domain byte and all children into one buffer keeps the SBF
/// backend to one slice descriptor and one hash syscall per occupied parent.
pub fn node_hash8(hash: HashFn, children: &[[u8; 32]; 8]) -> [u8; 32] {
    let mut input = [0u8; 257];
    input[0] = DOM_NODE8;
    for (slot, child) in children.iter().enumerate() {
        input[1 + slot * 32..1 + (slot + 1) * 32].copy_from_slice(child);
    }
    hash(&[&input])
}

/// Verify a radix-8 deduplicated minimal-subtree proof.
///
/// `entries` must be sorted, unique `(leaf_index, leaf_hash)` pairs.
/// `node_bytes` contains the missing children as contiguous 32-byte hashes,
/// consumed level-by-level, then parent-index and child-slot order. The tree
/// contains `2^binary_depth` leaves, so `binary_depth` must be divisible by
/// three.
pub fn verify_radix8_minimal_subtree_bytes(
    hash: HashFn,
    root: &[u8; 32],
    binary_depth: u32,
    entries: &[(u32, [u8; 32])],
    node_bytes: &[u8],
    level: &mut Vec<(u32, [u8; 32])>,
    next: &mut Vec<(u32, [u8; 32])>,
) -> bool {
    if entries.is_empty() || binary_depth % 3 != 0 || node_bytes.len() & 31 != 0 {
        return false;
    }
    for pair in entries.windows(2) {
        if pair[0].0 >= pair[1].0 {
            return false;
        }
    }
    if binary_depth >= 32 || entries.last().unwrap().0 >= (1u32 << binary_depth) {
        return false;
    }

    level.clear();
    level.extend_from_slice(entries);
    verify_radix8_minimal_subtree_level_bytes(hash, root, binary_depth, node_bytes, level, next)
}

/// Verify a radix-8 frontier from caller-populated, already validated leaves.
///
/// This is useful when a proof parser has already established sortedness,
/// uniqueness, and range while decoding canonical leaf values. The function
/// still checks shape/framing conditions and consumes the full frontier.
pub(crate) fn verify_radix8_minimal_subtree_prevalidated_in_place(
    hash: HashFn,
    root: &[u8; 32],
    binary_depth: u32,
    node_bytes: &[u8],
    level: &mut Vec<(u32, [u8; 32])>,
    next: &mut Vec<(u32, [u8; 32])>,
) -> bool {
    if level.is_empty()
        || binary_depth % 3 != 0
        || binary_depth >= 32
        || node_bytes.len() & 31 != 0
        || level.last().unwrap().0 >= (1u32 << binary_depth)
    {
        return false;
    }
    verify_radix8_minimal_subtree_level_bytes(hash, root, binary_depth, node_bytes, level, next)
}

fn verify_radix8_minimal_subtree_level_bytes(
    hash: HashFn,
    root: &[u8; 32],
    binary_depth: u32,
    node_bytes: &[u8],
    level: &mut Vec<(u32, [u8; 32])>,
    next: &mut Vec<(u32, [u8; 32])>,
) -> bool {
    let mut node_pos = 0usize;
    for _ in 0..binary_depth / 3 {
        next.clear();
        let mut position = 0usize;
        while position < level.len() {
            let parent_index = level[position].0 >> 3;
            let mut children = [[0u8; 32]; 8];
            let mut present = 0u8;
            while position < level.len() && level[position].0 >> 3 == parent_index {
                let slot = (level[position].0 & 7) as usize;
                let slot_mask = 1u8 << slot;
                if present & slot_mask != 0 {
                    return false;
                }
                children[slot] = level[position].1;
                present |= slot_mask;
                position += 1;
            }
            for (slot, child) in children.iter_mut().enumerate() {
                if present & (1u8 << slot) == 0 {
                    if node_pos + 32 > node_bytes.len() {
                        return false;
                    }
                    *child = node_bytes[node_pos..node_pos + 32].try_into().unwrap();
                    node_pos += 32;
                }
            }
            next.push((parent_index, node_hash8(hash, &children)));
        }
        core::mem::swap(level, next);
    }

    node_pos == node_bytes.len() && level.len() == 1 && level[0].0 == 0 && level[0].1 == *root
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_hash(inputs: &[&[u8]]) -> [u8; 32] {
        use sha2::{Digest, Sha256};
        let mut hasher = Sha256::new();
        for input in inputs {
            hasher.update(input);
        }
        hasher.finalize().into()
    }

    #[test]
    fn node_hash8_pins_domain_and_order() {
        use sha2::{Digest, Sha256};

        let children: [[u8; 32]; 8] = core::array::from_fn(|slot| [slot as u8; 32]);
        let mut independent = Sha256::new();
        independent.update([DOM_NODE8]);
        for child in &children {
            independent.update(child);
        }
        let expected: [u8; 32] = independent.finalize().into();
        assert_eq!(node_hash8(test_hash, &children), expected);

        let mut swapped = children;
        swapped.swap(3, 4);
        assert_ne!(
            node_hash8(test_hash, &children),
            node_hash8(test_hash, &swapped)
        );
    }
}
