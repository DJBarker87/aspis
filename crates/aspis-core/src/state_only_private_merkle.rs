//! Domain-separated private Merkle leaves for state-only profile 21.
//!
//! The caller fixes the width of `value` from the profile/layout.  A fresh
//! hidden 32-byte salt belongs to one logical leaf and is disclosed only for
//! queried leaves.  Tree tags must be unique across committed oracles.

use crate::transcript::HashFn;

const DOM_LEAF: u8 = 0x10;

pub const STATE_ONLY_PRIVATE_LEAF_SALT_BYTES: usize = 32;

/// Hash a wire-contiguous `value || salt32` record with exactly two `hashv`
/// slices. The profile parser validates the fixed value width before calling
/// this function. This is byte-identical to [`private_leaf_hash`] and avoids
/// one SBF slice descriptor for every opened leaf.
#[inline]
pub fn private_leaf_hash_record(hash: HashFn, tree_tag: u8, value_and_salt: &[u8]) -> [u8; 32] {
    hash(&[&[DOM_LEAF, tree_tag], value_and_salt])
}

/// Hash one fixed-width private Merkle leaf as
/// `SHA256(0x10 || tree_tag || value || salt32)`.
///
/// Keeping the inputs as three slices avoids an allocation and is byte-exact
/// for both the host SHA-256 backend and Solana's `hashv` syscall.
#[inline]
pub fn private_leaf_hash(
    hash: HashFn,
    tree_tag: u8,
    value: &[u8],
    salt: &[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES],
) -> [u8; 32] {
    hash(&[&[DOM_LEAF, tree_tag], value, salt])
}

#[cfg(test)]
mod tests {
    use sha2::{Digest, Sha256};

    use super::*;

    fn test_hash(inputs: &[&[u8]]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        for input in inputs {
            hasher.update(input);
        }
        hasher.finalize().into()
    }

    #[test]
    fn private_leaf_hash_matches_independent_concatenation() {
        let value = core::array::from_fn::<_, 416, _>(|index| {
            (index as u8).wrapping_mul(73).wrapping_add(19)
        });
        let salt = core::array::from_fn(|index| (index as u8).wrapping_mul(29).wrapping_add(7));
        let actual = private_leaf_hash(test_hash, 0x31, &value, &salt);

        let mut independent = Sha256::new();
        independent.update([DOM_LEAF, 0x31]);
        independent.update(value);
        independent.update(salt);
        let expected: [u8; 32] = independent.finalize().into();
        assert_eq!(actual, expected);

        let mut record = [0u8; 448];
        record[..value.len()].copy_from_slice(&value);
        record[value.len()..].copy_from_slice(&salt);
        assert_eq!(private_leaf_hash_record(test_hash, 0x31, &record), actual);
        assert_eq!(
            actual,
            [
                0xdb, 0x5c, 0x38, 0x74, 0xf4, 0x84, 0x7f, 0x35, 0xee, 0xf4, 0x7a, 0x66, 0xa2, 0x63,
                0x96, 0xd9, 0xc9, 0x86, 0xb8, 0x46, 0xae, 0xd6, 0x18, 0x07, 0x33, 0xb6, 0x0a, 0x91,
                0xf4, 0x35, 0x56, 0x6a,
            ]
        );
    }

    #[test]
    fn tree_tag_value_and_salt_each_have_teeth() {
        let value = core::array::from_fn::<_, 256, _>(|index| {
            (index as u8).wrapping_mul(11).wrapping_add(3)
        });
        let salt = core::array::from_fn(|index| (index as u8).wrapping_mul(17).wrapping_add(5));
        let baseline = private_leaf_hash(test_hash, 0x42, &value, &salt);

        assert_ne!(baseline, private_leaf_hash(test_hash, 0x43, &value, &salt));

        let mut changed_value = value;
        changed_value[137] ^= 1;
        assert_ne!(
            baseline,
            private_leaf_hash(test_hash, 0x42, &changed_value, &salt)
        );

        let mut changed_salt = salt;
        changed_salt[23] ^= 1;
        assert_ne!(
            baseline,
            private_leaf_hash(test_hash, 0x42, &value, &changed_salt)
        );
    }
}
