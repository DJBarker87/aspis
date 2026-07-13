//! Host builder for canonical state-only private Merkle openings.

use aspis_core::merkle::{node_hash, node_hash4};
use aspis_core::state_only_private_merkle::{
    private_leaf_hash, STATE_ONLY_PRIVATE_LEAF_SALT_BYTES,
};
use aspis_core::HashFn;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateOnlyPrivateOpeningBuildError {
    InvalidDepth { depth: u32 },
    InvalidValueWidth { width: usize },
    ValuesLengthMismatch { expected: usize, actual: usize },
    SaltCountMismatch { expected: usize, actual: usize },
    EmptyOpening,
    CountOutOfRange { count: usize },
    IndicesNotStrictlyIncreasing,
    LeafIndexOutOfRange { index: u32 },
    LengthOverflow,
    OpenedLeafDoesNotMatchTree { index: u32 },
}

pub struct StateOnlyPrivateMerkleTree {
    hash: HashFn,
    binary_depth: u32,
    tree_tag: u8,
    value_width: usize,
    levels: Vec<Vec<[u8; 32]>>,
}

impl Drop for StateOnlyPrivateMerkleTree {
    fn drop(&mut self) {
        for level in &mut self.levels {
            for node in level {
                for byte in node {
                    // SAFETY: the node is uniquely borrowed during drop.
                    unsafe { core::ptr::write_volatile(byte, 0) };
                }
            }
        }
        core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
    }
}

impl StateOnlyPrivateMerkleTree {
    pub fn binary_depth(&self) -> u32 {
        self.binary_depth
    }

    pub fn tree_tag(&self) -> u8 {
        self.tree_tag
    }

    pub fn value_width(&self) -> usize {
        self.value_width
    }

    pub fn leaf_count(&self) -> usize {
        self.levels[0].len()
    }

    pub fn root(&self) -> [u8; 32] {
        self.levels.last().unwrap()[0]
    }

    /// Canonical frontier order consumed by the in-core
    /// radix-4/binary-cap verifier.
    pub fn frontier(
        &self,
        expected_sorted_indices: &[u32],
    ) -> Result<Vec<[u8; 32]>, StateOnlyPrivateOpeningBuildError> {
        validate_indices(self.binary_depth, expected_sorted_indices)?;
        let mut frontier = Vec::new();
        let mut current = expected_sorted_indices.to_vec();
        for level in &self.levels[..self.levels.len() - 1] {
            if level.len() == 2 {
                if current.len() == 1 {
                    frontier.push(level[(current[0] ^ 1) as usize]);
                }
                current.clear();
                current.push(0);
                continue;
            }
            let mut next = Vec::new();
            let mut position = 0usize;
            while position < current.len() {
                let parent = current[position] >> 2;
                let mut present = 0u8;
                while position < current.len() && current[position] >> 2 == parent {
                    present |= 1u8 << (current[position] & 3);
                    position += 1;
                }
                for slot in 0..4u32 {
                    if present & (1u8 << slot) == 0 {
                        frontier.push(level[(4 * parent + slot) as usize]);
                    }
                }
                next.push(parent);
            }
            current = next;
        }
        Ok(frontier)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BuiltStateOnlyPrivateOpening {
    pub bytes: Vec<u8>,
    pub frontier_nodes: usize,
}

fn checked_leaf_count(binary_depth: u32) -> Result<usize, StateOnlyPrivateOpeningBuildError> {
    if binary_depth >= 32 || binary_depth >= usize::BITS {
        return Err(StateOnlyPrivateOpeningBuildError::InvalidDepth {
            depth: binary_depth,
        });
    }
    Ok(1usize << binary_depth)
}

fn validate_indices(
    binary_depth: u32,
    indices: &[u32],
) -> Result<(), StateOnlyPrivateOpeningBuildError> {
    let leaf_count = checked_leaf_count(binary_depth)?;
    if indices.is_empty() {
        return Err(StateOnlyPrivateOpeningBuildError::EmptyOpening);
    }
    if indices.len() > u16::MAX as usize {
        return Err(StateOnlyPrivateOpeningBuildError::CountOutOfRange {
            count: indices.len(),
        });
    }
    for pair in indices.windows(2) {
        if pair[0] >= pair[1] {
            return Err(StateOnlyPrivateOpeningBuildError::IndicesNotStrictlyIncreasing);
        }
    }
    if let Some(&index) = indices.iter().find(|&&index| index as usize >= leaf_count) {
        return Err(StateOnlyPrivateOpeningBuildError::LeafIndexOutOfRange { index });
    }
    Ok(())
}

fn value_at<'a>(values: &'a [u8], value_width: usize, index: usize) -> Option<&'a [u8]> {
    let start = index.checked_mul(value_width)?;
    values.get(start..start.checked_add(value_width)?)
}

/// Build a canonical `2^binary_depth` radix-4 tree with an optional binary
/// cap. Leaf nodes are salted once with `private_leaf_hash`; there is no
/// second leaf-hash layer.
pub fn build_state_only_private_merkle_tree(
    hash: HashFn,
    binary_depth: u32,
    tree_tag: u8,
    value_width: usize,
    values: &[u8],
    salts: &[[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]],
) -> Result<StateOnlyPrivateMerkleTree, StateOnlyPrivateOpeningBuildError> {
    let leaf_count = checked_leaf_count(binary_depth)?;
    if value_width == 0 {
        return Err(StateOnlyPrivateOpeningBuildError::InvalidValueWidth { width: value_width });
    }
    let expected_values = leaf_count
        .checked_mul(value_width)
        .ok_or(StateOnlyPrivateOpeningBuildError::LengthOverflow)?;
    if values.len() != expected_values {
        return Err(StateOnlyPrivateOpeningBuildError::ValuesLengthMismatch {
            expected: expected_values,
            actual: values.len(),
        });
    }
    if salts.len() != leaf_count {
        return Err(StateOnlyPrivateOpeningBuildError::SaltCountMismatch {
            expected: leaf_count,
            actual: salts.len(),
        });
    }

    let mut levels = vec![(0..leaf_count)
        .map(|index| {
            private_leaf_hash(
                hash,
                tree_tag,
                value_at(values, value_width, index).unwrap(),
                &salts[index],
            )
        })
        .collect::<Vec<_>>()];
    while levels.last().unwrap().len() > 1 {
        let previous = levels.last().unwrap();
        let next = if previous.len() == 2 {
            vec![node_hash(hash, &previous[0], &previous[1])]
        } else {
            previous
                .chunks_exact(4)
                .map(|children| node_hash4(hash, children.try_into().unwrap()))
                .collect()
        };
        levels.push(next);
    }
    Ok(StateOnlyPrivateMerkleTree {
        hash,
        binary_depth,
        tree_tag,
        value_width,
        levels,
    })
}

/// Serialize one opening as
/// `count_u16 || (value || salt32)^count || frontier_count_u32 || frontier`.
/// Indices are supplied by the transcript and are not proof bytes.
pub fn serialize_state_only_private_opening(
    tree: &StateOnlyPrivateMerkleTree,
    values: &[u8],
    salts: &[[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]],
    expected_sorted_indices: &[u32],
) -> Result<BuiltStateOnlyPrivateOpening, StateOnlyPrivateOpeningBuildError> {
    validate_indices(tree.binary_depth, expected_sorted_indices)?;
    let expected_values = tree
        .leaf_count()
        .checked_mul(tree.value_width)
        .ok_or(StateOnlyPrivateOpeningBuildError::LengthOverflow)?;
    if values.len() != expected_values {
        return Err(StateOnlyPrivateOpeningBuildError::ValuesLengthMismatch {
            expected: expected_values,
            actual: values.len(),
        });
    }
    if salts.len() != tree.leaf_count() {
        return Err(StateOnlyPrivateOpeningBuildError::SaltCountMismatch {
            expected: tree.leaf_count(),
            actual: salts.len(),
        });
    }

    for &index in expected_sorted_indices {
        let index = index as usize;
        let digest = private_leaf_hash(
            tree.hash,
            tree.tree_tag,
            value_at(values, tree.value_width, index).unwrap(),
            &salts[index],
        );
        if digest != tree.levels[0][index] {
            return Err(
                StateOnlyPrivateOpeningBuildError::OpenedLeafDoesNotMatchTree {
                    index: index as u32,
                },
            );
        }
    }

    let frontier = tree.frontier(expected_sorted_indices)?;
    let record_width = tree
        .value_width
        .checked_add(STATE_ONLY_PRIVATE_LEAF_SALT_BYTES)
        .ok_or(StateOnlyPrivateOpeningBuildError::LengthOverflow)?;
    let records_len = expected_sorted_indices
        .len()
        .checked_mul(record_width)
        .ok_or(StateOnlyPrivateOpeningBuildError::LengthOverflow)?;
    let frontier_len = frontier
        .len()
        .checked_mul(32)
        .ok_or(StateOnlyPrivateOpeningBuildError::LengthOverflow)?;
    let capacity = 2usize
        .checked_add(records_len)
        .and_then(|value| value.checked_add(4))
        .and_then(|value| value.checked_add(frontier_len))
        .ok_or(StateOnlyPrivateOpeningBuildError::LengthOverflow)?;
    let mut bytes = Vec::with_capacity(capacity);
    bytes.extend_from_slice(&(expected_sorted_indices.len() as u16).to_le_bytes());
    for &index in expected_sorted_indices {
        let index = index as usize;
        bytes.extend_from_slice(value_at(values, tree.value_width, index).unwrap());
        bytes.extend_from_slice(&salts[index]);
    }
    bytes.extend_from_slice(&(frontier.len() as u32).to_le_bytes());
    for node in &frontier {
        bytes.extend_from_slice(node);
    }
    Ok(BuiltStateOnlyPrivateOpening {
        bytes,
        frontier_nodes: frontier.len(),
    })
}

#[cfg(test)]
mod tests {
    use aspis_core::state_only_private_openings::{
        verify_state_only_private_opening, verify_state_only_private_opening_from_proof,
        StateOnlyPrivateOpeningError,
    };

    use super::*;
    use crate::HOST_HASH;

    const DEPTH: u32 = 5;
    const WIDTH: usize = 64;
    const TAG: u8 = 0x71;
    const INDICES: [u32; 3] = [1, 7, 30];

    fn fixture() -> (
        Vec<u8>,
        Vec<[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]>,
        StateOnlyPrivateMerkleTree,
        BuiltStateOnlyPrivateOpening,
    ) {
        let leaves = 1usize << DEPTH;
        let values = (0..leaves * WIDTH)
            .map(|offset| {
                let leaf = offset / WIDTH;
                let byte = offset % WIDTH;
                (leaf as u8)
                    .wrapping_mul(13)
                    .wrapping_add((byte as u8).wrapping_mul(7))
                    .wrapping_add(3)
            })
            .collect::<Vec<_>>();
        let salts = (0..leaves)
            .map(|leaf| {
                core::array::from_fn(|byte| {
                    (leaf as u8)
                        .wrapping_mul(17)
                        .wrapping_add((byte as u8).wrapping_mul(11))
                        .wrapping_add(5)
                })
            })
            .collect::<Vec<_>>();
        let tree =
            build_state_only_private_merkle_tree(HOST_HASH, DEPTH, TAG, WIDTH, &values, &salts)
                .unwrap();
        let opening =
            serialize_state_only_private_opening(&tree, &values, &salts, &INDICES).unwrap();
        (values, salts, tree, opening)
    }

    #[test]
    fn private_opening_roundtrip_zero_copy_and_kat() {
        let (values, salts, tree, opening) = fixture();
        let parsed = verify_state_only_private_opening(
            HOST_HASH,
            &tree.root(),
            DEPTH,
            TAG,
            WIDTH,
            &INDICES,
            &opening.bytes,
        )
        .unwrap();
        assert_eq!(parsed.count, INDICES.len());
        for (ordinal, &index) in INDICES.iter().enumerate() {
            assert_eq!(
                parsed.value(ordinal).unwrap(),
                value_at(&values, WIDTH, index as usize).unwrap()
            );
            assert_eq!(parsed.salt(ordinal).unwrap(), &salts[index as usize]);
        }
        assert_eq!(parsed.records.as_ptr(), opening.bytes[2..].as_ptr());
        assert_eq!(opening.frontier_nodes, 14);
        assert_eq!(
            tree.root(),
            [
                0x62, 0x21, 0x1c, 0x74, 0x11, 0x21, 0x67, 0x11, 0x1f, 0xab, 0x10, 0x10, 0xaa, 0x01,
                0x8d, 0xb1, 0x7e, 0xd8, 0x5a, 0xb3, 0x03, 0xa6, 0xe4, 0x33, 0xe2, 0x4e, 0x57, 0x7f,
                0xf5, 0xe7, 0xa3, 0x23,
            ]
        );
    }

    #[test]
    fn private_opening_tag_value_salt_frontier_and_framing_teeth() {
        let (_values, _salts, tree, opening) = fixture();
        let verify = |bytes: &[u8], tag: u8, indices: &[u32]| {
            verify_state_only_private_opening(
                HOST_HASH,
                &tree.root(),
                DEPTH,
                tag,
                WIDTH,
                indices,
                bytes,
            )
            .map(|_| ())
        };

        assert_eq!(
            verify(&opening.bytes, TAG ^ 1, &INDICES),
            Err(StateOnlyPrivateOpeningError::MerkleMismatch)
        );

        let mut wrong_value = opening.bytes.clone();
        wrong_value[2 + 19] ^= 1;
        assert_eq!(
            verify(&wrong_value, TAG, &INDICES),
            Err(StateOnlyPrivateOpeningError::MerkleMismatch)
        );

        let mut wrong_salt = opening.bytes.clone();
        wrong_salt[2 + WIDTH + 23] ^= 1;
        assert_eq!(
            verify(&wrong_salt, TAG, &INDICES),
            Err(StateOnlyPrivateOpeningError::MerkleMismatch)
        );

        let mut wrong_frontier = opening.bytes.clone();
        *wrong_frontier.last_mut().unwrap() ^= 1;
        assert_eq!(
            verify(&wrong_frontier, TAG, &INDICES),
            Err(StateOnlyPrivateOpeningError::MerkleMismatch)
        );

        let mut wrong_count = opening.bytes.clone();
        wrong_count[..2].copy_from_slice(&2u16.to_le_bytes());
        assert_eq!(
            verify(&wrong_count, TAG, &INDICES),
            Err(StateOnlyPrivateOpeningError::CountMismatch {
                expected: 3,
                actual: 2,
            })
        );

        assert_eq!(
            verify(&opening.bytes, TAG, &[7, 1, 30]),
            Err(StateOnlyPrivateOpeningError::IndicesNotStrictlyIncreasing)
        );

        let mut trailing = opening.bytes.clone();
        trailing.push(0xa5);
        assert_eq!(
            verify(&trailing, TAG, &INDICES),
            Err(StateOnlyPrivateOpeningError::TrailingBytes {
                offset: opening.bytes.len(),
                remaining: 1,
            })
        );
        let (_, remainder) = verify_state_only_private_opening_from_proof(
            HOST_HASH,
            &tree.root(),
            DEPTH,
            TAG,
            WIDTH,
            &INDICES,
            &trailing,
        )
        .unwrap();
        assert_eq!(remainder, &[0xa5]);
    }
}
