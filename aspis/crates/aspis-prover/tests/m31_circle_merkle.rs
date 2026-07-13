use aspis_core::circle_merkle::{
    parse_circle_layer0_opening, verify_circle_layer0_opening, CircleMerkleError,
    CIRCLE_C1_LAYER0_TAG, CIRCLE_C1_LEAF_BYTES, CIRCLE_C2_LAYER0_TAG, CIRCLE_C2_LEAF_BYTES,
    CIRCLE_LAYER0_BINARY_DEPTH,
};
use aspis_core::field::{CM31, M31, P, QM31};
use aspis_core::merkle::{leaf_hash, node_hash4, verify_radix4_minimal_subtree_bytes};
use aspis_prover::circle_candidate::{
    c1_layer0_leaves, c2_layer0_leaves, CircleEncoder, C1_COLUMNS, C2_COLUMNS, TRACE_LEN,
};
use aspis_prover::HOST_HASH;

const OFFICIAL_C1_ROOT: &str = "c6a93117eb8ccd3e0e9c3ff9598ce6f34682f82c430a955da1c0f799c6c2ad4f";
const OFFICIAL_C2_ROOT: &str = "c764cdff2474ee79b56fe9baeaa3c7cc5e62c2ae3b1f0ed470c00c28f83930b3";

#[derive(Clone, Copy)]
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0 = self.0.wrapping_mul(0x2545_f491_4f6c_dd1d);
        self.0
    }

    fn m31(&mut self) -> M31 {
        M31((self.next() as u32) % P)
    }

    fn qm31(&mut self) -> QM31 {
        QM31 {
            c0: CM31::new(self.m31(), self.m31()),
            c1: CM31::new(self.m31(), self.m31()),
        }
    }
}

fn fixture() -> (Vec<Vec<M31>>, Vec<Vec<QM31>>) {
    let mut rng = Rng(0x4349_5243_4c45_4332);
    let c1 = (0..C1_COLUMNS)
        .map(|column| {
            (0..TRACE_LEN)
                .map(|row| rng.m31().add(M31((column * 65_537 + row * 257 + 1) as u32)))
                .collect()
        })
        .collect();
    let c2 = (0..C2_COLUMNS)
        .map(|helper| {
            (0..TRACE_LEN)
                .map(|row| {
                    let mut value = rng.qm31();
                    value.c0.a = value.c0.a.add(M31((helper * 4099 + row + 1) as u32));
                    value
                })
                .collect()
        })
        .collect();
    (c1, c2)
}

fn hex(bytes: [u8; 32]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn build_tree<const N: usize>(leaves: &[[u8; N]], tag: u8) -> Vec<Vec<[u8; 32]>> {
    let mut levels = vec![leaves
        .iter()
        .map(|leaf| leaf_hash(HOST_HASH, tag, leaf))
        .collect::<Vec<_>>()];
    while levels.last().unwrap().len() > 1 {
        let next = levels
            .last()
            .unwrap()
            .chunks_exact(4)
            .map(|children| node_hash4(HOST_HASH, children.try_into().unwrap()))
            .collect();
        levels.push(next);
    }
    levels
}

fn emit_frontier(levels: &[Vec<[u8; 32]>], indices: &[u32]) -> Vec<[u8; 32]> {
    let mut nodes = Vec::new();
    let mut level_indices = indices.to_vec();
    for level in &levels[..levels.len() - 1] {
        let mut next = Vec::new();
        let mut position = 0;
        while position < level_indices.len() {
            let parent = level_indices[position] >> 2;
            let mut present = 0u8;
            while position < level_indices.len() && level_indices[position] >> 2 == parent {
                present |= 1 << (level_indices[position] & 3);
                position += 1;
            }
            for slot in 0..4u32 {
                if present & (1 << slot) == 0 {
                    nodes.push(level[(4 * parent + slot) as usize]);
                }
            }
            next.push(parent);
        }
        level_indices = next;
    }
    nodes
}

fn opening_bytes(
    indices: &[u32],
    c1_leaves: &[[u8; CIRCLE_C1_LEAF_BYTES]],
    c2_leaves: &[[u8; CIRCLE_C2_LEAF_BYTES]],
    c1_tree: &[Vec<[u8; 32]>],
    c2_tree: &[Vec<[u8; 32]>],
) -> Vec<u8> {
    let mut proof = Vec::new();
    proof.extend_from_slice(&(indices.len() as u16).to_le_bytes());
    for &index in indices {
        proof.extend_from_slice(&c1_leaves[index as usize]);
    }
    for &index in indices {
        proof.extend_from_slice(&c2_leaves[index as usize]);
    }
    let c1_frontier = emit_frontier(c1_tree, indices);
    proof.extend_from_slice(&(c1_frontier.len() as u32).to_le_bytes());
    for node in c1_frontier {
        proof.extend_from_slice(&node);
    }
    let c2_frontier = emit_frontier(c2_tree, indices);
    proof.extend_from_slice(&(c2_frontier.len() as u32).to_le_bytes());
    for node in c2_frontier {
        proof.extend_from_slice(&node);
    }
    proof
}

struct Material {
    c1_leaves: Vec<[u8; CIRCLE_C1_LEAF_BYTES]>,
    c2_leaves: Vec<[u8; CIRCLE_C2_LEAF_BYTES]>,
    c1_tree: Vec<Vec<[u8; 32]>>,
    c2_tree: Vec<Vec<[u8; 32]>>,
}

impl Material {
    fn new() -> Self {
        let (c1_messages, c2_messages) = fixture();
        let encoder = CircleEncoder::new();
        let c1 = encoder.encode_c1_columns(&c1_messages).unwrap();
        let c2 = encoder.encode_c2_columns(&c2_messages).unwrap();
        let c1_leaves = c1_layer0_leaves(&c1).unwrap();
        let c2_leaves = c2_layer0_leaves(&c2).unwrap();
        let c1_tree = build_tree(&c1_leaves, CIRCLE_C1_LAYER0_TAG);
        let c2_tree = build_tree(&c2_leaves, CIRCLE_C2_LAYER0_TAG);
        Self {
            c1_leaves,
            c2_leaves,
            c1_tree,
            c2_tree,
        }
    }

    fn c1_root(&self) -> [u8; 32] {
        self.c1_tree.last().unwrap()[0]
    }

    fn c2_root(&self) -> [u8; 32] {
        self.c2_tree.last().unwrap()[0]
    }
}

fn verify_with_tags_weakened(
    proof: &[u8],
    indices: &[u32],
    c1_root: &[u8; 32],
    c2_root: &[u8; 32],
    c1_tag: u8,
    c2_tag: u8,
) -> bool {
    let opening = parse_circle_layer0_opening(proof, indices.len()).unwrap();
    let mut level = Vec::new();
    let mut next = Vec::new();
    let c1_entries = indices
        .iter()
        .enumerate()
        .map(|(leaf, &index)| {
            (
                index,
                leaf_hash(HOST_HASH, c1_tag, opening.c1_leaf(leaf).unwrap()),
            )
        })
        .collect::<Vec<_>>();
    if !verify_radix4_minimal_subtree_bytes(
        HOST_HASH,
        c1_root,
        CIRCLE_LAYER0_BINARY_DEPTH,
        &c1_entries,
        opening.c1_frontier,
        &mut level,
        &mut next,
    ) {
        return false;
    }
    let c2_entries = indices
        .iter()
        .enumerate()
        .map(|(leaf, &index)| {
            (
                index,
                leaf_hash(HOST_HASH, c2_tag, opening.c2_leaf(leaf).unwrap()),
            )
        })
        .collect::<Vec<_>>();
    verify_radix4_minimal_subtree_bytes(
        HOST_HASH,
        c2_root,
        CIRCLE_LAYER0_BINARY_DEPTH,
        &c2_entries,
        opening.c2_frontier,
        &mut level,
        &mut next,
    )
}

fn c1_column_major_leaf(canonical: &[u8]) -> [u8; CIRCLE_C1_LEAF_BYTES] {
    let mut wrong = [0u8; CIRCLE_C1_LEAF_BYTES];
    for slot in 0..4 {
        for column in 0..C1_COLUMNS {
            let source = (slot * C1_COLUMNS + column) * 4;
            let target = (column * 4 + slot) * 4;
            wrong[target..target + 4].copy_from_slice(&canonical[source..source + 4]);
        }
    }
    wrong
}

fn c1_slot_major_leaf(wrong: &[u8]) -> [u8; CIRCLE_C1_LEAF_BYTES] {
    let mut canonical = [0u8; CIRCLE_C1_LEAF_BYTES];
    for slot in 0..4 {
        for column in 0..C1_COLUMNS {
            let source = (column * 4 + slot) * 4;
            let target = (slot * C1_COLUMNS + column) * 4;
            canonical[target..target + 4].copy_from_slice(&wrong[source..source + 4]);
        }
    }
    canonical
}

fn c2_slot_major_leaf(canonical: &[u8]) -> [u8; CIRCLE_C2_LEAF_BYTES] {
    let mut wrong = [0u8; CIRCLE_C2_LEAF_BYTES];
    for helper in 0..C2_COLUMNS {
        for slot in 0..4 {
            let source = (helper * 4 + slot) * 16;
            let target = (slot * C2_COLUMNS + helper) * 16;
            wrong[target..target + 16].copy_from_slice(&canonical[source..source + 16]);
        }
    }
    wrong
}

fn c2_helper_major_leaf(wrong: &[u8]) -> [u8; CIRCLE_C2_LEAF_BYTES] {
    let mut canonical = [0u8; CIRCLE_C2_LEAF_BYTES];
    for helper in 0..C2_COLUMNS {
        for slot in 0..4 {
            let source = (slot * C2_COLUMNS + helper) * 16;
            let target = (helper * 4 + slot) * 16;
            canonical[target..target + 16].copy_from_slice(&wrong[source..source + 16]);
        }
    }
    canonical
}

fn verify_c1_column_major_weakened(
    adversarial_proof: &[u8],
    indices: &[u32],
    c1_root: &[u8; 32],
    c2_root: &[u8; 32],
) -> bool {
    let offsets = parse_circle_layer0_opening(adversarial_proof, indices.len())
        .unwrap()
        .offsets;
    let mut reinterpreted = adversarial_proof.to_vec();
    for leaf in 0..indices.len() {
        let start = offsets.c1_leaves + leaf * CIRCLE_C1_LEAF_BYTES;
        let canonical = c1_slot_major_leaf(&reinterpreted[start..start + CIRCLE_C1_LEAF_BYTES]);
        reinterpreted[start..start + CIRCLE_C1_LEAF_BYTES].copy_from_slice(&canonical);
    }
    verify_circle_layer0_opening(HOST_HASH, c1_root, c2_root, indices, &reinterpreted).is_ok()
}

fn verify_c2_slot_major_weakened(
    adversarial_proof: &[u8],
    indices: &[u32],
    c1_root: &[u8; 32],
    c2_root: &[u8; 32],
) -> bool {
    let offsets = parse_circle_layer0_opening(adversarial_proof, indices.len())
        .unwrap()
        .offsets;
    let mut reinterpreted = adversarial_proof.to_vec();
    for leaf in 0..indices.len() {
        let start = offsets.c2_leaves + leaf * CIRCLE_C2_LEAF_BYTES;
        let canonical = c2_helper_major_leaf(&reinterpreted[start..start + CIRCLE_C2_LEAF_BYTES]);
        reinterpreted[start..start + CIRCLE_C2_LEAF_BYTES].copy_from_slice(&canonical);
    }
    verify_circle_layer0_opening(HOST_HASH, c1_root, c2_root, indices, &reinterpreted).is_ok()
}

fn verify_reversed_c1_siblings_weakened(
    adversarial_proof: &[u8],
    indices: &[u32],
    c1_root: &[u8; 32],
    c2_root: &[u8; 32],
) -> bool {
    let opening = parse_circle_layer0_opening(adversarial_proof, indices.len()).unwrap();
    let mut reinterpreted = adversarial_proof.to_vec();
    for group in reinterpreted[opening.offsets.c1_frontier..opening.offsets.c2_node_count]
        .chunks_exact_mut(3 * 32)
    {
        for byte in 0..32 {
            group.swap(byte, 2 * 32 + byte);
        }
    }
    verify_circle_layer0_opening(HOST_HASH, c1_root, c2_root, indices, &reinterpreted).is_ok()
}

fn single_root_from_frontier(tag: u8, mut index: u32, leaf: &[u8], frontier: &[u8]) -> [u8; 32] {
    assert_eq!(frontier.len(), 5 * 3 * 32);
    let mut current = leaf_hash(HOST_HASH, tag, leaf);
    let mut position = 0;
    for _ in 0..5 {
        let own_slot = (index & 3) as usize;
        let mut children = [[0u8; 32]; 4];
        for (slot, child) in children.iter_mut().enumerate() {
            if slot == own_slot {
                *child = current;
            } else {
                *child = frontier[position..position + 32].try_into().unwrap();
                position += 32;
            }
        }
        current = node_hash4(HOST_HASH, &children);
        index >>= 2;
    }
    assert_eq!(position, frontier.len());
    current
}

#[test]
fn fixed_circle_opening_verifies_against_committed_official_stwo_roots() {
    let material = Material::new();
    assert_eq!(hex(material.c1_root()), OFFICIAL_C1_ROOT);
    assert_eq!(hex(material.c2_root()), OFFICIAL_C2_ROOT);
    let indices = [0, 1, 137, 511, 512, 1_023];
    let proof = opening_bytes(
        &indices,
        &material.c1_leaves,
        &material.c2_leaves,
        &material.c1_tree,
        &material.c2_tree,
    );
    let opening = verify_circle_layer0_opening(
        HOST_HASH,
        &material.c1_root(),
        &material.c2_root(),
        &indices,
        &proof,
    )
    .unwrap();
    assert_eq!(opening.unique_count, indices.len());
    assert_eq!(opening.c1_leaf(2).unwrap(), material.c1_leaves[137]);
    assert_eq!(opening.c2_leaf(5).unwrap(), material.c2_leaves[1_023]);
    let c1_leaf_offset = opening.offsets.c1_leaves;

    let mut noncanonical = proof;
    noncanonical[c1_leaf_offset..c1_leaf_offset + 4].copy_from_slice(&P.to_le_bytes());
    assert_eq!(
        verify_circle_layer0_opening(
            HOST_HASH,
            &material.c1_root(),
            &material.c2_root(),
            &indices,
            &noncanonical,
        ),
        Err(CircleMerkleError::NonCanonicalC1 { leaf: 0, offset: 0 })
    );
}

#[test]
fn wrong_c1_and_c2_leaf_orders_have_demonstrated_teeth() {
    let material = Material::new();
    let indices = [137];
    let proof = opening_bytes(
        &indices,
        &material.c1_leaves,
        &material.c2_leaves,
        &material.c1_tree,
        &material.c2_tree,
    );
    let offsets = parse_circle_layer0_opening(&proof, 1).unwrap().offsets;

    let mut wrong_c1 = proof.clone();
    let leaf = c1_column_major_leaf(
        &wrong_c1[offsets.c1_leaves..offsets.c1_leaves + CIRCLE_C1_LEAF_BYTES],
    );
    wrong_c1[offsets.c1_leaves..offsets.c1_leaves + CIRCLE_C1_LEAF_BYTES].copy_from_slice(&leaf);
    assert_eq!(
        verify_circle_layer0_opening(
            HOST_HASH,
            &material.c1_root(),
            &material.c2_root(),
            &indices,
            &wrong_c1,
        ),
        Err(CircleMerkleError::C1MerkleMismatch)
    );
    assert!(verify_c1_column_major_weakened(
        &wrong_c1,
        &indices,
        &material.c1_root(),
        &material.c2_root(),
    ));

    let mut wrong_c2 = proof;
    let leaf =
        c2_slot_major_leaf(&wrong_c2[offsets.c2_leaves..offsets.c2_leaves + CIRCLE_C2_LEAF_BYTES]);
    wrong_c2[offsets.c2_leaves..offsets.c2_leaves + CIRCLE_C2_LEAF_BYTES].copy_from_slice(&leaf);
    assert_eq!(
        verify_circle_layer0_opening(
            HOST_HASH,
            &material.c1_root(),
            &material.c2_root(),
            &indices,
            &wrong_c2,
        ),
        Err(CircleMerkleError::C2MerkleMismatch)
    );
    assert!(verify_c2_slot_major_weakened(
        &wrong_c2,
        &indices,
        &material.c1_root(),
        &material.c2_root(),
    ));
}

#[test]
fn tag_swap_and_sibling_order_have_demonstrated_teeth() {
    let material = Material::new();
    let indices = [137];

    let swapped_c1_tree = build_tree(&material.c1_leaves, CIRCLE_C2_LAYER0_TAG);
    let swapped_c2_tree = build_tree(&material.c2_leaves, CIRCLE_C1_LAYER0_TAG);
    let swapped_proof = opening_bytes(
        &indices,
        &material.c1_leaves,
        &material.c2_leaves,
        &swapped_c1_tree,
        &swapped_c2_tree,
    );
    let swapped_c1_root = swapped_c1_tree.last().unwrap()[0];
    let swapped_c2_root = swapped_c2_tree.last().unwrap()[0];
    assert_eq!(
        verify_circle_layer0_opening(
            HOST_HASH,
            &swapped_c1_root,
            &swapped_c2_root,
            &indices,
            &swapped_proof,
        ),
        Err(CircleMerkleError::C1MerkleMismatch)
    );
    assert!(verify_with_tags_weakened(
        &swapped_proof,
        &indices,
        &swapped_c1_root,
        &swapped_c2_root,
        CIRCLE_C2_LAYER0_TAG,
        CIRCLE_C1_LAYER0_TAG,
    ));

    let proof = opening_bytes(
        &indices,
        &material.c1_leaves,
        &material.c2_leaves,
        &material.c1_tree,
        &material.c2_tree,
    );
    let opening = parse_circle_layer0_opening(&proof, 1).unwrap();
    assert_eq!(opening.c1_frontier.len(), 5 * 3 * 32);
    let mut reversed = proof.clone();
    for group in reversed[opening.offsets.c1_frontier..opening.offsets.c2_node_count]
        .chunks_exact_mut(3 * 32)
    {
        for byte in 0..32 {
            group.swap(byte, 2 * 32 + byte);
        }
    }
    assert_eq!(
        verify_circle_layer0_opening(
            HOST_HASH,
            &material.c1_root(),
            &material.c2_root(),
            &indices,
            &reversed,
        ),
        Err(CircleMerkleError::C1MerkleMismatch)
    );
    assert!(verify_reversed_c1_siblings_weakened(
        &reversed,
        &indices,
        &material.c1_root(),
        &material.c2_root(),
    ));
}

#[test]
fn c1_frontier_reuse_for_c2_has_demonstrated_teeth() {
    let material = Material::new();
    let indices = [137];
    let proof = opening_bytes(
        &indices,
        &material.c1_leaves,
        &material.c2_leaves,
        &material.c1_tree,
        &material.c2_tree,
    );
    let opening = parse_circle_layer0_opening(&proof, 1).unwrap();
    let malicious_c2_root = single_root_from_frontier(
        CIRCLE_C2_LAYER0_TAG,
        indices[0],
        opening.c2_leaf(0).unwrap(),
        opening.c1_frontier,
    );

    // Exact framing still carries a distinct C2 node-count field, but the
    // malicious vector supplies zero C2 nodes and expects C1's path reused.
    let mut shared = proof[..opening.offsets.c2_node_count].to_vec();
    shared.extend_from_slice(&0u32.to_le_bytes());
    assert_eq!(
        verify_circle_layer0_opening(
            HOST_HASH,
            &material.c1_root(),
            &malicious_c2_root,
            &indices,
            &shared,
        ),
        Err(CircleMerkleError::C2MerkleMismatch)
    );

    let weakened = parse_circle_layer0_opening(&shared, 1).unwrap();
    let mut level = Vec::new();
    let mut next = Vec::new();
    let c1_entry = [(
        indices[0],
        leaf_hash(
            HOST_HASH,
            CIRCLE_C1_LAYER0_TAG,
            weakened.c1_leaf(0).unwrap(),
        ),
    )];
    let c2_entry = [(
        indices[0],
        leaf_hash(
            HOST_HASH,
            CIRCLE_C2_LAYER0_TAG,
            weakened.c2_leaf(0).unwrap(),
        ),
    )];
    assert!(verify_radix4_minimal_subtree_bytes(
        HOST_HASH,
        &material.c1_root(),
        CIRCLE_LAYER0_BINARY_DEPTH,
        &c1_entry,
        weakened.c1_frontier,
        &mut level,
        &mut next,
    ));
    assert!(verify_radix4_minimal_subtree_bytes(
        HOST_HASH,
        &malicious_c2_root,
        CIRCLE_LAYER0_BINARY_DEPTH,
        &c2_entry,
        weakened.c1_frontier,
        &mut level,
        &mut next,
    ));
}
