use aspis_core::circle_fri::{
    normalized_circle_to_line_arity4_at_fiber, normalized_line_arity4_at_fiber,
};
use aspis_core::circle_line_merkle::{
    derive_circle_line_query_indices, parse_circle_line_openings, verify_circle_line_openings,
    verify_circle_line_openings_for_prefix, CircleLineMerkleError, CIRCLE_LINE_BINARY_DEPTHS,
    CIRCLE_LINE_LAYER_COUNT, CIRCLE_LINE_LEAF_BYTES, CIRCLE_LINE_TAGS,
};
use aspis_core::circle_prefix::{
    CandidatePrefix, CANDIDATE_FINAL_POLY_LOG_LEN, CANDIDATE_FLAGS, CANDIDATE_GRINDING_BITS,
    CANDIDATE_LOG_BLOWUP, CANDIDATE_LOG_ROWS, CANDIDATE_PREFIX_LEN, CANDIDATE_PREFIX_OFFSETS,
    CANDIDATE_PROFILE_ID, CANDIDATE_QUERY_COUNT, CANDIDATE_ROUND_COUNT,
};
use aspis_core::field::{qm31_power_table, CM31, M31, P, QM31};
use aspis_core::merkle::{leaf_hash, verify_radix4_minimal_subtree_bytes};
use aspis_core::proof::{Header, HEADER_LEN, VERSION_V4_S2};
use aspis_core::{FoldPayload, MerkleMode};
use aspis_prover::circle_candidate::{
    CircleEncoder, C1_COLUMNS, C2_COLUMNS, CODEWORD_LEN, TOTAL_COLUMNS, TRACE_LEN,
};
use aspis_prover::HOST_HASH;
use sha2::{Digest as _, Sha256};

const COMMITTED_LINE_ROOTS: [&str; CIRCLE_LINE_LAYER_COUNT] = [
    "660a1222ffb15265f3aa4e8750532e3bed26baff63245cfec4023148a8906ef7",
    "aa9e50e4f6e8556fc9825d204ab22f6c1e9faf66f34c54042b092025ae460317",
    "1a68889bf89fc3eddfcade024d9f7c30e637c256b77234e00939b05b0398168d",
];

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

fn q(values: [u32; 4]) -> QM31 {
    QM31 {
        c0: CM31::new(M31(values[0]), M31(values[1])),
        c1: CM31::new(M31(values[2]), M31(values[3])),
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

fn independent_hash(parts: &[&[u8]]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    for part in parts {
        hasher.update(part);
    }
    hasher.finalize().into()
}

fn hex(bytes: [u8; 32]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn independent_leaf_hash(tag: u8, leaf: &[u8]) -> [u8; 32] {
    independent_hash(&[&[0x10, tag], leaf])
}

fn independent_node_hash(children: &[[u8; 32]; 4]) -> [u8; 32] {
    let mut bytes = [0u8; 129];
    bytes[0] = 0x12;
    for (slot, child) in children.iter().enumerate() {
        bytes[1 + slot * 32..1 + (slot + 1) * 32].copy_from_slice(child);
    }
    independent_hash(&[&bytes])
}

fn line_leaves(values: &[QM31]) -> Vec<[u8; CIRCLE_LINE_LEAF_BYTES]> {
    assert_eq!(values.len() % 4, 0);
    values
        .chunks_exact(4)
        .map(|fiber| {
            let mut leaf = [0u8; CIRCLE_LINE_LEAF_BYTES];
            for (slot, value) in fiber.iter().enumerate() {
                value.write_le_bytes(&mut leaf[slot * 16..(slot + 1) * 16]);
            }
            leaf
        })
        .collect()
}

fn independent_tree(leaves: &[[u8; CIRCLE_LINE_LEAF_BYTES]], tag: u8) -> Vec<Vec<[u8; 32]>> {
    let mut levels = vec![leaves
        .iter()
        .map(|leaf| independent_leaf_hash(tag, leaf))
        .collect::<Vec<_>>()];
    while levels.last().unwrap().len() > 1 {
        levels.push(
            levels
                .last()
                .unwrap()
                .chunks_exact(4)
                .map(|children| independent_node_hash(children.try_into().unwrap()))
                .collect(),
        );
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

struct FoldMaterial {
    values: [Vec<QM31>; CIRCLE_LINE_LAYER_COUNT],
    leaves: [Vec<[u8; CIRCLE_LINE_LEAF_BYTES]>; CIRCLE_LINE_LAYER_COUNT],
    trees: [Vec<Vec<[u8; 32]>>; CIRCLE_LINE_LAYER_COUNT],
    roots: [[u8; 32]; CIRCLE_LINE_LAYER_COUNT],
}

impl FoldMaterial {
    fn new() -> Self {
        let (c1_messages, c2_messages) = fixture();
        let encoder = CircleEncoder::new();
        let c1 = encoder.encode_c1_columns(&c1_messages).unwrap();
        let c2 = encoder.encode_c2_columns(&c2_messages).unwrap();
        let gamma = q([17, 29, 43, 71]);
        let powers = qm31_power_table::<TOTAL_COLUMNS>(gamma);
        let combined = (0..CODEWORD_LEN)
            .map(|index| {
                let mut value = QM31::ZERO;
                for column in 0..C1_COLUMNS {
                    value = value.add(powers[column].mul_m31(c1[column][index]));
                }
                for helper in 0..C2_COLUMNS {
                    value = value.add(powers[C1_COLUMNS + helper].mul(c2[helper][index]));
                }
                value
            })
            .collect::<Vec<_>>();
        let alphas = [
            q([101, 307, 401, 809]),
            q([131, 313, 419, 811]),
            q([151, 331, 431, 821]),
        ];
        let layer1 = (0..1_024)
            .map(|fiber| {
                normalized_circle_to_line_arity4_at_fiber(
                    combined[4 * fiber..4 * fiber + 4].try_into().unwrap(),
                    alphas[0],
                    fiber,
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        let layer2 = (0..256)
            .map(|fiber| {
                normalized_line_arity4_at_fiber(
                    layer1[4 * fiber..4 * fiber + 4].try_into().unwrap(),
                    alphas[1],
                    1,
                    fiber,
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        let layer3 = (0..64)
            .map(|fiber| {
                normalized_line_arity4_at_fiber(
                    layer2[4 * fiber..4 * fiber + 4].try_into().unwrap(),
                    alphas[2],
                    2,
                    fiber,
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        let values = [layer1, layer2, layer3];
        let leaves = values.each_ref().map(|values| line_leaves(values));
        let trees =
            core::array::from_fn(|layer| independent_tree(&leaves[layer], CIRCLE_LINE_TAGS[layer]));
        let roots = trees.each_ref().map(|tree| tree.last().unwrap()[0]);
        Self {
            values,
            leaves,
            trees,
            roots,
        }
    }
}

fn opening_bytes_for_indices(
    indices: &[Vec<u32>; CIRCLE_LINE_LAYER_COUNT],
    material: &FoldMaterial,
    trees: &[Vec<Vec<[u8; 32]>>; CIRCLE_LINE_LAYER_COUNT],
) -> Vec<u8> {
    let mut proof = Vec::new();
    for layer in 0..CIRCLE_LINE_LAYER_COUNT {
        proof.extend_from_slice(&(indices[layer].len() as u16).to_le_bytes());
        for &index in &indices[layer] {
            proof.extend_from_slice(&material.leaves[layer][index as usize]);
        }
        let frontier = emit_frontier(&trees[layer], &indices[layer]);
        proof.extend_from_slice(&(frontier.len() as u32).to_le_bytes());
        for node in frontier {
            proof.extend_from_slice(&node);
        }
    }
    proof
}

fn opening_bytes(queries: &[u32], material: &FoldMaterial) -> Vec<u8> {
    let indices = derive_circle_line_query_indices(queries).unwrap();
    opening_bytes_for_indices(&indices.later, material, &material.trees)
}

fn prefix_bytes(roots: &[[u8; 32]; CIRCLE_LINE_LAYER_COUNT]) -> Vec<u8> {
    let mut bytes = vec![0u8; CANDIDATE_PREFIX_LEN];
    Header {
        version: VERSION_V4_S2,
        profile_id: CANDIDATE_PROFILE_ID,
        log_rows: CANDIDATE_LOG_ROWS,
        log_blowup: CANDIDATE_LOG_BLOWUP,
        query_count: CANDIDATE_QUERY_COUNT,
        grinding_bits: CANDIDATE_GRINDING_BITS,
        fold_payload: FoldPayload::RawFibers as u8,
        merkle_mode: MerkleMode::Radix4MinimalSubtree as u8,
        num_rounds: CANDIDATE_ROUND_COUNT as u32,
        final_poly_log_len: CANDIDATE_FINAL_POLY_LOG_LEN,
        flags: CANDIDATE_FLAGS,
    }
    .write(&mut bytes[..HEADER_LEN]);
    for (layer, root) in roots.iter().enumerate() {
        let root_start = CANDIDATE_PREFIX_OFFSETS.rounds[layer + 1]
            .root_start
            .unwrap();
        bytes[root_start..root_start + 32].copy_from_slice(root);
    }
    bytes
}

fn verify_with_indices_and_tags_weakened(
    adversarial_proof: &[u8],
    parser_queries: &[u32],
    indices: &[Vec<u32>; CIRCLE_LINE_LAYER_COUNT],
    roots: &[[u8; 32]; CIRCLE_LINE_LAYER_COUNT],
    tags: &[u8; CIRCLE_LINE_LAYER_COUNT],
) -> bool {
    let openings = parse_circle_line_openings(adversarial_proof, parser_queries).unwrap();
    let mut level = Vec::new();
    let mut next = Vec::new();
    for (layer, root) in roots.iter().enumerate() {
        let entries = indices[layer]
            .iter()
            .enumerate()
            .map(|(ordinal, &index)| {
                (
                    index,
                    leaf_hash(
                        HOST_HASH,
                        tags[layer],
                        openings.layers[layer].leaf(ordinal).unwrap(),
                    ),
                )
            })
            .collect::<Vec<_>>();
        if !verify_radix4_minimal_subtree_bytes(
            HOST_HASH,
            root,
            CIRCLE_LINE_BINARY_DEPTHS[layer],
            &entries,
            openings.layers[layer].frontier,
            &mut level,
            &mut next,
        ) {
            return false;
        }
    }
    true
}

fn transpose_slots(leaf: &[u8]) -> [u8; CIRCLE_LINE_LEAF_BYTES] {
    let mut transposed = [0u8; CIRCLE_LINE_LEAF_BYTES];
    for slot in 0..4 {
        let target = (slot ^ 1) * 16;
        transposed[target..target + 16].copy_from_slice(&leaf[slot * 16..(slot + 1) * 16]);
    }
    transposed
}

fn verify_slot_transpose_weakened(
    adversarial_proof: &[u8],
    queries: &[u32],
    roots: &[[u8; 32]; CIRCLE_LINE_LAYER_COUNT],
    target_layer: usize,
) -> bool {
    let openings = parse_circle_line_openings(adversarial_proof, queries).unwrap();
    let mut reinterpreted = adversarial_proof.to_vec();
    for leaf in 0..openings.layers[target_layer].unique_count {
        let start = openings.layers[target_layer].offsets.leaves + leaf * CIRCLE_LINE_LEAF_BYTES;
        let canonical = transpose_slots(&reinterpreted[start..start + CIRCLE_LINE_LEAF_BYTES]);
        reinterpreted[start..start + CIRCLE_LINE_LEAF_BYTES].copy_from_slice(&canonical);
    }
    verify_circle_line_openings(HOST_HASH, roots, queries, &reinterpreted).is_ok()
}

fn root_from_single_frontier(
    tag: u8,
    binary_depth: u32,
    mut index: u32,
    leaf: &[u8],
    frontier: &[u8],
) -> [u8; 32] {
    let mut current = independent_leaf_hash(tag, leaf);
    let mut position = 0;
    for _ in 0..binary_depth / 2 {
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
        current = independent_node_hash(&children);
        index >>= 2;
    }
    assert_eq!(position, frontier.len());
    current
}

fn verify_zero_pad_truncation_weakened(
    adversarial_proof: &[u8],
    queries: &[u32],
    roots: &[[u8; 32]; CIRCLE_LINE_LAYER_COUNT],
) -> bool {
    let mut padded = adversarial_proof.to_vec();
    padded.push(0);
    verify_circle_line_openings(HOST_HASH, roots, queries, &padded).is_ok()
}

fn verify_ignore_one_trailing_byte_weakened(
    adversarial_proof: &[u8],
    queries: &[u32],
    roots: &[[u8; 32]; CIRCLE_LINE_LAYER_COUNT],
) -> bool {
    let Some(canonical_len) = adversarial_proof.len().checked_sub(1) else {
        return false;
    };
    verify_circle_line_openings(
        HOST_HASH,
        roots,
        queries,
        &adversarial_proof[..canonical_len],
    )
    .is_ok()
}

fn verify_layer1_frontier_reuse_for_layer2_weakened(
    adversarial_proof: &[u8],
    queries: &[u32],
    roots: &[[u8; 32]; CIRCLE_LINE_LAYER_COUNT],
) -> bool {
    let openings = parse_circle_line_openings(adversarial_proof, queries).unwrap();
    let indices = derive_circle_line_query_indices(queries).unwrap();
    if indices.layer0.len() != 1 {
        return false;
    }
    let reused_len = (CIRCLE_LINE_BINARY_DEPTHS[1] / 2 * 3 * 32) as usize;
    let mut level = Vec::new();
    let mut next = Vec::new();
    for (layer, root) in roots.iter().enumerate() {
        let entries = indices.later[layer]
            .iter()
            .enumerate()
            .map(|(ordinal, &index)| {
                (
                    index,
                    leaf_hash(
                        HOST_HASH,
                        CIRCLE_LINE_TAGS[layer],
                        openings.layers[layer].leaf(ordinal).unwrap(),
                    ),
                )
            })
            .collect::<Vec<_>>();
        let frontier = if layer == 1 {
            &openings.layers[0].frontier[..reused_len]
        } else {
            openings.layers[layer].frontier
        };
        if !verify_radix4_minimal_subtree_bytes(
            HOST_HASH,
            root,
            CIRCLE_LINE_BINARY_DEPTHS[layer],
            &entries,
            frontier,
            &mut level,
            &mut next,
        ) {
            return false;
        }
    }
    true
}

#[test]
fn committed_fold_layers_verify_against_prefix_roots_and_expose_query_chain() {
    let material = FoldMaterial::new();
    let queries = [1_023, 0, 5, 4, 255, 256, 511, 512, 5, 137];
    let proof = opening_bytes(&queries, &material);
    let prefix_bytes = prefix_bytes(&material.roots);
    let prefix = CandidatePrefix::parse_exact(&prefix_bytes).unwrap();
    let verified =
        verify_circle_line_openings_for_prefix(HOST_HASH, &prefix, &queries, &proof).unwrap();
    for (root, expected) in material.roots.into_iter().zip(COMMITTED_LINE_ROOTS) {
        assert_eq!(hex(root), expected);
    }

    for query in verified.indices.layer0.iter().copied() {
        for layer in 1..=3u8 {
            let opened = verified.query_leaf_slot(query, layer).unwrap();
            let incoming_index = query >> (2 * (u32::from(layer) - 1));
            assert_eq!(opened.leaf_index, incoming_index >> 2);
            assert_eq!(opened.slot, (incoming_index & 3) as u8);
            assert_eq!(
                opened.value(),
                material.values[usize::from(layer - 1)][incoming_index as usize]
            );
        }
    }
    assert_eq!(
        verified.query_leaf_slot(2, 1),
        Err(CircleLineMerkleError::QueryNotOpened { query: 2 })
    );
    assert_eq!(
        verified.query_leaf_slot(0, 4),
        Err(CircleLineMerkleError::InvalidLayer { layer: 4 })
    );

    let first_leaf_offset = verified.openings.layers[0].offsets.leaves;
    let mut noncanonical = proof;
    noncanonical[first_leaf_offset..first_leaf_offset + 4].copy_from_slice(&P.to_le_bytes());
    assert_eq!(
        verify_circle_line_openings(HOST_HASH, &material.roots, &queries, &noncanonical),
        Err(CircleLineMerkleError::NonCanonicalLeaf {
            layer: 1,
            leaf: 0,
            offset: 0,
        })
    );
}

#[test]
fn wrong_layer_tag_and_wrong_query_shift_have_same_vector_teeth() {
    let material = FoldMaterial::new();
    let queries = [137];
    let canonical_indices = derive_circle_line_query_indices(&queries).unwrap();

    let mut wrong_tags = CIRCLE_LINE_TAGS;
    wrong_tags[0] = CIRCLE_LINE_TAGS[1];
    let wrong_trees =
        core::array::from_fn(|layer| independent_tree(&material.leaves[layer], wrong_tags[layer]));
    let wrong_roots = wrong_trees.each_ref().map(|tree| tree.last().unwrap()[0]);
    let wrong_tag_proof =
        opening_bytes_for_indices(&canonical_indices.later, &material, &wrong_trees);
    assert_eq!(
        verify_circle_line_openings(HOST_HASH, &wrong_roots, &queries, &wrong_tag_proof),
        Err(CircleLineMerkleError::MerkleMismatch { layer: 1 })
    );
    assert!(verify_with_indices_and_tags_weakened(
        &wrong_tag_proof,
        &queries,
        &canonical_indices.later,
        &wrong_roots,
        &wrong_tags,
    ));

    let wrong_indices = [vec![68], vec![17], vec![4]];
    let wrong_shift_proof = opening_bytes_for_indices(&wrong_indices, &material, &material.trees);
    assert_eq!(
        verify_circle_line_openings(HOST_HASH, &material.roots, &queries, &wrong_shift_proof),
        Err(CircleLineMerkleError::MerkleMismatch { layer: 1 })
    );
    assert!(verify_with_indices_and_tags_weakened(
        &wrong_shift_proof,
        &queries,
        &wrong_indices,
        &material.roots,
        &CIRCLE_LINE_TAGS,
    ));
}

#[test]
fn slot_transpose_and_frontier_reuse_have_same_vector_teeth() {
    let material = FoldMaterial::new();
    let queries = [137];
    let proof = opening_bytes(&queries, &material);
    let openings = parse_circle_line_openings(&proof, &queries).unwrap();
    for layer in 0..CIRCLE_LINE_LAYER_COUNT {
        let mut adversarial = proof.clone();
        let start = openings.layers[layer].offsets.leaves;
        let wrong = transpose_slots(&adversarial[start..start + CIRCLE_LINE_LEAF_BYTES]);
        adversarial[start..start + CIRCLE_LINE_LEAF_BYTES].copy_from_slice(&wrong);
        assert_eq!(
            verify_circle_line_openings(HOST_HASH, &material.roots, &queries, &adversarial),
            Err(CircleLineMerkleError::MerkleMismatch {
                layer: layer as u8 + 1,
            })
        );
        assert!(verify_slot_transpose_weakened(
            &adversarial,
            &queries,
            &material.roots,
            layer,
        ));
    }

    let layer1_frontier = openings.layers[0].frontier;
    let layer2_needed = (CIRCLE_LINE_BINARY_DEPTHS[1] / 2 * 3 * 32) as usize;
    let reused_frontier = &layer1_frontier[..layer2_needed];
    let malicious_layer2_root = root_from_single_frontier(
        CIRCLE_LINE_TAGS[1],
        CIRCLE_LINE_BINARY_DEPTHS[1],
        queries[0] >> 4,
        openings.layers[1].leaf(0).unwrap(),
        reused_frontier,
    );
    let mut malicious_roots = material.roots;
    malicious_roots[1] = malicious_layer2_root;
    let mut shared = Vec::new();
    shared.extend_from_slice(&proof[..openings.layers[1].offsets.frontier_count]);
    shared.extend_from_slice(&0u32.to_le_bytes());
    shared.extend_from_slice(&proof[openings.layers[1].offsets.record_end..]);
    assert_eq!(
        verify_circle_line_openings(HOST_HASH, &malicious_roots, &queries, &shared),
        Err(CircleLineMerkleError::MerkleMismatch { layer: 2 })
    );
    assert!(verify_layer1_frontier_reuse_for_layer2_weakened(
        &shared,
        &queries,
        &malicious_roots,
    ));
}

#[test]
fn truncation_and_trailing_bytes_have_same_vector_teeth() {
    let material = FoldMaterial::new();
    let queries = [137];
    let canonical = opening_bytes(&queries, &material);
    let openings = parse_circle_line_openings(&canonical, &queries).unwrap();
    let canonical_end = openings.end;

    let mut padded = canonical.clone();
    let final_byte = padded.pop().unwrap();
    padded.push(0);
    let padded_openings = parse_circle_line_openings(&padded, &queries).unwrap();
    let malicious_layer3_root = root_from_single_frontier(
        CIRCLE_LINE_TAGS[2],
        CIRCLE_LINE_BINARY_DEPTHS[2],
        queries[0] >> 6,
        padded_openings.layers[2].leaf(0).unwrap(),
        padded_openings.layers[2].frontier,
    );
    let mut malicious_roots = material.roots;
    malicious_roots[2] = malicious_layer3_root;
    let truncated = padded[..padded.len() - 1].to_vec();
    assert!(matches!(
        verify_circle_line_openings(HOST_HASH, &malicious_roots, &queries, &truncated),
        Err(CircleLineMerkleError::UnexpectedEnd { layer: 3, .. })
    ));
    assert!(verify_zero_pad_truncation_weakened(
        &truncated,
        &queries,
        &malicious_roots,
    ));
    assert_ne!(final_byte, 0, "fixture must make truncation non-vacuous");

    let mut trailing = canonical;
    trailing.push(0xa5);
    assert_eq!(
        verify_circle_line_openings(HOST_HASH, &material.roots, &queries, &trailing),
        Err(CircleLineMerkleError::TrailingBytes {
            offset: canonical_end,
            remaining: 1,
        })
    );
    assert!(verify_ignore_one_trailing_byte_weakened(
        &trailing,
        &queries,
        &material.roots,
    ));
}
