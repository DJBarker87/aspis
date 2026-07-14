use aspis_core::circle_line_merkle::{
    derive_circle_line_query_indices, CircleLineMerkleError, CIRCLE_LINE_LAYER_COUNT,
    CIRCLE_LINE_TAGS, RATE32_CIRCLE_OPENING_GEOMETRY,
};
use aspis_core::circle_merkle::{
    CircleMerkleError, CIRCLE_C1_LAYER0_TAG, CIRCLE_C1_LEAF_BYTES, CIRCLE_C2_LAYER0_TAG,
    CIRCLE_C2_LEAF_BYTES,
};
use aspis_core::circle_openings::{
    verify_and_check_circle_openings_for_geometry, verify_and_check_circle_openings_for_prefix,
    CircleOpeningsError,
};
use aspis_core::circle_prefix::{
    CandidatePrefix, CANDIDATE_FINAL_POLY_LEN, CANDIDATE_OOD_SAMPLES, CANDIDATE_PREFIX_LEN,
    CANDIDATE_PREFIX_OFFSETS, CANDIDATE_QUERY_COUNT, CANDIDATE_ROUND_COUNT,
};
use aspis_core::circle_query::CircleQueryError;
use aspis_core::field::{CM31, M31, P, QM31};
use aspis_core::merkle::{leaf_hash, node_hash4};
use aspis_core::sumcheck::SUMCHECK_COEFFICIENTS;
use aspis_prover::circle_candidate::{
    build_fold_commitments, build_fold_commitments_for_domain_log, c1_layer0_leaves,
    c1_layer0_leaves_for_codeword_len, c1_layer0_root, c1_layer0_root_for_codeword_len,
    c2_layer0_leaves, c2_layer0_leaves_for_codeword_len, c2_layer0_root,
    c2_layer0_root_for_codeword_len, candidate_statement_evaluations, gamma_combine_codewords,
    gamma_combine_codewords_for_len, gamma_combine_messages, serialize_candidate_prefix,
    CandidatePrefixMaterial, CircleEncoder, CircleFoldCommitments, C1_COLUMNS, C2_COLUMNS,
    TRACE_LEN,
};
use aspis_prover::circle_candidate_openings::serialize_candidate_openings_for_fiber_count;
use aspis_prover::HOST_HASH;
use sha2::{Digest as _, Sha256};

const RAW_QUERIES: [u32; CANDIDATE_QUERY_COUNT as usize] = [
    0, 1, 2, 3, 4, 5, 15, 16, 17, 63, 64, 65, 127, 128, 129, 137, 255, 256, 257, 383, 384, 385,
    511, 512, 513, 640, 641, 767, 768, 769, 895, 896, 897, 1_023, 137, 512,
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

fn messages() -> (Vec<Vec<M31>>, Vec<Vec<QM31>>) {
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
                    value.c0.a = value.c0.a.add(M31((helper * 4_099 + row + 1) as u32));
                    value
                })
                .collect()
        })
        .collect();
    (c1, c2)
}

fn tree<const N: usize>(leaves: &[[u8; N]], tag: u8) -> Vec<Vec<[u8; 32]>> {
    let mut levels = vec![leaves
        .iter()
        .map(|leaf| leaf_hash(HOST_HASH, tag, leaf))
        .collect::<Vec<_>>()];
    while levels.last().unwrap().len() > 1 {
        levels.push(
            levels
                .last()
                .unwrap()
                .chunks_exact(4)
                .map(|children| node_hash4(HOST_HASH, children.try_into().unwrap()))
                .collect(),
        );
    }
    levels
}

fn frontier(levels: &[Vec<[u8; 32]>], indices: &[u32]) -> Vec<[u8; 32]> {
    let mut result = Vec::new();
    let mut current = indices.to_vec();
    for level in &levels[..levels.len() - 1] {
        let mut next = Vec::new();
        let mut position = 0;
        while position < current.len() {
            let parent = current[position] >> 2;
            let mut present = 0u8;
            while position < current.len() && current[position] >> 2 == parent {
                present |= 1 << (current[position] & 3);
                position += 1;
            }
            for slot in 0..4u32 {
                if present & (1 << slot) == 0 {
                    result.push(level[(4 * parent + slot) as usize]);
                }
            }
            next.push(parent);
        }
        current = next;
    }
    result
}

fn append_frontier(bytes: &mut Vec<u8>, nodes: &[[u8; 32]]) {
    bytes.extend_from_slice(&(nodes.len() as u32).to_le_bytes());
    for node in nodes {
        bytes.extend_from_slice(node);
    }
}

fn serialize_suffix(
    queries: &[u32],
    c1_leaves: &[[u8; CIRCLE_C1_LEAF_BYTES]],
    c2_leaves: &[[u8; CIRCLE_C2_LEAF_BYTES]],
    folds: &CircleFoldCommitments,
) -> Vec<u8> {
    let indices = derive_circle_line_query_indices(queries).unwrap();
    let c1_tree = tree(c1_leaves, CIRCLE_C1_LAYER0_TAG);
    let c2_tree = tree(c2_leaves, CIRCLE_C2_LAYER0_TAG);
    let mut bytes = Vec::new();

    bytes.extend_from_slice(&(indices.layer0.len() as u16).to_le_bytes());
    for &index in &indices.layer0 {
        bytes.extend_from_slice(&c1_leaves[index as usize]);
    }
    for &index in &indices.layer0 {
        bytes.extend_from_slice(&c2_leaves[index as usize]);
    }
    append_frontier(&mut bytes, &frontier(&c1_tree, &indices.layer0));
    append_frontier(&mut bytes, &frontier(&c2_tree, &indices.layer0));

    for layer in 0..CIRCLE_LINE_LAYER_COUNT {
        let leaves = &folds.committed_leaves[layer];
        let levels = tree(leaves, CIRCLE_LINE_TAGS[layer]);
        assert_eq!(levels.last().unwrap()[0], folds.roots[layer]);
        bytes.extend_from_slice(&(indices.later[layer].len() as u16).to_le_bytes());
        for &index in &indices.later[layer] {
            bytes.extend_from_slice(&leaves[index as usize]);
        }
        append_frontier(&mut bytes, &frontier(&levels, &indices.later[layer]));
    }
    bytes
}

struct Fixture {
    prefix: [u8; CANDIDATE_PREFIX_LEN],
    c1_leaves: Vec<[u8; CIRCLE_C1_LEAF_BYTES]>,
    c2_leaves: Vec<[u8; CIRCLE_C2_LEAF_BYTES]>,
    combined_codeword: Vec<QM31>,
    combined_message: Vec<QM31>,
    folds: CircleFoldCommitments,
    gamma: QM31,
    alphas: [QM31; 4],
}

impl Fixture {
    fn new() -> Self {
        let (c1_messages, c2_messages) = messages();
        let encoder = CircleEncoder::new();
        let c1_codewords = encoder.encode_c1_columns(&c1_messages).unwrap();
        let c2_codewords = encoder.encode_c2_columns(&c2_messages).unwrap();
        let c1_leaves = c1_layer0_leaves(&c1_codewords).unwrap();
        let c2_leaves = c2_layer0_leaves(&c2_codewords).unwrap();
        let c1_root = c1_layer0_root(&c1_codewords, HOST_HASH).unwrap();
        let c2_root = c2_layer0_root(&c2_codewords, HOST_HASH).unwrap();
        let gamma = q([17, 29, 43, 71]);
        let alphas = [
            q([101, 307, 401, 809]),
            q([131, 313, 419, 811]),
            q([151, 331, 431, 821]),
            q([181, 337, 439, 823]),
        ];
        let combined_codeword =
            gamma_combine_codewords(&c1_codewords, &c2_codewords, gamma).unwrap();
        let combined_message = gamma_combine_messages(&c1_messages, &c2_messages, gamma).unwrap();
        let folds =
            build_fold_commitments(&combined_codeword, &combined_message, alphas, HOST_HASH)
                .unwrap();
        let z = core::array::from_fn(|coordinate| {
            let base = coordinate as u32 * 17 + 3;
            q([base, base + 2, base + 4, base + 8])
        });
        let statement_evaluations =
            candidate_statement_evaluations(&c1_messages, &c2_messages, &z).unwrap();
        let ood_values = core::array::from_fn(|round| {
            core::array::from_fn(|sample| {
                let base = (round * 101 + sample * 13 + 1) as u32;
                q([base, base + 1, base + 2, base + 3])
            })
        });
        let sumchecks = core::array::from_fn(|round| {
            core::array::from_fn(|coefficient| {
                let base = (round * 131 + coefficient * 19 + 7) as u32;
                q([base, base + 3, base + 5, base + 9])
            })
        });
        let prefix = serialize_candidate_prefix(&CandidatePrefixMaterial {
            c1_root,
            c2_root,
            statement_evaluations,
            later_roots: folds.roots,
            ood_values,
            sumchecks,
            final_coefficients: folds.final_coefficients,
            nonce: 0x6f70_656e_696e_6773,
            fold_nonces: [0; CANDIDATE_ROUND_COUNT],
        });
        Self {
            prefix,
            c1_leaves,
            c2_leaves,
            combined_codeword,
            combined_message,
            folds,
            gamma,
            alphas,
        }
    }

    fn suffix(&self) -> Vec<u8> {
        serialize_suffix(&RAW_QUERIES, &self.c1_leaves, &self.c2_leaves, &self.folds)
    }
}

fn verify_full<'a>(
    proof: &'a [u8],
    queries: &[u32],
    gamma: QM31,
    alphas: [QM31; 4],
) -> Result<aspis_core::circle_openings::VerifiedCircleOpenings<'a>, CircleOpeningsError> {
    let (prefix, suffix) = CandidatePrefix::parse_from_proof(proof).unwrap();
    verify_and_check_circle_openings_for_prefix(HOST_HASH, &prefix, queries, suffix, gamma, alphas)
}

#[test]
fn exact_full_suffix_authenticates_and_corruption_boundaries_are_distinct() {
    let fixture = Fixture::new();
    let suffix = fixture.suffix();
    let mut proof = fixture.prefix.to_vec();
    proof.extend_from_slice(&suffix);
    let verified = verify_full(&proof, &RAW_QUERIES, fixture.gamma, fixture.alphas).unwrap();
    let indices = derive_circle_line_query_indices(&RAW_QUERIES).unwrap();

    assert_eq!(RAW_QUERIES.len(), 36);
    assert_eq!(indices.layer0.len(), 34);
    assert_eq!(indices.later.each_ref().map(Vec::len), [21, 18, 15]);
    assert_eq!(verified.layer0.unique_count, indices.layer0.len());
    assert_eq!(verified.later.indices, indices);

    let query = 137u32;
    let ordinal = verified.later.indices.layer0.binary_search(&query).unwrap();
    let leaves = verified.query_leaves(query).unwrap();
    assert_eq!(leaves.c1, fixture.c1_leaves[query as usize]);
    assert_eq!(leaves.c2, fixture.c2_leaves[query as usize]);
    assert_eq!(leaves.c1, verified.layer0.c1_leaf(ordinal).unwrap());
    assert_eq!(leaves.c2, verified.layer0.c2_leaf(ordinal).unwrap());
    for layer in 1..=3u8 {
        let slot = verified.later.query_leaf_slot(query, layer).unwrap();
        let layer_index = usize::from(layer - 1);
        let incoming_index = query >> (2 * u32::from(layer - 1));
        assert_eq!(slot.leaf_index, incoming_index >> 2);
        assert_eq!(slot.slot, (incoming_index & 3) as u8);
        assert_eq!(leaves.later[layer_index], slot.leaf);
        assert_eq!(
            slot.value(),
            fixture.folds.committed_evaluations[layer_index][incoming_index as usize]
        );
    }

    eprintln!(
        "suffix_len={} suffix_sha={} layer0_end={} layer0_frontiers={:?} later_ends={:?} later_frontiers={:?}",
        suffix.len(),
        Sha256::digest(&suffix)
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>(),
        verified.layer0.offsets.end,
        [verified.layer0.c1_frontier.len() / 32, verified.layer0.c2_frontier.len() / 32],
        verified
            .later
            .openings
            .layers
            .each_ref()
            .map(|opening| opening.offsets.record_end),
        verified
            .later
            .openings
            .layers
            .each_ref()
            .map(|opening| opening.frontier.len() / 32),
    );

    let layer0_c1_offset = CANDIDATE_PREFIX_LEN + verified.layer0.offsets.c1_leaves;
    let mut bad_layer0 = proof.clone();
    bad_layer0[layer0_c1_offset] ^= 1;
    assert_eq!(
        verify_full(&bad_layer0, &RAW_QUERIES, fixture.gamma, fixture.alphas),
        Err(CircleOpeningsError::Layer0(
            CircleMerkleError::C1MerkleMismatch
        ))
    );

    let later_start = CANDIDATE_PREFIX_LEN + verified.layer0.offsets.end;
    let layer2_leaf_offset = later_start + verified.later.openings.layers[1].offsets.leaves;
    let mut bad_later = proof.clone();
    bad_later[layer2_leaf_offset] ^= 1;
    assert_eq!(
        verify_full(&bad_later, &RAW_QUERIES, fixture.gamma, fixture.alphas),
        Err(CircleOpeningsError::Later(
            CircleLineMerkleError::MerkleMismatch { layer: 2 }
        ))
    );

    let final_offset = CANDIDATE_PREFIX_OFFSETS.final_polynomial_start;
    let mut bad_arithmetic = proof.clone();
    let value = QM31::from_le_bytes(&bad_arithmetic[final_offset..final_offset + 16])
        .unwrap()
        .add(QM31::ONE);
    value.write_le_bytes(&mut bad_arithmetic[final_offset..final_offset + 16]);
    assert_eq!(
        verify_full(&bad_arithmetic, &RAW_QUERIES, fixture.gamma, fixture.alphas,),
        Err(CircleOpeningsError::Query(
            CircleQueryError::TerminalValueMismatch { final_index: 0 }
        ))
    );

    let mut bad_layer0_count = proof.clone();
    bad_layer0_count[CANDIDATE_PREFIX_LEN..CANDIDATE_PREFIX_LEN + 2]
        .copy_from_slice(&35u16.to_le_bytes());
    assert_eq!(
        verify_full(
            &bad_layer0_count,
            &RAW_QUERIES,
            fixture.gamma,
            fixture.alphas,
        ),
        Err(CircleOpeningsError::Layer0(
            CircleMerkleError::CountMismatch {
                expected: 34,
                actual: 35,
            }
        ))
    );

    let mut bad_later_count = proof.clone();
    let layer1_count = later_start + verified.later.openings.layers[0].offsets.unique_count;
    bad_later_count[layer1_count..layer1_count + 2].copy_from_slice(&29u16.to_le_bytes());
    assert_eq!(
        verify_full(
            &bad_later_count,
            &RAW_QUERIES,
            fixture.gamma,
            fixture.alphas,
        ),
        Err(CircleOpeningsError::Later(
            CircleLineMerkleError::CountMismatch {
                layer: 1,
                expected: 21,
                actual: 29,
            }
        ))
    );

    let mut trailing = proof.clone();
    trailing.push(0xa5);
    assert!(matches!(
        verify_full(&trailing, &RAW_QUERIES, fixture.gamma, fixture.alphas),
        Err(CircleOpeningsError::Later(
            CircleLineMerkleError::TrailingBytes { remaining: 1, .. }
        ))
    ));

    let mut alternate_alphas = fixture.alphas;
    alternate_alphas[0] = alternate_alphas[0].add(QM31::ONE);
    let alternate_folds = build_fold_commitments(
        &fixture.combined_codeword,
        &fixture.combined_message,
        alternate_alphas,
        HOST_HASH,
    )
    .unwrap();
    let alternate_suffix = serialize_suffix(
        &RAW_QUERIES,
        &fixture.c1_leaves,
        &fixture.c2_leaves,
        &alternate_folds,
    );
    let mut mixed = fixture.prefix.to_vec();
    mixed.extend_from_slice(&suffix[..verified.layer0.offsets.end]);
    mixed.extend_from_slice(&alternate_suffix[verified.layer0.offsets.end..]);
    assert_eq!(
        verify_full(&mixed, &RAW_QUERIES, fixture.gamma, fixture.alphas),
        Err(CircleOpeningsError::Later(
            CircleLineMerkleError::MerkleMismatch { layer: 1 }
        ))
    );

    assert_eq!(
        verify_full(
            &proof,
            &RAW_QUERIES[..RAW_QUERIES.len() - 1],
            fixture.gamma,
            fixture.alphas,
        ),
        Err(CircleOpeningsError::QueryCountMismatch {
            expected: 36,
            actual: 35,
        })
    );
    let mut out_of_range = RAW_QUERIES;
    out_of_range[0] = 1_024;
    assert_eq!(
        verify_full(&proof, &out_of_range, fixture.gamma, fixture.alphas),
        Err(CircleOpeningsError::Later(
            CircleLineMerkleError::QueryOutOfRange { query: 1_024 }
        ))
    );

    assert_eq!(CANDIDATE_OOD_SAMPLES, 2);
    assert_eq!(CANDIDATE_ROUND_COUNT, 4);
    assert_eq!(SUMCHECK_COEFFICIENTS, 7);
    assert_eq!(CANDIDATE_FINAL_POLY_LEN, 4);
}

#[test]
fn rate32_q29_odd_depth_opening_and_query_chain_roundtrip() {
    const DOMAIN_LOG: u32 = 15;
    const CODEWORD_LEN: usize = 1 << DOMAIN_LOG;
    const FIBER_COUNT: usize = CODEWORD_LEN / 4;
    let (c1_messages, c2_messages) = messages();
    let encoder = CircleEncoder::new_for_domain_log(DOMAIN_LOG);
    let c1_codewords = encoder.encode_c1_columns(&c1_messages).unwrap();
    let c2_codewords = encoder.encode_c2_columns(&c2_messages).unwrap();
    let c1_leaves = c1_layer0_leaves_for_codeword_len(&c1_codewords, CODEWORD_LEN).unwrap();
    let c2_leaves = c2_layer0_leaves_for_codeword_len(&c2_codewords, CODEWORD_LEN).unwrap();
    let c1_root = c1_layer0_root_for_codeword_len(&c1_codewords, CODEWORD_LEN, HOST_HASH).unwrap();
    let c2_root = c2_layer0_root_for_codeword_len(&c2_codewords, CODEWORD_LEN, HOST_HASH).unwrap();
    let gamma = q([23, 47, 89, 167]);
    let alphas = [
        q([211, 223, 227, 229]),
        q([233, 239, 241, 251]),
        q([257, 263, 269, 271]),
        q([277, 281, 283, 293]),
    ];
    let combined_codeword =
        gamma_combine_codewords_for_len(&c1_codewords, &c2_codewords, gamma, CODEWORD_LEN).unwrap();
    let combined_message = gamma_combine_messages(&c1_messages, &c2_messages, gamma).unwrap();
    let folds = build_fold_commitments_for_domain_log(
        &combined_codeword,
        &combined_message,
        alphas,
        DOMAIN_LOG,
        HOST_HASH,
    )
    .unwrap();
    let queries: Vec<u32> = (0..29)
        .map(|i| ((i * 277 + i * i * 19 + 11) % FIBER_COUNT) as u32)
        .collect();
    assert_eq!(queries.len(), 29);
    let suffix = serialize_candidate_openings_for_fiber_count(
        &queries,
        &c1_leaves,
        &c2_leaves,
        &folds,
        FIBER_COUNT,
        HOST_HASH,
    )
    .unwrap();
    let verified = verify_and_check_circle_openings_for_geometry(
        HOST_HASH,
        &c1_root,
        &c2_root,
        &folds.roots,
        &queries,
        &suffix,
        gamma,
        alphas,
        folds.final_coefficients,
        RATE32_CIRCLE_OPENING_GEOMETRY,
    )
    .unwrap();
    assert_eq!(verified.later.indices.layer0.len(), 29);

    let mut corrupt = suffix.clone();
    corrupt[verified.layer0.offsets.c1_leaves] ^= 1;
    assert!(verify_and_check_circle_openings_for_geometry(
        HOST_HASH,
        &c1_root,
        &c2_root,
        &folds.roots,
        &queries,
        &corrupt,
        gamma,
        alphas,
        folds.final_coefficients,
        RATE32_CIRCLE_OPENING_GEOMETRY,
    )
    .is_err());
}
