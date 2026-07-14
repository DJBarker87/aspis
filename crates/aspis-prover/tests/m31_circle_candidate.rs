#[path = "support/m31_circle_reference.rs"]
mod circle_reference;

use aspis_core::circle_prefix::{CandidatePrefix, CANDIDATE_OOD_SAMPLES, CANDIDATE_ROUND_COUNT};
use aspis_core::field::{qm31_power_table, CM31, M31, P, QM31};
use aspis_core::sumcheck::SUMCHECK_COEFFICIENTS;
use aspis_prover::circle_candidate::{
    build_fold_commitments, c1_layer0_leaf, c1_layer0_leaves, c1_layer0_root, c2_layer0_leaf,
    c2_layer0_leaves, c2_layer0_root, candidate_statement_evaluations, gamma_combine_codewords,
    gamma_combine_messages, gamma_combine_opened_fiber, gamma_combine_statement_evaluations,
    serialize_candidate_prefix, xor11_point, CandidatePrefixMaterial, CircleCandidateError,
    CircleEncoder, C1_COLUMNS, C1_LAYER0_LEAF_BYTES, C2_COLUMNS, C2_LAYER0_LEAF_BYTES,
    CODEWORD_LEN, COMBINED_COMMITTED_LAYERS, COMBINED_LAYER_LEAF_BYTES, FIBER_COUNT, FIBER_SLOTS,
    FINAL_COEFFICIENT_LEN, FINAL_EVALUATION_LEN, M31_CIRCLE_C1_LAYER0_TAG,
    M31_CIRCLE_C2_LAYER0_TAG, TOTAL_COLUMNS, TRACE_LEN,
};
use aspis_prover::{multilinear_eval, HOST_HASH};
use circle_reference::encode_circle;
use sha2::{Digest as _, Sha256};

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

fn multilinear_eval_qm31(coefficients: &[QM31], point: &[QM31]) -> QM31 {
    assert_eq!(coefficients.len(), 1usize << point.len());
    let mut layer = coefficients.to_vec();
    for coordinate in point.iter().rev() {
        layer = layer
            .chunks_exact(2)
            .map(|pair| pair[0].add(coordinate.mul(pair[1].sub(pair[0]))))
            .collect();
    }
    layer[0]
}

fn reference_encode_qm31(message: &[QM31]) -> Vec<QM31> {
    let coordinate = |value: QM31, index: usize| match index {
        0 => value.c0.a,
        1 => value.c0.b,
        2 => value.c1.a,
        3 => value.c1.b,
        _ => unreachable!(),
    };
    let encoded = core::array::from_fn::<_, 4, _>(|index| {
        let base = message
            .iter()
            .copied()
            .map(|value| coordinate(value, index))
            .collect::<Vec<_>>();
        encode_circle(&base, 12)
    });
    (0..CODEWORD_LEN)
        .map(|index| QM31 {
            c0: CM31::new(encoded[0][index], encoded[1][index]),
            c1: CM31::new(encoded[2][index], encoded[3][index]),
        })
        .collect()
}

fn digest_m31_codewords(codewords: &[Vec<M31>]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    for codeword in codewords {
        for value in codeword {
            hasher.update(value.to_le_bytes());
        }
    }
    hasher.finalize().into()
}

fn digest_qm31_codewords(codewords: &[Vec<QM31>]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    let mut bytes = [0u8; 16];
    for codeword in codewords {
        for value in codeword {
            value.write_le_bytes(&mut bytes);
            hasher.update(bytes);
        }
    }
    hasher.finalize().into()
}

fn digest_leaves<const N: usize>(leaves: &[[u8; N]]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    for leaf in leaves {
        hasher.update(leaf);
    }
    hasher.finalize().into()
}

fn reference_c1_leaf(codewords: &[Vec<M31>], fiber: usize) -> [u8; C1_LAYER0_LEAF_BYTES] {
    let mut leaf = [0u8; C1_LAYER0_LEAF_BYTES];
    let mut offset = 0;
    for slot in 0..FIBER_SLOTS {
        for codeword in codewords {
            leaf[offset..offset + 4].copy_from_slice(&codeword[4 * fiber + slot].to_le_bytes());
            offset += 4;
        }
    }
    leaf
}

fn reference_c2_leaf(codewords: &[Vec<QM31>], fiber: usize) -> [u8; C2_LAYER0_LEAF_BYTES] {
    let mut leaf = [0u8; C2_LAYER0_LEAF_BYTES];
    let mut offset = 0;
    for codeword in codewords {
        for slot in 0..FIBER_SLOTS {
            codeword[4 * fiber + slot].write_le_bytes(&mut leaf[offset..offset + 16]);
            offset += 16;
        }
    }
    leaf
}

fn hash_leaf<const N: usize>(tag: u8, leaf: &[u8; N]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update([0x10, tag]);
    hasher.update(leaf);
    hasher.finalize().into()
}

fn reference_radix4_root<const N: usize>(tag: u8, leaves: &[[u8; N]]) -> [u8; 32] {
    let mut level = leaves
        .iter()
        .map(|leaf| hash_leaf(tag, leaf))
        .collect::<Vec<_>>();
    while level.len() > 1 {
        assert_eq!(level.len() % 4, 0);
        level = level
            .chunks_exact(4)
            .map(|children| {
                let mut hasher = Sha256::new();
                hasher.update([0x12]);
                for child in children {
                    hasher.update(child);
                }
                hasher.finalize().into()
            })
            .collect();
    }
    level[0]
}

fn sampled_indices() -> Vec<usize> {
    let mut indices = vec![0, 1, 2, 3, 548, 549, 550, 551, 4092, 4093, 4094, 4095];
    let mut rng = Rng(0x424f_554e_4441_5259);
    for _ in 0..32 {
        indices.push(rng.next() as usize % CODEWORD_LEN);
    }
    indices.sort_unstable();
    indices.dedup();
    indices
}

fn sampled_fibers() -> Vec<usize> {
    let mut fibers = vec![0, 1, 137, 511, 512, 1022, 1023];
    let mut rng = Rng(0x4649_4245_5253_3132);
    for _ in 0..24 {
        fibers.push(rng.next() as usize % FIBER_COUNT);
    }
    fibers.sort_unstable();
    fibers.dedup();
    fibers
}

#[test]
fn full_codewords_leaves_and_roots_match_independent_circle_reference() {
    let (c1_messages, c2_messages) = fixture();
    let encoder = CircleEncoder::new();
    let actual_c1 = encoder.encode_c1_columns(&c1_messages).unwrap();
    let actual_c2 = encoder.encode_c2_columns(&c2_messages).unwrap();
    let expected_c1 = c1_messages
        .iter()
        .map(|message| encode_circle(message, 12))
        .collect::<Vec<_>>();
    let expected_c2 = c2_messages
        .iter()
        .map(|message| reference_encode_qm31(message))
        .collect::<Vec<_>>();

    // Full serialized codeword digests cover every symbol in all 51 columns.
    assert_eq!(
        digest_m31_codewords(&actual_c1),
        digest_m31_codewords(&expected_c1)
    );
    assert_eq!(
        digest_qm31_codewords(&actual_c2),
        digest_qm31_codewords(&expected_c2)
    );
    for index in sampled_indices() {
        for column in 0..C1_COLUMNS {
            assert_eq!(actual_c1[column][index], expected_c1[column][index]);
        }
        for helper in 0..C2_COLUMNS {
            assert_eq!(actual_c2[helper][index], expected_c2[helper][index]);
        }
    }

    let actual_c1_leaves = c1_layer0_leaves(&actual_c1).unwrap();
    let actual_c2_leaves = c2_layer0_leaves(&actual_c2).unwrap();
    let expected_c1_leaves = (0..FIBER_COUNT)
        .map(|fiber| reference_c1_leaf(&expected_c1, fiber))
        .collect::<Vec<_>>();
    let expected_c2_leaves = (0..FIBER_COUNT)
        .map(|fiber| reference_c2_leaf(&expected_c2, fiber))
        .collect::<Vec<_>>();
    assert_eq!(
        digest_leaves(&actual_c1_leaves),
        digest_leaves(&expected_c1_leaves)
    );
    assert_eq!(
        digest_leaves(&actual_c2_leaves),
        digest_leaves(&expected_c2_leaves)
    );
    for fiber in sampled_fibers() {
        assert_eq!(actual_c1_leaves[fiber], expected_c1_leaves[fiber]);
        assert_eq!(actual_c2_leaves[fiber], expected_c2_leaves[fiber]);
        assert_eq!(
            c1_layer0_leaf(&actual_c1, fiber).unwrap(),
            expected_c1_leaves[fiber]
        );
        assert_eq!(
            c2_layer0_leaf(&actual_c2, fiber).unwrap(),
            expected_c2_leaves[fiber]
        );
    }

    assert_eq!(
        c1_layer0_root(&actual_c1, HOST_HASH).unwrap(),
        reference_radix4_root(M31_CIRCLE_C1_LAYER0_TAG, &expected_c1_leaves)
    );
    assert_eq!(
        c2_layer0_root(&actual_c2, HOST_HASH).unwrap(),
        reference_radix4_root(M31_CIRCLE_C2_LAYER0_TAG, &expected_c2_leaves)
    );
    assert_ne!(
        reference_radix4_root(M31_CIRCLE_C1_LAYER0_TAG, &expected_c1_leaves),
        reference_radix4_root(M31_CIRCLE_C2_LAYER0_TAG, &expected_c1_leaves)
    );
}

#[test]
fn gamma_combination_and_corruptions_pin_slot_and_helper_order() {
    let (c1_messages, c2_messages) = fixture();
    let encoder = CircleEncoder::new();
    let mut c1 = encoder.encode_c1_columns(&c1_messages).unwrap();
    let c2 = encoder.encode_c2_columns(&c2_messages).unwrap();
    let fiber = 137;
    let gamma = Rng(0x4741_4d4d_4150_4f57).qm31();
    let c1_leaf = c1_layer0_leaf(&c1, fiber).unwrap();
    let c2_leaf = c2_layer0_leaf(&c2, fiber).unwrap();
    let combined = gamma_combine_opened_fiber(&c1_leaf, &c2_leaf, gamma).unwrap();
    let powers = qm31_power_table::<TOTAL_COLUMNS>(gamma);
    let expected = core::array::from_fn(|slot| {
        let mut sum = QM31::ZERO;
        for column in 0..C1_COLUMNS {
            sum = sum.add(powers[column].mul_m31(c1[column][4 * fiber + slot]));
        }
        for helper in 0..C2_COLUMNS {
            sum = sum.add(powers[C1_COLUMNS + helper].mul(c2[helper][4 * fiber + slot]));
        }
        sum
    });
    assert_eq!(combined, expected);

    let root = c1_layer0_root(&c1, HOST_HASH).unwrap();
    c1[17][4 * fiber + 2] = c1[17][4 * fiber + 2].add(M31::ONE);
    assert_ne!(c1_layer0_root(&c1, HOST_HASH).unwrap(), root);

    let mut changed_leaf = c1_leaf;
    let changed = M31::from_le_bytes(changed_leaf[0..4].try_into().unwrap())
        .unwrap()
        .add(M31::ONE);
    changed_leaf[0..4].copy_from_slice(&changed.to_le_bytes());
    assert_ne!(
        gamma_combine_opened_fiber(&changed_leaf, &c2_leaf, gamma).unwrap(),
        combined
    );

    let mut noncanonical_c1 = c1_leaf;
    noncanonical_c1[0..4].copy_from_slice(&P.to_le_bytes());
    assert_eq!(
        gamma_combine_opened_fiber(&noncanonical_c1, &c2_leaf, gamma),
        Err(CircleCandidateError::NonCanonicalM31 { offset: 0 })
    );
    let mut noncanonical_c2 = c2_leaf;
    noncanonical_c2[0..4].copy_from_slice(&P.to_le_bytes());
    assert_eq!(
        gamma_combine_opened_fiber(&c1_leaf, &noncanonical_c2, gamma),
        Err(CircleCandidateError::NonCanonicalQm31 { offset: 0 })
    );

    let mut swapped_helpers = c2_leaf;
    let (h1, h2) = swapped_helpers.split_at_mut(C2_LAYER0_LEAF_BYTES / 2);
    h1.swap_with_slice(h2);
    assert_ne!(
        gamma_combine_opened_fiber(&c1_leaf, &swapped_helpers, gamma).unwrap(),
        combined
    );
}

#[test]
fn two_point_statement_block_matches_the_gamma_combined_message() {
    let (c1_messages, c2_messages) = fixture();
    let mut rng = Rng(0x5354_4154_454d_4c45);
    let z = core::array::from_fn(|_| rng.qm31());
    let second = xor11_point(&z);
    assert_eq!(second[..8], z[..8]);
    assert_eq!(second[8], QM31::ONE.sub(z[8]));
    assert_eq!(second[9], QM31::ONE.sub(z[9]));

    let evaluations = candidate_statement_evaluations(&c1_messages, &c2_messages, &z).unwrap();
    assert_eq!(evaluations[0], multilinear_eval(&c1_messages[0], &z));
    assert_eq!(evaluations[48], multilinear_eval(&c1_messages[48], &z));
    assert_eq!(evaluations[49], multilinear_eval_qm31(&c2_messages[0], &z));
    assert_eq!(evaluations[50], multilinear_eval_qm31(&c2_messages[1], &z));
    assert_eq!(evaluations[51], multilinear_eval(&c1_messages[0], &second));
    assert_eq!(
        evaluations[101],
        multilinear_eval_qm31(&c2_messages[1], &second)
    );

    let gamma = rng.qm31();
    let claims = gamma_combine_statement_evaluations(&evaluations, gamma);
    let combined_message = gamma_combine_messages(&c1_messages, &c2_messages, gamma).unwrap();
    assert_eq!(claims[0], multilinear_eval_qm31(&combined_message, &z));
    assert_eq!(claims[1], multilinear_eval_qm31(&combined_message, &second));

    let mut wrong_order = evaluations;
    wrong_order.swap(49, 50);
    assert_ne!(
        gamma_combine_statement_evaluations(&wrong_order, gamma),
        claims
    );
}

#[test]
fn combined_circle_folds_roots_and_terminal_tensor_are_one_consistent_path() {
    let (c1_messages, c2_messages) = fixture();
    let encoder = CircleEncoder::new();
    let c1 = encoder.encode_c1_columns(&c1_messages).unwrap();
    let c2 = encoder.encode_c2_columns(&c2_messages).unwrap();
    let mut rng = Rng(0x464f_4c44_4349_5243);
    let gamma = rng.qm31();
    let alphas = core::array::from_fn(|_| rng.qm31());
    let combined_codeword = gamma_combine_codewords(&c1, &c2, gamma).unwrap();
    let combined_message = gamma_combine_messages(&c1_messages, &c2_messages, gamma).unwrap();

    for fiber in sampled_fibers() {
        let opened = gamma_combine_opened_fiber(
            &c1_layer0_leaf(&c1, fiber).unwrap(),
            &c2_layer0_leaf(&c2, fiber).unwrap(),
            gamma,
        )
        .unwrap();
        assert_eq!(
            opened.as_slice(),
            &combined_codeword[4 * fiber..4 * fiber + 4]
        );
    }

    let folds =
        build_fold_commitments(&combined_codeword, &combined_message, alphas, HOST_HASH).unwrap();
    assert_eq!(
        folds
            .committed_evaluations
            .each_ref()
            .map(|values| values.len()),
        [1024, 256, 64]
    );
    assert_eq!(
        folds.committed_leaves.each_ref().map(|leaves| leaves.len()),
        [256, 64, 16]
    );
    assert_eq!(folds.final_evaluations.len(), FINAL_EVALUATION_LEN);
    assert_eq!(folds.final_coefficients.len(), FINAL_COEFFICIENT_LEN);
    let mut fold_hasher = Sha256::new();
    for root in &folds.roots {
        fold_hasher.update(root);
    }
    for value in &folds.final_evaluations {
        let mut bytes = [0u8; 16];
        value.write_le_bytes(&mut bytes);
        fold_hasher.update(bytes);
    }
    for value in &folds.final_coefficients {
        let mut bytes = [0u8; 16];
        value.write_le_bytes(&mut bytes);
        fold_hasher.update(bytes);
    }
    let fold_digest: [u8; 32] = fold_hasher.finalize().into();
    assert_eq!(
        fold_digest,
        [
            0x0a, 0x8b, 0xe4, 0xac, 0x36, 0x1d, 0x87, 0x67, 0x8a, 0xe3, 0x4b, 0x08, 0xca, 0x68,
            0xe5, 0xfb, 0x43, 0xef, 0xd1, 0x1b, 0xcf, 0x65, 0x9a, 0x08, 0x91, 0x84, 0x71, 0x1b,
            0xcc, 0x20, 0xc8, 0xaf,
        ]
    );
    for layer in 0..COMBINED_COMMITTED_LAYERS {
        assert_eq!(
            folds.roots[layer],
            reference_radix4_root(
                M31_CIRCLE_C1_LAYER0_TAG + layer as u8 + 1,
                &folds.committed_leaves[layer],
            )
        );
        for (leaf, values) in folds.committed_leaves[layer]
            .iter()
            .zip(folds.committed_evaluations[layer].chunks_exact(4))
        {
            let mut expected = [0u8; COMBINED_LAYER_LEAF_BYTES];
            for (slot, value) in values.iter().enumerate() {
                value.write_le_bytes(&mut expected[slot * 16..slot * 16 + 16]);
            }
            assert_eq!(*leaf, expected);
        }
    }

    let mut changed_alphas = alphas;
    changed_alphas[2] = changed_alphas[2].add(QM31::ONE);
    let changed = build_fold_commitments(
        &combined_codeword,
        &combined_message,
        changed_alphas,
        HOST_HASH,
    )
    .unwrap();
    assert_ne!(changed.roots[2], folds.roots[2]);
    assert_ne!(changed.final_coefficients, folds.final_coefficients);
}

#[test]
fn host_prefix_serializer_roundtrips_the_exact_core_parser_shape() {
    let (c1_messages, c2_messages) = fixture();
    let encoder = CircleEncoder::new();
    let c1 = encoder.encode_c1_columns(&c1_messages).unwrap();
    let c2 = encoder.encode_c2_columns(&c2_messages).unwrap();
    let c1_root = c1_layer0_root(&c1, HOST_HASH).unwrap();
    let c2_root = c2_layer0_root(&c2, HOST_HASH).unwrap();
    let mut rng = Rng(0x5052_4546_4958_5752);
    let gamma = rng.qm31();
    let alphas = core::array::from_fn(|_| rng.qm31());
    let combined_codeword = gamma_combine_codewords(&c1, &c2, gamma).unwrap();
    let combined_message = gamma_combine_messages(&c1_messages, &c2_messages, gamma).unwrap();
    let folds =
        build_fold_commitments(&combined_codeword, &combined_message, alphas, HOST_HASH).unwrap();
    let statement_evaluations = core::array::from_fn(|_| rng.qm31());
    let ood_values: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT] =
        core::array::from_fn(|_| core::array::from_fn(|_| rng.qm31()));
    let sumchecks: [[QM31; SUMCHECK_COEFFICIENTS]; CANDIDATE_ROUND_COUNT] =
        core::array::from_fn(|_| core::array::from_fn(|_| rng.qm31()));
    let nonce = 0x8877_6655_4433_2211;
    let bytes = serialize_candidate_prefix(&CandidatePrefixMaterial {
        c1_root,
        c2_root,
        statement_evaluations,
        later_roots: folds.roots,
        ood_values,
        sumchecks,
        final_coefficients: folds.final_coefficients,
        nonce,
        fold_nonces: [0; CANDIDATE_ROUND_COUNT],
    });
    let parsed = CandidatePrefix::parse_exact(&bytes).unwrap();
    assert_eq!(*parsed.c1_root, c1_root);
    assert_eq!(*parsed.c2_root, c2_root);
    assert_eq!(parsed.nonce, nonce);
    for (index, expected) in statement_evaluations.iter().enumerate() {
        assert_eq!(parsed.statement_evaluation(index), Some(*expected));
    }
    for (layer, (expected_oods, expected_sumcheck)) in ood_values.iter().zip(&sumchecks).enumerate()
    {
        if layer == 0 {
            assert!(parsed.rounds[layer].root.is_none());
        } else {
            assert_eq!(*parsed.rounds[layer].root.unwrap(), folds.roots[layer - 1]);
        }
        for (sample, expected) in expected_oods.iter().enumerate() {
            assert_eq!(parsed.rounds[layer].ood_value(sample), Some(*expected));
        }
        for (coefficient, expected) in expected_sumcheck.iter().enumerate() {
            assert_eq!(
                parsed.rounds[layer].sumcheck_coefficient(coefficient),
                Some(*expected)
            );
        }
    }
    for (coefficient, expected) in folds.final_coefficients.iter().enumerate() {
        assert_eq!(parsed.final_coefficient(coefficient), Some(*expected));
    }
    assert_eq!(
        <[u8; 32]>::from(Sha256::digest(bytes)),
        [
            0xa5, 0xf0, 0xe5, 0x3f, 0xaa, 0x4a, 0x77, 0x1a, 0x9c, 0x2d, 0x4a, 0x92, 0x8c, 0x6b,
            0x00, 0xaa, 0xa7, 0x18, 0xc1, 0x59, 0x4f, 0x2f, 0xfb, 0x75, 0xe0, 0x93, 0x82, 0xcb,
            0x8d, 0x35, 0xa0, 0x29,
        ]
    );
}

#[test]
fn exact_shape_checks_reject_ambiguous_messages_codewords_and_leaves() {
    let encoder = CircleEncoder::new();
    assert_eq!(
        encoder.encode_c1_message(&vec![M31::ZERO; TRACE_LEN - 1]),
        Err(CircleCandidateError::MessageLength {
            expected: TRACE_LEN,
            actual: TRACE_LEN - 1,
        })
    );
    assert_eq!(
        encoder.encode_c2_columns(&[]),
        Err(CircleCandidateError::ColumnCount {
            expected: C2_COLUMNS,
            actual: 0,
        })
    );

    let mut wrong = vec![vec![M31::ZERO; CODEWORD_LEN]; C1_COLUMNS];
    wrong[7].pop();
    assert_eq!(
        c1_layer0_leaf(&wrong, 0),
        Err(CircleCandidateError::CodewordLength {
            column: 7,
            expected: CODEWORD_LEN,
            actual: CODEWORD_LEN - 1,
        })
    );
    let exact = vec![vec![M31::ZERO; CODEWORD_LEN]; C1_COLUMNS];
    assert_eq!(
        c1_layer0_leaf(&exact, FIBER_COUNT),
        Err(CircleCandidateError::FiberIndex { index: FIBER_COUNT })
    );
    assert_eq!(
        gamma_combine_opened_fiber(
            &[0u8; C1_LAYER0_LEAF_BYTES - 1],
            &[0u8; C2_LAYER0_LEAF_BYTES],
            QM31::ONE,
        ),
        Err(CircleCandidateError::LeafLength {
            expected: C1_LAYER0_LEAF_BYTES,
            actual: C1_LAYER0_LEAF_BYTES - 1,
        })
    );
}
