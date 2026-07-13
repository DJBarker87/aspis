use aspis_core::circle_fri::{
    evaluate_final_line_tensor, fixed_circle_fiber_point, fixed_line_domain_x,
    fixed_line_fold_coordinates, map_fixed_query, normalized_circle_to_line_arity4_at_fiber,
    normalized_line_arity4_at_fiber, FixedQueryPath, LineArity4Coordinates, FIXED_FINAL_LINE_LAYER,
    FIXED_QUERY_FIBER_COUNT,
};
use aspis_core::circle_query::{
    c1_symbol_offset, c2_symbol_offset, check_fixed_circle_query, gamma_combine_fixed_layer0,
    later_slot_offset, CircleQueryError, CircleQueryLeaf, CIRCLE_QUERY_C1_LEAF_BYTES,
    CIRCLE_QUERY_C2_LEAF_BYTES, CIRCLE_QUERY_LATER_LEAF_BYTES,
};
use aspis_core::field::{CM31, M31, P, QM31};
use aspis_prover::circle_candidate::{
    build_fold_commitments, c1_layer0_leaves, c2_layer0_leaves, gamma_combine_codewords,
    gamma_combine_messages, CircleEncoder, CircleFoldCommitments, C1_COLUMNS, C2_COLUMNS,
    CODEWORD_LEN, TRACE_LEN,
};
use sha2::{Digest, Sha256};

fn host_hash(inputs: &[&[u8]]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    for input in inputs {
        hasher.update(input);
    }
    hasher.finalize().into()
}

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

struct Fixture {
    c1_messages: Vec<Vec<M31>>,
    c2_messages: Vec<Vec<QM31>>,
    c1_codewords: Vec<Vec<M31>>,
    c2_codewords: Vec<Vec<QM31>>,
    c1_leaves: Vec<[u8; CIRCLE_QUERY_C1_LEAF_BYTES]>,
    c2_leaves: Vec<[u8; CIRCLE_QUERY_C2_LEAF_BYTES]>,
    folds: CircleFoldCommitments,
    gamma: QM31,
    alphas: [QM31; 4],
}

fn fixture() -> Fixture {
    let mut rng = Rng(0x5155_4552_595f_4348);
    let c1_messages = (0..C1_COLUMNS)
        .map(|_| (0..TRACE_LEN).map(|_| rng.m31()).collect::<Vec<_>>())
        .collect::<Vec<_>>();
    let c2_messages = (0..C2_COLUMNS)
        .map(|_| (0..TRACE_LEN).map(|_| rng.qm31()).collect::<Vec<_>>())
        .collect::<Vec<_>>();
    let gamma = rng.qm31();
    let alphas = core::array::from_fn(|_| rng.qm31());
    let encoder = CircleEncoder::new();
    let c1_codewords = encoder.encode_c1_columns(&c1_messages).unwrap();
    let c2_codewords = encoder.encode_c2_columns(&c2_messages).unwrap();
    let c1_leaves = c1_layer0_leaves(&c1_codewords).unwrap();
    let c2_leaves = c2_layer0_leaves(&c2_codewords).unwrap();
    let combined_codeword = gamma_combine_codewords(&c1_codewords, &c2_codewords, gamma).unwrap();
    let combined_message = gamma_combine_messages(&c1_messages, &c2_messages, gamma).unwrap();
    let folds =
        build_fold_commitments(&combined_codeword, &combined_message, alphas, host_hash).unwrap();
    Fixture {
        c1_messages,
        c2_messages,
        c1_codewords,
        c2_codewords,
        c1_leaves,
        c2_leaves,
        folds,
        gamma,
        alphas,
    }
}

fn later_leaves(fixture: &Fixture, query: usize) -> [&[u8]; 3] {
    [
        &fixture.folds.committed_leaves[0][query >> 2],
        &fixture.folds.committed_leaves[1][query >> 4],
        &fixture.folds.committed_leaves[2][query >> 6],
    ]
}

fn check_fixture(
    fixture: &Fixture,
    query: usize,
    final_natural: [QM31; 4],
) -> Result<aspis_core::circle_query::CircleQueryCheck, CircleQueryError> {
    check_fixed_circle_query(
        &fixture.c1_leaves[query],
        &fixture.c2_leaves[query],
        later_leaves(fixture, query),
        query,
        fixture.gamma,
        fixture.alphas,
        final_natural,
    )
}

fn decode_later(leaf: &[u8]) -> [QM31; 4] {
    core::array::from_fn(|slot| {
        let offset = slot * 16;
        QM31::from_le_bytes(&leaf[offset..offset + 16]).unwrap()
    })
}

fn encode_later(values: [QM31; 4]) -> [u8; CIRCLE_QUERY_LATER_LEAF_BYTES] {
    let mut leaf = [0u8; CIRCLE_QUERY_LATER_LEAF_BYTES];
    for (slot, value) in values.into_iter().enumerate() {
        value.write_le_bytes(&mut leaf[slot * 16..slot * 16 + 16]);
    }
    leaf
}

fn sample_values(seed: u64) -> [QM31; 4] {
    let mut rng = Rng(seed);
    core::array::from_fn(|_| rng.qm31())
}

#[test]
fn all_1024_committed_candidate_query_paths_are_consistent() {
    let fixture = fixture();
    for query in 0..FIXED_QUERY_FIBER_COUNT {
        let checked = check_fixture(&fixture, query, fixture.folds.final_coefficients).unwrap();
        assert_eq!(checked.path.layer0_fiber, query);
        assert_eq!(checked.path.later[0].leaf, query >> 2);
        assert_eq!(checked.path.later[1].leaf, query >> 4);
        assert_eq!(checked.path.later[2].leaf, query >> 6);
        assert_eq!(checked.path.final_index, query >> 6);
        assert_eq!(
            checked.folded_values,
            [
                fixture.folds.committed_evaluations[0][query],
                fixture.folds.committed_evaluations[1][query >> 2],
                fixture.folds.committed_evaluations[2][query >> 4],
                fixture.folds.final_evaluations[query >> 6],
            ]
        );
    }
}

#[test]
fn exact_lengths_canonical_offsets_and_mismatch_offsets_are_explicit() {
    let fixture = fixture();
    let query = 0b10_01_11usize;
    let path = map_fixed_query(query).unwrap();

    assert_eq!(c1_symbol_offset(0, 0), Some(0));
    assert_eq!(c1_symbol_offset(3, 48), Some(780));
    assert_eq!(c1_symbol_offset(4, 0), None);
    assert_eq!(c2_symbol_offset(0, 0), Some(0));
    assert_eq!(c2_symbol_offset(1, 3), Some(112));
    assert_eq!(c2_symbol_offset(2, 0), None);
    assert_eq!(later_slot_offset(3), Some(48));
    assert_eq!(later_slot_offset(4), None);

    assert_eq!(
        check_fixed_circle_query(
            &fixture.c1_leaves[query][..CIRCLE_QUERY_C1_LEAF_BYTES - 1],
            &fixture.c2_leaves[query],
            later_leaves(&fixture, query),
            query,
            fixture.gamma,
            fixture.alphas,
            fixture.folds.final_coefficients,
        ),
        Err(CircleQueryError::LeafLength {
            leaf: CircleQueryLeaf::C1,
            expected: CIRCLE_QUERY_C1_LEAF_BYTES,
            actual: CIRCLE_QUERY_C1_LEAF_BYTES - 1,
        })
    );
    assert_eq!(
        check_fixed_circle_query(
            &fixture.c1_leaves[query],
            &fixture.c2_leaves[query][..CIRCLE_QUERY_C2_LEAF_BYTES - 1],
            later_leaves(&fixture, query),
            query,
            fixture.gamma,
            fixture.alphas,
            fixture.folds.final_coefficients,
        ),
        Err(CircleQueryError::LeafLength {
            leaf: CircleQueryLeaf::C2,
            expected: CIRCLE_QUERY_C2_LEAF_BYTES,
            actual: CIRCLE_QUERY_C2_LEAF_BYTES - 1,
        })
    );
    let short_later =
        &fixture.folds.committed_leaves[0][query >> 2][..CIRCLE_QUERY_LATER_LEAF_BYTES - 1];
    assert_eq!(
        check_fixed_circle_query(
            &fixture.c1_leaves[query],
            &fixture.c2_leaves[query],
            [
                short_later,
                &fixture.folds.committed_leaves[1][query >> 4],
                &fixture.folds.committed_leaves[2][query >> 6],
            ],
            query,
            fixture.gamma,
            fixture.alphas,
            fixture.folds.final_coefficients,
        ),
        Err(CircleQueryError::LeafLength {
            leaf: CircleQueryLeaf::Later(1),
            expected: CIRCLE_QUERY_LATER_LEAF_BYTES,
            actual: CIRCLE_QUERY_LATER_LEAF_BYTES - 1,
        })
    );

    let mut bad_c1 = fixture.c1_leaves[query];
    let bad_c1_offset = c1_symbol_offset(2, 7).unwrap();
    bad_c1[bad_c1_offset..bad_c1_offset + 4].copy_from_slice(&P.to_le_bytes());
    assert_eq!(
        check_fixed_circle_query(
            &bad_c1,
            &fixture.c2_leaves[query],
            later_leaves(&fixture, query),
            query,
            fixture.gamma,
            fixture.alphas,
            fixture.folds.final_coefficients,
        ),
        Err(CircleQueryError::NonCanonicalM31 {
            offset: bad_c1_offset,
        })
    );

    let mut bad_c2 = fixture.c2_leaves[query];
    let bad_c2_offset = c2_symbol_offset(1, 2).unwrap();
    bad_c2[bad_c2_offset..bad_c2_offset + 4].copy_from_slice(&P.to_le_bytes());
    assert_eq!(
        check_fixed_circle_query(
            &fixture.c1_leaves[query],
            &bad_c2,
            later_leaves(&fixture, query),
            query,
            fixture.gamma,
            fixture.alphas,
            fixture.folds.final_coefficients,
        ),
        Err(CircleQueryError::NonCanonicalQm31 {
            leaf: CircleQueryLeaf::C2,
            offset: bad_c2_offset,
        })
    );

    let mut bad_later = fixture.folds.committed_leaves[1][query >> 4];
    bad_later[48..52].copy_from_slice(&P.to_le_bytes());
    let later = [
        &fixture.folds.committed_leaves[0][query >> 2][..],
        &bad_later[..],
        &fixture.folds.committed_leaves[2][query >> 6][..],
    ];
    assert_eq!(
        check_fixed_circle_query(
            &fixture.c1_leaves[query],
            &fixture.c2_leaves[query],
            later,
            query,
            fixture.gamma,
            fixture.alphas,
            fixture.folds.final_coefficients,
        ),
        Err(CircleQueryError::NonCanonicalQm31 {
            leaf: CircleQueryLeaf::Later(2),
            offset: 48,
        })
    );

    let mut wrong_layer1 = fixture.folds.committed_leaves[0][query >> 2];
    let layer1_offset = usize::from(path.later[0].slot) * 16;
    let value = QM31::from_le_bytes(&wrong_layer1[layer1_offset..layer1_offset + 16]).unwrap();
    value
        .add(QM31::ONE)
        .write_le_bytes(&mut wrong_layer1[layer1_offset..layer1_offset + 16]);
    let later = [
        &wrong_layer1[..],
        &fixture.folds.committed_leaves[1][query >> 4][..],
        &fixture.folds.committed_leaves[2][query >> 6][..],
    ];
    assert_eq!(
        check_fixed_circle_query(
            &fixture.c1_leaves[query],
            &fixture.c2_leaves[query],
            later,
            query,
            fixture.gamma,
            fixture.alphas,
            fixture.folds.final_coefficients,
        ),
        Err(CircleQueryError::LayerValueMismatch {
            layer: 1,
            offset: layer1_offset,
        })
    );

    let mut bad_final = fixture.folds.final_coefficients;
    bad_final[0] = bad_final[0].add(QM31::ONE);
    assert_eq!(
        check_fixture(&fixture, query, bad_final),
        Err(CircleQueryError::TerminalValueMismatch {
            final_index: query >> 6,
        })
    );
    assert_eq!(
        check_fixed_circle_query(
            &fixture.c1_leaves[0],
            &fixture.c2_leaves[0],
            later_leaves(&fixture, 0),
            FIXED_QUERY_FIBER_COUNT,
            fixture.gamma,
            fixture.alphas,
            fixture.folds.final_coefficients,
        ),
        Err(CircleQueryError::QueryOutOfRange {
            query: FIXED_QUERY_FIBER_COUNT,
        })
    );
}

#[derive(Clone, Copy)]
struct WeakPolicy {
    slots: [u8; 3],
    line_fibers: [usize; 3],
    final_index: usize,
    reuse_circle_alpha: bool,
    reuse_line_alpha_at: Option<usize>,
    final_is_stwo_storage: bool,
}

impl WeakPolicy {
    fn canonical(path: FixedQueryPath) -> Self {
        Self {
            slots: path.later.map(|location| location.slot),
            line_fibers: path.later.map(|location| location.leaf),
            final_index: path.final_index,
            reuse_circle_alpha: false,
            reuse_line_alpha_at: None,
            final_is_stwo_storage: false,
        }
    }
}

fn normalized_inverse(left: QM31, right: QM31, x: M31, alpha: QM31) -> QM31 {
    left.add(right)
        .half()
        .add(alpha.mul(left.sub(right).mul_m31(x.double().inv())))
}

fn weakened_circle_reused_alpha(values: [QM31; 4], alpha: QM31, query: usize) -> QM31 {
    let point = fixed_circle_fiber_point(query).unwrap();
    let positive = normalized_inverse(values[0], values[1], point.y, alpha);
    let negative = normalized_inverse(values[2], values[3], point.y.neg(), alpha);
    normalized_inverse(positive, negative, point.x, alpha)
}

fn weakened_line_reused_alpha(values: [QM31; 4], alpha: QM31, layer: u8, fiber: usize) -> QM31 {
    let LineArity4Coordinates {
        first_pair_x,
        second_pair_x,
        second_fold_x,
    } = fixed_line_fold_coordinates(layer, fiber).unwrap();
    let first = normalized_inverse(values[0], values[1], first_pair_x, alpha);
    let second = normalized_inverse(values[2], values[3], second_pair_x, alpha);
    normalized_inverse(first, second, second_fold_x, alpha)
}

fn evaluate_stwo_storage4(coefficients: [QM31; 4], x: M31) -> QM31 {
    let pi_x = x.mul(x).double().sub(M31::ONE);
    coefficients[0]
        .add(coefficients[1].mul_m31(pi_x))
        .add(coefficients[2].mul_m31(x))
        .add(coefficients[3].mul_m31(x.mul(pi_x)))
}

fn weakened_chain_accepts(
    combined_layer0: [QM31; 4],
    later_leaves: [&[u8]; 3],
    query: usize,
    alphas: [QM31; 4],
    final_values: [QM31; 4],
    policy: WeakPolicy,
) -> bool {
    let later = later_leaves.map(decode_later);
    let layer1 = if policy.reuse_circle_alpha {
        weakened_circle_reused_alpha(combined_layer0, alphas[0], query)
    } else {
        normalized_circle_to_line_arity4_at_fiber(combined_layer0, alphas[0], query).unwrap()
    };
    if later[0][usize::from(policy.slots[0])] != layer1 {
        return false;
    }

    let mut current = layer1;
    for round in 0..3 {
        current = if policy.reuse_line_alpha_at == Some(round) {
            weakened_line_reused_alpha(
                later[round],
                alphas[round + 1],
                round as u8 + 1,
                policy.line_fibers[round],
            )
        } else {
            normalized_line_arity4_at_fiber(
                later[round],
                alphas[round + 1],
                round as u8 + 1,
                policy.line_fibers[round],
            )
            .unwrap()
        };
        if round < 2 && later[round + 1][usize::from(policy.slots[round + 1])] != current {
            return false;
        }
    }

    let x = fixed_line_domain_x(FIXED_FINAL_LINE_LAYER, policy.final_index).unwrap();
    let final_evaluation = if policy.final_is_stwo_storage {
        evaluate_stwo_storage4(final_values, x)
    } else {
        evaluate_final_line_tensor(final_values, x)
    };
    final_evaluation == current
}

fn shifted_c2_leaf(c2_leaf: &[u8], gamma: QM31) -> [u8; CIRCLE_QUERY_C2_LEAF_BYTES] {
    let mut shifted = [0u8; CIRCLE_QUERY_C2_LEAF_BYTES];
    for index in 0..8 {
        let offset = index * 16;
        gamma
            .mul(QM31::from_le_bytes(&c2_leaf[offset..offset + 16]).unwrap())
            .write_le_bytes(&mut shifted[offset..offset + 16]);
    }
    shifted
}

fn weakened_gamma50_51_accepts(
    c1_leaf: &[u8],
    c2_leaf: &[u8],
    later: [&[u8]; 3],
    query: usize,
    gamma: QM31,
    alphas: [QM31; 4],
    final_values: [QM31; 4],
) -> bool {
    // The external bytes are unchanged. Only this weakened decoder multiplies
    // each raw helper by gamma before the canonical 49/50 kernel, which is
    // exactly the erroneous 50/51 exponent rule.
    let shifted = shifted_c2_leaf(c2_leaf, gamma);
    let combined = gamma_combine_fixed_layer0(c1_leaf, &shifted, gamma).unwrap();
    weakened_chain_accepts(
        combined,
        later,
        query,
        alphas,
        final_values,
        WeakPolicy::canonical(map_fixed_query(query).unwrap()),
    )
}

fn canonical_rejects(
    fixture: &Fixture,
    query: usize,
    later: [&[u8]; 3],
    final_values: [QM31; 4],
) -> CircleQueryError {
    check_fixed_circle_query(
        &fixture.c1_leaves[query],
        &fixture.c2_leaves[query],
        later,
        query,
        fixture.gamma,
        fixture.alphas,
        final_values,
    )
    .unwrap_err()
}

#[test]
fn gamma_shift_query_mapping_alpha_reuse_and_final_order_have_teeth() {
    let fixture = fixture();

    // Gamma-power shift: the weakened rule scales both helper values by gamma
    // before applying canonical powers 49/50, i.e. it actually uses 50/51.
    let shifted_c2_codewords = fixture
        .c2_codewords
        .iter()
        .map(|codeword| {
            codeword
                .iter()
                .map(|value| fixture.gamma.mul(*value))
                .collect()
        })
        .collect::<Vec<Vec<QM31>>>();
    let shifted_c2_messages = fixture
        .c2_messages
        .iter()
        .map(|message| {
            message
                .iter()
                .map(|value| fixture.gamma.mul(*value))
                .collect()
        })
        .collect::<Vec<Vec<QM31>>>();
    let shifted_codeword =
        gamma_combine_codewords(&fixture.c1_codewords, &shifted_c2_codewords, fixture.gamma)
            .unwrap();
    let shifted_message =
        gamma_combine_messages(&fixture.c1_messages, &shifted_c2_messages, fixture.gamma).unwrap();
    let shifted_folds = build_fold_commitments(
        &shifted_codeword,
        &shifted_message,
        fixture.alphas,
        host_hash,
    )
    .unwrap();
    let query = 731usize;
    let shifted_later: [&[u8]; 3] = [
        &shifted_folds.committed_leaves[0][query >> 2],
        &shifted_folds.committed_leaves[1][query >> 4],
        &shifted_folds.committed_leaves[2][query >> 6],
    ];
    assert!(weakened_gamma50_51_accepts(
        &fixture.c1_leaves[query],
        &fixture.c2_leaves[query],
        shifted_later,
        query,
        fixture.gamma,
        fixture.alphas,
        shifted_folds.final_coefficients,
    ));
    assert!(matches!(
        canonical_rejects(
            &fixture,
            query,
            shifted_later,
            shifted_folds.final_coefficients
        ),
        CircleQueryError::LayerValueMismatch { layer: 1, .. }
    ));

    // Stale slot mapping: a weakened verifier incorrectly reuses q&3 at
    // every committed layer instead of consuming the q>>2 and q>>4 chunks.
    let query = 0b10_01_00usize;
    let path = map_fixed_query(query).unwrap();
    let combined = gamma_combine_fixed_layer0(
        &fixture.c1_leaves[query],
        &fixture.c2_leaves[query],
        fixture.gamma,
    )
    .unwrap();
    let stale_slot = path.later[0].slot;
    assert_ne!(stale_slot, path.later[1].slot);
    assert_ne!(stale_slot, path.later[2].slot);
    let mut layer1_values = sample_values(0x4d41_505f_4c31);
    layer1_values[usize::from(stale_slot)] =
        normalized_circle_to_line_arity4_at_fiber(combined, fixture.alphas[0], query).unwrap();
    let layer2_value =
        normalized_line_arity4_at_fiber(layer1_values, fixture.alphas[1], 1, path.later[0].leaf)
            .unwrap();
    let mut layer2_values = sample_values(0x4d41_505f_4c32);
    layer2_values[usize::from(stale_slot)] = layer2_value;
    layer2_values[usize::from(path.later[1].slot)] = layer2_value.add(QM31::ONE);
    let layer3_value =
        normalized_line_arity4_at_fiber(layer2_values, fixture.alphas[2], 2, path.later[1].leaf)
            .unwrap();
    let mut layer3_values = sample_values(0x4d41_505f_4c33);
    layer3_values[usize::from(stale_slot)] = layer3_value;
    let terminal =
        normalized_line_arity4_at_fiber(layer3_values, fixture.alphas[3], 3, path.later[2].leaf)
            .unwrap();
    let stale_leaves = [
        encode_later(layer1_values),
        encode_later(layer2_values),
        encode_later(layer3_values),
    ];
    let stale_refs = stale_leaves.each_ref().map(|leaf| &leaf[..]);
    let mut stale_policy = WeakPolicy::canonical(path);
    stale_policy.slots = [stale_slot; 3];
    assert!(weakened_chain_accepts(
        combined,
        stale_refs,
        query,
        fixture.alphas,
        [terminal, QM31::ZERO, QM31::ZERO, QM31::ZERO],
        stale_policy,
    ));
    assert_eq!(
        canonical_rejects(
            &fixture,
            query,
            stale_refs,
            [terminal, QM31::ZERO, QM31::ZERO, QM31::ZERO]
        ),
        CircleQueryError::LayerValueMismatch {
            layer: 2,
            offset: usize::from(path.later[1].slot) * 16,
        }
    );

    // Repair both interpretations at layer 2, then separate them at layer 3
    // so the next q>>4 slot chunk has its own accepting weakened vector.
    let mut layer2_values = sample_values(0x4d41_505f_5232);
    layer2_values[usize::from(stale_slot)] = layer2_value;
    layer2_values[usize::from(path.later[1].slot)] = layer2_value;
    let layer3_value =
        normalized_line_arity4_at_fiber(layer2_values, fixture.alphas[2], 2, path.later[1].leaf)
            .unwrap();
    let mut layer3_values = sample_values(0x4d41_505f_5233);
    layer3_values[usize::from(stale_slot)] = layer3_value;
    layer3_values[usize::from(path.later[2].slot)] = layer3_value.add(QM31::ONE);
    let terminal =
        normalized_line_arity4_at_fiber(layer3_values, fixture.alphas[3], 3, path.later[2].leaf)
            .unwrap();
    let stale_layer3_leaves = [
        encode_later(layer1_values),
        encode_later(layer2_values),
        encode_later(layer3_values),
    ];
    let stale_layer3_refs = stale_layer3_leaves.each_ref().map(|leaf| &leaf[..]);
    assert!(weakened_chain_accepts(
        combined,
        stale_layer3_refs,
        query,
        fixture.alphas,
        [terminal, QM31::ZERO, QM31::ZERO, QM31::ZERO],
        stale_policy,
    ));
    assert_eq!(
        canonical_rejects(
            &fixture,
            query,
            stale_layer3_refs,
            [terminal, QM31::ZERO, QM31::ZERO, QM31::ZERO]
        ),
        CircleQueryError::LayerValueMismatch {
            layer: 3,
            offset: usize::from(path.later[2].slot) * 16,
        }
    );

    // Wrong terminal propagation uses q>>4 instead of q>>6 while all three
    // committed-layer comparisons remain honest.
    let query = 64usize;
    let path = map_fixed_query(query).unwrap();
    let wrong_final_index = (query >> 4) & 15;
    assert_ne!(wrong_final_index, path.final_index);
    let terminal = fixture.folds.final_evaluations[path.final_index];
    let wrong_x = fixed_line_domain_x(FIXED_FINAL_LINE_LAYER, wrong_final_index).unwrap();
    let final_for_wrong_x = [
        terminal.sub(QM31::ONE.mul_m31(wrong_x)),
        QM31::ONE,
        QM31::ZERO,
        QM31::ZERO,
    ];
    let combined = gamma_combine_fixed_layer0(
        &fixture.c1_leaves[query],
        &fixture.c2_leaves[query],
        fixture.gamma,
    )
    .unwrap();
    let mut wrong_final_policy = WeakPolicy::canonical(path);
    wrong_final_policy.final_index = wrong_final_index;
    assert!(weakened_chain_accepts(
        combined,
        later_leaves(&fixture, query),
        query,
        fixture.alphas,
        final_for_wrong_x,
        wrong_final_policy,
    ));
    assert_eq!(
        canonical_rejects(
            &fixture,
            query,
            later_leaves(&fixture, query),
            final_for_wrong_x,
        ),
        CircleQueryError::TerminalValueMismatch {
            final_index: path.final_index,
        }
    );

    // Alpha reuse in the circle fold: the weakened second binary fold uses
    // alpha again instead of alpha^2.
    let query = 509usize;
    let path = map_fixed_query(query).unwrap();
    let combined = gamma_combine_fixed_layer0(
        &fixture.c1_leaves[query],
        &fixture.c2_leaves[query],
        fixture.gamma,
    )
    .unwrap();
    let weak_layer1 = weakened_circle_reused_alpha(combined, fixture.alphas[0], query);
    let canonical_layer1 =
        normalized_circle_to_line_arity4_at_fiber(combined, fixture.alphas[0], query).unwrap();
    assert_ne!(weak_layer1, canonical_layer1);
    let mut layer1_values = sample_values(0x414c_5048_415f_4331);
    layer1_values[usize::from(path.later[0].slot)] = weak_layer1;
    let layer2_value =
        normalized_line_arity4_at_fiber(layer1_values, fixture.alphas[1], 1, path.later[0].leaf)
            .unwrap();
    let mut layer2_values = sample_values(0x414c_5048_415f_4332);
    layer2_values[usize::from(path.later[1].slot)] = layer2_value;
    let layer3_value =
        normalized_line_arity4_at_fiber(layer2_values, fixture.alphas[2], 2, path.later[1].leaf)
            .unwrap();
    let mut layer3_values = sample_values(0x414c_5048_415f_4333);
    layer3_values[usize::from(path.later[2].slot)] = layer3_value;
    let terminal =
        normalized_line_arity4_at_fiber(layer3_values, fixture.alphas[3], 3, path.later[2].leaf)
            .unwrap();
    let alpha_circle_leaves = [
        encode_later(layer1_values),
        encode_later(layer2_values),
        encode_later(layer3_values),
    ];
    let alpha_circle_refs = alpha_circle_leaves.each_ref().map(|leaf| &leaf[..]);
    let mut alpha_circle_policy = WeakPolicy::canonical(path);
    alpha_circle_policy.reuse_circle_alpha = true;
    assert!(weakened_chain_accepts(
        combined,
        alpha_circle_refs,
        query,
        fixture.alphas,
        [terminal, QM31::ZERO, QM31::ZERO, QM31::ZERO],
        alpha_circle_policy,
    ));
    assert!(matches!(
        canonical_rejects(
            &fixture,
            query,
            alpha_circle_refs,
            [terminal, QM31::ZERO, QM31::ZERO, QM31::ZERO],
        ),
        CircleQueryError::LayerValueMismatch { layer: 1, .. }
    ));

    // Alpha reuse in a later line fold is independently toothed.
    let query = 887usize;
    let path = map_fixed_query(query).unwrap();
    let combined = gamma_combine_fixed_layer0(
        &fixture.c1_leaves[query],
        &fixture.c2_leaves[query],
        fixture.gamma,
    )
    .unwrap();
    let mut layer1_values = sample_values(0x414c_5048_415f_4c31);
    layer1_values[usize::from(path.later[0].slot)] =
        normalized_circle_to_line_arity4_at_fiber(combined, fixture.alphas[0], query).unwrap();
    let weak_layer2 =
        weakened_line_reused_alpha(layer1_values, fixture.alphas[1], 1, path.later[0].leaf);
    let canonical_layer2 =
        normalized_line_arity4_at_fiber(layer1_values, fixture.alphas[1], 1, path.later[0].leaf)
            .unwrap();
    assert_ne!(weak_layer2, canonical_layer2);
    let mut layer2_values = sample_values(0x414c_5048_415f_4c32);
    layer2_values[usize::from(path.later[1].slot)] = weak_layer2;
    let layer3_value =
        normalized_line_arity4_at_fiber(layer2_values, fixture.alphas[2], 2, path.later[1].leaf)
            .unwrap();
    let mut layer3_values = sample_values(0x414c_5048_415f_4c33);
    layer3_values[usize::from(path.later[2].slot)] = layer3_value;
    let terminal =
        normalized_line_arity4_at_fiber(layer3_values, fixture.alphas[3], 3, path.later[2].leaf)
            .unwrap();
    let alpha_line_leaves = [
        encode_later(layer1_values),
        encode_later(layer2_values),
        encode_later(layer3_values),
    ];
    let alpha_line_refs = alpha_line_leaves.each_ref().map(|leaf| &leaf[..]);
    let mut alpha_line_policy = WeakPolicy::canonical(path);
    alpha_line_policy.reuse_line_alpha_at = Some(0);
    assert!(weakened_chain_accepts(
        combined,
        alpha_line_refs,
        query,
        fixture.alphas,
        [terminal, QM31::ZERO, QM31::ZERO, QM31::ZERO],
        alpha_line_policy,
    ));
    assert!(matches!(
        canonical_rejects(
            &fixture,
            query,
            alpha_line_refs,
            [terminal, QM31::ZERO, QM31::ZERO, QM31::ZERO],
        ),
        CircleQueryError::LayerValueMismatch { layer: 2, .. }
    ));

    // Final bytes in Stwo storage order are accepted only by the weakened
    // storage-order interpretation; canonical input is natural order.
    let query = 913usize;
    let path = map_fixed_query(query).unwrap();
    let natural = fixture.folds.final_coefficients;
    let storage = [natural[0], natural[2], natural[1], natural[3]];
    let combined = gamma_combine_fixed_layer0(
        &fixture.c1_leaves[query],
        &fixture.c2_leaves[query],
        fixture.gamma,
    )
    .unwrap();
    let mut storage_policy = WeakPolicy::canonical(path);
    storage_policy.final_is_stwo_storage = true;
    assert!(weakened_chain_accepts(
        combined,
        later_leaves(&fixture, query),
        query,
        fixture.alphas,
        storage,
        storage_policy,
    ));
    assert_eq!(
        canonical_rejects(&fixture, query, later_leaves(&fixture, query), storage,),
        CircleQueryError::TerminalValueMismatch {
            final_index: path.final_index,
        }
    );

    assert_eq!(fixture.c1_codewords[0].len(), CODEWORD_LEN);
}
