use aspis_core::field::{CM31, M31, QM31};
use aspis_statement::atomic_state_only_registry::atomic_state_only_path_aux_layout_v3;
use aspis_statement::atomic_state_only_trace::{
    atomic_merkle_root_v3, atomic_state_only_block_schedule_v3, atomic_state_only_bound_roots_v3,
    atomic_state_only_node_input_v3, build_atomic_state_only_trace_v3,
    validate_atomic_state_only_trace_v3, AtomicStateOnlyBlockV3, AtomicStateOnlyTraceV3,
    AtomicStateOnlyTraceV3Error, ATOMIC_STATE_ONLY_INPUT_PATH_BLOCK_START,
    ATOMIC_STATE_ONLY_OUTPUT_PATH_BLOCK_START,
};
use aspis_statement::trace_v4::BLOCK_ROWS;
use aspis_statement::{
    build_spend_trace_v4, derive_nullifier, derive_owner_key, evaluate_state_only_poseidon_oracle,
    merkle_root, note_commitment, output_commitment, project_state_only_trace_v4,
    AtomicPaymentStatementV4, Digest, MerklePath, SpendPublic, SpendWitness,
    StateOnlyPoseidonOpenings, StateOnlyPoseidonSelectors, MERKLE_NODE_COMPRESSION_V3_TWEAK,
    STATE_ONLY_ABSORPTION_ROW_IN_BLOCK, STATE_ONLY_FINAL_ROW_IN_BLOCK, STATE_ONLY_POSEIDON_BLOCKS,
    STATE_ONLY_POSEIDON_TRACE_ROWS,
};

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + index as u32 * 17))
}

fn fixture() -> (AtomicPaymentStatementV4, SpendWitness) {
    let nullifier_key = digest(101);
    let input_salt = digest(301);
    let output_salt = digest(501);
    let output_owner_key = digest(701);
    let asset_id = M31(17);
    let value = 1_000_000;
    let value_out = 999_999;
    let fee = 1;
    let owner_key = derive_owner_key(&nullifier_key);
    let input_leaf = note_commitment(&owner_key, value, asset_id, &input_salt);
    let output_leaf = output_commitment(&output_owner_key, value_out, asset_id, &output_salt);
    let merkle_path = MerklePath {
        siblings: (0..20)
            .map(|level| digest(1_000 + level as u32 * 31))
            .collect(),
        index: 0x5a5a5,
    };
    let witness = SpendWitness {
        nullifier_key,
        input_salt,
        output_salt,
        output_owner_key,
        input_asset_id: asset_id,
        value,
        value_out,
        merkle_path,
    };
    let current_anchor = atomic_merkle_root_v3(input_leaf, &witness.merkle_path).unwrap();
    let output_anchor = atomic_merkle_root_v3(output_leaf, &witness.merkle_path).unwrap();
    let statement = AtomicPaymentStatementV4 {
        pool: [0x5a; 32],
        sequence: 73,
        spend: SpendPublic {
            anchor: current_anchor,
            nullifier: derive_nullifier(&nullifier_key, &input_salt),
            output_commitment: output_leaf,
            asset_id,
            fee,
        },
        output_anchor,
        deployment_domain: [0x5d; 32],
    };
    (statement, witness)
}

fn lift(value: M31) -> QM31 {
    QM31::from_cm31(CM31::from_m31(value))
}

fn boolean_point(row: usize) -> [QM31; 10] {
    core::array::from_fn(|coordinate| {
        if (row >> (9 - coordinate)) & 1 == 0 {
            QM31::ZERO
        } else {
            QM31::ONE
        }
    })
}

fn block_image(trace: &AtomicStateOnlyTraceV3, block: usize) -> [[M31; 16]; 16] {
    core::array::from_fn(|local| {
        core::array::from_fn(|lane| trace.trace.c1[lane][block * BLOCK_ROWS + local])
    })
}

fn mutate_sibling_in_one_path(trace: &mut AtomicStateOnlyTraceV3, level: usize, output_path: bool) {
    let descriptor = trace.path[level];
    let block = if output_path {
        usize::from(descriptor.output_block)
    } else {
        usize::from(descriptor.input_block)
    };
    let base = block * BLOCK_ROWS;
    if descriptor.bit == 0 {
        trace.trace.c1[8][base] = trace.trace.c1[8][base].add(M31::ONE);
    } else {
        trace.trace.c1[0][base + STATE_ONLY_ABSORPTION_ROW_IN_BLOCK] =
            trace.trace.c1[0][base + STATE_ONLY_ABSORPTION_ROW_IN_BLOCK].add(M31::ONE);
    }
}

fn swap_children_in_one_path(trace: &mut AtomicStateOnlyTraceV3, level: usize, output_path: bool) {
    let descriptor = trace.path[level];
    let block = if output_path {
        usize::from(descriptor.output_block)
    } else {
        usize::from(descriptor.input_block)
    };
    let base = block * BLOCK_ROWS;
    let left: Digest = core::array::from_fn(|lane| {
        trace.trace.c1[lane][base + STATE_ONLY_ABSORPTION_ROW_IN_BLOCK]
    });
    let mut right: Digest = core::array::from_fn(|lane| trace.trace.c1[8 + lane][base]);
    right[7] = right[7].sub(MERKLE_NODE_COMPRESSION_V3_TWEAK);
    for lane in 0..8 {
        trace.trace.c1[lane][base + STATE_ONLY_ABSORPTION_ROW_IN_BLOCK] = right[lane];
        trace.trace.c1[8 + lane][base] = left[lane];
    }
    trace.trace.c1[15][base] = trace.trace.c1[15][base].add(MERKLE_NODE_COMPRESSION_V3_TWEAK);
}

#[test]
fn frozen_block_schedule_is_exact() {
    let expected = (0..49)
        .map(|block| atomic_state_only_block_schedule_v3(block).unwrap())
        .collect::<Vec<_>>();
    assert_eq!(expected[0], AtomicStateOnlyBlockV3::OwnerKey);
    assert_eq!(expected[1], AtomicStateOnlyBlockV3::InputNote(0));
    assert_eq!(expected[3], AtomicStateOnlyBlockV3::InputNote(2));
    for level in 0..20 {
        assert_eq!(
            expected[4 + level],
            AtomicStateOnlyBlockV3::InputPath(level as u8)
        );
        assert_eq!(
            expected[24 + level],
            AtomicStateOnlyBlockV3::OutputPath(level as u8)
        );
    }
    assert_eq!(expected[44], AtomicStateOnlyBlockV3::Nullifier(0));
    assert_eq!(expected[45], AtomicStateOnlyBlockV3::Nullifier(1));
    assert_eq!(expected[46], AtomicStateOnlyBlockV3::OutputNote(0));
    assert_eq!(expected[48], AtomicStateOnlyBlockV3::OutputNote(2));
    assert_eq!(atomic_state_only_block_schedule_v3(49), None);
}

#[test]
fn builder_preserves_non_path_blocks_and_replaces_exactly_blocks_4_through_43() {
    let (statement, witness) = fixture();
    let atomic = build_atomic_state_only_trace_v3(&statement, &witness).unwrap();
    let input_leaf = atomic.input_leaf;
    let surrogate_public = SpendPublic {
        anchor: merkle_root(input_leaf, &witness.merkle_path).unwrap(),
        nullifier: statement.spend.nullifier,
        output_commitment: statement.spend.output_commitment,
        asset_id: statement.spend.asset_id,
        fee: statement.spend.fee,
    };
    let source = build_spend_trace_v4(&surrogate_public, &witness).unwrap();
    let surrogate = project_state_only_trace_v4(&source).unwrap();
    for block in (0..=3).chain(44..=48) {
        for local in 0..BLOCK_ROWS {
            let row = block * BLOCK_ROWS + local;
            for lane in 0..16 {
                assert_eq!(atomic.trace.c1[lane][row], surrogate.c1[lane][row]);
            }
        }
    }
    assert!((4..=43).any(|block| {
        (0..BLOCK_ROWS).any(|local| {
            let row = block * BLOCK_ROWS + local;
            (0..16).any(|lane| atomic.trace.c1[lane][row] != surrogate.c1[lane][row])
        })
    }));
}

#[test]
fn one_path_sources_are_aliased_and_both_roots_match_public_bindings() {
    let (statement, witness) = fixture();
    let atomic = build_atomic_state_only_trace_v3(&statement, &witness).unwrap();
    let aux = atomic_state_only_path_aux_layout_v3().unwrap();
    for level in 0..20 {
        let descriptor = atomic.path[level];
        assert_eq!(descriptor.level, level as u8);
        assert_eq!(descriptor.sibling_source, aux[level].sibling);
        assert_eq!(descriptor.bit_source, aux[level].input_bit);
        assert_eq!(descriptor.input_block as usize, 4 + level);
        assert_eq!(descriptor.output_block as usize, 24 + level);
        assert_eq!(descriptor.sibling, witness.merkle_path.siblings[level]);
        assert_eq!(
            descriptor.bit,
            ((witness.merkle_path.index >> level) & 1) as u8
        );
    }
    let roots = atomic_state_only_bound_roots_v3(&atomic);
    assert_eq!(roots, (statement.spend.anchor, statement.output_anchor));
    assert_eq!(
        roots.0,
        atomic_merkle_root_v3(atomic.input_leaf, &witness.merkle_path).unwrap()
    );
    assert_eq!(
        roots.1,
        atomic_merkle_root_v3(atomic.output_leaf, &witness.merkle_path).unwrap()
    );
}

#[test]
fn every_v3_block_has_the_pinned_row0_row12_and_final_layout() {
    let (statement, witness) = fixture();
    let atomic = build_atomic_state_only_trace_v3(&statement, &witness).unwrap();
    for descriptor in atomic.path {
        for (block, left, right, parent) in [
            (
                usize::from(descriptor.input_block),
                descriptor.input_left,
                descriptor.input_right,
                descriptor.input_parent,
            ),
            (
                usize::from(descriptor.output_block),
                descriptor.output_left,
                descriptor.output_right,
                descriptor.output_parent,
            ),
        ] {
            let state = atomic_state_only_node_input_v3(&atomic, block).unwrap();
            assert_eq!(&state[..8], &left);
            assert_eq!(&state[8..15], &right[..7]);
            assert_eq!(state[15], right[7].add(MERKLE_NODE_COMPRESSION_V3_TWEAK));
            let base = block * BLOCK_ROWS;
            assert!((0..8).all(|lane| atomic.trace.c1[lane][base] == M31::ZERO));
            assert!((8..16).all(|lane| {
                let expected = if lane == 15 {
                    right[7].add(MERKLE_NODE_COMPRESSION_V3_TWEAK)
                } else {
                    right[lane - 8]
                };
                atomic.trace.c1[lane][base] == expected
            }));
            assert!((0..8).all(|lane| {
                atomic.trace.c1[lane][base + STATE_ONLY_ABSORPTION_ROW_IN_BLOCK] == left[lane]
            }));
            assert!((8..16).all(|lane| {
                atomic.trace.c1[lane][base + STATE_ONLY_ABSORPTION_ROW_IN_BLOCK] == M31::ZERO
            }));
            let final_digest: Digest = core::array::from_fn(|lane| {
                atomic.trace.c1[lane][base + STATE_ONLY_FINAL_ROW_IN_BLOCK]
            });
            assert_eq!(final_digest, parent);
        }
    }
}

#[test]
fn poseidon_oracle_replays_all_1024_boolean_rows() {
    let (statement, witness) = fixture();
    let atomic = build_atomic_state_only_trace_v3(&statement, &witness).unwrap();
    let mut active = 0usize;
    for row in 0..STATE_ONLY_POSEIDON_TRACE_ROWS {
        let point = boolean_point(row);
        let openings = StateOnlyPoseidonOpenings {
            z: core::array::from_fn(|lane| lift(atomic.trace.c1[lane][row])),
            succ_z: core::array::from_fn(|lane| {
                lift(atomic.trace.c1[lane][(row + 1) & (STATE_ONLY_POSEIDON_TRACE_ROWS - 1)])
            }),
            xor12_z: core::array::from_fn(|lane| lift(atomic.trace.c1[lane][row ^ 12])),
        };
        let residuals = evaluate_state_only_poseidon_oracle(
            &openings,
            &StateOnlyPoseidonSelectors::at_point(&point),
        );
        assert!(
            residuals.iter().all(|value| value.is_zero()),
            "row={row} residuals={residuals:?}"
        );
        if row / 16 < STATE_ONLY_POSEIDON_BLOCKS && row % 16 < 11 {
            active += 1;
        }
    }
    assert_eq!(active, 49 * 11);
}

#[test]
fn every_level_one_path_sibling_and_direction_mutation_rejects() {
    let (statement, witness) = fixture();
    let honest = build_atomic_state_only_trace_v3(&statement, &witness).unwrap();
    for level in 0..20 {
        for output_path in [false, true] {
            let untouched_block = if output_path {
                ATOMIC_STATE_ONLY_INPUT_PATH_BLOCK_START + level
            } else {
                ATOMIC_STATE_ONLY_OUTPUT_PATH_BLOCK_START + level
            };
            let untouched = block_image(&honest, untouched_block);

            let mut sibling = honest.clone();
            mutate_sibling_in_one_path(&mut sibling, level, output_path);
            assert!(matches!(
                validate_atomic_state_only_trace_v3(&statement, &witness, &sibling),
                Err(AtomicStateOnlyTraceV3Error::TraceMismatch { .. })
            ));
            assert_eq!(block_image(&sibling, untouched_block), untouched);

            let mut bit = honest.clone();
            swap_children_in_one_path(&mut bit, level, output_path);
            assert!(matches!(
                validate_atomic_state_only_trace_v3(&statement, &witness, &bit),
                Err(AtomicStateOnlyTraceV3Error::TraceMismatch { .. })
            ));
            assert_eq!(block_image(&bit, untouched_block), untouched);
        }
    }
}

#[test]
fn swapped_child_tweak_root_and_leaf_teeth_reject() {
    let (statement, witness) = fixture();
    let honest = build_atomic_state_only_trace_v3(&statement, &witness).unwrap();

    let mut swapped = honest.clone();
    swap_children_in_one_path(&mut swapped, 7, false);
    assert!(validate_atomic_state_only_trace_v3(&statement, &witness, &swapped).is_err());

    let mut tweak = honest.clone();
    let base = usize::from(tweak.path[9].input_block) * BLOCK_ROWS;
    tweak.trace.c1[15][base] = tweak.trace.c1[15][base].sub(M31::ONE);
    assert!(validate_atomic_state_only_trace_v3(&statement, &witness, &tweak).is_err());

    let mut current_root = statement.clone();
    current_root.spend.anchor[0] = current_root.spend.anchor[0].add(M31::ONE);
    assert_eq!(
        build_atomic_state_only_trace_v3(&current_root, &witness),
        Err(AtomicStateOnlyTraceV3Error::CurrentAnchorMismatch)
    );
    let mut output_root = statement.clone();
    output_root.output_anchor[0] = output_root.output_anchor[0].add(M31::ONE);
    assert_eq!(
        build_atomic_state_only_trace_v3(&output_root, &witness),
        Err(AtomicStateOnlyTraceV3Error::OutputAnchorMismatch)
    );

    let mut input_leaf = witness.clone();
    input_leaf.input_salt[0] = input_leaf.input_salt[0].add(M31::ONE);
    assert!(build_atomic_state_only_trace_v3(&statement, &input_leaf).is_err());
    let mut output_leaf = witness.clone();
    output_leaf.output_salt[0] = output_leaf.output_salt[0].add(M31::ONE);
    assert_eq!(
        build_atomic_state_only_trace_v3(&statement, &output_leaf),
        Err(AtomicStateOnlyTraceV3Error::SpendBinding)
    );
}
