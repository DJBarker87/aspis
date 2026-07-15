use aspis_core::field::{CM31, M31, QM31};
use aspis_statement::atomic_state_only_registry::{
    atomic_state_only_path_aux_layout_v3, atomic_state_only_registry_fingerprint_v3,
    atomic_state_only_registry_stats_v3, atomic_state_only_relation_free_mask_cells_v3,
    atomic_state_only_relation_free_mask_fingerprint_v3,
    atomic_state_only_required_point_transforms_v3, build_atomic_state_only_copy_helper_v3,
    build_atomic_state_only_registry_v3, verify_atomic_state_only_copy_registry_v3,
    verify_atomic_state_only_public_roots_v3, AtomicCopyLinkKindV3, AtomicPointTransformV3,
    AtomicStateOnlyRegistryErrorV3, AtomicTupleLimbV3, ATOMIC_STATE_ONLY_SELECTED_PCS_WIDTH,
    ATOMIC_STATE_ONLY_TERMINAL_POINTS, ATOMIC_STATE_ONLY_THETA_COLLISION_DEGREE,
    ATOMIC_STATE_ONLY_THETA_LANES, ATOMIC_STATE_ONLY_ZEROCHECK_DEGREE,
    PINNED_ATOMIC_STATE_ONLY_REGISTRY_FINGERPRINT_V3,
};
use aspis_statement::atomic_state_only_trace::{
    atomic_merkle_root_v3, build_atomic_state_only_trace_v3, AtomicStateOnlyTraceV3,
};
use aspis_statement::{
    atomic_state_only_terminal::atomic_state_only_selected_constraint_composition_compiled_v3,
    derive_nullifier, derive_owner_key, note_commitment, output_commitment,
    AtomicPaymentStatementV4, Digest, MerklePath, SpendPublic, SpendWitness,
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
    let statement = AtomicPaymentStatementV4 {
        pool: [0x5a; 32],
        sequence: 73,
        spend: SpendPublic {
            anchor: atomic_merkle_root_v3(input_leaf, &witness.merkle_path).unwrap(),
            nullifier: derive_nullifier(&nullifier_key, &input_salt),
            output_commitment: output_leaf,
            asset_id,
            fee: 1,
        },
        output_anchor: atomic_merkle_root_v3(output_leaf, &witness.merkle_path).unwrap(),
        deployment_domain: [0x5d; 32],
    };
    (statement, witness)
}

fn challenges() -> (QM31, QM31) {
    (
        QM31 {
            c0: CM31::new(M31(17), M31(29)),
            c1: CM31::new(M31(43), M31(71)),
        },
        QM31 {
            c0: CM31::new(M31(101), M31(307)),
            c1: CM31::new(M31(401), M31(809)),
        },
    )
}

fn boolean_point(row: usize) -> [QM31; 10] {
    core::array::from_fn(|coordinate| {
        if row & (1 << (9 - coordinate)) == 0 {
            QM31::ZERO
        } else {
            QM31::ONE
        }
    })
}

fn boolean_row(point: &[QM31; 10]) -> usize {
    point.iter().fold(0usize, |row, value| {
        assert!(*value == QM31::ZERO || *value == QM31::ONE);
        (row << 1) | usize::from(*value == QM31::ONE)
    })
}

fn write(trace: &mut AtomicStateOnlyTraceV3, cell: aspis_statement::TraceCell, value: M31) {
    trace.trace.c1[usize::from(cell.column)][usize::from(cell.row)] = value;
}

fn assert_copy_rejects(trace: &AtomicStateOnlyTraceV3) {
    let registry = build_atomic_state_only_registry_v3().unwrap();
    let (lambda, chi) = challenges();
    assert_eq!(
        verify_atomic_state_only_copy_registry_v3(&registry, trace, lambda, chi),
        Err(AtomicStateOnlyRegistryErrorV3::CopyImbalance)
    );
}

#[test]
fn exact_registry_stats_and_fingerprint_are_reported() {
    if let Err(error) = atomic_state_only_path_aux_layout_v3() {
        panic!("atomic path aux layout failed first: {error:?}");
    }
    let registry = build_atomic_state_only_registry_v3().unwrap();
    let stats = atomic_state_only_registry_stats_v3(&registry).unwrap();
    let fingerprint = atomic_state_only_registry_fingerprint_v3(&registry).unwrap();
    eprintln!("atomic-v3 registry stats: {stats:?}");
    eprintln!("atomic-v3 registry fingerprint: {fingerprint:#018x}");
    assert_eq!(registry.path_current_links, 40);
    assert_eq!(registry.path_selection_links, 80);
    assert_eq!(registry.path_bit_alias_links, 40);
    assert_eq!(registry.retained_links, 23);
    assert_eq!(stats.copy_terms_m, registry.retained_links + 160);
    assert_eq!(stats.copy_terms_m, 183);
    assert_eq!(stats.unique_tag_groups, 143);
    assert_eq!(stats.endpoint_active_rows, 210);
    assert_eq!(stats.maximum_producers_per_row, 2);
    assert_eq!(stats.maximum_consumers_per_row, 2);
    assert!(stats.auxiliary_cells_used <= stats.auxiliary_cells_capacity);
    assert_eq!(stats.auxiliary_cells_used, 629);
    assert_eq!(stats.auxiliary_cells_capacity, 1_280);
    assert_eq!(stats.auxiliary_rows_high_water, 68);
    assert_eq!(stats.tuple_patterns, 15);
    assert_eq!(stats.tensor_routing_rank, 74);
    assert_eq!(stats.theta_lanes, ATOMIC_STATE_ONLY_THETA_LANES);
    assert_eq!(
        stats.theta_collision_degree,
        ATOMIC_STATE_ONLY_THETA_COLLISION_DEGREE
    );
    assert_eq!(stats.zerocheck_degree, ATOMIC_STATE_ONLY_ZEROCHECK_DEGREE);
    assert_eq!(stats.terminal_points, ATOMIC_STATE_ONLY_TERMINAL_POINTS);
    assert_eq!(
        stats.selected_pcs_width,
        ATOMIC_STATE_ONLY_SELECTED_PCS_WIDTH
    );
    assert_eq!(stats.selected_pcs_width, 28);
    assert_eq!(
        fingerprint,
        PINNED_ATOMIC_STATE_ONLY_REGISTRY_FINGERPRINT_V3
    );
    let mask_cells = atomic_state_only_relation_free_mask_cells_v3().unwrap();
    assert_eq!(mask_cells.len(), 5_262);
    assert_eq!(
        atomic_state_only_relation_free_mask_fingerprint_v3().unwrap(),
        aspis_core::state_only_hiding::PINNED_ATOMIC_STATE_ONLY_RELATION_FREE_MASK_FINGERPRINT_V3,
    );
    assert_eq!(
        aspis_core::state_only_hiding::PINNED_ATOMIC_STATE_ONLY_COPY_ACTIVE_ROWS_FINGERPRINT_V3,
        aspis_statement::atomic_state_only_terminal::PINNED_ATOMIC_STATE_ONLY_COPY_ACTIVE_ROWS_FINGERPRINT_V3,
    );
}

#[test]
fn every_path_selection_uses_the_one_shared_level_bit() {
    let registry = build_atomic_state_only_registry_v3().unwrap();
    for link in &registry.links {
        let AtomicCopyLinkKindV3::PathSelect {
            output,
            level,
            item,
        } = link.kind
        else {
            continue;
        };
        let aux = registry.path_aux[usize::from(level)];
        let expected = match (output, item) {
            (false, 0) => aux.input_bit,
            (true, 0) => aux.output_bit,
            (_, 1) => aux.sibling_bit,
            _ => unreachable!(),
        };
        let actual = match link.producer.limbs[0] {
            AtomicTupleLimbV3::AffineCell { cell, .. } => cell,
            other => panic!("path selection lacks its level bit: {other:?}"),
        };
        assert_eq!(actual, expected);
    }
}

#[test]
fn all_copy_endpoints_are_z_local_and_the_statement_uses_exactly_three_points() {
    let registry = build_atomic_state_only_registry_v3().unwrap();
    for link in &registry.links {
        for tuple in [link.producer, link.consumer] {
            for limb in tuple.limbs {
                if let AtomicTupleLimbV3::AffineCell { cell, .. } = limb {
                    assert_eq!(cell.row, tuple.row, "link {} is not z-local", link.id);
                }
            }
        }
    }
    assert_eq!(
        atomic_state_only_required_point_transforms_v3(),
        [
            AtomicPointTransformV3::Z,
            AtomicPointTransformV3::Succ,
            AtomicPointTransformV3::Xor12,
        ]
    );
}

#[test]
fn endpoint_values_and_same_path_sources_match_the_trace_foundation() {
    let (statement, witness) = fixture();
    let trace = build_atomic_state_only_trace_v3(&statement, &witness).unwrap();
    let registry = build_atomic_state_only_registry_v3().unwrap();
    let aux = atomic_state_only_path_aux_layout_v3().unwrap();
    for level in 0..20 {
        let descriptor = trace.path[level];
        let layout = aux[level];
        let read = |cell: aspis_statement::TraceCell| {
            trace.trace.c1[usize::from(cell.column)][usize::from(cell.row)]
        };
        assert_eq!(read(layout.input_bit), M31(u32::from(descriptor.bit)));
        assert_eq!(read(layout.output_bit), M31(u32::from(descriptor.bit)));
        assert_eq!(read(layout.sibling_bit), M31(u32::from(descriptor.bit)));
        for limb in 0..8 {
            assert_eq!(
                read(layout.input_current[limb]),
                descriptor.input_current[limb]
            );
            assert_eq!(
                read(layout.output_current[limb]),
                descriptor.output_current[limb]
            );
            assert_eq!(read(layout.sibling[limb]), descriptor.sibling[limb]);
        }
    }
    let (lambda, chi) = challenges();
    verify_atomic_state_only_copy_registry_v3(&registry, &trace, lambda, chi).unwrap();
    verify_atomic_state_only_public_roots_v3(&statement, &trace).unwrap();
}

#[test]
fn every_level_current_sibling_and_bit_alias_corruption_rejects() {
    let (statement, witness) = fixture();
    let honest = build_atomic_state_only_trace_v3(&statement, &witness).unwrap();
    let aux = atomic_state_only_path_aux_layout_v3().unwrap();
    for level in 0..20 {
        for target in [
            aux[level].input_current[0],
            aux[level].output_current[0],
            aux[level].input_bit,
            aux[level].output_bit,
            aux[level].sibling_bit,
            aux[level].sibling[0],
        ] {
            let mut changed = honest.clone();
            let value = changed.trace.c1[usize::from(target.column)][usize::from(target.row)];
            write(&mut changed, target, value.add(M31::ONE));
            assert_copy_rejects(&changed);
        }
    }
}

#[test]
fn every_level_path_input_corruption_rejects_independently() {
    let (statement, witness) = fixture();
    let honest = build_atomic_state_only_trace_v3(&statement, &witness).unwrap();
    for level in 0..20 {
        for block in [4 + level, 24 + level] {
            for (row, column) in [(block * 16 + 12, 0usize), (block * 16, 8usize)] {
                let mut changed = honest.clone();
                changed.trace.c1[column][row] = changed.trace.c1[column][row].add(M31::ONE);
                assert_copy_rejects(&changed);
            }
        }
    }
}

#[test]
fn each_public_root_binding_has_an_independent_tooth() {
    let (statement, witness) = fixture();
    let trace = build_atomic_state_only_trace_v3(&statement, &witness).unwrap();
    let mut current = statement.clone();
    current.spend.anchor[0] = current.spend.anchor[0].add(M31::ONE);
    assert_eq!(
        verify_atomic_state_only_public_roots_v3(&current, &trace),
        Err(AtomicStateOnlyRegistryErrorV3::PublicRootMismatch)
    );
    let mut output = statement.clone();
    output.output_anchor[0] = output.output_anchor[0].add(M31::ONE);
    assert_eq!(
        verify_atomic_state_only_public_roots_v3(&output, &trace),
        Err(AtomicStateOnlyRegistryErrorV3::PublicRootMismatch)
    );
}

#[test]
fn honest_atomic_constraint_composition_vanishes_on_every_boolean_row() {
    let (statement, witness) = fixture();
    let atomic = build_atomic_state_only_trace_v3(&statement, &witness).unwrap();
    let (lambda, chi) = challenges();
    let theta = QM31 {
        c0: CM31::new(M31(911), M31(1_003)),
        c1: CM31::new(M31(1_109), M31(1_213)),
    };
    let h1 = build_atomic_state_only_copy_helper_v3(&atomic.trace, lambda, chi).unwrap();
    for row in 0..1024 {
        let point = boolean_point(row);
        let points = [
            point,
            aspis_statement::state_only_poseidon::successor_point(&point),
            aspis_statement::state_only_poseidon::xor12_point(&point),
        ];
        let mut claims = [QM31::ZERO; 84];
        for (point_index, selected) in points.iter().enumerate() {
            let selected_row = boolean_row(selected);
            let base = 28 * point_index;
            for column in 0..16 {
                claims[base + column] =
                    QM31::from_cm31(CM31::from_m31(atomic.trace.c1[column][selected_row]));
            }
            claims[base + 26] = h1[selected_row];
        }
        assert_eq!(
            atomic_state_only_selected_constraint_composition_compiled_v3(
                &statement, &claims, &point, lambda, chi, theta,
            )
            .unwrap(),
            QM31::ZERO,
            "nonzero atomic composition at Boolean row {row}",
        );
    }
}
