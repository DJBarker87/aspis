//! Regenerate atomic-v3 terminal routing constants from the host registry.

use std::collections::BTreeSet;

use aspis_core::field::{M31, P};
use aspis_statement::atomic_state_only_registry::{
    atomic_state_only_registry_fingerprint_v3, build_atomic_state_only_registry_v3,
    AtomicCopyTupleV3, AtomicTupleLimbV3, PINNED_ATOMIC_STATE_ONLY_REGISTRY_FINGERPRINT_V3,
};

// Exhaustive search over all row-bit bipartitions selected this exact split:
// the four most-significant row bits form the 16-entry factor and the six
// least-significant bits form the 64-entry factor.  It preserves the exact
// routing matrices while reducing shared products 84 -> 61.
const DEFAULT_ROUTING_LOW_ROW_BITS: u16 = 0x03c0;

fn projected_index(row: usize, bit_mask: u16) -> usize {
    let mut output = 0usize;
    for bit in (0..10).rev() {
        if bit_mask & (1 << bit) != 0 {
            output = (output << 1) | ((row >> bit) & 1);
        }
    }
    output
}

#[derive(Clone, PartialEq, Eq)]
struct Pattern {
    kinds: [u8; 16],
    columns: [u8; 16],
    scales: [u32; 16],
    offsets: [u32; 16],
}

fn pattern(tuple: AtomicCopyTupleV3) -> Pattern {
    let mut output = Pattern {
        kinds: [0; 16],
        columns: [0; 16],
        scales: [0; 16],
        offsets: [0; 16],
    };
    for (index, limb) in tuple.limbs.into_iter().enumerate() {
        match limb {
            AtomicTupleLimbV3::Zero => {}
            AtomicTupleLimbV3::Constant(value) => {
                output.kinds[index] = 1;
                output.offsets[index] = value.0;
            }
            AtomicTupleLimbV3::AffineCell {
                cell,
                scale,
                offset,
            } => {
                assert_eq!(cell.row, tuple.row);
                output.kinds[index] = 2;
                output.columns[index] = cell.column;
                output.scales[index] = scale.0;
                output.offsets[index] = offset.0;
            }
        }
    }
    output
}

fn emit_u8_array(values: &[u8; 16]) -> String {
    format!("{:?}", values)
}

fn emit_u32_array(values: &[u32; 16]) -> String {
    format!("{:?}", values)
}

fn pivot_factors(
    matrix: &[Vec<M31>],
    pivot_row: usize,
    pivot_column: usize,
) -> (Vec<M31>, Vec<M31>) {
    let inverse = matrix[pivot_row][pivot_column].inv();
    let left = (0..64)
        .map(|row| matrix[row][pivot_column])
        .collect::<Vec<_>>();
    let right = (0..16)
        .map(|column| matrix[pivot_row][column].mul(inverse))
        .collect::<Vec<_>>();
    (left, right)
}

fn factor_cost(factor: &[M31]) -> (usize, usize) {
    factor
        .iter()
        .fold((0usize, 0usize), |(entries, products), value| {
            if *value == M31::ZERO {
                (entries, products)
            } else if *value == M31::ONE || value.0 == P - 1 {
                (entries + 1, products)
            } else {
                (entries + 1, products + 1)
            }
        })
}

fn product_reduction_groups(factor: &[M31], packed: bool) -> usize {
    const CAPACITY: u64 = u64::MAX / (P as u64 - 1);
    let coefficients = factor
        .iter()
        .filter_map(|coefficient| {
            (coefficient.0 != 0 && coefficient.0 != 1 && coefficient.0 != P - 1)
                .then_some(u64::from(coefficient.0))
        })
        .collect::<Vec<_>>();
    if !packed {
        let mut groups = 0usize;
        let mut sum = 0u64;
        for coefficient in coefficients {
            if sum > CAPACITY - coefficient {
                groups += 1;
                sum = 0;
            }
            sum += coefficient;
        }
        return groups + usize::from(sum != 0);
    }

    let mut sorted = coefficients;
    sorted.sort_unstable_by(|left, right| right.cmp(left));
    let mut bins = Vec::<u64>::new();
    for coefficient in sorted {
        if let Some(bin) = bins.iter_mut().find(|sum| **sum <= CAPACITY - coefficient) {
            *bin += coefficient;
        } else {
            bins.push(coefficient);
        }
    }
    bins.len()
}

fn append_sparse_factors(entries: &mut Vec<(u8, u32)>, factors: &[Vec<M31>]) -> Vec<(u16, u8)> {
    factors
        .iter()
        .map(|factor| {
            let start = entries.len();
            for (index, coefficient) in factor.iter().enumerate() {
                if *coefficient != M31::ZERO {
                    entries.push((index as u8, coefficient.0));
                }
            }
            (start as u16, (entries.len() - start) as u8)
        })
        .collect()
}

fn vector_space_rank(mut rows: Vec<Vec<M31>>) -> usize {
    if rows.is_empty() {
        return 0;
    }
    let columns = rows[0].len();
    let mut rank = 0usize;
    for column in 0..columns {
        let Some(pivot) = (rank..rows.len()).find(|&row| rows[row][column] != M31::ZERO) else {
            continue;
        };
        rows.swap(rank, pivot);
        let inverse = rows[rank][column].inv();
        for value in &mut rows[rank][column..] {
            *value = value.mul(inverse);
        }
        let pivot_row = rows[rank].clone();
        for row in 0..rows.len() {
            if row == rank || rows[row][column] == M31::ZERO {
                continue;
            }
            let scale = rows[row][column];
            for entry in column..columns {
                rows[row][entry] = rows[row][entry].sub(scale.mul(pivot_row[entry]));
            }
        }
        rank += 1;
        if rank == rows.len() {
            break;
        }
    }
    rank
}

struct LinearFactorization {
    basis: Vec<Vec<M31>>,
    expressions: Vec<Vec<M31>>,
    direct_basis: Vec<u8>,
}

impl LinearFactorization {
    fn cost(&self) -> (usize, usize, usize) {
        let mut entries = 0usize;
        let mut products = 0usize;
        for factor in self.basis.iter().chain(self.expressions.iter()) {
            let cost = factor_cost(factor);
            entries += cost.0;
            products += cost.1;
        }
        (self.basis.len(), entries, products)
    }
}

fn factorization_from_basis(factors: &[Vec<M31>], basis_indices: &[usize]) -> LinearFactorization {
    let rank = basis_indices.len();
    let basis_rows = basis_indices
        .iter()
        .map(|&index| factors[index].clone())
        .collect::<Vec<_>>();
    assert_eq!(vector_space_rank(basis_rows.clone()), rank);

    let mut reduced = basis_rows.clone();
    let mut transform = vec![vec![M31::ZERO; rank]; rank];
    for (index, row) in transform.iter_mut().enumerate() {
        row[index] = M31::ONE;
    }
    let mut pivots = Vec::with_capacity(rank);
    let mut pivot_row = 0usize;
    for column in 0..factors[0].len() {
        let Some(row) = (pivot_row..rank).find(|&row| reduced[row][column] != M31::ZERO) else {
            continue;
        };
        reduced.swap(pivot_row, row);
        transform.swap(pivot_row, row);
        let inverse = reduced[pivot_row][column].inv();
        for value in &mut reduced[pivot_row] {
            *value = value.mul(inverse);
        }
        for value in &mut transform[pivot_row] {
            *value = value.mul(inverse);
        }
        let reduced_pivot = reduced[pivot_row].clone();
        let transform_pivot = transform[pivot_row].clone();
        for row in 0..rank {
            if row == pivot_row || reduced[row][column] == M31::ZERO {
                continue;
            }
            let scale = reduced[row][column];
            for entry in 0..reduced[row].len() {
                reduced[row][entry] = reduced[row][entry].sub(scale.mul(reduced_pivot[entry]));
            }
            for entry in 0..rank {
                transform[row][entry] =
                    transform[row][entry].sub(scale.mul(transform_pivot[entry]));
            }
        }
        pivots.push(column);
        pivot_row += 1;
        if pivot_row == rank {
            break;
        }
    }
    assert_eq!(pivots.len(), rank);

    let mut expressions = vec![Vec::new(); factors.len()];
    let mut direct_basis = vec![u8::MAX; factors.len()];
    for (index, factor) in factors.iter().enumerate() {
        if let Some(basis) = basis_indices
            .iter()
            .position(|&candidate| candidate == index)
        {
            direct_basis[index] = basis as u8;
            continue;
        }
        let mut target = factor.clone();
        let mut expression = vec![M31::ZERO; rank];
        for row in 0..rank {
            let scale = target[pivots[row]];
            if scale == M31::ZERO {
                continue;
            }
            for entry in 0..target.len() {
                target[entry] = target[entry].sub(scale.mul(reduced[row][entry]));
            }
            for entry in 0..rank {
                expression[entry] = expression[entry].add(scale.mul(transform[row][entry]));
            }
        }
        assert!(target.iter().all(|value| *value == M31::ZERO));
        expressions[index] = expression;
    }
    LinearFactorization {
        basis: basis_rows,
        expressions,
        direct_basis,
    }
}

fn factorize_linear_forms(factors: &[Vec<M31>], product_weight: usize) -> LinearFactorization {
    if factors.is_empty() {
        return LinearFactorization {
            basis: Vec::new(),
            expressions: Vec::new(),
            direct_basis: Vec::new(),
        };
    }
    let rank = vector_space_rank(factors.to_vec());
    let mut order = (0..factors.len()).collect::<Vec<_>>();
    order.sort_by_key(|&index| {
        let (entries, products) = factor_cost(&factors[index]);
        (
            entries + product_weight * products,
            products,
            entries,
            index,
        )
    });
    let mut basis_indices = Vec::with_capacity(rank);
    let mut basis_rows = Vec::<Vec<M31>>::with_capacity(rank);
    let mut current_rank = 0usize;
    for index in order {
        let mut candidate = basis_rows.clone();
        candidate.push(factors[index].clone());
        let candidate_rank = vector_space_rank(candidate);
        if candidate_rank > current_rank {
            basis_indices.push(index);
            basis_rows.push(factors[index].clone());
            current_rank = candidate_rank;
            if current_rank == rank {
                break;
            }
        }
    }
    assert_eq!(basis_indices.len(), rank);

    let score = |factorization: &LinearFactorization| {
        let (_, entries, products) = factorization.cost();
        (entries + product_weight * products, products, entries)
    };
    let mut best = factorization_from_basis(factors, &basis_indices);
    loop {
        let mut best_swap = None;
        let mut best_score = score(&best);
        for position in 0..rank {
            for candidate in 0..factors.len() {
                if basis_indices.contains(&candidate) {
                    continue;
                }
                let mut trial_indices = basis_indices.clone();
                trial_indices[position] = candidate;
                let trial_rows = trial_indices
                    .iter()
                    .map(|&index| factors[index].clone())
                    .collect::<Vec<_>>();
                if vector_space_rank(trial_rows) != rank {
                    continue;
                }
                let trial = factorization_from_basis(factors, &trial_indices);
                let trial_score = score(&trial);
                if trial_score < best_score {
                    best_score = trial_score;
                    best_swap = Some((position, candidate, trial));
                }
            }
        }
        let Some((position, candidate, trial)) = best_swap else {
            break;
        };
        basis_indices[position] = candidate;
        best = trial;
    }
    best
}

fn main() {
    let routing_low_row_bits = std::env::var("ASPIS_ATOMIC_ROUTING_LOW_MASK")
        .ok()
        .map(|value| {
            let value = value.strip_prefix("0x").unwrap_or(&value);
            u16::from_str_radix(value, 16).expect("hex row-bit mask")
        })
        .unwrap_or(DEFAULT_ROUTING_LOW_ROW_BITS);
    let pivot_strategy =
        std::env::var("ASPIS_ATOMIC_ROUTING_PIVOT").unwrap_or_else(|_| "first".to_owned());
    let basis_product_weight = std::env::var("ASPIS_ATOMIC_ROUTING_BASIS_PRODUCT_WEIGHT")
        .ok()
        .map(|value| value.parse::<usize>().expect("basis product weight"))
        // Exhaustive SBF profiling pins weight one: it keeps the 29-form
        // basis while minimizing the measured entry/product tradeoff.
        .unwrap_or(1);
    assert!(matches!(
        pivot_strategy.as_str(),
        "first" | "sparse" | "runtime"
    ));
    assert_eq!(routing_low_row_bits.count_ones(), 4);
    let registry = build_atomic_state_only_registry_v3().unwrap();
    let fingerprint = atomic_state_only_registry_fingerprint_v3(&registry).unwrap();
    assert_eq!(
        fingerprint,
        PINNED_ATOMIC_STATE_ONLY_REGISTRY_FINGERPRINT_V3
    );
    println!("// @generated by examples/generate_atomic_state_only_terminal_constants.rs.");
    println!("// Do not hand-edit. Random off-domain identity tests bind this file to the host registry.");
    println!();
    println!("pub(crate) const COMPILED_ATOMIC_REGISTRY_FINGERPRINT: u64 = {fingerprint:#018x};");
    println!(
        "pub(crate) const ATOMIC_COPY_ROUTING_LOW_ROW_BITS: u16 = {routing_low_row_bits:#06x};"
    );

    let active_rows = registry
        .links
        .iter()
        .flat_map(|link| [link.producer.row, link.consumer.row])
        .collect::<BTreeSet<_>>();
    let mut active_fingerprint = 0xcbf2_9ce4_8422_2325u64;
    for row in &active_rows {
        for byte in row.to_le_bytes() {
            active_fingerprint ^= u64::from(byte);
            active_fingerprint = active_fingerprint.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
    println!(
        "pub(crate) const COMPILED_ATOMIC_COPY_ACTIVE_ROWS: [u16; {}] = {:?};",
        active_rows.len(),
        active_rows.iter().copied().collect::<Vec<_>>()
    );
    println!(
        "pub(crate) const COMPILED_ATOMIC_COPY_ACTIVE_ROWS_FINGERPRINT: u64 = {active_fingerprint:#018x};"
    );
    let mut inactive_row_masks = [u16::MAX; 64];
    for &row in &active_rows {
        let row = usize::from(row);
        inactive_row_masks[row >> 4] &= !(1u16 << (row & 15));
    }
    let mut inactive_group_masks = Vec::<u16>::new();
    let mut inactive_row_groups = [0u8; 64];
    for (high, &mask) in inactive_row_masks.iter().enumerate() {
        let group = inactive_group_masks
            .iter()
            .position(|&candidate| candidate == mask)
            .unwrap_or_else(|| {
                inactive_group_masks.push(mask);
                inactive_group_masks.len() - 1
            });
        inactive_row_groups[high] = group as u8;
    }
    println!(
        "pub(crate) const COMPILED_ATOMIC_COPY_INACTIVE_ROW_MASKS: [u16; 64] = {:?};",
        inactive_row_masks
    );
    println!(
        "pub(crate) const COMPILED_ATOMIC_COPY_INACTIVE_ROW_GROUPS: [u8; 64] = {:?};",
        inactive_row_groups
    );
    println!(
        "pub(crate) const COMPILED_ATOMIC_COPY_INACTIVE_GROUP_MASKS: [u16; {}] = {:?};",
        inactive_group_masks.len(),
        inactive_group_masks
    );
    let high_row_bits = (!routing_low_row_bits) & 0x03ff;
    let mut active_low_masks = [0u16; 64];
    for &row in &active_rows {
        let row = usize::from(row);
        active_low_masks[projected_index(row, high_row_bits)] |=
            1 << projected_index(row, routing_low_row_bits);
    }
    let distinct_low_masks = active_low_masks
        .iter()
        .copied()
        .filter(|&mask| mask != 0)
        .collect::<BTreeSet<_>>();
    println!(
        "pub(crate) const COMPILED_ATOMIC_COPY_ACTIVE_FACTORS: [(u64, u16); {}] = [",
        distinct_low_masks.len()
    );
    for low_mask in distinct_low_masks {
        let high_mask = active_low_masks
            .iter()
            .enumerate()
            .filter(|(_, mask)| **mask == low_mask)
            .fold(0u64, |mask, (high, _)| mask | (1u64 << high));
        println!("    (0x{high_mask:016x}, 0x{low_mask:04x}),");
    }
    println!("];");

    let mut patterns = Vec::new();
    for link in &registry.links {
        for tuple in [link.producer, link.consumer] {
            let candidate = pattern(tuple);
            if !patterns.contains(&candidate) {
                patterns.push(candidate);
            }
        }
    }
    println!(
        "pub(crate) const ATOMIC_COPY_PATTERNS: [CompiledAtomicPattern; {}] = [",
        patterns.len()
    );
    for item in &patterns {
        println!(
            "    CompiledAtomicPattern {{ kinds: {}, columns: {}, scales: {}, offsets: {} }},",
            emit_u8_array(&item.kinds),
            emit_u8_array(&item.columns),
            emit_u32_array(&item.scales),
            emit_u32_array(&item.offsets)
        );
    }
    println!("];");

    let matrix_count = 4 * (2 + patterns.len());
    let mut matrices = vec![vec![vec![M31::ZERO; 16]; 64]; matrix_count];
    let mut pattern_masks = [0u16; 4];
    let mut producer_arity = [0u8; 1024];
    let mut consumer_arity = [0u8; 1024];
    let mut compiled_links = Vec::new();
    for link in &registry.links {
        let mut endpoints = Vec::new();
        for (tuple, side, arity) in [
            (link.producer, 0usize, &mut producer_arity),
            (link.consumer, 2usize, &mut consumer_arity),
        ] {
            let row = usize::from(tuple.row);
            let slot = side + usize::from(arity[row]);
            assert!(
                slot < side + 2,
                "copy endpoint arity exceeds two at row {row}"
            );
            arity[row] += 1;
            let key = pattern(tuple);
            let pattern_id = patterns
                .iter()
                .position(|candidate| *candidate == key)
                .unwrap();
            let high = projected_index(row, high_row_bits);
            let low = projected_index(row, routing_low_row_bits);
            let base = slot * (2 + patterns.len());
            matrices[base][high][low] = matrices[base][high][low].add(M31::ONE);
            matrices[base + 1][high][low] = matrices[base + 1][high][low].add(link.tag);
            matrices[base + 2 + pattern_id][high][low] =
                matrices[base + 2 + pattern_id][high][low].add(M31::ONE);
            pattern_masks[slot] |= 1 << pattern_id;
            endpoints.push((tuple.row, (slot - side) as u8, pattern_id as u8));
        }
        compiled_links.push((link.tag.0, endpoints[0], endpoints[1]));
    }

    let mut raw_terms = Vec::<(u8, u8, u8)>::new();
    let mut unique_left = Vec::<Vec<M31>>::new();
    let mut unique_right = Vec::<Vec<M31>>::new();
    for (matrix_index, matrix) in matrices.iter_mut().enumerate() {
        loop {
            let mut candidates = Vec::new();
            for row in 0..64 {
                for column in 0..16 {
                    if matrix[row][column] != M31::ZERO {
                        candidates.push((row, column));
                    }
                }
            }
            let pivot = if pivot_strategy == "first" {
                candidates.into_iter().next()
            } else {
                candidates.into_iter().min_by_key(|&(row, column)| {
                    let (left, right) = pivot_factors(matrix, row, column);
                    let left_id = unique_left.iter().position(|factor| *factor == left);
                    let right_id = unique_right.iter().position(|factor| *factor == right);
                    let (left_entries, left_products) = factor_cost(&left);
                    let (right_entries, right_products) = factor_cost(&right);
                    let new_entries =
                        left_id.map_or(left_entries, |_| 0) + right_id.map_or(right_entries, |_| 0);
                    let new_products = left_id.map_or(left_products, |_| 0)
                        + right_id.map_or(right_products, |_| 0);
                    let pair_is_new = match (left_id, right_id) {
                        (Some(left), Some(right)) => {
                            !raw_terms
                                .iter()
                                .any(|&(_, candidate_left, candidate_right)| {
                                    usize::from(candidate_left) == left
                                        && usize::from(candidate_right) == right
                                })
                        }
                        _ => true,
                    };
                    if pivot_strategy == "sparse" {
                        (
                            new_products,
                            new_entries,
                            usize::from(pair_is_new),
                            row,
                            column,
                        )
                    } else {
                        // Approximate the SBF evaluator: one fresh QM31 pair
                        // product is far dearer than one sparse entry, while a
                        // nontrivial scalar coefficient adds four M31 products.
                        let estimated =
                            usize::from(pair_is_new) * 400 + new_entries * 10 + new_products * 30;
                        (estimated, new_products, new_entries, row, column)
                    }
                })
            };
            let Some((pivot_row, pivot_column)) = pivot else {
                break;
            };
            let (left, right) = pivot_factors(matrix, pivot_row, pivot_column);
            let left_id = unique_left
                .iter()
                .position(|factor| *factor == left)
                .unwrap_or_else(|| {
                    unique_left.push(left.clone());
                    unique_left.len() - 1
                });
            let right_id = unique_right
                .iter()
                .position(|factor| *factor == right)
                .unwrap_or_else(|| {
                    unique_right.push(right.clone());
                    unique_right.len() - 1
                });
            raw_terms.push((matrix_index as u8, left_id as u8, right_id as u8));
            for row in 0..64 {
                for column in 0..16 {
                    matrix[row][column] = matrix[row][column].sub(left[row].mul(right[column]));
                }
            }
        }
    }

    let left_factorization = factorize_linear_forms(&unique_left, basis_product_weight);
    let right_factorization = factorize_linear_forms(&unique_right, basis_product_weight);
    let current_reductions: usize = left_factorization
        .basis
        .iter()
        .chain(left_factorization.expressions.iter())
        .chain(right_factorization.basis.iter())
        .chain(right_factorization.expressions.iter())
        .map(|factor| product_reduction_groups(factor, false))
        .sum();
    let packed_reductions: usize = left_factorization
        .basis
        .iter()
        .chain(left_factorization.expressions.iter())
        .chain(right_factorization.basis.iter())
        .chain(right_factorization.expressions.iter())
        .map(|factor| product_reduction_groups(factor, true))
        .sum();
    let mut entries = Vec::<(u8, u32)>::new();
    let left_basis_factors = append_sparse_factors(&mut entries, &left_factorization.basis);
    let left_reconstruction_factors =
        append_sparse_factors(&mut entries, &left_factorization.expressions);
    let right_basis_factors = append_sparse_factors(&mut entries, &right_factorization.basis);
    let right_reconstruction_factors =
        append_sparse_factors(&mut entries, &right_factorization.expressions);

    let mut pair_terms = Vec::<(u8, u8, u16, u8)>::new();
    let mut destinations = Vec::<u8>::new();
    let mut emitted_pairs = BTreeSet::new();
    for &(_, left, right) in &raw_terms {
        if !emitted_pairs.insert((left, right)) {
            continue;
        }
        let start = destinations.len();
        destinations.extend(raw_terms.iter().filter_map(
            |&(matrix, candidate_left, candidate_right)| {
                (candidate_left == left && candidate_right == right).then_some(matrix)
            },
        ));
        pair_terms.push((
            left,
            right,
            start as u16,
            (destinations.len() - start) as u8,
        ));
    }

    println!(
        "pub(crate) const ATOMIC_COPY_ROUTING_RANK: usize = {};",
        raw_terms.len()
    );
    println!(
        "pub(crate) const ATOMIC_COPY_ROUTING_LEFT_BASIS_FACTORS: [(u16, u8); {}] = {:?};",
        left_basis_factors.len(),
        left_basis_factors
    );
    println!(
        "pub(crate) const ATOMIC_COPY_ROUTING_LEFT_RECONSTRUCTION_FACTORS: [(u16, u8); {}] = {:?};",
        left_reconstruction_factors.len(),
        left_reconstruction_factors
    );
    println!(
        "pub(crate) const ATOMIC_COPY_ROUTING_LEFT_DIRECT_BASIS: [u8; {}] = {:?};",
        left_factorization.direct_basis.len(),
        left_factorization.direct_basis
    );
    println!(
        "pub(crate) const ATOMIC_COPY_ROUTING_RIGHT_BASIS_FACTORS: [(u16, u8); {}] = {:?};",
        right_basis_factors.len(),
        right_basis_factors
    );
    println!(
        "pub(crate) const ATOMIC_COPY_ROUTING_RIGHT_RECONSTRUCTION_FACTORS: [(u16, u8); {}] = {:?};",
        right_reconstruction_factors.len(),
        right_reconstruction_factors
    );
    println!(
        "pub(crate) const ATOMIC_COPY_ROUTING_RIGHT_DIRECT_BASIS: [u8; {}] = {:?};",
        right_factorization.direct_basis.len(),
        right_factorization.direct_basis
    );
    println!(
        "pub(crate) const ATOMIC_COPY_ROUTING_ENTRIES: [(u8, u32); {}] = {:?};",
        entries.len(),
        entries
    );
    println!(
        "pub(crate) const ATOMIC_COPY_ROUTING_PAIR_TERMS: [(u8, u8, u16, u8); {}] = {:?};",
        pair_terms.len(),
        pair_terms
    );
    println!(
        "pub(crate) const ATOMIC_COPY_ROUTING_DESTINATIONS: [u8; {}] = {:?};",
        destinations.len(),
        destinations
    );
    println!(
        "pub(crate) const ATOMIC_COPY_ROUTING_PATTERN_MASKS: [u16; 4] = {:?};",
        pattern_masks
    );
    println!(
        "pub(crate) const COMPILED_ATOMIC_COPY_LINKS: [CompiledAtomicCopyLink; {}] = [",
        compiled_links.len()
    );
    for (tag, producer, consumer) in compiled_links {
        println!(
            "    CompiledAtomicCopyLink {{ tag: {tag}, producer: CompiledAtomicCopyEndpoint {{ row: {}, slot: {}, pattern: {} }}, consumer: CompiledAtomicCopyEndpoint {{ row: {}, slot: {}, pattern: {} }} }},",
            producer.0, producer.1, producer.2, consumer.0, consumer.1, consumer.2
        );
    }
    println!("];");
    eprintln!(
        "atomic terminal: pivot={} basis_product_weight={} links={} active={} patterns={} rank={} left={} left_fact={:?} right={} right_fact={:?} shared_pairs={} destinations={} entries={} products={} reduction_groups={}/{} P={P}",
        pivot_strategy,
        basis_product_weight,
        registry.links.len(),
        active_rows.len(),
        patterns.len(),
        raw_terms.len(),
        unique_left.len(),
        left_factorization.cost(),
        unique_right.len(),
        right_factorization.cost(),
        pair_terms.len(),
        destinations.len(),
        entries.len(),
        entries
            .iter()
            .filter(|(_, coefficient)| *coefficient != 1 && *coefficient != P - 1)
            .count(),
        current_reductions,
        packed_reductions,
    );
}
