//! Exhaustively search row-bit bipartitions for the atomic-v3 routing tensor.
//!
//! This is a derivation tool, not verifier code.  A chosen partition must be
//! regenerated into constants and protected by compiled/reference identity
//! tests before it can affect an SBF measurement.

use std::collections::BTreeSet;

use aspis_core::field::M31;
use aspis_statement::atomic_state_only_registry::{
    build_atomic_state_only_registry_v3, AtomicCopyTupleV3, AtomicTupleLimbV3,
};

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
                output.kinds[index] = 2;
                output.columns[index] = cell.column;
                output.scales[index] = scale.0;
                output.offsets[index] = offset.0;
            }
        }
    }
    output
}

fn projected_index(row: usize, bit_mask: u16) -> usize {
    let mut output = 0usize;
    for bit in (0..10).rev() {
        if bit_mask & (1 << bit) != 0 {
            output = (output << 1) | ((row >> bit) & 1);
        }
    }
    output
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Score {
    shared_pairs: usize,
    total_rank: usize,
    factor_entries: usize,
    left_factors: usize,
    right_factors: usize,
    low_mask: u16,
}

#[derive(Clone, Copy)]
struct Endpoint {
    row: usize,
    slot: usize,
    pattern: usize,
    tag: M31,
}

fn endpoints() -> (usize, Vec<Endpoint>) {
    let registry = build_atomic_state_only_registry_v3().unwrap();
    let mut patterns = Vec::new();
    for link in &registry.links {
        for tuple in [link.producer, link.consumer] {
            let candidate = pattern(tuple);
            if !patterns.contains(&candidate) {
                patterns.push(candidate);
            }
        }
    }
    let mut producer_arity = [0u8; 1024];
    let mut consumer_arity = [0u8; 1024];
    let mut endpoints = Vec::with_capacity(2 * registry.links.len());
    for link in &registry.links {
        for (tuple, side, arity) in [
            (link.producer, 0usize, &mut producer_arity),
            (link.consumer, 2usize, &mut consumer_arity),
        ] {
            let row = usize::from(tuple.row);
            let slot = side + usize::from(arity[row]);
            arity[row] += 1;
            let pattern = patterns
                .iter()
                .position(|value| *value == pattern(tuple))
                .unwrap();
            endpoints.push(Endpoint {
                row,
                slot,
                pattern,
                tag: link.tag,
            });
        }
    }
    (patterns.len(), endpoints)
}

fn score_partition(pattern_count: usize, endpoints: &[Endpoint], low_mask: u16) -> Score {
    let high_mask = (!low_mask) & 0x03ff;
    let high_len = 1usize << high_mask.count_ones();
    let low_len = 1usize << low_mask.count_ones();
    let matrix_count = 4 * (2 + pattern_count);
    let mut matrices = vec![vec![vec![M31::ZERO; low_len]; high_len]; matrix_count];
    for endpoint in endpoints {
        let high = projected_index(endpoint.row, high_mask);
        let low = projected_index(endpoint.row, low_mask);
        let base = endpoint.slot * (2 + pattern_count);
        matrices[base][high][low] = matrices[base][high][low].add(M31::ONE);
        matrices[base + 1][high][low] = matrices[base + 1][high][low].add(endpoint.tag);
        matrices[base + 2 + endpoint.pattern][high][low] =
            matrices[base + 2 + endpoint.pattern][high][low].add(M31::ONE);
    }

    let mut unique_left = Vec::<Vec<M31>>::new();
    let mut unique_right = Vec::<Vec<M31>>::new();
    let mut pairs = BTreeSet::new();
    let mut total_rank = 0usize;
    for matrix in &mut matrices {
        loop {
            let pivot = (0..high_len).find_map(|row| {
                (0..low_len)
                    .find(|&column| matrix[row][column] != M31::ZERO)
                    .map(|column| (row, column))
            });
            let Some((pivot_row, pivot_column)) = pivot else {
                break;
            };
            let inverse = matrix[pivot_row][pivot_column].inv();
            let left = (0..high_len)
                .map(|row| matrix[row][pivot_column])
                .collect::<Vec<_>>();
            let right = (0..low_len)
                .map(|column| matrix[pivot_row][column].mul(inverse))
                .collect::<Vec<_>>();
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
            pairs.insert((left_id, right_id));
            total_rank += 1;
            for row in 0..high_len {
                for column in 0..low_len {
                    matrix[row][column] = matrix[row][column].sub(left[row].mul(right[column]));
                }
            }
        }
    }
    let factor_entries = unique_left
        .iter()
        .chain(&unique_right)
        .map(|factor| factor.iter().filter(|&&value| value != M31::ZERO).count())
        .sum();
    Score {
        shared_pairs: pairs.len(),
        total_rank,
        factor_entries,
        left_factors: unique_left.len(),
        right_factors: unique_right.len(),
        low_mask,
    }
}

fn main() {
    let (pattern_count, endpoints) = endpoints();
    let mut scores = Vec::new();
    // Keep both selector tables reasonably small.  The current compiler uses
    // four low bits; five/five and six/four are both viable SBF shapes.
    for low_bits in 3..=7 {
        for low_mask in 1u16..0x03ff {
            if low_mask.count_ones() == low_bits {
                scores.push(score_partition(pattern_count, &endpoints, low_mask));
            }
        }
    }
    scores.sort_unstable();
    println!("best partitions by (shared pairs, rank, entries):");
    for score in scores.iter().take(20) {
        println!("{score:?}");
    }
    for bits in 3..=7 {
        let best_pairs = scores
            .iter()
            .filter(|score| score.low_mask.count_ones() == bits)
            .min()
            .unwrap();
        let best_entries = scores
            .iter()
            .filter(|score| score.low_mask.count_ones() == bits)
            .min_by_key(|score| (score.factor_entries, score.shared_pairs, score.total_rank))
            .unwrap();
        println!("low_bits={bits} best_pairs={best_pairs:?} best_entries={best_entries:?}");
    }
    let current = score_partition(pattern_count, &endpoints, 0x000f);
    println!("current: {current:?}");
}
