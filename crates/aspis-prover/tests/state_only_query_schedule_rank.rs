//! Adversarial schedule probes for the state-only hiding rank argument.
//!
//! This file is deliberately diagnostic.  It tests the deterministic
//! layer-zero part of the mask map on structured fiber schedules; it is not a
//! proof that the complete sumcheck quotient has full rank for every query
//! tuple.

#[path = "support/m31_circle_reference.rs"]
mod circle_reference;

use aspis_core::field::M31;
use aspis_prover::circle_candidate::CircleEncoder;
use std::collections::BTreeSet;

const TRACE_ROWS: usize = 1024;
const FIBER_SLOTS: usize = 4;
const COMMON_TAIL_START: usize = 879;

fn rank_m31(mut matrix: Vec<Vec<M31>>) -> usize {
    let rows = matrix.len();
    let columns = matrix.first().map_or(0, Vec::len);
    let mut rank = 0usize;
    for column in 0..columns {
        let Some(pivot) = (rank..rows).find(|&row| matrix[row][column] != M31::ZERO) else {
            continue;
        };
        matrix.swap(rank, pivot);
        let inverse = matrix[rank][column].inv();
        for value in &mut matrix[rank][column..] {
            *value = value.mul(inverse);
        }
        let pivot_tail = matrix[rank][column..].to_vec();
        for row in rank + 1..rows {
            let scale = matrix[row][column];
            if scale == M31::ZERO {
                continue;
            }
            for (value, pivot_value) in matrix[row][column..].iter_mut().zip(&pivot_tail) {
                *value = value.sub(scale.mul(*pivot_value));
            }
        }
        rank += 1;
        if rank == rows {
            break;
        }
    }
    rank
}

fn structured_schedules(fibers: usize, queries: usize) -> Vec<(&'static str, Vec<usize>)> {
    let mut schedules = Vec::new();
    for (name, start, stride) in [
        ("consecutive-0", 0usize, 1usize),
        ("consecutive-quarter", fibers / 4, 1),
        ("stride-2", 0, 2),
        ("stride-4", 0, 4),
        ("stride-16", 0, 16),
        ("stride-64", 0, 64),
        ("stride-128", 0, 128),
        ("stride-256", 0, 256),
        ("stride-512", 0, 512),
        ("stride-1024", 0, 1024),
        ("odd-stride", 17, 573),
    ] {
        let mut values = Vec::with_capacity(queries);
        let mut candidate = start;
        let mut valid = true;
        while values.len() < queries {
            let value = candidate % fibers;
            if values.contains(&value) {
                valid = false;
                break;
            }
            values.push(value);
            candidate = candidate.wrapping_add(stride);
        }
        if valid {
            schedules.push((name, values));
        }
    }
    schedules
}

fn common_tail_query_matrix(
    encoder: &CircleEncoder,
    schedules: &[(&'static str, Vec<usize>)],
    coefficient_start: usize,
) -> Vec<(&'static str, usize)> {
    let tail = coefficient_start..TRACE_ROWS;
    let codewords = tail
        .map(|coefficient| {
            let mut message = vec![M31::ZERO; TRACE_ROWS];
            message[coefficient] = M31::ONE;
            encoder.encode_c1_message(&message).unwrap()
        })
        .collect::<Vec<_>>();

    schedules
        .iter()
        .map(|(name, queries)| {
            let mut rows = Vec::with_capacity(FIBER_SLOTS * queries.len());
            for &query in queries {
                for slot in 0..FIBER_SLOTS {
                    let codeword_index = FIBER_SLOTS * query + slot;
                    rows.push(
                        codewords
                            .iter()
                            .map(|codeword| codeword[codeword_index])
                            .collect::<Vec<_>>(),
                    );
                }
            }
            (*name, rank_m31(rows))
        })
        .collect()
}

fn run(domain_log: u32, queries: usize) {
    let encoder = CircleEncoder::new_for_domain_log(domain_log);
    let fibers = encoder.codeword_len() / FIBER_SLOTS;
    let schedules = structured_schedules(fibers, queries);
    let ranks = common_tail_query_matrix(&encoder, &schedules, COMMON_TAIL_START);
    for (name, rank) in ranks {
        eprintln!("domain-log={domain_log} q={queries} {name}: rank={rank}");
        assert_eq!(rank, queries * FIBER_SLOTS, "schedule {name}");
    }
}

fn double_x(value: M31) -> M31 {
    value.mul(value).add(value.mul(value)).sub(M31::ONE)
}

#[test]
fn rate32_aligned_block_has_distinct_nodes_and_nonzero_common_factor_everywhere() {
    let domain_log = 15u32;
    let fibers = 1usize << (domain_log - 2);
    let mut nodes = BTreeSet::new();
    for fiber in 0..fibers {
        let point = circle_reference::bit_reversed_domain_point(4 * fiber, domain_log);
        let node = double_x(point.x);
        assert!(
            nodes.insert(node.0),
            "duplicate quotient node at fiber {fiber}"
        );

        // Line tensor indices 224..255 have bits 5,6,7 fixed. Their common
        // factor is D^5(node) * D^6(node) * D^7(node), for D(x)=2x^2-1.
        let mut iterated = node;
        let mut common = M31::ONE;
        for level in 0..=7 {
            if level >= 5 {
                common = common.mul(iterated);
            }
            iterated = double_x(iterated);
        }
        assert_ne!(common, M31::ZERO, "zero common factor at fiber {fiber}");
    }
    assert_eq!(nodes.len(), fibers);
}

#[test]
fn aligned_affine_subcube_is_a_deterministic_rate32_query_basis() {
    // Rows 896..1023 are `111xxxxxxx`: after the invertible four-slot
    // butterfly, each residue class supplies the aligned tensor interval
    // 224..255.  It is a nonzero common factor times all degree-<=31 line
    // polynomials, so any 29 distinct lower-domain points have rank 29 in
    // each residue class.
    let encoder = CircleEncoder::new_for_domain_log(15);
    let schedules = structured_schedules(encoder.codeword_len() / FIBER_SLOTS, 29);
    for (name, rank) in common_tail_query_matrix(&encoder, &schedules, 896) {
        eprintln!("aligned rate32 q29 {name}: rank={rank}");
        assert_eq!(rank, 116, "schedule {name}");
    }
}

#[test]
fn aligned_affine_subcube_is_too_small_for_rate16_q36() {
    let encoder = CircleEncoder::new_for_domain_log(14);
    let schedules = structured_schedules(encoder.codeword_len() / FIBER_SLOTS, 36);
    for (name, rank) in common_tail_query_matrix(&encoder, &schedules, 896) {
        eprintln!("aligned rate16 q36 {name}: rank={rank}");
        assert_eq!(rank, 128, "schedule {name}");
    }
}

#[test]
fn common_tail_is_not_silently_assumed_to_be_a_monomial_vandermonde_basis() {
    // A scaled monomial Vandermonde proof would require the ratio between
    // adjacent coefficient columns to be constant at each codeword point.
    // Check that premise explicitly before anyone cites it.  The direct
    // circle-tensor FFT basis does not promise this representation.
    let encoder = CircleEncoder::new_for_domain_log(14);
    let codewords = (COMMON_TAIL_START..COMMON_TAIL_START + 3)
        .map(|coefficient| {
            let mut message = vec![M31::ZERO; TRACE_ROWS];
            message[coefficient] = M31::ONE;
            encoder.encode_c1_message(&message).unwrap()
        })
        .collect::<Vec<_>>();
    let mut recurrence_points = 0usize;
    for point in 0..encoder.codeword_len() {
        if codewords[0][point] == M31::ZERO || codewords[1][point] == M31::ZERO {
            continue;
        }
        let ratio01 = codewords[1][point].mul(codewords[0][point].inv());
        let ratio12 = codewords[2][point].mul(codewords[1][point].inv());
        if ratio01 == ratio12 {
            recurrence_points += 1;
        }
    }
    eprintln!(
        "common-tail adjacent-column monomial recurrence points: {recurrence_points}/{}",
        encoder.codeword_len()
    );
    assert!(recurrence_points < encoder.codeword_len());
}

#[test]
fn common_relation_free_tail_surjects_on_structured_rate16_query_schedules() {
    run(14, 36);
}

#[test]
fn common_relation_free_tail_surjects_on_structured_rate32_query_schedules() {
    run(15, 29);
}
