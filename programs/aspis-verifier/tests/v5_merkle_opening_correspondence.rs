//! Byte- and routing-level evidence for the V5 private Merkle bridge.
//!
//! These tests exercise the production helper composition against the released
//! proof and inspect the actual hash-call buffers.  The universal statement is
//! the Lean theorem; these tests are deliberately supporting evidence only.

#![cfg(any(feature = "v5-cu-probe", feature = "v5-production-tag67"))]

use std::cell::RefCell;

use aspis_core::field::{M31, QM31};
use aspis_core::merkle::Radix4BinaryCapTopology;
use aspis_core::state_only_private_openings::{
    verify_state_only_private_opening_from_proof_with_topology, StateOnlyPrivateOpening,
};
use aspis_statement::{
    atomic_payment_statement_digest_v4, decode_digest_canonical, AtomicPaymentStatementV4,
    SpendPublic,
};
use aspis_verifier::v5_cu_probe::private_openings::{
    verify_v5_private_openings, V5PrivateOpeningRoots, VerifiedV5PrivateOpenings,
    V5_PRIVATE_DEPTHS, V5_PRIVATE_TREE_TAGS, V5_PRIVATE_VALUE_WIDTHS,
};
use aspis_verifier::v5_cu_probe::{
    v5_complete_queries_with_statement_digest, V5_CU_PROBE_PRIVATE_PROOF_OFFSET,
    V5_CU_PROBE_PRIVATE_ROOTS_OFFSET,
};
use solana_program::hash::hashv;

const MAINNET_PROOF: &[u8] =
    include_bytes!("../../../release/aspis-v5-tag67-mainnet-v1/proof/v5-mainnet-proof.bin");

#[derive(Clone, Debug)]
struct HashCall {
    slices: Vec<usize>,
    bytes: Vec<u8>,
}

thread_local! {
    static HASH_CALLS: RefCell<Vec<HashCall>> = const { RefCell::new(Vec::new()) };
}

fn host_hashv(inputs: &[&[u8]]) -> [u8; 32] {
    hashv(inputs).to_bytes()
}

fn tracing_hashv(inputs: &[&[u8]]) -> [u8; 32] {
    HASH_CALLS.with(|calls| {
        calls.borrow_mut().push(HashCall {
            slices: inputs.iter().map(|input| input.len()).collect(),
            bytes: inputs
                .iter()
                .flat_map(|input| input.iter().copied())
                .collect(),
        });
    });
    host_hashv(inputs)
}

fn take_hash_calls() -> Vec<HashCall> {
    HASH_CALLS.with(|calls| std::mem::take(&mut *calls.borrow_mut()))
}

fn decode_hex_32(value: &str) -> [u8; 32] {
    assert_eq!(value.len(), 64);
    let mut output = [0u8; 32];
    for (index, byte) in output.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&value[index * 2..index * 2 + 2], 16).unwrap();
    }
    output
}

fn decode_digest(value: &str) -> [M31; 8] {
    decode_digest_canonical(&decode_hex_32(value)).unwrap()
}

fn mainnet_statement() -> AtomicPaymentStatementV4 {
    AtomicPaymentStatementV4 {
        pool: decode_hex_32("0d5b6b8aef565a35887ad0c60acbaa27a7c8db501a1adfc1ad2171c44664de48"),
        sequence: 0,
        spend: SpendPublic {
            anchor: decode_digest(
                "2f1c920dc6b3ad1fa6d29a0da5eb3232892c4c0edcd86c4a3825215a9fb7da63",
            ),
            nullifier: decode_digest(
                "251bbb2be96bef3b6eccab04da5ab27bc3b3c04bfb9ef5598a417d3406759317",
            ),
            output_commitment: decode_digest(
                "7a08e0333baf4b7bc34e14690adcb507ef6e32021e5767628d388337eab0c30e",
            ),
            asset_id: M31(17),
            fee: 1,
        },
        output_anchor: decode_digest(
            "e0de9172992f6e4803419a5fca909d3d3507ee7d81cc956ef4977a1ceeab967f",
        ),
        deployment_domain: decode_hex_32(
            "87682be1a518ecc95f7aac6e7f400a1419c0383a0d554877a6ab0a3ce6e31936",
        ),
    }
}

fn released_roots() -> V5PrivateOpeningRoots {
    let bytes =
        &MAINNET_PROOF[V5_CU_PROBE_PRIVATE_ROOTS_OFFSET..V5_CU_PROBE_PRIVATE_ROOTS_OFFSET + 5 * 32];
    V5PrivateOpeningRoots {
        c1: bytes[0..32].try_into().unwrap(),
        c2: bytes[32..64].try_into().unwrap(),
        later: [
            bytes[64..96].try_into().unwrap(),
            bytes[96..128].try_into().unwrap(),
            bytes[128..160].try_into().unwrap(),
        ],
    }
}

fn released_queries() -> [u32; 18] {
    let statement_digest =
        atomic_payment_statement_digest_v4(&mainnet_statement(), host_hashv).unwrap();
    v5_complete_queries_with_statement_digest(host_hashv, MAINNET_PROOF, &statement_digest).unwrap()
}

fn released_suffix() -> &'static [u8] {
    &MAINNET_PROOF[V5_CU_PROBE_PRIVATE_PROOF_OFFSET..]
}

fn verify_released<'a>(
    hash: aspis_core::HashFn,
    proof: &'a [u8],
    queries: &[u32],
) -> Result<
    VerifiedV5PrivateOpenings<'a>,
    aspis_verifier::v5_cu_probe::private_openings::V5PrivateOpeningError,
> {
    verify_v5_private_openings(hash, &released_roots(), queries, proof)
}

fn section_bounds(openings: &VerifiedV5PrivateOpenings<'_>) -> [(usize, usize); 5] {
    let lengths = [
        openings.c1.offsets.end,
        openings.c2.offsets.end,
        openings.later[0].offsets.end,
        openings.later[1].offsets.end,
        openings.later[2].offsets.end,
    ];
    let mut start = 0usize;
    core::array::from_fn(|section| {
        let bounds = (start, start + lengths[section]);
        start = bounds.1;
        bounds
    })
}

fn openings<'a>(
    verified: &'a VerifiedV5PrivateOpenings<'a>,
) -> [&'a StateOnlyPrivateOpening<'a>; 5] {
    [
        &verified.c1,
        &verified.c2,
        &verified.later[0],
        &verified.later[1],
        &verified.later[2],
    ]
}

fn monotone_value<'a>(
    opening: &'a StateOnlyPrivateOpening<'a>,
    indices: &[u32],
    ordinal: &mut usize,
    index: u32,
) -> &'a [u8] {
    while *ordinal < indices.len() && indices[*ordinal] < index {
        *ordinal += 1;
    }
    assert_eq!(indices.get(*ordinal).copied(), Some(index));
    opening.value(*ordinal).unwrap()
}

fn assert_four_qm31_slots_are_canonical(value: &[u8]) {
    assert_eq!(value.len(), 64);
    for slot in 0..4 {
        assert!(QM31::from_le_bytes(&value[slot * 16..(slot + 1) * 16]).is_some());
    }
}

#[test]
fn released_helper_hashes_exact_records_and_exact_domain_separated_buffers() {
    let queries = released_queries();
    take_hash_calls();
    let verified = verify_released(tracing_hashv, released_suffix(), &queries).unwrap();
    let calls = take_hash_calls();

    for (section, opening) in openings(&verified).into_iter().enumerate() {
        assert_eq!(
            opening.record_width(),
            V5_PRIVATE_VALUE_WIDTHS[section] + 32
        );
        for ordinal in 0..opening.count {
            let record = opening.record(ordinal).unwrap();
            let value = opening.value(ordinal).unwrap();
            let salt = opening.salt(ordinal).unwrap();
            assert_eq!(record, [value, salt.as_slice()].concat());
            assert_eq!(record.as_ptr(), value.as_ptr());
            assert_eq!(
                salt.as_ptr() as usize - record.as_ptr() as usize,
                V5_PRIVATE_VALUE_WIDTHS[section]
            );
        }
    }

    let leaf_calls = calls
        .iter()
        .filter(|call| call.bytes.first() == Some(&0x10))
        .collect::<Vec<_>>();
    assert_eq!(
        leaf_calls.len(),
        openings(&verified)
            .iter()
            .map(|opening| opening.count)
            .sum()
    );
    for section in 0..5 {
        let matching = leaf_calls
            .iter()
            .filter(|call| call.bytes.get(1) == Some(&V5_PRIVATE_TREE_TAGS[section]))
            .collect::<Vec<_>>();
        assert_eq!(matching.len(), openings(&verified)[section].count);
        for call in matching {
            assert_eq!(call.slices, [2, V5_PRIVATE_VALUE_WIDTHS[section] + 32]);
            assert_eq!(call.bytes.len(), 2 + V5_PRIVATE_VALUE_WIDTHS[section] + 32);
        }
    }

    let radix_calls = calls
        .iter()
        .filter(|call| call.bytes.first() == Some(&0x12))
        .collect::<Vec<_>>();
    assert!(!radix_calls.is_empty());
    assert!(radix_calls
        .iter()
        .all(|call| call.slices == [129] && call.bytes.len() == 1 + 4 * 32));

    let binary_calls = calls
        .iter()
        .filter(|call| call.bytes.first() == Some(&0x11))
        .collect::<Vec<_>>();
    assert_eq!(binary_calls.len(), 5);
    assert!(binary_calls
        .iter()
        .all(|call| call.slices == [65] && call.bytes.len() == 1 + 2 * 32));
    assert_eq!(
        leaf_calls.len() + radix_calls.len() + binary_calls.len(),
        calls.len()
    );
}

#[test]
fn returned_slices_and_ordinals_are_exactly_the_four_fri_read_schedules() {
    let queries = released_queries();
    let suffix = released_suffix();
    let verified = verify_released(host_hashv, suffix, &queries).unwrap();
    let bounds = section_bounds(&verified);

    assert_eq!(verified.bytes_consumed, suffix.len());
    for (section, opening) in openings(&verified).into_iter().enumerate() {
        let section_bytes = &suffix[bounds[section].0..bounds[section].1];
        assert_eq!(opening.offsets.count, 0);
        assert_eq!(opening.offsets.records, 2);
        assert_eq!(opening.offsets.frontier_count, 2 + opening.records.len());
        assert_eq!(opening.offsets.frontier, opening.offsets.frontier_count + 4);
        assert_eq!(opening.offsets.end, section_bytes.len());
        assert_eq!(
            opening.records.len(),
            opening.count * opening.record_width()
        );
        assert_eq!(opening.frontier.len() % 32, 0);
        assert_eq!(
            opening.records.as_ptr(),
            section_bytes.as_ptr().wrapping_add(opening.offsets.records)
        );
        assert_eq!(
            opening.frontier.as_ptr(),
            section_bytes
                .as_ptr()
                .wrapping_add(opening.offsets.frontier)
        );
    }

    assert!(verified
        .indices
        .layer0
        .windows(2)
        .all(|pair| pair[0] < pair[1]));
    for layer in &verified.indices.later {
        assert!(layer.windows(2).all(|pair| pair[0] < pair[1]));
    }

    // Production loop 1: C1/C2 layer zero -> selected slot of line 1.
    let mut line1_ordinal = 0usize;
    for (ordinal, &query) in verified.indices.layer0.iter().enumerate() {
        let c1 = verified.c1.value(ordinal).unwrap();
        let c2 = verified.c2.value(ordinal).unwrap();
        assert_eq!(c1.len(), 256);
        assert_eq!(c2.len(), 192);
        for slot in 0..4 {
            for column in 0..16 {
                let offset = (slot * 16 + column) * 4;
                let encoded: [u8; 4] = c1[offset..offset + 4].try_into().unwrap();
                assert!(M31::from_le_bytes(encoded).is_some());
            }
        }
        for helper in 0..3 {
            for slot in 0..4 {
                let offset = (helper * 4 + slot) * 16;
                assert!(QM31::from_le_bytes(&c2[offset..offset + 16]).is_some());
            }
        }
        let parent = query >> 2;
        let parent_value = monotone_value(
            &verified.later[0],
            &verified.indices.later[0],
            &mut line1_ordinal,
            parent,
        );
        let slot = (query & 3) as usize;
        assert!(QM31::from_le_bytes(&parent_value[slot * 16..(slot + 1) * 16]).is_some());
    }

    // Production loops 2 and 3: line 1 -> line 2 and line 2 -> line 3.
    for layer in 0..2 {
        let mut outgoing_ordinal = 0usize;
        for (ordinal, &index) in verified.indices.later[layer].iter().enumerate() {
            let incoming = verified.later[layer].value(ordinal).unwrap();
            assert_four_qm31_slots_are_canonical(incoming);
            let parent = index >> 2;
            let outgoing = monotone_value(
                &verified.later[layer + 1],
                &verified.indices.later[layer + 1],
                &mut outgoing_ordinal,
                parent,
            );
            assert_four_qm31_slots_are_canonical(outgoing);
            let slot = (index & 3) as usize;
            assert!(QM31::from_le_bytes(&outgoing[slot * 16..(slot + 1) * 16]).is_some());
        }
    }

    // Production loop 4: line 3 -> the final polynomial.
    for ordinal in 0..verified.indices.later[2].len() {
        assert_four_qm31_slots_are_canonical(verified.later[2].value(ordinal).unwrap());
    }
}

#[test]
fn altered_value_salt_or_radix_child_is_rejected() {
    let queries = released_queries();
    let baseline = verify_released(host_hashv, released_suffix(), &queries).unwrap();
    let c1 = &baseline.c1;

    let mut changed_value = released_suffix().to_vec();
    changed_value[c1.offsets.records + 17] ^= 1;
    assert!(verify_released(host_hashv, &changed_value, &queries).is_err());

    let mut changed_salt = released_suffix().to_vec();
    changed_salt[c1.offsets.records + V5_PRIVATE_VALUE_WIDTHS[0] + 9] ^= 1;
    assert!(verify_released(host_hashv, &changed_salt, &queries).is_err());

    assert!(c1.frontier.len() >= 64);
    let mut swapped_children = released_suffix().to_vec();
    for offset in 0..32 {
        swapped_children.swap(
            c1.offsets.frontier + offset,
            c1.offsets.frontier + 32 + offset,
        );
    }
    assert!(verify_released(host_hashv, &swapped_children, &queries).is_err());
}

#[test]
fn wrong_tree_tag_and_wrong_shifted_index_are_rejected() {
    let queries = released_queries();
    let suffix = released_suffix();
    let baseline = verify_released(host_hashv, suffix, &queries).unwrap();
    let bounds = section_bounds(&baseline);
    let topology =
        Radix4BinaryCapTopology::new(V5_PRIVATE_DEPTHS[0], &baseline.indices.layer0).unwrap();
    let mut level = Vec::new();
    let mut next = Vec::new();

    let c1_proof = &suffix[bounds[0].0..bounds[0].1];
    assert!(verify_state_only_private_opening_from_proof_with_topology(
        host_hashv,
        &released_roots().c1,
        V5_PRIVATE_DEPTHS[0],
        V5_PRIVATE_TREE_TAGS[0] ^ 1,
        V5_PRIVATE_VALUE_WIDTHS[0],
        &baseline.indices.layer0,
        c1_proof,
        &topology,
        0,
        &mut level,
        &mut next,
    )
    .is_err());

    let mut wrong_shifted = baseline.indices.later[0].clone();
    let changed = (0..wrong_shifted.len()).find(|&position| {
        let lower_ok = position == 0 || wrong_shifted[position - 1] + 1 < wrong_shifted[position];
        lower_ok && wrong_shifted[position] > 0
    });
    if let Some(position) = changed {
        wrong_shifted[position] -= 1;
    } else {
        let position = wrong_shifted.len() - 1;
        assert!(wrong_shifted[position] + 1 < (1 << V5_PRIVATE_DEPTHS[2]));
        wrong_shifted[position] += 1;
    }
    assert!(wrong_shifted.windows(2).all(|pair| pair[0] < pair[1]));
    let line1_proof = &suffix[bounds[2].0..bounds[2].1];
    assert!(verify_state_only_private_opening_from_proof_with_topology(
        host_hashv,
        &released_roots().later[0],
        V5_PRIVATE_DEPTHS[2],
        V5_PRIVATE_TREE_TAGS[2],
        V5_PRIVATE_VALUE_WIDTHS[2],
        &wrong_shifted,
        line1_proof,
        &topology,
        1,
        &mut level,
        &mut next,
    )
    .is_err());
}

#[test]
fn input_queries_are_sorted_and_deduplicated_before_authentication() {
    let queries = released_queries();
    let baseline = verify_released(host_hashv, released_suffix(), &queries).unwrap();
    let mut reordered = queries.to_vec();
    reordered.reverse();
    reordered.extend_from_slice(&queries[..4]);
    let normalized = verify_released(host_hashv, released_suffix(), &reordered).unwrap();
    assert_eq!(normalized.indices, baseline.indices);
}

#[test]
fn trailing_or_omitted_frontier_material_is_rejected() {
    let queries = released_queries();
    let mut trailing = released_suffix().to_vec();
    trailing.push(0xa5);
    assert!(verify_released(host_hashv, &trailing, &queries).is_err());

    let omitted = &released_suffix()[..released_suffix().len() - 1];
    assert!(verify_released(host_hashv, omitted, &queries).is_err());
}
