use aspis_core::field::M31;
use aspis_statement::{
    insertion_root, verify_output_insertion, AtomicStatementError, Digest,
    ATOMIC_PAYMENT_EMPTY_LEAF, ATOMIC_PAYMENT_TREE_DEPTH, STATE_ONLY_POSEIDON_BLOCK_ROWS,
    STATE_ONLY_POSEIDON_TRACE_ROWS,
};

/// The complete atomic statement has four logically independent hash
/// families.  In particular, spent-note membership cannot double as the
/// append-position non-membership proof: their leaves and, in general, their
/// authentication paths are different.
const NON_PATH_PERMUTATIONS: usize = 1 + 3 + 2 + 3;
const SPENT_MEMBERSHIP_PERMUTATIONS: usize = ATOMIC_PAYMENT_TREE_DEPTH;
const EMPTY_INSERTION_PERMUTATIONS: usize = ATOMIC_PAYMENT_TREE_DEPTH;
const OUTPUT_INSERTION_PERMUTATIONS: usize = ATOMIC_PAYMENT_TREE_DEPTH;
const COMPLETE_ATOMIC_PERMUTATIONS: usize = NON_PATH_PERMUTATIONS
    + SPENT_MEMBERSHIP_PERMUTATIONS
    + EMPTY_INSERTION_PERMUTATIONS
    + OUTPUT_INSERTION_PERMUTATIONS;

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + 17 * index as u32))
}

fn siblings(seed: u32) -> [Digest; ATOMIC_PAYMENT_TREE_DEPTH] {
    core::array::from_fn(|level| digest(seed + 31 * level as u32))
}

#[test]
fn complete_public_append_does_not_fit_the_aligned_1024_row_layout() {
    assert_eq!(NON_PATH_PERMUTATIONS, 9);
    assert_eq!(COMPLETE_ATOMIC_PERMUTATIONS, 69);
    assert_eq!(STATE_ONLY_POSEIDON_BLOCK_ROWS, 16);
    assert_eq!(STATE_ONLY_POSEIDON_TRACE_ROWS, 1_024);

    let required_rows = COMPLETE_ATOMIC_PERMUTATIONS * STATE_ONLY_POSEIDON_BLOCK_ROWS;
    let aligned_capacity = STATE_ONLY_POSEIDON_TRACE_ROWS / STATE_ONLY_POSEIDON_BLOCK_ROWS;
    assert_eq!(required_rows, 1_104);
    assert_eq!(aligned_capacity, 64);
    assert!(COMPLETE_ATOMIC_PERMUTATIONS > aligned_capacity);
    assert_eq!(required_rows - STATE_ONLY_POSEIDON_TRACE_ROWS, 80);
}

#[test]
fn the_existing_two_path_shape_cannot_substitute_spent_membership_for_empty_insertion() {
    let path = siblings(1_000);
    let private_spent_leaf = digest(7_001);
    let sequence = 0x5_a5a5;
    let spent_root = insertion_root(private_spent_leaf, sequence, &path).unwrap();
    let empty_root = insertion_root(ATOMIC_PAYMENT_EMPTY_LEAF, sequence, &path).unwrap();

    assert_ne!(private_spent_leaf, ATOMIC_PAYMENT_EMPTY_LEAF);
    assert_ne!(spent_root, empty_root);
}

#[test]
fn every_public_sequence_bit_has_an_independent_rejecting_tooth() {
    let path = siblings(2_000);
    let output = digest(9_001);
    let sequence = 0x5_a5a5;
    let current = insertion_root(ATOMIC_PAYMENT_EMPTY_LEAF, sequence, &path).unwrap();
    let next = insertion_root(output, sequence, &path).unwrap();
    verify_output_insertion(&current, &output, &next, sequence, &path).unwrap();

    for bit in 0..ATOMIC_PAYMENT_TREE_DEPTH {
        let changed = sequence ^ (1 << bit);
        assert!(matches!(
            verify_output_insertion(&current, &output, &next, changed, &path),
            Err(AtomicStatementError::CurrentAnchorMismatch)
                | Err(AtomicStatementError::OutputAnchorMismatch)
        ));
    }
}

#[test]
fn every_private_append_sibling_and_the_output_leaf_are_bound() {
    let path = siblings(3_000);
    let output = digest(11_001);
    let sequence = 73;
    let current = insertion_root(ATOMIC_PAYMENT_EMPTY_LEAF, sequence, &path).unwrap();
    let next = insertion_root(output, sequence, &path).unwrap();

    for level in 0..ATOMIC_PAYMENT_TREE_DEPTH {
        let mut changed = path;
        changed[level][level % changed[level].len()] =
            changed[level][level % changed[level].len()].add(M31::ONE);
        assert!(verify_output_insertion(&current, &output, &next, sequence, &changed).is_err());
    }

    let mut changed_output = output;
    changed_output[0] = changed_output[0].add(M31::ONE);
    assert_eq!(
        verify_output_insertion(&current, &changed_output, &next, sequence, &path),
        Err(AtomicStatementError::OutputAnchorMismatch)
    );
}

#[test]
fn independently_supplied_empty_and_output_paths_cannot_diverge() {
    let path = siblings(4_000);
    let output = digest(13_001);
    let sequence = 511;
    let current = insertion_root(ATOMIC_PAYMENT_EMPTY_LEAF, sequence, &path).unwrap();
    let next = insertion_root(output, sequence, &path).unwrap();

    let mut output_only_path = path;
    output_only_path[7][3] = output_only_path[7][3].add(M31::ONE);
    // This is the exact seam a complete copy registry must close: checking
    // the two equations with different sibling vectors is not an append.
    assert_ne!(
        insertion_root(output, sequence, &output_only_path).unwrap(),
        next
    );
    verify_output_insertion(&current, &output, &next, sequence, &path).unwrap();
}
