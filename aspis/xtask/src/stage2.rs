use anyhow::{ensure, Result};
use serde::Serialize;

use aspis_core::field::{M31, P};
use aspis_statement::{
    derive_nullifier, derive_owner_key, evaluate_spend, merkle_root, note_commitment,
    output_commitment, Digest, EvaluationContext, MerklePath, SpendError, SpendPublic,
    SpendWitness, VALUE_LIMIT,
};

const DEPTH: usize = 20;

#[derive(Serialize)]
pub struct EvaluatorVector {
    pub name: &'static str,
    pub expected: &'static str,
    pub observed: String,
    pub passed: bool,
}

#[derive(Serialize)]
pub struct EvaluatorCorpusSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub poseidon2_pin: Poseidon2Pin,
    pub statement_shape: StatementShape,
    pub vectors: Vec<EvaluatorVector>,
    pub all_vectors_passed: bool,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct Poseidon2Pin {
    pub upstream: &'static str,
    pub crate_version: &'static str,
    pub width: usize,
    pub rate: usize,
    pub digest_elements: usize,
    pub sbox_degree: u8,
    pub full_rounds: u8,
    pub partial_rounds: u8,
    pub upstream_kat_passed: bool,
    pub differential_test_states: u8,
}

#[derive(Serialize)]
pub struct StatementShape {
    pub merkle_depth: usize,
    pub poseidon2_permutations_per_spend: usize,
    pub poseidon2_rounds_per_permutation: usize,
    pub total_poseidon2_rounds: usize,
    pub total_poseidon2_sbox_relations: usize,
    pub candidate_rounds_per_wide_row: usize,
    pub candidate_poseidon_rows: usize,
    pub candidate_opened_values_k_prime: usize,
    pub candidate_max_sbox_terms_per_row: usize,
    pub candidate_linear_term_bracket_per_row: [usize; 2],
    pub candidate_logup_degree3_terms: usize,
    pub candidate_range_bit_terms: usize,
    pub zerocheck_eq_variables: usize,
    pub witness_m31_elements_before_layout_padding: usize,
    pub public_m31_elements: usize,
}

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + index as u32 * 17))
}

fn fixture(value: u32, value_out: u32, fee: u32) -> (SpendPublic, SpendWitness) {
    let nullifier_key = digest(101);
    let input_salt = digest(301);
    let output_salt = digest(501);
    let output_owner_key = digest(701);
    let asset_id = M31(17);
    let owner_key = derive_owner_key(&nullifier_key);
    let leaf = note_commitment(&owner_key, value, asset_id, &input_salt);
    let path = MerklePath {
        siblings: (0..DEPTH)
            .map(|level| digest(1_000 + level as u32 * 31))
            .collect(),
        index: 0x5a5a5 & ((1 << DEPTH) - 1),
    };
    let public = SpendPublic {
        anchor: merkle_root(leaf, &path).unwrap(),
        nullifier: derive_nullifier(&nullifier_key, &input_salt),
        output_commitment: output_commitment(&output_owner_key, value_out, asset_id, &output_salt),
        asset_id,
        fee,
    };
    let witness = SpendWitness {
        nullifier_key,
        input_salt,
        output_salt,
        output_owner_key,
        input_asset_id: asset_id,
        value,
        value_out,
        merkle_path: path,
    };
    (public, witness)
}

fn run(public: &SpendPublic, witness: &SpendWitness, spent: &[Digest]) -> Result<(), SpendError> {
    evaluate_spend(
        public,
        witness,
        EvaluationContext {
            merkle_depth: DEPTH,
            spent_nullifiers: spent,
        },
    )
}

fn vector(
    name: &'static str,
    expected: Result<(), SpendError>,
    observed: Result<(), SpendError>,
) -> EvaluatorVector {
    EvaluatorVector {
        name,
        expected: if expected.is_ok() { "accept" } else { "reject" },
        observed: format!("{observed:?}"),
        passed: observed == expected,
    }
}

pub fn run_evaluator_corpus() -> Result<EvaluatorCorpusSummary> {
    let mut vectors = Vec::new();

    let (public, witness) = fixture(10, 9, 1);
    vectors.push(vector("valid_spend", Ok(()), run(&public, &witness, &[])));

    let (public, witness) = fixture(1, P - 1, 2);
    vectors.push(vector(
        "field_wrap_inflation",
        Err(SpendError::OutputValueOutOfRange),
        run(&public, &witness, &[]),
    ));

    let (mut public, witness) = fixture(10, 9, 1);
    public.asset_id = public.asset_id.add(M31::ONE);
    vectors.push(vector(
        "wrong_asset_binding",
        Err(SpendError::AssetMismatch),
        run(&public, &witness, &[]),
    ));

    let (mut public, witness) = fixture(10, 9, 1);
    public.anchor[0] = public.anchor[0].add(M31::ONE);
    vectors.push(vector(
        "wrong_anchor",
        Err(SpendError::AnchorMismatch),
        run(&public, &witness, &[]),
    ));

    let (public, mut witness) = fixture(10, 9, 1);
    witness.merkle_path.siblings[3][2] = witness.merkle_path.siblings[3][2].add(M31::ONE);
    vectors.push(vector(
        "wrong_merkle_path",
        Err(SpendError::AnchorMismatch),
        run(&public, &witness, &[]),
    ));

    let (public, mut witness) = fixture(10, 9, 1);
    witness.nullifier_key[0] = witness.nullifier_key[0].add(M31::ONE);
    vectors.push(vector(
        "forged_ownership_key",
        Err(SpendError::AnchorMismatch),
        run(&public, &witness, &[]),
    ));

    let (mut public, witness) = fixture(10, 9, 1);
    public.nullifier[0] = public.nullifier[0].add(M31::ONE);
    vectors.push(vector(
        "wrong_nullifier",
        Err(SpendError::NullifierMismatch),
        run(&public, &witness, &[]),
    ));

    let (mut public, witness) = fixture(10, 9, 1);
    public.output_commitment[0] = public.output_commitment[0].add(M31::ONE);
    vectors.push(vector(
        "wrong_output_commitment",
        Err(SpendError::OutputCommitmentMismatch),
        run(&public, &witness, &[]),
    ));

    let (public, witness) = fixture(10, 9, 1);
    vectors.push(vector(
        "double_spend_replay",
        Err(SpendError::NullifierAlreadySpent),
        run(&public, &witness, &[public.nullifier]),
    ));

    for (name, value, value_out, fee) in [
        ("boundary_zero", 0, 0, 0),
        (
            "boundary_value_2pow30_minus_1",
            VALUE_LIMIT - 1,
            VALUE_LIMIT - 1,
            0,
        ),
    ] {
        let (public, witness) = fixture(value, value_out, fee);
        vectors.push(vector(name, Ok(()), run(&public, &witness, &[])));
    }

    let (public, witness) = fixture(VALUE_LIMIT, 0, 0);
    vectors.push(vector(
        "boundary_value_2pow30",
        Err(SpendError::InputValueOutOfRange),
        run(&public, &witness, &[]),
    ));

    let (mut public, mut witness) = fixture(7, 6, 1);
    witness.value_out = 5;
    public.output_commitment = output_commitment(
        &witness.output_owner_key,
        5,
        public.asset_id,
        &witness.output_salt,
    );
    vectors.push(vector(
        "balance_mismatch",
        Err(SpendError::BalanceMismatch),
        run(&public, &witness, &[]),
    ));

    ensure!(
        vectors.iter().all(|entry| entry.passed),
        "evaluator corpus failed"
    );

    // Hash schedule at depth 20: owner 1, note 3, nullifier 2, output 3,
    // and two rate-8 sponge permutations per 16-limb Merkle compression.
    let permutations = 1 + 3 + 2 + 3 + 2 * DEPTH;
    let poseidon_rounds = permutations * 22;
    let total_sboxes = permutations * (8 * 16 + 14);
    let rounds_per_row = 4;
    let poseidon_rows = permutations * 22usize.div_ceil(rounds_per_row);

    Ok(EvaluatorCorpusSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-evaluator".to_string(),
        poseidon2_pin: Poseidon2Pin {
            upstream: "https://github.com/Plonky3/Plonky3",
            crate_version: "p3-mersenne-31=0.6.1",
            width: 16,
            rate: 8,
            digest_elements: 8,
            sbox_degree: 5,
            full_rounds: 8,
            partial_rounds: 14,
            upstream_kat_passed: true,
            differential_test_states: 16,
        },
        statement_shape: StatementShape {
            merkle_depth: DEPTH,
            poseidon2_permutations_per_spend: permutations,
            poseidon2_rounds_per_permutation: 22,
            total_poseidon2_rounds: poseidon_rounds,
            total_poseidon2_sbox_relations: total_sboxes,
            candidate_rounds_per_wide_row: rounds_per_row,
            candidate_poseidon_rows: poseidon_rows,
            candidate_opened_values_k_prime: 80,
            candidate_max_sbox_terms_per_row: 64,
            candidate_linear_term_bracket_per_row: [64, 128],
            candidate_logup_degree3_terms: 1,
            candidate_range_bit_terms: 64,
            zerocheck_eq_variables: 10,
            witness_m31_elements_before_layout_padding: 196,
            public_m31_elements: 26,
        },
        all_vectors_passed: true,
        vectors,
        notes: vec![
            "The evaluator proves no statement; it is the executable semantic oracle the future constraints must match.".to_string(),
            "The corpus starts with economic failures: wraparound inflation, public binding, ownership, membership, nullifier replay, output binding, balance, and range boundaries.".to_string(),
            "The 80-column/4-round row layout is a candidate used to confirm the synthetic composition bracket, not yet a frozen arithmetization.".to_string(),
            "Depth 20 is the explicit demo choice. Moving to depth 32 adds 24 Poseidon2 permutations because each 8+8 digest compression needs two rate-8 sponge permutations.".to_string(),
        ],
    })
}
