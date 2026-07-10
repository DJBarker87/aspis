use anyhow::{ensure, Result};
use serde::Serialize;

use aspis_core::field::{CM31, M31, P, QM31};
use aspis_statement::{
    build_10bit_range_logup_rows, build_logup_helper, derive_nullifier, derive_owner_key,
    evaluate_spend, evaluate_spend_with_range_lookup, forge_post_chi_multiplicities, merkle_root,
    note_commitment, output_commitment, verify_logup_constraints, Digest, EvaluationContext,
    LogUpError, LogUpMainRow, MerklePath, RangeLookupWitness, SpendError, SpendPublic,
    SpendWitness, RANGE_LIMB_BITS, RANGE_LIMB_LIMIT, VALUE_LIMIT,
};

const DEPTH: usize = 20;

#[derive(Serialize)]
pub struct EvaluatorVector {
    pub name: &'static str,
    pub expected: &'static str,
    pub direct_observed: String,
    pub lookup_observed: String,
    pub direct_passed: bool,
    pub lookup_passed: bool,
    pub passed: bool,
}

#[derive(Serialize)]
pub struct LookupAttackVector {
    pub name: &'static str,
    pub expected: String,
    pub observed: String,
    pub passed: bool,
}

#[derive(Serialize)]
pub struct LogUpConstraintVector {
    pub name: &'static str,
    pub expected: String,
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
    pub lookup_attack_vectors: Vec<LookupAttackVector>,
    pub logup_constraint_vectors: Vec<LogUpConstraintVector>,
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
    pub candidate_range_lookup_limb_bits: u32,
    pub candidate_range_lookup_limbs: usize,
    pub candidate_range_reconstruction_terms: usize,
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

fn run_lookup(
    public: &SpendPublic,
    witness: &SpendWitness,
    range_witness: &RangeLookupWitness,
    spent: &[Digest],
) -> Result<(), SpendError> {
    evaluate_spend_with_range_lookup(
        public,
        witness,
        range_witness,
        EvaluationContext {
            merkle_depth: DEPTH,
            spent_nullifiers: spent,
        },
    )
}

fn vector(
    name: &'static str,
    expected: Result<(), SpendError>,
    public: &SpendPublic,
    witness: &SpendWitness,
    spent: &[Digest],
) -> EvaluatorVector {
    let direct_observed = run(public, witness, spent);
    let range_witness = RangeLookupWitness::from_spend(witness);
    let lookup_observed = run_lookup(public, witness, &range_witness, spent);
    let direct_passed = direct_observed == expected;
    // The lookup path can report a lookup-specific error for the same invalid
    // spend. Its accept/reject classification must agree with the oracle.
    let lookup_passed = lookup_observed.is_ok() == expected.is_ok();
    EvaluatorVector {
        name,
        expected: if expected.is_ok() { "accept" } else { "reject" },
        direct_observed: format!("{direct_observed:?}"),
        lookup_observed: format!("{lookup_observed:?}"),
        direct_passed,
        lookup_passed,
        passed: direct_passed && lookup_passed,
    }
}

fn lookup_attack_vector(
    name: &'static str,
    expected: SpendError,
    public: &SpendPublic,
    witness: &SpendWitness,
    range_witness: &RangeLookupWitness,
) -> LookupAttackVector {
    let observed = run_lookup(public, witness, range_witness, &[]);
    LookupAttackVector {
        name,
        expected: format!("Err({expected:?})"),
        observed: format!("{observed:?}"),
        passed: observed == Err(expected),
    }
}

fn logup_vector(
    name: &'static str,
    expected: Result<(), LogUpError>,
    observed: Result<(), LogUpError>,
) -> LogUpConstraintVector {
    LogUpConstraintVector {
        name,
        expected: format!("{expected:?}"),
        observed: format!("{observed:?}"),
        passed: observed == expected,
    }
}

fn require_logup<T>(result: core::result::Result<T, LogUpError>) -> Result<T> {
    result.map_err(|error| anyhow::anyhow!("LogUp fixture construction failed: {error:?}"))
}

pub fn run_evaluator_corpus() -> Result<EvaluatorCorpusSummary> {
    let mut vectors = Vec::new();

    let (public, witness) = fixture(10, 9, 1);
    vectors.push(vector("valid_spend", Ok(()), &public, &witness, &[]));

    let (public, witness) = fixture(1, P - 1, 2);
    vectors.push(vector(
        "field_wrap_inflation",
        Err(SpendError::OutputValueOutOfRange),
        &public,
        &witness,
        &[],
    ));

    let (mut public, witness) = fixture(10, 9, 1);
    public.asset_id = public.asset_id.add(M31::ONE);
    vectors.push(vector(
        "wrong_asset_binding",
        Err(SpendError::AssetMismatch),
        &public,
        &witness,
        &[],
    ));

    let (mut public, witness) = fixture(10, 9, 1);
    public.anchor[0] = public.anchor[0].add(M31::ONE);
    vectors.push(vector(
        "wrong_anchor",
        Err(SpendError::AnchorMismatch),
        &public,
        &witness,
        &[],
    ));

    let (public, mut witness) = fixture(10, 9, 1);
    witness.merkle_path.siblings[3][2] = witness.merkle_path.siblings[3][2].add(M31::ONE);
    vectors.push(vector(
        "wrong_merkle_path",
        Err(SpendError::AnchorMismatch),
        &public,
        &witness,
        &[],
    ));

    let (public, mut witness) = fixture(10, 9, 1);
    witness.nullifier_key[0] = witness.nullifier_key[0].add(M31::ONE);
    vectors.push(vector(
        "forged_ownership_key",
        Err(SpendError::AnchorMismatch),
        &public,
        &witness,
        &[],
    ));

    let (mut public, witness) = fixture(10, 9, 1);
    public.nullifier[0] = public.nullifier[0].add(M31::ONE);
    vectors.push(vector(
        "wrong_nullifier",
        Err(SpendError::NullifierMismatch),
        &public,
        &witness,
        &[],
    ));

    let (mut public, witness) = fixture(10, 9, 1);
    public.output_commitment[0] = public.output_commitment[0].add(M31::ONE);
    vectors.push(vector(
        "wrong_output_commitment",
        Err(SpendError::OutputCommitmentMismatch),
        &public,
        &witness,
        &[],
    ));

    let (public, witness) = fixture(10, 9, 1);
    vectors.push(vector(
        "double_spend_replay",
        Err(SpendError::NullifierAlreadySpent),
        &public,
        &witness,
        &[public.nullifier],
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
        vectors.push(vector(name, Ok(()), &public, &witness, &[]));
    }

    let (public, witness) = fixture(VALUE_LIMIT, 0, 0);
    vectors.push(vector(
        "boundary_value_2pow30",
        Err(SpendError::InputValueOutOfRange),
        &public,
        &witness,
        &[],
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
        &public,
        &witness,
        &[],
    ));

    let (public, witness) = fixture(1_000_000, 999_999, 1);
    let canonical_lookup = RangeLookupWitness::from_spend(&witness);
    let mut non_member = canonical_lookup;
    non_member.input_value_limbs[0] = RANGE_LIMB_LIMIT;
    let mut wrong_reconstruction = canonical_lookup;
    wrong_reconstruction.output_value_limbs[0] ^= 1;
    let lookup_attack_vectors = vec![
        lookup_attack_vector(
            "lookup_limb_1024",
            SpendError::RangeLookupLimbOutOfRange,
            &public,
            &witness,
            &non_member,
        ),
        lookup_attack_vector(
            "lookup_reconstruction_corruption",
            SpendError::RangeLookupReconstructionMismatch,
            &public,
            &witness,
            &wrong_reconstruction,
        ),
    ];

    let chi = QM31 {
        c0: CM31::new(M31(1_234_567), M31(7_654_321)),
        c1: CM31::new(M31(99), M31(101)),
    };
    let honest_rows = require_logup(build_10bit_range_logup_rows(&[0, 1, 1, 17, 511, 1023]))?;
    let honest_helper = require_logup(build_logup_helper(&honest_rows, chi))?;
    let mut corrupted_helper = honest_helper.clone();
    corrupted_helper[17] = corrupted_helper[17].add(QM31::ONE);
    let mut corrupted_multiplicity_rows = honest_rows.clone();
    corrupted_multiplicity_rows[1].consumer_weight =
        corrupted_multiplicity_rows[1].consumer_weight.add(M31::ONE);
    let corrupted_multiplicity_helper =
        require_logup(build_logup_helper(&corrupted_multiplicity_rows, chi))?;

    let lift = |value: u32| QM31::from_cm31(CM31::from_m31(M31(value)));
    let mut unmatched_rows = require_logup(build_10bit_range_logup_rows(&[]))?;
    unmatched_rows[0].producer_value = lift(1024);
    unmatched_rows[0].producer_weight = M31::ONE;
    let unmatched_helper = require_logup(build_logup_helper(&unmatched_rows, chi))?;
    let pole_rows = vec![LogUpMainRow {
        producer_value: lift(5),
        consumer_value: lift(5),
        producer_weight: M31::ONE,
        consumer_weight: M31::ONE,
    }];

    // Order-teeth demonstration: with the multiplicity column chosen AFTER
    // chi, four fractional multiplicities cancel an out-of-table producer
    // and the full constraint set accepts. Expected Ok(()) means the attack
    // succeeds under the weakened order; the canonical order (multiplicity
    // column committed in C1 before chi) is what forbids the construction.
    let mut post_chi_rows = require_logup(build_10bit_range_logup_rows(&[]))?;
    post_chi_rows[0].producer_value = lift(1024);
    post_chi_rows[0].producer_weight = M31::ONE;
    let forged = forge_post_chi_multiplicities(chi, lift(1024))
        .ok_or_else(|| anyhow::anyhow!("post-chi multiplicity solve unexpectedly singular"))?;
    ensure!(
        forged.iter().any(|weight| *weight != M31::ZERO),
        "post-chi forgery degenerated to the honest empty multiset"
    );
    for (row, multiplicity) in forged.into_iter().enumerate() {
        post_chi_rows[row].consumer_weight = multiplicity;
    }
    let post_chi_helper = require_logup(build_logup_helper(&post_chi_rows, chi))?;

    let logup_constraint_vectors = vec![
        logup_vector(
            "logup_honest_range_multiset",
            Ok(()),
            verify_logup_constraints(&honest_rows, &honest_helper, chi),
        ),
        logup_vector(
            "logup_helper_corruption",
            Err(LogUpError::RowRelationMismatch { row: 17 }),
            verify_logup_constraints(&honest_rows, &corrupted_helper, chi),
        ),
        logup_vector(
            "logup_multiplicity_corruption",
            Err(LogUpError::TotalSumMismatch),
            verify_logup_constraints(
                &corrupted_multiplicity_rows,
                &corrupted_multiplicity_helper,
                chi,
            ),
        ),
        logup_vector(
            "logup_nonmember_1024",
            Err(LogUpError::RangeValueOutOfTable {
                query: 0,
                value: 1024,
            }),
            build_10bit_range_logup_rows(&[1024]).map(|_| ()),
        ),
        logup_vector(
            "logup_total_sum_has_teeth",
            Err(LogUpError::TotalSumMismatch),
            verify_logup_constraints(&unmatched_rows, &unmatched_helper, chi),
        ),
        logup_vector(
            "logup_active_pole",
            Err(LogUpError::ActivePole {
                row: 0,
                side: aspis_statement::LogUpSide::Producer,
            }),
            build_logup_helper(&pole_rows, lift(5)).map(|_| ()),
        ),
        logup_vector(
            "logup_multiplicity_after_chi_weakened_order_accepts",
            Ok(()),
            verify_logup_constraints(&post_chi_rows, &post_chi_helper, chi),
        ),
    ];

    ensure!(
        vectors.iter().all(|entry| entry.passed)
            && lookup_attack_vectors.iter().all(|entry| entry.passed)
            && logup_constraint_vectors.iter().all(|entry| entry.passed),
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
            candidate_logup_degree3_terms: 2,
            candidate_range_bit_terms: 0,
            candidate_range_lookup_limb_bits: RANGE_LIMB_BITS,
            candidate_range_lookup_limbs: 6,
            candidate_range_reconstruction_terms: 6,
            zerocheck_eq_variables: 10,
            witness_m31_elements_before_layout_padding: 196,
            public_m31_elements: 26,
        },
        all_vectors_passed: true,
        vectors,
        lookup_attack_vectors,
        logup_constraint_vectors,
        notes: vec![
            "The evaluator proves no statement; it is the executable semantic oracle the future constraints must match.".to_string(),
            "The corpus starts with economic failures: wraparound inflation, public binding, ownership, membership, nullifier replay, output binding, balance, and range boundaries.".to_string(),
            "The lookup evaluator uses six exact 10-bit limbs, checks fixed-table membership, and enforces reconstruction. It is a semantic oracle; the LogUp proof relation is not integrated yet.".to_string(),
            "The LogUp oracle now constructs the post-chi helper, checks the degree-3 local identity, and separately checks sum(h)=0. Its teeth corpus shows that local rows alone do not reject an unmatched nonmember.".to_string(),
            "logup_multiplicity_after_chi_weakened_order_accepts is an attack demonstration: expected Ok means the forged fractional multiplicities defeat every check when the multiplicity column is chosen after chi. The canonical order commits multiplicities in C1 before chi; the vector is the teeth behind that ordering line in the soundness note.".to_string(),
            "The 80-column/4-round row layout is a candidate used to confirm the synthetic composition bracket, not yet a frozen arithmetization.".to_string(),
            "Depth 20 is the explicit demo choice. Moving to depth 32 adds 24 Poseidon2 permutations because each 8+8 digest compression needs two rate-8 sponge permutations.".to_string(),
        ],
    })
}
