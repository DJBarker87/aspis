use anyhow::{bail, Context, Result};
use serde::{Deserialize, Serialize};
use std::{env, fs, path::PathBuf, time::Instant};
use winterfell::{
    crypto::{hashers::Sha3_256, DefaultRandomCoin, MerkleTree},
    math::{fields::f64::BaseElement, FieldElement, ToElements},
    matrix::ColMatrix,
    Air, AirContext, Assertion, AuxRandElements, BatchingMethod, CompositionPoly,
    CompositionPolyTrace, ConstraintCompositionCoefficients, DefaultConstraintCommitment,
    DefaultConstraintEvaluator, DefaultTraceLde, EvaluationFrame, FieldExtension, PartitionOptions,
    ProofOptions, Prover, StarkDomain, TraceInfo, TraceTable, TransitionConstraintDegree,
};

const KECCAK_ROUNDS: usize = 24;
const KECCAK_BITS: usize = 64;
const KECCAK_THETA_ROWS_PER_ROUND: usize = KECCAK_BITS;
const KECCAK_RHO_PI_ROWS_PER_ROUND: usize = KECCAK_BITS;
const KECCAK_CHI_IOTA_ROWS_PER_ROUND: usize = KECCAK_BITS;
const KECCAK_STATE_COLUMNS: usize = 25;
const KECCAK_THETA_C_COLUMNS: usize = 5;
const KECCAK_THETA_D_COLUMNS: usize = 5;
const KECCAK_TRACE_WIDTH: usize =
    KECCAK_STATE_COLUMNS + KECCAK_THETA_C_COLUMNS + KECCAK_THETA_D_COLUMNS;

const N: usize = 256;
const K_44: usize = 4;
const L_44: usize = 4;
const KECCAK_CONSERVATIVE_TOTAL_PERMUTATIONS: usize = 120;
const WINTERFELL_TRACE_WIDTH_CAP: usize = 255;
const YANO_NUM_QUERIES: usize = 30;
const YANO_BLOWUP: usize = 16;
const YANO_GRINDING: u32 = 8;
const YANO_FRI_FOLDING: usize = 4;
const YANO_FRI_REMAINDER_MAX_DEGREE: usize = 31;

#[derive(Deserialize)]
struct ExpandAResults {
    reports: Vec<ExpandAReport>,
}

#[derive(Deserialize)]
struct ExpandAReport {
    parameter_set: String,
    total_shake128_permutations: usize,
}

#[derive(Deserialize)]
struct VerifyHashResults {
    tr_hash: HashReport,
    mu_hash: HashReport,
    ctilde_hash: HashReport,
    sample_in_ball: SampleInBallReport,
}

#[derive(Deserialize)]
struct HashReport {
    total_permutations: usize,
}

#[derive(Deserialize)]
struct SampleInBallReport {
    total_permutations: usize,
}

#[derive(Serialize)]
struct FieldSupportSummary {
    winterfell_trace_width_cap: usize,
    binary_fields_exposed: bool,
    fields: Vec<FieldDescription>,
}

#[derive(Serialize)]
struct FieldDescription {
    name: &'static str,
    modulus: &'static str,
    element_bytes: usize,
    note: &'static str,
}

#[derive(Serialize)]
struct MeasuredShakeTranscript {
    expanda_permutations: usize,
    tr_permutations: usize,
    mu_permutations: usize,
    ctilde_prime_permutations: usize,
    sample_in_ball_permutations: usize,
    exact_total_permutations: usize,
    conservative_total_permutations: usize,
}

#[derive(Serialize)]
struct KeccakAirCandidate {
    field: &'static str,
    trace_width: usize,
    live_columns: KeccakColumns,
    fixed_columns: Vec<&'static str>,
    rows_per_round: KeccakRowsPerRound,
    rows_per_permutation: usize,
    exact_total_active_rows: usize,
    conservative_total_active_rows: usize,
    methodology: &'static str,
}

#[derive(Serialize)]
struct KeccakColumns {
    state_bits: usize,
    theta_c_bits: usize,
    theta_d_bits: usize,
    total: usize,
}

#[derive(Serialize)]
struct KeccakRowsPerRound {
    theta: usize,
    rho_pi: usize,
    chi_iota: usize,
    total: usize,
}

#[derive(Serialize)]
struct ArithmeticSliceModel {
    trace_width_max: usize,
    methodology: &'static str,
    components: Vec<RowComponent>,
    total_rows: usize,
}

#[derive(Serialize)]
struct RowComponent {
    label: &'static str,
    rows: usize,
    rationale: &'static str,
}

#[derive(Serialize)]
struct CombinedProjection {
    exact_total_active_rows: usize,
    exact_padded_trace_length: usize,
    conservative_total_active_rows: usize,
    conservative_padded_trace_length: usize,
    trace_width_max: usize,
    main_trace_query_lower_bound_bytes_f64_q30: usize,
    main_trace_query_lower_bound_bytes_f128_q30: usize,
}

#[derive(Serialize)]
struct ProofProxyResult {
    field: &'static str,
    field_extension: &'static str,
    trace_width: usize,
    trace_length: usize,
    num_queries: usize,
    blowup_factor: usize,
    proof_bytes: usize,
    generation_millis: u128,
    note: &'static str,
}

#[derive(Serialize)]
struct StageBProjectionReport {
    methodology: &'static str,
    field_support: FieldSupportSummary,
    measured_shake_transcript: MeasuredShakeTranscript,
    keccak_air_candidate: KeccakAirCandidate,
    arithmetic_slice_model: ArithmeticSliceModel,
    combined_projection: CombinedProjection,
    proof_proxy: Option<ProofProxyResult>,
}

#[derive(Clone)]
struct ProxyPublicInputs {
    seeds: Vec<BaseElement>,
    incs: Vec<BaseElement>,
}

impl ToElements<BaseElement> for ProxyPublicInputs {
    fn to_elements(&self) -> Vec<BaseElement> {
        let mut out = Vec::with_capacity(self.seeds.len() + self.incs.len());
        out.extend_from_slice(&self.seeds);
        out.extend_from_slice(&self.incs);
        out
    }
}

struct ProxyAir {
    context: AirContext<BaseElement>,
    public_inputs: ProxyPublicInputs,
}

impl ProxyAir {
    fn new_internal(info: TraceInfo, public_inputs: ProxyPublicInputs, options: ProofOptions) -> Self {
        let degrees = vec![TransitionConstraintDegree::new(1); info.width()];
        let num_assertions = info.width() * 2;
        Self {
            context: AirContext::new(info, degrees, num_assertions, options),
            public_inputs,
        }
    }
}

impl Air for ProxyAir {
    type BaseField = BaseElement;
    type PublicInputs = ProxyPublicInputs;

    fn new(info: TraceInfo, public_inputs: Self::PublicInputs, options: ProofOptions) -> Self {
        Self::new_internal(info, public_inputs, options)
    }

    fn context(&self) -> &AirContext<Self::BaseField> {
        &self.context
    }

    fn evaluate_transition<E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        frame: &EvaluationFrame<E>,
        _periodic: &[E],
        result: &mut [E],
    ) {
        for (i, inc) in self.public_inputs.incs.iter().enumerate() {
            result[i] = frame.next()[i] - frame.current()[i] - E::from(*inc);
        }
    }

    fn get_assertions(&self) -> Vec<Assertion<Self::BaseField>> {
        let last = self.trace_length() - 1;
        let mut assertions = Vec::with_capacity(self.public_inputs.seeds.len() * 2);
        for (i, (seed, inc)) in self
            .public_inputs
            .seeds
            .iter()
            .zip(self.public_inputs.incs.iter())
            .enumerate()
        {
            assertions.push(Assertion::single(i, 0, *seed));
            assertions.push(Assertion::single(
                i,
                last,
                *seed + (*inc * BaseElement::new(last as u64)),
            ));
        }
        assertions
    }
}

struct ProxyProver {
    options: ProofOptions,
    public_inputs: ProxyPublicInputs,
}

type H = Sha3_256<BaseElement>;
type VC = MerkleTree<H>;
type RC = DefaultRandomCoin<H>;

impl Prover for ProxyProver {
    type BaseField = BaseElement;
    type Air = ProxyAir;
    type Trace = TraceTable<BaseElement>;

    type HashFn = H;
    type VC = VC;
    type RandomCoin = RC;

    type TraceLde<E: FieldElement<BaseField = BaseElement>> = DefaultTraceLde<E, H, VC>;
    type ConstraintCommitment<E: FieldElement<BaseField = BaseElement>> =
        DefaultConstraintCommitment<E, H, VC>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = BaseElement>> =
        DefaultConstraintEvaluator<'a, ProxyAir, E>;

    fn get_pub_inputs(&self, _trace: &Self::Trace) -> ProxyPublicInputs {
        self.public_inputs.clone()
    }

    fn options(&self) -> &ProofOptions {
        &self.options
    }

    fn new_trace_lde<E: FieldElement<BaseField = BaseElement>>(
        &self,
        info: &TraceInfo,
        main: &ColMatrix<BaseElement>,
        domain: &StarkDomain<BaseElement>,
        partition_options: PartitionOptions,
    ) -> (Self::TraceLde<E>, winterfell::TracePolyTable<E>) {
        DefaultTraceLde::new(info, main, domain, partition_options)
    }

    fn build_constraint_commitment<E: FieldElement<BaseField = BaseElement>>(
        &self,
        composition_poly_trace: CompositionPolyTrace<E>,
        num_constraint_composition_columns: usize,
        domain: &StarkDomain<BaseElement>,
        partition_options: PartitionOptions,
    ) -> (Self::ConstraintCommitment<E>, CompositionPoly<E>) {
        DefaultConstraintCommitment::new(
            composition_poly_trace,
            num_constraint_composition_columns,
            domain,
            partition_options,
        )
    }

    fn new_evaluator<'a, E: FieldElement<BaseField = BaseElement>>(
        &self,
        air: &'a ProxyAir,
        aux_rand_elements: Option<AuxRandElements<E>>,
        composition_coefficients: ConstraintCompositionCoefficients<E>,
    ) -> Self::ConstraintEvaluator<'a, E> {
        DefaultConstraintEvaluator::new(air, aux_rand_elements, composition_coefficients)
    }
}

fn next_power_of_two(value: usize) -> usize {
    value.max(8).next_power_of_two()
}

fn parse_args() -> Result<(PathBuf, bool)> {
    let mut out_path = None;
    let mut skip_proxy = false;
    let mut args = env::args().skip(1);

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--out" => out_path = Some(PathBuf::from(args.next().context("missing value for --out")?)),
            "--skip-proof-proxy" => skip_proxy = true,
            other => bail!("unknown argument: {other}"),
        }
    }

    Ok((
        out_path.unwrap_or_else(|| {
            PathBuf::from("/Users/dominic/ZK/results/mldsa-solana-stark/stage-b-projection.json")
        }),
        skip_proxy,
    ))
}

fn load_measured_transcript(root: &PathBuf) -> Result<MeasuredShakeTranscript> {
    let expanda_path = root.join("results/mldsa-solana-stark/shake-expanda-prototype.json");
    let expanda: ExpandAResults = serde_json::from_slice(
        &fs::read(&expanda_path).with_context(|| format!("reading {}", expanda_path.display()))?,
    )
    .with_context(|| format!("parsing {}", expanda_path.display()))?;
    let expanda_44 = expanda
        .reports
        .iter()
        .find(|report| report.parameter_set == "ML-DSA-44")
        .context("missing ML-DSA-44 ExpandA report")?;

    let verify_path = root.join("results/mldsa-solana-stark/verify-hash-path-prototype.json");
    let verify: VerifyHashResults = serde_json::from_slice(
        &fs::read(&verify_path).with_context(|| format!("reading {}", verify_path.display()))?,
    )
    .with_context(|| format!("parsing {}", verify_path.display()))?;

    Ok(MeasuredShakeTranscript {
        expanda_permutations: expanda_44.total_shake128_permutations,
        tr_permutations: verify.tr_hash.total_permutations,
        mu_permutations: verify.mu_hash.total_permutations,
        ctilde_prime_permutations: verify.ctilde_hash.total_permutations,
        sample_in_ball_permutations: verify.sample_in_ball.total_permutations,
        exact_total_permutations: expanda_44.total_shake128_permutations
            + verify.tr_hash.total_permutations
            + verify.mu_hash.total_permutations
            + verify.ctilde_hash.total_permutations
            + verify.sample_in_ball.total_permutations,
        conservative_total_permutations: KECCAK_CONSERVATIVE_TOTAL_PERMUTATIONS,
    })
}

fn build_keccak_candidate(transcript: &MeasuredShakeTranscript) -> KeccakAirCandidate {
    let rows_per_round = KECCAK_THETA_ROWS_PER_ROUND
        + KECCAK_RHO_PI_ROWS_PER_ROUND
        + KECCAK_CHI_IOTA_ROWS_PER_ROUND;
    let rows_per_permutation = KECCAK_ROUNDS * rows_per_round;

    KeccakAirCandidate {
        field: "winter-math::fields::f64::BaseElement (Goldilocks prime field)",
        trace_width: KECCAK_TRACE_WIDTH,
        live_columns: KeccakColumns {
            state_bits: KECCAK_STATE_COLUMNS,
            theta_c_bits: KECCAK_THETA_C_COLUMNS,
            theta_d_bits: KECCAK_THETA_D_COLUMNS,
            total: KECCAK_TRACE_WIDTH,
        },
        fixed_columns: vec![
            "phase selector",
            "round index selector",
            "bit index selector",
            "rho/pi source-lane mapping",
            "round constant bits for iota",
        ],
        rows_per_round: KeccakRowsPerRound {
            theta: KECCAK_THETA_ROWS_PER_ROUND,
            rho_pi: KECCAK_RHO_PI_ROWS_PER_ROUND,
            chi_iota: KECCAK_CHI_IOTA_ROWS_PER_ROUND,
            total: rows_per_round,
        },
        rows_per_permutation,
        exact_total_active_rows: transcript.exact_total_permutations * rows_per_permutation,
        conservative_total_active_rows: transcript.conservative_total_permutations * rows_per_permutation,
        methodology: "35-column bit-plane candidate. Each row carries one Keccak bit-plane over the 25 state bits; theta uses 5 extra C bits and 5 extra D bits. Current and next rows carry phase input/output so step outputs are not double-counted as extra trace columns. One round is serialized into theta, rho/pi, and chi+iota passes of 64 rows each.",
    }
}

fn build_arithmetic_model() -> ArithmeticSliceModel {
    let components = vec![
        RowComponent {
            label: "pk_decode_t1_materialize",
            rows: K_44 * N,
            rationale: "One row per decoded t1 coefficient.",
        },
        RowComponent {
            label: "sig_decode_z_materialize",
            rows: L_44 * N,
            rationale: "One row per decoded z coefficient.",
        },
        RowComponent {
            label: "sig_decode_hint_materialize",
            rows: K_44 * N,
            rationale: "One row per materialized hint coefficient after HintBitUnpack.",
        },
        RowComponent {
            label: "scale_t1_by_2_pow_d",
            rows: K_44 * N,
            rationale: "One row per t1 coefficient to multiply by 2^d before NTT.",
        },
        RowComponent {
            label: "forward_ntt",
            rows: (L_44 + 1 + K_44) * (N / 2 * 8),
            rationale: "Butterfly count for NTT(z), NTT(c), and NTT(t1 * 2^d).",
        },
        RowComponent {
            label: "ahat_times_ntt_z",
            rows: K_44 * L_44 * N,
            rationale: "One row per pointwise multiply in Ahat o NTT(z).",
        },
        RowComponent {
            label: "ntt_c_times_ntt_t1",
            rows: K_44 * N,
            rationale: "One row per pointwise multiply in NTT(c) o NTT(t1 * 2^d).",
        },
        RowComponent {
            label: "pointwise_accumulate_and_subtract",
            rows: K_44 * N * 4,
            rationale: "Four binary add/sub rows per output coefficient to sum four products and subtract the correction term.",
        },
        RowComponent {
            label: "inverse_ntt",
            rows: K_44 * (N / 2 * 8),
            rationale: "Butterfly count for inverse NTT over k output polynomials.",
        },
        RowComponent {
            label: "use_hint",
            rows: K_44 * N,
            rationale: "One row per coefficient for Decompose/UseHint reconstruction.",
        },
        RowComponent {
            label: "w1_encode",
            rows: K_44 * N,
            rationale: "One row per coefficient to pack w1' for ctilde' hashing.",
        },
        RowComponent {
            label: "z_norm",
            rows: L_44 * N,
            rationale: "One row per z coefficient for the infinity-norm bound check.",
        },
    ];

    let total_rows = components.iter().map(|component| component.rows).sum();

    ArithmeticSliceModel {
        trace_width_max: 12,
        methodology: "Row model for the arithmetic slice of ML-DSA-44 Verify_internal using one row per butterfly or coefficient-local arithmetic relation. This is a Stage B trace-shape model, not yet a proved AIR.",
        components,
        total_rows,
    }
}

fn build_field_support() -> FieldSupportSummary {
    FieldSupportSummary {
        winterfell_trace_width_cap: WINTERFELL_TRACE_WIDTH_CAP,
        binary_fields_exposed: false,
        fields: vec![
            FieldDescription {
                name: "f64",
                modulus: "2^64 - 2^32 + 1",
                element_bytes: std::mem::size_of::<u64>(),
                note: "Goldilocks prime field; Winterfell docs note that a quadratic extension is needed for ~100-bit proof soundness.",
            },
            FieldDescription {
                name: "f62",
                modulus: "2^62 - 111 * 2^39 + 1",
                element_bytes: std::mem::size_of::<u64>(),
                note: "64-bit storage, 62-bit prime field.",
            },
            FieldDescription {
                name: "f128",
                modulus: "2^128 - 45 * 2^40 + 1",
                element_bytes: std::mem::size_of::<u128>(),
                note: "Pinned Yano-derived local prover/verifier field choice.",
            },
        ],
    }
}

fn build_combined_projection(
    keccak: &KeccakAirCandidate,
    arithmetic: &ArithmeticSliceModel,
) -> CombinedProjection {
    let exact_total_active_rows = keccak.exact_total_active_rows + arithmetic.total_rows;
    let conservative_total_active_rows = keccak.conservative_total_active_rows + arithmetic.total_rows;
    let trace_width_max = keccak.trace_width.max(arithmetic.trace_width_max);

    CombinedProjection {
        exact_total_active_rows,
        exact_padded_trace_length: next_power_of_two(exact_total_active_rows),
        conservative_total_active_rows,
        conservative_padded_trace_length: next_power_of_two(conservative_total_active_rows),
        trace_width_max,
        main_trace_query_lower_bound_bytes_f64_q30: trace_width_max
            * std::mem::size_of::<u64>()
            * YANO_NUM_QUERIES,
        main_trace_query_lower_bound_bytes_f128_q30: trace_width_max
            * std::mem::size_of::<u128>()
            * YANO_NUM_QUERIES,
    }
}

fn run_proof_proxy(trace_width: usize, trace_length: usize) -> Result<ProofProxyResult> {
    let seeds = (0..trace_width)
        .map(|index| BaseElement::new((index as u64) + 7))
        .collect::<Vec<_>>();
    let incs = (0..trace_width)
        .map(|index| BaseElement::new((index as u64) + 3))
        .collect::<Vec<_>>();
    let public_inputs = ProxyPublicInputs { seeds, incs };

    let mut trace = TraceTable::new(trace_width, trace_length);
    trace.fill(
        |state| {
            for (index, value) in state.iter_mut().enumerate() {
                *value = public_inputs.seeds[index];
            }
        },
        |_step, state| {
            for (index, value) in state.iter_mut().enumerate() {
                *value += public_inputs.incs[index];
            }
        },
    );

    let options = ProofOptions::new(
        YANO_NUM_QUERIES,
        YANO_BLOWUP,
        YANO_GRINDING,
        FieldExtension::Quadratic,
        YANO_FRI_FOLDING,
        YANO_FRI_REMAINDER_MAX_DEGREE,
        BatchingMethod::Linear,
        BatchingMethod::Linear,
    );

    let prover = ProxyProver {
        options,
        public_inputs,
    };

    let started = Instant::now();
    let proof = prover.prove(trace).context("generating synthetic proof proxy")?;
    let generation_millis = started.elapsed().as_millis();

    Ok(ProofProxyResult {
        field: "f64",
        field_extension: "Quadratic",
        trace_width,
        trace_length,
        num_queries: YANO_NUM_QUERIES,
        blowup_factor: YANO_BLOWUP,
        proof_bytes: proof.to_bytes().len(),
        generation_millis,
        note: "Synthetic affine-copy AIR with the same trace width/length and Yano-mirrored Winterfell proof options except for using the available 256-bit SHA3 hasher in crates.io Winterfell. This is a proof-size proxy, not a proof of ML-DSA verification.",
    })
}

fn main() -> Result<()> {
    let (out_path, skip_proxy) = parse_args()?;
    let root = PathBuf::from("/Users/dominic/ZK");

    let measured_shake_transcript = load_measured_transcript(&root)?;
    let keccak_air_candidate = build_keccak_candidate(&measured_shake_transcript);
    let arithmetic_slice_model = build_arithmetic_model();
    let combined_projection = build_combined_projection(&keccak_air_candidate, &arithmetic_slice_model);
    let proof_proxy = if skip_proxy {
        None
    } else {
        Some(run_proof_proxy(
            combined_projection.trace_width_max,
            combined_projection.exact_padded_trace_length,
        )?)
    };

    let report = StageBProjectionReport {
        methodology: "Stage B projection that combines measured SHAKE permutation counts with a 255-column-compliant Keccak candidate and a row model for the arithmetic slice. Proof bytes come from a synthetic Winterfell proxy AIR at the same width/length and proof options.",
        field_support: build_field_support(),
        measured_shake_transcript,
        keccak_air_candidate,
        arithmetic_slice_model,
        combined_projection,
        proof_proxy,
    };

    let json = serde_json::to_string_pretty(&report)?;
    if let Some(parent) = out_path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(&out_path, &json)?;
    println!("{json}");
    Ok(())
}
