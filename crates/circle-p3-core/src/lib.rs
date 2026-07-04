#![no_std]

extern crate alloc;

use alloc::{
    string::{String, ToString},
    vec,
    vec::Vec,
};
use core::marker::PhantomData;

use p3_air::symbolic::{AirLayout, SymbolicAirBuilder};
use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_challenger::{CanObserve, FieldChallenger, HashChallenger, SerializingChallenger32};
use p3_circle::CirclePcs;
use p3_commit::{ExtensionMmcs, Pcs, PolynomialSpace};
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField32};
use p3_fri::FriParameters;
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_mersenne_31::Mersenne31;
use p3_symmetric::{CompressionFunctionFromHasher, MerkleCap, SerializingHasher};
use p3_uni_stark::{
    get_log_num_quotient_chunks, prove, recompose_quotient_from_chunks, validate_degree_bits,
    verify, verify_constraints, InvalidProofShapeError, PcsError, Proof, StarkConfig,
    StarkGenericConfig, VerificationError, VerifierConstraintFolder,
};
use p3_util::checked_log_size_sum;
use serde::{Deserialize, Serialize};
use thiserror::Error;

pub const P3_CIRCLE_REFERENCE_GIT_REV: &str = "0f87f2b543a01880274965c410bf804c124f5046";
pub const P3_CIRCLE_FIXTURE_NAME: &str = "uni_stark_circle_v1.postcard";

pub type CircleVal = Mersenne31;
pub type CircleChallenge = BinomialExtensionField<CircleVal, 3>;
pub type CircleByteHash = p3_keccak::Keccak256Hash;
pub type CircleFieldHash = SerializingHasher<CircleByteHash>;
pub type CircleCompress = CompressionFunctionFromHasher<CircleByteHash, 2, 32>;
pub type CircleValMmcs = MerkleTreeMmcs<CircleVal, u8, CircleFieldHash, CircleCompress, 2, 32>;
pub type CircleChallengeMmcs = ExtensionMmcs<CircleVal, CircleChallenge, CircleValMmcs>;
pub type CircleChallenger =
    SerializingChallenger32<CircleVal, HashChallenger<u8, CircleByteHash, 32>>;
pub type CirclePcsType = CirclePcs<CircleVal, CircleValMmcs, CircleChallengeMmcs>;
pub type CircleConfig = StarkConfig<CirclePcsType, CircleChallenge, CircleChallenger>;
pub type CircleProof = Proof<CircleConfig>;
pub type CircleDigest = [u8; 32];
pub type CircleMerkleCap = MerkleCap<CircleVal, CircleDigest>;
pub type CircleMerkleProof = Vec<CircleDigest>;
const CIRCLE_CHALLENGE_DIMENSION: usize =
    <CircleChallenge as BasedVectorSpace<CircleVal>>::DIMENSION;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct CircleFriConfig {
    pub log_blowup: usize,
    pub log_final_poly_len: usize,
    pub max_log_arity: usize,
    pub num_queries: usize,
    pub commit_proof_of_work_bits: usize,
    pub query_proof_of_work_bits: usize,
}

impl CircleFriConfig {
    pub const fn conjectured_soundness_bits(self) -> usize {
        (self.log_blowup * self.num_queries) + self.query_proof_of_work_bits
    }
}

pub const DEFAULT_CIRCLE_FRI_CONFIG: CircleFriConfig = CircleFriConfig {
    log_blowup: 1,
    log_final_poly_len: 0,
    max_log_arity: 1,
    num_queries: 40,
    commit_proof_of_work_bits: 0,
    query_proof_of_work_bits: 8,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[repr(u8)]
pub enum ScenarioKind {
    Fibonacci8 = 1,
    Square8 = 2,
    AffinePair16 = 3,
    Counter4 = 4,
    Counter8 = 5,
    Counter16 = 6,
}

impl ScenarioKind {
    pub const ALL: [Self; 3] = [Self::Fibonacci8, Self::Square8, Self::AffinePair16];
    pub const PARAMETER_SWEEP: [Self; 3] = [Self::Counter4, Self::Counter8, Self::Counter16];

    pub fn from_tag(tag: u8) -> Option<Self> {
        match tag {
            1 => Some(Self::Fibonacci8),
            2 => Some(Self::Square8),
            3 => Some(Self::AffinePair16),
            4 => Some(Self::Counter4),
            5 => Some(Self::Counter8),
            6 => Some(Self::Counter16),
            _ => None,
        }
    }

    pub const fn tag(self) -> u8 {
        self as u8
    }

    pub const fn slug(self) -> &'static str {
        match self {
            Self::Fibonacci8 => "fibonacci8",
            Self::Square8 => "square8",
            Self::AffinePair16 => "affine-pair16",
            Self::Counter4 => "counter4",
            Self::Counter8 => "counter8",
            Self::Counter16 => "counter16",
        }
    }

    pub const fn title(self) -> &'static str {
        match self {
            Self::Fibonacci8 => "Fibonacci8",
            Self::Square8 => "Square8",
            Self::AffinePair16 => "AffinePair16",
            Self::Counter4 => "Counter4",
            Self::Counter8 => "Counter8",
            Self::Counter16 => "Counter16",
        }
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct ReferenceParameters {
    pub git_rev: &'static str,
    pub fixture_name: &'static str,
    pub base_field: &'static str,
    pub challenge_field: &'static str,
    pub transcript_hash: &'static str,
    pub merkle_hash: &'static str,
    pub fri: CircleFriConfig,
    pub conjectured_soundness_bits: usize,
}

#[derive(Clone, Debug, Serialize)]
pub struct ScenarioMetadata {
    pub kind: ScenarioKind,
    pub name: &'static str,
    pub trace_rows: usize,
    pub trace_width: usize,
    pub constraint_count: usize,
    pub public_value_count: usize,
    pub max_constraint_degree: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum MutationKind {
    QueryResponseBit,
    MerklePathBit,
    TranscriptCommitmentBit,
    FinalPolynomialBit,
}

impl MutationKind {
    pub const ALL: [Self; 4] = [
        Self::QueryResponseBit,
        Self::MerklePathBit,
        Self::TranscriptCommitmentBit,
        Self::FinalPolynomialBit,
    ];

    pub const fn slug(self) -> &'static str {
        match self {
            Self::QueryResponseBit => "query-response-bit",
            Self::MerklePathBit => "merkle-path-bit",
            Self::TranscriptCommitmentBit => "transcript-commitment-bit",
            Self::FinalPolynomialBit => "final-polynomial-bit",
        }
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct ProofSummary {
    pub degree_bits: usize,
    pub proof_bytes: usize,
    pub trace_local_width: usize,
    pub trace_next_width: usize,
    pub quotient_chunk_count: usize,
    pub quotient_chunk_dimension: usize,
    pub has_random_commitment: bool,
    pub trace_commit_cap_roots: usize,
    pub quotient_commit_cap_roots: usize,
    pub first_layer_commit_cap_roots: usize,
    pub lambda_count: usize,
    pub fri_query_count: usize,
    pub fri_commit_phase_rounds: usize,
    pub fri_log_arities: Vec<u8>,
    pub total_input_openings: usize,
    pub total_first_layer_siblings: usize,
    pub total_commit_phase_siblings: usize,
    pub total_merkle_siblings: usize,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MirrorProof {
    pub commitments: MirrorCommitments,
    pub opened_values: MirrorOpenedValues,
    pub opening_proof: MirrorCirclePcsProof,
    pub degree_bits: usize,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MirrorCommitments {
    pub trace: CircleMerkleCap,
    pub quotient_chunks: CircleMerkleCap,
    pub random: Option<CircleMerkleCap>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MirrorOpenedValues {
    pub trace_local: Vec<CircleChallenge>,
    pub trace_next: Option<Vec<CircleChallenge>>,
    pub preprocessed_local: Option<Vec<CircleChallenge>>,
    pub preprocessed_next: Option<Vec<CircleChallenge>>,
    pub quotient_chunks: Vec<Vec<CircleChallenge>>,
    pub random: Option<Vec<CircleChallenge>>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MirrorCirclePcsProof {
    pub first_layer_commitment: CircleMerkleCap,
    pub lambdas: Vec<CircleChallenge>,
    pub fri_proof: MirrorCircleFriProof,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MirrorCircleFriProof {
    pub commit_phase_commits: Vec<CircleMerkleCap>,
    pub query_proofs: Vec<MirrorCircleQueryProof>,
    pub final_poly: CircleChallenge,
    pub pow_witness: CircleVal,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MirrorCircleQueryProof {
    pub input_proof: MirrorCircleInputProof,
    pub commit_phase_openings: Vec<MirrorCircleCommitPhaseProofStep>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MirrorCircleInputProof {
    pub input_openings: Vec<MirrorBatchOpening>,
    pub first_layer_siblings: Vec<CircleChallenge>,
    pub first_layer_proof: CircleMerkleProof,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MirrorBatchOpening {
    pub opened_values: Vec<Vec<CircleVal>>,
    pub opening_proof: CircleMerkleProof,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MirrorCircleCommitPhaseProofStep {
    pub log_arity: u8,
    pub sibling_values: Vec<CircleChallenge>,
    pub opening_proof: CircleMerkleProof,
}

#[derive(Debug, Error)]
pub enum CircleError {
    #[error("invalid scenario tag: {0}")]
    InvalidScenarioTag(u8),
    #[error("proof parse failed: {0}")]
    Parse(postcard::Error),
    #[error("proof serialize failed: {0}")]
    Serialize(postcard::Error),
    #[error("reference verification failed: {0}")]
    ReferenceVerification(String),
    #[error("mirror verification failed: {0}")]
    MirrorVerification(String),
    #[error("mutation failed: {0}")]
    Mutation(&'static str),
}

pub fn reference_parameters() -> ReferenceParameters {
    ReferenceParameters {
        git_rev: P3_CIRCLE_REFERENCE_GIT_REV,
        fixture_name: P3_CIRCLE_FIXTURE_NAME,
        base_field: "M31",
        challenge_field: "M31 cubic extension",
        transcript_hash: "Keccak256",
        merkle_hash: "Keccak256",
        fri: DEFAULT_CIRCLE_FRI_CONFIG,
        conjectured_soundness_bits: DEFAULT_CIRCLE_FRI_CONFIG.conjectured_soundness_bits(),
    }
}

pub fn scenario_metadata(kind: ScenarioKind) -> ScenarioMetadata {
    match kind {
        ScenarioKind::Fibonacci8 => ScenarioMetadata {
            kind,
            name: kind.title(),
            trace_rows: 8,
            trace_width: 2,
            constraint_count: 5,
            public_value_count: 3,
            max_constraint_degree: 2,
        },
        ScenarioKind::Square8 => ScenarioMetadata {
            kind,
            name: kind.title(),
            trace_rows: 8,
            trace_width: 1,
            constraint_count: 3,
            public_value_count: 2,
            max_constraint_degree: 3,
        },
        ScenarioKind::AffinePair16 => ScenarioMetadata {
            kind,
            name: kind.title(),
            trace_rows: 16,
            trace_width: 2,
            constraint_count: 6,
            public_value_count: 4,
            max_constraint_degree: 2,
        },
        ScenarioKind::Counter4 => ScenarioMetadata {
            kind,
            name: kind.title(),
            trace_rows: 4,
            trace_width: 1,
            constraint_count: 3,
            public_value_count: 2,
            max_constraint_degree: 2,
        },
        ScenarioKind::Counter8 => ScenarioMetadata {
            kind,
            name: kind.title(),
            trace_rows: 8,
            trace_width: 1,
            constraint_count: 3,
            public_value_count: 2,
            max_constraint_degree: 2,
        },
        ScenarioKind::Counter16 => ScenarioMetadata {
            kind,
            name: kind.title(),
            trace_rows: 16,
            trace_width: 1,
            constraint_count: 3,
            public_value_count: 2,
            max_constraint_degree: 2,
        },
    }
}

pub fn parse_mirror_proof(bytes: &[u8]) -> Result<MirrorProof, CircleError> {
    postcard::from_bytes(bytes).map_err(CircleError::Parse)
}

pub fn serialize_mirror_proof(proof: &MirrorProof) -> Result<Vec<u8>, CircleError> {
    postcard::to_allocvec(proof).map_err(CircleError::Serialize)
}

pub fn summarize_proof_bytes(bytes: &[u8]) -> Result<ProofSummary, CircleError> {
    let proof = parse_mirror_proof(bytes)?;
    Ok(summarize_proof(&proof, bytes.len()))
}

pub fn reference_prove_scenario(kind: ScenarioKind) -> Result<Vec<u8>, CircleError> {
    reference_prove_scenario_with_fri(kind, DEFAULT_CIRCLE_FRI_CONFIG)
}

pub fn reference_prove_scenario_with_fri(
    kind: ScenarioKind,
    fri: CircleFriConfig,
) -> Result<Vec<u8>, CircleError> {
    let config = make_circle_config(fri);
    let (air, trace, public_values) = scenario_spec(kind);
    let proof = prove(&config, &air, trace, &public_values);
    postcard::to_allocvec(&proof).map_err(CircleError::Serialize)
}

pub fn reference_verify_scenario_bytes(
    kind: ScenarioKind,
    bytes: &[u8],
) -> Result<(), CircleError> {
    reference_verify_scenario_bytes_with_fri(kind, DEFAULT_CIRCLE_FRI_CONFIG, bytes)
}

pub fn reference_verify_scenario_bytes_with_fri(
    kind: ScenarioKind,
    fri: CircleFriConfig,
    bytes: &[u8],
) -> Result<(), CircleError> {
    let config = make_circle_config(fri);
    let (air, _, public_values) = scenario_spec(kind);
    let proof: CircleProof = postcard::from_bytes(bytes).map_err(CircleError::Parse)?;
    verify(&config, &air, &proof, &public_values)
        .map_err(|err| CircleError::ReferenceVerification(err.to_string()))
}

pub fn mirror_verify_scenario_bytes(kind: ScenarioKind, bytes: &[u8]) -> Result<(), CircleError> {
    mirror_verify_scenario_bytes_with_fri(kind, DEFAULT_CIRCLE_FRI_CONFIG, bytes)
}

pub fn mirror_verify_scenario_bytes_with_fri(
    kind: ScenarioKind,
    fri: CircleFriConfig,
    bytes: &[u8],
) -> Result<(), CircleError> {
    let config = make_circle_config(fri);
    let (air, _, public_values) = scenario_spec(kind);
    let proof: CircleProof = postcard::from_bytes(bytes).map_err(CircleError::Parse)?;
    mirror_verify(&config, &air, &proof, &public_values)
        .map_err(|err| CircleError::MirrorVerification(err.to_string()))
}

pub fn mutate_serialized_proof(
    bytes: &[u8],
    mutation: MutationKind,
) -> Result<Vec<u8>, CircleError> {
    let mut proof = parse_mirror_proof(bytes)?;
    mutate_mirror_proof(&mut proof, mutation)?;
    serialize_mirror_proof(&proof)
}

pub fn instruction_data(kind: ScenarioKind, proof_bytes: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(1 + proof_bytes.len());
    out.push(kind.tag());
    out.extend_from_slice(proof_bytes);
    out
}

pub fn parse_instruction_data(data: &[u8]) -> Result<(ScenarioKind, &[u8]), CircleError> {
    let (&tag, rest) = data
        .split_first()
        .ok_or(CircleError::Mutation("instruction data is empty"))?;
    let kind = ScenarioKind::from_tag(tag).ok_or(CircleError::InvalidScenarioTag(tag))?;
    Ok((kind, rest))
}

fn make_circle_config(fri: CircleFriConfig) -> CircleConfig {
    let byte_hash = CircleByteHash {};
    let field_hash = CircleFieldHash::new(byte_hash);
    let compress = CircleCompress::new(byte_hash);
    let val_mmcs = CircleValMmcs::new(field_hash, compress, 0);
    let challenge_mmcs = CircleChallengeMmcs::new(val_mmcs.clone());
    let fri_params = FriParameters {
        log_blowup: fri.log_blowup,
        log_final_poly_len: fri.log_final_poly_len,
        max_log_arity: fri.max_log_arity,
        num_queries: fri.num_queries,
        commit_proof_of_work_bits: fri.commit_proof_of_work_bits,
        query_proof_of_work_bits: fri.query_proof_of_work_bits,
        mmcs: challenge_mmcs,
    };
    let pcs = CirclePcsType {
        mmcs: val_mmcs,
        fri_params,
        _phantom: PhantomData,
    };
    let challenger = CircleChallenger::from_hasher(vec![], byte_hash);
    CircleConfig::new(pcs, challenger)
}

fn scenario_spec(kind: ScenarioKind) -> (ScenarioAir, RowMajorMatrix<CircleVal>, Vec<CircleVal>) {
    match kind {
        ScenarioKind::Fibonacci8 => {
            let trace = fibonacci_trace(8, CircleVal::ZERO, CircleVal::ONE);
            let public_values = vec![CircleVal::ZERO, CircleVal::ONE, trace.values[15]];
            (ScenarioAir::Fibonacci(FibonacciAir), trace, public_values)
        }
        ScenarioKind::Square8 => {
            let seed = CircleVal::from_u64(3);
            let trace = square_trace(8, seed);
            let public_values = vec![seed, trace.values[7]];
            (ScenarioAir::Square(SquareAir), trace, public_values)
        }
        ScenarioKind::AffinePair16 => {
            let start_a = CircleVal::from_u64(2);
            let start_b = CircleVal::from_u64(7);
            let trace = affine_pair_trace(16, start_a, start_b);
            let last_row = (16 - 1) * 2;
            let public_values = vec![
                start_a,
                start_b,
                trace.values[last_row],
                trace.values[last_row + 1],
            ];
            (ScenarioAir::AffinePair(AffinePairAir), trace, public_values)
        }
        ScenarioKind::Counter4 => counter_scenario(4),
        ScenarioKind::Counter8 => counter_scenario(8),
        ScenarioKind::Counter16 => counter_scenario(16),
    }
}

fn summarize_proof(proof: &MirrorProof, proof_bytes: usize) -> ProofSummary {
    let mut fri_log_arities = Vec::new();
    let mut total_input_openings = 0usize;
    let mut total_first_layer_siblings = 0usize;
    let mut total_commit_phase_siblings = 0usize;
    let mut total_merkle_siblings = 0usize;

    for query_proof in &proof.opening_proof.fri_proof.query_proofs {
        total_input_openings += query_proof.input_proof.input_openings.len();
        total_first_layer_siblings += query_proof.input_proof.first_layer_siblings.len();
        total_merkle_siblings += query_proof.input_proof.first_layer_proof.len();
        for batch in &query_proof.input_proof.input_openings {
            total_merkle_siblings += batch.opening_proof.len();
        }
        if fri_log_arities.is_empty() {
            for step in &query_proof.commit_phase_openings {
                fri_log_arities.push(step.log_arity);
            }
        }
        for step in &query_proof.commit_phase_openings {
            total_commit_phase_siblings += step.sibling_values.len();
            total_merkle_siblings += step.opening_proof.len();
        }
    }

    ProofSummary {
        degree_bits: proof.degree_bits,
        proof_bytes,
        trace_local_width: proof.opened_values.trace_local.len(),
        trace_next_width: proof.opened_values.trace_next.as_ref().map_or(0, Vec::len),
        quotient_chunk_count: proof.opened_values.quotient_chunks.len(),
        quotient_chunk_dimension: proof
            .opened_values
            .quotient_chunks
            .first()
            .map_or(0, Vec::len),
        has_random_commitment: proof.commitments.random.is_some(),
        trace_commit_cap_roots: proof.commitments.trace.num_roots(),
        quotient_commit_cap_roots: proof.commitments.quotient_chunks.num_roots(),
        first_layer_commit_cap_roots: proof.opening_proof.first_layer_commitment.num_roots(),
        lambda_count: proof.opening_proof.lambdas.len(),
        fri_query_count: proof.opening_proof.fri_proof.query_proofs.len(),
        fri_commit_phase_rounds: proof.opening_proof.fri_proof.commit_phase_commits.len(),
        fri_log_arities,
        total_input_openings,
        total_first_layer_siblings,
        total_commit_phase_siblings,
        total_merkle_siblings,
    }
}

fn mutate_mirror_proof(proof: &mut MirrorProof, mutation: MutationKind) -> Result<(), CircleError> {
    match mutation {
        MutationKind::QueryResponseBit => {
            let value = proof
                .opened_values
                .trace_local
                .get_mut(0)
                .ok_or(CircleError::Mutation("missing trace_local[0]"))?;
            *value = flip_challenge_bit(*value)?;
        }
        MutationKind::MerklePathBit => {
            if let Some(step) = proof
                .opening_proof
                .fri_proof
                .query_proofs
                .get_mut(0)
                .and_then(|qp| qp.commit_phase_openings.get_mut(0))
                .filter(|step| !step.opening_proof.is_empty())
            {
                step.opening_proof[0][0] ^= 1;
                return Ok(());
            }
            if let Some(proof_bytes) = proof
                .opening_proof
                .fri_proof
                .query_proofs
                .get_mut(0)
                .map(|qp| &mut qp.input_proof.first_layer_proof)
                .filter(|proof_bytes| !proof_bytes.is_empty())
            {
                proof_bytes[0][0] ^= 1;
                return Ok(());
            }
            return Err(CircleError::Mutation("no Merkle path bytes available"));
        }
        MutationKind::TranscriptCommitmentBit => {
            let mut roots = proof.commitments.trace.clone().into_roots();
            let first = roots
                .get_mut(0)
                .ok_or(CircleError::Mutation("empty trace commitment cap"))?;
            first[0] ^= 1;
            proof.commitments.trace = CircleMerkleCap::new(roots);
        }
        MutationKind::FinalPolynomialBit => {
            proof.opening_proof.fri_proof.final_poly =
                flip_challenge_bit(proof.opening_proof.fri_proof.final_poly)?;
        }
    }
    Ok(())
}

fn flip_challenge_bit(value: CircleChallenge) -> Result<CircleChallenge, CircleError> {
    let coeffs = value.as_basis_coefficients_slice();
    if coeffs.len() != 3 {
        return Err(CircleError::Mutation(
            "unexpected challenge basis dimension",
        ));
    }
    let flipped = flip_base_bit(coeffs[0])?;
    Ok(CircleChallenge::new([flipped, coeffs[1], coeffs[2]]))
}

fn flip_base_bit(value: CircleVal) -> Result<CircleVal, CircleError> {
    let raw = value.as_canonical_u32() ^ 1;
    CircleVal::new_checked(raw).ok_or(CircleError::Mutation("invalid base-field bit flip"))
}

fn fibonacci_trace(rows: usize, a0: CircleVal, b0: CircleVal) -> RowMajorMatrix<CircleVal> {
    let mut values = Vec::with_capacity(rows * 2);
    let mut a = a0;
    let mut b = b0;
    for _ in 0..rows {
        values.push(a);
        values.push(b);
        let next_a = b;
        let next_b = a + b;
        a = next_a;
        b = next_b;
    }
    RowMajorMatrix::new(values, 2)
}

fn square_trace(rows: usize, seed: CircleVal) -> RowMajorMatrix<CircleVal> {
    let mut values = Vec::with_capacity(rows);
    let mut current = seed;
    for _ in 0..rows {
        values.push(current);
        current = current * current + CircleVal::ONE;
    }
    RowMajorMatrix::new(values, 1)
}

fn affine_pair_trace(rows: usize, a0: CircleVal, b0: CircleVal) -> RowMajorMatrix<CircleVal> {
    let mut values = Vec::with_capacity(rows * 2);
    let mut a = a0;
    let mut b = b0;
    let five = CircleVal::from_u64(5);
    for _ in 0..rows {
        values.push(a);
        values.push(b);
        let next_a = a + b;
        let next_b = a + b + b + five;
        a = next_a;
        b = next_b;
    }
    RowMajorMatrix::new(values, 2)
}

fn counter_trace(rows: usize, start: CircleVal) -> RowMajorMatrix<CircleVal> {
    let mut values = Vec::with_capacity(rows);
    let mut current = start;
    for _ in 0..rows {
        values.push(current);
        current += CircleVal::ONE;
    }
    RowMajorMatrix::new(values, 1)
}

fn counter_scenario(rows: usize) -> (ScenarioAir, RowMajorMatrix<CircleVal>, Vec<CircleVal>) {
    let start = CircleVal::from_u64(3);
    let trace = counter_trace(rows, start);
    let public_values = vec![start, trace.values[rows - 1]];
    (ScenarioAir::Counter(CounterAir), trace, public_values)
}

#[derive(Clone, Debug)]
enum ScenarioAir {
    Fibonacci(FibonacciAir),
    Square(SquareAir),
    AffinePair(AffinePairAir),
    Counter(CounterAir),
}

#[derive(Clone, Copy, Debug)]
struct FibonacciAir;

#[derive(Clone, Copy, Debug)]
struct SquareAir;

#[derive(Clone, Copy, Debug)]
struct AffinePairAir;

#[derive(Clone, Copy, Debug)]
struct CounterAir;

impl<F> BaseAir<F> for FibonacciAir {
    fn width(&self) -> usize {
        2
    }

    fn num_public_values(&self) -> usize {
        3
    }

    fn num_constraints(&self) -> Option<usize> {
        Some(5)
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        Some(2)
    }
}

impl<AB: AirBuilder<F = CircleVal>> Air<AB> for FibonacciAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        let next = main.next_slice();
        let public = builder.public_values();
        let p0 = public[0];
        let p1 = public[1];
        let p2 = public[2];

        let mut first = builder.when_first_row();
        first.assert_eq(local[0], p0);
        first.assert_eq(local[1], p1);

        let mut transition = builder.when_transition();
        transition.assert_eq(next[0], local[1]);
        transition.assert_eq(next[1], local[0] + local[1]);

        builder.when_last_row().assert_eq(local[1], p2);
    }
}

impl<F> BaseAir<F> for SquareAir {
    fn width(&self) -> usize {
        1
    }

    fn num_public_values(&self) -> usize {
        2
    }

    fn num_constraints(&self) -> Option<usize> {
        Some(3)
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        Some(3)
    }
}

impl<AB: AirBuilder<F = CircleVal>> Air<AB> for SquareAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        let next = main.next_slice();
        let public = builder.public_values();
        let seed = public[0];
        let last = public[1];

        builder.when_first_row().assert_eq(local[0], seed);
        builder
            .when_transition()
            .assert_eq(next[0], local[0] * local[0] + CircleVal::ONE);
        builder.when_last_row().assert_eq(local[0], last);
    }
}

impl<F> BaseAir<F> for AffinePairAir {
    fn width(&self) -> usize {
        2
    }

    fn num_public_values(&self) -> usize {
        4
    }

    fn num_constraints(&self) -> Option<usize> {
        Some(6)
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        Some(2)
    }
}

impl<F> BaseAir<F> for CounterAir {
    fn width(&self) -> usize {
        1
    }

    fn num_public_values(&self) -> usize {
        2
    }

    fn num_constraints(&self) -> Option<usize> {
        Some(3)
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        Some(2)
    }
}

impl<AB: AirBuilder<F = CircleVal>> Air<AB> for CounterAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        let next = main.next_slice();
        let public = builder.public_values();
        let first = public[0];
        let last = public[1];

        builder.when_first_row().assert_eq(local[0], first);
        builder
            .when_transition()
            .assert_eq(next[0], local[0] + CircleVal::ONE);
        builder.when_last_row().assert_eq(local[0], last);
    }
}

impl<AB: AirBuilder<F = CircleVal>> Air<AB> for AffinePairAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        let next = main.next_slice();
        let public = builder.public_values();
        let p0 = public[0];
        let p1 = public[1];
        let p2 = public[2];
        let p3 = public[3];
        let five = AB::Expr::from(CircleVal::from_u64(5));

        let mut first = builder.when_first_row();
        first.assert_eq(local[0], p0);
        first.assert_eq(local[1], p1);

        let mut transition = builder.when_transition();
        transition.assert_eq(next[0], local[0] + local[1]);
        transition.assert_eq(next[1], local[0] + local[1] + local[1] + five);

        let mut last = builder.when_last_row();
        last.assert_eq(local[0], p2);
        last.assert_eq(local[1], p3);
    }
}

impl<F> BaseAir<F> for ScenarioAir {
    fn width(&self) -> usize {
        match self {
            Self::Fibonacci(air) => <FibonacciAir as BaseAir<F>>::width(air),
            Self::Square(air) => <SquareAir as BaseAir<F>>::width(air),
            Self::AffinePair(air) => <AffinePairAir as BaseAir<F>>::width(air),
            Self::Counter(air) => <CounterAir as BaseAir<F>>::width(air),
        }
    }

    fn num_public_values(&self) -> usize {
        match self {
            Self::Fibonacci(air) => <FibonacciAir as BaseAir<F>>::num_public_values(air),
            Self::Square(air) => <SquareAir as BaseAir<F>>::num_public_values(air),
            Self::AffinePair(air) => <AffinePairAir as BaseAir<F>>::num_public_values(air),
            Self::Counter(air) => <CounterAir as BaseAir<F>>::num_public_values(air),
        }
    }

    fn num_constraints(&self) -> Option<usize> {
        match self {
            Self::Fibonacci(air) => <FibonacciAir as BaseAir<F>>::num_constraints(air),
            Self::Square(air) => <SquareAir as BaseAir<F>>::num_constraints(air),
            Self::AffinePair(air) => <AffinePairAir as BaseAir<F>>::num_constraints(air),
            Self::Counter(air) => <CounterAir as BaseAir<F>>::num_constraints(air),
        }
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        match self {
            Self::Fibonacci(air) => <FibonacciAir as BaseAir<F>>::max_constraint_degree(air),
            Self::Square(air) => <SquareAir as BaseAir<F>>::max_constraint_degree(air),
            Self::AffinePair(air) => <AffinePairAir as BaseAir<F>>::max_constraint_degree(air),
            Self::Counter(air) => <CounterAir as BaseAir<F>>::max_constraint_degree(air),
        }
    }
}

impl<AB: AirBuilder<F = CircleVal>> Air<AB> for ScenarioAir {
    fn eval(&self, builder: &mut AB) {
        match self {
            Self::Fibonacci(air) => air.eval(builder),
            Self::Square(air) => air.eval(builder),
            Self::AffinePair(air) => air.eval(builder),
            Self::Counter(air) => air.eval(builder),
        }
    }
}

fn mirror_verify<A>(
    config: &CircleConfig,
    air: &A,
    proof: &CircleProof,
    public_values: &[CircleVal],
) -> Result<(), VerificationError<PcsError<CircleConfig>>>
where
    A: Air<SymbolicAirBuilder<CircleVal>> + for<'a> Air<VerifierConstraintFolder<'a, CircleConfig>>,
{
    let Proof {
        commitments,
        opened_values,
        opening_proof,
        degree_bits,
    } = proof;
    let degree_bits = *degree_bits;
    let pcs = config.pcs();

    let (base_degree_bits, degree) = validate_degree_bits(None, degree_bits, config.is_zk())?;
    let trace_domain =
        <CirclePcsType as Pcs<CircleChallenge, CircleChallenger>>::natural_domain_for_degree(
            pcs, degree,
        );

    if opened_values.preprocessed_local.is_some() || opened_values.preprocessed_next.is_some() {
        return Err(InvalidProofShapeError::UnexpectedPreprocessedValues { air: 0 }.into());
    }

    let layout = AirLayout {
        preprocessed_width: 0,
        main_width: air.width(),
        num_public_values: air.num_public_values(),
        num_periodic_columns: air.num_periodic_columns(),
        ..Default::default()
    };
    let log_num_quotient_chunks =
        get_log_num_quotient_chunks::<CircleVal, A>(air, layout, config.is_zk());
    let (_, num_quotient_chunks) = checked_log_size_sum(log_num_quotient_chunks, config.is_zk())
        .ok_or_else(|| InvalidProofShapeError::QuotientDomainTooLarge {
            air: None,
            maximum: usize::BITS as usize - 1,
            got: log_num_quotient_chunks.saturating_add(config.is_zk()),
        })?;

    if (opened_values.random.is_some()
        != <CirclePcsType as Pcs<CircleChallenge, CircleChallenger>>::ZK)
        || (commitments.random.is_some()
            != <CirclePcsType as Pcs<CircleChallenge, CircleChallenger>>::ZK)
    {
        return Err(VerificationError::RandomizationError);
    }

    let expected_public_values_len = air.num_public_values();
    if public_values.len() != expected_public_values_len {
        return Err(InvalidProofShapeError::PublicValuesLengthMismatch {
            expected: expected_public_values_len,
            got: public_values.len(),
        }
        .into());
    }

    let air_width = air.width();
    let main_next = !air.main_next_row_columns().is_empty();
    let trace_next_ok = if main_next {
        opened_values
            .trace_next
            .as_ref()
            .is_some_and(|values| values.len() == air_width)
    } else {
        opened_values.trace_next.is_none()
    };
    let valid_shape = opened_values.trace_local.len() == air_width
        && trace_next_ok
        && opened_values.quotient_chunks.len() == num_quotient_chunks
        && opened_values
            .quotient_chunks
            .iter()
            .all(|chunk| chunk.len() == CIRCLE_CHALLENGE_DIMENSION)
        && opened_values
            .random
            .as_ref()
            .is_none_or(|values| values.len() == CIRCLE_CHALLENGE_DIMENSION);
    if !valid_shape {
        return Err(InvalidProofShapeError::OpenedValuesDimensionMismatch.into());
    }

    let init_trace_domain =
        <CirclePcsType as Pcs<CircleChallenge, CircleChallenger>>::natural_domain_for_degree(
            pcs,
            degree >> config.is_zk(),
        );
    let (_, quotient_domain_size) = checked_log_size_sum(degree_bits, log_num_quotient_chunks)
        .ok_or_else(|| InvalidProofShapeError::QuotientDomainTooLarge {
            air: None,
            maximum: usize::BITS as usize - 1,
            got: degree_bits.saturating_add(log_num_quotient_chunks),
        })?;
    let quotient_domain = trace_domain.create_disjoint_domain(quotient_domain_size);
    let quotient_chunks_domains = quotient_domain.split_domains(num_quotient_chunks);
    let mut randomized_quotient_chunks_domains = Vec::with_capacity(quotient_chunks_domains.len());
    for domain in &quotient_chunks_domains {
        let randomized_degree = domain.size() << config.is_zk();
        randomized_quotient_chunks_domains.push(<CirclePcsType as Pcs<
            CircleChallenge,
            CircleChallenger,
        >>::natural_domain_for_degree(
            pcs, randomized_degree
        ));
    }

    let mut challenger = config.initialise_challenger();
    challenger.observe(CircleVal::from_usize(degree_bits));
    challenger.observe(CircleVal::from_usize(base_degree_bits));
    challenger.observe(CircleVal::ZERO);
    challenger.observe(commitments.trace.clone());
    challenger.observe_slice(public_values);

    let alpha = challenger.sample_algebra_element();
    challenger.observe(commitments.quotient_chunks.clone());
    let zeta = challenger.sample_algebra_element();
    let periodic_values: Vec<CircleChallenge> = air
        .periodic_columns()
        .iter()
        .map(|periodic_column| init_trace_domain.evaluate_periodic_column_at(periodic_column, zeta))
        .collect();
    let zeta_next = init_trace_domain
        .next_point(zeta)
        .ok_or(VerificationError::NextPointUnavailable)?;

    let mut coms_to_verify = Vec::new();
    let mut trace_points = vec![(zeta, opened_values.trace_local.clone())];
    if main_next {
        trace_points.push((
            zeta_next,
            opened_values
                .trace_next
                .clone()
                .expect("trace_next shape checked above"),
        ));
    }
    coms_to_verify.push((
        commitments.trace.clone(),
        vec![(trace_domain, trace_points)],
    ));

    if randomized_quotient_chunks_domains.len() != opened_values.quotient_chunks.len() {
        return Err(InvalidProofShapeError::QuotientDomainsCountMismatch { air: 0 }.into());
    }
    let mut quotient_round = Vec::with_capacity(opened_values.quotient_chunks.len());
    for (domain, values) in randomized_quotient_chunks_domains
        .iter()
        .zip(opened_values.quotient_chunks.iter())
    {
        let point_values: Vec<CircleChallenge> = values.clone();
        quotient_round.push((*domain, vec![(zeta, point_values)]));
    }
    coms_to_verify.push((commitments.quotient_chunks.clone(), quotient_round));

    pcs.verify(coms_to_verify, opening_proof, &mut challenger)
        .map_err(VerificationError::InvalidOpeningArgument)?;

    let quotient = recompose_quotient_from_chunks::<CircleConfig>(
        &quotient_chunks_domains,
        &opened_values.quotient_chunks,
        zeta,
    );

    let zero_trace_next;
    let trace_next_slice = match &opened_values.trace_next {
        Some(values) => values.as_slice(),
        None => {
            zero_trace_next = vec![CircleChallenge::ZERO; air_width];
            zero_trace_next.as_slice()
        }
    };
    verify_constraints::<CircleConfig, A, PcsError<CircleConfig>>(
        air,
        &opened_values.trace_local,
        trace_next_slice,
        None,
        None,
        &periodic_values,
        public_values,
        init_trace_domain,
        zeta,
        alpha,
        quotient,
    )?;

    Ok(())
}
