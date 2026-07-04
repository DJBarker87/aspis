use std::{
    any::Any,
    borrow::Cow,
    cell::RefCell,
    panic::{self, AssertUnwindSafe},
    rc::Rc,
    slice,
    time::Instant,
};

use anyhow::{anyhow, bail, Context, Result};
use ark_ff::{AdditiveGroup, BigInteger, Field, PrimeField};
use serde::{Deserialize, Serialize};
use spongefish::StdHash;
use whir::{
    algebra::{
        dot,
        embedding::{Basefield, Embedding, Identity},
        eq_weights,
        fields::{Field64, Field64_3, FieldWithSize},
        geometric_sequence,
        linear_form::{Covector, Evaluate, LinearForm, MultilinearExtension},
        tensor_product,
    },
    bits::Bits,
    hash::{Hash, BLAKE3, ENGINES, HASH_COUNTER},
    parameters::ProtocolParameters,
    protocols::{irs_commit, proof_of_work, sumcheck, whir::FinalClaim},
    transcript::{
        codecs::{Empty, U64},
        Codec, Decoding, DomainSeparator, DuplexSpongeInterface, Proof, ProverMessage, ProverState,
        VerificationError, VerificationResult, VerifierMessage, VerifierState,
    },
    utils::zip_strict,
};

#[cfg(debug_assertions)]
use whir::transcript::Interaction;

pub const OFFICIAL_WHIR_GIT_REV: &str = "0aeaa7f337c743d9ddfcb9d909628d6491e3355c";
pub const OFFICIAL_WHIR_REPO_URL: &str = "https://github.com/WizardOfMenlo/whir";
pub const TARGET_FIELD_MODE: &str = "Goldilocks3";
pub const SOUNDNESS_REGIME: &str = "Johnson-bound list decoding";
pub const MERKLE_HASH_MODE: &str = "Blake3";
pub const POW_HASH_MODE: &str = "Blake3";
pub const TRANSCRIPT_HASH_MODE: &str = "Shake128";
pub const DOMAIN_SEPARATOR_HASH_MODE: &str = "Sha3-256/Sha3-512";

type SourceField = Field64;
type TargetField = Field64_3;
type Goldilocks3Embedding = Basefield<TargetField>;
type Goldilocks3Config = whir::protocols::whir::Config<Goldilocks3Embedding>;

const EMPTY_INSTANCE: Empty = Empty;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum VectorPattern {
    Ascending,
    Affine3x5,
    Quadratic7,
}

impl VectorPattern {
    pub const fn slug(self) -> &'static str {
        match self {
            Self::Ascending => "ascending",
            Self::Affine3x5 => "affine3x5",
            Self::Quadratic7 => "quadratic7",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct ScenarioConfig {
    pub name: String,
    pub security_level: usize,
    pub pow_bits: usize,
    pub num_variables: usize,
    pub evaluations: usize,
    pub linear_constraints: usize,
    pub rate_bits: usize,
    pub initial_folding_factor: usize,
    pub folding_factor: usize,
    pub vector_pattern: VectorPattern,
}

impl ScenarioConfig {
    pub fn slug(&self) -> String {
        format!(
            "{}-t{}-rate{}-d{}-e{}-l{}-i{}-k{}-{}",
            self.name,
            self.security_level,
            rate_slug(self.rate_bits),
            self.num_variables,
            self.evaluations,
            self.linear_constraints,
            self.initial_folding_factor,
            self.folding_factor,
            self.vector_pattern.slug()
        )
    }
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
pub struct ReferenceParameters {
    pub git_rev: &'static str,
    pub repo_url: &'static str,
    pub field_mode: &'static str,
    pub soundness_regime: &'static str,
    pub source_field: &'static str,
    pub target_field: &'static str,
    pub transcript_hash: &'static str,
    pub domain_separator_hash: &'static str,
    pub merkle_hash: &'static str,
    pub pow_hash: &'static str,
}

#[derive(Clone, Debug, Serialize)]
pub struct RoundSchedule {
    pub round_index: usize,
    pub vector_size: usize,
    pub codeword_length: usize,
    pub in_domain_samples: usize,
    pub out_domain_samples: usize,
    pub johnson_slack: f64,
    pub list_size_log2: f64,
    pub query_pow_bits: f64,
    pub sumcheck_pow_bits: f64,
}

#[derive(Clone, Debug, Serialize)]
pub struct ScenarioMetadata {
    pub name: String,
    pub security_target_bits: usize,
    pub achieved_security_bits: f64,
    pub pow_bits_requested: usize,
    pub max_required_pow_bits: f64,
    pub pow_cap_satisfied: bool,
    pub num_variables: usize,
    pub vector_size: usize,
    pub evaluations: usize,
    pub linear_constraints: usize,
    pub rate_bits: usize,
    pub rate: String,
    pub initial_folding_factor: usize,
    pub folding_factor: usize,
    pub source_field_bits: f64,
    pub target_field_bits: f64,
    pub initial_in_domain_samples: usize,
    pub initial_out_domain_samples: usize,
    pub initial_johnson_slack: f64,
    pub initial_codeword_length: usize,
    pub initial_sumcheck_pow_bits: f64,
    pub initial_skip_pow_bits: f64,
    pub round_count: usize,
    pub rounds: Vec<RoundSchedule>,
    pub final_coeff_count: usize,
    pub final_pow_bits: f64,
    pub final_sumcheck_pow_bits: f64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RawProof {
    pub narg_string: Vec<u8>,
    pub hints: Vec<u8>,
    #[cfg(debug_assertions)]
    pub pattern: Vec<Interaction>,
}

impl RawProof {
    fn from_proof(proof: Proof) -> Self {
        Self {
            narg_string: proof.narg_string,
            hints: proof.hints,
            #[cfg(debug_assertions)]
            pattern: proof.pattern,
        }
    }

    fn to_proof(&self) -> Proof {
        Proof {
            narg_string: self.narg_string.clone(),
            hints: self.hints.clone(),
            #[cfg(debug_assertions)]
            pattern: self.pattern.clone(),
        }
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct ProofSummary {
    pub narg_bytes: usize,
    pub hints_bytes: usize,
    pub transcript_bytes: usize,
}

#[derive(Clone, Debug, Serialize)]
pub struct TranscriptIoLog {
    pub absorb_events: Vec<String>,
    pub squeeze_events: Vec<String>,
    pub ratchet_count: usize,
}

#[derive(Clone, Debug, Serialize)]
pub struct VerificationMetrics {
    pub elapsed_ns: u128,
    pub hash_count: u64,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct FinalClaimTrace {
    pub evaluation_point: Vec<String>,
    pub rlc_coefficients: Vec<String>,
    pub linear_form_rlc: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct VerificationRecord {
    pub metrics: VerificationMetrics,
    pub transcript_io: TranscriptIoLog,
    pub final_claim: FinalClaimTrace,
}

#[derive(Clone, Debug, Serialize)]
pub struct ChallengeRlcTrace {
    pub label: String,
    pub count: usize,
    pub generator: Option<String>,
    pub coefficients: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct ReceivedCommitmentTrace {
    pub stage: String,
    pub out_of_domain_points: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct QueryTrace {
    pub stage: String,
    pub codeword_length: usize,
    pub requested_count: usize,
    pub deduplicate: bool,
    pub query_indices: Vec<usize>,
    pub query_points: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct PowTrace {
    pub stage: String,
    pub difficulty_bits: f64,
    pub threshold: u64,
    pub challenge: Option<String>,
    pub nonce: Option<u64>,
    pub skipped: bool,
}

#[derive(Clone, Debug, Serialize)]
pub struct SumcheckTrace {
    pub stage: String,
    pub randomness: Vec<String>,
    pub mask_rlc: String,
}

#[derive(Clone, Debug, Default, Serialize)]
pub struct StructuredTrace {
    pub received_commitments: Vec<ReceivedCommitmentTrace>,
    pub query_openings: Vec<QueryTrace>,
    pub rlc_challenges: Vec<ChallengeRlcTrace>,
    pub pow_checks: Vec<PowTrace>,
    pub sumchecks: Vec<SumcheckTrace>,
    pub final_vector_length: usize,
}

#[derive(Clone, Debug, Serialize)]
pub struct MirrorVerificationRecord {
    pub metrics: VerificationMetrics,
    pub transcript_io: TranscriptIoLog,
    pub final_claim: FinalClaimTrace,
    pub structured_trace: StructuredTrace,
}

#[derive(Clone, Debug, Serialize)]
pub struct TranscriptParity {
    pub absorb_match: bool,
    pub squeeze_match: bool,
    pub ratchet_match: bool,
    pub final_claim_match: bool,
}

#[derive(Clone, Debug, Serialize)]
pub struct ScenarioProbe {
    pub metadata: ScenarioMetadata,
    pub proof_summary: ProofSummary,
    pub raw_proof: RawProof,
    pub reference: VerificationRecord,
    pub mirror: MirrorVerificationRecord,
    pub transcript_parity: TranscriptParity,
}

struct PreparedScenario {
    params: Goldilocks3Config,
    session: String,
    vector: Vec<SourceField>,
    evaluations: Vec<TargetField>,
    prove_forms: Vec<Box<dyn LinearForm<TargetField>>>,
    verify_forms: Vec<Box<dyn LinearForm<TargetField>>>,
}

enum RoundCommitment<'a, F: Field> {
    Initial {
        commitments: &'a [&'a irs_commit::Commitment<F>],
        batching_weights: Vec<F>,
    },
    Round {
        commitment: irs_commit::Commitment<F>,
    },
}

#[derive(Default)]
struct TranscriptRecorder {
    absorb_events: Vec<String>,
    squeeze_events: Vec<String>,
    ratchet_count: usize,
}

impl TranscriptRecorder {
    fn shared() -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Self::default()))
    }

    fn snapshot(&self) -> TranscriptIoLog {
        TranscriptIoLog {
            absorb_events: self.absorb_events.clone(),
            squeeze_events: self.squeeze_events.clone(),
            ratchet_count: self.ratchet_count,
        }
    }
}

#[derive(Clone, Default)]
struct RecordingSponge {
    inner: StdHash,
    recorder: Rc<RefCell<TranscriptRecorder>>,
}

impl RecordingSponge {
    fn new(recorder: Rc<RefCell<TranscriptRecorder>>) -> Self {
        Self {
            inner: StdHash::default(),
            recorder,
        }
    }
}

impl DuplexSpongeInterface for RecordingSponge {
    type U = u8;

    fn absorb(&mut self, input: &[u8]) -> &mut Self {
        self.recorder
            .borrow_mut()
            .absorb_events
            .push(hex_bytes(input));
        self.inner.absorb(input);
        self
    }

    fn squeeze(&mut self, output: &mut [u8]) -> &mut Self {
        self.inner.squeeze(output);
        self.recorder
            .borrow_mut()
            .squeeze_events
            .push(hex_bytes(output));
        self
    }

    fn ratchet(&mut self) -> &mut Self {
        self.recorder.borrow_mut().ratchet_count += 1;
        self.inner.ratchet();
        self
    }
}

pub fn reference_parameters() -> ReferenceParameters {
    ReferenceParameters {
        git_rev: OFFICIAL_WHIR_GIT_REV,
        repo_url: OFFICIAL_WHIR_REPO_URL,
        field_mode: TARGET_FIELD_MODE,
        soundness_regime: SOUNDNESS_REGIME,
        source_field: "Goldilocks (64-bit)",
        target_field: "Goldilocks cubic extension (192-bit)",
        transcript_hash: TRANSCRIPT_HASH_MODE,
        domain_separator_hash: DOMAIN_SEPARATOR_HASH_MODE,
        merkle_hash: MERKLE_HASH_MODE,
        pow_hash: POW_HASH_MODE,
    }
}

pub fn scenario_metadata(config: &ScenarioConfig) -> Result<ScenarioMetadata> {
    let params = build_params(config)?;
    let rounds = params
        .round_configs
        .iter()
        .enumerate()
        .map(|(round_index, round)| RoundSchedule {
            round_index,
            vector_size: round.initial_size(),
            codeword_length: round.irs_committer.codeword_length,
            in_domain_samples: round.irs_committer.in_domain_samples,
            out_domain_samples: round.irs_committer.out_domain_samples,
            johnson_slack: round.irs_committer.johnson_slack.into_inner(),
            list_size_log2: round.irs_committer.list_size().log2(),
            query_pow_bits: f64::from(round.pow.difficulty()),
            sumcheck_pow_bits: f64::from(round.sumcheck.round_pow.difficulty()),
        })
        .collect::<Vec<_>>();
    Ok(ScenarioMetadata {
        name: config.name.clone(),
        security_target_bits: config.security_level,
        achieved_security_bits: params
            .security_level(1, config.evaluations + config.linear_constraints),
        pow_bits_requested: config.pow_bits,
        max_required_pow_bits: max_required_pow_bits(&params),
        pow_cap_satisfied: params.check_max_pow_bits(Bits::new(config.pow_bits as f64)),
        num_variables: config.num_variables,
        vector_size: 1usize << config.num_variables,
        evaluations: config.evaluations,
        linear_constraints: config.linear_constraints,
        rate_bits: config.rate_bits,
        rate: format!("1/{}", 1usize << config.rate_bits),
        initial_folding_factor: config.initial_folding_factor,
        folding_factor: config.folding_factor,
        source_field_bits: SourceField::field_size_bits(),
        target_field_bits: TargetField::field_size_bits(),
        initial_in_domain_samples: params.initial_committer.in_domain_samples,
        initial_out_domain_samples: params.initial_committer.out_domain_samples,
        initial_johnson_slack: params.initial_committer.johnson_slack.into_inner(),
        initial_codeword_length: params.initial_committer.codeword_length,
        initial_sumcheck_pow_bits: f64::from(params.initial_sumcheck.round_pow.difficulty()),
        initial_skip_pow_bits: f64::from(params.initial_skip_pow.difficulty()),
        round_count: params.round_configs.len(),
        rounds,
        final_coeff_count: params.final_sumcheck.initial_size,
        final_pow_bits: f64::from(params.final_pow.difficulty()),
        final_sumcheck_pow_bits: f64::from(params.final_sumcheck.round_pow.difficulty()),
    })
}

pub fn summarize_raw_proof(raw_proof: &RawProof) -> ProofSummary {
    ProofSummary {
        narg_bytes: raw_proof.narg_string.len(),
        hints_bytes: raw_proof.hints.len(),
        transcript_bytes: raw_proof.narg_string.len() + raw_proof.hints.len(),
    }
}

pub fn reference_prove_scenario(config: &ScenarioConfig) -> Result<RawProof> {
    let prepared = build_scenario(config)?;
    let ds = domain_separator(&prepared.params, &prepared.session);
    let mut prover_state = ProverState::new_std(&ds);
    let witness = prepared
        .params
        .commit(&mut prover_state, &[prepared.vector.as_slice()]);
    let _ = prepared.params.prove(
        &mut prover_state,
        vec![Cow::Borrowed(prepared.vector.as_slice())],
        vec![Cow::Owned(witness)],
        prepared.prove_forms,
        Cow::Borrowed(prepared.evaluations.as_slice()),
    );
    Ok(RawProof::from_proof(prover_state.proof()))
}

pub fn reference_verify_scenario(
    config: &ScenarioConfig,
    raw_proof: &RawProof,
) -> Result<VerificationRecord> {
    catch_rejection(|| reference_verify_inner(config, raw_proof))
}

pub fn mirror_verify_scenario(
    config: &ScenarioConfig,
    raw_proof: &RawProof,
) -> Result<MirrorVerificationRecord> {
    catch_rejection(|| mirror_verify_inner(config, raw_proof))
}

pub fn probe_valid_scenario(config: &ScenarioConfig) -> Result<ScenarioProbe> {
    let metadata = scenario_metadata(config)?;
    let raw_proof = reference_prove_scenario(config)?;
    let proof_summary = summarize_raw_proof(&raw_proof);
    let reference = reference_verify_scenario(config, &raw_proof)?;
    let mirror = mirror_verify_scenario(config, &raw_proof)?;
    let transcript_parity = TranscriptParity {
        absorb_match: reference.transcript_io.absorb_events == mirror.transcript_io.absorb_events,
        squeeze_match: reference.transcript_io.squeeze_events
            == mirror.transcript_io.squeeze_events,
        ratchet_match: reference.transcript_io.ratchet_count == mirror.transcript_io.ratchet_count,
        final_claim_match: reference.final_claim == mirror.final_claim,
    };
    Ok(ScenarioProbe {
        metadata,
        proof_summary,
        raw_proof,
        reference,
        mirror,
        transcript_parity,
    })
}

pub fn mutate_raw_proof(raw_proof: &RawProof, kind: MutationKind) -> Result<RawProof> {
    let mut mutated = raw_proof.clone();
    match kind {
        MutationKind::QueryResponseBit => flip_first_byte(&mut mutated.hints)
            .context("query-response mutation requires a non-empty hint stream")?,
        MutationKind::MerklePathBit => flip_last_byte(&mut mutated.hints)
            .context("merkle-path mutation requires a non-empty hint stream")?,
        MutationKind::TranscriptCommitmentBit => flip_first_byte(&mut mutated.narg_string)
            .context("transcript-commitment mutation requires a non-empty narg stream")?,
        MutationKind::FinalPolynomialBit => {
            let offset = final_polynomial_proxy_offset(mutated.narg_string.len());
            flip_byte_at(&mut mutated.narg_string, offset)
                .context("final-polynomial mutation requires a non-empty narg stream")?;
        }
    }
    Ok(mutated)
}

pub fn current_hash_mode() -> String {
    ENGINES
        .retrieve(BLAKE3)
        .map(|engine| engine.name().to_string())
        .unwrap_or_else(|| MERKLE_HASH_MODE.to_string())
}

fn reference_verify_inner(
    config: &ScenarioConfig,
    raw_proof: &RawProof,
) -> Result<VerificationRecord> {
    let prepared = build_scenario(config)?;
    let proof = raw_proof.to_proof();
    let ds = domain_separator(&prepared.params, &prepared.session);
    let recorder = TranscriptRecorder::shared();
    HASH_COUNTER.reset();
    let started = Instant::now();
    let mut verifier_state =
        VerifierState::new(&ds, &proof, RecordingSponge::new(recorder.clone()));
    let commitment = prepared
        .params
        .receive_commitment(&mut verifier_state)
        .map_err(|_| anyhow!("reference receive_commitment rejected"))?;
    let final_claim = prepared
        .params
        .verify(&mut verifier_state, &[&commitment], &prepared.evaluations)
        .map_err(|_| anyhow!("reference verifier rejected"))?;
    final_claim
        .verify(
            prepared
                .verify_forms
                .iter()
                .map(|form| form.as_ref() as &dyn LinearForm<TargetField>),
        )
        .map_err(|_| anyhow!("reference final linear-form check rejected"))?;
    let transcript_io = recorder.borrow().snapshot();
    Ok(VerificationRecord {
        metrics: VerificationMetrics {
            elapsed_ns: started.elapsed().as_nanos(),
            hash_count: HASH_COUNTER.get() as u64,
        },
        transcript_io,
        final_claim: final_claim_trace(&final_claim),
    })
}

fn mirror_verify_inner(
    config: &ScenarioConfig,
    raw_proof: &RawProof,
) -> Result<MirrorVerificationRecord> {
    let prepared = build_scenario(config)?;
    let proof = raw_proof.to_proof();
    let ds = domain_separator(&prepared.params, &prepared.session);
    let recorder = TranscriptRecorder::shared();
    HASH_COUNTER.reset();
    let started = Instant::now();
    let mut verifier_state =
        VerifierState::new(&ds, &proof, RecordingSponge::new(recorder.clone()));
    let commitment = prepared
        .params
        .receive_commitment(&mut verifier_state)
        .map_err(|_| anyhow!("mirror receive_commitment rejected"))?;
    let (final_claim, structured_trace) = mirror_verify_config_with_trace(
        &prepared.params,
        &mut verifier_state,
        &[&commitment],
        &prepared.evaluations,
    )
    .map_err(|_| anyhow!("mirror verifier rejected"))?;
    final_claim
        .verify(
            prepared
                .verify_forms
                .iter()
                .map(|form| form.as_ref() as &dyn LinearForm<TargetField>),
        )
        .map_err(|_| anyhow!("mirror final linear-form check rejected"))?;
    let transcript_io = recorder.borrow().snapshot();
    Ok(MirrorVerificationRecord {
        metrics: VerificationMetrics {
            elapsed_ns: started.elapsed().as_nanos(),
            hash_count: HASH_COUNTER.get() as u64,
        },
        transcript_io,
        final_claim: final_claim_trace(&final_claim),
        structured_trace,
    })
}

fn build_params(config: &ScenarioConfig) -> Result<Goldilocks3Config> {
    let whir_params = ProtocolParameters {
        unique_decoding: false,
        security_level: config.security_level,
        pow_bits: config.pow_bits,
        initial_folding_factor: config.initial_folding_factor,
        folding_factor: config.folding_factor,
        starting_log_inv_rate: config.rate_bits,
        batch_size: 1,
        hash_id: BLAKE3,
    };
    Ok(Goldilocks3Config::new(
        1usize << config.num_variables,
        &whir_params,
    ))
}

fn build_scenario(config: &ScenarioConfig) -> Result<PreparedScenario> {
    let params = build_params(config)?;
    let num_coeffs = 1usize << config.num_variables;
    let vector = build_vector(config.vector_pattern, num_coeffs);
    let mut evaluations = Vec::with_capacity(config.evaluations + config.linear_constraints);
    let mut prove_forms: Vec<Box<dyn LinearForm<TargetField>>> =
        Vec::with_capacity(config.evaluations + config.linear_constraints);
    let mut verify_forms: Vec<Box<dyn LinearForm<TargetField>>> =
        Vec::with_capacity(config.evaluations + config.linear_constraints);

    for index in 0..config.linear_constraints {
        let coeffs = build_covector(config.vector_pattern, index, num_coeffs);
        let verify_form = Covector {
            vector: coeffs.clone(),
        };
        evaluations.push(verify_form.evaluate(params.embedding(), &vector));
        prove_forms.push(Box::new(Covector { vector: coeffs }));
        verify_forms.push(Box::new(verify_form));
    }

    for index in 0..config.evaluations {
        let point = build_point(config.vector_pattern, index, config.num_variables);
        let verify_form = MultilinearExtension::new(point.clone());
        evaluations.push(verify_form.evaluate(params.embedding(), &vector));
        prove_forms.push(Box::new(MultilinearExtension::new(point.clone())));
        verify_forms.push(Box::new(verify_form));
    }

    Ok(PreparedScenario {
        params,
        session: format!("whir-jb-parity/{}", config.slug()),
        vector,
        evaluations,
        prove_forms,
        verify_forms,
    })
}

fn build_vector(pattern: VectorPattern, len: usize) -> Vec<SourceField> {
    (0..len)
        .map(|index| {
            let value = match pattern {
                VectorPattern::Ascending => index as u64,
                VectorPattern::Affine3x5 => 3 * index as u64 + 5,
                VectorPattern::Quadratic7 => {
                    let idx = index as u64;
                    idx.saturating_mul(idx).wrapping_add(7)
                }
            };
            SourceField::from(value)
        })
        .collect()
}

fn build_covector(pattern: VectorPattern, offset: usize, len: usize) -> Vec<TargetField> {
    (0..len)
        .map(|index| {
            let base = index as u64 + offset as u64 + 1;
            let value = match pattern {
                VectorPattern::Ascending => base,
                VectorPattern::Affine3x5 => 5 * base + 3,
                VectorPattern::Quadratic7 => base.saturating_mul(base).wrapping_add(11),
            };
            TargetField::from(value)
        })
        .collect()
}

fn build_point(
    pattern: VectorPattern,
    point_index: usize,
    num_variables: usize,
) -> Vec<TargetField> {
    (0..num_variables)
        .map(|coord| {
            let value = match pattern {
                VectorPattern::Ascending => (point_index + coord + 1) as u64,
                VectorPattern::Affine3x5 => (3 * (point_index + 1) + 5 * (coord + 1)) as u64,
                VectorPattern::Quadratic7 => {
                    let seed = (point_index + coord + 2) as u64;
                    seed.saturating_mul(seed).wrapping_add(7)
                }
            };
            TargetField::from(value)
        })
        .collect()
}

fn domain_separator<'a>(
    params: &'a Goldilocks3Config,
    session: &'a str,
) -> DomainSeparator<'a, Empty> {
    DomainSeparator::protocol(params)
        .session(&session)
        .instance(&EMPTY_INSTANCE)
}

fn mirror_verify_config_with_trace<M, H>(
    params: &whir::protocols::whir::Config<M>,
    verifier_state: &mut VerifierState<'_, H>,
    commitments: &[&whir::protocols::whir::Commitment<M::Target>],
    evaluations: &[M::Target],
) -> VerificationResult<(FinalClaim<M::Target>, StructuredTrace)>
where
    H: DuplexSpongeInterface,
    M: Embedding,
    M::Source: Field,
    M::Target: Codec<[H::U]>,
    u8: Decoding<[H::U]>,
    [u8; 32]: Decoding<[H::U]>,
    U64: Codec<[H::U]>,
    Hash: ProverMessage<[H::U]>,
{
    let mut trace = StructuredTrace::default();
    for (index, commitment) in commitments.iter().enumerate() {
        record_received_commitment(
            format!("initial_commitment_{index}"),
            commitment,
            &mut trace,
        );
    }

    let num_vectors = commitments.len() * params.initial_committer.num_vectors;
    ensure_verification(evaluations.len().is_multiple_of(num_vectors))?;
    let num_linear_forms = evaluations.len() / num_vectors;
    if num_vectors == 0 {
        return Ok((FinalClaim::default(), trace));
    }

    let (oods_evals, oods_matrix) = {
        let mut oods_evals = Vec::new();
        let mut oods_matrix = Vec::new();
        let mut vector_offset = 0;
        for commitment in commitments {
            for (weights, oods_row) in zip_strict(
                commitment.out_of_domain().evaluators(params.initial_size()),
                commitment.out_of_domain().rows(),
            ) {
                for j in 0..num_vectors {
                    if j >= vector_offset && j < oods_row.len() + vector_offset {
                        oods_matrix.push(oods_row[j - vector_offset]);
                    } else {
                        oods_matrix.push(verifier_state.prover_message()?);
                    }
                }
                oods_evals.push(weights);
            }
            vector_offset += commitment.num_vectors();
        }
        (oods_evals, oods_matrix)
    };

    let vector_rlc_coeffs = geometric_challenge_with_trace(
        verifier_state,
        num_vectors,
        "initial_vector_rlc",
        &mut trace,
    );
    let mut prev_commitment = RoundCommitment::Initial {
        commitments,
        batching_weights: vector_rlc_coeffs.clone(),
    };

    let constraint_rlc_coeffs: Vec<M::Target> = geometric_challenge_with_trace(
        verifier_state,
        oods_evals.len() + num_linear_forms,
        "initial_constraint_rlc",
        &mut trace,
    );
    let (initial_form_rlc_coeffs, oods_rlc_coeffs) =
        constraint_rlc_coeffs.split_at(num_linear_forms);

    let mut the_sum = zip_strict(
        initial_form_rlc_coeffs,
        evaluations.chunks_exact(num_vectors),
    )
    .map(|(poly_coeff, row)| *poly_coeff * dot(&vector_rlc_coeffs, row))
    .sum::<M::Target>();
    the_sum += zip_strict(oods_rlc_coeffs, oods_matrix.chunks_exact(num_vectors))
        .map(|(poly_coeff, row)| *poly_coeff * dot(&vector_rlc_coeffs, row))
        .sum::<M::Target>();
    let mut round_constraints = vec![(oods_rlc_coeffs.to_vec(), oods_evals)];
    let mut round_folding_randomness = Vec::new();

    let folding_randomness = if constraint_rlc_coeffs.is_empty() {
        ensure_verification(the_sum == M::Target::ZERO)?;
        let folding_randomness =
            verifier_state.verifier_message_vec(params.initial_sumcheck.num_rounds);
        trace.sumchecks.push(SumcheckTrace {
            stage: "initial_skip_sumcheck".to_string(),
            randomness: field_vec_hex(&folding_randomness),
            mask_rlc: field_hex(M::Target::ONE),
        });
        proof_of_work_verify_with_trace(
            "initial_skip_pow",
            &params.initial_skip_pow,
            verifier_state,
            &mut trace,
        )?;
        folding_randomness
    } else {
        sumcheck_verify_with_trace(
            "initial_sumcheck",
            &params.initial_sumcheck,
            verifier_state,
            &mut the_sum,
            &mut trace,
        )?
        .0
    };
    round_folding_randomness.push(folding_randomness);

    for (round_index, round_config) in params.round_configs.iter().enumerate() {
        let commitment = round_config
            .irs_committer
            .receive_commitment(verifier_state)?;
        record_received_commitment(
            format!("round_{round_index}_commitment"),
            &commitment,
            &mut trace,
        );

        proof_of_work_verify_with_trace(
            format!("round_{round_index}_pow"),
            &round_config.pow,
            verifier_state,
            &mut trace,
        )?;

        let (in_domain, poly_rlc) = match prev_commitment {
            RoundCommitment::Initial {
                commitments,
                batching_weights,
            } => {
                let in_domain = params
                    .initial_committer
                    .verify(verifier_state, commitments)?;
                record_query_trace(
                    format!("round_{round_index}_open_initial"),
                    &params.initial_committer,
                    &in_domain,
                    &mut trace,
                )?;
                (in_domain.lift(params.embedding()), batching_weights)
            }
            RoundCommitment::Round { commitment } => {
                let prev_round_config = &params.round_configs[round_index - 1];
                let in_domain = prev_round_config
                    .irs_committer
                    .verify(verifier_state, &[&commitment])?;
                record_query_trace(
                    format!("round_{round_index}_open_round_{}", round_index - 1),
                    &prev_round_config.irs_committer,
                    &in_domain,
                    &mut trace,
                )?;
                (in_domain, vec![M::Target::ONE])
            }
        };

        let constraint_weights = commitment
            .out_of_domain()
            .evaluators(round_config.initial_size())
            .chain(in_domain.evaluators(round_config.initial_size()))
            .collect::<Vec<_>>();
        let constraint_values = commitment
            .out_of_domain()
            .values(&[M::Target::ONE])
            .chain(in_domain.values(&tensor_product(
                &poly_rlc,
                &eq_weights(round_folding_randomness.last().unwrap()),
            )))
            .collect::<Vec<_>>();
        let constraint_rlc_coeffs = geometric_challenge_with_trace(
            verifier_state,
            constraint_values.len(),
            format!("round_{round_index}_constraint_rlc"),
            &mut trace,
        );
        the_sum += dot(&constraint_rlc_coeffs, &constraint_values);
        round_constraints.push((constraint_rlc_coeffs, constraint_weights));

        let folding_randomness = sumcheck_verify_with_trace(
            format!("round_{round_index}_sumcheck"),
            &round_config.sumcheck,
            verifier_state,
            &mut the_sum,
            &mut trace,
        )?
        .0;
        round_folding_randomness.push(folding_randomness);

        prev_commitment = RoundCommitment::Round { commitment };
    }

    let final_vector = verifier_state.prover_messages_vec(params.final_sumcheck.initial_size)?;
    trace.final_vector_length = final_vector.len();

    proof_of_work_verify_with_trace("final_pow", &params.final_pow, verifier_state, &mut trace)?;

    let (in_domain, poly_rlc) = match prev_commitment {
        RoundCommitment::Initial {
            commitments,
            batching_weights,
        } => {
            let in_domain = params
                .initial_committer
                .verify(verifier_state, commitments)?;
            record_query_trace(
                "final_open_initial",
                &params.initial_committer,
                &in_domain,
                &mut trace,
            )?;
            (in_domain.lift(params.embedding()), batching_weights)
        }
        RoundCommitment::Round { commitment } => {
            let prev_round_config = params.round_configs.last().unwrap();
            let in_domain = prev_round_config
                .irs_committer
                .verify(verifier_state, &[&commitment])?;
            record_query_trace(
                "final_open_last_round",
                &prev_round_config.irs_committer,
                &in_domain,
                &mut trace,
            )?;
            (in_domain, vec![M::Target::ONE])
        }
    };

    for (weights, evals) in zip_strict(
        in_domain.evaluators(final_vector.len()),
        in_domain.values(&tensor_product(
            &poly_rlc,
            &eq_weights(round_folding_randomness.last().unwrap()),
        )),
    ) {
        ensure_verification(
            weights.evaluate(&Identity::<M::Target>::new(), &final_vector) == evals,
        )?;
    }

    let final_sumcheck_randomness = sumcheck_verify_with_trace(
        "final_sumcheck",
        &params.final_sumcheck,
        verifier_state,
        &mut the_sum,
        &mut trace,
    )?
    .0;
    round_folding_randomness.push(final_sumcheck_randomness.clone());

    let evaluation_point = round_folding_randomness
        .into_iter()
        .flat_map(|poly| poly.into_iter())
        .collect::<Vec<_>>();

    let poly_eval = MultilinearExtension::new(final_sumcheck_randomness)
        .evaluate(&Identity::new(), &final_vector);
    let mut linear_form_rlc = the_sum / poly_eval;

    for (round, (weights_rlc_coeffs, weights)) in round_constraints.into_iter().enumerate() {
        let num_variables = round.checked_sub(1).map_or_else(
            || params.initial_num_variables(),
            |prev| params.round_configs[prev].initial_num_variables(),
        );
        let start = evaluation_point.len().saturating_sub(num_variables);
        for (rlc_coeff, weights) in zip_strict(weights_rlc_coeffs, weights) {
            linear_form_rlc -= rlc_coeff * weights.mle_evaluate(&evaluation_point[start..]);
        }
    }

    Ok((
        FinalClaim {
            evaluation_point,
            rlc_coefficients: initial_form_rlc_coeffs.to_vec(),
            linear_form_rlc,
        },
        trace,
    ))
}

fn record_received_commitment<G: Field>(
    stage: impl Into<String>,
    commitment: &irs_commit::Commitment<G>,
    trace: &mut StructuredTrace,
) {
    trace.received_commitments.push(ReceivedCommitmentTrace {
        stage: stage.into(),
        out_of_domain_points: field_vec_hex(&commitment.out_of_domain().points),
    });
}

fn record_query_trace<M>(
    stage: impl Into<String>,
    config: &irs_commit::Config<M>,
    evaluations: &irs_commit::Evaluations<M::Source>,
    trace: &mut StructuredTrace,
) -> VerificationResult<()>
where
    M: Embedding,
    M::Source: Field,
{
    let query_indices =
        recover_query_indices(config, &evaluations.points).map_err(|_| VerificationError)?;
    trace.query_openings.push(QueryTrace {
        stage: stage.into(),
        codeword_length: config.codeword_length,
        requested_count: config.in_domain_samples,
        deduplicate: config.deduplicate_in_domain,
        query_indices,
        query_points: field_vec_hex(&evaluations.points),
    });
    Ok(())
}

fn recover_query_indices<M>(
    config: &irs_commit::Config<M>,
    points: &[M::Source],
) -> Result<Vec<usize>>
where
    M: Embedding,
    M::Source: Field,
{
    if points.is_empty() {
        return Ok(Vec::new());
    }
    let all_indices = (0..config.codeword_length).collect::<Vec<_>>();
    let all_points = config.evaluation_points(&all_indices);
    points
        .iter()
        .map(|target| {
            all_points
                .iter()
                .position(|candidate| candidate == target)
                .ok_or_else(|| anyhow!("failed to recover query index from evaluation point"))
        })
        .collect()
}

fn geometric_challenge_with_trace<T, F>(
    transcript: &mut T,
    count: usize,
    label: impl Into<String>,
    trace: &mut StructuredTrace,
) -> Vec<F>
where
    T: VerifierMessage,
    F: Field + Decoding<[T::U]>,
{
    let label = label.into();
    match count {
        0 => {
            trace.rlc_challenges.push(ChallengeRlcTrace {
                label,
                count,
                generator: None,
                coefficients: Vec::new(),
            });
            Vec::new()
        }
        1 => {
            let coefficients = vec![F::ONE];
            trace.rlc_challenges.push(ChallengeRlcTrace {
                label,
                count,
                generator: None,
                coefficients: field_vec_hex(&coefficients),
            });
            coefficients
        }
        _ => {
            let generator = transcript.verifier_message::<F>();
            let coefficients = geometric_sequence(generator, count);
            trace.rlc_challenges.push(ChallengeRlcTrace {
                label,
                count,
                generator: Some(field_hex(generator)),
                coefficients: field_vec_hex(&coefficients),
            });
            coefficients
        }
    }
}

fn sumcheck_verify_with_trace<H, F>(
    stage: impl Into<String>,
    config: &sumcheck::Config<F>,
    verifier_state: &mut VerifierState<'_, H>,
    sum: &mut F,
    trace: &mut StructuredTrace,
) -> VerificationResult<(Vec<F>, F)>
where
    H: DuplexSpongeInterface,
    F: Field + Codec<[H::U]>,
    [u8; 32]: Decoding<[H::U]>,
    U64: Codec<[H::U]>,
{
    let stage = stage.into();
    let mut mask_rlc = F::ONE;
    if config.mask_length > 0 && config.num_rounds > 0 {
        let mask_sum: F = verifier_state.prover_message()?;
        mask_rlc = verifier_state.verifier_message();
        *sum = mask_sum + mask_rlc * *sum;
    }

    let mut univariate = vec![F::ZERO; config.mask_length.max(3)];
    let mut randomness = Vec::with_capacity(config.num_rounds);
    for round in 0..config.num_rounds {
        univariate[0] = verifier_state.prover_message()?;
        for coefficient in &mut univariate[2..] {
            *coefficient = verifier_state.prover_message()?;
        }
        univariate[1] = *sum - univariate[0].double() - univariate[2..].iter().sum::<F>();

        proof_of_work_verify_with_trace(
            format!("{stage}/round_{round}_pow"),
            &config.round_pow,
            verifier_state,
            trace,
        )?;

        let folding_randomness = verifier_state.verifier_message::<F>();
        randomness.push(folding_randomness);
        *sum = whir::algebra::univariate_evaluate(&univariate, folding_randomness);
    }

    trace.sumchecks.push(SumcheckTrace {
        stage,
        randomness: field_vec_hex(&randomness),
        mask_rlc: field_hex(mask_rlc),
    });
    Ok((randomness, mask_rlc))
}

fn proof_of_work_verify_with_trace<H>(
    stage: impl Into<String>,
    config: &proof_of_work::Config,
    verifier_state: &mut VerifierState<'_, H>,
    trace: &mut StructuredTrace,
) -> VerificationResult<()>
where
    H: DuplexSpongeInterface,
    [u8; 32]: Decoding<[H::U]>,
    U64: Codec<[H::U]>,
{
    let stage = stage.into();
    if config.threshold == u64::MAX {
        trace.pow_checks.push(PowTrace {
            stage,
            difficulty_bits: f64::from(config.difficulty()),
            threshold: config.threshold,
            challenge: None,
            nonce: None,
            skipped: true,
        });
        return Ok(());
    }

    let engine = ENGINES.retrieve(config.hash_id);
    ensure_verification(engine.is_some())?;
    let engine = engine.unwrap();
    let challenge: [u8; 32] = verifier_state.verifier_message();
    let nonce: U64 = verifier_state.prover_message()?;

    let mut input = [0u8; 64];
    input[..32].copy_from_slice(&challenge);
    input[32..40].copy_from_slice(&nonce.0.to_le_bytes());
    let mut output = Hash::default();
    engine.hash_many(64, &input, slice::from_mut(&mut output));
    let value = u64::from_le_bytes(output.0[..8].try_into().unwrap());
    ensure_verification(value <= config.threshold)?;

    trace.pow_checks.push(PowTrace {
        stage,
        difficulty_bits: f64::from(config.difficulty()),
        threshold: config.threshold,
        challenge: Some(hex_bytes(&challenge)),
        nonce: Some(nonce.0),
        skipped: false,
    });
    Ok(())
}

fn final_claim_trace<F: Field>(final_claim: &FinalClaim<F>) -> FinalClaimTrace {
    FinalClaimTrace {
        evaluation_point: field_vec_hex(&final_claim.evaluation_point),
        rlc_coefficients: field_vec_hex(&final_claim.rlc_coefficients),
        linear_form_rlc: field_hex(final_claim.linear_form_rlc),
    }
}

fn field_vec_hex<F: Field>(values: &[F]) -> Vec<String> {
    values.iter().map(|value| field_hex(*value)).collect()
}

fn field_hex<F: Field>(value: F) -> String {
    let base_bytes = (F::BasePrimeField::MODULUS_BIT_SIZE as usize).div_ceil(8);
    let mut out = Vec::with_capacity(base_bytes * F::extension_degree() as usize);
    for coefficient in value.to_base_prime_field_elements() {
        let mut bytes = coefficient.into_bigint().to_bytes_le();
        bytes.resize(base_bytes, 0);
        bytes.truncate(base_bytes);
        out.extend_from_slice(&bytes);
    }
    hex_bytes(&out)
}

fn hex_bytes(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(nibble_to_hex(byte >> 4));
        out.push(nibble_to_hex(byte & 0x0f));
    }
    out
}

fn nibble_to_hex(nibble: u8) -> char {
    match nibble {
        0..=9 => (b'0' + nibble) as char,
        10..=15 => (b'a' + (nibble - 10)) as char,
        _ => unreachable!(),
    }
}

fn catch_rejection<T, F>(f: F) -> Result<T>
where
    F: FnOnce() -> Result<T>,
{
    match panic::catch_unwind(AssertUnwindSafe(f)) {
        Ok(result) => result,
        Err(payload) => Err(anyhow!(
            "panic during verification: {}",
            panic_message(payload)
        )),
    }
}

fn panic_message(payload: Box<dyn Any + Send>) -> String {
    if let Some(message) = payload.downcast_ref::<&str>() {
        (*message).to_string()
    } else if let Some(message) = payload.downcast_ref::<String>() {
        message.clone()
    } else {
        "non-string panic payload".to_string()
    }
}

fn flip_first_byte(bytes: &mut [u8]) -> Result<()> {
    let Some(first) = bytes.first_mut() else {
        bail!("buffer was empty");
    };
    *first ^= 1;
    Ok(())
}

fn flip_last_byte(bytes: &mut [u8]) -> Result<()> {
    let Some(last) = bytes.last_mut() else {
        bail!("buffer was empty");
    };
    *last ^= 1;
    Ok(())
}

fn flip_byte_at(bytes: &mut [u8], index: usize) -> Result<()> {
    let Some(target) = bytes.get_mut(index) else {
        bail!("buffer was empty or index out of range");
    };
    *target ^= 1;
    Ok(())
}

fn final_polynomial_proxy_offset(len: usize) -> usize {
    if len > 96 {
        len - 96
    } else {
        len / 2
    }
}

fn max_required_pow_bits(params: &Goldilocks3Config) -> f64 {
    let mut max_bits = f64::from(params.initial_sumcheck.round_pow.difficulty());
    max_bits = max_bits.max(f64::from(params.initial_skip_pow.difficulty()));
    for round in &params.round_configs {
        max_bits = max_bits.max(f64::from(round.pow.difficulty()));
        max_bits = max_bits.max(f64::from(round.sumcheck.round_pow.difficulty()));
    }
    max_bits = max_bits.max(f64::from(params.final_pow.difficulty()));
    max_bits.max(f64::from(params.final_sumcheck.round_pow.difficulty()))
}

fn rate_slug(rate_bits: usize) -> String {
    format!("1over{}", 1usize << rate_bits)
}

fn ensure_verification(condition: bool) -> VerificationResult<()> {
    if condition {
        Ok(())
    } else {
        Err(VerificationError)
    }
}
