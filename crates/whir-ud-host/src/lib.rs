use std::{
    any::Any,
    borrow::Cow,
    panic::{self, AssertUnwindSafe},
    time::Instant,
};

use anyhow::{anyhow, bail, Context, Result};
use ark_ff::{AdditiveGroup, Field};
use serde::{Deserialize, Serialize};
use whir::{
    algebra::{
        dot,
        embedding::{Basefield, Embedding, Identity},
        eq_weights,
        fields::{Field64, Field64_2, FieldWithSize},
        linear_form::{Covector, Evaluate, LinearForm, MultilinearExtension},
        tensor_product,
    },
    bits::Bits,
    hash::{Hash, BLAKE3, ENGINES, HASH_COUNTER},
    parameters::ProtocolParameters,
    protocols::{geometric_challenge::geometric_challenge, irs_commit, whir::FinalClaim},
    transcript::{
        codecs::{Empty, U64},
        Codec, Decoding, DomainSeparator, DuplexSpongeInterface, Proof, ProverMessage, ProverState,
        VerificationResult, VerifierMessage, VerifierState,
    },
    utils::zip_strict,
};

pub const OFFICIAL_WHIR_GIT_REV: &str = "0aeaa7f337c743d9ddfcb9d909628d6491e3355c";
pub const OFFICIAL_WHIR_REPO_URL: &str = "https://github.com/WizardOfMenlo/whir";
pub const TARGET_FIELD_MODE: &str = "Goldilocks2";
pub const MERKLE_HASH_MODE: &str = "Blake3";
pub const POW_HASH_MODE: &str = "Blake3";
pub const TRANSCRIPT_HASH_MODE: &str = "Shake128";
pub const DOMAIN_SEPARATOR_HASH_MODE: &str = "Sha3-256/Sha3-512";

type SourceField = Field64;
type TargetField = Field64_2;
type Goldilocks2Embedding = Basefield<TargetField>;
type Goldilocks2Config = whir::protocols::whir::Config<Goldilocks2Embedding>;

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
    pub unique_decoding: bool,
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
    pub source_field: &'static str,
    pub target_field: &'static str,
    pub transcript_hash: &'static str,
    pub domain_separator_hash: &'static str,
    pub merkle_hash: &'static str,
    pub pow_hash: &'static str,
    pub unique_decoding: bool,
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
    pub unique_decoding: bool,
    pub source_field_bits: f64,
    pub target_field_bits: f64,
    pub initial_in_domain_samples: usize,
    pub round_count: usize,
    pub final_coeff_count: usize,
}

#[derive(Clone, Debug, Serialize)]
pub struct ProofSummary {
    pub serialized_bytes: usize,
    pub narg_bytes: usize,
    pub hints_bytes: usize,
    pub transcript_bytes: usize,
}

#[derive(Clone, Debug, Serialize)]
pub struct VerificationMetrics {
    pub elapsed_ns: u128,
    pub hash_count: u64,
}

#[derive(Clone, Debug, Serialize)]
pub struct ScenarioProbe {
    pub metadata: ScenarioMetadata,
    pub proof_summary: ProofSummary,
    pub proof_bytes: Vec<u8>,
    pub reference: VerificationMetrics,
    pub mirror: VerificationMetrics,
}

struct PreparedScenario {
    params: Goldilocks2Config,
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

pub fn reference_parameters() -> ReferenceParameters {
    ReferenceParameters {
        git_rev: OFFICIAL_WHIR_GIT_REV,
        repo_url: OFFICIAL_WHIR_REPO_URL,
        field_mode: TARGET_FIELD_MODE,
        source_field: "Goldilocks (64-bit)",
        target_field: "Goldilocks quadratic extension (128-bit)",
        transcript_hash: TRANSCRIPT_HASH_MODE,
        domain_separator_hash: DOMAIN_SEPARATOR_HASH_MODE,
        merkle_hash: MERKLE_HASH_MODE,
        pow_hash: POW_HASH_MODE,
        unique_decoding: true,
    }
}

pub fn scenario_metadata(config: &ScenarioConfig) -> Result<ScenarioMetadata> {
    let params = build_params(config)?;
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
        unique_decoding: config.unique_decoding,
        source_field_bits: SourceField::field_size_bits(),
        target_field_bits: TargetField::field_size_bits(),
        initial_in_domain_samples: params.initial_committer.in_domain_samples,
        round_count: params.round_configs.len(),
        final_coeff_count: params.final_sumcheck.initial_size,
    })
}

pub fn summarize_proof_bytes(bytes: &[u8]) -> Result<ProofSummary> {
    let proof = deserialize_proof(bytes)?;
    Ok(ProofSummary {
        serialized_bytes: bytes.len(),
        narg_bytes: proof.narg_string.len(),
        hints_bytes: proof.hints.len(),
        transcript_bytes: proof.narg_string.len() + proof.hints.len(),
    })
}

pub fn reference_prove_scenario(config: &ScenarioConfig) -> Result<Vec<u8>> {
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
    serialize_proof(&prover_state.proof())
}

pub fn reference_verify_scenario_bytes(
    config: &ScenarioConfig,
    bytes: &[u8],
) -> Result<VerificationMetrics> {
    catch_rejection(|| reference_verify_inner(config, bytes))
}

pub fn mirror_verify_scenario_bytes(
    config: &ScenarioConfig,
    bytes: &[u8],
) -> Result<VerificationMetrics> {
    catch_rejection(|| mirror_verify_inner(config, bytes))
}

pub fn probe_valid_scenario(config: &ScenarioConfig) -> Result<ScenarioProbe> {
    let metadata = scenario_metadata(config)?;
    let proof_bytes = reference_prove_scenario(config)?;
    let proof_summary = summarize_proof_bytes(&proof_bytes)?;
    let reference = reference_verify_scenario_bytes(config, &proof_bytes)?;
    let mirror = mirror_verify_scenario_bytes(config, &proof_bytes)?;
    Ok(ScenarioProbe {
        metadata,
        proof_summary,
        proof_bytes,
        reference,
        mirror,
    })
}

pub fn mutate_serialized_proof(bytes: &[u8], kind: MutationKind) -> Result<Vec<u8>> {
    let mut proof = deserialize_proof(bytes)?;
    match kind {
        MutationKind::QueryResponseBit => flip_first_byte(&mut proof.hints)
            .context("query-response proxy mutation requires a non-empty hint stream")?,
        MutationKind::MerklePathBit => flip_last_byte(&mut proof.hints)
            .context("merkle-path proxy mutation requires a non-empty hint stream")?,
        MutationKind::TranscriptCommitmentBit => flip_first_byte(&mut proof.narg_string)
            .context("transcript-commitment mutation requires a non-empty transcript stream")?,
        MutationKind::FinalPolynomialBit => {
            let offset = final_polynomial_proxy_offset(proof.narg_string.len());
            flip_byte_at(&mut proof.narg_string, offset)
                .context("final-polynomial proxy mutation requires a non-empty transcript stream")?
        }
    }
    serialize_proof(&proof)
}

fn reference_verify_inner(config: &ScenarioConfig, bytes: &[u8]) -> Result<VerificationMetrics> {
    let prepared = build_scenario(config)?;
    let proof = deserialize_proof(bytes)?;
    let ds = domain_separator(&prepared.params, &prepared.session);
    HASH_COUNTER.reset();
    let started = Instant::now();
    let mut verifier_state = VerifierState::new_std(&ds, &proof);
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
    Ok(VerificationMetrics {
        elapsed_ns: started.elapsed().as_nanos(),
        hash_count: HASH_COUNTER.get() as u64,
    })
}

fn mirror_verify_inner(config: &ScenarioConfig, bytes: &[u8]) -> Result<VerificationMetrics> {
    let prepared = build_scenario(config)?;
    let proof = deserialize_proof(bytes)?;
    let ds = domain_separator(&prepared.params, &prepared.session);
    HASH_COUNTER.reset();
    let started = Instant::now();
    let mut verifier_state = VerifierState::new_std(&ds, &proof);
    let commitment = prepared
        .params
        .receive_commitment(&mut verifier_state)
        .map_err(|_| anyhow!("mirror receive_commitment rejected"))?;
    let final_claim = mirror_verify_config(
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
    Ok(VerificationMetrics {
        elapsed_ns: started.elapsed().as_nanos(),
        hash_count: HASH_COUNTER.get() as u64,
    })
}

fn build_params(config: &ScenarioConfig) -> Result<Goldilocks2Config> {
    if !config.unique_decoding {
        bail!("WHIR-UD spike requires unique_decoding=true");
    }
    let whir_params = ProtocolParameters {
        unique_decoding: true,
        security_level: config.security_level,
        pow_bits: config.pow_bits,
        initial_folding_factor: config.initial_folding_factor,
        folding_factor: config.folding_factor,
        starting_log_inv_rate: config.rate_bits,
        batch_size: 1,
        hash_id: BLAKE3,
    };
    Ok(Goldilocks2Config::new(
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
        session: format!("whir-ud-spike/{}", config.slug()),
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

fn serialize_proof(proof: &Proof) -> Result<Vec<u8>> {
    let mut out = Vec::new();
    ciborium::into_writer(proof, &mut out).context("failed to serialize proof with ciborium")?;
    Ok(out)
}

fn deserialize_proof(bytes: &[u8]) -> Result<Proof> {
    ciborium::from_reader(bytes).context("failed to deserialize proof with ciborium")
}

fn domain_separator<'a>(
    params: &'a Goldilocks2Config,
    session: &'a str,
) -> DomainSeparator<'a, Empty> {
    DomainSeparator::protocol(params)
        .session(&session)
        .instance(&EMPTY_INSTANCE)
}

fn catch_rejection<F>(f: F) -> Result<VerificationMetrics>
where
    F: FnOnce() -> Result<VerificationMetrics>,
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

fn max_required_pow_bits(params: &Goldilocks2Config) -> f64 {
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

fn hash_engine_name() -> String {
    ENGINES
        .retrieve(BLAKE3)
        .map(|engine| engine.name().to_string())
        .unwrap_or_else(|| MERKLE_HASH_MODE.to_string())
}

fn mirror_verify_config<M: Embedding, H>(
    params: &whir::protocols::whir::Config<M>,
    verifier_state: &mut VerifierState<'_, H>,
    commitments: &[&whir::protocols::whir::Commitment<M::Target>],
    evaluations: &[M::Target],
) -> VerificationResult<FinalClaim<M::Target>>
where
    H: DuplexSpongeInterface,
    M::Target: Codec<[H::U]>,
    u8: Decoding<[H::U]>,
    [u8; 32]: Decoding<[H::U]>,
    U64: Codec<[H::U]>,
    Hash: ProverMessage<[H::U]>,
{
    let num_vectors = commitments.len() * params.initial_committer.num_vectors;
    ensure_verification(evaluations.len().is_multiple_of(num_vectors))?;
    let num_linear_forms = evaluations.len() / num_vectors;
    if num_vectors == 0 {
        return Ok(FinalClaim::default());
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

    let vector_rlc_coeffs = geometric_challenge(verifier_state, num_vectors);
    let mut prev_commitment = RoundCommitment::Initial {
        commitments,
        batching_weights: vector_rlc_coeffs.clone(),
    };

    let constraint_rlc_coeffs: Vec<M::Target> =
        geometric_challenge(verifier_state, oods_evals.len() + num_linear_forms);
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
        assert_eq!(the_sum, M::Target::ZERO);
        let folding_randomness =
            verifier_state.verifier_message_vec(params.initial_sumcheck.num_rounds);
        params.initial_skip_pow.verify(verifier_state)?;
        folding_randomness
    } else {
        params
            .initial_sumcheck
            .verify(verifier_state, &mut the_sum)?
            .0
    };
    round_folding_randomness.push(folding_randomness);

    for (round_index, round_config) in params.round_configs.iter().enumerate() {
        let commitment = round_config
            .irs_committer
            .receive_commitment(verifier_state)?;
        round_config.pow.verify(verifier_state)?;

        let (in_domain, poly_rlc) = match prev_commitment {
            RoundCommitment::Initial {
                commitments,
                batching_weights,
            } => {
                let in_domain = params
                    .initial_committer
                    .verify(verifier_state, commitments)?;
                (in_domain.lift(params.embedding()), batching_weights)
            }
            RoundCommitment::Round { commitment } => {
                let prev_round_config = &params.round_configs[round_index - 1];
                let in_domain = prev_round_config
                    .irs_committer
                    .verify(verifier_state, &[&commitment])?;
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
        let constraint_rlc_coeffs = geometric_challenge(verifier_state, constraint_values.len());
        the_sum += dot(&constraint_rlc_coeffs, &constraint_values);
        round_constraints.push((constraint_rlc_coeffs, constraint_weights));

        let folding_randomness = round_config
            .sumcheck
            .verify(verifier_state, &mut the_sum)?
            .0;
        round_folding_randomness.push(folding_randomness);

        prev_commitment = RoundCommitment::Round { commitment };
    }

    let final_vector = verifier_state.prover_messages_vec(params.final_sumcheck.initial_size)?;
    params.final_pow.verify(verifier_state)?;

    let (in_domain, poly_rlc) = match prev_commitment {
        RoundCommitment::Initial {
            commitments,
            batching_weights,
        } => {
            let in_domain = params
                .initial_committer
                .verify(verifier_state, commitments)?;
            (in_domain.lift(params.embedding()), batching_weights)
        }
        RoundCommitment::Round { commitment } => {
            let prev_round_config = &params.round_configs.last().unwrap();
            let in_domain = prev_round_config
                .irs_committer
                .verify(verifier_state, &[&commitment])?;
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

    let final_sumcheck_randomness = params
        .final_sumcheck
        .verify(verifier_state, &mut the_sum)?
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

    Ok(FinalClaim {
        evaluation_point,
        rlc_coefficients: initial_form_rlc_coeffs.to_vec(),
        linear_form_rlc,
    })
}

pub fn current_hash_mode() -> String {
    hash_engine_name()
}

fn ensure_verification(condition: bool) -> VerificationResult<()> {
    if condition {
        Ok(())
    } else {
        Err(whir::transcript::VerificationError)
    }
}
