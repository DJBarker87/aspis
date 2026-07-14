//! Host builder for the read-only profile-21 masked-switch PCS diagnostic.

use aspis_core::field::QM31;
use aspis_core::merkle::{leaf_hash, node_hash, node_hash4};
use aspis_core::state_only_masked_switch::{
    evaluate_masked_switch_line, masked_switch_query_point, MaskedSwitchSchedule,
    MaskedSwitchVerifyError, MASKED_SWITCH_COEFFICIENTS, MASKED_SWITCH_FINAL_WORK_BITS,
    MASKED_SWITCH_LINE_DOMAIN_LOG, MASKED_SWITCH_LINE_VALUES_PER_LEAF,
    MASKED_SWITCH_MESSAGE_COEFFICIENTS, MASKED_SWITCH_PROFILE_DOMAIN, MASKED_SWITCH_QUERY_COUNT,
    MASKED_SWITCH_QUERY_MAX_DRAWS, MASKED_SWITCH_SOURCE_WORK_BITS, MASKED_SWITCH_U_LEAF_TAG,
    MASKED_SWITCH_VERSION, MASKED_SWITCH_XF_LEAF_TAG,
};
use aspis_core::transcript::{label, Transcript};
use aspis_core::HashFn;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MaskedSwitchBuildError {
    Core(MaskedSwitchVerifyError),
    Challenge,
    DeltaZeroExhausted,
    Ood,
    Query,
    TreeShape,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MaskedSwitchPowMode {
    Mine,
    UnminedZero,
}

impl From<MaskedSwitchVerifyError> for MaskedSwitchBuildError {
    fn from(error: MaskedSwitchVerifyError) -> Self {
        Self::Core(error)
    }
}

#[derive(Clone, Debug)]
pub struct BuiltStateOnlyMaskedSwitchDiagnostic {
    pub proof: Vec<u8>,
    pub schedule: MaskedSwitchSchedule,
    pub xf_frontier_nodes: usize,
    pub u_frontier_nodes: usize,
    pub source_work_nonce: u64,
    pub final_work_nonce: u64,
    pub pow_valid: bool,
}

fn append_qm31(output: &mut Vec<u8>, value: QM31) {
    let mut bytes = [0u8; 16];
    value.write_le_bytes(&mut bytes);
    output.extend_from_slice(&bytes);
}

fn absorb_qm31_pair(transcript: &mut Transcript, label: u8, first: QM31, second: QM31) {
    let mut bytes = [0u8; 32];
    first.write_le_bytes(&mut bytes[..16]);
    second.write_le_bytes(&mut bytes[16..]);
    transcript.absorb(label, &bytes);
}

fn sample_nonzero_delta(transcript: &mut Transcript) -> Result<QM31, MaskedSwitchBuildError> {
    for _ in 0..3 {
        let candidate = transcript
            .challenge_qm31()
            .map_err(|_| MaskedSwitchBuildError::Challenge)?;
        if candidate != QM31::ZERO {
            return Ok(candidate);
        }
    }
    Err(MaskedSwitchBuildError::DeltaZeroExhausted)
}

fn target_dot(coefficients: &[QM31; MASKED_SWITCH_COEFFICIENTS], eta: QM31) -> QM31 {
    let mut power = QM31::ONE;
    let mut result = QM31::ZERO;
    for coefficient in &coefficients[..MASKED_SWITCH_MESSAGE_COEFFICIENTS] {
        result = result.add(power.mul(*coefficient));
        power = power.mul(eta);
    }
    result
}

fn tree<const N: usize>(leaves: &[[u8; N]], tag: u8, hash: HashFn) -> Vec<Vec<[u8; 32]>> {
    let mut levels = vec![leaves
        .iter()
        .map(|leaf| leaf_hash(hash, tag, leaf))
        .collect::<Vec<_>>()];
    while levels.last().map_or(0, Vec::len) > 1 {
        let previous = levels.last().unwrap();
        levels.push(if previous.len() == 2 {
            vec![node_hash(hash, &previous[0], &previous[1])]
        } else {
            previous
                .chunks_exact(4)
                .map(|children| node_hash4(hash, children.try_into().unwrap()))
                .collect()
        });
    }
    levels
}

fn frontier(levels: &[Vec<[u8; 32]>], indices: &[u32]) -> Vec<[u8; 32]> {
    let mut result = Vec::new();
    let mut current = indices.to_vec();
    for level in &levels[..levels.len() - 1] {
        if level.len() == 2 {
            if current.len() == 1 {
                result.push(level[(current[0] ^ 1) as usize]);
            }
            current.clear();
            current.push(0);
            continue;
        }
        let mut next = Vec::new();
        let mut position = 0usize;
        while position < current.len() {
            let parent = current[position] >> 2;
            let mut present = 0u8;
            while position < current.len() && current[position] >> 2 == parent {
                present |= 1u8 << (current[position] & 3);
                position += 1;
            }
            for slot in 0..4u32 {
                if present & (1u8 << slot) == 0 {
                    result.push(level[(4 * parent + slot) as usize]);
                }
            }
            next.push(parent);
        }
        current = next;
    }
    result
}

fn append_frontier(bytes: &mut Vec<u8>, nodes: &[[u8; 32]]) {
    bytes.extend_from_slice(&(nodes.len() as u32).to_le_bytes());
    for node in nodes {
        bytes.extend_from_slice(node);
    }
}

/// Build a deterministic unmined fixture. Both work checks are still executed
/// by the verifier, but diagnostic mode permits their predicates to fail;
/// production profile 21 must mine the same positioned g36 witnesses.
pub fn build_state_only_masked_switch_diagnostic(
    statement_digest: &[u8; 32],
    x: [QM31; MASKED_SWITCH_COEFFICIENTS],
    f: [QM31; MASKED_SWITCH_COEFFICIENTS],
    hash: HashFn,
) -> Result<BuiltStateOnlyMaskedSwitchDiagnostic, MaskedSwitchBuildError> {
    build_state_only_masked_switch(
        statement_digest,
        x,
        f,
        hash,
        MaskedSwitchPowMode::UnminedZero,
    )
}

/// Build the same byte-exact switch proof with either diagnostic zero nonces
/// or the canonical production miner. The source witness remains before
/// delta and the final witness remains before q16.
pub fn build_state_only_masked_switch(
    statement_digest: &[u8; 32],
    x: [QM31; MASKED_SWITCH_COEFFICIENTS],
    f: [QM31; MASKED_SWITCH_COEFFICIENTS],
    hash: HashFn,
    pow_mode: MaskedSwitchPowMode,
) -> Result<BuiltStateOnlyMaskedSwitchDiagnostic, MaskedSwitchBuildError> {
    let line_value_count = 1usize << MASKED_SWITCH_LINE_DOMAIN_LOG;
    let leaf_count = line_value_count / MASKED_SWITCH_LINE_VALUES_PER_LEAF;
    let mut x_values = Vec::with_capacity(line_value_count);
    let mut f_values = Vec::with_capacity(line_value_count);
    for index in 0..line_value_count {
        let point = masked_switch_query_point(index as u32)?;
        let x_value = evaluate_masked_switch_line(&x, point)?;
        let f_value = evaluate_masked_switch_line(&f, point)?;
        x_values.push(x_value);
        f_values.push(f_value);
    }
    let mut xf_leaves = Vec::with_capacity(leaf_count);
    for leaf_index in 0..leaf_count {
        let mut leaf = [0u8; 128];
        for slot in 0..MASKED_SWITCH_LINE_VALUES_PER_LEAF {
            let value_index = MASKED_SWITCH_LINE_VALUES_PER_LEAF * leaf_index + slot;
            x_values[value_index].write_le_bytes(&mut leaf[16 * slot..]);
            let f_start = 16 * (MASKED_SWITCH_LINE_VALUES_PER_LEAF + slot);
            f_values[value_index].write_le_bytes(&mut leaf[f_start..]);
        }
        xf_leaves.push(leaf);
    }
    let xf_tree = tree(&xf_leaves, MASKED_SWITCH_XF_LEAF_TAG, hash);
    let xf_root = *xf_tree
        .last()
        .and_then(|level| level.first())
        .ok_or(MaskedSwitchBuildError::TreeShape)?;

    let mut transcript = Transcript::new(hash);
    transcript.absorb(label::PROFILE, MASKED_SWITCH_PROFILE_DOMAIN);
    transcript.absorb(label::STATEMENT, statement_digest);
    transcript.absorb(label::M31_STATE_ONLY_SWITCH_XF_ROOT, &xf_root);
    let target_challenge = transcript
        .challenge_qm31()
        .map_err(|_| MaskedSwitchBuildError::Challenge)?;
    let t_x = target_dot(&x, target_challenge);
    let mu_f = target_dot(&f, target_challenge);
    absorb_qm31_pair(
        &mut transcript,
        label::M31_STATE_ONLY_SWITCH_TARGETS,
        t_x,
        mu_f,
    );

    let source_work_nonce = match pow_mode {
        MaskedSwitchPowMode::Mine => {
            crate::pow::find_grinding_nonce(&transcript, MASKED_SWITCH_SOURCE_WORK_BITS)
        }
        MaskedSwitchPowMode::UnminedZero => 0,
    };
    let source_work_valid =
        transcript.grinding_ok(source_work_nonce, MASKED_SWITCH_SOURCE_WORK_BITS);
    transcript.absorb(
        label::M31_STATE_ONLY_SWITCH_SOURCE_POW_NONCE,
        &source_work_nonce.to_le_bytes(),
    );
    let delta = sample_nonzero_delta(&mut transcript)?;
    let u = core::array::from_fn(|index| f[index].add(delta.mul(x[index])));

    let mut u_bytes = Vec::with_capacity(16 * MASKED_SWITCH_COEFFICIENTS);
    for coefficient in u {
        append_qm31(&mut u_bytes, coefficient);
    }
    transcript.absorb(label::M31_STATE_ONLY_SWITCH_U, &u_bytes);

    let u_values = f_values
        .iter()
        .copied()
        .zip(x_values.iter().copied())
        .map(|(f_value, x_value)| f_value.add(delta.mul(x_value)))
        .collect::<Vec<_>>();
    let mut u_leaves = Vec::with_capacity(leaf_count);
    for leaf_index in 0..leaf_count {
        let mut leaf = [0u8; 64];
        for slot in 0..MASKED_SWITCH_LINE_VALUES_PER_LEAF {
            let value_index = MASKED_SWITCH_LINE_VALUES_PER_LEAF * leaf_index + slot;
            u_values[value_index].write_le_bytes(&mut leaf[16 * slot..]);
        }
        u_leaves.push(leaf);
    }
    let u_tree = tree(&u_leaves, MASKED_SWITCH_U_LEAF_TAG, hash);
    let translated_root = *u_tree
        .last()
        .and_then(|level| level.first())
        .ok_or(MaskedSwitchBuildError::TreeShape)?;
    transcript.absorb(
        label::M31_STATE_ONLY_SWITCH_TRANSLATED_ROOT,
        &translated_root,
    );
    let beta = [
        transcript
            .challenge_ood_qm31()
            .map_err(|_| MaskedSwitchBuildError::Ood)?,
        transcript
            .challenge_ood_qm31()
            .map_err(|_| MaskedSwitchBuildError::Ood)?,
    ];
    let beta_values = [
        evaluate_masked_switch_line(&u, beta[0])?,
        evaluate_masked_switch_line(&u, beta[1])?,
    ];

    let final_work_nonce = match pow_mode {
        MaskedSwitchPowMode::Mine => {
            crate::pow::find_grinding_nonce(&transcript, MASKED_SWITCH_FINAL_WORK_BITS)
        }
        MaskedSwitchPowMode::UnminedZero => 0,
    };
    let final_work_valid = transcript.grinding_ok(final_work_nonce, MASKED_SWITCH_FINAL_WORK_BITS);
    transcript.absorb(
        label::M31_STATE_ONLY_SWITCH_FINAL_POW_NONCE,
        &final_work_nonce.to_le_bytes(),
    );
    let query_vec = transcript
        .challenge_queries_without_replacement(
            MASKED_SWITCH_QUERY_COUNT,
            1u32 << MASKED_SWITCH_LINE_DOMAIN_LOG,
            MASKED_SWITCH_QUERY_MAX_DRAWS,
        )
        .map_err(|_| MaskedSwitchBuildError::Query)?;
    let queries: [u32; MASKED_SWITCH_QUERY_COUNT] = query_vec
        .try_into()
        .map_err(|_| MaskedSwitchBuildError::Query)?;
    let mut sorted_queries = queries;
    sorted_queries.sort_unstable();
    let mut leaf_indices = sorted_queries.map(|query| query >> 2).to_vec();
    leaf_indices.dedup();
    let xf_frontier = frontier(&xf_tree, &leaf_indices);
    let u_frontier = frontier(&u_tree, &leaf_indices);

    let mut proof = Vec::new();
    proof.push(MASKED_SWITCH_VERSION);
    proof.extend_from_slice(&xf_root);
    append_qm31(&mut proof, t_x);
    append_qm31(&mut proof, mu_f);
    proof.extend_from_slice(&source_work_nonce.to_le_bytes());
    proof.extend_from_slice(&u_bytes);
    proof.extend_from_slice(&translated_root);
    append_qm31(&mut proof, beta_values[0]);
    append_qm31(&mut proof, beta_values[1]);
    proof.extend_from_slice(&final_work_nonce.to_le_bytes());
    proof.extend_from_slice(&(leaf_indices.len() as u16).to_le_bytes());
    for &leaf_index in &leaf_indices {
        proof.extend_from_slice(&xf_leaves[leaf_index as usize]);
        proof.extend_from_slice(&u_leaves[leaf_index as usize]);
    }
    append_frontier(&mut proof, &xf_frontier);
    append_frontier(&mut proof, &u_frontier);

    Ok(BuiltStateOnlyMaskedSwitchDiagnostic {
        proof,
        schedule: MaskedSwitchSchedule {
            target_challenge,
            delta,
            beta,
            queries,
        },
        xf_frontier_nodes: xf_frontier.len(),
        u_frontier_nodes: u_frontier.len(),
        source_work_nonce,
        final_work_nonce,
        pow_valid: source_work_valid && final_work_valid,
    })
}
