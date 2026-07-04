use std::time::Instant;

use anyhow::{bail, Result};
use whir_m31_core::{
    field::{
        eval_local_block_m31, eval_local_block_qm31, local_interpolant_m31, local_interpolant_qm31,
        LiftPolicy, Qm31, M31,
    },
    merkle::{hash_leaf, hash_node, MerkleHash},
    profile::WhirProfileManifest,
    proof::{
        serialize_m31_block, serialize_qm31, serialize_qm31_block, CommitmentRoot, FoldRoundProof,
        MerkleProof, QueryBlock, QueryOpening, TranscriptCommitmentSection, WhirEnvelopeV1,
        WhirProofV0,
    },
    statement::{SpendV0Binding, StatementDigest},
    transcript::Transcript,
    verify_proof_bytes, VerificationReport,
};

#[derive(Clone, Debug)]
pub struct MultilinearWitness {
    pub evaluations: Vec<M31>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ProverMeasurements {
    pub total_ns: u128,
    pub commitment_ns: u128,
    pub query_ns: u128,
    pub proof_bytes: usize,
}

#[derive(Clone, Debug)]
pub struct ProverOutput {
    pub statement_digest: StatementDigest,
    pub final_value: Qm31,
    pub proof: WhirEnvelopeV1,
    pub proof_bytes: Vec<u8>,
    pub measurements: ProverMeasurements,
}

#[derive(Clone)]
struct MerkleTree {
    levels: Vec<Vec<MerkleHash>>,
}

#[derive(Clone)]
enum CommittedBlocks {
    M31(Vec<[M31; 4]>),
    QM31(Vec<[Qm31; 4]>),
}

impl MerkleTree {
    fn from_serialized_leaves(leaves: &[Vec<u8>]) -> Self {
        let mut levels = Vec::new();
        let mut current = leaves
            .iter()
            .map(|bytes| hash_leaf(bytes))
            .collect::<Vec<_>>();
        levels.push(current.clone());
        while current.len() > 1 {
            let mut next = Vec::with_capacity(current.len() / 2);
            for pair in current.chunks_exact(2) {
                next.push(hash_node(&pair[0], &pair[1]));
            }
            levels.push(next.clone());
            current = next;
        }
        Self { levels }
    }

    fn root(&self) -> MerkleHash {
        self.levels
            .last()
            .expect("merkle tree has no levels")
            .first()
            .copied()
            .expect("merkle tree has no root")
    }

    fn open(&self, mut index: usize) -> MerkleProof {
        let mut siblings = Vec::with_capacity(self.levels.len().saturating_sub(1));
        for level in &self.levels[..self.levels.len().saturating_sub(1)] {
            let sibling_index = index ^ 1;
            siblings.push(level[sibling_index]);
            index >>= 1;
        }
        MerkleProof { siblings }
    }
}

impl CommittedBlocks {
    fn current_block(&self, index: usize) -> QueryBlock {
        match self {
            Self::M31(values) => QueryBlock::M31(values[index]),
            Self::QM31(values) => QueryBlock::QM31(values[index]),
        }
    }

    fn next_qm31_block(&self, index: usize) -> [Qm31; 4] {
        match self {
            Self::QM31(values) => values[index],
            Self::M31(_) => panic!("expected QM31 block"),
        }
    }
}

pub fn deterministic_witness(
    profile: &'static WhirProfileManifest,
    seed: StatementDigest,
) -> MultilinearWitness {
    let mut state = u64::from_le_bytes(seed[0..8].try_into().unwrap()) ^ 0x9e37_79b9_7f4a_7c15;
    let len = 1usize << profile.log_num_rows;
    let mut evaluations = Vec::with_capacity(len);
    for index in 0..len {
        state = mix64(state ^ index as u64);
        evaluations.push(M31::from((state as u32) & 0x7fff_ffff));
    }
    MultilinearWitness { evaluations }
}

pub fn prove(
    profile: &'static WhirProfileManifest,
    binding: &SpendV0Binding,
    witness: &MultilinearWitness,
) -> Result<ProverOutput> {
    let expected_len = 1usize << profile.log_num_rows;
    if witness.evaluations.len() != expected_len {
        bail!(
            "witness length {} does not match expected {}",
            witness.evaluations.len(),
            expected_len
        );
    }

    let statement_digest = binding.digest();
    let total_started = Instant::now();
    let mut transcript = Transcript::new(profile.id, &statement_digest);
    let mut roots = Vec::with_capacity(profile.round_count());
    let mut trees = Vec::with_capacity(profile.round_count());
    let mut blocks = Vec::with_capacity(profile.round_count());
    let mut current_m31 = Some(witness.evaluations.clone());
    let mut current_qm31: Vec<Qm31> = Vec::new();
    let commitment_started = Instant::now();

    for round in 0..profile.round_count() {
        if round == 0 {
            let table = current_m31.take().expect("missing initial table");
            let round_blocks = table
                .chunks_exact(4)
                .map(|chunk| local_interpolant_m31([chunk[0], chunk[1], chunk[2], chunk[3]]))
                .collect::<Vec<_>>();
            let leaves = round_blocks
                .iter()
                .map(|values| serialize_m31_block(*values).to_vec())
                .collect::<Vec<_>>();
            let tree = MerkleTree::from_serialized_leaves(&leaves);
            let root = tree.root();
            transcript.absorb_root(round, &root);
            let (x, y) = transcript.sample_round_challenge_pair(round);
            current_qm31 = round_blocks
                .iter()
                .map(|coeffs| eval_local_block_m31(*coeffs, x, y, LiftPolicy::LateQm31))
                .collect();
            roots.push(CommitmentRoot(root));
            trees.push(tree);
            blocks.push(CommittedBlocks::M31(round_blocks));
        } else {
            let round_blocks = current_qm31
                .chunks_exact(4)
                .map(|chunk| local_interpolant_qm31([chunk[0], chunk[1], chunk[2], chunk[3]]))
                .collect::<Vec<_>>();
            let leaves = round_blocks
                .iter()
                .map(|values| serialize_qm31_block(*values).to_vec())
                .collect::<Vec<_>>();
            let tree = MerkleTree::from_serialized_leaves(&leaves);
            let root = tree.root();
            transcript.absorb_root(round, &root);
            let (x, y) = transcript.sample_round_challenge_pair(round);
            current_qm31 = round_blocks
                .iter()
                .map(|coeffs| eval_local_block_qm31(*coeffs, x, y))
                .collect();
            roots.push(CommitmentRoot(root));
            trees.push(tree);
            blocks.push(CommittedBlocks::QM31(round_blocks));
        }
    }
    if current_qm31.len() != 1 {
        bail!(
            "expected final table of length 1, found {}",
            current_qm31.len()
        );
    }
    let final_value = current_qm31[0];
    transcript.absorb_final_value(&serialize_qm31(final_value));
    let commitment_ns = commitment_started.elapsed().as_nanos();

    let query_started = Instant::now();
    let mut rounds = Vec::with_capacity(profile.round_count());
    for round in 0..profile.round_count() {
        let mut openings = Vec::with_capacity(profile.query_repetitions_per_round as usize);
        for repetition in 0..profile.query_repetitions_per_round as usize {
            let query_index = transcript.sample_query_index(
                round,
                repetition,
                profile.block_count_at_round(round),
            );
            let current_path = trees[round].open(query_index);
            let current_block = blocks[round].current_block(query_index);
            let (next_block, next_path) = if round + 1 < profile.round_count() {
                let next_group_index = query_index >> profile.fold_vars_per_round;
                (
                    Some(blocks[round + 1].next_qm31_block(next_group_index)),
                    Some(trees[round + 1].open(next_group_index)),
                )
            } else {
                (None, None)
            };
            openings.push(QueryOpening {
                current_block,
                current_path,
                next_block,
                next_path,
            });
        }
        rounds.push(FoldRoundProof { openings });
    }
    let query_ns = query_started.elapsed().as_nanos();

    let proof = WhirEnvelopeV1 {
        profile_id: profile.id,
        hash_mode: profile.hash_mode,
        fold_mode: profile.fold_mode,
        statement_binding_version: profile.statement_binding_version,
        statement_digest,
        proof: WhirProofV0 {
            commitments: TranscriptCommitmentSection {
                round_roots: roots,
                final_value,
            },
            rounds,
        },
    };
    let proof_bytes = proof.encode(profile);
    Ok(ProverOutput {
        statement_digest,
        final_value,
        proof,
        measurements: ProverMeasurements {
            total_ns: total_started.elapsed().as_nanos(),
            commitment_ns,
            query_ns,
            proof_bytes: proof_bytes.len(),
        },
        proof_bytes,
    })
}

pub fn verify(
    profile: &'static WhirProfileManifest,
    binding: &SpendV0Binding,
    proof_bytes: &[u8],
) -> Result<VerificationReport> {
    verify_proof_bytes(profile.id, binding, proof_bytes)
        .map_err(|error| anyhow::anyhow!("host verification failed: {error:?}"))
}

fn mix64(mut value: u64) -> u64 {
    value ^= value >> 30;
    value = value.wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value ^= value >> 27;
    value = value.wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

#[cfg(test)]
mod tests {
    use super::*;
    use whir_m31_core::{
        profile::{profile_manifest, ProfileId},
        proof::HEADER_BYTES,
        statement::SpendV0Binding,
    };

    fn sample_binding() -> SpendV0Binding {
        SpendV0Binding::new(
            [1_u8; 32],
            &[[2_u8; 32]],
            &[[3_u8; 32], [4_u8; 32]],
            [5_u8; 32],
            17,
        )
    }

    #[test]
    fn host_prover_and_verifier_round_trip_dev() {
        let profile = profile_manifest(ProfileId::WhirM31DevV0);
        let binding = sample_binding();
        let witness = deterministic_witness(profile, binding.digest());
        let proof = prove(profile, &binding, &witness).unwrap();
        verify(profile, &binding, &proof.proof_bytes).unwrap();
    }

    #[test]
    fn statement_digest_mismatch_rejects() {
        let profile = profile_manifest(ProfileId::WhirM31DevV0);
        let binding = sample_binding();
        let witness = deterministic_witness(profile, binding.digest());
        let proof = prove(profile, &binding, &witness).unwrap();
        let other = SpendV0Binding::new([9_u8; 32], &[[2_u8; 32]], &[[3_u8; 32]], [5_u8; 32], 17);
        assert!(verify(profile, &other, &proof.proof_bytes).is_err());
    }

    #[test]
    fn transcript_root_corruption_rejects() {
        let profile = profile_manifest(ProfileId::WhirM31DevV0);
        let binding = sample_binding();
        let witness = deterministic_witness(profile, binding.digest());
        let proof = prove(profile, &binding, &witness).unwrap();
        let mut corrupted = proof.proof_bytes.clone();
        corrupted[HEADER_BYTES] ^= 0x01;
        assert!(verify(profile, &binding, &corrupted).is_err());
    }

    #[test]
    fn truncated_proof_rejects() {
        let profile = profile_manifest(ProfileId::WhirM31DevV0);
        let binding = sample_binding();
        let witness = deterministic_witness(profile, binding.digest());
        let proof = prove(profile, &binding, &witness).unwrap();
        let truncated = &proof.proof_bytes[..proof.proof_bytes.len() - 1];
        assert!(verify(profile, &binding, truncated).is_err());
    }
}
