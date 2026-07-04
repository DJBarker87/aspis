use alloc::vec::Vec;

use crate::field::{
    block_value_from_qm31_coeffs, eval_local_block_m31, eval_local_block_qm31, LiftPolicy, Qm31,
    M31,
};
use crate::merkle::MerkleHash;
use crate::profile::{HashMode, ProfileId, WhirFoldMode, WhirProfileManifest};
use crate::statement::StatementDigest;

pub const WHIR_ENVELOPE_MAGIC: [u8; 4] = *b"WHM1";
pub const ENVELOPE_VERSION: u16 = 1;
pub const HEADER_BYTES: usize = 60;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CommitmentRoot(pub MerkleHash);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct QueryIndex(pub u32);

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MerkleProof {
    pub siblings: Vec<MerkleHash>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MerkleMultiProof {
    pub paths: Vec<MerkleProof>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum QueryBlock {
    M31([M31; 4]),
    QM31([Qm31; 4]),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct QueryOpening {
    pub current_block: QueryBlock,
    pub current_path: MerkleProof,
    pub next_block: Option<[Qm31; 4]>,
    pub next_path: Option<MerkleProof>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FoldRoundProof {
    pub openings: Vec<QueryOpening>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TranscriptCommitmentSection {
    pub round_roots: Vec<CommitmentRoot>,
    pub final_value: Qm31,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WhirProofV0 {
    pub commitments: TranscriptCommitmentSection,
    pub rounds: Vec<FoldRoundProof>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WhirEnvelopeV1 {
    pub profile_id: ProfileId,
    pub hash_mode: HashMode,
    pub fold_mode: WhirFoldMode,
    pub statement_binding_version: u16,
    pub statement_digest: StatementDigest,
    pub proof: WhirProofV0,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ParseError {
    Length,
    Magic,
    Version,
    ProofVersion,
    ProfileMismatch,
    HashModeMismatch,
    FoldModeMismatch,
    StatementBindingVersionMismatch,
    RoundCountMismatch,
    QueryCountMismatch,
    FoldVarsMismatch,
    CanonicalField,
}

pub struct WhirEnvelopeView<'a> {
    profile: &'static WhirProfileManifest,
    bytes: &'a [u8],
    statement_digest: StatementDigest,
    roots_offset: usize,
    final_value_offset: usize,
    round_offsets: [usize; 8],
}

pub struct QueryOpeningView<'a> {
    bytes: &'a [u8],
    round: usize,
    current_block_offset: usize,
    current_siblings_offset: usize,
    next_block_offset: usize,
    next_siblings_offset: usize,
    current_siblings_len: usize,
    next_siblings_len: usize,
}

impl WhirEnvelopeV1 {
    pub fn encode(&self, profile: &'static WhirProfileManifest) -> Vec<u8> {
        let expected_rounds = profile.round_count();
        assert_eq!(self.proof.commitments.round_roots.len(), expected_rounds);
        assert_eq!(self.proof.rounds.len(), expected_rounds);
        let mut out = Vec::with_capacity(expected_proof_len(profile));
        out.extend_from_slice(&WHIR_ENVELOPE_MAGIC);
        out.extend_from_slice(&ENVELOPE_VERSION.to_le_bytes());
        out.extend_from_slice(&profile.proof_version.to_le_bytes());
        out.extend_from_slice(&(self.profile_id as u16).to_le_bytes());
        out.extend_from_slice(&(self.hash_mode as u16).to_le_bytes());
        out.extend_from_slice(&(self.fold_mode as u16).to_le_bytes());
        out.extend_from_slice(&self.statement_binding_version.to_le_bytes());
        out.extend_from_slice(&(expected_proof_len(profile) as u32).to_le_bytes());
        out.extend_from_slice(&self.statement_digest);
        out.push(expected_rounds as u8);
        out.push(profile.query_repetitions_per_round);
        out.push(profile.fold_vars_per_round);
        out.push(1);
        out.extend_from_slice(&0_u32.to_le_bytes());
        for root in &self.proof.commitments.round_roots {
            out.extend_from_slice(&root.0);
        }
        write_qm31(&mut out, self.proof.commitments.final_value);
        for (round_index, round) in self.proof.rounds.iter().enumerate() {
            assert_eq!(
                round.openings.len(),
                profile.query_repetitions_per_round as usize
            );
            for opening in &round.openings {
                match opening.current_block {
                    QueryBlock::M31(values) => {
                        assert_eq!(round_index, 0);
                        write_m31_block(&mut out, values);
                    }
                    QueryBlock::QM31(values) => {
                        assert!(round_index > 0);
                        write_qm31_block(&mut out, values);
                    }
                }
                for sibling in &opening.current_path.siblings {
                    out.extend_from_slice(sibling);
                }
                if round_index + 1 < expected_rounds {
                    let next_block = opening.next_block.expect("missing next block");
                    let next_path = opening.next_path.as_ref().expect("missing next path");
                    write_qm31_block(&mut out, next_block);
                    for sibling in &next_path.siblings {
                        out.extend_from_slice(sibling);
                    }
                }
            }
        }
        debug_assert_eq!(out.len(), expected_proof_len(profile));
        out
    }

    pub fn decode_owned(
        profile: &'static WhirProfileManifest,
        bytes: &[u8],
    ) -> Result<Self, ParseError> {
        let view = WhirEnvelopeView::parse(profile, bytes)?;
        let mut round_roots = Vec::with_capacity(profile.round_count());
        let mut round = 0;
        while round < profile.round_count() {
            round_roots.push(view.round_root(round));
            round += 1;
        }
        let mut rounds = Vec::with_capacity(profile.round_count());
        round = 0;
        while round < profile.round_count() {
            let mut openings = Vec::with_capacity(profile.query_repetitions_per_round as usize);
            let mut repetition = 0;
            while repetition < profile.query_repetitions_per_round as usize {
                let opening = view.query_opening(round, repetition)?;
                let current_block = if round == 0 {
                    QueryBlock::M31(read_m31_block(opening.current_block_bytes())?)
                } else {
                    QueryBlock::QM31(read_qm31_block(opening.current_block_bytes())?)
                };
                let current_path = read_merkle_proof(opening.current_siblings_bytes());
                let next_block = if round + 1 < profile.round_count() {
                    Some(read_qm31_block(opening.next_block_bytes())?)
                } else {
                    None
                };
                let next_path = if round + 1 < profile.round_count() {
                    Some(read_merkle_proof(opening.next_siblings_bytes()))
                } else {
                    None
                };
                openings.push(QueryOpening {
                    current_block,
                    current_path,
                    next_block,
                    next_path,
                });
                repetition += 1;
            }
            rounds.push(FoldRoundProof { openings });
            round += 1;
        }
        Ok(Self {
            profile_id: profile.id,
            hash_mode: profile.hash_mode,
            fold_mode: profile.fold_mode,
            statement_binding_version: profile.statement_binding_version,
            statement_digest: view.statement_digest(),
            proof: WhirProofV0 {
                commitments: TranscriptCommitmentSection {
                    round_roots,
                    final_value: view.final_value()?,
                },
                rounds,
            },
        })
    }
}

impl<'a> WhirEnvelopeView<'a> {
    pub fn parse(
        profile: &'static WhirProfileManifest,
        bytes: &'a [u8],
    ) -> Result<Self, ParseError> {
        if bytes.len() != expected_proof_len(profile) {
            return Err(ParseError::Length);
        }
        if bytes[..4] != WHIR_ENVELOPE_MAGIC {
            return Err(ParseError::Magic);
        }
        if read_u16(bytes, 4)? != ENVELOPE_VERSION {
            return Err(ParseError::Version);
        }
        if read_u16(bytes, 6)? != profile.proof_version {
            return Err(ParseError::ProofVersion);
        }
        if read_u16(bytes, 8)? != profile.id as u16 {
            return Err(ParseError::ProfileMismatch);
        }
        if read_u16(bytes, 10)? != profile.hash_mode as u16 {
            return Err(ParseError::HashModeMismatch);
        }
        if read_u16(bytes, 12)? != profile.fold_mode as u16 {
            return Err(ParseError::FoldModeMismatch);
        }
        if read_u16(bytes, 14)? != profile.statement_binding_version {
            return Err(ParseError::StatementBindingVersionMismatch);
        }
        if read_u32(bytes, 16)? as usize != bytes.len() {
            return Err(ParseError::Length);
        }
        let mut digest = [0_u8; 32];
        digest.copy_from_slice(&bytes[20..52]);
        if bytes[52] as usize != profile.round_count() {
            return Err(ParseError::RoundCountMismatch);
        }
        if bytes[53] != profile.query_repetitions_per_round {
            return Err(ParseError::QueryCountMismatch);
        }
        if bytes[54] != profile.fold_vars_per_round {
            return Err(ParseError::FoldVarsMismatch);
        }

        let roots_offset = HEADER_BYTES;
        let final_value_offset = roots_offset + profile.round_count() * 32;
        let mut round_offsets = [0_usize; 8];
        let mut cursor = final_value_offset + 16;
        let mut round = 0;
        while round < profile.round_count() {
            round_offsets[round] = cursor;
            cursor +=
                profile.round_query_bytes(round) * profile.query_repetitions_per_round as usize;
            round += 1;
        }
        Ok(Self {
            profile,
            bytes,
            statement_digest: digest,
            roots_offset,
            final_value_offset,
            round_offsets,
        })
    }

    pub fn statement_digest(&self) -> StatementDigest {
        self.statement_digest
    }

    pub fn round_root(&self, round: usize) -> CommitmentRoot {
        let offset = self.roots_offset + round * 32;
        let mut root = [0_u8; 32];
        root.copy_from_slice(&self.bytes[offset..offset + 32]);
        CommitmentRoot(root)
    }

    pub fn final_value(&self) -> Result<Qm31, ParseError> {
        read_qm31(self.bytes, self.final_value_offset)
    }

    pub fn query_opening(
        &self,
        round: usize,
        repetition: usize,
    ) -> Result<QueryOpeningView<'a>, ParseError> {
        if round >= self.profile.round_count() {
            return Err(ParseError::RoundCountMismatch);
        }
        if repetition >= self.profile.query_repetitions_per_round as usize {
            return Err(ParseError::QueryCountMismatch);
        }
        let base = self.round_offsets[round] + repetition * self.profile.round_query_bytes(round);
        let current_block_offset = base;
        let current_block_len = self.profile.current_block_bytes(round);
        let current_siblings_offset = current_block_offset + current_block_len;
        let current_siblings_len = self.profile.current_merkle_depth(round) * 32;
        let next_block_offset = current_siblings_offset + current_siblings_len;
        let next_siblings_offset = next_block_offset + self.profile.next_block_bytes(round);
        let next_siblings_len = self.profile.next_merkle_depth(round) * 32;
        Ok(QueryOpeningView {
            bytes: self.bytes,
            round,
            current_block_offset,
            current_siblings_offset,
            next_block_offset,
            next_siblings_offset,
            current_siblings_len,
            next_siblings_len,
        })
    }
}

impl<'a> QueryOpeningView<'a> {
    pub fn current_block(&self) -> Result<QueryBlock, ParseError> {
        if self.round == 0 {
            Ok(QueryBlock::M31(read_m31_block(self.current_block_bytes())?))
        } else {
            Ok(QueryBlock::QM31(read_qm31_block(
                self.current_block_bytes(),
            )?))
        }
    }

    pub fn current_block_bytes(&self) -> &'a [u8] {
        let len = if self.round == 0 { 16 } else { 64 };
        &self.bytes[self.current_block_offset..self.current_block_offset + len]
    }

    pub fn current_siblings_bytes(&self) -> &'a [u8] {
        &self.bytes
            [self.current_siblings_offset..self.current_siblings_offset + self.current_siblings_len]
    }

    pub fn next_block_bytes(&self) -> &'a [u8] {
        &self.bytes[self.next_block_offset..self.next_block_offset + 64]
    }

    pub fn next_siblings_bytes(&self) -> &'a [u8] {
        &self.bytes[self.next_siblings_offset..self.next_siblings_offset + self.next_siblings_len]
    }

    pub fn next_block(&self) -> Result<[Qm31; 4], ParseError> {
        read_qm31_block(self.next_block_bytes())
    }
}

pub fn expected_proof_len(profile: &WhirProfileManifest) -> usize {
    let mut len = HEADER_BYTES + profile.round_count() * 32 + 16;
    let mut round = 0;
    while round < profile.round_count() {
        len += profile.round_query_bytes(round) * profile.query_repetitions_per_round as usize;
        round += 1;
    }
    len
}

pub fn evaluate_block_for_verifier(
    current_block: QueryBlock,
    next_block: Option<[Qm31; 4]>,
    query_index: usize,
    x: Qm31,
    y: Qm31,
    lift_policy: LiftPolicy,
) -> (Qm31, Option<Qm31>) {
    let expected = match current_block {
        QueryBlock::M31(values) => eval_local_block_m31(values, x, y, lift_policy),
        QueryBlock::QM31(values) => eval_local_block_qm31(values, x, y),
    };
    let actual = next_block.map(|coeffs| block_value_from_qm31_coeffs(coeffs, query_index & 0x3));
    (expected, actual)
}

pub fn serialize_m31(value: M31) -> [u8; 4] {
    value.as_u32().to_le_bytes()
}

pub fn serialize_qm31(value: Qm31) -> [u8; 16] {
    let mut out = [0_u8; 16];
    for (index, limb) in value.to_m31_array().iter().enumerate() {
        out[index * 4..index * 4 + 4].copy_from_slice(&limb.as_u32().to_le_bytes());
    }
    out
}

pub fn serialize_m31_block(values: [M31; 4]) -> [u8; 16] {
    let mut out = [0_u8; 16];
    for (index, value) in values.iter().enumerate() {
        out[index * 4..index * 4 + 4].copy_from_slice(&value.as_u32().to_le_bytes());
    }
    out
}

pub fn serialize_qm31_block(values: [Qm31; 4]) -> [u8; 64] {
    let mut out = [0_u8; 64];
    for (index, value) in values.iter().enumerate() {
        out[index * 16..index * 16 + 16].copy_from_slice(&serialize_qm31(*value));
    }
    out
}

fn write_m31(out: &mut Vec<u8>, value: M31) {
    out.extend_from_slice(&value.as_u32().to_le_bytes());
}

fn write_qm31(out: &mut Vec<u8>, value: Qm31) {
    for limb in value.to_m31_array() {
        write_m31(out, limb);
    }
}

fn write_m31_block(out: &mut Vec<u8>, values: [M31; 4]) {
    for value in values {
        write_m31(out, value);
    }
}

fn write_qm31_block(out: &mut Vec<u8>, values: [Qm31; 4]) {
    for value in values {
        write_qm31(out, value);
    }
}

fn read_merkle_proof(bytes: &[u8]) -> MerkleProof {
    let mut siblings = Vec::with_capacity(bytes.len() / 32);
    for chunk in bytes.chunks_exact(32) {
        let mut hash = [0_u8; 32];
        hash.copy_from_slice(chunk);
        siblings.push(hash);
    }
    MerkleProof { siblings }
}

fn read_u16(bytes: &[u8], offset: usize) -> Result<u16, ParseError> {
    if offset + 2 > bytes.len() {
        return Err(ParseError::Length);
    }
    let mut raw = [0_u8; 2];
    raw.copy_from_slice(&bytes[offset..offset + 2]);
    Ok(u16::from_le_bytes(raw))
}

fn read_u32(bytes: &[u8], offset: usize) -> Result<u32, ParseError> {
    if offset + 4 > bytes.len() {
        return Err(ParseError::Length);
    }
    let mut raw = [0_u8; 4];
    raw.copy_from_slice(&bytes[offset..offset + 4]);
    Ok(u32::from_le_bytes(raw))
}

fn read_m31(bytes: &[u8], offset: usize) -> Result<M31, ParseError> {
    let value = read_u32(bytes, offset)?;
    M31::from_canonical_u32(value).ok_or(ParseError::CanonicalField)
}

fn read_qm31(bytes: &[u8], offset: usize) -> Result<Qm31, ParseError> {
    Ok(Qm31::from_m31_array([
        read_m31(bytes, offset)?,
        read_m31(bytes, offset + 4)?,
        read_m31(bytes, offset + 8)?,
        read_m31(bytes, offset + 12)?,
    ]))
}

fn read_m31_block(bytes: &[u8]) -> Result<[M31; 4], ParseError> {
    Ok([
        read_m31(bytes, 0)?,
        read_m31(bytes, 4)?,
        read_m31(bytes, 8)?,
        read_m31(bytes, 12)?,
    ])
}

fn read_qm31_block(bytes: &[u8]) -> Result<[Qm31; 4], ParseError> {
    Ok([
        read_qm31(bytes, 0)?,
        read_qm31(bytes, 16)?,
        read_qm31(bytes, 32)?,
        read_qm31(bytes, 48)?,
    ])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{local_interpolant_m31, local_interpolant_qm31};
    use crate::profile::{profile_manifest, ProfileId};

    fn sample_env(profile: &'static WhirProfileManifest) -> WhirEnvelopeV1 {
        let mut roots = Vec::new();
        let mut round = 0;
        while round < profile.round_count() {
            roots.push(CommitmentRoot([round as u8; 32]));
            round += 1;
        }
        let mut rounds = Vec::new();
        round = 0;
        while round < profile.round_count() {
            let mut openings = Vec::new();
            let mut repetition = 0;
            while repetition < profile.query_repetitions_per_round as usize {
                openings.push(QueryOpening {
                    current_block: if round == 0 {
                        QueryBlock::M31(local_interpolant_m31([
                            M31::from(3u32),
                            M31::from(5u32),
                            M31::from(7u32),
                            M31::from(11u32),
                        ]))
                    } else {
                        QueryBlock::QM31(local_interpolant_qm31([
                            Qm31::from_u32_unchecked(1, 0, 0, 0),
                            Qm31::from_u32_unchecked(2, 0, 0, 0),
                            Qm31::from_u32_unchecked(3, 0, 0, 0),
                            Qm31::from_u32_unchecked(5, 0, 0, 0),
                        ]))
                    },
                    current_path: MerkleProof {
                        siblings: vec![[repetition as u8; 32]; profile.current_merkle_depth(round)],
                    },
                    next_block: if round + 1 < profile.round_count() {
                        Some(local_interpolant_qm31([
                            Qm31::from_u32_unchecked(13, 0, 0, 0),
                            Qm31::from_u32_unchecked(17, 0, 0, 0),
                            Qm31::from_u32_unchecked(19, 0, 0, 0),
                            Qm31::from_u32_unchecked(23, 0, 0, 0),
                        ]))
                    } else {
                        None
                    },
                    next_path: if round + 1 < profile.round_count() {
                        Some(MerkleProof {
                            siblings: vec![[round as u8; 32]; profile.next_merkle_depth(round)],
                        })
                    } else {
                        None
                    },
                });
                repetition += 1;
            }
            rounds.push(FoldRoundProof { openings });
            round += 1;
        }
        WhirEnvelopeV1 {
            profile_id: profile.id,
            hash_mode: profile.hash_mode,
            fold_mode: profile.fold_mode,
            statement_binding_version: profile.statement_binding_version,
            statement_digest: [9_u8; 32],
            proof: WhirProofV0 {
                commitments: TranscriptCommitmentSection {
                    round_roots: roots,
                    final_value: Qm31::from_u32_unchecked(29, 0, 0, 0),
                },
                rounds,
            },
        }
    }

    #[test]
    fn encode_decode_round_trip() {
        let profile = profile_manifest(ProfileId::WhirM31DevV0);
        let env = sample_env(profile);
        let bytes = env.encode(profile);
        let decoded = WhirEnvelopeV1::decode_owned(profile, &bytes).unwrap();
        assert_eq!(env, decoded);
    }

    #[test]
    fn rejects_non_canonical_qm31_limb() {
        let profile = profile_manifest(ProfileId::WhirM31DevV0);
        let env = sample_env(profile);
        let mut bytes = env.encode(profile);
        let final_offset = HEADER_BYTES + profile.round_count() * 32;
        bytes[final_offset..final_offset + 4]
            .copy_from_slice(&crate::field::M31_MODULUS.to_le_bytes());
        assert_eq!(
            WhirEnvelopeV1::decode_owned(profile, &bytes).unwrap_err(),
            ParseError::CanonicalField
        );
    }
}
