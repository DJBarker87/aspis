//! Aspis on-chain verifier (Stage 0 slice).
//!
//! The program is the crate seam the design cares about: it parses and
//! verifies proof envelopes against a statement digest and knows nothing
//! about spends. Staged upload follows the Yano pattern: a proof account is
//! populated chunk by chunk, then `Verify` runs `aspis_core::verify` over it
//! with the SHA-256 syscall as the hash backend.
//!
//! Proof account layout:
//! [0..4] magic "ASPU", [4..8] proof_len u32 LE, [8..40] upload authority,
//! [40..40+proof_len] proof bytes.

use borsh::{BorshDeserialize, BorshSerialize};
#[cfg(not(feature = "no-entrypoint"))]
use solana_program::entrypoint;
use solana_program::{
    account_info::{next_account_info, AccountInfo},
    declare_id,
    entrypoint::ProgramResult,
    hash::hashv,
    log::sol_log_compute_units,
    msg,
    program_error::ProgramError,
    pubkey::Pubkey,
};

declare_id!("2Ao6ThT7qABozK7zD7UwSsAC64zyZY34TfSB8TAYPxTD");

const PROOF_ACCOUNT_MAGIC: [u8; 4] = *b"ASPU";
pub const PROOF_ACCOUNT_HEADER_LEN: usize = 40;
const AUTHORITY_OFFSET: usize = 8;

#[derive(Clone, Debug, BorshSerialize, BorshDeserialize)]
pub enum AspisInstruction {
    /// Set the proof length header. Account must be pre-created with owner =
    /// this program and space >= 4 + total_len.
    InitProof { total_len: u32 },
    /// Copy `chunk` into the proof body at `offset`.
    UploadChunk { offset: u32, chunk: Vec<u8> },
    /// Verify the uploaded proof against `statement_digest`.
    Verify { statement_digest: [u8; 32] },
    /// Diagnostic verifier run with CU markers in the simulation logs.
    VerifyProfile { statement_digest: [u8; 32] },
    /// Synthetic wide-row layout probe for the Stage 2 layout decision.
    LayoutProbe {
        log_rows: u8,
        columns: u16,
        query_count: u16,
        leaf_bytes: u16,
    },
    /// Known-answer transcript vector: recompute `aspis_core::transcript_kat`
    /// with the SHA-256 syscall backend and compare against the host-pinned
    /// digest supplied by the client. A mismatch is a host/SBF transcript
    /// divergence and errors loudly.
    TranscriptKat { expected: [u8; 32] },
    /// Pure-compute Stage 2 measurement. This runs the extension-field
    /// constraint composition in isolation and requires no accounts.
    ConstraintCompositionProbe {
        opened_values: u16,
        poseidon_sbox_terms: u16,
        poseidon_linear_terms: u16,
        logup_degree3_terms: u16,
        range_bit_terms: u16,
        eq_variables: u8,
        optimized: bool,
    },
    /// Pure-compute software Poseidon2-M31 permutation measurement.
    Poseidon2Probe { permutations: u16 },
    /// Verify a claim-carrying proof. The (z, v) evaluation claim is a public
    /// input (16-byte LE QM31 coordinates + value), transcript-absorbed and
    /// enforced by the interleaved relation sumcheck.
    VerifyWithClaim {
        statement_digest: [u8; 32],
        claim_z: Vec<[u8; 16]>,
        claim_v: [u8; 16],
    },
}

fn run_poseidon2_probe(permutations: u16) -> ProgramResult {
    if permutations > 128 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let mut state = core::array::from_fn(|index| aspis_core::field::M31(index as u32 + 1));
    for iteration in 0..permutations {
        state[0] = state[0].add(aspis_core::field::M31(iteration as u32 + 1));
        aspis_statement::poseidon2::permute(&mut state);
    }
    if state[0] == aspis_core::field::M31::ZERO && permutations == u16::MAX {
        Err(ProgramError::InvalidInstructionData)
    } else {
        Ok(())
    }
}

fn run_constraint_composition_probe(
    probe: aspis_statement::CompositionProbe,
    optimized: bool,
) -> ProgramResult {
    if probe.opened_values > 256
        || probe.poseidon_sbox_terms > 256
        || probe.poseidon_linear_terms > 512
        || probe.logup_degree3_terms > 8
        || probe.range_bit_terms > 256
        || probe.eq_variables > 24
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    let result = if optimized {
        aspis_statement::evaluate_composition_probe_optimized(probe)
    } else {
        aspis_statement::evaluate_composition_probe(probe)
    };
    // Keep the dynamic computation observably live without adding a hash or
    // log call to the isolated field-arithmetic measurement.
    if result.accumulator == aspis_core::field::QM31::ZERO
        && result.qm31_multiplications == u32::MAX
    {
        Err(ProgramError::InvalidInstructionData)
    } else {
        Ok(())
    }
}

/// hashv-shaped backend over the Solana SHA-256 syscall.
fn sbf_hashv(inputs: &[&[u8]]) -> [u8; 32] {
    hashv(inputs).to_bytes()
}

fn trace_cu(event: aspis_core::TraceEvent) {
    match event {
        aspis_core::TraceEvent::Start => msg!("aspis-cu:start"),
        aspis_core::TraceEvent::HeaderParsed => msg!("aspis-cu:header_parsed"),
        aspis_core::TraceEvent::TranscriptReady => msg!("aspis-cu:transcript_ready"),
        aspis_core::TraceEvent::LayerOodDone(layer) => msg!("aspis-cu:layer_ood_done:{}", layer),
        aspis_core::TraceEvent::LayerSumcheckDone(layer) => {
            msg!("aspis-cu:layer_sumcheck_done:{}", layer)
        }
        aspis_core::TraceEvent::QueriesReady => msg!("aspis-cu:queries_ready"),
        aspis_core::TraceEvent::LayerStart(layer) => msg!("aspis-cu:layer_start:{}", layer),
        aspis_core::TraceEvent::LayerMerkleDone(layer) => {
            msg!("aspis-cu:layer_merkle_done:{}", layer)
        }
        aspis_core::TraceEvent::LayerFoldDone(layer) => msg!("aspis-cu:layer_fold_done:{}", layer),
        aspis_core::TraceEvent::FinalCheckStart => msg!("aspis-cu:final_check_start"),
        aspis_core::TraceEvent::Done => msg!("aspis-cu:done"),
    }
    sol_log_compute_units();
}

fn run_layout_probe(
    log_rows: u8,
    columns: u16,
    query_count: u16,
    leaf_bytes: u16,
) -> ProgramResult {
    if log_rows > 16 || columns == 0 || query_count == 0 || leaf_bytes == 0 || leaf_bytes > 4096 {
        return Err(ProgramError::InvalidInstructionData);
    }
    msg!(
        "aspis-layout:start log_rows={} columns={} queries={} leaf_bytes={}",
        log_rows,
        columns,
        query_count,
        leaf_bytes
    );
    sol_log_compute_units();

    let leaf = vec![0u8; leaf_bytes as usize];
    let mut acc = [0u8; 32];
    for q in 0..query_count {
        let q_bytes = q.to_le_bytes();
        acc = hashv(&[b"aspis-layout-leaf", &leaf, &q_bytes]).to_bytes();
    }
    msg!("aspis-layout:leaf_hash_done");
    sol_log_compute_units();

    for q in 0..query_count {
        for level in 0..log_rows {
            let q_bytes = q.to_le_bytes();
            let level_bytes = level.to_le_bytes();
            acc = hashv(&[b"aspis-layout-node", &acc, &q_bytes, &level_bytes]).to_bytes();
        }
    }
    msg!("aspis-layout:merkle_done");
    sol_log_compute_units();

    let gamma = aspis_core::field::QM31 {
        c0: aspis_core::field::CM31 {
            a: aspis_core::field::M31(7),
            b: aspis_core::field::M31(11),
        },
        c1: aspis_core::field::CM31 {
            a: aspis_core::field::M31(13),
            b: aspis_core::field::M31(17),
        },
    };
    let mut rlc = aspis_core::field::QM31::ZERO;
    for q in 0..query_count {
        for c in 0..columns {
            let limb = aspis_core::field::CM31::from_m31(aspis_core::field::M31(
                1 + ((q as u32).wrapping_mul(131) + c as u32) % 1_000_000,
            ));
            rlc = rlc.add(gamma.mul_cm31(limb));
        }
    }
    let mut rlc_bytes = [0u8; 16];
    rlc.write_le_bytes(&mut rlc_bytes);
    let digest = hashv(&[b"aspis-layout-rlc", &acc, &rlc_bytes]).to_bytes();
    msg!("aspis-layout:rlc_done");
    sol_log_compute_units();

    if digest[0] == 255 {
        return Err(ProgramError::InvalidInstructionData);
    }
    msg!("aspis-layout:done");
    Ok(())
}

fn verify_uploaded_proof(
    proof_account: &AccountInfo,
    statement_digest: [u8; 32],
    claim: Option<&aspis_core::EvaluationClaim>,
    profile_cu: bool,
) -> ProgramResult {
    let data = proof_account.try_borrow_data()?;
    let total_len = proof_len(&data)?;
    let end = PROOF_ACCOUNT_HEADER_LEN
        .checked_add(total_len)
        .ok_or(ProgramError::InvalidAccountData)?;
    if end > data.len() {
        return Err(ProgramError::InvalidAccountData);
    }
    let proof = &data[PROOF_ACCOUNT_HEADER_LEN..end];
    let trace_fn = if profile_cu {
        Some(trace_cu as _)
    } else {
        None
    };
    let result = aspis_core::verify_with_claim_and_trace(
        proof,
        &statement_digest,
        claim,
        sbf_hashv,
        trace_fn,
    );
    match result {
        Ok(()) => {
            msg!("aspis: proof accepted");
            Ok(())
        }
        Err(err) => {
            msg!("aspis: proof rejected");
            Err(ProgramError::Custom(err.code()))
        }
    }
}

fn proof_account_initialized(data: &[u8]) -> bool {
    data.len() >= PROOF_ACCOUNT_HEADER_LEN && data[0..4] == PROOF_ACCOUNT_MAGIC
}

fn proof_len(data: &[u8]) -> Result<usize, ProgramError> {
    if data.len() < PROOF_ACCOUNT_HEADER_LEN || data[0..4] != PROOF_ACCOUNT_MAGIC {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(u32::from_le_bytes(data[4..8].try_into().unwrap()) as usize)
}

fn require_upload_authority(data: &[u8], authority: &AccountInfo) -> ProgramResult {
    if !authority.is_signer {
        return Err(ProgramError::MissingRequiredSignature);
    }
    if data.len() < PROOF_ACCOUNT_HEADER_LEN || data[0..4] != PROOF_ACCOUNT_MAGIC {
        return Err(ProgramError::InvalidAccountData);
    }
    if data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32] != authority.key.to_bytes() {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}

#[cfg(not(feature = "no-entrypoint"))]
entrypoint!(process_instruction);

pub fn process_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    let instruction = AspisInstruction::try_from_slice(instruction_data)
        .map_err(|_| ProgramError::InvalidInstructionData)?;

    // Pure-compute diagnostic: no accounts required.
    if let AspisInstruction::TranscriptKat { expected } = instruction {
        let digest = aspis_core::transcript::transcript_kat(sbf_hashv);
        return if digest == expected {
            msg!("aspis: transcript KAT matched");
            Ok(())
        } else {
            msg!("aspis: transcript KAT MISMATCH (host/SBF divergence)");
            Err(ProgramError::InvalidInstructionData)
        };
    }
    if let AspisInstruction::ConstraintCompositionProbe {
        opened_values,
        poseidon_sbox_terms,
        poseidon_linear_terms,
        logup_degree3_terms,
        range_bit_terms,
        eq_variables,
        optimized,
    } = instruction
    {
        return run_constraint_composition_probe(
            aspis_statement::CompositionProbe {
                opened_values,
                poseidon_sbox_terms,
                poseidon_linear_terms,
                logup_degree3_terms,
                range_bit_terms,
                eq_variables,
            },
            optimized,
        );
    }
    if let AspisInstruction::Poseidon2Probe { permutations } = instruction {
        return run_poseidon2_probe(permutations);
    }

    let account_iter = &mut accounts.iter();
    let proof_account = next_account_info(account_iter)?;
    if proof_account.owner != program_id {
        return Err(ProgramError::IncorrectProgramId);
    }

    match instruction {
        AspisInstruction::InitProof { total_len } => {
            let authority = next_account_info(account_iter)?;
            if !authority.is_signer {
                return Err(ProgramError::MissingRequiredSignature);
            }
            let mut data = proof_account.try_borrow_mut_data()?;
            let required_len = PROOF_ACCOUNT_HEADER_LEN
                .checked_add(total_len as usize)
                .ok_or(ProgramError::InvalidInstructionData)?;
            if data.len() < required_len {
                return Err(ProgramError::AccountDataTooSmall);
            }
            if proof_account_initialized(&data) {
                if data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32] != authority.key.to_bytes() {
                    return Err(ProgramError::InvalidAccountData);
                }
            } else if !proof_account.is_signer {
                return Err(ProgramError::MissingRequiredSignature);
            }
            data[0..4].copy_from_slice(&PROOF_ACCOUNT_MAGIC);
            data[4..8].copy_from_slice(&total_len.to_le_bytes());
            data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32].copy_from_slice(authority.key.as_ref());
            Ok(())
        }
        AspisInstruction::UploadChunk { offset, chunk } => {
            let authority = next_account_info(account_iter)?;
            let mut data = proof_account.try_borrow_mut_data()?;
            require_upload_authority(&data, authority)?;
            let total_len = proof_len(&data)?;
            let start = PROOF_ACCOUNT_HEADER_LEN
                .checked_add(offset as usize)
                .ok_or(ProgramError::InvalidInstructionData)?;
            let end = start
                .checked_add(chunk.len())
                .ok_or(ProgramError::InvalidInstructionData)?;
            if offset as usize + chunk.len() > total_len || end > data.len() {
                return Err(ProgramError::InvalidInstructionData);
            }
            data[start..end].copy_from_slice(&chunk);
            Ok(())
        }
        AspisInstruction::Verify { statement_digest } => {
            verify_uploaded_proof(proof_account, statement_digest, None, false)
        }
        AspisInstruction::VerifyProfile { statement_digest } => {
            verify_uploaded_proof(proof_account, statement_digest, None, true)
        }
        AspisInstruction::VerifyWithClaim {
            statement_digest,
            claim_z,
            claim_v,
        } => {
            let z = claim_z
                .iter()
                .map(|bytes| aspis_core::field::QM31::from_le_bytes(bytes))
                .collect::<Option<Vec<_>>>()
                .ok_or(ProgramError::InvalidInstructionData)?;
            let v = aspis_core::field::QM31::from_le_bytes(&claim_v)
                .ok_or(ProgramError::InvalidInstructionData)?;
            let claim = aspis_core::EvaluationClaim { z, v };
            verify_uploaded_proof(proof_account, statement_digest, Some(&claim), false)
        }
        AspisInstruction::LayoutProbe {
            log_rows,
            columns,
            query_count,
            leaf_bytes,
        } => run_layout_probe(log_rows, columns, query_count, leaf_bytes),
        // handled before account resolution above
        AspisInstruction::TranscriptKat { .. } => unreachable!(),
        AspisInstruction::ConstraintCompositionProbe { .. } => unreachable!(),
        AspisInstruction::Poseidon2Probe { .. } => unreachable!(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use solana_program::{account_info::AccountInfo, clock::Epoch};

    #[test]
    fn constraint_composition_probe_requires_no_accounts() {
        let probe = aspis_statement::CompositionProbe::OPTIMISTIC;
        let instruction = AspisInstruction::ConstraintCompositionProbe {
            opened_values: probe.opened_values,
            poseidon_sbox_terms: probe.poseidon_sbox_terms,
            poseidon_linear_terms: probe.poseidon_linear_terms,
            logup_degree3_terms: probe.logup_degree3_terms,
            range_bit_terms: probe.range_bit_terms,
            eq_variables: probe.eq_variables,
            optimized: false,
        };
        assert_eq!(
            process_instruction(&id(), &[], &borsh::to_vec(&instruction).unwrap()),
            Ok(())
        );
    }

    #[test]
    fn poseidon2_probe_requires_no_accounts() {
        let instruction = AspisInstruction::Poseidon2Probe { permutations: 2 };
        assert_eq!(
            process_instruction(&id(), &[], &borsh::to_vec(&instruction).unwrap()),
            Ok(())
        );
    }

    fn make_account<'a>(
        key: &'a Pubkey,
        owner: &'a Pubkey,
        lamports: &'a mut u64,
        data: &'a mut [u8],
        is_signer: bool,
        is_writable: bool,
    ) -> AccountInfo<'a> {
        AccountInfo::new(
            key,
            is_signer,
            is_writable,
            lamports,
            data,
            owner,
            false,
            Epoch::default(),
        )
    }

    #[test]
    fn init_requires_authority_signature() {
        let program_id = id();
        let proof_key = Pubkey::new_unique();
        let authority_key = Pubkey::new_unique();
        let mut proof_lamports = 0;
        let mut authority_lamports = 0;
        let mut proof_data = [0u8; PROOF_ACCOUNT_HEADER_LEN + 8];
        let mut authority_data = [];
        let proof = make_account(
            &proof_key,
            &program_id,
            &mut proof_lamports,
            &mut proof_data,
            true,
            true,
        );
        let authority = make_account(
            &authority_key,
            &program_id,
            &mut authority_lamports,
            &mut authority_data,
            false,
            false,
        );
        let ix = borsh::to_vec(&AspisInstruction::InitProof { total_len: 8 }).unwrap();
        assert_eq!(
            process_instruction(&program_id, &[proof, authority], &ix),
            Err(ProgramError::MissingRequiredSignature)
        );
    }

    #[test]
    fn upload_rejects_wrong_authority() {
        let program_id = id();
        let proof_key = Pubkey::new_unique();
        let authority_key = Pubkey::new_unique();
        let wrong_key = Pubkey::new_unique();
        let mut proof_lamports = 0;
        let mut authority_lamports = 0;
        let mut wrong_lamports = 0;
        let mut proof_data = [0u8; PROOF_ACCOUNT_HEADER_LEN + 8];
        let mut authority_data = [];
        let mut wrong_data = [];

        let init_ix = borsh::to_vec(&AspisInstruction::InitProof { total_len: 8 }).unwrap();
        {
            let proof = make_account(
                &proof_key,
                &program_id,
                &mut proof_lamports,
                &mut proof_data,
                true,
                true,
            );
            let authority = make_account(
                &authority_key,
                &program_id,
                &mut authority_lamports,
                &mut authority_data,
                true,
                false,
            );
            assert_eq!(
                process_instruction(&program_id, &[proof, authority], &init_ix),
                Ok(())
            );
        }

        let upload_ix = borsh::to_vec(&AspisInstruction::UploadChunk {
            offset: 0,
            chunk: vec![1, 2, 3, 4],
        })
        .unwrap();
        let proof = make_account(
            &proof_key,
            &program_id,
            &mut proof_lamports,
            &mut proof_data,
            false,
            true,
        );
        let wrong = make_account(
            &wrong_key,
            &program_id,
            &mut wrong_lamports,
            &mut wrong_data,
            true,
            false,
        );
        assert_eq!(
            process_instruction(&program_id, &[proof, wrong], &upload_ix),
            Err(ProgramError::InvalidAccountData)
        );
    }

    #[test]
    fn verify_rejects_short_account_without_panicking() {
        let program_id = id();
        let proof_key = Pubkey::new_unique();
        let mut proof_lamports = 0;
        let mut proof_data = [0u8; 2];
        let proof = make_account(
            &proof_key,
            &program_id,
            &mut proof_lamports,
            &mut proof_data,
            false,
            false,
        );
        let ix = borsh::to_vec(&AspisInstruction::Verify {
            statement_digest: [0u8; 32],
        })
        .unwrap();
        assert_eq!(
            process_instruction(&program_id, &[proof], &ix),
            Err(ProgramError::InvalidAccountData)
        );
    }

    /// End-to-end instruction-path test for `VerifyWithClaim` (review Low):
    /// a real claim-carrying proof through the program dispatch, with the
    /// non-SBF hashv fallback standing in for the syscall (the transcript
    /// KAT covers host/SBF hash equivalence separately).
    #[test]
    fn verify_with_claim_instruction_paths() {
        use aspis_core::params::PROFILE_CAPACITY_LR10_Q32_G16 as PROFILE;
        use aspis_prover::{multilinear_eval, prove_with_claim, seeded_coeffs, ProveOptions};

        let coeffs = seeded_coeffs(PROFILE.log_rows, 5);
        let statement_digest = [0x42u8; 32];
        let z: Vec<aspis_core::field::QM31> = (0..PROFILE.log_rows)
            .map(|i| {
                aspis_core::field::QM31::from_cm31(aspis_core::field::CM31::from_m31(
                    aspis_core::field::M31(1000 + i),
                ))
            })
            .collect();
        let claim = aspis_core::EvaluationClaim {
            v: multilinear_eval(&coeffs, &z),
            z,
        };
        let proof = prove_with_claim(
            &PROFILE,
            &coeffs,
            &statement_digest,
            &claim,
            &ProveOptions {
                fold_payload: aspis_core::FoldPayload::RawFibers,
                merkle_mode: aspis_core::MerkleMode::MinimalSubtree,
            },
            aspis_prover::HOST_HASH,
        );

        // proof account: ASPU magic, len, authority, proof bytes
        let program_id = id();
        let proof_key = Pubkey::new_unique();
        let mut proof_lamports = 0;
        let mut proof_data = vec![0u8; PROOF_ACCOUNT_HEADER_LEN + proof.len()];
        proof_data[0..4].copy_from_slice(&PROOF_ACCOUNT_MAGIC);
        proof_data[4..8].copy_from_slice(&(proof.len() as u32).to_le_bytes());
        proof_data[PROOF_ACCOUNT_HEADER_LEN..].copy_from_slice(&proof);

        let claim_z: Vec<[u8; 16]> = claim
            .z
            .iter()
            .map(|zi| {
                let mut b = [0u8; 16];
                zi.write_le_bytes(&mut b);
                b
            })
            .collect();
        let mut claim_v = [0u8; 16];
        claim.v.write_le_bytes(&mut claim_v);

        // correct claim accepts through the instruction path
        {
            let account = make_account(
                &proof_key,
                &program_id,
                &mut proof_lamports,
                &mut proof_data,
                false,
                false,
            );
            let ix = borsh::to_vec(&AspisInstruction::VerifyWithClaim {
                statement_digest,
                claim_z: claim_z.clone(),
                claim_v,
            })
            .unwrap();
            assert_eq!(process_instruction(&program_id, &[account], &ix), Ok(()));
        }

        // perturbed claim value rejects (transcript binding)
        {
            let account = make_account(
                &proof_key,
                &program_id,
                &mut proof_lamports,
                &mut proof_data,
                false,
                false,
            );
            let mut wrong_v = claim_v;
            wrong_v[0] ^= 1;
            let ix = borsh::to_vec(&AspisInstruction::VerifyWithClaim {
                statement_digest,
                claim_z: claim_z.clone(),
                claim_v: wrong_v,
            })
            .unwrap();
            assert!(matches!(
                process_instruction(&program_id, &[account], &ix),
                Err(ProgramError::Custom(_))
            ));
        }

        // claim-carrying proof through the plain Verify path rejects with
        // ClaimMissing (code 14)
        {
            let account = make_account(
                &proof_key,
                &program_id,
                &mut proof_lamports,
                &mut proof_data,
                false,
                false,
            );
            let ix = borsh::to_vec(&AspisInstruction::Verify { statement_digest }).unwrap();
            assert_eq!(
                process_instruction(&program_id, &[account], &ix),
                Err(ProgramError::Custom(
                    aspis_core::VerifyError::ClaimMissing.code()
                ))
            );
        }
    }
}
