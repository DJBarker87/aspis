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

#[derive(Clone, Copy, Debug, BorshSerialize, BorshDeserialize)]
pub enum ZkKernelKind {
    M31InverseSoftware,
    M31InverseSyscall,
    Qm31SquareGeneric,
    Qm31SquareSpecialized,
    M31Pow2Generic,
    M31Pow2Shift,
}

#[derive(Clone, Debug, BorshSerialize, BorshDeserialize)]
pub enum AspisInstruction {
    /// Set the proof length header. Account must be pre-created with owner =
    /// this program and space >= 4 + total_len.
    InitProof { total_len: u32 },
    /// Copy `chunk` into the proof body at `offset`.
    UploadChunk { offset: u32, chunk: Vec<u8> },
    /// Verify the uploaded proof against `statement_digest` with the selected
    /// cached-domain and unit-circle-conjugate kernels.
    Verify { statement_digest: [u8; 32] },
    /// Compatibility alias for the optimized verifier, retained so existing
    /// Stage-2 measurement transactions remain decodable.
    VerifyFast { statement_digest: [u8; 32] },
    /// Legacy batch-denominator verifier with `sol_big_mod_exp` supplying its
    /// one M31 inverse per round. Measurement-only comparison path.
    VerifySyscallInverse { statement_digest: [u8; 32] },
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
    /// The same permutation using lazy M31 linear layers and power-of-two
    /// shifts. Kept as a separate instruction so the SBF delta is literal.
    Poseidon2OptimizedProbe { permutations: u16 },
    /// Microbench reusable field kernels proposed for a `solmath-zk` crate.
    ZkKernelProbe { kind: ZkKernelKind, iterations: u16 },
    /// Correct wide-column gamma RLC probe. Kernel 0 is precomputed powers,
    /// 1 is a four-product lazy dot, 2 is per-query Horner, 3/4 pack four
    /// M31 columns into QM31, 5 packs pairs into CM31, 6 uses whole-dot u128
    /// accumulation, 7 lazily accumulates four-term block reductions, and 8
    /// specializes that winner to fixed stack-backed k=80 tables.
    WideRlcProbe {
        columns: u16,
        query_count: u16,
        kernel: u8,
    },
    /// Synthetic minimal-subtree traversal with current binary nodes or
    /// candidate radix-4 nodes. Leaf hashing is deliberately excluded.
    MerkleArityProbe {
        depth: u8,
        query_count: u16,
        arity: u8,
    },
    /// Verify a claim-carrying proof. The (z, v) evaluation claim is a public
    /// input (16-byte LE QM31 coordinates + value), transcript-absorbed and
    /// enforced by the interleaved relation sumcheck.
    VerifyWithClaim {
        statement_digest: [u8; 32],
        claim_z: Vec<[u8; 16]>,
        claim_v: [u8; 16],
    },
    /// Pre-optimization software-batch denominator path. Appended to preserve
    /// every existing Borsh instruction discriminant; measurement only.
    VerifyLegacySoftware { statement_digest: [u8; 32] },
}

fn run_poseidon2_probe(permutations: u16, optimized: bool) -> ProgramResult {
    if permutations > 128 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let mut state = core::array::from_fn(|index| aspis_core::field::M31(index as u32 + 1));
    for iteration in 0..permutations {
        state[0] = state[0].add(aspis_core::field::M31(iteration as u32 + 1));
        if optimized {
            aspis_statement::poseidon2::permute_optimized(&mut state);
        } else {
            aspis_statement::poseidon2::permute(&mut state);
        }
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

#[allow(unexpected_cfgs)]
#[inline(always)]
fn m31_inverse_syscall(value: aspis_core::field::M31) -> aspis_core::field::M31 {
    #[cfg(target_os = "solana")]
    {
        #[repr(C)]
        struct BigModExpParams {
            base: *const u8,
            base_len: u64,
            exponent: *const u8,
            exponent_len: u64,
            modulus: *const u8,
            modulus_len: u64,
        }

        let base = value.0.to_be_bytes();
        let exponent = (aspis_core::field::P - 2).to_be_bytes();
        let modulus = aspis_core::field::P.to_be_bytes();
        let mut output = [0u8; 4];
        let params = BigModExpParams {
            base: base.as_ptr(),
            base_len: base.len() as u64,
            exponent: exponent.as_ptr(),
            exponent_len: exponent.len() as u64,
            modulus: modulus.as_ptr(),
            modulus_len: modulus.len() as u64,
        };
        #[allow(deprecated)]
        unsafe {
            solana_program::syscalls::sol_big_mod_exp(
                &params as *const _ as *const u8,
                output.as_mut_ptr(),
            );
        }
        aspis_core::field::M31(u32::from_be_bytes(output))
    }
    #[cfg(not(target_os = "solana"))]
    {
        value.inv()
    }
}

fn run_zk_kernel_probe(kind: ZkKernelKind, iterations: u16) -> ProgramResult {
    use aspis_core::field::{CM31, M31, QM31};

    if iterations > 8_192 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let mut scalar = M31(17);
    let mut extension = QM31 {
        c0: CM31::new(M31(3), M31(5)),
        c1: CM31::new(M31(7), M31(11)),
    };
    for iteration in 0..iterations {
        let step = M31(1 + iteration as u32 % 1_000);
        match kind {
            ZkKernelKind::M31InverseSoftware => {
                scalar = scalar.add(step).inv();
            }
            ZkKernelKind::M31InverseSyscall => {
                scalar = m31_inverse_syscall(scalar.add(step));
            }
            ZkKernelKind::Qm31SquareGeneric => {
                extension.c0.a = extension.c0.a.add(step);
                extension = extension.mul(extension);
                scalar = scalar.add(extension.c0.a);
            }
            ZkKernelKind::Qm31SquareSpecialized => {
                extension.c0.a = extension.c0.a.add(step);
                extension = extension.square();
                scalar = scalar.add(extension.c0.a);
            }
            ZkKernelKind::M31Pow2Generic => {
                let shift = (iteration % 17) as u8;
                scalar = scalar.add(step).mul(M31(1u32 << shift));
            }
            ZkKernelKind::M31Pow2Shift => {
                let shift = (iteration % 17) as u8;
                scalar = scalar.add(step).mul_pow2(shift);
            }
        }
    }
    if scalar == M31::ZERO {
        Err(ProgramError::InvalidInstructionData)
    } else {
        Ok(())
    }
}

fn run_wide_rlc_probe(columns: u16, query_count: u16, kernel: u8) -> ProgramResult {
    use aspis_core::field::{
        qm31_cm31_dot, qm31_dot, qm31_m31_dot, qm31_m31_dot_eager_outer, qm31_m31_dot_u128, CM31,
        M31, QM31,
    };

    if columns == 0
        || columns > 256
        || query_count > 64
        || kernel > 11
        || (kernel == 8 && columns != 80)
        || (kernel == 9 && columns != 84)
        || (kernel == 10 && columns != 67)
        || (kernel == 11 && columns != 65)
        || ((kernel == 3 || kernel == 4) && columns % 4 != 0)
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    let gamma = QM31 {
        c0: CM31::new(M31(7), M31(11)),
        c1: CM31::new(M31(13), M31(17)),
    };
    // Fixed-width variants of the winning outer-lazy kernel: 80 is the
    // historical k80 candidate, 84 the k'<=84 pin, 67 the r=3 layout
    // candidate, 65 the r=3 + LogUp-GKR (no committed helpers) candidate.
    match kernel {
        8 => return run_wide_rlc_fixed::<80>(query_count, gamma),
        9 => return run_wide_rlc_fixed::<84>(query_count, gamma),
        10 => return run_wide_rlc_fixed::<67>(query_count, gamma),
        11 => return run_wide_rlc_fixed::<65>(query_count, gamma),
        _ => {}
    }
    let coefficient_count = if kernel == 5 {
        columns / 2
    } else if kernel == 3 || kernel == 4 {
        columns / 4
    } else {
        columns
    };
    let mut powers = Vec::with_capacity(coefficient_count as usize);
    if kernel != 2 {
        let mut power = QM31::ONE;
        for _ in 0..coefficient_count {
            powers.push(power);
            power = power.mul(gamma);
        }
    }
    let mut values = Vec::with_capacity(columns as usize);
    let mut packed_values = Vec::with_capacity((columns / 4) as usize);
    let mut paired_values = Vec::with_capacity((columns / 2) as usize);
    let mut sink = QM31::ONE;
    for query in 0..query_count {
        values.clear();
        for column in 0..columns {
            let seed = 1 + (query as u32 * 131 + column as u32 * 17) % 1_000_000;
            values.push(M31(seed));
        }
        if kernel == 5 {
            paired_values.clear();
            for chunk in values.chunks_exact(2) {
                paired_values.push(CM31::new(chunk[0], chunk[1]));
            }
        } else if kernel == 3 || kernel == 4 {
            packed_values.clear();
            for chunk in values.chunks_exact(4) {
                packed_values.push(QM31 {
                    c0: CM31::new(chunk[0], chunk[1]),
                    c1: CM31::new(chunk[2], chunk[3]),
                });
            }
        }
        let rlc = match kernel {
            0 => powers
                .iter()
                .zip(&values)
                .fold(QM31::ZERO, |sum, (power, value)| {
                    sum.add(power.mul_m31(*value))
                }),
            1 => qm31_m31_dot_eager_outer(&powers, &values),
            2 => values.iter().rev().fold(QM31::ZERO, |accumulator, value| {
                accumulator
                    .mul(gamma)
                    .add(QM31::from_cm31(CM31::from_m31(*value)))
            }),
            3 => qm31_dot(&powers, &packed_values),
            4 => powers
                .iter()
                .zip(&packed_values)
                .fold(QM31::ZERO, |sum, (power, value)| sum.add(power.mul(*value))),
            5 => qm31_cm31_dot(&powers, &paired_values),
            6 => qm31_m31_dot_u128(&powers, &values),
            7 => qm31_m31_dot(&powers, &values),
            _ => unreachable!(),
        };
        sink = sink.add(rlc);
    }
    if sink == QM31::ZERO {
        Err(ProgramError::InvalidInstructionData)
    } else {
        Ok(())
    }
}

#[inline(never)]
fn run_wide_rlc_fixed<const N: usize>(
    query_count: u16,
    gamma: aspis_core::field::QM31,
) -> ProgramResult {
    use aspis_core::field::{qm31_m31_dot, qm31_power_table, M31, QM31};

    let powers = qm31_power_table::<N>(gamma);
    let mut values = [M31::ZERO; N];
    let mut sink = QM31::ONE;
    for query in 0..query_count {
        for (column, value) in values.iter_mut().enumerate() {
            let seed = 1 + (query as u32 * 131 + column as u32 * 17) % 1_000_000;
            *value = M31(seed);
        }
        sink = sink.add(qm31_m31_dot(&powers, &values));
    }
    if sink == QM31::ZERO {
        Err(ProgramError::InvalidInstructionData)
    } else {
        Ok(())
    }
}

fn run_merkle_arity_probe(depth: u8, query_count: u16, arity: u8) -> ProgramResult {
    if depth == 0
        || depth > 16
        || query_count == 0
        || query_count > 64
        || (arity != 2 && arity != 4)
        || (arity == 4 && depth % 2 != 0)
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    let mask = (1u32 << depth) - 1;
    let mut level = Vec::with_capacity(query_count as usize);
    for query in 0..query_count {
        let index = (query as u32)
            .wrapping_mul(0x9e37_79b9)
            .wrapping_add(0x7f4a_7c15)
            & mask;
        let mut value = [0u8; 32];
        value[0..4].copy_from_slice(&index.to_le_bytes());
        level.push((index, value));
    }
    level.sort_unstable_by_key(|entry| entry.0);
    level.dedup_by_key(|entry| entry.0);
    let mut next = Vec::with_capacity(level.len());
    if arity == 2 {
        for _ in 0..depth {
            next.clear();
            let mut position = 0usize;
            while position < level.len() {
                let (index, hash) = level[position];
                let parent = if index & 1 == 0
                    && position + 1 < level.len()
                    && level[position + 1].0 == index + 1
                {
                    let parent =
                        aspis_core::merkle::node_hash(sbf_hashv, &hash, &level[position + 1].1);
                    position += 2;
                    parent
                } else {
                    let sibling = [0u8; 32];
                    position += 1;
                    if index & 1 == 0 {
                        aspis_core::merkle::node_hash(sbf_hashv, &hash, &sibling)
                    } else {
                        aspis_core::merkle::node_hash(sbf_hashv, &sibling, &hash)
                    }
                };
                next.push((index >> 1, parent));
            }
            core::mem::swap(&mut level, &mut next);
        }
    } else {
        for _ in 0..depth / 2 {
            next.clear();
            let mut position = 0usize;
            while position < level.len() {
                let parent_index = level[position].0 >> 2;
                let mut children = [[0u8; 32]; 4];
                while position < level.len() && level[position].0 >> 2 == parent_index {
                    let slot = (level[position].0 & 3) as usize;
                    children[slot] = level[position].1;
                    position += 1;
                }
                let mut input = [0u8; 129];
                input[0] = 0x12;
                for (slot, child) in children.iter().enumerate() {
                    input[1 + slot * 32..1 + (slot + 1) * 32].copy_from_slice(child);
                }
                next.push((parent_index, sbf_hashv(&[&input])));
            }
            core::mem::swap(&mut level, &mut next);
        }
    }
    if level.len() == 1 && level[0].1 != [0u8; 32] {
        Ok(())
    } else {
        Err(ProgramError::InvalidInstructionData)
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
    denominator_mode: u8,
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
    let result = if denominator_mode == 2 {
        aspis_core::verify_with_claim_trace_and_inverse(
            proof,
            &statement_digest,
            claim,
            sbf_hashv,
            trace_fn,
            m31_inverse_syscall,
        )
    } else if denominator_mode == 1 {
        aspis_core::verify_with_claim_and_trace(
            proof,
            &statement_digest,
            claim,
            sbf_hashv,
            trace_fn,
        )
    } else {
        aspis_core::verify_with_claim_trace_and_inverse(
            proof,
            &statement_digest,
            claim,
            sbf_hashv,
            trace_fn,
            aspis_core::field::M31::inv,
        )
    };
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
        return run_poseidon2_probe(permutations, false);
    }
    if let AspisInstruction::Poseidon2OptimizedProbe { permutations } = instruction {
        return run_poseidon2_probe(permutations, true);
    }
    if let AspisInstruction::ZkKernelProbe { kind, iterations } = instruction {
        return run_zk_kernel_probe(kind, iterations);
    }
    if let AspisInstruction::WideRlcProbe {
        columns,
        query_count,
        kernel,
    } = instruction
    {
        return run_wide_rlc_probe(columns, query_count, kernel);
    }
    if let AspisInstruction::MerkleArityProbe {
        depth,
        query_count,
        arity,
    } = instruction
    {
        return run_merkle_arity_probe(depth, query_count, arity);
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
            verify_uploaded_proof(proof_account, statement_digest, None, false, 1)
        }
        AspisInstruction::VerifyFast { statement_digest } => {
            verify_uploaded_proof(proof_account, statement_digest, None, false, 1)
        }
        AspisInstruction::VerifySyscallInverse { statement_digest } => {
            verify_uploaded_proof(proof_account, statement_digest, None, false, 2)
        }
        AspisInstruction::VerifyProfile { statement_digest } => {
            verify_uploaded_proof(proof_account, statement_digest, None, true, 1)
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
            verify_uploaded_proof(proof_account, statement_digest, Some(&claim), false, 1)
        }
        AspisInstruction::VerifyLegacySoftware { statement_digest } => {
            verify_uploaded_proof(proof_account, statement_digest, None, false, 0)
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
        AspisInstruction::Poseidon2OptimizedProbe { .. } => unreachable!(),
        AspisInstruction::ZkKernelProbe { .. } => unreachable!(),
        AspisInstruction::WideRlcProbe { .. } => unreachable!(),
        AspisInstruction::MerkleArityProbe { .. } => unreachable!(),
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
        for instruction in [
            AspisInstruction::Poseidon2Probe { permutations: 2 },
            AspisInstruction::Poseidon2OptimizedProbe { permutations: 2 },
        ] {
            assert_eq!(
                process_instruction(&id(), &[], &borsh::to_vec(&instruction).unwrap()),
                Ok(())
            );
        }
    }

    #[test]
    fn zk_kernel_probes_require_no_accounts() {
        for kind in [
            ZkKernelKind::M31InverseSoftware,
            ZkKernelKind::M31InverseSyscall,
            ZkKernelKind::Qm31SquareGeneric,
            ZkKernelKind::Qm31SquareSpecialized,
            ZkKernelKind::M31Pow2Generic,
            ZkKernelKind::M31Pow2Shift,
        ] {
            let instruction = AspisInstruction::ZkKernelProbe {
                kind,
                iterations: 8,
            };
            assert_eq!(
                process_instruction(&id(), &[], &borsh::to_vec(&instruction).unwrap()),
                Ok(())
            );
        }
    }

    #[test]
    fn wide_rlc_kernels_require_no_accounts() {
        for kernel in 0..=6 {
            let instruction = AspisInstruction::WideRlcProbe {
                columns: 8,
                query_count: 3,
                kernel,
            };
            assert_eq!(
                process_instruction(&id(), &[], &borsh::to_vec(&instruction).unwrap()),
                Ok(())
            );
        }
    }

    #[test]
    fn merkle_arity_probes_require_no_accounts() {
        for arity in [2, 4] {
            let instruction = AspisInstruction::MerkleArityProbe {
                depth: 10,
                query_count: 8,
                arity,
            };
            assert_eq!(
                process_instruction(&id(), &[], &borsh::to_vec(&instruction).unwrap()),
                Ok(())
            );
        }
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
