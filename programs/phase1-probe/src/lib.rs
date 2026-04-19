use core::hint::black_box;

use borsh::{to_vec, BorshDeserialize, BorshSerialize};
#[cfg(not(feature = "no-entrypoint"))]
use solana_program::entrypoint;
use solana_program::{
    account_info::{next_account_info, AccountInfo},
    declare_id,
    entrypoint::ProgramResult,
    hash::{hash, hashv},
    instruction::{AccountMeta, Instruction},
    program_error::ProgramError,
    pubkey::Pubkey,
};
use winter_math::{
    fields::{f128::BaseElement, QuadExtension},
    FieldElement, StarkField,
};

mod phase2;
mod real_fri;

pub use phase2::{
    build_phase2_proof_bytes, build_phase2_whir_query_proof_bytes, run_phase2_arithmetic_bench,
    run_phase2_extension_bench, run_phase2_skeleton_verify, run_phase2_whir_query_verify,
    ArithmeticKernelId, ArithmeticWorkloadId, ExtensionKernelId, ExtensionWorkloadId,
    LazyReductionMode, LiftPolicy, MerkleProofMode, Phase2ArithmeticConfig, Phase2Counters,
    Phase2ExtensionConfig, Phase2ProofPlan, Phase2VerifierConfig, Phase2WhirQueryPlan,
    Phase2WhirRoundPlan, Phase2WhirStatementShape, ReductionMode, WhirFoldMode,
    PHASE2_WHIR_MAX_OPENING_TERMS, PHASE2_WHIR_MAX_ROUNDS,
};
pub use real_fri::{run_real_fri_verify, RealFriVerifyOutcome};

declare_id!("Fg6PaFpoGXkYsidMpWTK6W2BeZ7FEfcYkgMQhgqH3R9L");

#[derive(Clone, Copy, Debug, BorshSerialize, BorshDeserialize)]
pub enum MerkleBatchMode {
    Serial,
    Interleaved,
}

#[derive(Clone, Copy, Debug, BorshSerialize, BorshDeserialize)]
pub enum ProofParseFormat {
    FixedWidth,
    Leb128,
}

#[derive(Clone, Copy, Debug, BorshSerialize, BorshDeserialize)]
pub enum FieldKernel {
    AddSub,
    Mul,
    Inv,
    ExtensionMul,
}

#[derive(Clone, Debug, BorshSerialize, BorshDeserialize)]
pub struct SyntheticVerifierProfile {
    pub hash_calls: u32,
    pub bytes_per_hash_call: u32,
    pub merkle_paths: u32,
    pub merkle_depth: u32,
    pub sibling_size: u32,
    pub proof_segments: u32,
    pub field_add_sub_ops: u32,
    pub field_mul_ops: u32,
    pub field_inv_ops: u32,
    pub extension_mul_ops: u32,
    pub fixed_layout: bool,
    pub read_bytes_per_account: u32,
    pub write_bytes_per_account: u32,
}

#[derive(Clone, Debug, BorshSerialize, BorshDeserialize)]
pub enum ProbeInstruction {
    Noop,
    Hash {
        hash_calls: u32,
        bytes_per_call: u32,
    },
    Merkle {
        path_depth: u32,
        path_count: u32,
        sibling_size: u32,
        batch_mode: MerkleBatchMode,
    },
    ParseProof {
        segment_count: u32,
        format: ProofParseFormat,
    },
    FieldOps {
        kernel: FieldKernel,
        iterations: u32,
    },
    HeapProbe {
        scratch_bytes: u32,
        touch_stride: u32,
    },
    PopulateAccounts {
        variable_layout: bool,
        seed: u8,
    },
    AccountIo {
        fixed_layout: bool,
        read_bytes_per_account: u32,
        write_bytes_per_account: u32,
    },
    UploadChunk {
        offset: u32,
        rolling_hash: bool,
        prior_digest: [u8; 32],
        chunk: Vec<u8>,
    },
    SyntheticVerifier {
        profile: SyntheticVerifierProfile,
        format: ProofParseFormat,
        batch_mode: MerkleBatchMode,
    },
    Phase2Arithmetic {
        config: Phase2ArithmeticConfig,
        workload: ArithmeticWorkloadId,
        iterations: u32,
    },
    Phase2Extension {
        config: Phase2ExtensionConfig,
        workload: ExtensionWorkloadId,
        iterations: u32,
    },
    Phase2SkeletonVerify {
        config: Phase2VerifierConfig,
        repeat: u32,
    },
    Phase2WhirQueryVerify {
        config: Phase2VerifierConfig,
        repeat: u32,
    },
    Phase2RealFriVerify {
        seed_u64: u64,
        inc_u64: u64,
        repeat: u32,
    },
}

impl ProbeInstruction {
    pub fn encode(&self) -> Vec<u8> {
        to_vec(self).expect("instruction serialization")
    }

    pub fn instruction(
        program_id: Pubkey,
        accounts: Vec<AccountMeta>,
        payload: Self,
    ) -> Instruction {
        Instruction {
            program_id,
            accounts,
            data: payload.encode(),
        }
    }
}

#[cfg(not(feature = "no-entrypoint"))]
entrypoint!(process_instruction);

pub fn process_instruction(
    _program_id: &Pubkey,
    accounts: &[AccountInfo],
    input: &[u8],
) -> ProgramResult {
    let instruction = ProbeInstruction::try_from_slice(input)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    match instruction {
        ProbeInstruction::Noop => Ok(()),
        ProbeInstruction::Hash {
            hash_calls,
            bytes_per_call,
        } => {
            black_box(run_hash_bench(hash_calls as usize, bytes_per_call as usize));
            Ok(())
        }
        ProbeInstruction::Merkle {
            path_depth,
            path_count,
            sibling_size,
            batch_mode,
        } => {
            black_box(run_merkle_bench(
                path_depth as usize,
                path_count as usize,
                sibling_size as usize,
                batch_mode,
            ));
            Ok(())
        }
        ProbeInstruction::ParseProof {
            segment_count,
            format,
        } => {
            let account = next_account_info(&mut accounts.iter())?;
            let data = account.try_borrow_data()?;
            black_box(parse_proof(&data, segment_count as usize, format)?);
            Ok(())
        }
        ProbeInstruction::FieldOps { kernel, iterations } => {
            black_box(run_field_kernel(kernel, iterations));
            Ok(())
        }
        ProbeInstruction::HeapProbe {
            scratch_bytes,
            touch_stride,
        } => {
            black_box(run_heap_probe(
                scratch_bytes as usize,
                touch_stride.max(1) as usize,
            ));
            Ok(())
        }
        ProbeInstruction::PopulateAccounts {
            variable_layout,
            seed,
        } => populate_accounts(accounts, variable_layout, seed),
        ProbeInstruction::AccountIo {
            fixed_layout,
            read_bytes_per_account,
            write_bytes_per_account,
        } => {
            black_box(run_account_io(
                accounts,
                fixed_layout,
                read_bytes_per_account as usize,
                write_bytes_per_account as usize,
            )?);
            Ok(())
        }
        ProbeInstruction::UploadChunk {
            offset,
            rolling_hash,
            prior_digest,
            chunk,
        } => {
            let account = next_account_info(&mut accounts.iter())?;
            write_upload_chunk(
                account,
                offset as usize,
                rolling_hash,
                &prior_digest,
                &chunk,
            )?;
            Ok(())
        }
        ProbeInstruction::SyntheticVerifier {
            profile,
            format,
            batch_mode,
        } => run_synthetic_verifier(accounts, &profile, format, batch_mode),
        ProbeInstruction::Phase2Arithmetic {
            config,
            workload,
            iterations,
        } => {
            black_box(run_phase2_arithmetic_bench(config, workload, iterations).digest);
            Ok(())
        }
        ProbeInstruction::Phase2Extension {
            config,
            workload,
            iterations,
        } => {
            black_box(run_phase2_extension_bench(config, workload, iterations).digest);
            Ok(())
        }
        ProbeInstruction::Phase2SkeletonVerify { config, repeat } => {
            let proof_account = next_account_info(&mut accounts.iter())?;
            let proof_bytes = proof_account.try_borrow_data()?;
            black_box(
                run_phase2_skeleton_verify(config, &proof_bytes, repeat)
                    .map_err(|_| ProgramError::InvalidInstructionData)?
                    .digest,
            );
            Ok(())
        }
        ProbeInstruction::Phase2WhirQueryVerify { config, repeat } => {
            let proof_account = next_account_info(&mut accounts.iter())?;
            let proof_bytes = proof_account.try_borrow_data()?;
            black_box(
                run_phase2_whir_query_verify(config, &proof_bytes, repeat)
                    .map_err(|_| ProgramError::InvalidInstructionData)?
                    .digest,
            );
            Ok(())
        }
        ProbeInstruction::Phase2RealFriVerify {
            seed_u64,
            inc_u64,
            repeat,
        } => {
            let proof_account = next_account_info(&mut accounts.iter())?;
            let proof_bytes = proof_account.try_borrow_data()?;
            black_box(
                run_real_fri_verify(&proof_bytes, seed_u64, inc_u64, repeat)
                    .map_err(|_| ProgramError::InvalidInstructionData)?
                    .digest,
            );
            Ok(())
        }
    }
}

fn deterministic_bytes(len: usize, seed: u8) -> Vec<u8> {
    let mut bytes = vec![0_u8; len];
    for (index, value) in bytes.iter_mut().enumerate() {
        *value = seed.wrapping_add((index % 251) as u8);
    }
    bytes
}

fn run_hash_bench(hash_calls: usize, bytes_per_call: usize) -> [u8; 32] {
    let payload = deterministic_bytes(bytes_per_call.max(1), 17);
    let mut digest = hash(&[0_u8]);
    for round in 0..hash_calls {
        let round_byte = [round as u8];
        digest = hashv(&[digest.as_ref(), &round_byte, &payload]);
    }
    digest.to_bytes()
}

fn run_merkle_bench(
    path_depth: usize,
    path_count: usize,
    sibling_size: usize,
    batch_mode: MerkleBatchMode,
) -> [u8; 32] {
    let path_count = path_count.max(1);
    let sibling_size = sibling_size.max(32);
    let mut leaves = (0..path_count)
        .map(|index| hash(&deterministic_bytes(32, index as u8)))
        .collect::<Vec<_>>();

    match batch_mode {
        MerkleBatchMode::Serial => {
            for leaf in &mut leaves {
                let mut current = *leaf;
                for level in 0..path_depth {
                    let sibling = deterministic_bytes(sibling_size, (level % 251) as u8);
                    current = hashv(&[current.as_ref(), &sibling]);
                }
                *leaf = current;
            }
        }
        MerkleBatchMode::Interleaved => {
            for level in 0..path_depth {
                for leaf in &mut leaves {
                    let sibling = deterministic_bytes(sibling_size, (level % 251) as u8);
                    *leaf = hashv(&[leaf.as_ref(), &sibling]);
                }
            }
        }
    }

    let mut folded = hash(&[0_u8]);
    for leaf in leaves {
        folded = hashv(&[folded.as_ref(), leaf.as_ref()]);
    }
    folded.to_bytes()
}

fn parse_proof(
    bytes: &[u8],
    segment_count: usize,
    format: ProofParseFormat,
) -> Result<u64, ProgramError> {
    let mut cursor = 0usize;
    let mut checksum = 0u64;
    for segment_index in 0..segment_count {
        let length = match format {
            ProofParseFormat::FixedWidth => {
                if cursor + 4 > bytes.len() {
                    return Err(ProgramError::InvalidInstructionData);
                }
                let mut raw = [0_u8; 4];
                raw.copy_from_slice(&bytes[cursor..cursor + 4]);
                cursor += 4;
                u32::from_le_bytes(raw) as usize
            }
            ProofParseFormat::Leb128 => {
                let (value, consumed) = decode_leb128(&bytes[cursor..])?;
                cursor += consumed;
                value
            }
        };
        let end = cursor.saturating_add(length);
        if end > bytes.len() {
            return Err(ProgramError::InvalidInstructionData);
        }
        for byte in &bytes[cursor..end] {
            checksum = checksum
                .wrapping_mul(16777619)
                .wrapping_add(*byte as u64 + segment_index as u64);
        }
        cursor = end;
    }
    Ok(checksum)
}

fn decode_leb128(bytes: &[u8]) -> Result<(usize, usize), ProgramError> {
    let mut value = 0usize;
    let mut shift = 0usize;
    for (index, byte) in bytes.iter().enumerate() {
        value |= ((byte & 0x7f) as usize) << shift;
        if byte & 0x80 == 0 {
            return Ok((value, index + 1));
        }
        shift += 7;
        if shift >= usize::BITS as usize {
            break;
        }
    }
    Err(ProgramError::InvalidInstructionData)
}

fn run_field_kernel(kernel: FieldKernel, iterations: u32) -> u128 {
    let rounds = iterations.max(1);
    match kernel {
        FieldKernel::AddSub => {
            let mut a = BaseElement::from(7u64);
            let mut b = BaseElement::from(19u64);
            let mut c = BaseElement::from(23u64);
            let d = BaseElement::from(29u64);
            for _ in 0..rounds {
                a += b;
                b -= c;
                c += d;
            }
            a.as_int() ^ b.as_int() ^ c.as_int() ^ d.as_int()
        }
        FieldKernel::Mul => {
            let mut a = BaseElement::from(7u64);
            let mut b = BaseElement::from(19u64);
            let mut c = BaseElement::from(23u64);
            let d = BaseElement::from(29u64);
            for _ in 0..rounds {
                a *= b;
                b *= c;
                c *= d;
            }
            a.as_int() ^ b.as_int() ^ c.as_int() ^ d.as_int()
        }
        FieldKernel::Inv => {
            let mut a = BaseElement::from(7u64);
            let mut b = BaseElement::from(19u64);
            let mut c = BaseElement::from(23u64);
            let d = BaseElement::from(29u64);
            for _ in 0..rounds {
                a = a.inv();
                b = b.inv();
                c += d;
            }
            a.as_int() ^ b.as_int() ^ c.as_int() ^ d.as_int()
        }
        FieldKernel::ExtensionMul => {
            let mut a = QuadExtension::<BaseElement>::new(
                BaseElement::from(7u64),
                BaseElement::from(19u64),
            );
            let mut b = QuadExtension::<BaseElement>::new(
                BaseElement::from(23u64),
                BaseElement::from(29u64),
            );
            let c = QuadExtension::<BaseElement>::new(
                BaseElement::from(31u64),
                BaseElement::from(37u64),
            );
            for _ in 0..rounds {
                a *= b;
                b *= c;
            }
            a.base_element(0).as_int()
                ^ a.base_element(1).as_int()
                ^ b.base_element(0).as_int()
                ^ b.base_element(1).as_int()
        }
    }
}

fn run_heap_probe(scratch_bytes: usize, touch_stride: usize) -> u64 {
    let scratch_bytes = scratch_bytes.max(1);
    let mut scratch = vec![0_u8; scratch_bytes];
    for index in (0..scratch.len()).step_by(touch_stride.max(1)) {
        scratch[index] = scratch[index].wrapping_add((index % 251) as u8);
    }
    scratch.iter().fold(0u64, |acc, byte| acc + *byte as u64)
}

fn encode_leb128(mut value: usize, out: &mut [u8]) -> usize {
    let mut cursor = 0usize;
    loop {
        let mut byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        out[cursor] = byte;
        cursor += 1;
        if value == 0 {
            break;
        }
    }
    cursor
}

fn populate_accounts(accounts: &[AccountInfo], variable_layout: bool, seed: u8) -> ProgramResult {
    for (account_index, account) in accounts.iter().enumerate() {
        if !account.is_writable {
            continue;
        }
        let mut data = account.try_borrow_mut_data()?;
        if variable_layout {
            let mut cursor = 0usize;
            while cursor < data.len() {
                let length = ((cursor / 7) + 5).min(48);
                let mut encoded = [0u8; 10];
                let used = encode_leb128(length, &mut encoded);
                if cursor + used >= data.len() {
                    break;
                }
                data[cursor..cursor + used].copy_from_slice(&encoded[..used]);
                cursor += used;
                let end = (cursor + length).min(data.len());
                for (offset, value) in data[cursor..end].iter_mut().enumerate() {
                    *value = seed
                        .wrapping_add(account_index as u8)
                        .wrapping_add(offset as u8);
                }
                cursor = end;
            }
        } else {
            for (offset, value) in data.iter_mut().enumerate() {
                *value = seed
                    .wrapping_add((account_index % 251) as u8)
                    .wrapping_add((offset % 251) as u8);
            }
        }
    }
    Ok(())
}

fn run_account_io(
    accounts: &[AccountInfo],
    fixed_layout: bool,
    read_bytes_per_account: usize,
    write_bytes_per_account: usize,
) -> Result<u64, ProgramError> {
    let mut checksum = 0u64;
    for account in accounts {
        let data = account.try_borrow_data()?;
        let readable = read_bytes_per_account.min(data.len());
        if fixed_layout {
            for chunk in data[..readable.max(1)].chunks(32) {
                checksum = checksum.wrapping_add(chunk.first().copied().unwrap_or_default() as u64);
            }
        } else {
            let mut cursor = 0usize;
            while cursor < readable {
                let (segment_len, consumed) = decode_leb128(&data[cursor..readable])?;
                cursor += consumed;
                let end = (cursor + segment_len).min(readable);
                checksum = checksum.wrapping_add((end - cursor) as u64);
                for byte in &data[cursor..end] {
                    checksum ^= *byte as u64;
                }
                cursor = end;
            }
        }
        drop(data);

        if account.is_writable && write_bytes_per_account > 0 {
            let mut data = account.try_borrow_mut_data()?;
            let writable = write_bytes_per_account.min(data.len());
            for byte in data.iter_mut().take(writable) {
                *byte = byte.wrapping_add(1);
            }
        }
    }
    Ok(checksum)
}

fn write_upload_chunk(
    account: &AccountInfo,
    offset: usize,
    rolling_hash: bool,
    prior_digest: &[u8; 32],
    chunk: &[u8],
) -> ProgramResult {
    if !account.is_writable {
        return Err(ProgramError::InvalidAccountData);
    }
    let mut data = account.try_borrow_mut_data()?;
    let end = offset.saturating_add(chunk.len());
    if end > data.len() {
        return Err(ProgramError::AccountDataTooSmall);
    }
    data[offset..end].copy_from_slice(chunk);
    if rolling_hash {
        black_box(hashv(&[prior_digest, chunk]));
    }
    Ok(())
}

fn run_synthetic_verifier(
    accounts: &[AccountInfo],
    profile: &SyntheticVerifierProfile,
    format: ProofParseFormat,
    batch_mode: MerkleBatchMode,
) -> ProgramResult {
    let mut iter = accounts.iter();
    let proof_account = next_account_info(&mut iter)?;
    let proof_data = proof_account.try_borrow_data()?;
    black_box(parse_proof(
        &proof_data,
        profile.proof_segments as usize,
        format,
    )?);
    drop(proof_data);

    black_box(run_hash_bench(
        profile.hash_calls as usize,
        profile.bytes_per_hash_call as usize,
    ));
    black_box(run_merkle_bench(
        profile.merkle_depth as usize,
        profile.merkle_paths as usize,
        profile.sibling_size as usize,
        batch_mode,
    ));
    if profile.field_add_sub_ops > 0 {
        black_box(run_field_kernel(
            FieldKernel::AddSub,
            profile.field_add_sub_ops,
        ));
    }
    if profile.field_mul_ops > 0 {
        black_box(run_field_kernel(FieldKernel::Mul, profile.field_mul_ops));
    }
    if profile.field_inv_ops > 0 {
        black_box(run_field_kernel(FieldKernel::Inv, profile.field_inv_ops));
    }
    if profile.extension_mul_ops > 0 {
        black_box(run_field_kernel(
            FieldKernel::ExtensionMul,
            profile.extension_mul_ops,
        ));
    }

    let io_accounts = iter.cloned().collect::<Vec<_>>();
    black_box(run_account_io(
        &io_accounts,
        profile.fixed_layout,
        profile.read_bytes_per_account as usize,
        profile.write_bytes_per_account as usize,
    )?);
    Ok(())
}

pub fn build_upload_instruction(
    program_id: Pubkey,
    upload_account: Pubkey,
    offset: u32,
    rolling_hash: bool,
    prior_digest: [u8; 32],
    chunk: Vec<u8>,
) -> Instruction {
    ProbeInstruction::instruction(
        program_id,
        vec![AccountMeta::new(upload_account, false)],
        ProbeInstruction::UploadChunk {
            offset,
            rolling_hash,
            prior_digest,
            chunk,
        },
    )
}

pub fn build_parse_instruction(
    program_id: Pubkey,
    upload_account: Pubkey,
    segment_count: u32,
    format: ProofParseFormat,
) -> Instruction {
    ProbeInstruction::instruction(
        program_id,
        vec![AccountMeta::new_readonly(upload_account, false)],
        ProbeInstruction::ParseProof {
            segment_count,
            format,
        },
    )
}

pub fn build_synthetic_instruction(
    program_id: Pubkey,
    upload_account: Pubkey,
    profile: SyntheticVerifierProfile,
    io_accounts: Vec<AccountMeta>,
    format: ProofParseFormat,
    batch_mode: MerkleBatchMode,
) -> Instruction {
    let mut accounts = vec![AccountMeta::new_readonly(upload_account, false)];
    accounts.extend(io_accounts);
    ProbeInstruction::instruction(
        program_id,
        accounts,
        ProbeInstruction::SyntheticVerifier {
            profile,
            format,
            batch_mode,
        },
    )
}

pub fn build_phase2_arithmetic_instruction(
    program_id: Pubkey,
    config: Phase2ArithmeticConfig,
    workload: ArithmeticWorkloadId,
    iterations: u32,
) -> Instruction {
    ProbeInstruction::instruction(
        program_id,
        Vec::new(),
        ProbeInstruction::Phase2Arithmetic {
            config,
            workload,
            iterations,
        },
    )
}

pub fn build_phase2_extension_instruction(
    program_id: Pubkey,
    config: Phase2ExtensionConfig,
    workload: ExtensionWorkloadId,
    iterations: u32,
) -> Instruction {
    ProbeInstruction::instruction(
        program_id,
        Vec::new(),
        ProbeInstruction::Phase2Extension {
            config,
            workload,
            iterations,
        },
    )
}

pub fn build_phase2_skeleton_instruction(
    program_id: Pubkey,
    proof_account: Pubkey,
    config: Phase2VerifierConfig,
    repeat: u32,
) -> Instruction {
    ProbeInstruction::instruction(
        program_id,
        vec![AccountMeta::new_readonly(proof_account, false)],
        ProbeInstruction::Phase2SkeletonVerify { config, repeat },
    )
}

pub fn build_phase2_whir_query_instruction(
    program_id: Pubkey,
    proof_account: Pubkey,
    config: Phase2VerifierConfig,
    repeat: u32,
) -> Instruction {
    ProbeInstruction::instruction(
        program_id,
        vec![AccountMeta::new_readonly(proof_account, false)],
        ProbeInstruction::Phase2WhirQueryVerify { config, repeat },
    )
}

pub fn build_phase2_real_fri_instruction(
    program_id: Pubkey,
    proof_account: Pubkey,
    seed_u64: u64,
    inc_u64: u64,
    repeat: u32,
) -> Instruction {
    ProbeInstruction::instruction(
        program_id,
        vec![AccountMeta::new_readonly(proof_account, false)],
        ProbeInstruction::Phase2RealFriVerify {
            seed_u64,
            inc_u64,
            repeat,
        },
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_fixed_segments() {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&3u32.to_le_bytes());
        bytes.extend_from_slice(&[1, 2, 3]);
        bytes.extend_from_slice(&2u32.to_le_bytes());
        bytes.extend_from_slice(&[4, 5]);
        assert!(parse_proof(&bytes, 2, ProofParseFormat::FixedWidth).is_ok());
    }
}
