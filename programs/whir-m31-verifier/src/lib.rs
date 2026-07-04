use borsh::{to_vec, BorshDeserialize, BorshSerialize};
#[cfg(not(feature = "no-entrypoint"))]
use solana_program::entrypoint;
#[cfg(feature = "instrumentation")]
use solana_program::msg;
use solana_program::{
    account_info::{next_account_info, AccountInfo},
    declare_id,
    entrypoint::ProgramResult,
    instruction::{AccountMeta, Instruction},
    program_error::ProgramError,
    pubkey::Pubkey,
};
use whir_m31_core::{
    profile::ProfileId,
    statement::{SpendV0Binding, SPEND_V0_BINDING_BYTES},
    verify_proof_bytes,
};

declare_id!("2x2QhzvzkxvCKxJPcDmNHGT2StPMjQuBzx9NHxjRwmQn");

const UPLOAD_MAGIC: [u8; 4] = *b"WMU1";
const UPLOAD_VERSION: u16 = 1;
pub const UPLOAD_HEADER_BYTES: usize = 64;

#[derive(Clone, Debug, BorshSerialize, BorshDeserialize)]
pub enum WhirM31Instruction {
    InitUpload {
        profile_id: u16,
        proof_len: u32,
    },
    UploadChunk {
        offset: u32,
        prior_digest: [u8; 32],
        chunk: Vec<u8>,
    },
    Verify {
        binding_bytes: [u8; SPEND_V0_BINDING_BYTES],
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct UploadHeader {
    profile_id: u16,
    proof_len: u32,
    uploaded_len: u32,
    rolling_digest: [u8; 32],
    verified: u8,
}

impl WhirM31Instruction {
    pub fn encode(&self) -> Vec<u8> {
        to_vec(self).expect("instruction encoding")
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

pub fn build_init_upload_instruction(
    program_id: Pubkey,
    upload_account: Pubkey,
    profile_id: ProfileId,
    proof_len: usize,
) -> Instruction {
    WhirM31Instruction::instruction(
        program_id,
        vec![AccountMeta::new(upload_account, false)],
        WhirM31Instruction::InitUpload {
            profile_id: profile_id as u16,
            proof_len: proof_len as u32,
        },
    )
}

pub fn build_upload_chunk_instruction(
    program_id: Pubkey,
    upload_account: Pubkey,
    offset: usize,
    prior_digest: [u8; 32],
    chunk: Vec<u8>,
) -> Instruction {
    WhirM31Instruction::instruction(
        program_id,
        vec![AccountMeta::new(upload_account, false)],
        WhirM31Instruction::UploadChunk {
            offset: offset as u32,
            prior_digest,
            chunk,
        },
    )
}

pub fn build_verify_instruction(
    program_id: Pubkey,
    upload_account: Pubkey,
    binding: SpendV0Binding,
) -> Instruction {
    WhirM31Instruction::instruction(
        program_id,
        vec![AccountMeta::new(upload_account, false)],
        WhirM31Instruction::Verify {
            binding_bytes: binding.canonical_bytes(),
        },
    )
}

#[cfg(not(feature = "no-entrypoint"))]
entrypoint!(process_instruction);

pub fn process_instruction(
    _program_id: &Pubkey,
    accounts: &[AccountInfo],
    input: &[u8],
) -> ProgramResult {
    let instruction = WhirM31Instruction::try_from_slice(input)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    match instruction {
        WhirM31Instruction::InitUpload {
            profile_id,
            proof_len,
        } => {
            let account = next_account_info(&mut accounts.iter())?;
            handle_init_upload(account, profile_id, proof_len)
        }
        WhirM31Instruction::UploadChunk {
            offset,
            prior_digest,
            chunk,
        } => {
            let account = next_account_info(&mut accounts.iter())?;
            handle_upload_chunk(account, offset as usize, prior_digest, &chunk)
        }
        WhirM31Instruction::Verify { binding_bytes } => {
            let account = next_account_info(&mut accounts.iter())?;
            handle_verify(account, binding_bytes)
        }
    }
}

fn handle_init_upload(account: &AccountInfo, profile_id: u16, proof_len: u32) -> ProgramResult {
    let mut data = account.try_borrow_mut_data()?;
    if data.len() < UPLOAD_HEADER_BYTES + proof_len as usize {
        return Err(ProgramError::AccountDataTooSmall);
    }
    let _ = decode_profile_id(profile_id)?;
    for byte in data.iter_mut() {
        *byte = 0;
    }
    write_header(
        &mut data,
        UploadHeader {
            profile_id,
            proof_len,
            uploaded_len: 0,
            rolling_digest: [0_u8; 32],
            verified: 0,
        },
    )
}

fn handle_upload_chunk(
    account: &AccountInfo,
    offset: usize,
    prior_digest: [u8; 32],
    chunk: &[u8],
) -> ProgramResult {
    let mut data = account.try_borrow_mut_data()?;
    let mut header = read_header(&data)?;
    if offset != header.uploaded_len as usize {
        return Err(ProgramError::InvalidInstructionData);
    }
    if prior_digest != header.rolling_digest {
        return Err(ProgramError::InvalidInstructionData);
    }
    let proof_end = UPLOAD_HEADER_BYTES + header.proof_len as usize;
    let write_start = UPLOAD_HEADER_BYTES + offset;
    let write_end = write_start.saturating_add(chunk.len());
    if write_end > proof_end {
        return Err(ProgramError::AccountDataTooSmall);
    }
    data[write_start..write_end].copy_from_slice(chunk);
    header.uploaded_len = header
        .uploaded_len
        .checked_add(chunk.len() as u32)
        .ok_or(ProgramError::InvalidInstructionData)?;
    header.rolling_digest =
        solana_program::hash::hashv(&[&header.rolling_digest, chunk]).to_bytes();
    write_header(&mut data, header)
}

fn handle_verify(
    account: &AccountInfo,
    binding_bytes: [u8; SPEND_V0_BINDING_BYTES],
) -> ProgramResult {
    let mut data = account.try_borrow_mut_data()?;
    let mut header = read_header(&data)?;
    if header.uploaded_len != header.proof_len {
        return Err(ProgramError::InvalidInstructionData);
    }
    let profile_id = decode_profile_id(header.profile_id)?;
    let binding = SpendV0Binding::from_canonical_bytes(binding_bytes)
        .ok_or(ProgramError::InvalidInstructionData)?;
    let proof_end = UPLOAD_HEADER_BYTES + header.proof_len as usize;
    let proof_bytes = &data[UPLOAD_HEADER_BYTES..proof_end];

    #[cfg(feature = "instrumentation")]
    msg!(
        "whir-m31-verifier: verifying profile={} proof_bytes={}",
        header.profile_id,
        header.proof_len
    );

    verify_proof_bytes(profile_id, &binding, proof_bytes)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    header.verified = 1;
    write_header(&mut data, header)?;
    #[cfg(feature = "instrumentation")]
    msg!("whir-m31-verifier: accepted");
    Ok(())
}

fn decode_profile_id(raw: u16) -> Result<ProfileId, ProgramError> {
    match raw {
        value if value == ProfileId::WhirM31DevV0 as u16 => Ok(ProfileId::WhirM31DevV0),
        value if value == ProfileId::WhirM31SolanaV0 as u16 => Ok(ProfileId::WhirM31SolanaV0),
        _ => Err(ProgramError::InvalidInstructionData),
    }
}

fn read_header(data: &[u8]) -> Result<UploadHeader, ProgramError> {
    if data.len() < UPLOAD_HEADER_BYTES {
        return Err(ProgramError::AccountDataTooSmall);
    }
    if data[0..4] != UPLOAD_MAGIC {
        return Err(ProgramError::UninitializedAccount);
    }
    let version = u16::from_le_bytes(data[4..6].try_into().unwrap());
    if version != UPLOAD_VERSION {
        return Err(ProgramError::InvalidAccountData);
    }
    let mut rolling_digest = [0_u8; 32];
    rolling_digest.copy_from_slice(&data[16..48]);
    Ok(UploadHeader {
        profile_id: u16::from_le_bytes(data[6..8].try_into().unwrap()),
        proof_len: u32::from_le_bytes(data[8..12].try_into().unwrap()),
        uploaded_len: u32::from_le_bytes(data[12..16].try_into().unwrap()),
        rolling_digest,
        verified: data[48],
    })
}

fn write_header(data: &mut [u8], header: UploadHeader) -> ProgramResult {
    if data.len() < UPLOAD_HEADER_BYTES {
        return Err(ProgramError::AccountDataTooSmall);
    }
    data[0..4].copy_from_slice(&UPLOAD_MAGIC);
    data[4..6].copy_from_slice(&UPLOAD_VERSION.to_le_bytes());
    data[6..8].copy_from_slice(&header.profile_id.to_le_bytes());
    data[8..12].copy_from_slice(&header.proof_len.to_le_bytes());
    data[12..16].copy_from_slice(&header.uploaded_len.to_le_bytes());
    data[16..48].copy_from_slice(&header.rolling_digest);
    data[48] = header.verified;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn instruction_round_trip() {
        let inst = WhirM31Instruction::InitUpload {
            profile_id: ProfileId::WhirM31DevV0 as u16,
            proof_len: 128,
        };
        let bytes = inst.encode();
        let decoded = WhirM31Instruction::try_from_slice(&bytes).unwrap();
        match decoded {
            WhirM31Instruction::InitUpload {
                profile_id,
                proof_len,
            } => {
                assert_eq!(profile_id, ProfileId::WhirM31DevV0 as u16);
                assert_eq!(proof_len, 128);
            }
            _ => panic!("wrong instruction variant"),
        }
    }
}
