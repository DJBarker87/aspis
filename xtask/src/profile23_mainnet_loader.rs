//! Pure loader-v3 construction and account-image validation for the disposable
//! Profile23 deployment.
//!
//! This module deliberately performs no RPC calls, signing, submission, file
//! access, or ambient configuration lookup. Callers must journal and authorize
//! every transaction around these deterministic helpers.

#![allow(deprecated)]

use anyhow::{anyhow, ensure, Context, Result};
use solana_sdk::{
    bpf_loader_upgradeable::{self, UpgradeableLoaderState},
    hash::Hash,
    instruction::Instruction,
    message::Message,
    packet::PACKET_DATA_SIZE,
    pubkey::Pubkey,
    transaction::Transaction,
};

/// Solana's maximum serialized transaction size.
pub const LOADER_V3_PACKET_BYTES: usize = PACKET_DATA_SIZE;

/// A caller-supplied account image. All fields are treated as untrusted.
#[derive(Clone, Copy, Debug)]
pub struct LoaderAccountImage<'a> {
    pub address: Pubkey,
    pub owner: Pubkey,
    pub executable: bool,
    pub data: &'a [u8],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ParsedBuffer<'a> {
    pub authority_address: Option<Pubkey>,
    pub program_bytes: &'a [u8],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ParsedProgram {
    pub programdata_address: Pubkey,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ParsedProgramData<'a> {
    pub deployment_slot: u64,
    pub upgrade_authority_address: Option<Pubkey>,
    pub program_bytes: &'a [u8],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ValidatedBuffer {
    pub address: Pubkey,
    pub authority_address: Pubkey,
    pub capacity: usize,
    pub deployed_bytes: usize,
    pub zero_padding_bytes: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ValidatedProgram {
    pub address: Pubkey,
    pub programdata_address: Pubkey,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ValidatedProgramData {
    pub address: Pubkey,
    pub deployment_slot: u64,
    pub upgrade_authority_address: Pubkey,
    pub maximum_program_len: usize,
    pub deployed_bytes: usize,
    pub zero_padding_bytes: usize,
}

/// One deterministic loader write and its exact unsigned transaction size.
/// `Transaction::new_unsigned` includes fixed-size default signature slots, so
/// this byte count is identical to the eventual signed legacy wire length.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoaderWriteChunk {
    pub offset: u32,
    pub bytes: Vec<u8>,
    pub instruction: Instruction,
    pub transaction_wire_bytes: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoaderWritePlan {
    pub packet_limit_bytes: usize,
    pub chunk_bytes: usize,
    pub chunks: Vec<LoaderWriteChunk>,
}

impl LoaderWritePlan {
    /// Reconstruct the intended program bytes while checking that the plan is
    /// contiguous and that each instruction still agrees with its descriptor.
    pub fn reconstruct_program_bytes(&self) -> Result<Vec<u8>> {
        let total = self.chunks.iter().try_fold(0usize, |expected, chunk| {
            ensure!(
                usize::try_from(chunk.offset).ok() == Some(expected),
                "loader write plan has a non-contiguous offset"
            );
            expected
                .checked_add(chunk.bytes.len())
                .context("loader write plan length overflow")
        })?;
        let mut reconstructed = Vec::with_capacity(total);
        for chunk in &self.chunks {
            reconstructed.extend_from_slice(&chunk.bytes);
        }
        Ok(reconstructed)
    }
}

/// Derive the only ProgramData address valid for this runtime program ID.
pub fn derive_programdata_address(runtime_program_id: &Pubkey) -> Pubkey {
    bpf_loader_upgradeable::get_program_data_address(runtime_program_id)
}

/// Build the atomic System create + loader InitializeBuffer pair.
pub fn build_create_and_initialize_buffer(
    payer: &Pubkey,
    buffer: &Pubkey,
    initial_buffer_authority: &Pubkey,
    rent_lamports: u64,
    exact_program_len: usize,
) -> Result<Vec<Instruction>> {
    ensure!(rent_lamports > 0, "buffer rent must be nonzero");
    checked_account_len(
        UpgradeableLoaderState::size_of_buffer_metadata(),
        exact_program_len,
        "buffer",
    )?;
    ensure!(exact_program_len > 0, "program length must be nonzero");
    ensure!(buffer != payer, "buffer address must differ from payer");
    ensure!(
        buffer != initial_buffer_authority,
        "buffer address must differ from its authority"
    );
    bpf_loader_upgradeable::create_buffer(
        payer,
        buffer,
        initial_buffer_authority,
        rent_lamports,
        exact_program_len,
    )
    .map_err(|error| anyhow!("construct loader-v3 buffer creation: {error:?}"))
}

/// Build a checked buffer-authority transfer. Both the old and new authority
/// metas produced by the SDK are signers.
pub fn build_set_buffer_authority_checked(
    buffer: &Pubkey,
    current_authority: &Pubkey,
    new_authority: &Pubkey,
) -> Result<Instruction> {
    ensure!(
        current_authority != new_authority,
        "checked buffer authority transfer must change authority"
    );
    ensure!(buffer != current_authority && buffer != new_authority);
    Ok(bpf_loader_upgradeable::set_buffer_authority_checked(
        buffer,
        current_authority,
        new_authority,
    ))
}

/// Build the initial deployment at an exact maximum length. The returned pair
/// atomically creates the Program account and consumes the prepared buffer into
/// the loader-derived ProgramData account.
pub fn build_deploy_with_exact_sbf_len(
    payer: &Pubkey,
    runtime_program_id: &Pubkey,
    buffer: &Pubkey,
    upgrade_authority: &Pubkey,
    program_account_rent_lamports: u64,
    exact_sbf_len: usize,
) -> Result<Vec<Instruction>> {
    ensure!(
        program_account_rent_lamports > 0,
        "Program account rent must be nonzero"
    );
    checked_account_len(
        UpgradeableLoaderState::size_of_programdata_metadata(),
        exact_sbf_len,
        "ProgramData",
    )?;
    ensure!(exact_sbf_len > 0, "SBF length must be nonzero");
    ensure!(runtime_program_id != payer);
    ensure!(runtime_program_id != buffer);
    ensure!(buffer != payer && buffer != upgrade_authority);
    bpf_loader_upgradeable::deploy_with_max_program_len(
        payer,
        runtime_program_id,
        buffer,
        upgrade_authority,
        program_account_rent_lamports,
        exact_sbf_len,
    )
    .map_err(|error| anyhow!("construct exact loader-v3 deployment: {error:?}"))
}

/// Build loader-v3 cleanup for an initialized or partially written buffer.
pub fn build_close_buffer_to_payer(
    buffer: &Pubkey,
    payer: &Pubkey,
    buffer_authority: &Pubkey,
) -> Result<Instruction> {
    ensure!(buffer != payer);
    ensure!(buffer != buffer_authority);
    Ok(bpf_loader_upgradeable::close(
        buffer,
        payer,
        buffer_authority,
    ))
}

/// Build permanent ProgramData closure. The linked Program account is required
/// by loader-v3 when closing deployed program data; its small rent deposit is
/// intentionally not represented as refundable by this instruction.
pub fn build_close_programdata_to_payer(
    runtime_program_id: &Pubkey,
    payer: &Pubkey,
    upgrade_authority: &Pubkey,
) -> Result<Instruction> {
    ensure!(runtime_program_id != payer);
    let programdata = derive_programdata_address(runtime_program_id);
    ensure!(programdata != *payer && programdata != *upgrade_authority);
    Ok(bpf_loader_upgradeable::close_any(
        &programdata,
        payer,
        Some(upgrade_authority),
        Some(runtime_program_id),
    ))
}

/// Serialized legacy transaction length with the exact number of 64-byte
/// signature placeholders implied by the instruction metas.
pub fn unsigned_legacy_transaction_wire_bytes(
    payer: &Pubkey,
    instructions: &[Instruction],
) -> Result<usize> {
    let message = Message::new_with_blockhash(instructions, Some(payer), &Hash::default());
    let transaction = Transaction::new_unsigned(message);
    Ok(bincode::serialize(&transaction)
        .context("serialize unsigned loader transaction")?
        .len())
}

/// Compute the largest loader write payload whose complete legacy transaction
/// remains within Solana's packet limit for these exact payer/authority roles.
pub fn packet_safe_write_chunk_bytes(
    payer: &Pubkey,
    buffer: &Pubkey,
    buffer_authority: &Pubkey,
) -> Result<usize> {
    ensure!(buffer != payer && buffer != buffer_authority);
    let fits = |bytes: usize| -> Result<bool> {
        let instruction =
            bpf_loader_upgradeable::write(buffer, buffer_authority, 0, vec![0u8; bytes]);
        Ok(
            unsigned_legacy_transaction_wire_bytes(payer, &[instruction])?
                <= LOADER_V3_PACKET_BYTES,
        )
    };

    let mut lower = 0usize;
    let mut upper = LOADER_V3_PACKET_BYTES
        .checked_add(1)
        .context("packet-size search overflow")?;
    while lower + 1 < upper {
        let candidate = lower + (upper - lower) / 2;
        if fits(candidate)? {
            lower = candidate;
        } else {
            upper = candidate;
        }
    }
    ensure!(lower > 0, "no nonempty loader write fits a packet");
    ensure!(fits(lower)?);
    ensure!(!fits(lower + 1)?);
    Ok(lower)
}

/// Split an exact SBF image into the largest packet-safe loader writes.
pub fn build_packet_safe_write_plan(
    payer: &Pubkey,
    buffer: &Pubkey,
    buffer_authority: &Pubkey,
    sbf: &[u8],
) -> Result<LoaderWritePlan> {
    ensure!(!sbf.is_empty(), "SBF image must be nonempty");
    ensure!(
        sbf.len() <= u32::MAX as usize,
        "SBF image exceeds loader-v3 u32 offsets"
    );
    let chunk_bytes = packet_safe_write_chunk_bytes(payer, buffer, buffer_authority)?;
    let mut chunks = Vec::with_capacity(sbf.len().div_ceil(chunk_bytes));
    for (index, bytes) in sbf.chunks(chunk_bytes).enumerate() {
        let offset = index
            .checked_mul(chunk_bytes)
            .and_then(|offset| u32::try_from(offset).ok())
            .context("loader write offset overflow")?;
        let instruction =
            bpf_loader_upgradeable::write(buffer, buffer_authority, offset, bytes.to_vec());
        let transaction_wire_bytes =
            unsigned_legacy_transaction_wire_bytes(payer, &[instruction.clone()])?;
        ensure!(
            transaction_wire_bytes <= LOADER_V3_PACKET_BYTES,
            "loader write at offset {offset} exceeds packet limit"
        );
        chunks.push(LoaderWriteChunk {
            offset,
            bytes: bytes.to_vec(),
            instruction,
            transaction_wire_bytes,
        });
    }
    let plan = LoaderWritePlan {
        packet_limit_bytes: LOADER_V3_PACKET_BYTES,
        chunk_bytes,
        chunks,
    };
    ensure!(plan.reconstruct_program_bytes()? == sbf);
    Ok(plan)
}

pub fn parse_buffer_account<'a>(image: &LoaderAccountImage<'a>) -> Result<ParsedBuffer<'a>> {
    require_loader_account(image, false, "buffer")?;
    let metadata_bytes = UpgradeableLoaderState::size_of_buffer_metadata();
    let state = deserialize_metadata(image.data, metadata_bytes, "buffer")?;
    let UpgradeableLoaderState::Buffer { authority_address } = state else {
        return Err(anyhow!("loader account is not Buffer state"));
    };
    Ok(ParsedBuffer {
        authority_address,
        program_bytes: &image.data[metadata_bytes..],
    })
}

pub fn parse_program_account(image: &LoaderAccountImage<'_>) -> Result<ParsedProgram> {
    require_loader_account(image, true, "Program")?;
    ensure!(
        image.data.len() == UpgradeableLoaderState::size_of_program(),
        "Program account data length mismatch"
    );
    let state: UpgradeableLoaderState =
        bincode::deserialize(image.data).context("decode loader Program state")?;
    let UpgradeableLoaderState::Program {
        programdata_address,
    } = state
    else {
        return Err(anyhow!("loader account is not Program state"));
    };
    Ok(ParsedProgram {
        programdata_address,
    })
}

pub fn parse_programdata_account<'a>(
    image: &LoaderAccountImage<'a>,
) -> Result<ParsedProgramData<'a>> {
    require_loader_account(image, false, "ProgramData")?;
    let metadata_bytes = UpgradeableLoaderState::size_of_programdata_metadata();
    let state = deserialize_metadata(image.data, metadata_bytes, "ProgramData")?;
    let UpgradeableLoaderState::ProgramData {
        slot,
        upgrade_authority_address,
    } = state
    else {
        return Err(anyhow!("loader account is not ProgramData state"));
    };
    Ok(ParsedProgramData {
        deployment_slot: slot,
        upgrade_authority_address,
        program_bytes: &image.data[metadata_bytes..],
    })
}

pub fn validate_exact_buffer_account(
    image: &LoaderAccountImage<'_>,
    expected_buffer_address: &Pubkey,
    expected_authority: &Pubkey,
    expected_sbf: &[u8],
    expected_capacity: usize,
) -> Result<ValidatedBuffer> {
    ensure!(image.address == *expected_buffer_address);
    ensure!(!expected_sbf.is_empty(), "expected SBF must be nonempty");
    ensure!(expected_sbf.len() <= expected_capacity);
    let expected_len = checked_account_len(
        UpgradeableLoaderState::size_of_buffer_metadata(),
        expected_capacity,
        "buffer",
    )?;
    ensure!(
        image.data.len() == expected_len,
        "buffer allocation mismatch"
    );
    let parsed = parse_buffer_account(image)?;
    ensure!(
        parsed.authority_address == Some(*expected_authority),
        "buffer authority mismatch"
    );
    validate_program_bytes(
        parsed.program_bytes,
        expected_sbf,
        expected_capacity,
        "buffer",
    )?;
    Ok(ValidatedBuffer {
        address: image.address,
        authority_address: *expected_authority,
        capacity: expected_capacity,
        deployed_bytes: expected_sbf.len(),
        zero_padding_bytes: expected_capacity - expected_sbf.len(),
    })
}

pub fn validate_exact_program_account(
    image: &LoaderAccountImage<'_>,
    runtime_program_id: &Pubkey,
) -> Result<ValidatedProgram> {
    ensure!(
        image.address == *runtime_program_id,
        "Program address differs from runtime ID"
    );
    let parsed = parse_program_account(image)?;
    let expected_programdata = derive_programdata_address(runtime_program_id);
    ensure!(
        parsed.programdata_address == expected_programdata,
        "Program links a noncanonical ProgramData address"
    );
    Ok(ValidatedProgram {
        address: image.address,
        programdata_address: parsed.programdata_address,
    })
}

pub fn validate_exact_programdata_account(
    image: &LoaderAccountImage<'_>,
    runtime_program_id: &Pubkey,
    expected_upgrade_authority: &Pubkey,
    expected_sbf: &[u8],
    expected_maximum_program_len: usize,
) -> Result<ValidatedProgramData> {
    ensure!(
        image.address == derive_programdata_address(runtime_program_id),
        "ProgramData address differs from runtime derivation"
    );
    ensure!(!expected_sbf.is_empty(), "expected SBF must be nonempty");
    ensure!(expected_sbf.len() <= expected_maximum_program_len);
    let expected_len = checked_account_len(
        UpgradeableLoaderState::size_of_programdata_metadata(),
        expected_maximum_program_len,
        "ProgramData",
    )?;
    ensure!(
        image.data.len() == expected_len,
        "ProgramData maximum length mismatch"
    );
    let parsed = parse_programdata_account(image)?;
    ensure!(
        parsed.upgrade_authority_address == Some(*expected_upgrade_authority),
        "ProgramData upgrade authority mismatch"
    );
    validate_program_bytes(
        parsed.program_bytes,
        expected_sbf,
        expected_maximum_program_len,
        "ProgramData",
    )?;
    Ok(ValidatedProgramData {
        address: image.address,
        deployment_slot: parsed.deployment_slot,
        upgrade_authority_address: *expected_upgrade_authority,
        maximum_program_len: expected_maximum_program_len,
        deployed_bytes: expected_sbf.len(),
        zero_padding_bytes: expected_maximum_program_len - expected_sbf.len(),
    })
}

fn checked_account_len(metadata: usize, payload: usize, label: &str) -> Result<usize> {
    metadata
        .checked_add(payload)
        .with_context(|| format!("{label} account length overflow"))
}

fn require_loader_account(
    image: &LoaderAccountImage<'_>,
    executable: bool,
    label: &str,
) -> Result<()> {
    ensure!(
        image.owner == bpf_loader_upgradeable::id(),
        "{label} owner is not BPFLoaderUpgradeable"
    );
    ensure!(
        image.executable == executable,
        "{label} executable flag mismatch"
    );
    Ok(())
}

fn deserialize_metadata(
    data: &[u8],
    metadata_bytes: usize,
    label: &str,
) -> Result<UpgradeableLoaderState> {
    let metadata = data
        .get(..metadata_bytes)
        .with_context(|| format!("{label} account is shorter than loader metadata"))?;
    bincode::deserialize(metadata).with_context(|| format!("decode loader {label} metadata"))
}

fn validate_program_bytes(
    allocation: &[u8],
    expected_sbf: &[u8],
    expected_capacity: usize,
    label: &str,
) -> Result<()> {
    ensure!(allocation.len() == expected_capacity);
    ensure!(
        allocation.get(..expected_sbf.len()) == Some(expected_sbf),
        "{label} SBF bytes differ"
    );
    ensure!(
        allocation[expected_sbf.len()..]
            .iter()
            .all(|byte| *byte == 0),
        "{label} padding is nonzero"
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use solana_sdk::{
        loader_upgradeable_instruction::UpgradeableLoaderInstruction,
        system_instruction::SystemInstruction,
    };

    fn account_data(state: UpgradeableLoaderState, metadata_len: usize, payload: &[u8]) -> Vec<u8> {
        let metadata = bincode::serialize(&state).unwrap();
        assert_eq!(metadata.len(), metadata_len);
        let mut data = Vec::with_capacity(metadata.len() + payload.len());
        data.extend_from_slice(&metadata);
        data.extend_from_slice(payload);
        data
    }

    fn loader_instruction(instruction: &Instruction) -> UpgradeableLoaderInstruction {
        assert_eq!(instruction.program_id, bpf_loader_upgradeable::id());
        bincode::deserialize(&instruction.data).unwrap()
    }

    #[test]
    fn programdata_derivation_tracks_the_disposable_runtime_id() {
        let first = Pubkey::new_unique();
        let second = Pubkey::new_unique();
        assert_ne!(first, second);
        assert_ne!(
            derive_programdata_address(&first),
            derive_programdata_address(&second)
        );
        assert_eq!(
            derive_programdata_address(&first),
            bpf_loader_upgradeable::get_program_data_address(&first)
        );
    }

    #[test]
    fn buffer_creation_is_atomic_create_then_initialize() {
        let payer = Pubkey::new_unique();
        let buffer = Pubkey::new_unique();
        let authority = Pubkey::new_unique();
        let instructions =
            build_create_and_initialize_buffer(&payer, &buffer, &authority, 123_456, 921_848)
                .unwrap();
        assert_eq!(instructions.len(), 2);
        let create: SystemInstruction = bincode::deserialize(&instructions[0].data).unwrap();
        assert!(matches!(
            create,
            SystemInstruction::CreateAccount {
                lamports: 123_456,
                space,
                owner
            } if space == UpgradeableLoaderState::size_of_buffer(921_848) as u64
                && owner == bpf_loader_upgradeable::id()
        ));
        assert!(matches!(
            loader_instruction(&instructions[1]),
            UpgradeableLoaderInstruction::InitializeBuffer
        ));
        assert_eq!(instructions[1].accounts[0].pubkey, buffer);
        assert_eq!(instructions[1].accounts[1].pubkey, authority);
    }

    #[test]
    fn checked_authority_transfer_requires_both_authorities_to_sign() {
        let buffer = Pubkey::new_unique();
        let current = Pubkey::new_unique();
        let next = Pubkey::new_unique();
        let instruction = build_set_buffer_authority_checked(&buffer, &current, &next).unwrap();
        assert!(matches!(
            loader_instruction(&instruction),
            UpgradeableLoaderInstruction::SetAuthorityChecked
        ));
        assert_eq!(instruction.accounts.len(), 3);
        assert!(instruction.accounts[1].is_signer);
        assert!(instruction.accounts[2].is_signer);
    }

    #[test]
    fn exact_deploy_uses_dynamic_programdata_and_no_headroom() {
        let payer = Pubkey::new_unique();
        let program = Pubkey::new_unique();
        let buffer = Pubkey::new_unique();
        let authority = Pubkey::new_unique();
        let instructions = build_deploy_with_exact_sbf_len(
            &payer, &program, &buffer, &authority, 1_141_440, 921_848,
        )
        .unwrap();
        assert_eq!(instructions.len(), 2);
        assert!(matches!(
            loader_instruction(&instructions[1]),
            UpgradeableLoaderInstruction::DeployWithMaxDataLen {
                max_data_len: 921_848
            }
        ));
        assert_eq!(
            instructions[1].accounts[1].pubkey,
            derive_programdata_address(&program)
        );
        assert_eq!(instructions[1].accounts[2].pubkey, program);
        assert_eq!(instructions[1].accounts[3].pubkey, buffer);
        assert_eq!(instructions[1].accounts[7].pubkey, authority);
        assert!(instructions[1].accounts[7].is_signer);
    }

    #[test]
    fn close_builders_pin_payer_authority_and_linked_program() {
        let payer = Pubkey::new_unique();
        let program = Pubkey::new_unique();
        let buffer = Pubkey::new_unique();
        let authority = Pubkey::new_unique();
        let buffer_close = build_close_buffer_to_payer(&buffer, &payer, &authority).unwrap();
        assert!(matches!(
            loader_instruction(&buffer_close),
            UpgradeableLoaderInstruction::Close
        ));
        assert_eq!(
            buffer_close
                .accounts
                .iter()
                .map(|meta| meta.pubkey)
                .collect::<Vec<_>>(),
            vec![buffer, payer, authority]
        );
        assert!(buffer_close.accounts[2].is_signer);

        let programdata_close =
            build_close_programdata_to_payer(&program, &payer, &authority).unwrap();
        assert!(matches!(
            loader_instruction(&programdata_close),
            UpgradeableLoaderInstruction::Close
        ));
        assert_eq!(
            programdata_close
                .accounts
                .iter()
                .map(|meta| meta.pubkey)
                .collect::<Vec<_>>(),
            vec![
                derive_programdata_address(&program),
                payer,
                authority,
                program
            ]
        );
        assert!(programdata_close.accounts[2].is_signer);
        assert!(programdata_close.accounts[3].is_writable);
    }

    #[test]
    fn write_plan_reconstructs_bytes_and_every_wire_fits() {
        let payer = Pubkey::new_unique();
        let buffer = Pubkey::new_unique();
        let authority = payer;
        let sbf = (0..8_192)
            .map(|index| (index as u8).wrapping_mul(29))
            .collect::<Vec<_>>();
        let plan = build_packet_safe_write_plan(&payer, &buffer, &authority, &sbf).unwrap();
        assert_eq!(plan.reconstruct_program_bytes().unwrap(), sbf);
        assert!(plan.chunk_bytes > 900);
        assert!(plan
            .chunks
            .iter()
            .all(|chunk| chunk.transaction_wire_bytes <= LOADER_V3_PACKET_BYTES));
        let too_large =
            bpf_loader_upgradeable::write(&buffer, &authority, 0, vec![0u8; plan.chunk_bytes + 1]);
        assert!(
            unsigned_legacy_transaction_wire_bytes(&payer, &[too_large]).unwrap()
                > LOADER_V3_PACKET_BYTES
        );
    }

    #[test]
    fn distinct_write_authority_reduces_packet_payload_but_remains_safe() {
        let payer = Pubkey::new_unique();
        let buffer = Pubkey::new_unique();
        let distinct_authority = Pubkey::new_unique();
        let one_signer = packet_safe_write_chunk_bytes(&payer, &buffer, &payer).unwrap();
        let two_signer =
            packet_safe_write_chunk_bytes(&payer, &buffer, &distinct_authority).unwrap();
        assert!(two_signer < one_signer);
        assert!(two_signer > 800);
    }

    #[test]
    fn exact_account_images_validate_and_padding_drift_fails() {
        let program = Pubkey::new_unique();
        let programdata = derive_programdata_address(&program);
        let buffer = Pubkey::new_unique();
        let authority = Pubkey::new_unique();
        let sbf = [7u8, 11, 19, 23, 29];
        let mut padded = sbf.to_vec();
        padded.extend_from_slice(&[0u8; 3]);

        let buffer_data = account_data(
            UpgradeableLoaderState::Buffer {
                authority_address: Some(authority),
            },
            UpgradeableLoaderState::size_of_buffer_metadata(),
            &padded,
        );
        let buffer_image = LoaderAccountImage {
            address: buffer,
            owner: bpf_loader_upgradeable::id(),
            executable: false,
            data: &buffer_data,
        };
        let validated_buffer =
            validate_exact_buffer_account(&buffer_image, &buffer, &authority, &sbf, 8).unwrap();
        assert_eq!(validated_buffer.zero_padding_bytes, 3);

        let program_data = account_data(
            UpgradeableLoaderState::Program {
                programdata_address: programdata,
            },
            UpgradeableLoaderState::size_of_program(),
            &[],
        );
        let program_image = LoaderAccountImage {
            address: program,
            owner: bpf_loader_upgradeable::id(),
            executable: true,
            data: &program_data,
        };
        assert_eq!(
            validate_exact_program_account(&program_image, &program)
                .unwrap()
                .programdata_address,
            programdata
        );

        let programdata_data = account_data(
            UpgradeableLoaderState::ProgramData {
                slot: 4242,
                upgrade_authority_address: Some(authority),
            },
            UpgradeableLoaderState::size_of_programdata_metadata(),
            &padded,
        );
        let programdata_image = LoaderAccountImage {
            address: programdata,
            owner: bpf_loader_upgradeable::id(),
            executable: false,
            data: &programdata_data,
        };
        let validated_programdata =
            validate_exact_programdata_account(&programdata_image, &program, &authority, &sbf, 8)
                .unwrap();
        assert_eq!(validated_programdata.deployment_slot, 4242);
        assert_eq!(validated_programdata.zero_padding_bytes, 3);

        let mut nonzero_padding = programdata_data.clone();
        *nonzero_padding.last_mut().unwrap() = 1;
        let drifted = LoaderAccountImage {
            data: &nonzero_padding,
            ..programdata_image
        };
        assert!(
            validate_exact_programdata_account(&drifted, &program, &authority, &sbf, 8).is_err()
        );
    }

    #[test]
    fn validators_reject_wrong_owner_address_authority_and_linkage() {
        let program = Pubkey::new_unique();
        let authority = Pubkey::new_unique();
        let sbf = [1u8, 2, 3];
        let programdata = derive_programdata_address(&program);
        let data = account_data(
            UpgradeableLoaderState::ProgramData {
                slot: 1,
                upgrade_authority_address: Some(authority),
            },
            UpgradeableLoaderState::size_of_programdata_metadata(),
            &sbf,
        );
        let valid = LoaderAccountImage {
            address: programdata,
            owner: bpf_loader_upgradeable::id(),
            executable: false,
            data: &data,
        };
        assert!(validate_exact_programdata_account(&valid, &program, &authority, &sbf, 3).is_ok());
        assert!(validate_exact_programdata_account(
            &LoaderAccountImage {
                owner: Pubkey::new_unique(),
                ..valid
            },
            &program,
            &authority,
            &sbf,
            3
        )
        .is_err());
        assert!(validate_exact_programdata_account(
            &valid,
            &Pubkey::new_unique(),
            &authority,
            &sbf,
            3
        )
        .is_err());
        assert!(validate_exact_programdata_account(
            &valid,
            &program,
            &Pubkey::new_unique(),
            &sbf,
            3
        )
        .is_err());
    }
}
