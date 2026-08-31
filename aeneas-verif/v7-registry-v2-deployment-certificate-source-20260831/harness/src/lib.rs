#![no_std]

pub const LOADER_V3_PROGRAM_BYTES: u64 = 36;
pub const LOADER_V3_PROGRAMDATA_METADATA_BYTES: u64 = 45;

pub type Bytes32 = [u8; 32];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AccountHeader {
    pub key: Bytes32,
    pub owner: Bytes32,
    pub executable: bool,
    pub signer: bool,
    pub writable: bool,
}

/// Result of production's exact `bincode::deserialize` on the 36-byte
/// loader-v3 Program account image.  This is an explicit primitive result,
/// not a claim that the extraction harness reimplements bincode.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProgramDecode {
    DecodeError,
    Program { programdata_address: Bytes32 },
    OtherVariant,
}

/// Result of production's exact `bincode::deserialize` on the first 45 bytes
/// of the loader-v3 ProgramData image.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProgramDataDecode {
    DecodeError,
    Immutable,
    Mutable,
    OtherVariant,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DeploymentError {
    InvalidVerifierProgram,
    InvalidProgramData,
    VerifierNotImmutable,
    ExecutableHashMismatch,
}

/// Literal values observed at the three source primitives Aeneas cannot
/// presently translate through `AccountInfo` shared-borrow joins:
///
/// * loader-v3 state decoding;
/// * `Pubkey::find_program_address`;
/// * SHA-256 of `programdata[45..]`.
///
/// The authenticator below checks those values with production's exact
/// fail-closed control flow.  No primitive result is accepted merely because
/// it was supplied.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DeploymentObservation {
    pub expected_program: Bytes32,
    pub loader_v3: Bytes32,
    pub program_account: AccountHeader,
    pub programdata_account: AccountHeader,
    pub program_account_data_len: u64,
    pub program_decode: ProgramDecode,
    pub derived_programdata: Bytes32,
    pub programdata_account_data_len: u64,
    pub programdata_decode: ProgramDataDecode,
    pub executable_sha256: Bytes32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ImmutableDeploymentCertificate {
    pub program: Bytes32,
    pub loader_v3: Bytes32,
    pub programdata_address: Bytes32,
    pub executable_sha256: Bytes32,
}

/// Fixed-width projection of production
/// `authenticate_immutable_loader_v3_deployment_v2` after the three named
/// source primitives above have returned.  Branch order and errors follow
/// `programs/aspis-registry/src/processor.rs:212-285`.
pub fn authenticate_immutable_loader_v3_deployment_projection(
    observation: DeploymentObservation,
) -> Result<ImmutableDeploymentCertificate, DeploymentError> {
    if observation.program_account.key != observation.expected_program
        || observation.program_account.owner != observation.loader_v3
        || !observation.program_account.executable
        || observation.program_account.signer
        || observation.program_account.writable
    {
        return Err(DeploymentError::InvalidVerifierProgram);
    }
    if observation.programdata_account.owner != observation.loader_v3
        || observation.programdata_account.executable
        || observation.programdata_account.signer
        || observation.programdata_account.writable
    {
        return Err(DeploymentError::InvalidProgramData);
    }

    if observation.program_account_data_len != LOADER_V3_PROGRAM_BYTES {
        return Err(DeploymentError::InvalidVerifierProgram);
    }
    let linked_programdata = match observation.program_decode {
        ProgramDecode::Program {
            programdata_address,
        } => programdata_address,
        ProgramDecode::DecodeError | ProgramDecode::OtherVariant => {
            return Err(DeploymentError::InvalidVerifierProgram)
        }
    };

    if linked_programdata != observation.programdata_account.key
        || linked_programdata != observation.derived_programdata
    {
        return Err(DeploymentError::InvalidProgramData);
    }

    if observation.programdata_account_data_len <= LOADER_V3_PROGRAMDATA_METADATA_BYTES {
        return Err(DeploymentError::InvalidProgramData);
    }
    match observation.programdata_decode {
        ProgramDataDecode::Immutable => {}
        ProgramDataDecode::Mutable => return Err(DeploymentError::VerifierNotImmutable),
        ProgramDataDecode::DecodeError | ProgramDataDecode::OtherVariant => {
            return Err(DeploymentError::InvalidProgramData)
        }
    }

    if observation.executable_sha256 == [0u8; 32] {
        return Err(DeploymentError::InvalidProgramData);
    }

    Ok(ImmutableDeploymentCertificate {
        program: observation.expected_program,
        loader_v3: observation.loader_v3,
        programdata_address: linked_programdata,
        executable_sha256: observation.executable_sha256,
    })
}

/// Production initialize/schedule compare the caller's expected digest with
/// the authenticated full-payload digest before storing the certificate.
pub fn bind_expected_executable_sha256(
    certificate: ImmutableDeploymentCertificate,
    expected_executable_sha256: Bytes32,
) -> Result<ImmutableDeploymentCertificate, DeploymentError> {
    if certificate.executable_sha256 != expected_executable_sha256 {
        return Err(DeploymentError::ExecutableHashMismatch);
    }
    Ok(certificate)
}

pub fn deployment_certificate_source_roots(
    observation: DeploymentObservation,
    expected_executable_sha256: Bytes32,
) -> Result<ImmutableDeploymentCertificate, DeploymentError> {
    let certificate = authenticate_immutable_loader_v3_deployment_projection(observation)?;
    bind_expected_executable_sha256(certificate, expected_executable_sha256)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bytes(value: u8) -> Bytes32 {
        [value; 32]
    }

    fn honest() -> DeploymentObservation {
        DeploymentObservation {
            expected_program: bytes(1),
            loader_v3: bytes(2),
            program_account: AccountHeader {
                key: bytes(1),
                owner: bytes(2),
                executable: true,
                signer: false,
                writable: false,
            },
            programdata_account: AccountHeader {
                key: bytes(3),
                owner: bytes(2),
                executable: false,
                signer: false,
                writable: false,
            },
            program_account_data_len: LOADER_V3_PROGRAM_BYTES,
            program_decode: ProgramDecode::Program {
                programdata_address: bytes(3),
            },
            derived_programdata: bytes(3),
            programdata_account_data_len: LOADER_V3_PROGRAMDATA_METADATA_BYTES + 1,
            programdata_decode: ProgramDataDecode::Immutable,
            executable_sha256: bytes(4),
        }
    }

    #[test]
    fn honest_certificate_is_exact() {
        let observation = honest();
        assert_eq!(
            deployment_certificate_source_roots(observation, bytes(4)),
            Ok(ImmutableDeploymentCertificate {
                program: bytes(1),
                loader_v3: bytes(2),
                programdata_address: bytes(3),
                executable_sha256: bytes(4),
            })
        );
    }

    #[test]
    fn every_fail_closed_gate_rejects() {
        for mutation in 0..17 {
            let mut observation = honest();
            match mutation {
                0 => observation.program_account.key = bytes(9),
                1 => observation.program_account.owner = bytes(9),
                2 => observation.program_account.executable = false,
                3 => observation.program_account.signer = true,
                4 => observation.program_account.writable = true,
                5 => observation.programdata_account.owner = bytes(9),
                6 => observation.programdata_account.executable = true,
                7 => observation.programdata_account.signer = true,
                8 => observation.programdata_account.writable = true,
                9 => observation.program_account_data_len -= 1,
                10 => observation.program_decode = ProgramDecode::DecodeError,
                11 => observation.programdata_account.key = bytes(9),
                12 => observation.derived_programdata = bytes(9),
                13 => {
                    observation.programdata_account_data_len = LOADER_V3_PROGRAMDATA_METADATA_BYTES
                }
                14 => observation.programdata_decode = ProgramDataDecode::DecodeError,
                15 => observation.programdata_decode = ProgramDataDecode::Mutable,
                16 => observation.executable_sha256 = [0u8; 32],
                _ => unreachable!(),
            }
            assert!(authenticate_immutable_loader_v3_deployment_projection(observation).is_err());
        }
    }

    #[test]
    fn expected_hash_mismatch_rejects() {
        assert_eq!(
            deployment_certificate_source_roots(honest(), bytes(9)),
            Err(DeploymentError::ExecutableHashMismatch)
        );
    }
}
