use crate::error::RegistryProgramErrorV1;

pub const REGISTRY_MUTATION_INSTRUCTION_MAGIC: [u8; 4] = *b"ASRM";
pub const REGISTRY_MUTATION_INSTRUCTION_VERSION: u8 = 1;
pub const REGISTRY_INITIALIZE_INSTRUCTION_BYTES: usize = 80;
pub const REGISTRY_SCHEDULE_INSTRUCTION_BYTES: usize = 128;
pub const REGISTRY_SIMPLE_MUTATION_INSTRUCTION_BYTES: usize = 16;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum RegistryMutationOpcodeV1 {
    Initialize = 0,
    ScheduleProfile = 1,
    Pause = 2,
    Unpause = 3,
    Activate = 4,
    Retire = 5,
    Freeze = 6,
}

impl TryFrom<u8> for RegistryMutationOpcodeV1 {
    type Error = RegistryProgramErrorV1;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(Self::Initialize),
            1 => Ok(Self::ScheduleProfile),
            2 => Ok(Self::Pause),
            3 => Ok(Self::Unpause),
            4 => Ok(Self::Activate),
            5 => Ok(Self::Retire),
            6 => Ok(Self::Freeze),
            _ => Err(RegistryProgramErrorV1::InvalidInstruction),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RegistryInstructionV1 {
    Initialize {
        pool: [u8; 32],
        policy_binding: [u8; 32],
        minimum_activation_delay_slots: u64,
    },
    ScheduleProfile {
        expected_generation: u64,
        verifier_program: [u8; 32],
        profile_binding: [u8; 32],
        release_binding: [u8; 32],
        statement_version: u8,
        activation_slot: u64,
    },
    Pause {
        expected_generation: u64,
    },
    Unpause {
        expected_generation: u64,
    },
    Activate {
        expected_generation: u64,
    },
    Retire {
        expected_generation: u64,
    },
    Freeze {
        expected_generation: u64,
    },
}

impl RegistryInstructionV1 {
    pub fn requires_clock(&self) -> bool {
        matches!(
            self,
            Self::ScheduleProfile { .. } | Self::Activate { .. } | Self::Retire { .. }
        )
    }
}

fn exact_array<const N: usize>(bytes: &[u8]) -> Result<[u8; N], RegistryProgramErrorV1> {
    bytes
        .try_into()
        .map_err(|_| RegistryProgramErrorV1::InvalidInstruction)
}

fn require_header(bytes: &[u8]) -> Result<RegistryMutationOpcodeV1, RegistryProgramErrorV1> {
    if bytes.len() < 8
        || bytes[..4] != REGISTRY_MUTATION_INSTRUCTION_MAGIC
        || bytes[4] != REGISTRY_MUTATION_INSTRUCTION_VERSION
        || bytes[6..8] != [0u8; 2]
    {
        return Err(RegistryProgramErrorV1::InvalidInstruction);
    }
    RegistryMutationOpcodeV1::try_from(bytes[5])
}

pub fn decode_registry_instruction_v1(
    bytes: &[u8],
) -> Result<RegistryInstructionV1, RegistryProgramErrorV1> {
    let opcode = require_header(bytes)?;
    match opcode {
        RegistryMutationOpcodeV1::Initialize => {
            if bytes.len() != REGISTRY_INITIALIZE_INSTRUCTION_BYTES {
                return Err(RegistryProgramErrorV1::InvalidInstruction);
            }
            Ok(RegistryInstructionV1::Initialize {
                pool: exact_array(&bytes[8..40])?,
                policy_binding: exact_array(&bytes[40..72])?,
                minimum_activation_delay_slots: u64::from_le_bytes(exact_array(&bytes[72..80])?),
            })
        }
        RegistryMutationOpcodeV1::ScheduleProfile => {
            if bytes.len() != REGISTRY_SCHEDULE_INSTRUCTION_BYTES || bytes[113..120] != [0u8; 7] {
                return Err(RegistryProgramErrorV1::InvalidInstruction);
            }
            Ok(RegistryInstructionV1::ScheduleProfile {
                expected_generation: u64::from_le_bytes(exact_array(&bytes[8..16])?),
                verifier_program: exact_array(&bytes[16..48])?,
                profile_binding: exact_array(&bytes[48..80])?,
                release_binding: exact_array(&bytes[80..112])?,
                statement_version: bytes[112],
                activation_slot: u64::from_le_bytes(exact_array(&bytes[120..128])?),
            })
        }
        RegistryMutationOpcodeV1::Pause
        | RegistryMutationOpcodeV1::Unpause
        | RegistryMutationOpcodeV1::Activate
        | RegistryMutationOpcodeV1::Retire
        | RegistryMutationOpcodeV1::Freeze => {
            if bytes.len() != REGISTRY_SIMPLE_MUTATION_INSTRUCTION_BYTES {
                return Err(RegistryProgramErrorV1::InvalidInstruction);
            }
            let expected_generation = u64::from_le_bytes(exact_array(&bytes[8..16])?);
            Ok(match opcode {
                RegistryMutationOpcodeV1::Pause => RegistryInstructionV1::Pause {
                    expected_generation,
                },
                RegistryMutationOpcodeV1::Unpause => RegistryInstructionV1::Unpause {
                    expected_generation,
                },
                RegistryMutationOpcodeV1::Activate => RegistryInstructionV1::Activate {
                    expected_generation,
                },
                RegistryMutationOpcodeV1::Retire => RegistryInstructionV1::Retire {
                    expected_generation,
                },
                RegistryMutationOpcodeV1::Freeze => RegistryInstructionV1::Freeze {
                    expected_generation,
                },
                _ => return Err(RegistryProgramErrorV1::InvalidInstruction),
            })
        }
    }
}

fn header(opcode: RegistryMutationOpcodeV1) -> [u8; 8] {
    let mut output = [0u8; 8];
    output[..4].copy_from_slice(&REGISTRY_MUTATION_INSTRUCTION_MAGIC);
    output[4] = REGISTRY_MUTATION_INSTRUCTION_VERSION;
    output[5] = opcode as u8;
    output
}

pub fn encode_initialize_registry_v1(
    pool: [u8; 32],
    policy_binding: [u8; 32],
    minimum_activation_delay_slots: u64,
) -> [u8; REGISTRY_INITIALIZE_INSTRUCTION_BYTES] {
    let mut output = [0u8; REGISTRY_INITIALIZE_INSTRUCTION_BYTES];
    output[..8].copy_from_slice(&header(RegistryMutationOpcodeV1::Initialize));
    output[8..40].copy_from_slice(&pool);
    output[40..72].copy_from_slice(&policy_binding);
    output[72..80].copy_from_slice(&minimum_activation_delay_slots.to_le_bytes());
    output
}

pub fn encode_schedule_profile_v1(
    expected_generation: u64,
    verifier_program: [u8; 32],
    profile_binding: [u8; 32],
    release_binding: [u8; 32],
    statement_version: u8,
    activation_slot: u64,
) -> [u8; REGISTRY_SCHEDULE_INSTRUCTION_BYTES] {
    let mut output = [0u8; REGISTRY_SCHEDULE_INSTRUCTION_BYTES];
    output[..8].copy_from_slice(&header(RegistryMutationOpcodeV1::ScheduleProfile));
    output[8..16].copy_from_slice(&expected_generation.to_le_bytes());
    output[16..48].copy_from_slice(&verifier_program);
    output[48..80].copy_from_slice(&profile_binding);
    output[80..112].copy_from_slice(&release_binding);
    output[112] = statement_version;
    output[120..128].copy_from_slice(&activation_slot.to_le_bytes());
    output
}

pub fn encode_simple_mutation_v1(
    opcode: RegistryMutationOpcodeV1,
    expected_generation: u64,
) -> Result<[u8; REGISTRY_SIMPLE_MUTATION_INSTRUCTION_BYTES], RegistryProgramErrorV1> {
    if matches!(
        opcode,
        RegistryMutationOpcodeV1::Initialize | RegistryMutationOpcodeV1::ScheduleProfile
    ) {
        return Err(RegistryProgramErrorV1::InvalidInstruction);
    }
    let mut output = [0u8; REGISTRY_SIMPLE_MUTATION_INSTRUCTION_BYTES];
    output[..8].copy_from_slice(&header(opcode));
    output[8..16].copy_from_slice(&expected_generation.to_le_bytes());
    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_instruction_roundtrips_and_trailing_or_reserved_bytes_fail() {
        let initialize = encode_initialize_registry_v1([1u8; 32], [2u8; 32], 9);
        assert_eq!(
            decode_registry_instruction_v1(&initialize),
            Ok(RegistryInstructionV1::Initialize {
                pool: [1u8; 32],
                policy_binding: [2u8; 32],
                minimum_activation_delay_slots: 9,
            })
        );

        let schedule = encode_schedule_profile_v1(4, [3u8; 32], [4u8; 32], [5u8; 32], 1, 99);
        assert_eq!(
            decode_registry_instruction_v1(&schedule),
            Ok(RegistryInstructionV1::ScheduleProfile {
                expected_generation: 4,
                verifier_program: [3u8; 32],
                profile_binding: [4u8; 32],
                release_binding: [5u8; 32],
                statement_version: 1,
                activation_slot: 99,
            })
        );

        for opcode in [
            RegistryMutationOpcodeV1::Pause,
            RegistryMutationOpcodeV1::Unpause,
            RegistryMutationOpcodeV1::Activate,
            RegistryMutationOpcodeV1::Retire,
            RegistryMutationOpcodeV1::Freeze,
        ] {
            let encoded = encode_simple_mutation_v1(opcode, 7).unwrap();
            assert!(decode_registry_instruction_v1(&encoded).is_ok());
        }

        let mut reserved = schedule;
        reserved[119] = 1;
        assert_eq!(
            decode_registry_instruction_v1(&reserved),
            Err(RegistryProgramErrorV1::InvalidInstruction)
        );
        let mut trailing = initialize.to_vec();
        trailing.push(0);
        assert_eq!(
            decode_registry_instruction_v1(&trailing),
            Err(RegistryProgramErrorV1::InvalidInstruction)
        );

        for offset in [0usize, 4, 5, 6] {
            let mut malformed = initialize;
            malformed[offset] ^= 0x80;
            assert_eq!(
                decode_registry_instruction_v1(&malformed),
                Err(RegistryProgramErrorV1::InvalidInstruction)
            );
        }
    }
}
