use solana_program::program_error::ProgramError;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum RegistryProgramErrorV1 {
    InvalidInstruction = 0x4153_3001,
    InvalidAccountCount = 0x4153_3002,
    DuplicateAccount = 0x4153_3003,
    InvalidRegistryAddress = 0x4153_3004,
    InvalidRegistryAccount = 0x4153_3005,
    InvalidEntryAddress = 0x4153_3006,
    InvalidEntryAccount = 0x4153_3007,
    InvalidAuthority = 0x4153_3008,
    InvalidPayer = 0x4153_3009,
    InvalidSystemProgram = 0x4153_300A,
    InvalidFreshAccount = 0x4153_300B,
    GenerationMismatch = 0x4153_300C,
    GenerationOverflow = 0x4153_300D,
    RegistryFrozen = 0x4153_300E,
    RegistryAlreadyPaused = 0x4153_300F,
    RegistryNotPaused = 0x4153_3010,
    ActivationDelayOverflow = 0x4153_3011,
    ActivationDelayNotElapsed = 0x4153_3012,
    EntryNotPending = 0x4153_3013,
    EntryNotActive = 0x4153_3014,
    InvalidEntryState = 0x4153_3015,
    ReplacementNotActive = 0x4153_3016,
    IncompatibleReplacement = 0x4153_3017,
    InvalidRetirementSlot = 0x4153_3018,
}

impl From<RegistryProgramErrorV1> for ProgramError {
    fn from(error: RegistryProgramErrorV1) -> Self {
        Self::Custom(error as u32)
    }
}
