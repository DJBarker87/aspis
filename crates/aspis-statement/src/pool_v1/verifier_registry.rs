//! Canonical Pool V1 verifier-registry account images.
//!
//! These pure byte formats keep the append-only Pool state independent of any
//! one proof release. Solana PDA/owner checks and verifier dispatch belong to
//! the separate Pool program layer.

pub const POOL_V1_VERIFIER_REGISTRY_MAGIC: [u8; 4] = *b"ASRG";
pub const POOL_V1_VERIFIER_REGISTRY_VERSION: u8 = 1;
pub const POOL_V1_VERIFIER_REGISTRY_BYTES: usize = 128;
pub const POOL_V1_VERIFIER_REGISTRY_FLAG_PAUSED: u8 = 1 << 0;
pub const POOL_V1_VERIFIER_REGISTRY_FLAG_IMMUTABLE: u8 = 1 << 1;
pub const POOL_V1_VERIFIER_REGISTRY_FLAGS_MASK: u8 =
    POOL_V1_VERIFIER_REGISTRY_FLAG_PAUSED | POOL_V1_VERIFIER_REGISTRY_FLAG_IMMUTABLE;

pub const POOL_V1_VERIFIER_ENTRY_MAGIC: [u8; 4] = *b"ASRE";
pub const POOL_V1_VERIFIER_ENTRY_VERSION: u8 = 1;
pub const POOL_V1_VERIFIER_ENTRY_BYTES: usize = 192;
pub const POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT: u64 = u64::MAX;

/// Registry V2 is a distinct, fail-closed account family.  It preserves the
/// V1 governance fields while additionally certifying that the registry
/// program itself was an immutable loader-v3 deployment when initialized.
pub const POOL_V1_VERIFIER_REGISTRY_V2_MAGIC: [u8; 4] = *b"ASR2";
pub const POOL_V1_VERIFIER_REGISTRY_V2_VERSION: u8 = 2;
pub const POOL_V1_VERIFIER_REGISTRY_V2_BYTES: usize = 256;
pub const POOL_V1_VERIFIER_ENTRY_V2_MAGIC: [u8; 4] = *b"ASE2";
pub const POOL_V1_VERIFIER_ENTRY_V2_VERSION: u8 = 2;
pub const POOL_V1_VERIFIER_ENTRY_V2_BYTES: usize = 320;
pub const POOL_V1_VERIFIER_DEPLOYMENT_MODE_IMMUTABLE_LOADER_V3: u8 = 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1VerifierRegistryFormatError {
    WrongLength,
    WrongMagic,
    WrongVersion,
    NonZeroReserved,
    UnsupportedFlags,
    InvalidStatus,
    InvalidAuthorityMode,
    ZeroRequiredBinding,
    InvalidActivationDelay,
    InvalidStatementVersion,
    InvalidRetirementSlot,
    InvalidDeploymentMode,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum VerifierEntryStatusV1 {
    Pending = 0,
    Active = 1,
    Paused = 2,
    Retired = 3,
}

impl TryFrom<u8> for VerifierEntryStatusV1 {
    type Error = PoolV1VerifierRegistryFormatError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(Self::Pending),
            1 => Ok(Self::Active),
            2 => Ok(Self::Paused),
            3 => Ok(Self::Retired),
            _ => Err(PoolV1VerifierRegistryFormatError::InvalidStatus),
        }
    }
}

/// One canonical registry account per Pool.
///
/// Layout (128 bytes):
/// `magic[4] || version || flags || reserved[2] || pool[32] || authority[32]
/// || policy_binding[32] || generation_le[8] || min_delay_le[8] || reserved[8]`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifierRegistryV1 {
    pub flags: u8,
    pub pool: [u8; 32],
    pub authority: [u8; 32],
    pub policy_binding: [u8; 32],
    pub generation: u64,
    pub minimum_activation_delay_slots: u64,
}

impl VerifierRegistryV1 {
    pub fn is_paused(&self) -> bool {
        self.flags & POOL_V1_VERIFIER_REGISTRY_FLAG_PAUSED != 0
    }

    pub fn is_immutable(&self) -> bool {
        self.flags & POOL_V1_VERIFIER_REGISTRY_FLAG_IMMUTABLE != 0
    }
}

/// One exact verifier/profile/release entry under a Pool registry.
///
/// Layout (192 bytes):
/// `magic[4] || version || status || statement_version || reserved || pool[32]
/// || verifier_program[32] || profile_binding[32] || release_binding[32]
/// || activation_slot_le[8] || retirement_slot_le[8] || policy_binding[32]
/// || reserved[8]`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifierRegistryEntryV1 {
    pub status: VerifierEntryStatusV1,
    pub statement_version: u8,
    pub pool: [u8; 32],
    pub verifier_program: [u8; 32],
    pub profile_binding: [u8; 32],
    pub release_binding: [u8; 32],
    pub activation_slot: u64,
    pub retirement_slot: u64,
    pub policy_binding: [u8; 32],
}

/// Canonical V2 registry image (256 bytes):
///
/// `magic[4] || version || flags || deployment_mode || reserved || pool[32]
/// || authority[32] || policy_binding[32] || generation_le[8]
/// || min_delay_le[8] || registry_program[32] || loader_program[32]
/// || programdata[32] || executable_sha256[32] || reserved[8]`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifierRegistryV2 {
    pub flags: u8,
    pub pool: [u8; 32],
    pub authority: [u8; 32],
    pub policy_binding: [u8; 32],
    pub generation: u64,
    pub minimum_activation_delay_slots: u64,
    pub registry_program: [u8; 32],
    pub loader_program: [u8; 32],
    pub programdata_address: [u8; 32],
    pub executable_hash: [u8; 32],
}

impl VerifierRegistryV2 {
    pub fn is_paused(&self) -> bool {
        self.flags & POOL_V1_VERIFIER_REGISTRY_FLAG_PAUSED != 0
    }

    pub fn is_immutable(&self) -> bool {
        self.flags & POOL_V1_VERIFIER_REGISTRY_FLAG_IMMUTABLE != 0
    }
}

/// Canonical V2 release certificate (320 bytes):
///
/// `magic[4] || version || status || statement_version || deployment_mode
/// || pool[32] || verifier_program[32] || profile_binding[32]
/// || release_binding[32] || loader_program[32] || programdata[32]
/// || executable_sha256[32] || expected_upgrade_authority[32]
/// || activation_slot_le[8] || retirement_slot_le[8] || policy_binding[32]
/// || flags_and_reserved[8]`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifierRegistryEntryV2 {
    pub status: VerifierEntryStatusV1,
    pub statement_version: u8,
    pub pool: [u8; 32],
    pub verifier_program: [u8; 32],
    pub profile_binding: [u8; 32],
    pub release_binding: [u8; 32],
    pub loader_program: [u8; 32],
    pub programdata_address: [u8; 32],
    pub executable_hash: [u8; 32],
    /// Production V2 requires this to be all zero, denoting `None`.
    pub expected_upgrade_authority: [u8; 32],
    pub activation_slot: u64,
    pub retirement_slot: u64,
    pub policy_binding: [u8; 32],
}

impl VerifierRegistryEntryV2 {
    pub fn has_no_retirement_slot(&self) -> bool {
        self.retirement_slot == POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT
    }

    pub fn is_active_at(&self, slot: u64) -> bool {
        self.status == VerifierEntryStatusV1::Active
            && self.activation_slot <= slot
            && (self.has_no_retirement_slot() || slot < self.retirement_slot)
    }

    pub fn is_exact_compatible_replacement_for(&self, retiring: &Self, slot: u64) -> bool {
        self.pool == retiring.pool
            && self.policy_binding == retiring.policy_binding
            && self.profile_binding == retiring.profile_binding
            && self.statement_version == retiring.statement_version
            && self.release_binding != retiring.release_binding
            && self.is_active_at(slot)
    }
}

impl VerifierRegistryEntryV1 {
    pub fn has_no_retirement_slot(&self) -> bool {
        self.retirement_slot == POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT
    }

    /// The exact active-interval predicate used by Pool V1 authorization.
    pub fn is_active_at(&self, slot: u64) -> bool {
        self.status == VerifierEntryStatusV1::Active
            && self.activation_slot <= slot
            && (self.has_no_retirement_slot() || slot < self.retirement_slot)
    }

    /// Conservative concrete refinement of the formal registry's abstract
    /// compatibility predicate.
    ///
    /// Pool V1 treats a profile binding as the identifier of one exact spend
    /// relation and statement contract. A replacement is therefore accepted
    /// only when it keeps the Pool, policy, profile and statement version,
    /// changes the release, and is active at the retirement slot. This is
    /// deliberately narrower than allowing governance to assert an unrelated
    /// profile is compatible.
    pub fn is_exact_compatible_replacement_for(&self, retiring: &Self, slot: u64) -> bool {
        self.pool == retiring.pool
            && self.policy_binding == retiring.policy_binding
            && self.profile_binding == retiring.profile_binding
            && self.statement_version == retiring.statement_version
            && self.release_binding != retiring.release_binding
            && self.is_active_at(slot)
    }
}

fn required_binding_is_zero(value: &[u8; 32]) -> bool {
    *value == [0u8; 32]
}

pub fn validate_verifier_registry_v1(
    registry: &VerifierRegistryV1,
) -> Result<(), PoolV1VerifierRegistryFormatError> {
    if registry.flags & !POOL_V1_VERIFIER_REGISTRY_FLAGS_MASK != 0 {
        return Err(PoolV1VerifierRegistryFormatError::UnsupportedFlags);
    }
    if required_binding_is_zero(&registry.pool)
        || required_binding_is_zero(&registry.policy_binding)
    {
        return Err(PoolV1VerifierRegistryFormatError::ZeroRequiredBinding);
    }
    if registry.is_immutable() != required_binding_is_zero(&registry.authority) {
        return Err(PoolV1VerifierRegistryFormatError::InvalidAuthorityMode);
    }
    if registry.minimum_activation_delay_slots == 0 {
        return Err(PoolV1VerifierRegistryFormatError::InvalidActivationDelay);
    }
    Ok(())
}

pub fn encode_verifier_registry_v1(
    registry: &VerifierRegistryV1,
) -> Result<[u8; POOL_V1_VERIFIER_REGISTRY_BYTES], PoolV1VerifierRegistryFormatError> {
    validate_verifier_registry_v1(registry)?;
    let mut output = [0u8; POOL_V1_VERIFIER_REGISTRY_BYTES];
    output[..4].copy_from_slice(&POOL_V1_VERIFIER_REGISTRY_MAGIC);
    output[4] = POOL_V1_VERIFIER_REGISTRY_VERSION;
    output[5] = registry.flags;
    output[8..40].copy_from_slice(&registry.pool);
    output[40..72].copy_from_slice(&registry.authority);
    output[72..104].copy_from_slice(&registry.policy_binding);
    output[104..112].copy_from_slice(&registry.generation.to_le_bytes());
    output[112..120].copy_from_slice(&registry.minimum_activation_delay_slots.to_le_bytes());
    Ok(output)
}

pub fn decode_verifier_registry_v1(
    bytes: &[u8],
) -> Result<VerifierRegistryV1, PoolV1VerifierRegistryFormatError> {
    if bytes.len() != POOL_V1_VERIFIER_REGISTRY_BYTES {
        return Err(PoolV1VerifierRegistryFormatError::WrongLength);
    }
    if bytes[..4] != POOL_V1_VERIFIER_REGISTRY_MAGIC {
        return Err(PoolV1VerifierRegistryFormatError::WrongMagic);
    }
    if bytes[4] != POOL_V1_VERIFIER_REGISTRY_VERSION {
        return Err(PoolV1VerifierRegistryFormatError::WrongVersion);
    }
    if bytes[6..8] != [0u8; 2] || bytes[120..128] != [0u8; 8] {
        return Err(PoolV1VerifierRegistryFormatError::NonZeroReserved);
    }
    let registry = VerifierRegistryV1 {
        flags: bytes[5],
        pool: bytes[8..40].try_into().unwrap(),
        authority: bytes[40..72].try_into().unwrap(),
        policy_binding: bytes[72..104].try_into().unwrap(),
        generation: u64::from_le_bytes(bytes[104..112].try_into().unwrap()),
        minimum_activation_delay_slots: u64::from_le_bytes(bytes[112..120].try_into().unwrap()),
    };
    validate_verifier_registry_v1(&registry)?;
    Ok(registry)
}

pub fn validate_verifier_registry_entry_v1(
    entry: &VerifierRegistryEntryV1,
) -> Result<(), PoolV1VerifierRegistryFormatError> {
    if entry.statement_version == 0 {
        return Err(PoolV1VerifierRegistryFormatError::InvalidStatementVersion);
    }
    if required_binding_is_zero(&entry.pool)
        || required_binding_is_zero(&entry.verifier_program)
        || required_binding_is_zero(&entry.profile_binding)
        || required_binding_is_zero(&entry.release_binding)
        || required_binding_is_zero(&entry.policy_binding)
    {
        return Err(PoolV1VerifierRegistryFormatError::ZeroRequiredBinding);
    }
    if !entry.has_no_retirement_slot() && entry.retirement_slot <= entry.activation_slot {
        return Err(PoolV1VerifierRegistryFormatError::InvalidRetirementSlot);
    }
    Ok(())
}

pub fn encode_verifier_registry_entry_v1(
    entry: &VerifierRegistryEntryV1,
) -> Result<[u8; POOL_V1_VERIFIER_ENTRY_BYTES], PoolV1VerifierRegistryFormatError> {
    validate_verifier_registry_entry_v1(entry)?;
    let mut output = [0u8; POOL_V1_VERIFIER_ENTRY_BYTES];
    output[..4].copy_from_slice(&POOL_V1_VERIFIER_ENTRY_MAGIC);
    output[4] = POOL_V1_VERIFIER_ENTRY_VERSION;
    output[5] = entry.status as u8;
    output[6] = entry.statement_version;
    output[8..40].copy_from_slice(&entry.pool);
    output[40..72].copy_from_slice(&entry.verifier_program);
    output[72..104].copy_from_slice(&entry.profile_binding);
    output[104..136].copy_from_slice(&entry.release_binding);
    output[136..144].copy_from_slice(&entry.activation_slot.to_le_bytes());
    output[144..152].copy_from_slice(&entry.retirement_slot.to_le_bytes());
    output[152..184].copy_from_slice(&entry.policy_binding);
    Ok(output)
}

pub fn decode_verifier_registry_entry_v1(
    bytes: &[u8],
) -> Result<VerifierRegistryEntryV1, PoolV1VerifierRegistryFormatError> {
    if bytes.len() != POOL_V1_VERIFIER_ENTRY_BYTES {
        return Err(PoolV1VerifierRegistryFormatError::WrongLength);
    }
    if bytes[..4] != POOL_V1_VERIFIER_ENTRY_MAGIC {
        return Err(PoolV1VerifierRegistryFormatError::WrongMagic);
    }
    if bytes[4] != POOL_V1_VERIFIER_ENTRY_VERSION {
        return Err(PoolV1VerifierRegistryFormatError::WrongVersion);
    }
    if bytes[7] != 0 || bytes[184..192] != [0u8; 8] {
        return Err(PoolV1VerifierRegistryFormatError::NonZeroReserved);
    }
    let entry = VerifierRegistryEntryV1 {
        status: VerifierEntryStatusV1::try_from(bytes[5])?,
        statement_version: bytes[6],
        pool: bytes[8..40].try_into().unwrap(),
        verifier_program: bytes[40..72].try_into().unwrap(),
        profile_binding: bytes[72..104].try_into().unwrap(),
        release_binding: bytes[104..136].try_into().unwrap(),
        activation_slot: u64::from_le_bytes(bytes[136..144].try_into().unwrap()),
        retirement_slot: u64::from_le_bytes(bytes[144..152].try_into().unwrap()),
        policy_binding: bytes[152..184].try_into().unwrap(),
    };
    validate_verifier_registry_entry_v1(&entry)?;
    Ok(entry)
}

pub fn validate_verifier_registry_v2(
    registry: &VerifierRegistryV2,
) -> Result<(), PoolV1VerifierRegistryFormatError> {
    if registry.flags & !POOL_V1_VERIFIER_REGISTRY_FLAGS_MASK != 0 {
        return Err(PoolV1VerifierRegistryFormatError::UnsupportedFlags);
    }
    if required_binding_is_zero(&registry.pool)
        || required_binding_is_zero(&registry.policy_binding)
        || required_binding_is_zero(&registry.registry_program)
        || required_binding_is_zero(&registry.loader_program)
        || required_binding_is_zero(&registry.programdata_address)
        || required_binding_is_zero(&registry.executable_hash)
    {
        return Err(PoolV1VerifierRegistryFormatError::ZeroRequiredBinding);
    }
    if registry.is_immutable() != required_binding_is_zero(&registry.authority) {
        return Err(PoolV1VerifierRegistryFormatError::InvalidAuthorityMode);
    }
    if registry.minimum_activation_delay_slots == 0 {
        return Err(PoolV1VerifierRegistryFormatError::InvalidActivationDelay);
    }
    Ok(())
}

pub fn encode_verifier_registry_v2(
    registry: &VerifierRegistryV2,
) -> Result<[u8; POOL_V1_VERIFIER_REGISTRY_V2_BYTES], PoolV1VerifierRegistryFormatError> {
    validate_verifier_registry_v2(registry)?;
    let mut output = [0u8; POOL_V1_VERIFIER_REGISTRY_V2_BYTES];
    output[..4].copy_from_slice(&POOL_V1_VERIFIER_REGISTRY_V2_MAGIC);
    output[4] = POOL_V1_VERIFIER_REGISTRY_V2_VERSION;
    output[5] = registry.flags;
    output[6] = POOL_V1_VERIFIER_DEPLOYMENT_MODE_IMMUTABLE_LOADER_V3;
    output[8..40].copy_from_slice(&registry.pool);
    output[40..72].copy_from_slice(&registry.authority);
    output[72..104].copy_from_slice(&registry.policy_binding);
    output[104..112].copy_from_slice(&registry.generation.to_le_bytes());
    output[112..120].copy_from_slice(&registry.minimum_activation_delay_slots.to_le_bytes());
    output[120..152].copy_from_slice(&registry.registry_program);
    output[152..184].copy_from_slice(&registry.loader_program);
    output[184..216].copy_from_slice(&registry.programdata_address);
    output[216..248].copy_from_slice(&registry.executable_hash);
    Ok(output)
}

pub fn decode_verifier_registry_v2(
    bytes: &[u8],
) -> Result<VerifierRegistryV2, PoolV1VerifierRegistryFormatError> {
    if bytes.len() != POOL_V1_VERIFIER_REGISTRY_V2_BYTES {
        return Err(PoolV1VerifierRegistryFormatError::WrongLength);
    }
    if bytes[..4] != POOL_V1_VERIFIER_REGISTRY_V2_MAGIC {
        return Err(PoolV1VerifierRegistryFormatError::WrongMagic);
    }
    if bytes[4] != POOL_V1_VERIFIER_REGISTRY_V2_VERSION {
        return Err(PoolV1VerifierRegistryFormatError::WrongVersion);
    }
    if bytes[6] != POOL_V1_VERIFIER_DEPLOYMENT_MODE_IMMUTABLE_LOADER_V3 {
        return Err(PoolV1VerifierRegistryFormatError::InvalidDeploymentMode);
    }
    if bytes[7] != 0 || bytes[248..256] != [0u8; 8] {
        return Err(PoolV1VerifierRegistryFormatError::NonZeroReserved);
    }
    let registry = VerifierRegistryV2 {
        flags: bytes[5],
        pool: bytes[8..40].try_into().unwrap(),
        authority: bytes[40..72].try_into().unwrap(),
        policy_binding: bytes[72..104].try_into().unwrap(),
        generation: u64::from_le_bytes(bytes[104..112].try_into().unwrap()),
        minimum_activation_delay_slots: u64::from_le_bytes(bytes[112..120].try_into().unwrap()),
        registry_program: bytes[120..152].try_into().unwrap(),
        loader_program: bytes[152..184].try_into().unwrap(),
        programdata_address: bytes[184..216].try_into().unwrap(),
        executable_hash: bytes[216..248].try_into().unwrap(),
    };
    validate_verifier_registry_v2(&registry)?;
    Ok(registry)
}

pub fn validate_verifier_registry_entry_v2(
    entry: &VerifierRegistryEntryV2,
) -> Result<(), PoolV1VerifierRegistryFormatError> {
    if entry.statement_version == 0 {
        return Err(PoolV1VerifierRegistryFormatError::InvalidStatementVersion);
    }
    if required_binding_is_zero(&entry.pool)
        || required_binding_is_zero(&entry.verifier_program)
        || required_binding_is_zero(&entry.profile_binding)
        || required_binding_is_zero(&entry.release_binding)
        || required_binding_is_zero(&entry.loader_program)
        || required_binding_is_zero(&entry.programdata_address)
        || required_binding_is_zero(&entry.executable_hash)
        || required_binding_is_zero(&entry.policy_binding)
    {
        return Err(PoolV1VerifierRegistryFormatError::ZeroRequiredBinding);
    }
    if entry.expected_upgrade_authority != [0u8; 32] {
        return Err(PoolV1VerifierRegistryFormatError::InvalidAuthorityMode);
    }
    if !entry.has_no_retirement_slot() && entry.retirement_slot <= entry.activation_slot {
        return Err(PoolV1VerifierRegistryFormatError::InvalidRetirementSlot);
    }
    Ok(())
}

pub fn encode_verifier_registry_entry_v2(
    entry: &VerifierRegistryEntryV2,
) -> Result<[u8; POOL_V1_VERIFIER_ENTRY_V2_BYTES], PoolV1VerifierRegistryFormatError> {
    validate_verifier_registry_entry_v2(entry)?;
    let mut output = [0u8; POOL_V1_VERIFIER_ENTRY_V2_BYTES];
    output[..4].copy_from_slice(&POOL_V1_VERIFIER_ENTRY_V2_MAGIC);
    output[4] = POOL_V1_VERIFIER_ENTRY_V2_VERSION;
    output[5] = entry.status as u8;
    output[6] = entry.statement_version;
    output[7] = POOL_V1_VERIFIER_DEPLOYMENT_MODE_IMMUTABLE_LOADER_V3;
    output[8..40].copy_from_slice(&entry.pool);
    output[40..72].copy_from_slice(&entry.verifier_program);
    output[72..104].copy_from_slice(&entry.profile_binding);
    output[104..136].copy_from_slice(&entry.release_binding);
    output[136..168].copy_from_slice(&entry.loader_program);
    output[168..200].copy_from_slice(&entry.programdata_address);
    output[200..232].copy_from_slice(&entry.executable_hash);
    output[232..264].copy_from_slice(&entry.expected_upgrade_authority);
    output[264..272].copy_from_slice(&entry.activation_slot.to_le_bytes());
    output[272..280].copy_from_slice(&entry.retirement_slot.to_le_bytes());
    output[280..312].copy_from_slice(&entry.policy_binding);
    Ok(output)
}

pub fn decode_verifier_registry_entry_v2(
    bytes: &[u8],
) -> Result<VerifierRegistryEntryV2, PoolV1VerifierRegistryFormatError> {
    if bytes.len() != POOL_V1_VERIFIER_ENTRY_V2_BYTES {
        return Err(PoolV1VerifierRegistryFormatError::WrongLength);
    }
    if bytes[..4] != POOL_V1_VERIFIER_ENTRY_V2_MAGIC {
        return Err(PoolV1VerifierRegistryFormatError::WrongMagic);
    }
    if bytes[4] != POOL_V1_VERIFIER_ENTRY_V2_VERSION {
        return Err(PoolV1VerifierRegistryFormatError::WrongVersion);
    }
    if bytes[7] != POOL_V1_VERIFIER_DEPLOYMENT_MODE_IMMUTABLE_LOADER_V3 {
        return Err(PoolV1VerifierRegistryFormatError::InvalidDeploymentMode);
    }
    if bytes[312..320] != [0u8; 8] {
        return Err(PoolV1VerifierRegistryFormatError::NonZeroReserved);
    }
    let entry = VerifierRegistryEntryV2 {
        status: VerifierEntryStatusV1::try_from(bytes[5])?,
        statement_version: bytes[6],
        pool: bytes[8..40].try_into().unwrap(),
        verifier_program: bytes[40..72].try_into().unwrap(),
        profile_binding: bytes[72..104].try_into().unwrap(),
        release_binding: bytes[104..136].try_into().unwrap(),
        loader_program: bytes[136..168].try_into().unwrap(),
        programdata_address: bytes[168..200].try_into().unwrap(),
        executable_hash: bytes[200..232].try_into().unwrap(),
        expected_upgrade_authority: bytes[232..264].try_into().unwrap(),
        activation_slot: u64::from_le_bytes(bytes[264..272].try_into().unwrap()),
        retirement_slot: u64::from_le_bytes(bytes[272..280].try_into().unwrap()),
        policy_binding: bytes[280..312].try_into().unwrap(),
    };
    validate_verifier_registry_entry_v2(&entry)?;
    Ok(entry)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn registry() -> VerifierRegistryV1 {
        VerifierRegistryV1 {
            flags: 0,
            pool: [1u8; 32],
            authority: [2u8; 32],
            policy_binding: [3u8; 32],
            generation: 4,
            minimum_activation_delay_slots: 5,
        }
    }

    fn entry() -> VerifierRegistryEntryV1 {
        VerifierRegistryEntryV1 {
            status: VerifierEntryStatusV1::Active,
            statement_version: 1,
            pool: [1u8; 32],
            verifier_program: [2u8; 32],
            profile_binding: [3u8; 32],
            release_binding: [4u8; 32],
            activation_slot: 10,
            retirement_slot: POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
            policy_binding: [5u8; 32],
        }
    }

    #[test]
    fn registry_image_roundtrips_and_rejects_unknown_flags_and_reserved_bytes() {
        let original = registry();
        let encoded = encode_verifier_registry_v1(&original).unwrap();
        assert_eq!(encoded.len(), POOL_V1_VERIFIER_REGISTRY_BYTES);
        assert_eq!(decode_verifier_registry_v1(&encoded), Ok(original));

        let mut unknown_flags = encoded;
        unknown_flags[5] = 0x80;
        assert_eq!(
            decode_verifier_registry_v1(&unknown_flags),
            Err(PoolV1VerifierRegistryFormatError::UnsupportedFlags)
        );
        let mut reserved = encoded;
        reserved[127] = 1;
        assert_eq!(
            decode_verifier_registry_v1(&reserved),
            Err(PoolV1VerifierRegistryFormatError::NonZeroReserved)
        );
        assert_eq!(
            encode_verifier_registry_v1(&VerifierRegistryV1 {
                minimum_activation_delay_slots: 0,
                ..original
            }),
            Err(PoolV1VerifierRegistryFormatError::InvalidActivationDelay)
        );
    }

    #[test]
    fn entry_image_roundtrips_and_rejects_status_retirement_and_reserved_bytes() {
        let original = entry();
        let encoded = encode_verifier_registry_entry_v1(&original).unwrap();
        assert_eq!(encoded.len(), POOL_V1_VERIFIER_ENTRY_BYTES);
        assert_eq!(decode_verifier_registry_entry_v1(&encoded), Ok(original));

        let mut invalid_status = encoded;
        invalid_status[5] = 4;
        assert_eq!(
            decode_verifier_registry_entry_v1(&invalid_status),
            Err(PoolV1VerifierRegistryFormatError::InvalidStatus)
        );
        let mut reserved = encoded;
        reserved[191] = 1;
        assert_eq!(
            decode_verifier_registry_entry_v1(&reserved),
            Err(PoolV1VerifierRegistryFormatError::NonZeroReserved)
        );
        assert_eq!(
            encode_verifier_registry_entry_v1(&VerifierRegistryEntryV1 {
                retirement_slot: original.activation_slot,
                ..original
            }),
            Err(PoolV1VerifierRegistryFormatError::InvalidRetirementSlot)
        );
    }

    #[test]
    fn active_interval_and_exact_replacement_are_fail_closed() {
        let retiring = entry();
        let replacement = VerifierRegistryEntryV1 {
            verifier_program: [9u8; 32],
            release_binding: [6u8; 32],
            activation_slot: 9,
            ..retiring
        };

        assert!(replacement.is_active_at(10));
        assert!(replacement.is_exact_compatible_replacement_for(&retiring, 10));
        assert!(!VerifierRegistryEntryV1 {
            profile_binding: [7u8; 32],
            ..replacement
        }
        .is_exact_compatible_replacement_for(&retiring, 10));
        assert!(!VerifierRegistryEntryV1 {
            release_binding: retiring.release_binding,
            ..replacement
        }
        .is_exact_compatible_replacement_for(&retiring, 10));
        assert!(!VerifierRegistryEntryV1 {
            status: VerifierEntryStatusV1::Paused,
            ..replacement
        }
        .is_exact_compatible_replacement_for(&retiring, 10));
    }

    fn registry_v2() -> VerifierRegistryV2 {
        VerifierRegistryV2 {
            flags: 0,
            pool: [1u8; 32],
            authority: [2u8; 32],
            policy_binding: [3u8; 32],
            generation: 4,
            minimum_activation_delay_slots: 5,
            registry_program: [6u8; 32],
            loader_program: [7u8; 32],
            programdata_address: [8u8; 32],
            executable_hash: [9u8; 32],
        }
    }

    fn entry_v2() -> VerifierRegistryEntryV2 {
        VerifierRegistryEntryV2 {
            status: VerifierEntryStatusV1::Active,
            statement_version: 1,
            pool: [1u8; 32],
            verifier_program: [2u8; 32],
            profile_binding: [3u8; 32],
            release_binding: [4u8; 32],
            loader_program: [5u8; 32],
            programdata_address: [6u8; 32],
            executable_hash: [7u8; 32],
            expected_upgrade_authority: [0u8; 32],
            activation_slot: 10,
            retirement_slot: POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
            policy_binding: [8u8; 32],
        }
    }

    #[test]
    fn v2_registry_and_entry_roundtrip_without_reinterpreting_v1() {
        let registry = registry_v2();
        let encoded_registry = encode_verifier_registry_v2(&registry).unwrap();
        assert_eq!(encoded_registry.len(), POOL_V1_VERIFIER_REGISTRY_V2_BYTES);
        assert_eq!(decode_verifier_registry_v2(&encoded_registry), Ok(registry));
        assert!(decode_verifier_registry_v1(&encoded_registry).is_err());

        let entry = entry_v2();
        let encoded_entry = encode_verifier_registry_entry_v2(&entry).unwrap();
        assert_eq!(encoded_entry.len(), POOL_V1_VERIFIER_ENTRY_V2_BYTES);
        assert_eq!(decode_verifier_registry_entry_v2(&encoded_entry), Ok(entry));
        assert!(decode_verifier_registry_entry_v1(&encoded_entry).is_err());

        let mut bad_mode = encoded_entry;
        bad_mode[7] = 2;
        assert_eq!(
            decode_verifier_registry_entry_v2(&bad_mode),
            Err(PoolV1VerifierRegistryFormatError::InvalidDeploymentMode)
        );
        assert_eq!(
            encode_verifier_registry_entry_v2(&VerifierRegistryEntryV2 {
                expected_upgrade_authority: [1u8; 32],
                ..entry
            }),
            Err(PoolV1VerifierRegistryFormatError::InvalidAuthorityMode)
        );
    }
}
