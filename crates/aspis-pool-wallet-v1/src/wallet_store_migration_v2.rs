//! Canonical, crash-recoverable ownership handoff from legacy wallet stores.
//!
//! `ASMG` is a small authority journal. Its `Prepared` image contains the
//! complete target bytes so recovery never has to reconstruct a migrated
//! state from a partially retired source set. `ASRT` is the fixed-size marker
//! written over each legacy source after ownership has committed.
//!
//! This module does not interpret the target format. It binds exact source and
//! target bytes, installs the target, advances authority monotonically and
//! makes legacy retirement mechanically auditable.

use std::{
    collections::HashSet,
    io,
    path::{Path, PathBuf},
};

use sha2::{Digest as _, Sha256};
use subtle::ConstantTimeEq;

use crate::durable_state::{AtomicReplaceBoundaryV1, AtomicStateFileV1, DurableStateErrorV1};

pub const WALLET_STORE_MIGRATION_AUTHORITY_FILE_V2: &str = ".aspis-wallet-v2-migration";
pub const WALLET_STORE_MIGRATION_MAGIC_V2: [u8; 4] = *b"ASMG";
pub const WALLET_STORE_MIGRATION_VERSION_V2: u8 = 1;
pub const WALLET_STORE_RETIREMENT_MAGIC_V2: [u8; 4] = *b"ASRT";
pub const WALLET_STORE_RETIREMENT_VERSION_V2: u8 = 1;

const MIGRATION_HEADER_BYTES_V2: usize = 224;
const SOURCE_DESCRIPTOR_BYTES_V2: usize = 112;
const MIGRATION_CHECKSUM_OFFSET_V2: usize = 184;
const RETIREMENT_BYTES_V2: usize = 256;
const RETIREMENT_CHECKSUM_OFFSET_V2: usize = 224;
const MAX_MIGRATION_IMAGE_BYTES_V2: usize = 64 * 1024 * 1024;
const SOURCE_COUNT_V2: usize = 5;

const SOURCE_DIGEST_DOMAIN_V2: &[u8] =
    b"aspis:pool-v1:wallet-store-migration:exact-source:sha256:v2";
const TARGET_DIGEST_DOMAIN_V2: &[u8] =
    b"aspis:pool-v1:wallet-store-migration:exact-target:sha256:v2";
const SOURCE_MANIFEST_DOMAIN_V2: &[u8] =
    b"aspis:pool-v1:wallet-store-migration:source-manifest:sha256:v2";
const MIGRATION_ID_DOMAIN_V2: &[u8] = b"aspis:pool-v1:wallet-store-migration:id:sha256:v2";
const MIGRATION_CHECKSUM_DOMAIN_V2: &[u8] =
    b"aspis:pool-v1:wallet-store-migration:journal-checksum:sha256:v2";
const RETIREMENT_CHECKSUM_DOMAIN_V2: &[u8] =
    b"aspis:pool-v1:wallet-store-migration:retirement-checksum:sha256:v2";
const CANONICAL_PATH_DOMAIN_V2: &[u8] =
    b"aspis:pool-v1:wallet-store-migration:canonical-path:sha256:v2";
const CANONICAL_DIRECTORY_DOMAIN_V2: &[u8] =
    b"aspis:pool-v1:wallet-store-migration:canonical-directory:sha256:v2";

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum WalletStoreSourceRoleV2 {
    WalletState = 1,
    WitnessState = 2,
    LaneForestState = 3,
    RelayerAdmissionState = 4,
    RelayerExecutionJournal = 5,
}

impl core::fmt::Debug for WalletStoreSourceRoleV2 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str(match self {
            Self::WalletState => "ASDW",
            Self::WitnessState => "ASWJ",
            Self::LaneForestState => "ASD8",
            Self::RelayerAdmissionState => "ASRQ",
            Self::RelayerExecutionJournal => "ASRJ",
        })
    }
}

impl WalletStoreSourceRoleV2 {
    pub const ALL: [Self; SOURCE_COUNT_V2] = [
        Self::WalletState,
        Self::WitnessState,
        Self::LaneForestState,
        Self::RelayerAdmissionState,
        Self::RelayerExecutionJournal,
    ];

    pub const fn magic_v2(self) -> [u8; 4] {
        match self {
            Self::WalletState => *b"ASDW",
            Self::WitnessState => *b"ASWJ",
            Self::LaneForestState => *b"ASD8",
            Self::RelayerAdmissionState => *b"ASRQ",
            Self::RelayerExecutionJournal => *b"ASRJ",
        }
    }

    fn from_byte_v2(byte: u8) -> Result<Self, WalletStoreMigrationErrorV2> {
        match byte {
            1 => Ok(Self::WalletState),
            2 => Ok(Self::WitnessState),
            3 => Ok(Self::LaneForestState),
            4 => Ok(Self::RelayerAdmissionState),
            5 => Ok(Self::RelayerExecutionJournal),
            _ => Err(WalletStoreMigrationErrorV2::InvalidSourceRole),
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct WalletStoreSourceDescriptorV2 {
    role: WalletStoreSourceRoleV2,
    magic: [u8; 4],
    version: u8,
    length: u64,
    digest: [u8; 32],
    path_digest: [u8; 32],
    authority_directory_digest: [u8; 32],
}

impl core::fmt::Debug for WalletStoreSourceDescriptorV2 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("WalletStoreSourceDescriptorV2")
            .field("role", &self.role)
            .field("version", &self.version)
            .field("length", &self.length)
            .field("digest", &"[REDACTED]")
            .finish()
    }
}

impl WalletStoreSourceDescriptorV2 {
    pub fn from_exact_path_and_bytes_v2(
        role: WalletStoreSourceRoleV2,
        source_path: impl AsRef<Path>,
        bytes: &[u8],
    ) -> Result<Self, WalletStoreMigrationErrorV2> {
        if bytes.len() < 5 || bytes.len() > MAX_MIGRATION_IMAGE_BYTES_V2 {
            return Err(WalletStoreMigrationErrorV2::InvalidSourceDescriptor);
        }
        let magic: [u8; 4] = bytes[..4]
            .try_into()
            .map_err(|_| WalletStoreMigrationErrorV2::InvalidSourceDescriptor)?;
        let version = bytes[4];
        if magic != role.magic_v2() || version == 0 {
            return Err(WalletStoreMigrationErrorV2::InvalidSourceDescriptor);
        }
        let on_disk = std::fs::read(source_path.as_ref())
            .map_err(|_| WalletStoreMigrationErrorV2::InvalidSourceDescriptor)?;
        if on_disk != bytes {
            return Err(WalletStoreMigrationErrorV2::InvalidSourceDescriptor);
        }
        let length =
            u64::try_from(bytes.len()).map_err(|_| WalletStoreMigrationErrorV2::CountOverflow)?;
        let digest = exact_source_digest_v2(role, bytes)?;
        let (path_digest, authority_directory_digest) =
            canonical_existing_path_digests_v2(source_path.as_ref())
                .map_err(|_| WalletStoreMigrationErrorV2::InvalidSourceDescriptor)?;
        Ok(Self {
            role,
            magic,
            version,
            length,
            digest,
            path_digest,
            authority_directory_digest,
        })
    }

    pub fn role(&self) -> WalletStoreSourceRoleV2 {
        self.role
    }

    pub fn magic(&self) -> &[u8; 4] {
        &self.magic
    }

    pub fn version(&self) -> u8 {
        self.version
    }

    pub fn length(&self) -> u64 {
        self.length
    }

    pub fn digest(&self) -> &[u8; 32] {
        &self.digest
    }

    pub fn path_digest(&self) -> &[u8; 32] {
        &self.path_digest
    }

    pub fn authority_directory_digest(&self) -> &[u8; 32] {
        &self.authority_directory_digest
    }

    fn validate_v2(&self) -> Result<(), WalletStoreMigrationErrorV2> {
        if self.magic != self.role.magic_v2()
            || self.version == 0
            || self.length < 5
            || self.digest == [0u8; 32]
            || self.path_digest == [0u8; 32]
            || self.authority_directory_digest == [0u8; 32]
        {
            return Err(WalletStoreMigrationErrorV2::InvalidSourceDescriptor);
        }
        Ok(())
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct WalletStoreMigrationPlanV2 {
    migration_id: [u8; 32],
    source_manifest_digest: [u8; 32],
    sources: Vec<WalletStoreSourceDescriptorV2>,
    target_digest: [u8; 32],
    target_path_digest: [u8; 32],
    authority_directory_digest: [u8; 32],
    target_bytes: Vec<u8>,
}

impl core::fmt::Debug for WalletStoreMigrationPlanV2 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("WalletStoreMigrationPlanV2")
            .field("source_count", &self.sources.len())
            .field("target_length", &self.target_bytes.len())
            .field("private_digests_and_target", &"[REDACTED]")
            .finish()
    }
}

impl WalletStoreMigrationPlanV2 {
    pub fn new_v2(
        mut sources: Vec<WalletStoreSourceDescriptorV2>,
        target_path: impl AsRef<Path>,
        target_bytes: Vec<u8>,
    ) -> Result<Self, WalletStoreMigrationErrorV2> {
        if target_bytes.is_empty() {
            return Err(WalletStoreMigrationErrorV2::InvalidTarget);
        }
        sources.sort_by_key(|source| source.role);
        validate_sources_v2(&sources)?;
        let (target_path_digest, authority_directory_digest) =
            canonical_bound_path_digests_v2(target_path.as_ref())
                .map_err(|_| WalletStoreMigrationErrorV2::InvalidTarget)?;
        if sources.iter().any(|source| {
            source.authority_directory_digest != authority_directory_digest
                || source.path_digest == target_path_digest
        }) {
            return Err(WalletStoreMigrationErrorV2::InvalidTarget);
        }
        let source_manifest_digest = source_manifest_digest_v2(&sources)?;
        let target_digest = exact_target_digest_v2(&target_bytes)?;
        let migration_id = migration_id_v2(
            source_manifest_digest,
            target_digest,
            target_path_digest,
            authority_directory_digest,
            target_bytes.len(),
        )?;
        let plan = Self {
            migration_id,
            source_manifest_digest,
            sources,
            target_digest,
            target_path_digest,
            authority_directory_digest,
            target_bytes,
        };
        plan.validate_v2()?;
        Ok(plan)
    }

    pub fn migration_id(&self) -> &[u8; 32] {
        &self.migration_id
    }

    pub fn source_manifest_digest(&self) -> &[u8; 32] {
        &self.source_manifest_digest
    }

    pub fn sources(&self) -> &[WalletStoreSourceDescriptorV2] {
        &self.sources
    }

    pub fn source_v2(
        &self,
        role: WalletStoreSourceRoleV2,
    ) -> Option<&WalletStoreSourceDescriptorV2> {
        self.sources.iter().find(|source| source.role == role)
    }

    pub fn target_digest(&self) -> &[u8; 32] {
        &self.target_digest
    }

    pub fn target_path_digest(&self) -> &[u8; 32] {
        &self.target_path_digest
    }

    pub fn authority_directory_digest(&self) -> &[u8; 32] {
        &self.authority_directory_digest
    }

    pub fn target_bytes(&self) -> &[u8] {
        &self.target_bytes
    }

    fn validate_v2(&self) -> Result<(), WalletStoreMigrationErrorV2> {
        validate_sources_v2(&self.sources)?;
        let source_manifest_digest = source_manifest_digest_v2(&self.sources)?;
        let target_digest = exact_target_digest_v2(&self.target_bytes)?;
        let migration_id = migration_id_v2(
            source_manifest_digest,
            target_digest,
            self.target_path_digest,
            self.authority_directory_digest,
            self.target_bytes.len(),
        )?;
        if self.target_bytes.is_empty()
            || self.target_path_digest == [0u8; 32]
            || self.authority_directory_digest == [0u8; 32]
            || self.sources.iter().any(|source| {
                source.authority_directory_digest != self.authority_directory_digest
                    || source.path_digest == self.target_path_digest
            })
            || !bool::from(self.source_manifest_digest.ct_eq(&source_manifest_digest))
            || !bool::from(self.target_digest.ct_eq(&target_digest))
            || !bool::from(self.migration_id.ct_eq(&migration_id))
        {
            return Err(WalletStoreMigrationErrorV2::DigestMismatch);
        }
        let encoded_length = MIGRATION_HEADER_BYTES_V2
            .checked_add(
                self.sources
                    .len()
                    .checked_mul(SOURCE_DESCRIPTOR_BYTES_V2)
                    .ok_or(WalletStoreMigrationErrorV2::CountOverflow)?,
            )
            .and_then(|length| length.checked_add(self.target_bytes.len()))
            .ok_or(WalletStoreMigrationErrorV2::CountOverflow)?;
        if encoded_length > MAX_MIGRATION_IMAGE_BYTES_V2 {
            return Err(WalletStoreMigrationErrorV2::ImageTooLarge);
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum WalletStoreMigrationPhaseV2 {
    Prepared = 1,
    TargetInstalled = 2,
    OwnershipCommitted = 3,
    LegacyRetired = 4,
}

impl WalletStoreMigrationPhaseV2 {
    fn from_byte_v2(byte: u8) -> Result<Self, WalletStoreMigrationErrorV2> {
        match byte {
            1 => Ok(Self::Prepared),
            2 => Ok(Self::TargetInstalled),
            3 => Ok(Self::OwnershipCommitted),
            4 => Ok(Self::LegacyRetired),
            _ => Err(WalletStoreMigrationErrorV2::InvalidPhase),
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct WalletStoreMigrationJournalStateV2 {
    phase: WalletStoreMigrationPhaseV2,
    plan: WalletStoreMigrationPlanV2,
}

impl core::fmt::Debug for WalletStoreMigrationJournalStateV2 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("WalletStoreMigrationJournalStateV2")
            .field("phase", &self.phase)
            .field("plan", &self.plan)
            .finish()
    }
}

impl WalletStoreMigrationJournalStateV2 {
    pub fn prepared_v2(plan: WalletStoreMigrationPlanV2) -> Self {
        Self {
            phase: WalletStoreMigrationPhaseV2::Prepared,
            plan,
        }
    }

    pub fn phase(&self) -> WalletStoreMigrationPhaseV2 {
        self.phase
    }

    pub fn plan(&self) -> &WalletStoreMigrationPlanV2 {
        &self.plan
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct WalletStoreMigrationReceiptV2 {
    migration_id: [u8; 32],
    phase: WalletStoreMigrationPhaseV2,
    source_manifest_digest: [u8; 32],
    target_length: u64,
    target_digest: [u8; 32],
    target_path_digest: [u8; 32],
}

impl core::fmt::Debug for WalletStoreMigrationReceiptV2 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("WalletStoreMigrationReceiptV2")
            .field("phase", &self.phase)
            .field("target_length", &self.target_length)
            .field("private_digests", &"[REDACTED]")
            .finish()
    }
}

impl WalletStoreMigrationReceiptV2 {
    pub fn migration_id(&self) -> &[u8; 32] {
        &self.migration_id
    }

    pub fn phase(&self) -> WalletStoreMigrationPhaseV2 {
        self.phase
    }

    pub fn source_manifest_digest(&self) -> &[u8; 32] {
        &self.source_manifest_digest
    }

    pub fn target_length(&self) -> u64 {
        self.target_length
    }

    pub fn target_digest(&self) -> &[u8; 32] {
        &self.target_digest
    }

    pub fn target_path_digest(&self) -> &[u8; 32] {
        &self.target_path_digest
    }

    /// Bind a later authoritative ASL2 generation to the one migration target
    /// path without pretending the ASMG genesis digest equals the evolved
    /// image. Current-image authenticity is checked independently against the
    /// external monotonic service.
    pub(crate) fn authenticates_target_path_v2(&self, path: &Path) -> bool {
        canonical_bound_path_digests_v2(path)
            .is_ok_and(|(path_digest, _)| path_digest == self.target_path_digest)
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct WalletStoreRetirementTombstoneV2 {
    role: WalletStoreSourceRoleV2,
    source_magic: [u8; 4],
    source_version: u8,
    source_length: u64,
    source_digest: [u8; 32],
    source_path_digest: [u8; 32],
    migration_id: [u8; 32],
    target_length: u64,
    target_digest: [u8; 32],
    target_path_digest: [u8; 32],
    authority_directory_digest: [u8; 32],
}

impl core::fmt::Debug for WalletStoreRetirementTombstoneV2 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("WalletStoreRetirementTombstoneV2")
            .field("role", &self.role)
            .field("source_version", &self.source_version)
            .field("source_length", &self.source_length)
            .field("target_length", &self.target_length)
            .field("private_digests", &"[REDACTED]")
            .finish()
    }
}

impl WalletStoreRetirementTombstoneV2 {
    fn from_plan_v2(
        role: WalletStoreSourceRoleV2,
        plan: &WalletStoreMigrationPlanV2,
    ) -> Result<Self, WalletStoreMigrationErrorV2> {
        let source = plan
            .source_v2(role)
            .ok_or(WalletStoreMigrationErrorV2::InvalidSourceRole)?;
        Ok(Self {
            role,
            source_magic: source.magic,
            source_version: source.version,
            source_length: source.length,
            source_digest: source.digest,
            source_path_digest: source.path_digest,
            migration_id: plan.migration_id,
            target_length: u64::try_from(plan.target_bytes.len())
                .map_err(|_| WalletStoreMigrationErrorV2::CountOverflow)?,
            target_digest: plan.target_digest,
            target_path_digest: plan.target_path_digest,
            authority_directory_digest: plan.authority_directory_digest,
        })
    }

    pub fn role(&self) -> WalletStoreSourceRoleV2 {
        self.role
    }

    pub fn source_magic(&self) -> &[u8; 4] {
        &self.source_magic
    }

    pub fn source_version(&self) -> u8 {
        self.source_version
    }

    pub fn source_length(&self) -> u64 {
        self.source_length
    }

    pub fn source_digest(&self) -> &[u8; 32] {
        &self.source_digest
    }

    pub fn source_path_digest(&self) -> &[u8; 32] {
        &self.source_path_digest
    }

    pub fn migration_id(&self) -> &[u8; 32] {
        &self.migration_id
    }

    pub fn target_length(&self) -> u64 {
        self.target_length
    }

    pub fn target_digest(&self) -> &[u8; 32] {
        &self.target_digest
    }

    pub fn target_path_digest(&self) -> &[u8; 32] {
        &self.target_path_digest
    }

    pub fn authority_directory_digest(&self) -> &[u8; 32] {
        &self.authority_directory_digest
    }

    fn validate_v2(&self) -> Result<(), WalletStoreMigrationErrorV2> {
        if self.source_magic != self.role.magic_v2()
            || self.source_version == 0
            || self.source_length < 5
            || self.source_digest == [0u8; 32]
            || self.source_path_digest == [0u8; 32]
            || self.migration_id == [0u8; 32]
            || self.target_length == 0
            || self.target_digest == [0u8; 32]
            || self.target_path_digest == [0u8; 32]
            || self.authority_directory_digest == [0u8; 32]
            || self.source_path_digest == self.target_path_digest
        {
            return Err(WalletStoreMigrationErrorV2::InvalidTombstone);
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WalletStoreMigrationUpdateV2 {
    Written,
    AlreadyPresent,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WalletStoreMigrationWriteV2 {
    JournalPrepared,
    TargetImage,
    JournalTargetInstalled,
    JournalOwnershipCommitted,
    LegacyTombstone(WalletStoreSourceRoleV2),
    JournalLegacyRetired,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WalletStoreMigrationLogicalBoundaryV2 {
    BeforeWrite,
    AfterWrite,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WalletStoreMigrationAtomicBoundaryV2 {
    TemporaryWrite,
    TemporaryFileSync,
    TargetRename,
    ParentDirectorySync,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WalletStoreMigrationLogicalFaultPointV2 {
    pub write: WalletStoreMigrationWriteV2,
    pub boundary: WalletStoreMigrationLogicalBoundaryV2,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WalletStoreMigrationAtomicFaultPointV2 {
    pub write: WalletStoreMigrationWriteV2,
    pub boundary: WalletStoreMigrationAtomicBoundaryV2,
}

pub trait WalletStoreMigrationFaultInjectorV2 {
    fn interrupt_logical_v2(&mut self, _: WalletStoreMigrationLogicalFaultPointV2) -> bool {
        false
    }

    fn interrupt_atomic_v2(&mut self, _: WalletStoreMigrationAtomicFaultPointV2) -> bool {
        false
    }
}

#[derive(Default)]
pub struct NoWalletStoreMigrationFaultsV2;

impl WalletStoreMigrationFaultInjectorV2 for NoWalletStoreMigrationFaultsV2 {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WalletStoreMigrationErrorV2 {
    Durable(DurableStateErrorV1),
    InvalidAuthorityPath,
    AuthorityBusy,
    MigrationInProgress,
    LegacyRetired,
    MissingJournal,
    WrongLength,
    WrongMagic,
    WrongVersion,
    NonZeroReserved,
    ChecksumMismatch,
    NonCanonicalEncoding,
    CountOverflow,
    ImageTooLarge,
    InvalidSourceRole,
    InvalidSourceDescriptor,
    InvalidPathBinding,
    NonCanonicalSourceOrder,
    DuplicateSource,
    InvalidTarget,
    DigestMismatch,
    MigrationConflict,
    SourceConflict,
    TargetConflict,
    InvalidPhase,
    PhaseRegression,
    InvalidTombstone,
    Poisoned,
    InjectedLogicalFault(WalletStoreMigrationLogicalFaultPointV2),
    InjectedAtomicFault(WalletStoreMigrationAtomicFaultPointV2),
}

impl From<DurableStateErrorV1> for WalletStoreMigrationErrorV2 {
    fn from(error: DurableStateErrorV1) -> Self {
        Self::Durable(error)
    }
}

pub fn wallet_store_migration_authority_path_v2(
    legacy_store_path: &Path,
) -> Result<PathBuf, WalletStoreMigrationErrorV2> {
    let parent = legacy_store_path
        .parent()
        .ok_or(WalletStoreMigrationErrorV2::InvalidAuthorityPath)?;
    if legacy_store_path.file_name().is_none() {
        return Err(WalletStoreMigrationErrorV2::InvalidAuthorityPath);
    }
    Ok(parent.join(WALLET_STORE_MIGRATION_AUTHORITY_FILE_V2))
}

/// Fail-closed authority probe used immediately before and immediately after a
/// legacy constructor acquires its own state lock. Migration must acquire all
/// source locks before writing `Prepared`; this two-sided check therefore
/// closes the open/migration race without requiring multiple legacy handles to
/// share one re-entrant file lock.
pub(crate) fn check_legacy_wallet_store_writer_allowed_v2(
    legacy_store_path: &Path,
) -> Result<(), WalletStoreMigrationErrorV2> {
    let authority_path = wallet_store_migration_authority_path_v2(legacy_store_path)?;
    let authority = match AtomicStateFileV1::acquire(&authority_path) {
        Ok(authority) => authority,
        Err(DurableStateErrorV1::AlreadyLocked) => {
            return Err(WalletStoreMigrationErrorV2::AuthorityBusy)
        }
        Err(error) => return Err(error.into()),
    };
    let Some(bytes) = authority.read_optional()? else {
        return Ok(());
    };
    if bytes.starts_with(&WALLET_STORE_MIGRATION_MAGIC_V2) {
        let state = decode_wallet_store_migration_journal_v2(&bytes)?;
        return Err(match state.phase {
            WalletStoreMigrationPhaseV2::Prepared
            | WalletStoreMigrationPhaseV2::TargetInstalled => {
                WalletStoreMigrationErrorV2::MigrationInProgress
            }
            WalletStoreMigrationPhaseV2::OwnershipCommitted
            | WalletStoreMigrationPhaseV2::LegacyRetired => {
                WalletStoreMigrationErrorV2::LegacyRetired
            }
        });
    }
    if bytes.starts_with(&WALLET_STORE_RETIREMENT_MAGIC_V2) {
        decode_wallet_store_retirement_tombstone_v2(&bytes)?;
        return Err(WalletStoreMigrationErrorV2::LegacyRetired);
    }
    Err(WalletStoreMigrationErrorV2::WrongMagic)
}

pub fn encode_wallet_store_migration_journal_v2(
    state: &WalletStoreMigrationJournalStateV2,
) -> Result<Vec<u8>, WalletStoreMigrationErrorV2> {
    state.plan.validate_v2()?;
    let target_length = state.plan.target_bytes.len();
    let descriptors_length = state
        .plan
        .sources
        .len()
        .checked_mul(SOURCE_DESCRIPTOR_BYTES_V2)
        .ok_or(WalletStoreMigrationErrorV2::CountOverflow)?;
    let length = MIGRATION_HEADER_BYTES_V2
        .checked_add(descriptors_length)
        .and_then(|value| value.checked_add(target_length))
        .ok_or(WalletStoreMigrationErrorV2::CountOverflow)?;
    if length > MAX_MIGRATION_IMAGE_BYTES_V2 {
        return Err(WalletStoreMigrationErrorV2::ImageTooLarge);
    }
    let mut bytes = vec![0u8; length];
    bytes[..4].copy_from_slice(&WALLET_STORE_MIGRATION_MAGIC_V2);
    bytes[4] = WALLET_STORE_MIGRATION_VERSION_V2;
    bytes[5] = state.phase as u8;
    bytes[6] = u8::try_from(state.plan.sources.len())
        .map_err(|_| WalletStoreMigrationErrorV2::CountOverflow)?;
    bytes[8..16].copy_from_slice(
        &u64::try_from(target_length)
            .map_err(|_| WalletStoreMigrationErrorV2::CountOverflow)?
            .to_le_bytes(),
    );
    bytes[16..24].copy_from_slice(
        &u64::try_from(length)
            .map_err(|_| WalletStoreMigrationErrorV2::CountOverflow)?
            .to_le_bytes(),
    );
    bytes[24..56].copy_from_slice(&state.plan.migration_id);
    bytes[56..88].copy_from_slice(&state.plan.source_manifest_digest);
    bytes[88..120].copy_from_slice(&state.plan.target_digest);
    bytes[120..152].copy_from_slice(&state.plan.target_path_digest);
    bytes[152..184].copy_from_slice(&state.plan.authority_directory_digest);
    let mut offset = MIGRATION_HEADER_BYTES_V2;
    for source in &state.plan.sources {
        encode_source_descriptor_v2(
            source,
            &mut bytes[offset..offset + SOURCE_DESCRIPTOR_BYTES_V2],
        )?;
        offset += SOURCE_DESCRIPTOR_BYTES_V2;
    }
    bytes[offset..].copy_from_slice(&state.plan.target_bytes);
    let checksum = migration_checksum_v2(&bytes)?;
    bytes[MIGRATION_CHECKSUM_OFFSET_V2..MIGRATION_CHECKSUM_OFFSET_V2 + 32]
        .copy_from_slice(&checksum);
    Ok(bytes)
}

pub fn decode_wallet_store_migration_journal_v2(
    bytes: &[u8],
) -> Result<WalletStoreMigrationJournalStateV2, WalletStoreMigrationErrorV2> {
    if bytes.len() < MIGRATION_HEADER_BYTES_V2 || bytes.len() > MAX_MIGRATION_IMAGE_BYTES_V2 {
        return Err(WalletStoreMigrationErrorV2::WrongLength);
    }
    if bytes[..4] != WALLET_STORE_MIGRATION_MAGIC_V2 {
        return Err(WalletStoreMigrationErrorV2::WrongMagic);
    }
    if bytes[4] != WALLET_STORE_MIGRATION_VERSION_V2 {
        return Err(WalletStoreMigrationErrorV2::WrongVersion);
    }
    let phase = WalletStoreMigrationPhaseV2::from_byte_v2(bytes[5])?;
    let source_count = bytes[6] as usize;
    if source_count != SOURCE_COUNT_V2 {
        return Err(WalletStoreMigrationErrorV2::InvalidSourceRole);
    }
    if bytes[7] != 0 || bytes[216..224].iter().any(|byte| *byte != 0) {
        return Err(WalletStoreMigrationErrorV2::NonZeroReserved);
    }
    let target_length = usize::try_from(u64::from_le_bytes(
        bytes[8..16]
            .try_into()
            .map_err(|_| WalletStoreMigrationErrorV2::WrongLength)?,
    ))
    .map_err(|_| WalletStoreMigrationErrorV2::CountOverflow)?;
    let encoded_length = usize::try_from(u64::from_le_bytes(
        bytes[16..24]
            .try_into()
            .map_err(|_| WalletStoreMigrationErrorV2::WrongLength)?,
    ))
    .map_err(|_| WalletStoreMigrationErrorV2::CountOverflow)?;
    let descriptors_length = source_count
        .checked_mul(SOURCE_DESCRIPTOR_BYTES_V2)
        .ok_or(WalletStoreMigrationErrorV2::CountOverflow)?;
    let expected_length = MIGRATION_HEADER_BYTES_V2
        .checked_add(descriptors_length)
        .and_then(|value| value.checked_add(target_length))
        .ok_or(WalletStoreMigrationErrorV2::CountOverflow)?;
    if encoded_length != bytes.len() || expected_length != bytes.len() || target_length == 0 {
        return Err(WalletStoreMigrationErrorV2::WrongLength);
    }
    let encoded_checksum: [u8; 32] = bytes
        [MIGRATION_CHECKSUM_OFFSET_V2..MIGRATION_CHECKSUM_OFFSET_V2 + 32]
        .try_into()
        .map_err(|_| WalletStoreMigrationErrorV2::WrongLength)?;
    if !bool::from(encoded_checksum.ct_eq(&migration_checksum_v2(bytes)?)) {
        return Err(WalletStoreMigrationErrorV2::ChecksumMismatch);
    }
    let mut sources = Vec::with_capacity(source_count);
    let mut offset = MIGRATION_HEADER_BYTES_V2;
    for _ in 0..source_count {
        sources.push(decode_source_descriptor_v2(
            &bytes[offset..offset + SOURCE_DESCRIPTOR_BYTES_V2],
        )?);
        offset += SOURCE_DESCRIPTOR_BYTES_V2;
    }
    validate_sources_v2(&sources)?;
    let target_bytes = bytes[offset..].to_vec();
    let plan = WalletStoreMigrationPlanV2 {
        migration_id: bytes[24..56]
            .try_into()
            .map_err(|_| WalletStoreMigrationErrorV2::WrongLength)?,
        source_manifest_digest: bytes[56..88]
            .try_into()
            .map_err(|_| WalletStoreMigrationErrorV2::WrongLength)?,
        sources,
        target_digest: bytes[88..120]
            .try_into()
            .map_err(|_| WalletStoreMigrationErrorV2::WrongLength)?,
        target_path_digest: bytes[120..152]
            .try_into()
            .map_err(|_| WalletStoreMigrationErrorV2::WrongLength)?,
        authority_directory_digest: bytes[152..184]
            .try_into()
            .map_err(|_| WalletStoreMigrationErrorV2::WrongLength)?,
        target_bytes,
    };
    plan.validate_v2()?;
    let state = WalletStoreMigrationJournalStateV2 { phase, plan };
    if encode_wallet_store_migration_journal_v2(&state)? != bytes {
        return Err(WalletStoreMigrationErrorV2::NonCanonicalEncoding);
    }
    Ok(state)
}

pub fn encode_wallet_store_retirement_tombstone_v2(
    tombstone: &WalletStoreRetirementTombstoneV2,
) -> Result<Vec<u8>, WalletStoreMigrationErrorV2> {
    tombstone.validate_v2()?;
    let mut bytes = vec![0u8; RETIREMENT_BYTES_V2];
    bytes[..4].copy_from_slice(&WALLET_STORE_RETIREMENT_MAGIC_V2);
    bytes[4] = WALLET_STORE_RETIREMENT_VERSION_V2;
    bytes[5] = tombstone.role as u8;
    bytes[6] = tombstone.source_version;
    bytes[8..40].copy_from_slice(&tombstone.migration_id);
    bytes[40..44].copy_from_slice(&tombstone.source_magic);
    bytes[48..56].copy_from_slice(&tombstone.source_length.to_le_bytes());
    bytes[56..88].copy_from_slice(&tombstone.source_digest);
    bytes[88..96].copy_from_slice(&tombstone.target_length.to_le_bytes());
    bytes[96..128].copy_from_slice(&tombstone.target_digest);
    bytes[128..160].copy_from_slice(&tombstone.source_path_digest);
    bytes[160..192].copy_from_slice(&tombstone.target_path_digest);
    bytes[192..224].copy_from_slice(&tombstone.authority_directory_digest);
    let checksum = retirement_checksum_v2(&bytes)?;
    bytes[RETIREMENT_CHECKSUM_OFFSET_V2..].copy_from_slice(&checksum);
    Ok(bytes)
}

pub fn decode_wallet_store_retirement_tombstone_v2(
    bytes: &[u8],
) -> Result<WalletStoreRetirementTombstoneV2, WalletStoreMigrationErrorV2> {
    if bytes.len() != RETIREMENT_BYTES_V2 {
        return Err(WalletStoreMigrationErrorV2::WrongLength);
    }
    if bytes[..4] != WALLET_STORE_RETIREMENT_MAGIC_V2 {
        return Err(WalletStoreMigrationErrorV2::WrongMagic);
    }
    if bytes[4] != WALLET_STORE_RETIREMENT_VERSION_V2 {
        return Err(WalletStoreMigrationErrorV2::WrongVersion);
    }
    if bytes[7] != 0 || bytes[44..48].iter().any(|byte| *byte != 0) {
        return Err(WalletStoreMigrationErrorV2::NonZeroReserved);
    }
    let encoded_checksum: [u8; 32] = bytes[RETIREMENT_CHECKSUM_OFFSET_V2..]
        .try_into()
        .map_err(|_| WalletStoreMigrationErrorV2::WrongLength)?;
    if !bool::from(encoded_checksum.ct_eq(&retirement_checksum_v2(bytes)?)) {
        return Err(WalletStoreMigrationErrorV2::ChecksumMismatch);
    }
    let tombstone = WalletStoreRetirementTombstoneV2 {
        role: WalletStoreSourceRoleV2::from_byte_v2(bytes[5])?,
        source_magic: bytes[40..44]
            .try_into()
            .map_err(|_| WalletStoreMigrationErrorV2::WrongLength)?,
        source_version: bytes[6],
        source_length: u64::from_le_bytes(
            bytes[48..56]
                .try_into()
                .map_err(|_| WalletStoreMigrationErrorV2::WrongLength)?,
        ),
        source_digest: bytes[56..88]
            .try_into()
            .map_err(|_| WalletStoreMigrationErrorV2::WrongLength)?,
        source_path_digest: bytes[128..160]
            .try_into()
            .map_err(|_| WalletStoreMigrationErrorV2::WrongLength)?,
        migration_id: bytes[8..40]
            .try_into()
            .map_err(|_| WalletStoreMigrationErrorV2::WrongLength)?,
        target_length: u64::from_le_bytes(
            bytes[88..96]
                .try_into()
                .map_err(|_| WalletStoreMigrationErrorV2::WrongLength)?,
        ),
        target_digest: bytes[96..128]
            .try_into()
            .map_err(|_| WalletStoreMigrationErrorV2::WrongLength)?,
        target_path_digest: bytes[160..192]
            .try_into()
            .map_err(|_| WalletStoreMigrationErrorV2::WrongLength)?,
        authority_directory_digest: bytes[192..224]
            .try_into()
            .map_err(|_| WalletStoreMigrationErrorV2::WrongLength)?,
    };
    tombstone.validate_v2()?;
    if encode_wallet_store_retirement_tombstone_v2(&tombstone)? != bytes {
        return Err(WalletStoreMigrationErrorV2::NonCanonicalEncoding);
    }
    Ok(tombstone)
}

pub fn validate_wallet_store_migration_phase_transition_v2(
    current: WalletStoreMigrationPhaseV2,
    next: WalletStoreMigrationPhaseV2,
) -> Result<WalletStoreMigrationUpdateV2, WalletStoreMigrationErrorV2> {
    if current == next {
        return Ok(WalletStoreMigrationUpdateV2::AlreadyPresent);
    }
    if next < current {
        return Err(WalletStoreMigrationErrorV2::PhaseRegression);
    }
    if next as u8 != current as u8 + 1 {
        return Err(WalletStoreMigrationErrorV2::InvalidPhase);
    }
    Ok(WalletStoreMigrationUpdateV2::Written)
}

pub struct DurableWalletStoreMigrationJournalV2 {
    file: AtomicStateFileV1,
    state: WalletStoreMigrationJournalStateV2,
    poisoned: bool,
}

impl DurableWalletStoreMigrationJournalV2 {
    pub fn open_or_prepare_v2(
        path: impl AsRef<Path>,
        plan: WalletStoreMigrationPlanV2,
    ) -> Result<(Self, WalletStoreMigrationUpdateV2), WalletStoreMigrationErrorV2> {
        Self::open_or_prepare_with_faults_v2(path, plan, &mut NoWalletStoreMigrationFaultsV2)
    }

    pub fn open_or_prepare_with_faults_v2<F: WalletStoreMigrationFaultInjectorV2>(
        path: impl AsRef<Path>,
        plan: WalletStoreMigrationPlanV2,
        faults: &mut F,
    ) -> Result<(Self, WalletStoreMigrationUpdateV2), WalletStoreMigrationErrorV2> {
        plan.validate_v2()?;
        validate_authority_path_for_plan_v2(path.as_ref(), &plan)?;
        let file = AtomicStateFileV1::acquire(path.as_ref())?;
        if let Some(bytes) = file.read_optional()? {
            let state = decode_wallet_store_migration_journal_v2(&bytes)?;
            if state.plan != plan {
                return Err(WalletStoreMigrationErrorV2::MigrationConflict);
            }
            return Ok((
                Self {
                    file,
                    state,
                    poisoned: false,
                },
                WalletStoreMigrationUpdateV2::AlreadyPresent,
            ));
        }
        let state = WalletStoreMigrationJournalStateV2::prepared_v2(plan);
        let bytes = encode_wallet_store_migration_journal_v2(&state)?;
        replace_with_faults_v2(
            &file,
            &bytes,
            WalletStoreMigrationWriteV2::JournalPrepared,
            faults,
        )?;
        Ok((
            Self {
                file,
                state,
                poisoned: false,
            },
            WalletStoreMigrationUpdateV2::Written,
        ))
    }

    pub fn open_existing_v2(path: impl AsRef<Path>) -> Result<Self, WalletStoreMigrationErrorV2> {
        validate_authority_path_v2(path.as_ref())?;
        let file = AtomicStateFileV1::acquire(path.as_ref())?;
        let bytes = file
            .read_optional()?
            .ok_or(WalletStoreMigrationErrorV2::MissingJournal)?;
        let state = decode_wallet_store_migration_journal_v2(&bytes)?;
        validate_authority_path_for_plan_v2(path.as_ref(), &state.plan)?;
        Ok(Self {
            file,
            state,
            poisoned: false,
        })
    }

    pub fn state_v2(
        &self,
    ) -> Result<&WalletStoreMigrationJournalStateV2, WalletStoreMigrationErrorV2> {
        self.ensure_live_v2()?;
        Ok(&self.state)
    }

    pub fn receipt_v2(&self) -> Result<WalletStoreMigrationReceiptV2, WalletStoreMigrationErrorV2> {
        self.ensure_live_v2()?;
        Ok(receipt_v2(&self.state))
    }

    pub fn target_bytes_v2(&self) -> Result<&[u8], WalletStoreMigrationErrorV2> {
        self.ensure_live_v2()?;
        Ok(&self.state.plan.target_bytes)
    }

    pub fn is_poisoned_v2(&self) -> bool {
        self.poisoned
    }

    /// Read the currently installed image only from the path bound into ASMG.
    /// Used by non-mutating exact recovery after legacy retirement, where the
    /// live ASL2 image may legitimately have advanced beyond genesis.
    pub fn read_bound_target_v2(
        &self,
        target_path: impl AsRef<Path>,
    ) -> Result<Vec<u8>, WalletStoreMigrationErrorV2> {
        self.ensure_live_v2()?;
        self.validate_target_path_binding_v2(target_path.as_ref())?;
        let target = AtomicStateFileV1::acquire(target_path.as_ref())?;
        target
            .read_optional()?
            .ok_or(WalletStoreMigrationErrorV2::TargetConflict)
    }

    pub fn install_target_v2(
        &mut self,
        target_path: impl AsRef<Path>,
    ) -> Result<WalletStoreMigrationUpdateV2, WalletStoreMigrationErrorV2> {
        self.install_target_with_faults_v2(target_path, &mut NoWalletStoreMigrationFaultsV2)
    }

    pub fn install_target_with_faults_v2<F: WalletStoreMigrationFaultInjectorV2>(
        &mut self,
        target_path: impl AsRef<Path>,
        faults: &mut F,
    ) -> Result<WalletStoreMigrationUpdateV2, WalletStoreMigrationErrorV2> {
        self.ensure_live_v2()?;
        self.validate_target_path_binding_v2(target_path.as_ref())?;
        if self.state.phase > WalletStoreMigrationPhaseV2::TargetInstalled {
            return Ok(WalletStoreMigrationUpdateV2::AlreadyPresent);
        }
        if self.state.phase == WalletStoreMigrationPhaseV2::TargetInstalled {
            return self.verify_installed_target_v2(target_path.as_ref());
        }
        let target = AtomicStateFileV1::acquire(target_path.as_ref())?;
        match target.read_optional()? {
            Some(bytes) if bytes == self.state.plan.target_bytes => {}
            Some(_) => return Err(WalletStoreMigrationErrorV2::TargetConflict),
            None => {
                if let Err(error) = replace_with_faults_v2(
                    &target,
                    &self.state.plan.target_bytes,
                    WalletStoreMigrationWriteV2::TargetImage,
                    faults,
                ) {
                    self.poisoned = true;
                    return Err(error);
                }
            }
        }
        drop(target);
        self.persist_phase_with_faults_v2(
            WalletStoreMigrationPhaseV2::TargetInstalled,
            WalletStoreMigrationWriteV2::JournalTargetInstalled,
            faults,
        )?;
        Ok(WalletStoreMigrationUpdateV2::Written)
    }

    #[cfg(test)]
    fn commit_ownership_v2(
        &mut self,
        target_path: impl AsRef<Path>,
    ) -> Result<WalletStoreMigrationUpdateV2, WalletStoreMigrationErrorV2> {
        self.commit_ownership_with_faults_v2(target_path, &mut NoWalletStoreMigrationFaultsV2)
    }

    #[cfg(test)]
    fn commit_ownership_with_faults_v2<F: WalletStoreMigrationFaultInjectorV2>(
        &mut self,
        target_path: impl AsRef<Path>,
        faults: &mut F,
    ) -> Result<WalletStoreMigrationUpdateV2, WalletStoreMigrationErrorV2> {
        self.ensure_live_v2()?;
        self.validate_target_path_binding_v2(target_path.as_ref())?;
        if self.state.phase >= WalletStoreMigrationPhaseV2::OwnershipCommitted {
            return Ok(WalletStoreMigrationUpdateV2::AlreadyPresent);
        }
        if self.state.phase != WalletStoreMigrationPhaseV2::TargetInstalled {
            return Err(WalletStoreMigrationErrorV2::InvalidPhase);
        }
        // Keep the exact target locked through the durable authority decision.
        // A cooperative target writer therefore cannot mutate or replace the
        // installed genesis between verification and OwnershipCommitted.
        let target = AtomicStateFileV1::acquire(target_path.as_ref())?;
        let bytes = target
            .read_optional()?
            .ok_or(WalletStoreMigrationErrorV2::TargetConflict)?;
        if bytes != self.state.plan.target_bytes {
            return Err(WalletStoreMigrationErrorV2::TargetConflict);
        }
        self.persist_phase_with_faults_v2(
            WalletStoreMigrationPhaseV2::OwnershipCommitted,
            WalletStoreMigrationWriteV2::JournalOwnershipCommitted,
            faults,
        )?;
        drop(target);
        Ok(WalletStoreMigrationUpdateV2::Written)
    }

    #[cfg(test)]
    fn retire_legacy_store_v2(
        &mut self,
        role: WalletStoreSourceRoleV2,
        source_path: impl AsRef<Path>,
    ) -> Result<WalletStoreMigrationUpdateV2, WalletStoreMigrationErrorV2> {
        self.retire_legacy_store_with_faults_v2(
            role,
            source_path,
            &mut NoWalletStoreMigrationFaultsV2,
        )
    }

    #[cfg(test)]
    fn retire_legacy_store_with_faults_v2<F: WalletStoreMigrationFaultInjectorV2>(
        &mut self,
        role: WalletStoreSourceRoleV2,
        source_path: impl AsRef<Path>,
        faults: &mut F,
    ) -> Result<WalletStoreMigrationUpdateV2, WalletStoreMigrationErrorV2> {
        self.ensure_live_v2()?;
        if self.state.phase < WalletStoreMigrationPhaseV2::OwnershipCommitted {
            return Err(WalletStoreMigrationErrorV2::InvalidPhase);
        }
        if source_path.as_ref() == self.file.path_v1() {
            return Err(WalletStoreMigrationErrorV2::SourceConflict);
        }
        self.validate_source_path_binding_v2(role, source_path.as_ref())?;
        let expected = WalletStoreRetirementTombstoneV2::from_plan_v2(role, &self.state.plan)?;
        let expected_bytes = encode_wallet_store_retirement_tombstone_v2(&expected)?;
        let source_file = AtomicStateFileV1::acquire(source_path.as_ref())?;
        let bytes = source_file
            .read_optional()?
            .ok_or(WalletStoreMigrationErrorV2::SourceConflict)?;
        if bytes.starts_with(&WALLET_STORE_RETIREMENT_MAGIC_V2) {
            let existing = decode_wallet_store_retirement_tombstone_v2(&bytes)
                .map_err(|_| WalletStoreMigrationErrorV2::SourceConflict)?;
            return if existing == expected {
                Ok(WalletStoreMigrationUpdateV2::AlreadyPresent)
            } else {
                Err(WalletStoreMigrationErrorV2::MigrationConflict)
            };
        }
        let actual = WalletStoreSourceDescriptorV2::from_exact_path_and_bytes_v2(
            role,
            source_path.as_ref(),
            &bytes,
        )
        .map_err(|_| WalletStoreMigrationErrorV2::SourceConflict)?;
        let expected_source = self
            .state
            .plan
            .source_v2(role)
            .ok_or(WalletStoreMigrationErrorV2::InvalidSourceRole)?;
        if actual != *expected_source {
            return Err(WalletStoreMigrationErrorV2::SourceConflict);
        }
        if let Err(error) = replace_with_faults_v2(
            &source_file,
            &expected_bytes,
            WalletStoreMigrationWriteV2::LegacyTombstone(role),
            faults,
        ) {
            self.poisoned = true;
            return Err(error);
        }
        Ok(WalletStoreMigrationUpdateV2::Written)
    }

    #[cfg(test)]
    fn complete_legacy_retirement_v2(
        &mut self,
        source_paths: &[(WalletStoreSourceRoleV2, PathBuf)],
    ) -> Result<WalletStoreMigrationUpdateV2, WalletStoreMigrationErrorV2> {
        self.complete_legacy_retirement_for_test_with_faults_v2(
            source_paths,
            &mut NoWalletStoreMigrationFaultsV2,
        )
    }

    /// Commit ownership when needed and hold the exact prepared ASL2 target
    /// lock continuously across every destructive ASRT replacement and the
    /// final `LegacyRetired` journal decision. Recovery can therefore never
    /// retire the last valid legacy copy after a missing/replaced target.
    pub fn commit_ownership_and_retire_with_target_guard_v2<
        F: WalletStoreMigrationFaultInjectorV2,
    >(
        &mut self,
        target_path: impl AsRef<Path>,
        source_paths: &[(WalletStoreSourceRoleV2, PathBuf)],
        faults: &mut F,
    ) -> Result<WalletStoreMigrationUpdateV2, WalletStoreMigrationErrorV2> {
        self.ensure_live_v2()?;
        self.validate_target_path_binding_v2(target_path.as_ref())?;
        if self.state.phase < WalletStoreMigrationPhaseV2::TargetInstalled {
            return Err(WalletStoreMigrationErrorV2::InvalidPhase);
        }
        validate_source_paths_v2(source_paths)?;
        for (role, path) in source_paths {
            self.validate_source_path_binding_v2(*role, path)?;
        }
        if self.state.phase == WalletStoreMigrationPhaseV2::LegacyRetired {
            return Ok(WalletStoreMigrationUpdateV2::AlreadyPresent);
        }
        let mut ordered = source_paths.to_vec();
        ordered.sort_by_key(|(role, _)| *role);

        let target = AtomicStateFileV1::acquire(target_path.as_ref())?;
        let bytes = target
            .read_optional()?
            .ok_or(WalletStoreMigrationErrorV2::TargetConflict)?;
        if bytes != self.state.plan.target_bytes {
            return Err(WalletStoreMigrationErrorV2::TargetConflict);
        }

        // Preflight and lock every source before the authority decision or the
        // first destructive ASRT replacement. A bad later path/image can
        // therefore never follow an earlier tombstone. Keeping all source
        // locks plus the target lock through LegacyRetired also excludes
        // cooperative legacy writers and target replacement during cutover.
        let mut locked_sources = Vec::with_capacity(ordered.len());
        for (role, path) in ordered {
            if path == self.file.path_v1() {
                return Err(WalletStoreMigrationErrorV2::SourceConflict);
            }
            let source_file = AtomicStateFileV1::acquire(&path)?;
            let source_bytes = source_file
                .read_optional()?
                .ok_or(WalletStoreMigrationErrorV2::SourceConflict)?;
            let tombstone = WalletStoreRetirementTombstoneV2::from_plan_v2(role, &self.state.plan)?;
            let tombstone_bytes = encode_wallet_store_retirement_tombstone_v2(&tombstone)?;
            let already_retired = if source_bytes.starts_with(&WALLET_STORE_RETIREMENT_MAGIC_V2) {
                let existing = decode_wallet_store_retirement_tombstone_v2(&source_bytes)
                    .map_err(|_| WalletStoreMigrationErrorV2::SourceConflict)?;
                if existing != tombstone {
                    return Err(WalletStoreMigrationErrorV2::MigrationConflict);
                }
                true
            } else {
                let actual = WalletStoreSourceDescriptorV2::from_exact_path_and_bytes_v2(
                    role,
                    &path,
                    &source_bytes,
                )
                .map_err(|_| WalletStoreMigrationErrorV2::SourceConflict)?;
                let expected = self
                    .state
                    .plan
                    .source_v2(role)
                    .ok_or(WalletStoreMigrationErrorV2::InvalidSourceRole)?;
                if actual != *expected {
                    return Err(WalletStoreMigrationErrorV2::SourceConflict);
                }
                false
            };
            locked_sources.push((role, source_file, tombstone_bytes, already_retired));
        }

        let mut update = WalletStoreMigrationUpdateV2::AlreadyPresent;
        if self.state.phase == WalletStoreMigrationPhaseV2::TargetInstalled {
            self.persist_phase_with_faults_v2(
                WalletStoreMigrationPhaseV2::OwnershipCommitted,
                WalletStoreMigrationWriteV2::JournalOwnershipCommitted,
                faults,
            )?;
            update = WalletStoreMigrationUpdateV2::Written;
        }
        for (role, source_file, tombstone_bytes, already_retired) in &locked_sources {
            if !already_retired {
                if let Err(error) = replace_with_faults_v2(
                    source_file,
                    tombstone_bytes,
                    WalletStoreMigrationWriteV2::LegacyTombstone(*role),
                    faults,
                ) {
                    self.poisoned = true;
                    return Err(error);
                }
                update = WalletStoreMigrationUpdateV2::Written;
            }
        }
        if self.state.phase != WalletStoreMigrationPhaseV2::LegacyRetired {
            self.persist_phase_with_faults_v2(
                WalletStoreMigrationPhaseV2::LegacyRetired,
                WalletStoreMigrationWriteV2::JournalLegacyRetired,
                faults,
            )?;
            update = WalletStoreMigrationUpdateV2::Written;
        }
        drop(locked_sources);
        drop(target);
        Ok(update)
    }

    /// Verify an already committed retirement without any phase-changing
    /// capability. The sole production transition to `LegacyRetired` is the
    /// target-guarded composite above.
    pub(crate) fn verify_completed_legacy_retirement_v2(
        &mut self,
        source_paths: &[(WalletStoreSourceRoleV2, PathBuf)],
    ) -> Result<WalletStoreMigrationUpdateV2, WalletStoreMigrationErrorV2> {
        self.ensure_live_v2()?;
        if self.state.phase != WalletStoreMigrationPhaseV2::LegacyRetired {
            return Err(WalletStoreMigrationErrorV2::InvalidPhase);
        }
        let locked_sources = self.lock_and_validate_retired_sources_v2(source_paths)?;
        drop(locked_sources);
        Ok(WalletStoreMigrationUpdateV2::AlreadyPresent)
    }

    #[cfg(test)]
    fn complete_legacy_retirement_for_test_with_faults_v2<
        F: WalletStoreMigrationFaultInjectorV2,
    >(
        &mut self,
        source_paths: &[(WalletStoreSourceRoleV2, PathBuf)],
        faults: &mut F,
    ) -> Result<WalletStoreMigrationUpdateV2, WalletStoreMigrationErrorV2> {
        self.ensure_live_v2()?;
        if self.state.phase < WalletStoreMigrationPhaseV2::OwnershipCommitted {
            return Err(WalletStoreMigrationErrorV2::InvalidPhase);
        }
        let locked_sources = self.lock_and_validate_retired_sources_v2(source_paths)?;
        if self.state.phase == WalletStoreMigrationPhaseV2::LegacyRetired {
            return Ok(WalletStoreMigrationUpdateV2::AlreadyPresent);
        }
        self.persist_phase_with_faults_v2(
            WalletStoreMigrationPhaseV2::LegacyRetired,
            WalletStoreMigrationWriteV2::JournalLegacyRetired,
            faults,
        )?;
        drop(locked_sources);
        Ok(WalletStoreMigrationUpdateV2::Written)
    }

    fn lock_and_validate_retired_sources_v2(
        &self,
        source_paths: &[(WalletStoreSourceRoleV2, PathBuf)],
    ) -> Result<Vec<AtomicStateFileV1>, WalletStoreMigrationErrorV2> {
        validate_source_paths_v2(source_paths)?;
        for (role, path) in source_paths {
            self.validate_source_path_binding_v2(*role, path)?;
        }
        let mut ordered = source_paths.to_vec();
        ordered.sort_by_key(|(role, _)| *role);
        let mut locked_sources = Vec::with_capacity(ordered.len());
        for (role, path) in ordered {
            if path == self.file.path_v1() {
                return Err(WalletStoreMigrationErrorV2::SourceConflict);
            }
            let file = AtomicStateFileV1::acquire(&path)?;
            let bytes = file
                .read_optional()?
                .ok_or(WalletStoreMigrationErrorV2::SourceConflict)?;
            let existing = decode_wallet_store_retirement_tombstone_v2(&bytes)
                .map_err(|_| WalletStoreMigrationErrorV2::SourceConflict)?;
            let expected = WalletStoreRetirementTombstoneV2::from_plan_v2(role, &self.state.plan)?;
            if existing != expected {
                return Err(WalletStoreMigrationErrorV2::MigrationConflict);
            }
            locked_sources.push(file);
        }
        Ok(locked_sources)
    }

    fn verify_installed_target_v2(
        &self,
        target_path: &Path,
    ) -> Result<WalletStoreMigrationUpdateV2, WalletStoreMigrationErrorV2> {
        let target = AtomicStateFileV1::acquire(target_path)?;
        let bytes = target
            .read_optional()?
            .ok_or(WalletStoreMigrationErrorV2::TargetConflict)?;
        if bytes == self.state.plan.target_bytes {
            Ok(WalletStoreMigrationUpdateV2::AlreadyPresent)
        } else {
            Err(WalletStoreMigrationErrorV2::TargetConflict)
        }
    }

    fn validate_target_path_binding_v2(
        &self,
        target_path: &Path,
    ) -> Result<(), WalletStoreMigrationErrorV2> {
        if target_path == self.file.path_v1() {
            return Err(WalletStoreMigrationErrorV2::TargetConflict);
        }
        let (path_digest, directory_digest) = canonical_bound_path_digests_v2(target_path)
            .map_err(|_| WalletStoreMigrationErrorV2::TargetConflict)?;
        if path_digest != self.state.plan.target_path_digest
            || directory_digest != self.state.plan.authority_directory_digest
        {
            return Err(WalletStoreMigrationErrorV2::TargetConflict);
        }
        Ok(())
    }

    fn validate_source_path_binding_v2(
        &self,
        role: WalletStoreSourceRoleV2,
        source_path: &Path,
    ) -> Result<(), WalletStoreMigrationErrorV2> {
        let expected = self
            .state
            .plan
            .source_v2(role)
            .ok_or(WalletStoreMigrationErrorV2::InvalidSourceRole)?;
        let (path_digest, directory_digest) = canonical_existing_path_digests_v2(source_path)
            .map_err(|_| WalletStoreMigrationErrorV2::SourceConflict)?;
        if path_digest != expected.path_digest
            || directory_digest != expected.authority_directory_digest
        {
            return Err(WalletStoreMigrationErrorV2::SourceConflict);
        }
        Ok(())
    }

    fn persist_phase_with_faults_v2<F: WalletStoreMigrationFaultInjectorV2>(
        &mut self,
        phase: WalletStoreMigrationPhaseV2,
        write: WalletStoreMigrationWriteV2,
        faults: &mut F,
    ) -> Result<(), WalletStoreMigrationErrorV2> {
        validate_wallet_store_migration_phase_transition_v2(self.state.phase, phase)?;
        let candidate = WalletStoreMigrationJournalStateV2 {
            phase,
            plan: self.state.plan.clone(),
        };
        let bytes = encode_wallet_store_migration_journal_v2(&candidate)?;
        if let Err(error) = replace_with_faults_v2(&self.file, &bytes, write, faults) {
            self.poisoned = true;
            return Err(error);
        }
        self.state = candidate;
        Ok(())
    }

    fn ensure_live_v2(&self) -> Result<(), WalletStoreMigrationErrorV2> {
        if self.poisoned {
            Err(WalletStoreMigrationErrorV2::Poisoned)
        } else {
            Ok(())
        }
    }
}

fn receipt_v2(state: &WalletStoreMigrationJournalStateV2) -> WalletStoreMigrationReceiptV2 {
    WalletStoreMigrationReceiptV2 {
        migration_id: state.plan.migration_id,
        phase: state.phase,
        source_manifest_digest: state.plan.source_manifest_digest,
        target_length: state.plan.target_bytes.len() as u64,
        target_digest: state.plan.target_digest,
        target_path_digest: state.plan.target_path_digest,
    }
}

fn validate_authority_path_v2(path: &Path) -> Result<(), WalletStoreMigrationErrorV2> {
    if path.file_name().and_then(|name| name.to_str())
        != Some(WALLET_STORE_MIGRATION_AUTHORITY_FILE_V2)
    {
        return Err(WalletStoreMigrationErrorV2::InvalidAuthorityPath);
    }
    Ok(())
}

fn validate_authority_path_for_plan_v2(
    path: &Path,
    plan: &WalletStoreMigrationPlanV2,
) -> Result<(), WalletStoreMigrationErrorV2> {
    validate_authority_path_v2(path)?;
    let (path_digest, directory_digest) = canonical_bound_path_digests_v2(path)
        .map_err(|_| WalletStoreMigrationErrorV2::InvalidAuthorityPath)?;
    if directory_digest != plan.authority_directory_digest
        || path_digest == plan.target_path_digest
        || plan
            .sources
            .iter()
            .any(|source| source.path_digest == path_digest)
    {
        return Err(WalletStoreMigrationErrorV2::InvalidAuthorityPath);
    }
    Ok(())
}

fn validate_sources_v2(
    sources: &[WalletStoreSourceDescriptorV2],
) -> Result<(), WalletStoreMigrationErrorV2> {
    if sources.len() != SOURCE_COUNT_V2 {
        return Err(WalletStoreMigrationErrorV2::InvalidSourceRole);
    }
    let mut seen = HashSet::with_capacity(sources.len());
    let mut paths = HashSet::with_capacity(sources.len());
    let mut authority_directory_digest = None;
    for (source, expected_role) in sources.iter().zip(WalletStoreSourceRoleV2::ALL) {
        source.validate_v2()?;
        if !seen.insert(source.role) || !paths.insert(source.path_digest) {
            return Err(WalletStoreMigrationErrorV2::DuplicateSource);
        }
        if authority_directory_digest
            .replace(source.authority_directory_digest)
            .is_some_and(|expected| expected != source.authority_directory_digest)
        {
            return Err(WalletStoreMigrationErrorV2::InvalidSourceDescriptor);
        }
        if source.role != expected_role {
            return Err(WalletStoreMigrationErrorV2::NonCanonicalSourceOrder);
        }
    }
    Ok(())
}

fn validate_source_paths_v2(
    source_paths: &[(WalletStoreSourceRoleV2, PathBuf)],
) -> Result<(), WalletStoreMigrationErrorV2> {
    if source_paths.len() != SOURCE_COUNT_V2 {
        return Err(WalletStoreMigrationErrorV2::InvalidSourceRole);
    }
    let mut roles = HashSet::with_capacity(source_paths.len());
    let mut paths = HashSet::with_capacity(source_paths.len());
    for (role, path) in source_paths {
        if !roles.insert(*role) || !paths.insert(path.clone()) {
            return Err(WalletStoreMigrationErrorV2::DuplicateSource);
        }
    }
    if !WalletStoreSourceRoleV2::ALL
        .iter()
        .all(|role| roles.contains(role))
    {
        return Err(WalletStoreMigrationErrorV2::InvalidSourceRole);
    }
    Ok(())
}

fn canonical_existing_path_digests_v2(
    path: &Path,
) -> Result<([u8; 32], [u8; 32]), WalletStoreMigrationErrorV2> {
    let (bound_path_digest, directory_digest) = canonical_bound_path_digests_v2(path)?;
    let canonical =
        std::fs::canonicalize(path).map_err(|_| WalletStoreMigrationErrorV2::InvalidPathBinding)?;
    let canonical_digest = canonical_path_digest_v2(CANONICAL_PATH_DOMAIN_V2, &canonical)?;
    if !bool::from(canonical_digest.ct_eq(&bound_path_digest)) {
        return Err(WalletStoreMigrationErrorV2::InvalidPathBinding);
    }
    Ok((bound_path_digest, directory_digest))
}

/// Bind a possibly not-yet-created file to its canonical existing parent and
/// exact UTF-8 filename. Source paths are additionally canonicalized as a
/// whole by `canonical_existing_path_digests_v2`, which rejects file symlinks.
fn canonical_bound_path_digests_v2(
    path: &Path,
) -> Result<([u8; 32], [u8; 32]), WalletStoreMigrationErrorV2> {
    let parent = path
        .parent()
        .ok_or(WalletStoreMigrationErrorV2::InvalidPathBinding)?;
    let file_name = path
        .file_name()
        .ok_or(WalletStoreMigrationErrorV2::InvalidPathBinding)?;
    let canonical_parent = std::fs::canonicalize(parent)
        .map_err(|_| WalletStoreMigrationErrorV2::InvalidPathBinding)?;
    let canonical_path = canonical_parent.join(file_name);
    Ok((
        canonical_path_digest_v2(CANONICAL_PATH_DOMAIN_V2, &canonical_path)?,
        canonical_path_digest_v2(CANONICAL_DIRECTORY_DOMAIN_V2, &canonical_parent)?,
    ))
}

fn canonical_path_digest_v2(
    domain: &[u8],
    path: &Path,
) -> Result<[u8; 32], WalletStoreMigrationErrorV2> {
    let path = path
        .to_str()
        .ok_or(WalletStoreMigrationErrorV2::InvalidPathBinding)?
        .as_bytes();
    let length =
        u64::try_from(path.len()).map_err(|_| WalletStoreMigrationErrorV2::CountOverflow)?;
    let mut hasher = Sha256::new();
    hasher.update(domain);
    hasher.update(length.to_le_bytes());
    hasher.update(path);
    Ok(hasher.finalize().into())
}

fn exact_source_digest_v2(
    role: WalletStoreSourceRoleV2,
    bytes: &[u8],
) -> Result<[u8; 32], WalletStoreMigrationErrorV2> {
    let length =
        u64::try_from(bytes.len()).map_err(|_| WalletStoreMigrationErrorV2::CountOverflow)?;
    let mut hasher = Sha256::new();
    hasher.update(SOURCE_DIGEST_DOMAIN_V2);
    hasher.update([role as u8]);
    hasher.update(length.to_le_bytes());
    hasher.update(bytes);
    Ok(hasher.finalize().into())
}

fn exact_target_digest_v2(bytes: &[u8]) -> Result<[u8; 32], WalletStoreMigrationErrorV2> {
    let length =
        u64::try_from(bytes.len()).map_err(|_| WalletStoreMigrationErrorV2::CountOverflow)?;
    let mut hasher = Sha256::new();
    hasher.update(TARGET_DIGEST_DOMAIN_V2);
    hasher.update(length.to_le_bytes());
    hasher.update(bytes);
    Ok(hasher.finalize().into())
}

fn source_manifest_digest_v2(
    sources: &[WalletStoreSourceDescriptorV2],
) -> Result<[u8; 32], WalletStoreMigrationErrorV2> {
    validate_sources_v2(sources)?;
    let mut hasher = Sha256::new();
    hasher.update(SOURCE_MANIFEST_DOMAIN_V2);
    hasher.update([sources.len() as u8]);
    for source in sources {
        let mut encoded = [0u8; SOURCE_DESCRIPTOR_BYTES_V2];
        encode_source_descriptor_v2(source, &mut encoded)?;
        hasher.update(encoded);
    }
    Ok(hasher.finalize().into())
}

fn migration_id_v2(
    source_manifest_digest: [u8; 32],
    target_digest: [u8; 32],
    target_path_digest: [u8; 32],
    authority_directory_digest: [u8; 32],
    target_length: usize,
) -> Result<[u8; 32], WalletStoreMigrationErrorV2> {
    let target_length =
        u64::try_from(target_length).map_err(|_| WalletStoreMigrationErrorV2::CountOverflow)?;
    let mut hasher = Sha256::new();
    hasher.update(MIGRATION_ID_DOMAIN_V2);
    hasher.update(source_manifest_digest);
    hasher.update(target_length.to_le_bytes());
    hasher.update(target_digest);
    hasher.update(target_path_digest);
    hasher.update(authority_directory_digest);
    Ok(hasher.finalize().into())
}

fn encode_source_descriptor_v2(
    source: &WalletStoreSourceDescriptorV2,
    output: &mut [u8],
) -> Result<(), WalletStoreMigrationErrorV2> {
    source.validate_v2()?;
    if output.len() != SOURCE_DESCRIPTOR_BYTES_V2 {
        return Err(WalletStoreMigrationErrorV2::WrongLength);
    }
    output.fill(0);
    output[0] = source.role as u8;
    output[1] = source.version;
    output[4..8].copy_from_slice(&source.magic);
    output[8..16].copy_from_slice(&source.length.to_le_bytes());
    output[16..48].copy_from_slice(&source.digest);
    output[48..80].copy_from_slice(&source.path_digest);
    output[80..112].copy_from_slice(&source.authority_directory_digest);
    Ok(())
}

fn decode_source_descriptor_v2(
    bytes: &[u8],
) -> Result<WalletStoreSourceDescriptorV2, WalletStoreMigrationErrorV2> {
    if bytes.len() != SOURCE_DESCRIPTOR_BYTES_V2 {
        return Err(WalletStoreMigrationErrorV2::WrongLength);
    }
    if bytes[2..4].iter().any(|byte| *byte != 0) {
        return Err(WalletStoreMigrationErrorV2::NonZeroReserved);
    }
    let source = WalletStoreSourceDescriptorV2 {
        role: WalletStoreSourceRoleV2::from_byte_v2(bytes[0])?,
        magic: bytes[4..8]
            .try_into()
            .map_err(|_| WalletStoreMigrationErrorV2::WrongLength)?,
        version: bytes[1],
        length: u64::from_le_bytes(
            bytes[8..16]
                .try_into()
                .map_err(|_| WalletStoreMigrationErrorV2::WrongLength)?,
        ),
        digest: bytes[16..48]
            .try_into()
            .map_err(|_| WalletStoreMigrationErrorV2::WrongLength)?,
        path_digest: bytes[48..80]
            .try_into()
            .map_err(|_| WalletStoreMigrationErrorV2::WrongLength)?,
        authority_directory_digest: bytes[80..112]
            .try_into()
            .map_err(|_| WalletStoreMigrationErrorV2::WrongLength)?,
    };
    source.validate_v2()?;
    Ok(source)
}

fn migration_checksum_v2(bytes: &[u8]) -> Result<[u8; 32], WalletStoreMigrationErrorV2> {
    if bytes.len() < MIGRATION_HEADER_BYTES_V2 {
        return Err(WalletStoreMigrationErrorV2::WrongLength);
    }
    let mut hasher = Sha256::new();
    hasher.update(MIGRATION_CHECKSUM_DOMAIN_V2);
    hasher.update(
        u64::try_from(bytes.len())
            .map_err(|_| WalletStoreMigrationErrorV2::CountOverflow)?
            .to_le_bytes(),
    );
    hasher.update(&bytes[..MIGRATION_CHECKSUM_OFFSET_V2]);
    hasher.update([0u8; 32]);
    hasher.update(&bytes[MIGRATION_CHECKSUM_OFFSET_V2 + 32..]);
    Ok(hasher.finalize().into())
}

fn retirement_checksum_v2(bytes: &[u8]) -> Result<[u8; 32], WalletStoreMigrationErrorV2> {
    if bytes.len() != RETIREMENT_BYTES_V2 {
        return Err(WalletStoreMigrationErrorV2::WrongLength);
    }
    let mut hasher = Sha256::new();
    hasher.update(RETIREMENT_CHECKSUM_DOMAIN_V2);
    hasher.update(&bytes[..RETIREMENT_CHECKSUM_OFFSET_V2]);
    hasher.update([0u8; 32]);
    Ok(hasher.finalize().into())
}

fn replace_with_faults_v2<F: WalletStoreMigrationFaultInjectorV2>(
    file: &AtomicStateFileV1,
    bytes: &[u8],
    write: WalletStoreMigrationWriteV2,
    faults: &mut F,
) -> Result<(), WalletStoreMigrationErrorV2> {
    let before = WalletStoreMigrationLogicalFaultPointV2 {
        write,
        boundary: WalletStoreMigrationLogicalBoundaryV2::BeforeWrite,
    };
    if faults.interrupt_logical_v2(before) {
        return Err(WalletStoreMigrationErrorV2::InjectedLogicalFault(before));
    }
    let mut injected = None;
    let result = file.replace_with_fault_v1(bytes, |boundary| {
        let point = WalletStoreMigrationAtomicFaultPointV2 {
            write,
            boundary: public_atomic_boundary_v2(boundary),
        };
        if faults.interrupt_atomic_v2(point) {
            injected = Some(point);
            Err(DurableStateErrorV1::Io(io::ErrorKind::Interrupted))
        } else {
            Ok(())
        }
    });
    if let Err(error) = result {
        return Err(injected.map_or(
            WalletStoreMigrationErrorV2::Durable(error),
            WalletStoreMigrationErrorV2::InjectedAtomicFault,
        ));
    }
    let after = WalletStoreMigrationLogicalFaultPointV2 {
        write,
        boundary: WalletStoreMigrationLogicalBoundaryV2::AfterWrite,
    };
    if faults.interrupt_logical_v2(after) {
        return Err(WalletStoreMigrationErrorV2::InjectedLogicalFault(after));
    }
    Ok(())
}

fn public_atomic_boundary_v2(
    boundary: AtomicReplaceBoundaryV1,
) -> WalletStoreMigrationAtomicBoundaryV2 {
    match boundary {
        AtomicReplaceBoundaryV1::TemporaryWrite => {
            WalletStoreMigrationAtomicBoundaryV2::TemporaryWrite
        }
        AtomicReplaceBoundaryV1::TemporaryFileSync => {
            WalletStoreMigrationAtomicBoundaryV2::TemporaryFileSync
        }
        AtomicReplaceBoundaryV1::TargetRename => WalletStoreMigrationAtomicBoundaryV2::TargetRename,
        AtomicReplaceBoundaryV1::ParentDirectorySync => {
            WalletStoreMigrationAtomicBoundaryV2::ParentDirectorySync
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        fs,
        sync::atomic::{AtomicU64, Ordering},
    };

    static NEXT_DIRECTORY_V2: AtomicU64 = AtomicU64::new(1);

    struct TestDirectoryV2(PathBuf);

    impl TestDirectoryV2 {
        fn new_v2() -> Self {
            let id = NEXT_DIRECTORY_V2.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "aspis-wallet-store-migration-{}-{}",
                std::process::id(),
                id
            ));
            fs::create_dir(&path).unwrap();
            Self(path)
        }

        fn authority_v2(&self) -> PathBuf {
            self.0.join(WALLET_STORE_MIGRATION_AUTHORITY_FILE_V2)
        }

        fn target_v2(&self) -> PathBuf {
            self.0.join("wallet.asl2")
        }

        fn source_v2(&self, role: WalletStoreSourceRoleV2) -> PathBuf {
            self.0.join(format!("source-{}", role as u8))
        }
    }

    impl Drop for TestDirectoryV2 {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn private_write_v2(path: &Path, bytes: &[u8]) {
        fs::write(path, bytes).unwrap();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;
            fs::set_permissions(path, fs::Permissions::from_mode(0o600)).unwrap();
        }
    }

    fn source_bytes_v2(role: WalletStoreSourceRoleV2) -> Vec<u8> {
        let mut bytes = Vec::from(role.magic_v2());
        bytes.push(
            if role == WalletStoreSourceRoleV2::RelayerExecutionJournal {
                2
            } else {
                1
            },
        );
        bytes.extend_from_slice(&[role as u8; 43]);
        bytes
    }

    fn plan_v2(directory: &TestDirectoryV2, target_seed: u8) -> WalletStoreMigrationPlanV2 {
        let sources = WalletStoreSourceRoleV2::ALL
            .into_iter()
            .rev()
            .map(|role| {
                let path = directory.source_v2(role);
                if !path.exists() {
                    private_write_v2(&path, &source_bytes_v2(role));
                }
                WalletStoreSourceDescriptorV2::from_exact_path_and_bytes_v2(
                    role,
                    path,
                    &source_bytes_v2(role),
                )
                .unwrap()
            })
            .collect();
        let mut target = Vec::from(*b"ASL2");
        target.extend_from_slice(&[target_seed; 124]);
        WalletStoreMigrationPlanV2::new_v2(sources, directory.target_v2(), target).unwrap()
    }

    fn write_sources_v2(directory: &TestDirectoryV2) -> Vec<(WalletStoreSourceRoleV2, PathBuf)> {
        WalletStoreSourceRoleV2::ALL
            .into_iter()
            .map(|role| {
                let path = directory.source_v2(role);
                private_write_v2(&path, &source_bytes_v2(role));
                (role, path)
            })
            .collect()
    }

    #[derive(Default)]
    struct OneFaultV2 {
        logical: Option<WalletStoreMigrationLogicalFaultPointV2>,
        atomic: Option<WalletStoreMigrationAtomicFaultPointV2>,
        fired: bool,
    }

    impl WalletStoreMigrationFaultInjectorV2 for OneFaultV2 {
        fn interrupt_logical_v2(&mut self, point: WalletStoreMigrationLogicalFaultPointV2) -> bool {
            if !self.fired && self.logical == Some(point) {
                self.fired = true;
                true
            } else {
                false
            }
        }

        fn interrupt_atomic_v2(&mut self, point: WalletStoreMigrationAtomicFaultPointV2) -> bool {
            if !self.fired && self.atomic == Some(point) {
                self.fired = true;
                true
            } else {
                false
            }
        }
    }

    #[test]
    fn canonical_journal_and_tombstone_roundtrip_fail_closed() {
        let directory = TestDirectoryV2::new_v2();
        let plan = plan_v2(&directory, 0x91);
        let state = WalletStoreMigrationJournalStateV2::prepared_v2(plan.clone());
        let encoded = encode_wallet_store_migration_journal_v2(&state).unwrap();
        assert_eq!(
            decode_wallet_store_migration_journal_v2(&encoded).unwrap(),
            state
        );

        let mut trailing = encoded.clone();
        trailing.push(0);
        assert_eq!(
            decode_wallet_store_migration_journal_v2(&trailing).unwrap_err(),
            WalletStoreMigrationErrorV2::WrongLength
        );
        let mut corrupt = encoded;
        *corrupt.last_mut().unwrap() ^= 1;
        assert_eq!(
            decode_wallet_store_migration_journal_v2(&corrupt).unwrap_err(),
            WalletStoreMigrationErrorV2::ChecksumMismatch
        );

        let tombstone = WalletStoreRetirementTombstoneV2::from_plan_v2(
            WalletStoreSourceRoleV2::RelayerExecutionJournal,
            &plan,
        )
        .unwrap();
        let encoded = encode_wallet_store_retirement_tombstone_v2(&tombstone).unwrap();
        assert_eq!(
            decode_wallet_store_retirement_tombstone_v2(&encoded).unwrap(),
            tombstone
        );
        let mut corrupt = encoded;
        corrupt[100] ^= 1;
        assert_eq!(
            decode_wallet_store_retirement_tombstone_v2(&corrupt).unwrap_err(),
            WalletStoreMigrationErrorV2::ChecksumMismatch
        );
    }

    #[test]
    fn exact_prepare_replay_succeeds_and_conflicting_identity_fails() {
        let directory = TestDirectoryV2::new_v2();
        let plan = plan_v2(&directory, 0x92);
        let (journal, update) = DurableWalletStoreMigrationJournalV2::open_or_prepare_v2(
            directory.authority_v2(),
            plan.clone(),
        )
        .unwrap();
        assert_eq!(update, WalletStoreMigrationUpdateV2::Written);
        assert_eq!(
            journal.receipt_v2().unwrap().phase(),
            WalletStoreMigrationPhaseV2::Prepared
        );
        drop(journal);

        let (journal, update) = DurableWalletStoreMigrationJournalV2::open_or_prepare_v2(
            directory.authority_v2(),
            plan,
        )
        .unwrap();
        assert_eq!(update, WalletStoreMigrationUpdateV2::AlreadyPresent);
        drop(journal);
        assert_eq!(
            DurableWalletStoreMigrationJournalV2::open_or_prepare_v2(
                directory.authority_v2(),
                plan_v2(&directory, 0x93),
            )
            .err(),
            Some(WalletStoreMigrationErrorV2::MigrationConflict)
        );
    }

    #[test]
    fn phase_transitions_target_and_retirement_are_monotone_and_idempotent() {
        assert_eq!(
            validate_wallet_store_migration_phase_transition_v2(
                WalletStoreMigrationPhaseV2::Prepared,
                WalletStoreMigrationPhaseV2::Prepared,
            )
            .unwrap(),
            WalletStoreMigrationUpdateV2::AlreadyPresent
        );
        assert_eq!(
            validate_wallet_store_migration_phase_transition_v2(
                WalletStoreMigrationPhaseV2::OwnershipCommitted,
                WalletStoreMigrationPhaseV2::TargetInstalled,
            )
            .unwrap_err(),
            WalletStoreMigrationErrorV2::PhaseRegression
        );
        assert_eq!(
            validate_wallet_store_migration_phase_transition_v2(
                WalletStoreMigrationPhaseV2::Prepared,
                WalletStoreMigrationPhaseV2::OwnershipCommitted,
            )
            .unwrap_err(),
            WalletStoreMigrationErrorV2::InvalidPhase
        );

        let directory = TestDirectoryV2::new_v2();
        let sources = write_sources_v2(&directory);
        let (mut journal, _) = DurableWalletStoreMigrationJournalV2::open_or_prepare_v2(
            directory.authority_v2(),
            plan_v2(&directory, 0x94),
        )
        .unwrap();
        assert_eq!(
            journal
                .commit_ownership_v2(directory.target_v2())
                .unwrap_err(),
            WalletStoreMigrationErrorV2::InvalidPhase
        );
        assert_eq!(
            journal.install_target_v2(directory.target_v2()).unwrap(),
            WalletStoreMigrationUpdateV2::Written
        );
        assert_eq!(
            journal.install_target_v2(directory.target_v2()).unwrap(),
            WalletStoreMigrationUpdateV2::AlreadyPresent
        );
        assert_eq!(
            journal.commit_ownership_v2(directory.target_v2()).unwrap(),
            WalletStoreMigrationUpdateV2::Written
        );
        assert_eq!(
            journal.commit_ownership_v2(directory.target_v2()).unwrap(),
            WalletStoreMigrationUpdateV2::AlreadyPresent
        );
        for (role, path) in &sources {
            assert_eq!(
                journal.retire_legacy_store_v2(*role, path).unwrap(),
                WalletStoreMigrationUpdateV2::Written
            );
            assert_eq!(
                journal.retire_legacy_store_v2(*role, path).unwrap(),
                WalletStoreMigrationUpdateV2::AlreadyPresent
            );
        }
        assert_eq!(
            journal.complete_legacy_retirement_v2(&sources).unwrap(),
            WalletStoreMigrationUpdateV2::Written
        );
        assert_eq!(
            journal.complete_legacy_retirement_v2(&sources).unwrap(),
            WalletStoreMigrationUpdateV2::AlreadyPresent
        );
        assert_eq!(
            journal.receipt_v2().unwrap().phase(),
            WalletStoreMigrationPhaseV2::LegacyRetired
        );
    }

    #[test]
    fn conflicting_source_target_and_tombstone_change_nothing() {
        let directory = TestDirectoryV2::new_v2();
        let sources = write_sources_v2(&directory);
        let (mut journal, _) = DurableWalletStoreMigrationJournalV2::open_or_prepare_v2(
            directory.authority_v2(),
            plan_v2(&directory, 0x95),
        )
        .unwrap();
        private_write_v2(&directory.target_v2(), b"different target");
        assert_eq!(
            journal
                .install_target_v2(directory.target_v2())
                .unwrap_err(),
            WalletStoreMigrationErrorV2::TargetConflict
        );
        assert_eq!(
            fs::read(directory.target_v2()).unwrap(),
            b"different target"
        );
        drop(journal);
        fs::remove_file(directory.target_v2()).unwrap();

        let mut journal =
            DurableWalletStoreMigrationJournalV2::open_existing_v2(directory.authority_v2())
                .unwrap();
        journal.install_target_v2(directory.target_v2()).unwrap();
        journal.commit_ownership_v2(directory.target_v2()).unwrap();
        let (role, path) = &sources[0];
        private_write_v2(
            path,
            &source_bytes_v2(WalletStoreSourceRoleV2::WitnessState),
        );
        assert_eq!(
            journal.retire_legacy_store_v2(*role, path).unwrap_err(),
            WalletStoreMigrationErrorV2::SourceConflict
        );
        assert_eq!(
            fs::read(path).unwrap(),
            source_bytes_v2(WalletStoreSourceRoleV2::WitnessState)
        );
    }

    #[test]
    fn canonical_path_bindings_reject_wrong_target_source_and_authority() {
        let directory = TestDirectoryV2::new_v2();
        let sources = write_sources_v2(&directory);
        let plan = plan_v2(&directory, 0x9a);

        let wrong_authority_directory = TestDirectoryV2::new_v2();
        assert_eq!(
            DurableWalletStoreMigrationJournalV2::open_or_prepare_v2(
                wrong_authority_directory.authority_v2(),
                plan.clone(),
            )
            .err(),
            Some(WalletStoreMigrationErrorV2::InvalidAuthorityPath)
        );

        let (mut journal, _) = DurableWalletStoreMigrationJournalV2::open_or_prepare_v2(
            directory.authority_v2(),
            plan,
        )
        .unwrap();
        let wrong_target = directory.0.join("other-wallet.asl2");
        assert_eq!(
            journal.install_target_v2(&wrong_target).unwrap_err(),
            WalletStoreMigrationErrorV2::TargetConflict
        );
        assert!(!wrong_target.exists());

        journal.install_target_v2(directory.target_v2()).unwrap();
        journal.commit_ownership_v2(directory.target_v2()).unwrap();

        let role = WalletStoreSourceRoleV2::WalletState;
        let wrong_source = directory.0.join("wallet-state-copy");
        private_write_v2(&wrong_source, &source_bytes_v2(role));
        assert_eq!(
            journal
                .retire_legacy_store_v2(role, &wrong_source)
                .unwrap_err(),
            WalletStoreMigrationErrorV2::SourceConflict
        );
        assert_eq!(fs::read(&wrong_source).unwrap(), source_bytes_v2(role));

        let mut wrong_sources = sources.clone();
        wrong_sources[0].1 = wrong_source;
        assert_eq!(
            journal
                .complete_legacy_retirement_v2(&wrong_sources)
                .unwrap_err(),
            WalletStoreMigrationErrorV2::SourceConflict
        );
    }

    #[test]
    fn ownership_revalidates_locked_exact_target_and_recovery_is_idempotent() {
        let directory = TestDirectoryV2::new_v2();
        write_sources_v2(&directory);
        let plan = plan_v2(&directory, 0x9b);
        let target_bytes = plan.target_bytes().to_vec();
        let (mut journal, _) = DurableWalletStoreMigrationJournalV2::open_or_prepare_v2(
            directory.authority_v2(),
            plan,
        )
        .unwrap();
        journal.install_target_v2(directory.target_v2()).unwrap();

        private_write_v2(&directory.target_v2(), b"replaced target");
        assert_eq!(
            journal
                .commit_ownership_v2(directory.target_v2())
                .unwrap_err(),
            WalletStoreMigrationErrorV2::TargetConflict
        );
        assert_eq!(
            journal.receipt_v2().unwrap().phase(),
            WalletStoreMigrationPhaseV2::TargetInstalled
        );

        fs::remove_file(directory.target_v2()).unwrap();
        assert_eq!(
            journal
                .commit_ownership_v2(directory.target_v2())
                .unwrap_err(),
            WalletStoreMigrationErrorV2::TargetConflict
        );
        assert_eq!(
            journal
                .install_target_v2(directory.target_v2())
                .unwrap_err(),
            WalletStoreMigrationErrorV2::TargetConflict
        );

        private_write_v2(&directory.target_v2(), &target_bytes);
        assert_eq!(
            journal.commit_ownership_v2(directory.target_v2()).unwrap(),
            WalletStoreMigrationUpdateV2::Written
        );
        assert_eq!(
            journal.commit_ownership_v2(directory.target_v2()).unwrap(),
            WalletStoreMigrationUpdateV2::AlreadyPresent
        );
        assert_eq!(
            journal
                .commit_ownership_v2(directory.0.join("other-wallet.asl2"))
                .unwrap_err(),
            WalletStoreMigrationErrorV2::TargetConflict
        );
    }

    #[test]
    fn legacy_writer_fence_is_absent_prepared_and_retired_aware() {
        let directory = TestDirectoryV2::new_v2();
        let legacy = directory.source_v2(WalletStoreSourceRoleV2::WalletState);
        assert_eq!(
            wallet_store_migration_authority_path_v2(&legacy).unwrap(),
            directory.authority_v2()
        );
        check_legacy_wallet_store_writer_allowed_v2(&legacy).unwrap();
        let (mut journal, _) = DurableWalletStoreMigrationJournalV2::open_or_prepare_v2(
            directory.authority_v2(),
            plan_v2(&directory, 0x96),
        )
        .unwrap();
        // The journal itself holds the common authority lock.
        assert_eq!(
            check_legacy_wallet_store_writer_allowed_v2(&legacy).unwrap_err(),
            WalletStoreMigrationErrorV2::AuthorityBusy
        );
        journal.install_target_v2(directory.target_v2()).unwrap();
        drop(journal);
        assert_eq!(
            check_legacy_wallet_store_writer_allowed_v2(&legacy).unwrap_err(),
            WalletStoreMigrationErrorV2::MigrationInProgress
        );
        let mut journal =
            DurableWalletStoreMigrationJournalV2::open_existing_v2(directory.authority_v2())
                .unwrap();
        journal.commit_ownership_v2(directory.target_v2()).unwrap();
        drop(journal);
        assert_eq!(
            check_legacy_wallet_store_writer_allowed_v2(&legacy).unwrap_err(),
            WalletStoreMigrationErrorV2::LegacyRetired
        );
    }

    fn prepare_phase_v2(
        directory: &TestDirectoryV2,
        desired: WalletStoreMigrationWriteV2,
    ) -> (
        DurableWalletStoreMigrationJournalV2,
        Vec<(WalletStoreSourceRoleV2, PathBuf)>,
    ) {
        let sources = write_sources_v2(directory);
        let (mut journal, _) = DurableWalletStoreMigrationJournalV2::open_or_prepare_v2(
            directory.authority_v2(),
            plan_v2(directory, 0xa1),
        )
        .unwrap();
        if desired != WalletStoreMigrationWriteV2::TargetImage
            && desired != WalletStoreMigrationWriteV2::JournalTargetInstalled
        {
            journal.install_target_v2(directory.target_v2()).unwrap();
        }
        if matches!(
            desired,
            WalletStoreMigrationWriteV2::LegacyTombstone(_)
                | WalletStoreMigrationWriteV2::JournalLegacyRetired
        ) {
            journal.commit_ownership_v2(directory.target_v2()).unwrap();
        }
        if desired == WalletStoreMigrationWriteV2::JournalLegacyRetired {
            for (role, path) in &sources {
                journal.retire_legacy_store_v2(*role, path).unwrap();
            }
        }
        (journal, sources)
    }

    fn exercise_atomic_fault_v2(
        write: WalletStoreMigrationWriteV2,
        boundary: WalletStoreMigrationAtomicBoundaryV2,
    ) {
        let directory = TestDirectoryV2::new_v2();
        if write == WalletStoreMigrationWriteV2::JournalPrepared {
            let mut fault = OneFaultV2 {
                atomic: Some(WalletStoreMigrationAtomicFaultPointV2 { write, boundary }),
                ..OneFaultV2::default()
            };
            assert!(
                DurableWalletStoreMigrationJournalV2::open_or_prepare_with_faults_v2(
                    directory.authority_v2(),
                    plan_v2(&directory, 0xa1),
                    &mut fault,
                )
                .is_err()
            );
            assert!(fault.fired);
            DurableWalletStoreMigrationJournalV2::open_or_prepare_v2(
                directory.authority_v2(),
                plan_v2(&directory, 0xa1),
            )
            .unwrap();
            return;
        }

        let (mut journal, sources) = prepare_phase_v2(&directory, write);
        let mut fault = OneFaultV2 {
            atomic: Some(WalletStoreMigrationAtomicFaultPointV2 { write, boundary }),
            ..OneFaultV2::default()
        };
        let result = match write {
            WalletStoreMigrationWriteV2::TargetImage
            | WalletStoreMigrationWriteV2::JournalTargetInstalled => {
                journal.install_target_with_faults_v2(directory.target_v2(), &mut fault)
            }
            WalletStoreMigrationWriteV2::JournalOwnershipCommitted => {
                journal.commit_ownership_with_faults_v2(directory.target_v2(), &mut fault)
            }
            WalletStoreMigrationWriteV2::LegacyTombstone(role) => journal
                .retire_legacy_store_with_faults_v2(role, directory.source_v2(role), &mut fault),
            WalletStoreMigrationWriteV2::JournalLegacyRetired => {
                journal.complete_legacy_retirement_for_test_with_faults_v2(&sources, &mut fault)
            }
            WalletStoreMigrationWriteV2::JournalPrepared => unreachable!(),
        };
        assert!(result.is_err());
        assert!(fault.fired);
        assert!(journal.is_poisoned_v2());
        drop(journal);

        let mut recovered =
            DurableWalletStoreMigrationJournalV2::open_existing_v2(directory.authority_v2())
                .unwrap();
        match write {
            WalletStoreMigrationWriteV2::TargetImage
            | WalletStoreMigrationWriteV2::JournalTargetInstalled => {
                recovered.install_target_v2(directory.target_v2()).unwrap();
            }
            WalletStoreMigrationWriteV2::JournalOwnershipCommitted => {
                recovered
                    .commit_ownership_v2(directory.target_v2())
                    .unwrap();
            }
            WalletStoreMigrationWriteV2::LegacyTombstone(role) => {
                recovered
                    .retire_legacy_store_v2(role, directory.source_v2(role))
                    .unwrap();
            }
            WalletStoreMigrationWriteV2::JournalLegacyRetired => {
                recovered.complete_legacy_retirement_v2(&sources).unwrap();
            }
            WalletStoreMigrationWriteV2::JournalPrepared => unreachable!(),
        }
    }

    #[test]
    fn every_real_atomic_write_boundary_is_recoverable_and_idempotent() {
        let writes = [
            WalletStoreMigrationWriteV2::JournalPrepared,
            WalletStoreMigrationWriteV2::TargetImage,
            WalletStoreMigrationWriteV2::JournalTargetInstalled,
            WalletStoreMigrationWriteV2::JournalOwnershipCommitted,
            WalletStoreMigrationWriteV2::LegacyTombstone(WalletStoreSourceRoleV2::WalletState),
            WalletStoreMigrationWriteV2::LegacyTombstone(WalletStoreSourceRoleV2::WitnessState),
            WalletStoreMigrationWriteV2::LegacyTombstone(WalletStoreSourceRoleV2::LaneForestState),
            WalletStoreMigrationWriteV2::LegacyTombstone(
                WalletStoreSourceRoleV2::RelayerAdmissionState,
            ),
            WalletStoreMigrationWriteV2::LegacyTombstone(
                WalletStoreSourceRoleV2::RelayerExecutionJournal,
            ),
            WalletStoreMigrationWriteV2::JournalLegacyRetired,
        ];
        let boundaries = [
            WalletStoreMigrationAtomicBoundaryV2::TemporaryWrite,
            WalletStoreMigrationAtomicBoundaryV2::TemporaryFileSync,
            WalletStoreMigrationAtomicBoundaryV2::TargetRename,
            WalletStoreMigrationAtomicBoundaryV2::ParentDirectorySync,
        ];
        for write in writes {
            for boundary in boundaries {
                exercise_atomic_fault_v2(write, boundary);
            }
        }
    }

    #[test]
    fn logical_before_and_after_faults_reopen_to_canonical_state() {
        for boundary in [
            WalletStoreMigrationLogicalBoundaryV2::BeforeWrite,
            WalletStoreMigrationLogicalBoundaryV2::AfterWrite,
        ] {
            let directory = TestDirectoryV2::new_v2();
            let point = WalletStoreMigrationLogicalFaultPointV2 {
                write: WalletStoreMigrationWriteV2::JournalPrepared,
                boundary,
            };
            let mut fault = OneFaultV2 {
                logical: Some(point),
                ..OneFaultV2::default()
            };
            assert_eq!(
                DurableWalletStoreMigrationJournalV2::open_or_prepare_with_faults_v2(
                    directory.authority_v2(),
                    plan_v2(&directory, 0xa2),
                    &mut fault,
                )
                .err(),
                Some(WalletStoreMigrationErrorV2::InjectedLogicalFault(point))
            );
            DurableWalletStoreMigrationJournalV2::open_or_prepare_v2(
                directory.authority_v2(),
                plan_v2(&directory, 0xa2),
            )
            .unwrap();
        }
    }
}
