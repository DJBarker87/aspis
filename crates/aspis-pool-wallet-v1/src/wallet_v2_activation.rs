//! Explicit, default-off production activation predicate for the V2 wallet.
//!
//! This module creates no runtime dispatch and performs no migration. It only
//! compares one operator-pinned production configuration with independently
//! collected runtime prerequisites. Every field must be present, singular,
//! nonzero where applicable, and exactly equal before an opaque permit exists.

use std::collections::HashSet;

use sha2::{Digest as _, Sha256};

use crate::lane_forest_wallet_txn_v2::{
    LaneForestWalletTxnCoordinatorV2, LANE_FOREST_WALLET_TXN_MAGIC_V2,
    LANE_FOREST_WALLET_TXN_VERSION_V3,
};
use crate::wallet_store_migration_v2::{
    WalletStoreMigrationPhaseV2, WalletStoreMigrationReceiptV2,
};

pub const WALLET_V2_ACTIVATION_SCHEMA_VERSION: u8 = 1;

const ACTIVATION_PERMIT_DOMAIN_V2: &[u8] =
    b"aspis:pool-v1:wallet-v2-production-activation-permit:sha256:v1";

#[allow(clippy::large_enum_variant)]
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub enum WalletV2ActivationMode {
    #[default]
    Disabled,
    Production(WalletV2ProductionConfig),
    /// Explicitly non-production path used to execute the complete runtime
    /// state machine against the volatile reference monotonic service.
    #[cfg(feature = "wallet-v2-reference-tests")]
    ReferenceOnly(WalletV2ProductionConfig),
}

/// Exact operator-pinned state allowed to enter production V2 dispatch.
#[derive(Clone, PartialEq, Eq)]
pub struct WalletV2ProductionConfig {
    asl2_magic: [u8; 4],
    asl2_schema_version: u8,
    activation_schema_version: u8,
    wallet_id: [u8; 32],
    note_cipher_id: [u8; 32],
    migration_id: [u8; 32],
    ownership_id: [u8; 32],
    migration_target_digest: [u8; 32],
    migration_target_path_digest: [u8; 32],
    monotonic_protection_id: [u8; 32],
    monotonic_store_qualification: [u8; 32],
    qualified_startup_digest: [u8; 32],
    qualified_provider_digest: [u8; 32],
    qualified_finality_digest: [u8; 32],
}

impl core::fmt::Debug for WalletV2ProductionConfig {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("WalletV2ProductionConfig")
            .field("asl2_magic", &self.asl2_magic)
            .field("asl2_schema_version", &self.asl2_schema_version)
            .field("activation_schema_version", &self.activation_schema_version)
            .field("activation_bindings", &"[REDACTED]")
            .finish()
    }
}

impl WalletV2ProductionConfig {
    #[allow(clippy::too_many_arguments)]
    pub fn new_v2(
        wallet_id: [u8; 32],
        note_cipher_id: [u8; 32],
        migration_id: [u8; 32],
        ownership_id: [u8; 32],
        migration_target_digest: [u8; 32],
        migration_target_path_digest: [u8; 32],
        monotonic_protection_id: [u8; 32],
        monotonic_store_qualification: [u8; 32],
        qualified_startup_digest: [u8; 32],
        qualified_provider_digest: [u8; 32],
        qualified_finality_digest: [u8; 32],
    ) -> Result<Self, WalletV2ActivationError> {
        let config = Self {
            asl2_magic: LANE_FOREST_WALLET_TXN_MAGIC_V2,
            asl2_schema_version: LANE_FOREST_WALLET_TXN_VERSION_V3,
            activation_schema_version: WALLET_V2_ACTIVATION_SCHEMA_VERSION,
            wallet_id,
            note_cipher_id,
            migration_id,
            ownership_id,
            migration_target_digest,
            migration_target_path_digest,
            monotonic_protection_id,
            monotonic_store_qualification,
            qualified_startup_digest,
            qualified_provider_digest,
            qualified_finality_digest,
        };
        config.validate_v2()?;
        Ok(config)
    }

    fn validate_v2(&self) -> Result<(), WalletV2ActivationError> {
        if self.asl2_magic != LANE_FOREST_WALLET_TXN_MAGIC_V2
            || self.asl2_schema_version != LANE_FOREST_WALLET_TXN_VERSION_V3
            || self.activation_schema_version != WALLET_V2_ACTIVATION_SCHEMA_VERSION
            || [
                self.wallet_id,
                self.note_cipher_id,
                self.migration_id,
                self.ownership_id,
                self.migration_target_digest,
                self.migration_target_path_digest,
                self.monotonic_protection_id,
                self.monotonic_store_qualification,
                self.qualified_startup_digest,
                self.qualified_provider_digest,
                self.qualified_finality_digest,
            ]
            .contains(&[0u8; 32])
        {
            return Err(WalletV2ActivationError::InvalidConfiguration);
        }
        Ok(())
    }
}

/// The five legacy mutation authorities which must be retired together.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum LegacyWalletStoreRoleV2 {
    WalletAndScanner = 1,
    WitnessJournal = 2,
    LaneForest = 3,
    RelayerAdmission = 4,
    RelayerExecution = 5,
}

const ALL_LEGACY_STORE_ROLES_V2: [LegacyWalletStoreRoleV2; 5] = [
    LegacyWalletStoreRoleV2::WalletAndScanner,
    LegacyWalletStoreRoleV2::WitnessJournal,
    LegacyWalletStoreRoleV2::LaneForest,
    LegacyWalletStoreRoleV2::RelayerAdmission,
    LegacyWalletStoreRoleV2::RelayerExecution,
];

/// Independently observed activation state. Digest lists deliberately remain
/// lists: zero entries are missing evidence and multiple entries are ambiguous
/// evidence, both of which fail closed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WalletV2ActivationPrerequisites {
    asl2_magic: [u8; 4],
    asl2_schema_version: u8,
    activation_schema_version: u8,
    wallet_id: [u8; 32],
    note_cipher_id: [u8; 32],
    migration_id: [u8; 32],
    migration_committed: bool,
    ownership_id: [u8; 32],
    asl2_ownership_committed: bool,
    retired_legacy_roles: Vec<LegacyWalletStoreRoleV2>,
    has_pending_transaction: bool,
    migration_target_digests: Vec<[u8; 32]>,
    migration_target_path_digest: [u8; 32],
    monotonic_protection_id: [u8; 32],
    monotonic_store_qualifications: Vec<[u8; 32]>,
    qualified_startup_digests: Vec<[u8; 32]>,
    qualified_provider_digests: Vec<[u8; 32]>,
    qualified_finality_digests: Vec<[u8; 32]>,
}

impl WalletV2ActivationPrerequisites {
    /// Derive all local prerequisites from the exact committed ASL2 target,
    /// the completed ASMG receipt, and the injected monotonic backend. Only
    /// provider/startup/finality qualification digests remain explicit
    /// external observations.
    pub fn from_authoritative_state_v2(
        coordinator: &LaneForestWalletTxnCoordinatorV2,
        ownership: WalletStoreMigrationReceiptV2,
        qualified_startup_digests: Vec<[u8; 32]>,
        qualified_provider_digests: Vec<[u8; 32]>,
        qualified_finality_digests: Vec<[u8; 32]>,
    ) -> Result<Self, WalletV2ActivationError> {
        if ownership.phase() != WalletStoreMigrationPhaseV2::LegacyRetired {
            return Err(
                if ownership.phase() < WalletStoreMigrationPhaseV2::OwnershipCommitted {
                    WalletV2ActivationError::OwnershipNotCommitted
                } else {
                    WalletV2ActivationError::LegacyWriterNotRetired
                },
            );
        }
        if coordinator
            .pending_phase_v2()
            .map_err(|_| WalletV2ActivationError::RuntimeStateRejected)?
            .is_some()
        {
            return Err(WalletV2ActivationError::PendingTransaction);
        }
        let activation = coordinator
            .activation_v2()
            .map_err(|_| WalletV2ActivationError::RuntimeStateRejected)?;
        let migration = activation
            .migration_genesis()
            .ok_or(WalletV2ActivationError::MigrationNotCommitted)?;
        let (target_path, _target_bytes) = coordinator
            .authoritative_target_image_v2()
            .map_err(|_| WalletV2ActivationError::RuntimeStateRejected)?;
        if !ownership.authenticates_target_path_v2(target_path) {
            return Err(WalletV2ActivationError::OwnershipTargetMismatch);
        }
        coordinator
            .externally_anchored_monotonic_commitment_v2()
            .map_err(|_| WalletV2ActivationError::MonotonicUnavailable)?;
        let protection_id = coordinator
            .monotonic_protection_id_v2()
            .copied()
            .ok_or(WalletV2ActivationError::MonotonicUnavailable)?;
        let monotonic_qualification = coordinator
            .production_monotonic_qualification_v2()
            .map_err(|_| WalletV2ActivationError::MonotonicUnqualified)?;
        Ok(Self {
            asl2_magic: LANE_FOREST_WALLET_TXN_MAGIC_V2,
            asl2_schema_version: LANE_FOREST_WALLET_TXN_VERSION_V3,
            activation_schema_version: WALLET_V2_ACTIVATION_SCHEMA_VERSION,
            wallet_id: *activation.wallet_identity_sha256(),
            note_cipher_id: *activation.note_cipher_id(),
            migration_id: *migration.migration_id(),
            migration_committed: true,
            ownership_id: *ownership.migration_id(),
            asl2_ownership_committed: true,
            retired_legacy_roles: ALL_LEGACY_STORE_ROLES_V2.to_vec(),
            has_pending_transaction: false,
            migration_target_digests: vec![*ownership.target_digest()],
            migration_target_path_digest: *ownership.target_path_digest(),
            monotonic_protection_id: protection_id,
            monotonic_store_qualifications: vec![monotonic_qualification.qualification_digest_v2()],
            qualified_startup_digests,
            qualified_provider_digests,
            qualified_finality_digests,
        })
    }

    /// Build otherwise identical runtime evidence for the explicitly
    /// non-production reference mode. This never calls or fabricates
    /// `production_monotonic_qualification_v2`.
    #[cfg(feature = "wallet-v2-reference-tests")]
    pub fn from_authoritative_state_reference_only_v2(
        coordinator: &LaneForestWalletTxnCoordinatorV2,
        ownership: WalletStoreMigrationReceiptV2,
        reference_service_digest: [u8; 32],
        qualified_startup_digests: Vec<[u8; 32]>,
        qualified_provider_digests: Vec<[u8; 32]>,
        qualified_finality_digests: Vec<[u8; 32]>,
    ) -> Result<Self, WalletV2ActivationError> {
        if reference_service_digest == [0u8; 32] {
            return Err(WalletV2ActivationError::MonotonicUnqualified);
        }
        let mut prerequisites = Self::from_authoritative_state_without_qualification_v2(
            coordinator,
            ownership,
            qualified_startup_digests,
            qualified_provider_digests,
            qualified_finality_digests,
        )?;
        prerequisites.monotonic_store_qualifications = vec![reference_service_digest];
        Ok(prerequisites)
    }

    #[cfg(feature = "wallet-v2-reference-tests")]
    fn from_authoritative_state_without_qualification_v2(
        coordinator: &LaneForestWalletTxnCoordinatorV2,
        ownership: WalletStoreMigrationReceiptV2,
        qualified_startup_digests: Vec<[u8; 32]>,
        qualified_provider_digests: Vec<[u8; 32]>,
        qualified_finality_digests: Vec<[u8; 32]>,
    ) -> Result<Self, WalletV2ActivationError> {
        if ownership.phase() != WalletStoreMigrationPhaseV2::LegacyRetired {
            return Err(WalletV2ActivationError::LegacyWriterNotRetired);
        }
        if coordinator
            .pending_phase_v2()
            .map_err(|_| WalletV2ActivationError::RuntimeStateRejected)?
            .is_some()
        {
            return Err(WalletV2ActivationError::PendingTransaction);
        }
        let activation = coordinator
            .activation_v2()
            .map_err(|_| WalletV2ActivationError::RuntimeStateRejected)?;
        let migration = activation
            .migration_genesis()
            .ok_or(WalletV2ActivationError::MigrationNotCommitted)?;
        let (target_path, _) = coordinator
            .authoritative_target_image_v2()
            .map_err(|_| WalletV2ActivationError::RuntimeStateRejected)?;
        if !ownership.authenticates_target_path_v2(target_path) {
            return Err(WalletV2ActivationError::OwnershipTargetMismatch);
        }
        coordinator
            .externally_anchored_monotonic_commitment_v2()
            .map_err(|_| WalletV2ActivationError::MonotonicUnavailable)?;
        let protection_id = coordinator
            .monotonic_protection_id_v2()
            .copied()
            .ok_or(WalletV2ActivationError::MonotonicUnavailable)?;
        Ok(Self {
            asl2_magic: LANE_FOREST_WALLET_TXN_MAGIC_V2,
            asl2_schema_version: LANE_FOREST_WALLET_TXN_VERSION_V3,
            activation_schema_version: WALLET_V2_ACTIVATION_SCHEMA_VERSION,
            wallet_id: *activation.wallet_identity_sha256(),
            note_cipher_id: *activation.note_cipher_id(),
            migration_id: *migration.migration_id(),
            migration_committed: true,
            ownership_id: *ownership.migration_id(),
            asl2_ownership_committed: true,
            retired_legacy_roles: ALL_LEGACY_STORE_ROLES_V2.to_vec(),
            has_pending_transaction: false,
            migration_target_digests: vec![*ownership.target_digest()],
            migration_target_path_digest: *ownership.target_path_digest(),
            monotonic_protection_id: protection_id,
            monotonic_store_qualifications: Vec::new(),
            qualified_startup_digests,
            qualified_provider_digests,
            qualified_finality_digests,
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum WalletV2ActivationClass {
    Production,
    #[cfg(feature = "wallet-v2-reference-tests")]
    ReferenceOnly,
}

/// Opaque proof that the complete predicate succeeded. Private fields prevent
/// construction by production dispatch code without calling the predicate.
#[derive(Clone, PartialEq, Eq)]
pub struct WalletV2ActivationPermit {
    activation_class: WalletV2ActivationClass,
    activation_digest: [u8; 32],
    wallet_id: [u8; 32],
    migration_id: [u8; 32],
    ownership_id: [u8; 32],
    migration_target_digest: [u8; 32],
    migration_target_path_digest: [u8; 32],
    note_cipher_id: [u8; 32],
    monotonic_protection_id: [u8; 32],
    monotonic_store_qualification: [u8; 32],
    qualified_startup_digest: [u8; 32],
    qualified_provider_digest: [u8; 32],
    qualified_finality_digest: [u8; 32],
}

impl core::fmt::Debug for WalletV2ActivationPermit {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("WalletV2ActivationPermit")
            .field("activation_class", &self.activation_class)
            .field("bindings", &"[REDACTED]")
            .finish()
    }
}

impl WalletV2ActivationPermit {
    pub(crate) fn activation_class_v2(&self) -> WalletV2ActivationClass {
        self.activation_class
    }
    pub fn activation_digest_v2(&self) -> &[u8; 32] {
        &self.activation_digest
    }

    pub fn wallet_id_v2(&self) -> &[u8; 32] {
        &self.wallet_id
    }

    pub fn migration_id_v2(&self) -> &[u8; 32] {
        &self.migration_id
    }

    pub fn ownership_id_v2(&self) -> &[u8; 32] {
        &self.ownership_id
    }

    pub fn migration_target_digest_v2(&self) -> &[u8; 32] {
        &self.migration_target_digest
    }

    pub fn migration_target_path_digest_v2(&self) -> &[u8; 32] {
        &self.migration_target_path_digest
    }

    pub fn note_cipher_id_v2(&self) -> &[u8; 32] {
        &self.note_cipher_id
    }

    pub fn monotonic_protection_id_v2(&self) -> &[u8; 32] {
        &self.monotonic_protection_id
    }

    pub fn monotonic_store_qualification_v2(&self) -> &[u8; 32] {
        &self.monotonic_store_qualification
    }

    pub fn qualified_startup_digest_v2(&self) -> &[u8; 32] {
        &self.qualified_startup_digest
    }

    pub fn qualified_provider_digest_v2(&self) -> &[u8; 32] {
        &self.qualified_provider_digest
    }

    pub fn qualified_finality_digest_v2(&self) -> &[u8; 32] {
        &self.qualified_finality_digest
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WalletV2ActivationError {
    Disabled,
    InvalidConfiguration,
    SchemaMismatch,
    IdentityMismatch,
    MigrationNotCommitted,
    OwnershipNotCommitted,
    LegacyWriterNotRetired,
    PendingTransaction,
    MissingPrerequisite,
    AmbiguousPrerequisite,
    MonotonicMismatch,
    QualificationMismatch,
    RuntimeStateRejected,
    MonotonicUnavailable,
    MonotonicUnqualified,
    OwnershipTargetMismatch,
}

/// Evaluate the sole production activation predicate. This has no side
/// effects, caches no permit, and installs no dispatch.
pub fn evaluate_wallet_v2_activation(
    mode: &WalletV2ActivationMode,
    prerequisites: &WalletV2ActivationPrerequisites,
) -> Result<WalletV2ActivationPermit, WalletV2ActivationError> {
    let (config, activation_class) = match mode {
        WalletV2ActivationMode::Disabled => return Err(WalletV2ActivationError::Disabled),
        WalletV2ActivationMode::Production(config) => (config, WalletV2ActivationClass::Production),
        #[cfg(feature = "wallet-v2-reference-tests")]
        WalletV2ActivationMode::ReferenceOnly(config) => {
            (config, WalletV2ActivationClass::ReferenceOnly)
        }
    };
    config.validate_v2()?;

    if prerequisites.asl2_magic != config.asl2_magic
        || prerequisites.asl2_schema_version != config.asl2_schema_version
        || prerequisites.activation_schema_version != config.activation_schema_version
    {
        return Err(WalletV2ActivationError::SchemaMismatch);
    }
    if [
        prerequisites.wallet_id,
        prerequisites.note_cipher_id,
        prerequisites.migration_id,
        prerequisites.ownership_id,
        prerequisites.monotonic_protection_id,
    ]
    .contains(&[0u8; 32])
        || prerequisites.wallet_id != config.wallet_id
        || prerequisites.note_cipher_id != config.note_cipher_id
        || prerequisites.migration_id != config.migration_id
        || prerequisites.ownership_id != config.ownership_id
    {
        return Err(WalletV2ActivationError::IdentityMismatch);
    }
    if !prerequisites.migration_committed {
        return Err(WalletV2ActivationError::MigrationNotCommitted);
    }
    if !prerequisites.asl2_ownership_committed {
        return Err(WalletV2ActivationError::OwnershipNotCommitted);
    }
    let retired: HashSet<_> = prerequisites.retired_legacy_roles.iter().copied().collect();
    if prerequisites.retired_legacy_roles.len() != ALL_LEGACY_STORE_ROLES_V2.len()
        || retired.len() != ALL_LEGACY_STORE_ROLES_V2.len()
        || ALL_LEGACY_STORE_ROLES_V2
            .iter()
            .any(|role| !retired.contains(role))
    {
        return Err(WalletV2ActivationError::LegacyWriterNotRetired);
    }
    if prerequisites.has_pending_transaction {
        return Err(WalletV2ActivationError::PendingTransaction);
    }

    let migration_target = exactly_one_nonzero_v2(&prerequisites.migration_target_digests)?;
    if migration_target != config.migration_target_digest
        || prerequisites.migration_target_path_digest != config.migration_target_path_digest
        || prerequisites.monotonic_protection_id != config.monotonic_protection_id
    {
        return Err(WalletV2ActivationError::MonotonicMismatch);
    }
    let monotonic_qualification =
        exactly_one_nonzero_v2(&prerequisites.monotonic_store_qualifications)?;
    if monotonic_qualification != config.monotonic_store_qualification {
        return Err(WalletV2ActivationError::QualificationMismatch);
    }
    let startup = exactly_one_nonzero_v2(&prerequisites.qualified_startup_digests)?;
    let provider = exactly_one_nonzero_v2(&prerequisites.qualified_provider_digests)?;
    let finality = exactly_one_nonzero_v2(&prerequisites.qualified_finality_digests)?;
    if startup != config.qualified_startup_digest
        || provider != config.qualified_provider_digest
        || finality != config.qualified_finality_digest
    {
        return Err(WalletV2ActivationError::QualificationMismatch);
    }

    let mut hasher = Sha256::new();
    hasher.update(ACTIVATION_PERMIT_DOMAIN_V2);
    hasher.update(config.asl2_magic);
    hasher.update([config.asl2_schema_version]);
    hasher.update([config.activation_schema_version]);
    hasher.update(config.wallet_id);
    hasher.update(config.note_cipher_id);
    hasher.update(config.migration_id);
    hasher.update(config.ownership_id);
    hasher.update(config.migration_target_digest);
    hasher.update(config.migration_target_path_digest);
    hasher.update(config.monotonic_protection_id);
    hasher.update(config.monotonic_store_qualification);
    hasher.update(config.qualified_startup_digest);
    hasher.update(config.qualified_provider_digest);
    hasher.update(config.qualified_finality_digest);
    let activation_digest = hasher.finalize().into();
    Ok(WalletV2ActivationPermit {
        activation_class,
        activation_digest,
        wallet_id: config.wallet_id,
        migration_id: config.migration_id,
        ownership_id: config.ownership_id,
        migration_target_digest: config.migration_target_digest,
        migration_target_path_digest: config.migration_target_path_digest,
        note_cipher_id: config.note_cipher_id,
        monotonic_protection_id: config.monotonic_protection_id,
        monotonic_store_qualification: config.monotonic_store_qualification,
        qualified_startup_digest: config.qualified_startup_digest,
        qualified_provider_digest: config.qualified_provider_digest,
        qualified_finality_digest: config.qualified_finality_digest,
    })
}

fn exactly_one_nonzero_v2(values: &[[u8; 32]]) -> Result<[u8; 32], WalletV2ActivationError> {
    match values {
        [] => Err(WalletV2ActivationError::MissingPrerequisite),
        [value] if *value == [0u8; 32] => Err(WalletV2ActivationError::MissingPrerequisite),
        [value] => Ok(*value),
        _ => Err(WalletV2ActivationError::AmbiguousPrerequisite),
    }
}

/// Cheap, side-effect-free preflight used before restart recovery. Full
/// startup still reconstructs prerequisites and reevaluates the predicate.
pub(crate) fn permit_matches_mode_configuration_v2(
    mode: &WalletV2ActivationMode,
    permit: &WalletV2ActivationPermit,
) -> bool {
    let (config, activation_class) = match mode {
        WalletV2ActivationMode::Disabled => return false,
        WalletV2ActivationMode::Production(config) => (config, WalletV2ActivationClass::Production),
        #[cfg(feature = "wallet-v2-reference-tests")]
        WalletV2ActivationMode::ReferenceOnly(config) => {
            (config, WalletV2ActivationClass::ReferenceOnly)
        }
    };
    config.validate_v2().is_ok()
        && permit.activation_class == activation_class
        && permit.wallet_id == config.wallet_id
        && permit.note_cipher_id == config.note_cipher_id
        && permit.migration_id == config.migration_id
        && permit.ownership_id == config.ownership_id
        && permit.migration_target_digest == config.migration_target_digest
        && permit.migration_target_path_digest == config.migration_target_path_digest
        && permit.monotonic_protection_id == config.monotonic_protection_id
        && permit.monotonic_store_qualification == config.monotonic_store_qualification
        && permit.qualified_startup_digest == config.qualified_startup_digest
        && permit.qualified_provider_digest == config.qualified_provider_digest
        && permit.qualified_finality_digest == config.qualified_finality_digest
}

#[cfg(test)]
mod tests {
    use super::*;

    fn digest(seed: u8) -> [u8; 32] {
        [seed; 32]
    }

    fn config() -> WalletV2ProductionConfig {
        WalletV2ProductionConfig::new_v2(
            digest(1),
            digest(2),
            digest(3),
            digest(4),
            digest(5),
            digest(6),
            digest(7),
            digest(8),
            digest(9),
            digest(10),
            digest(11),
        )
        .unwrap()
    }

    fn prerequisites() -> WalletV2ActivationPrerequisites {
        WalletV2ActivationPrerequisites {
            asl2_magic: LANE_FOREST_WALLET_TXN_MAGIC_V2,
            asl2_schema_version: LANE_FOREST_WALLET_TXN_VERSION_V3,
            activation_schema_version: WALLET_V2_ACTIVATION_SCHEMA_VERSION,
            wallet_id: digest(1),
            note_cipher_id: digest(2),
            migration_id: digest(3),
            migration_committed: true,
            ownership_id: digest(4),
            asl2_ownership_committed: true,
            retired_legacy_roles: ALL_LEGACY_STORE_ROLES_V2.to_vec(),
            has_pending_transaction: false,
            migration_target_digests: vec![digest(5)],
            migration_target_path_digest: digest(6),
            monotonic_protection_id: digest(7),
            monotonic_store_qualifications: vec![digest(8)],
            qualified_startup_digests: vec![digest(9)],
            qualified_provider_digests: vec![digest(10)],
            qualified_finality_digests: vec![digest(11)],
        }
    }

    #[test]
    fn default_is_disabled_and_production_success_is_exact_and_idempotent() {
        let prerequisites = prerequisites();
        assert_eq!(
            evaluate_wallet_v2_activation(&WalletV2ActivationMode::default(), &prerequisites),
            Err(WalletV2ActivationError::Disabled)
        );
        let mode = WalletV2ActivationMode::Production(config());
        let first = evaluate_wallet_v2_activation(&mode, &prerequisites).unwrap();
        let replay = evaluate_wallet_v2_activation(&mode, &prerequisites).unwrap();
        assert!(first.activation_digest_v2() != &[0u8; 32]);
        assert_eq!(first, replay);
        assert_eq!(first.wallet_id_v2(), &digest(1));
        assert_eq!(first.migration_id_v2(), &digest(3));
        assert_eq!(first.ownership_id_v2(), &digest(4));
        assert_eq!(first.migration_target_digest_v2(), &digest(5));
        assert_eq!(first.migration_target_path_digest_v2(), &digest(6));
    }

    #[derive(Clone, Copy, Debug)]
    enum FailureCase {
        SchemaMagic,
        SchemaVersion,
        ActivationVersion,
        WalletZero,
        WalletMismatch,
        CipherZero,
        CipherMismatch,
        MigrationZero,
        MigrationMismatch,
        MigrationUncommitted,
        OwnershipZero,
        OwnershipMismatch,
        OwnershipUncommitted,
        LegacyRoleMissing,
        LegacyRoleAmbiguous,
        PendingTransaction,
        MonotonicMissing,
        MonotonicZero,
        MonotonicMismatch,
        MonotonicAmbiguous,
        TargetPathZero,
        TargetPathMismatch,
        ProtectionZero,
        ProtectionMismatch,
        MonotonicQualificationMissing,
        MonotonicQualificationZero,
        MonotonicQualificationMismatch,
        MonotonicQualificationAmbiguous,
        StartupMissing,
        StartupZero,
        StartupMismatch,
        StartupAmbiguous,
        ProviderMissing,
        ProviderZero,
        ProviderMismatch,
        ProviderAmbiguous,
        FinalityMissing,
        FinalityZero,
        FinalityMismatch,
        FinalityAmbiguous,
    }

    const FAILURE_CASES: &[FailureCase] = &[
        FailureCase::SchemaMagic,
        FailureCase::SchemaVersion,
        FailureCase::ActivationVersion,
        FailureCase::WalletZero,
        FailureCase::WalletMismatch,
        FailureCase::CipherZero,
        FailureCase::CipherMismatch,
        FailureCase::MigrationZero,
        FailureCase::MigrationMismatch,
        FailureCase::MigrationUncommitted,
        FailureCase::OwnershipZero,
        FailureCase::OwnershipMismatch,
        FailureCase::OwnershipUncommitted,
        FailureCase::LegacyRoleMissing,
        FailureCase::LegacyRoleAmbiguous,
        FailureCase::PendingTransaction,
        FailureCase::MonotonicMissing,
        FailureCase::MonotonicZero,
        FailureCase::MonotonicMismatch,
        FailureCase::MonotonicAmbiguous,
        FailureCase::TargetPathZero,
        FailureCase::TargetPathMismatch,
        FailureCase::ProtectionZero,
        FailureCase::ProtectionMismatch,
        FailureCase::MonotonicQualificationMissing,
        FailureCase::MonotonicQualificationZero,
        FailureCase::MonotonicQualificationMismatch,
        FailureCase::MonotonicQualificationAmbiguous,
        FailureCase::StartupMissing,
        FailureCase::StartupZero,
        FailureCase::StartupMismatch,
        FailureCase::StartupAmbiguous,
        FailureCase::ProviderMissing,
        FailureCase::ProviderZero,
        FailureCase::ProviderMismatch,
        FailureCase::ProviderAmbiguous,
        FailureCase::FinalityMissing,
        FailureCase::FinalityZero,
        FailureCase::FinalityMismatch,
        FailureCase::FinalityAmbiguous,
    ];

    fn break_prerequisite(case: FailureCase, value: &mut WalletV2ActivationPrerequisites) {
        match case {
            FailureCase::SchemaMagic => value.asl2_magic = *b"BAD!",
            FailureCase::SchemaVersion => value.asl2_schema_version ^= 1,
            FailureCase::ActivationVersion => value.activation_schema_version ^= 1,
            FailureCase::WalletZero => value.wallet_id = [0u8; 32],
            FailureCase::WalletMismatch => value.wallet_id = digest(21),
            FailureCase::CipherZero => value.note_cipher_id = [0u8; 32],
            FailureCase::CipherMismatch => value.note_cipher_id = digest(22),
            FailureCase::MigrationZero => value.migration_id = [0u8; 32],
            FailureCase::MigrationMismatch => value.migration_id = digest(23),
            FailureCase::MigrationUncommitted => value.migration_committed = false,
            FailureCase::OwnershipZero => value.ownership_id = [0u8; 32],
            FailureCase::OwnershipMismatch => value.ownership_id = digest(24),
            FailureCase::OwnershipUncommitted => value.asl2_ownership_committed = false,
            FailureCase::LegacyRoleMissing => {
                value.retired_legacy_roles.pop();
            }
            FailureCase::LegacyRoleAmbiguous => value
                .retired_legacy_roles
                .push(LegacyWalletStoreRoleV2::WalletAndScanner),
            FailureCase::PendingTransaction => value.has_pending_transaction = true,
            FailureCase::MonotonicMissing => value.migration_target_digests.clear(),
            FailureCase::MonotonicZero => value.migration_target_digests[0] = [0u8; 32],
            FailureCase::MonotonicMismatch => value.migration_target_digests[0] = digest(25),
            FailureCase::MonotonicAmbiguous => {
                value.migration_target_digests.push(digest(26));
            }
            FailureCase::TargetPathZero => value.migration_target_path_digest = [0u8; 32],
            FailureCase::TargetPathMismatch => value.migration_target_path_digest = digest(36),
            FailureCase::ProtectionZero => value.monotonic_protection_id = [0u8; 32],
            FailureCase::ProtectionMismatch => value.monotonic_protection_id = digest(27),
            FailureCase::MonotonicQualificationMissing => {
                value.monotonic_store_qualifications.clear();
            }
            FailureCase::MonotonicQualificationZero => {
                value.monotonic_store_qualifications[0] = [0u8; 32];
            }
            FailureCase::MonotonicQualificationMismatch => {
                value.monotonic_store_qualifications[0] = digest(34);
            }
            FailureCase::MonotonicQualificationAmbiguous => {
                value.monotonic_store_qualifications.push(digest(35));
            }
            FailureCase::StartupMissing => value.qualified_startup_digests.clear(),
            FailureCase::StartupZero => value.qualified_startup_digests[0] = [0u8; 32],
            FailureCase::StartupMismatch => value.qualified_startup_digests[0] = digest(28),
            FailureCase::StartupAmbiguous => value.qualified_startup_digests.push(digest(29)),
            FailureCase::ProviderMissing => value.qualified_provider_digests.clear(),
            FailureCase::ProviderZero => value.qualified_provider_digests[0] = [0u8; 32],
            FailureCase::ProviderMismatch => value.qualified_provider_digests[0] = digest(30),
            FailureCase::ProviderAmbiguous => value.qualified_provider_digests.push(digest(31)),
            FailureCase::FinalityMissing => value.qualified_finality_digests.clear(),
            FailureCase::FinalityZero => value.qualified_finality_digests[0] = [0u8; 32],
            FailureCase::FinalityMismatch => value.qualified_finality_digests[0] = digest(32),
            FailureCase::FinalityAmbiguous => value.qualified_finality_digests.push(digest(33)),
        }
    }

    fn expected_error(case: FailureCase) -> WalletV2ActivationError {
        match case {
            FailureCase::SchemaMagic
            | FailureCase::SchemaVersion
            | FailureCase::ActivationVersion => WalletV2ActivationError::SchemaMismatch,
            FailureCase::WalletZero
            | FailureCase::WalletMismatch
            | FailureCase::CipherZero
            | FailureCase::CipherMismatch
            | FailureCase::MigrationZero
            | FailureCase::MigrationMismatch
            | FailureCase::OwnershipZero
            | FailureCase::OwnershipMismatch
            | FailureCase::ProtectionZero => WalletV2ActivationError::IdentityMismatch,
            FailureCase::MigrationUncommitted => WalletV2ActivationError::MigrationNotCommitted,
            FailureCase::OwnershipUncommitted => WalletV2ActivationError::OwnershipNotCommitted,
            FailureCase::LegacyRoleMissing | FailureCase::LegacyRoleAmbiguous => {
                WalletV2ActivationError::LegacyWriterNotRetired
            }
            FailureCase::PendingTransaction => WalletV2ActivationError::PendingTransaction,
            FailureCase::MonotonicMissing
            | FailureCase::MonotonicZero
            | FailureCase::MonotonicQualificationMissing
            | FailureCase::MonotonicQualificationZero
            | FailureCase::StartupMissing
            | FailureCase::StartupZero
            | FailureCase::ProviderMissing
            | FailureCase::ProviderZero
            | FailureCase::FinalityMissing
            | FailureCase::FinalityZero => WalletV2ActivationError::MissingPrerequisite,
            FailureCase::MonotonicAmbiguous
            | FailureCase::MonotonicQualificationAmbiguous
            | FailureCase::StartupAmbiguous
            | FailureCase::ProviderAmbiguous
            | FailureCase::FinalityAmbiguous => WalletV2ActivationError::AmbiguousPrerequisite,
            FailureCase::MonotonicMismatch
            | FailureCase::TargetPathZero
            | FailureCase::TargetPathMismatch
            | FailureCase::ProtectionMismatch => WalletV2ActivationError::MonotonicMismatch,
            FailureCase::MonotonicQualificationMismatch
            | FailureCase::StartupMismatch
            | FailureCase::ProviderMismatch
            | FailureCase::FinalityMismatch => WalletV2ActivationError::QualificationMismatch,
        }
    }

    #[test]
    fn every_runtime_prerequisite_independently_fails_closed() {
        let mode = WalletV2ActivationMode::Production(config());
        for case in FAILURE_CASES {
            let mut broken = prerequisites();
            break_prerequisite(*case, &mut broken);
            assert_eq!(
                evaluate_wallet_v2_activation(&mode, &broken),
                Err(expected_error(*case)),
                "wrong fail-closed outcome for case: {case:?}"
            );
        }
    }

    #[test]
    fn activation_accepts_only_asl2_schema_v3_and_remains_default_off() {
        assert_eq!(LANE_FOREST_WALLET_TXN_VERSION_V3, 3);
        let mut runtime = prerequisites();
        runtime.asl2_schema_version = 2;
        assert_eq!(
            evaluate_wallet_v2_activation(&WalletV2ActivationMode::default(), &runtime),
            Err(WalletV2ActivationError::Disabled)
        );
        assert_eq!(
            evaluate_wallet_v2_activation(&WalletV2ActivationMode::Production(config()), &runtime,),
            Err(WalletV2ActivationError::SchemaMismatch)
        );

        runtime.asl2_schema_version = LANE_FOREST_WALLET_TXN_VERSION_V3;
        assert!(evaluate_wallet_v2_activation(
            &WalletV2ActivationMode::Production(config()),
            &runtime,
        )
        .is_ok());
    }

    #[test]
    fn zero_configuration_bindings_are_rejected() {
        for index in 0..11 {
            let mut bindings = [
                digest(1),
                digest(2),
                digest(3),
                digest(4),
                digest(5),
                digest(6),
                digest(7),
                digest(8),
                digest(9),
                digest(10),
                digest(11),
            ];
            bindings[index] = [0u8; 32];
            assert_eq!(
                WalletV2ProductionConfig::new_v2(
                    bindings[0],
                    bindings[1],
                    bindings[2],
                    bindings[3],
                    bindings[4],
                    bindings[5],
                    bindings[6],
                    bindings[7],
                    bindings[8],
                    bindings[9],
                    bindings[10],
                ),
                Err(WalletV2ActivationError::InvalidConfiguration)
            );
        }
    }

    #[test]
    fn permit_copied_between_wallets_is_rejected() {
        let mode = WalletV2ActivationMode::Production(config());
        let permit = evaluate_wallet_v2_activation(&mode, &prerequisites()).unwrap();
        let mut other_wallet = prerequisites();
        other_wallet.wallet_id = digest(0x91);
        assert_eq!(
            evaluate_wallet_v2_activation(&mode, &other_wallet),
            Err(WalletV2ActivationError::IdentityMismatch)
        );
        assert_ne!(permit.wallet_id_v2(), &other_wallet.wallet_id);
        let other_mode = WalletV2ActivationMode::Production(
            WalletV2ProductionConfig::new_v2(
                digest(0x91),
                digest(2),
                digest(3),
                digest(4),
                digest(5),
                digest(6),
                digest(7),
                digest(8),
                digest(9),
                digest(10),
                digest(11),
            )
            .unwrap(),
        );
        assert!(!permit_matches_mode_configuration_v2(&other_mode, &permit));
    }
}
