//! Fail-closed operator startup manifest and multi-provider agreement gate.
//!
//! This is deliberately pure: network transport, provider authentication and
//! multisig custody remain outside the crate. The caller supplies observations
//! from every pinned provider plus an authenticated manifest envelope. No
//! signer, relayer queue or indexer loop should start unless this exact gate
//! returns a receipt.

use sha2::{Digest as _, Sha256};

use crate::scan_state::FinalizedChainPointV1;

pub const OPERATOR_RELEASE_MANIFEST_DOMAIN_V1: &[u8] =
    b"aspis:pool-v1:operator-release-manifest:sha256:v1";
pub const OPERATOR_STARTUP_RECEIPT_DOMAIN_V1: &[u8] =
    b"aspis:pool-v1:operator-startup-receipt:sha256:v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProgramDeploymentPinV1 {
    pub program_id: [u8; 32],
    pub loader_id: [u8; 32],
    /// Zero only for a loader form with no ProgramData account.
    pub programdata_address: [u8; 32],
    pub executable_sha256: [u8; 32],
    /// `None` pins an immutable deployment.
    pub upgrade_authority: Option<[u8; 32]>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolReleasePinV1 {
    pub pool_address: [u8; 32],
    pub deployment_domain: [u8; 32],
    pub asset_mint: [u8; 32],
    pub asset_id: u32,
    pub vault_token_account: [u8; 32],
    pub format_binding: [u8; 32],
    pub verifier_registry: [u8; 32],
    pub verifier_policy_binding: [u8; 32],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RegistryReleasePinV1 {
    pub registry_address: [u8; 32],
    pub policy_binding: [u8; 32],
    pub authority: [u8; 32],
    pub generation: u64,
    pub activation_delay_slots: u64,
    pub selected_entry: [u8; 32],
    pub verifier_program_id: [u8; 32],
    pub verifier_profile: [u8; 32],
    pub verifier_release: [u8; 32],
    pub statement_version: u8,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FinalizedReleaseCheckpointV1 {
    pub point: FinalizedChainPointV1,
    pub pool_state_sha256: [u8; 32],
    pub root_sequence: u64,
    pub root: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OperatorReleaseManifestV1 {
    pub release_id: [u8; 32],
    pub authority_set_id: [u8; 32],
    pub cluster_genesis_hash: [u8; 32],
    /// Canonically ascending hashes/identities of every configured provider.
    /// Startup requires every entry to report the exact same pinned state.
    pub provider_ids: Vec<[u8; 32]>,
    pub pool_program: ProgramDeploymentPinV1,
    pub registry_program: ProgramDeploymentPinV1,
    pub verifier_program: ProgramDeploymentPinV1,
    pub pool: PoolReleasePinV1,
    pub registry: RegistryReleasePinV1,
    pub relayer_policy_id: [u8; 32],
    pub operator_fee_payer: [u8; 32],
    pub minimum_fee_payer_reserve_lamports: u64,
    pub checkpoint: FinalizedReleaseCheckpointV1,
    pub pool_sbf_reproducible_build_sha256: [u8; 32],
    pub registry_sbf_reproducible_build_sha256: [u8; 32],
    pub verifier_sbf_reproducible_build_sha256: [u8; 32],
    pub formal_evidence_sha256: [u8; 32],
    pub finalized_devnet_lifecycle_sha256: [u8; 32],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FinalizedProviderObservationV1 {
    pub provider_id: [u8; 32],
    pub context_slot: u64,
    pub cluster_genesis_hash: [u8; 32],
    pub pool_program: ProgramDeploymentPinV1,
    pub registry_program: ProgramDeploymentPinV1,
    pub verifier_program: ProgramDeploymentPinV1,
    pub pool: PoolReleasePinV1,
    pub registry: RegistryReleasePinV1,
    pub registry_paused: bool,
    pub selected_entry_active: bool,
    pub selected_entry_retired: bool,
    pub checkpoint: FinalizedReleaseCheckpointV1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LocalOperatorStateV1 {
    pub indexer_head: FinalizedChainPointV1,
    pub root_sequence: u64,
    pub root: [u8; 32],
    pub relayer_policy_id: [u8; 32],
    pub operator_fee_payer: [u8; 32],
    pub minimum_fee_payer_reserve_lamports: u64,
    pub pool_sbf_sha256: [u8; 32],
    pub registry_sbf_sha256: [u8; 32],
    pub verifier_sbf_sha256: [u8; 32],
    pub formal_evidence_sha256: [u8; 32],
    pub finalized_devnet_lifecycle_sha256: [u8; 32],
}

pub trait ReleaseManifestAuthenticatorV1 {
    /// Authenticate the canonical manifest digest under the separately pinned
    /// governance/threshold authority set. The envelope is never interpreted
    /// or logged by this crate.
    fn authenticates_manifest_v1(
        &self,
        authority_set_id: &[u8; 32],
        manifest_digest: &[u8; 32],
        authenticated_envelope: &[u8],
    ) -> bool;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OperatorStartupErrorV1 {
    InvalidManifest,
    NonCanonicalProviders,
    ManifestAuthenticationFailed,
    MissingProvider,
    UnexpectedProvider,
    ProviderDisagreement,
    ProviderBelowCheckpoint,
    WrongCluster,
    ProgramDeploymentMismatch,
    PoolBindingMismatch,
    RegistryBindingMismatch,
    RegistryUnavailable,
    CheckpointMismatch,
    LocalStateMismatch,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OperatorStartupReceiptV1 {
    pub manifest_digest: [u8; 32],
    pub provider_set_digest: [u8; 32],
    pub checkpoint: FinalizedReleaseCheckpointV1,
    pub receipt_digest: [u8; 32],
}

pub fn operator_release_manifest_digest_v1(
    manifest: &OperatorReleaseManifestV1,
) -> Result<[u8; 32], OperatorStartupErrorV1> {
    validate_manifest_shape_v1(manifest)?;
    let mut hasher = Sha256::new();
    hasher.update(OPERATOR_RELEASE_MANIFEST_DOMAIN_V1);
    hasher.update(manifest.release_id);
    hasher.update(manifest.authority_set_id);
    hasher.update(manifest.cluster_genesis_hash);
    hasher.update(
        u32::try_from(manifest.provider_ids.len())
            .map_err(|_| OperatorStartupErrorV1::InvalidManifest)?
            .to_le_bytes(),
    );
    for provider in &manifest.provider_ids {
        hasher.update(provider);
    }
    hash_program_pin_v1(&mut hasher, manifest.pool_program);
    hash_program_pin_v1(&mut hasher, manifest.registry_program);
    hash_program_pin_v1(&mut hasher, manifest.verifier_program);
    hash_pool_pin_v1(&mut hasher, manifest.pool);
    hash_registry_pin_v1(&mut hasher, manifest.registry);
    hasher.update(manifest.relayer_policy_id);
    hasher.update(manifest.operator_fee_payer);
    hasher.update(manifest.minimum_fee_payer_reserve_lamports.to_le_bytes());
    hash_checkpoint_v1(&mut hasher, manifest.checkpoint);
    hasher.update(manifest.pool_sbf_reproducible_build_sha256);
    hasher.update(manifest.registry_sbf_reproducible_build_sha256);
    hasher.update(manifest.verifier_sbf_reproducible_build_sha256);
    hasher.update(manifest.formal_evidence_sha256);
    hasher.update(manifest.finalized_devnet_lifecycle_sha256);
    Ok(hasher.finalize().into())
}

pub fn validate_operator_startup_v1(
    manifest: &OperatorReleaseManifestV1,
    authenticated_manifest_envelope: &[u8],
    authenticator: &impl ReleaseManifestAuthenticatorV1,
    providers: &[FinalizedProviderObservationV1],
    local: LocalOperatorStateV1,
) -> Result<OperatorStartupReceiptV1, OperatorStartupErrorV1> {
    let manifest_digest = operator_release_manifest_digest_v1(manifest)?;
    if authenticated_manifest_envelope.is_empty()
        || !authenticator.authenticates_manifest_v1(
            &manifest.authority_set_id,
            &manifest_digest,
            authenticated_manifest_envelope,
        )
    {
        return Err(OperatorStartupErrorV1::ManifestAuthenticationFailed);
    }
    if providers.len() != manifest.provider_ids.len() {
        return Err(if providers.len() < manifest.provider_ids.len() {
            OperatorStartupErrorV1::MissingProvider
        } else {
            OperatorStartupErrorV1::UnexpectedProvider
        });
    }
    let mut ordered = providers.to_vec();
    ordered.sort_by_key(|provider| provider.provider_id);
    if ordered
        .iter()
        .map(|provider| provider.provider_id)
        .ne(manifest.provider_ids.iter().copied())
    {
        return Err(OperatorStartupErrorV1::UnexpectedProvider);
    }
    let first = ordered
        .first()
        .ok_or(OperatorStartupErrorV1::MissingProvider)?;
    for provider in &ordered {
        if provider.context_slot < manifest.checkpoint.point.slot() {
            return Err(OperatorStartupErrorV1::ProviderBelowCheckpoint);
        }
        if provider.cluster_genesis_hash != manifest.cluster_genesis_hash {
            return Err(OperatorStartupErrorV1::WrongCluster);
        }
        if provider.pool_program != manifest.pool_program
            || provider.registry_program != manifest.registry_program
            || provider.verifier_program != manifest.verifier_program
        {
            return Err(OperatorStartupErrorV1::ProgramDeploymentMismatch);
        }
        if provider.pool != manifest.pool {
            return Err(OperatorStartupErrorV1::PoolBindingMismatch);
        }
        if provider.registry != manifest.registry {
            return Err(OperatorStartupErrorV1::RegistryBindingMismatch);
        }
        if provider.registry_paused
            || !provider.selected_entry_active
            || provider.selected_entry_retired
        {
            return Err(OperatorStartupErrorV1::RegistryUnavailable);
        }
        if provider.checkpoint != manifest.checkpoint {
            return Err(OperatorStartupErrorV1::CheckpointMismatch);
        }
        if provider_without_identity_v1(provider) != provider_without_identity_v1(first) {
            return Err(OperatorStartupErrorV1::ProviderDisagreement);
        }
    }
    if local.indexer_head != manifest.checkpoint.point
        || local.root_sequence != manifest.checkpoint.root_sequence
        || local.root != manifest.checkpoint.root
        || local.relayer_policy_id != manifest.relayer_policy_id
        || local.operator_fee_payer != manifest.operator_fee_payer
        || local.minimum_fee_payer_reserve_lamports != manifest.minimum_fee_payer_reserve_lamports
        || local.pool_sbf_sha256 != manifest.pool_sbf_reproducible_build_sha256
        || local.registry_sbf_sha256 != manifest.registry_sbf_reproducible_build_sha256
        || local.verifier_sbf_sha256 != manifest.verifier_sbf_reproducible_build_sha256
        || local.formal_evidence_sha256 != manifest.formal_evidence_sha256
        || local.finalized_devnet_lifecycle_sha256 != manifest.finalized_devnet_lifecycle_sha256
    {
        return Err(OperatorStartupErrorV1::LocalStateMismatch);
    }

    let provider_set_digest = provider_set_digest_v1(&manifest.provider_ids);
    let mut hasher = Sha256::new();
    hasher.update(OPERATOR_STARTUP_RECEIPT_DOMAIN_V1);
    hasher.update(manifest_digest);
    hasher.update(provider_set_digest);
    hash_checkpoint_v1(&mut hasher, manifest.checkpoint);
    let receipt_digest = hasher.finalize().into();
    Ok(OperatorStartupReceiptV1 {
        manifest_digest,
        provider_set_digest,
        checkpoint: manifest.checkpoint,
        receipt_digest,
    })
}

fn validate_manifest_shape_v1(
    manifest: &OperatorReleaseManifestV1,
) -> Result<(), OperatorStartupErrorV1> {
    let required = [
        manifest.release_id,
        manifest.authority_set_id,
        manifest.cluster_genesis_hash,
        manifest.relayer_policy_id,
        manifest.operator_fee_payer,
        manifest.checkpoint.pool_state_sha256,
        manifest.checkpoint.root,
        manifest.pool_sbf_reproducible_build_sha256,
        manifest.registry_sbf_reproducible_build_sha256,
        manifest.verifier_sbf_reproducible_build_sha256,
        manifest.formal_evidence_sha256,
        manifest.finalized_devnet_lifecycle_sha256,
    ];
    if required.iter().any(|value| *value == [0u8; 32])
        || manifest.provider_ids.len() < 2
        || manifest.minimum_fee_payer_reserve_lamports == 0
        || manifest.registry.activation_delay_slots == 0
        || manifest.registry.statement_version == 0
        || manifest.pool.asset_id >= aspis_core::field::P
        || manifest.pool.verifier_registry != manifest.registry.registry_address
        || manifest.pool.verifier_policy_binding != manifest.registry.policy_binding
        || manifest.registry.verifier_program_id != manifest.verifier_program.program_id
        || manifest.pool_program.executable_sha256 != manifest.pool_sbf_reproducible_build_sha256
        || manifest.registry_program.executable_sha256
            != manifest.registry_sbf_reproducible_build_sha256
        || manifest.verifier_program.executable_sha256
            != manifest.verifier_sbf_reproducible_build_sha256
    {
        return Err(OperatorStartupErrorV1::InvalidManifest);
    }
    if manifest
        .provider_ids
        .windows(2)
        .any(|pair| pair[0] >= pair[1])
        || manifest
            .provider_ids
            .iter()
            .any(|provider| *provider == [0u8; 32])
    {
        return Err(OperatorStartupErrorV1::NonCanonicalProviders);
    }
    let program_ids = [
        manifest.pool_program.program_id,
        manifest.registry_program.program_id,
        manifest.verifier_program.program_id,
    ];
    if program_ids.iter().any(|id| *id == [0u8; 32])
        || program_ids[0] == program_ids[1]
        || program_ids[0] == program_ids[2]
        || program_ids[1] == program_ids[2]
        || !program_pin_shape_v1(manifest.pool_program)
        || !program_pin_shape_v1(manifest.registry_program)
        || !program_pin_shape_v1(manifest.verifier_program)
        || pool_pin_has_zero_v1(manifest.pool)
        || registry_pin_has_zero_v1(manifest.registry)
    {
        return Err(OperatorStartupErrorV1::InvalidManifest);
    }
    Ok(())
}

fn program_pin_shape_v1(pin: ProgramDeploymentPinV1) -> bool {
    pin.loader_id != [0u8; 32]
        && pin.executable_sha256 != [0u8; 32]
        && pin.upgrade_authority != Some([0u8; 32])
        && (pin.upgrade_authority.is_none() || pin.programdata_address != [0u8; 32])
}

fn pool_pin_has_zero_v1(pin: PoolReleasePinV1) -> bool {
    pin.pool_address == [0u8; 32]
        || pin.deployment_domain == [0u8; 32]
        || pin.asset_mint == [0u8; 32]
        || pin.vault_token_account == [0u8; 32]
        || pin.format_binding == [0u8; 32]
        || pin.verifier_registry == [0u8; 32]
        || pin.verifier_policy_binding == [0u8; 32]
}

fn registry_pin_has_zero_v1(pin: RegistryReleasePinV1) -> bool {
    pin.registry_address == [0u8; 32]
        || pin.policy_binding == [0u8; 32]
        || pin.authority == [0u8; 32]
        || pin.selected_entry == [0u8; 32]
        || pin.verifier_program_id == [0u8; 32]
        || pin.verifier_profile == [0u8; 32]
        || pin.verifier_release == [0u8; 32]
}

fn provider_without_identity_v1(
    provider: &FinalizedProviderObservationV1,
) -> FinalizedProviderObservationV1 {
    FinalizedProviderObservationV1 {
        provider_id: [0u8; 32],
        context_slot: 0,
        ..*provider
    }
}

fn provider_set_digest_v1(providers: &[[u8; 32]]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"aspis:pool-v1:operator-provider-set:sha256:v1");
    hasher.update((providers.len() as u32).to_le_bytes());
    for provider in providers {
        hasher.update(provider);
    }
    hasher.finalize().into()
}

fn hash_program_pin_v1(hasher: &mut Sha256, pin: ProgramDeploymentPinV1) {
    hasher.update(pin.program_id);
    hasher.update(pin.loader_id);
    hasher.update(pin.programdata_address);
    hasher.update(pin.executable_sha256);
    hasher.update([u8::from(pin.upgrade_authority.is_some())]);
    hasher.update(pin.upgrade_authority.unwrap_or([0u8; 32]));
}

fn hash_pool_pin_v1(hasher: &mut Sha256, pin: PoolReleasePinV1) {
    hasher.update(pin.pool_address);
    hasher.update(pin.deployment_domain);
    hasher.update(pin.asset_mint);
    hasher.update(pin.asset_id.to_le_bytes());
    hasher.update(pin.vault_token_account);
    hasher.update(pin.format_binding);
    hasher.update(pin.verifier_registry);
    hasher.update(pin.verifier_policy_binding);
}

fn hash_registry_pin_v1(hasher: &mut Sha256, pin: RegistryReleasePinV1) {
    hasher.update(pin.registry_address);
    hasher.update(pin.policy_binding);
    hasher.update(pin.authority);
    hasher.update(pin.generation.to_le_bytes());
    hasher.update(pin.activation_delay_slots.to_le_bytes());
    hasher.update(pin.selected_entry);
    hasher.update(pin.verifier_program_id);
    hasher.update(pin.verifier_profile);
    hasher.update(pin.verifier_release);
    hasher.update([pin.statement_version]);
}

fn hash_checkpoint_v1(hasher: &mut Sha256, checkpoint: FinalizedReleaseCheckpointV1) {
    hasher.update(checkpoint.point.slot().to_le_bytes());
    hasher.update(checkpoint.point.block_hash());
    hasher.update(checkpoint.pool_state_sha256);
    hasher.update(checkpoint.root_sequence.to_le_bytes());
    hasher.update(checkpoint.root);
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Authenticator(bool);

    impl ReleaseManifestAuthenticatorV1 for Authenticator {
        fn authenticates_manifest_v1(&self, _: &[u8; 32], _: &[u8; 32], envelope: &[u8]) -> bool {
            self.0 && envelope == [0xaa]
        }
    }

    fn bytes(seed: u8) -> [u8; 32] {
        [seed; 32]
    }

    fn program(seed: u8) -> ProgramDeploymentPinV1 {
        ProgramDeploymentPinV1 {
            program_id: bytes(seed),
            loader_id: bytes(0xf0),
            programdata_address: bytes(seed + 1),
            executable_sha256: bytes(seed + 2),
            upgrade_authority: Some(bytes(seed + 3)),
        }
    }

    fn manifest() -> OperatorReleaseManifestV1 {
        OperatorReleaseManifestV1 {
            release_id: bytes(1),
            authority_set_id: bytes(2),
            cluster_genesis_hash: bytes(3),
            provider_ids: vec![bytes(4), bytes(5)],
            pool_program: program(10),
            registry_program: program(20),
            verifier_program: program(30),
            pool: PoolReleasePinV1 {
                pool_address: bytes(40),
                deployment_domain: bytes(41),
                asset_mint: bytes(42),
                asset_id: 9,
                vault_token_account: bytes(43),
                format_binding: bytes(44),
                verifier_registry: bytes(50),
                verifier_policy_binding: bytes(51),
            },
            registry: RegistryReleasePinV1 {
                registry_address: bytes(50),
                policy_binding: bytes(51),
                authority: bytes(52),
                generation: 7,
                activation_delay_slots: 100,
                selected_entry: bytes(53),
                verifier_program_id: bytes(30),
                verifier_profile: bytes(54),
                verifier_release: bytes(55),
                statement_version: 1,
            },
            relayer_policy_id: bytes(60),
            operator_fee_payer: bytes(61),
            minimum_fee_payer_reserve_lamports: 1_000_000,
            checkpoint: FinalizedReleaseCheckpointV1 {
                point: FinalizedChainPointV1::new(1000, bytes(70)).unwrap(),
                pool_state_sha256: bytes(71),
                root_sequence: 88,
                root: bytes(72),
            },
            pool_sbf_reproducible_build_sha256: bytes(12),
            registry_sbf_reproducible_build_sha256: bytes(22),
            verifier_sbf_reproducible_build_sha256: bytes(32),
            formal_evidence_sha256: bytes(83),
            finalized_devnet_lifecycle_sha256: bytes(84),
        }
    }

    fn observation(
        manifest: &OperatorReleaseManifestV1,
        provider_id: [u8; 32],
    ) -> FinalizedProviderObservationV1 {
        FinalizedProviderObservationV1 {
            provider_id,
            context_slot: 1001,
            cluster_genesis_hash: manifest.cluster_genesis_hash,
            pool_program: manifest.pool_program,
            registry_program: manifest.registry_program,
            verifier_program: manifest.verifier_program,
            pool: manifest.pool,
            registry: manifest.registry,
            registry_paused: false,
            selected_entry_active: true,
            selected_entry_retired: false,
            checkpoint: manifest.checkpoint,
        }
    }

    fn local(manifest: &OperatorReleaseManifestV1) -> LocalOperatorStateV1 {
        LocalOperatorStateV1 {
            indexer_head: manifest.checkpoint.point,
            root_sequence: manifest.checkpoint.root_sequence,
            root: manifest.checkpoint.root,
            relayer_policy_id: manifest.relayer_policy_id,
            operator_fee_payer: manifest.operator_fee_payer,
            minimum_fee_payer_reserve_lamports: manifest.minimum_fee_payer_reserve_lamports,
            pool_sbf_sha256: manifest.pool_sbf_reproducible_build_sha256,
            registry_sbf_sha256: manifest.registry_sbf_reproducible_build_sha256,
            verifier_sbf_sha256: manifest.verifier_sbf_reproducible_build_sha256,
            formal_evidence_sha256: manifest.formal_evidence_sha256,
            finalized_devnet_lifecycle_sha256: manifest.finalized_devnet_lifecycle_sha256,
        }
    }

    #[test]
    fn startup_requires_authenticated_exact_two_provider_and_local_agreement() {
        let manifest = manifest();
        let providers = [
            observation(&manifest, manifest.provider_ids[1]),
            {
                let mut provider = observation(&manifest, manifest.provider_ids[0]);
                provider.context_slot = 1002;
                provider
            },
        ];
        let receipt = validate_operator_startup_v1(
            &manifest,
            &[0xaa],
            &Authenticator(true),
            &providers,
            local(&manifest),
        )
        .unwrap();
        assert_eq!(
            receipt.manifest_digest,
            operator_release_manifest_digest_v1(&manifest).unwrap()
        );

        let mut bad_provider = providers;
        bad_provider[0].pool_program.executable_sha256[0] ^= 1;
        assert_eq!(
            validate_operator_startup_v1(
                &manifest,
                &[0xaa],
                &Authenticator(true),
                &bad_provider,
                local(&manifest),
            ),
            Err(OperatorStartupErrorV1::ProgramDeploymentMismatch)
        );
        assert_eq!(
            validate_operator_startup_v1(
                &manifest,
                &[0xaa],
                &Authenticator(false),
                &providers,
                local(&manifest),
            ),
            Err(OperatorStartupErrorV1::ManifestAuthenticationFailed)
        );
        let mut bad_local = local(&manifest);
        bad_local.root[0] ^= 1;
        assert_eq!(
            validate_operator_startup_v1(
                &manifest,
                &[0xaa],
                &Authenticator(true),
                &providers,
                bad_local,
            ),
            Err(OperatorStartupErrorV1::LocalStateMismatch)
        );
    }
}
