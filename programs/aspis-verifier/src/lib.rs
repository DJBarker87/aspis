//! Aspis on-chain verifier.
//!
//! The production surface is the Spend minimal-dispatch entrypoint
//! ([`dispatch`]), the [`atomic_payment`] state-transition module, the
//! proof-account [`lifecycle`], and the production proof [`verify`] paths,
//! all speaking the frozen instruction [`wire`]. Superseded-profile and
//! diagnostic handlers and their feature definitions were removed with their
//! code; those wire tags fail closed in every build. The pre-strip research
//! tree is preserved at the git tags `research-archive-2026-07-14` and
//! `research-archive-2026-07-15` and in git history.
//!
//! The opt-in `v5-cu-probe` feature builds a separate local-validator-only
//! entrypoint. Tag 66 selects diagnostic kernels; tag 67 wraps the complete
//! v5 verifier in the unchanged atomic state transition.
//! Entrypoint builds are incompatible with `spend-production`; host tooling
//! may feature-unify the library only while `no-entrypoint` is set.
//!
//! The default `v5-production-tag67` production switch instead
//! routes tag 67 through the minimal production dispatcher and the same atomic
//! verify-and-apply wrapper. It never exposes tag 66 or the probe entrypoint.
//! It is part of the default feature set after the recorded correspondence,
//! formal, CU, and release gates passed.
//!
//! Proof account layout:
//! [0..4] magic "ASPU", [4..8] proof_len u32 LE, [8..40] upload authority,
//! [40..40+proof_len] proof bytes.

// Solana's entrypoint macro emits `target_os = "solana"`; the host toolchain's
// check-cfg list does not know that SBF target even though cargo-build-sbf does.
#![allow(unexpected_cfgs)]

#[cfg(all(feature = "spend-minimal-dispatch", not(feature = "spend-production")))]
compile_error!(
    "SPEND_MINIMAL_DISPATCH_REQUIRES_PRODUCTION: the minimal wire surface is valid only for spend-production"
);

#[cfg(all(feature = "spend-dynamic-rate512", not(feature = "spend-production")))]
compile_error!(
    "SPEND_DYNAMIC_RATE512_REQUIRES_PRODUCTION: query-local public coordinates are enabled only for spend-production"
);

#[cfg(all(
    feature = "v5-cu-probe",
    feature = "spend-production",
    not(feature = "no-entrypoint")
))]
compile_error!(
    "V5_CU_PROBE_FORBIDS_PRODUCTION (v5-cu-probe): the local CU probe must use its isolated tag-67 entrypoint"
);

#[cfg(all(
    feature = "v5-cu-probe",
    feature = "v5-production-tag67",
    not(feature = "no-entrypoint")
))]
compile_error!(
    "V5_TAG67_PRODUCTION_FORBIDS_PROBE: production tag 67 and the diagnostic probe entrypoint cannot coexist"
);

#[cfg(all(
    feature = "v6-cu-probe",
    any(
        feature = "spend-production",
        feature = "v5-production-tag67",
        feature = "v6-production-tag72",
        feature = "v7-production-tag73"
    ),
    not(feature = "no-entrypoint")
))]
compile_error!(
    "V6_CU_PROBE_FORBIDS_PRODUCTION: the V6 local CU probe must use its isolated entrypoint"
);

#[cfg(all(
    feature = "v6-cu-probe",
    feature = "v5-cu-probe",
    not(feature = "no-entrypoint")
))]
compile_error!("V6_CU_PROBE_FORBIDS_V5_PROBE: select exactly one local probe entrypoint");

#[cfg(all(
    feature = "v7-cu-probe",
    any(
        feature = "spend-production",
        feature = "v5-production-tag67",
        feature = "v6-production-tag72",
        feature = "v7-production-tag73"
    ),
    not(feature = "no-entrypoint")
))]
compile_error!(
    "V7_CU_PROBE_FORBIDS_PRODUCTION: the V7 local CU probe must use its isolated entrypoint"
);

#[cfg(all(
    feature = "v7-cu-probe",
    any(feature = "v5-cu-probe", feature = "v6-cu-probe"),
    not(feature = "no-entrypoint")
))]
compile_error!("V7_CU_PROBE_FORBIDS_OTHER_PROBES: select exactly one local probe entrypoint");

#[cfg(all(
    feature = "v7-pool-cu-profile",
    any(
        feature = "spend-production",
        feature = "v5-production-tag67",
        feature = "v6-production-tag72",
        feature = "v7-production-tag73",
        feature = "v5-cu-probe",
        feature = "v6-cu-probe",
        feature = "v7-cu-probe"
    ),
    not(feature = "no-entrypoint")
))]
compile_error!("V7_POOL_CU_PROFILE_FORBIDS_OTHER_ENTRYPOINTS: select only the local Pool profiler");

#[cfg(all(
    feature = "v7-pair-forest-cu-profile",
    any(
        feature = "spend-production",
        feature = "v5-production-tag67",
        feature = "v6-production-tag72",
        feature = "v7-production-tag73",
        feature = "v5-cu-probe",
        feature = "v6-cu-probe",
        feature = "v7-cu-probe",
        feature = "v7-pool-cu-profile"
    ),
    not(feature = "no-entrypoint")
))]
compile_error!(
    "V7_PAIR_FOREST_CU_PROFILE_FORBIDS_OTHER_ENTRYPOINTS: build the unverified transport profile in isolation"
);

#[cfg(any(
    all(
        feature = "v7-pair-forest-cu-return-824",
        any(
            feature = "v7-pair-forest-cu-return-856",
            feature = "v7-pair-forest-cu-return-920",
            feature = "v7-pair-forest-cu-return-1024"
        )
    ),
    all(
        feature = "v7-pair-forest-cu-return-856",
        any(
            feature = "v7-pair-forest-cu-return-920",
            feature = "v7-pair-forest-cu-return-1024"
        )
    ),
    all(
        feature = "v7-pair-forest-cu-return-920",
        feature = "v7-pair-forest-cu-return-1024"
    )
))]
compile_error!("V7_PAIR_FOREST_CU_RETURN_SWEEP_REQUIRES_EXACTLY_ONE_SIZE");

pub mod atomic_payment;
pub mod dispatch;
pub mod lifecycle;
#[cfg(any(feature = "v5-cu-probe", feature = "v5-production-tag67"))]
pub mod v5_atomic_terminal;
#[cfg(any(feature = "v5-cu-probe", feature = "v5-production-tag67"))]
pub mod v5_cu_probe;
#[cfg(any(feature = "v5-cu-probe", feature = "v5-production-tag67"))]
pub mod v5_full_transaction;
#[cfg(any(feature = "v5-cu-probe", feature = "v5-production-tag67"))]
pub mod v5_relation_stress;
#[cfg(feature = "v6-cu-probe")]
pub mod v6_cu_probe;
#[cfg(any(feature = "v6-production-tag72", test))]
pub mod v6_transaction;
#[cfg(any(
    feature = "v6-cu-probe",
    feature = "v6-production-tag72",
    feature = "v7-cu-probe",
    feature = "v7-production-tag73",
    feature = "v7-pool-cu-profile",
    test
))]
pub mod v6_verifier;
#[cfg(any(
    feature = "v7-pair-forest-asq8",
    feature = "v7-pair-forest-cu-profile",
    test
))]
pub mod v7_pair_empty_roots;
#[cfg(any(
    feature = "v7-pair-forest-asq8",
    feature = "v7-pair-forest-cu-profile",
    test
))]
pub mod v7_pair_forest_dispatch;
#[cfg(feature = "v7-pool-cu-profile")]
pub mod v7_pool_cu_profile;
#[cfg(any(feature = "v7-pool-dispatch-profile", test))]
pub mod v7_pool_dispatch;
#[cfg(any(
    feature = "v7-pool-dispatch-profile",
    feature = "v7-pool-cu-profile",
    test
))]
pub mod v7_pool_native_dispatch;
#[cfg(any(feature = "v7-pool-dispatch-profile", test))]
pub mod v7_pool_receipt;
pub mod v7_staged_pair_profile;
#[cfg(any(feature = "v7-production-tag73", test))]
pub mod v7_transaction;
#[cfg(any(
    feature = "v7-cu-probe",
    feature = "v7-production-tag73",
    feature = "v7-pool-cu-profile",
    test
))]
pub mod v7_verifier;
pub mod verify;
pub mod wire;

use solana_program::declare_id;

// Bound to the checked-in deployment keypair; release artifacts pin the
// resulting SBF hash. The abandoned first mainnet demonstration deployed a
// byte-identical predecessor binary under the disposable program id
// 9kPpUknrRicMvaGa6zPNERGUYDj6fMvMR8PwMS3iFR6Z. Every PDA derives from the
// runtime program_id parameter, so the constant is the canonical code
// identity, not a deployment binding.
declare_id!("7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue");

pub use dispatch::process_spend_production_instruction;
pub use lifecycle::PROOF_ACCOUNT_HEADER_LEN;
pub use wire::{
    AspisInstruction, ExactWideV4DiagnosticMode, JohnsonM31CircleDiagnosticPhase,
    M31CircleBasisDiagnosticMode, StateOnlyWidth28DiagnosticPhase, TwoPointBatchingDiagnosticMode,
    ZkKernelKind,
};

#[cfg(test)]
pub(crate) mod test_support {
    use solana_program::{account_info::AccountInfo, clock::Epoch, pubkey::Pubkey};

    pub(crate) fn make_account<'a>(
        key: &'a Pubkey,
        owner: &'a Pubkey,
        lamports: &'a mut u64,
        data: &'a mut [u8],
        is_signer: bool,
        is_writable: bool,
    ) -> AccountInfo<'a> {
        AccountInfo::new(
            key,
            is_signer,
            is_writable,
            lamports,
            data,
            owner,
            false,
            Epoch::default(),
        )
    }
}
