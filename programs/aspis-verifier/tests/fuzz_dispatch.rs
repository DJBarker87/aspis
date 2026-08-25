//! Fuzz-style harness for the production instruction dispatch surface
//! (`process_spend_production_instruction`).
//!
//! Approach: proptest on the pinned stable toolchain (cargo-fuzz's nightly +
//! libFuzzer requirement is out of scope for the stable CI pin).
//!
//! Invariants exercised:
//!  * Arbitrary instruction bytes against arbitrary small account vectors
//!    never panic and never index out of bounds — the dispatcher always
//!    returns a `Result<(), ProgramError>` (a defined error, by construction).
//!  * Empty instruction data is rejected as `InvalidInstructionData`.
//!  * Every tag outside the feature-selected production set is
//!    rejected with a defined error.

use aspis_verifier::{id, process_spend_production_instruction};
use proptest::prelude::*;
use solana_program::{
    account_info::AccountInfo, clock::Epoch, program_error::ProgramError, pubkey::Pubkey,
};

const PRODUCTION_TAGS: &[u8] = &[
    0,
    1,
    59,
    60,
    62,
    63,
    64,
    65,
    #[cfg(feature = "v5-production-tag67")]
    67,
    #[cfg(feature = "v6-production-tag72")]
    72,
];

/// One arbitrary account slot: its owner is either the running program or a
/// foreign key, and its signer/writable bits and data length vary.
#[derive(Clone, Debug)]
struct AccountSpec {
    owner_is_program: bool,
    is_signer: bool,
    is_writable: bool,
    lamports: u64,
    data_len: usize,
}

fn account_spec_strategy() -> impl Strategy<Value = AccountSpec> {
    (
        any::<bool>(),
        any::<bool>(),
        any::<bool>(),
        any::<u64>(),
        0usize..96,
    )
        .prop_map(
            |(owner_is_program, is_signer, is_writable, lamports, data_len)| AccountSpec {
                owner_is_program,
                is_signer,
                is_writable,
                lamports,
                data_len,
            },
        )
}

/// Materialise up to five accounts from their specs and run the dispatcher.
/// Each slot has its own independent backing storage so every `AccountInfo`
/// holds a distinct, non-aliasing mutable borrow. Slots beyond `specs.len()`
/// are simply not included in the account vector. Returns the result.
fn run_dispatch(instruction_data: &[u8], specs: &[AccountSpec]) -> Result<(), ProgramError> {
    let program_id = id();
    let foreign = Pubkey::new_from_array([7u8; 32]);
    let owner_of = |spec: &AccountSpec| {
        if spec.owner_is_program {
            program_id
        } else {
            foreign
        }
    };

    // Five independent backing slots; only the first `specs.len()` are used.
    let key0 = Pubkey::new_from_array([1u8; 32]);
    let key1 = Pubkey::new_from_array([2u8; 32]);
    let key2 = Pubkey::new_from_array([3u8; 32]);
    let key3 = Pubkey::new_from_array([4u8; 32]);
    let key4 = Pubkey::new_from_array([5u8; 32]);
    let mut lam0 = specs.first().map(|s| s.lamports).unwrap_or(0);
    let mut lam1 = specs.get(1).map(|s| s.lamports).unwrap_or(0);
    let mut lam2 = specs.get(2).map(|s| s.lamports).unwrap_or(0);
    let mut lam3 = specs.get(3).map(|s| s.lamports).unwrap_or(0);
    let mut lam4 = specs.get(4).map(|s| s.lamports).unwrap_or(0);
    let mut data0 = vec![0u8; specs.first().map(|s| s.data_len).unwrap_or(0)];
    let mut data1 = vec![0u8; specs.get(1).map(|s| s.data_len).unwrap_or(0)];
    let mut data2 = vec![0u8; specs.get(2).map(|s| s.data_len).unwrap_or(0)];
    let mut data3 = vec![0u8; specs.get(3).map(|s| s.data_len).unwrap_or(0)];
    let mut data4 = vec![0u8; specs.get(4).map(|s| s.data_len).unwrap_or(0)];
    let owner0 = specs.first().map(owner_of).unwrap_or(program_id);
    let owner1 = specs.get(1).map(owner_of).unwrap_or(program_id);
    let owner2 = specs.get(2).map(owner_of).unwrap_or(program_id);
    let owner3 = specs.get(3).map(owner_of).unwrap_or(program_id);
    let owner4 = specs.get(4).map(owner_of).unwrap_or(program_id);

    let mut accounts: Vec<AccountInfo> = Vec::with_capacity(specs.len());
    if let Some(spec) = specs.first() {
        accounts.push(AccountInfo::new(
            &key0,
            spec.is_signer,
            spec.is_writable,
            &mut lam0,
            data0.as_mut_slice(),
            &owner0,
            false,
            Epoch::default(),
        ));
    }
    if let Some(spec) = specs.get(1) {
        accounts.push(AccountInfo::new(
            &key1,
            spec.is_signer,
            spec.is_writable,
            &mut lam1,
            data1.as_mut_slice(),
            &owner1,
            false,
            Epoch::default(),
        ));
    }
    if let Some(spec) = specs.get(2) {
        accounts.push(AccountInfo::new(
            &key2,
            spec.is_signer,
            spec.is_writable,
            &mut lam2,
            data2.as_mut_slice(),
            &owner2,
            false,
            Epoch::default(),
        ));
    }
    if let Some(spec) = specs.get(3) {
        accounts.push(AccountInfo::new(
            &key3,
            spec.is_signer,
            spec.is_writable,
            &mut lam3,
            data3.as_mut_slice(),
            &owner3,
            false,
            Epoch::default(),
        ));
    }
    if let Some(spec) = specs.get(4) {
        accounts.push(AccountInfo::new(
            &key4,
            spec.is_signer,
            spec.is_writable,
            &mut lam4,
            data4.as_mut_slice(),
            &owner4,
            false,
            Epoch::default(),
        ));
    }

    process_spend_production_instruction(&program_id, &accounts, instruction_data)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(384))]

    /// Arbitrary instruction bytes and account shapes never panic.
    #[test]
    fn arbitrary_dispatch_never_panics(
        instruction_data in proptest::collection::vec(any::<u8>(), 0..200),
        specs in proptest::collection::vec(account_spec_strategy(), 0..6),
    ) {
        // The only contract is: no panic, no OOB; the type guarantees a
        // defined error on the failure path.
        let _ = run_dispatch(&instruction_data, &specs);
    }

    /// Bytes whose first byte is a production tag drive the real parse arms.
    #[test]
    fn production_tag_bodies_never_panic(
        tag_index in 0usize..PRODUCTION_TAGS.len(),
        body in proptest::collection::vec(any::<u8>(), 0..200),
        specs in proptest::collection::vec(account_spec_strategy(), 0..6),
    ) {
        let mut instruction_data = vec![PRODUCTION_TAGS[tag_index]];
        instruction_data.extend_from_slice(&body);
        let _ = run_dispatch(&instruction_data, &specs);
    }

    /// Every non-production leading tag is rejected with a defined error.
    #[test]
    fn unknown_tags_fail_closed(
        tag in any::<u8>().prop_filter("production tags handled elsewhere", |t| !PRODUCTION_TAGS.contains(t)),
        body in proptest::collection::vec(any::<u8>(), 0..64),
        specs in proptest::collection::vec(account_spec_strategy(), 0..6),
    ) {
        let mut instruction_data = vec![tag];
        instruction_data.extend_from_slice(&body);
        let result = run_dispatch(&instruction_data, &specs);
        // Tag 61 is the one non-frozen tag with an explicit custom fail-closed
        // result; everything else is InvalidInstructionData.
        prop_assert!(result.is_err(), "unknown tag {tag} was accepted");
    }
}

/// Empty instruction data is rejected as InvalidInstructionData with no
/// accounts present.
#[test]
fn empty_instruction_data_is_rejected() {
    let program_id = id();
    assert_eq!(
        process_spend_production_instruction(&program_id, &[], &[]),
        Err(ProgramError::InvalidInstructionData)
    );
}
