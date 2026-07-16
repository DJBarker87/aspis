//! Fuzz-style harness for the fixed-layout proof/prefix parser surface.
//!
//! Approach: the workspace is pinned to a stable toolchain (the CI job uses
//! `dtolnay/rust-toolchain@stable`), so cargo-fuzz's nightly + libFuzzer
//! requirement is out of scope. These are `proptest` harnesses that run under
//! the ordinary `cargo test` on the same stable pin.
//!
//! Guarantees exercised:
//!  * `proof::Header::parse` never panics on arbitrary bytes, and every
//!    accepted header round-trips: `write(parse(x)) == x[..HEADER_LEN]`.
//!  * The candidate/state-only/spend prefix parsers never panic on arbitrary
//!    or fixture-mutated bytes and only ever return a defined `Result`.
//!  * The absolute-offset helpers never panic and never return an offset
//!    outside the supplied proof bytes.
//!
//! The committed valid release proof fixture seeds a small deterministic
//! corpus so the harness explores structurally valid inputs and their local
//! mutations, not only random noise.

use aspis_core::circle_prefix::PaymentCandidatePrefix;
use aspis_core::proof::{
    first_layer_first_phase_opening_offset, first_layer_second_phase_helper_offset,
    first_layer_second_phase_opening_offset, ood_value_offset, second_phase_claim_offset, Cursor,
    Header, HEADER_LEN,
};
use aspis_core::state_only_prefix::{
    StateOnlyCandidatePrefix, StateOnlyProfile21Prefix, StateOnlySpendPrefix,
};
use proptest::prelude::*;

/// The committed valid Spend release proof. Used only to seed a structurally
/// valid starting corpus; the harness asserts no panics, not acceptance.
const RELEASE_PROOF: &[u8] =
    include_bytes!("../../aspis-prover/fixtures/spend_q18_g37_release.bin");

/// Drive every parser and offset helper on one byte string. Returns nothing;
/// the contract is that none of these calls may panic and every offset that
/// is returned lies within `bytes`.
fn exercise_all_parsers(bytes: &[u8]) {
    // Header: never panics, and any accepted header re-serializes to the same
    // 16 header bytes (canonical round-trip).
    if let Some(header) = Header::parse(bytes) {
        let mut written = [0u8; HEADER_LEN];
        header.write(&mut written);
        assert_eq!(
            &written[..],
            &bytes[..HEADER_LEN],
            "accepted header did not round-trip through write()"
        );

        // The pure header-arithmetic offset helpers are exercised only for
        // no-panic / no-overflow: they compute where a value *would* sit in a
        // complete proof, so their result may legitimately exceed a truncated
        // input's length. They must, however, never panic.
        for layer in 0..(header.num_rounds as usize).min(64) + 1 {
            for sample in 0..header.ood_samples_per_round() + 1 {
                let _ = ood_value_offset(&header, layer, sample);
            }
        }
        for helper in 0..header.second_phase_claim_count() + 1 {
            let _ = second_phase_claim_offset(&header, helper);
        }
    }

    // Proof-byte offset helpers: never panic, never return an offset that would
    // index past the slice.
    if let Some(offset) = first_layer_first_phase_opening_offset(bytes) {
        assert!(offset <= bytes.len(), "c1 opening offset out of bounds");
    }
    if let Some(offset) = first_layer_second_phase_opening_offset(bytes) {
        assert!(offset <= bytes.len(), "c2 opening offset out of bounds");
    }
    for helper in 0..3 {
        if let Some(offset) = first_layer_second_phase_helper_offset(bytes, helper) {
            assert!(offset <= bytes.len(), "c2 helper offset out of bounds");
        }
    }

    // The structured prefix parsers: reject-or-parse, never panic. Any leftover
    // openings slice returned must be a suffix of the input.
    if let Ok((_, rest)) = PaymentCandidatePrefix::parse_from_proof(bytes) {
        assert!(rest.len() <= bytes.len());
    }
    if let Ok((_, rest)) = StateOnlyCandidatePrefix::parse_from_proof(bytes) {
        assert!(rest.len() <= bytes.len());
    }
    if let Ok((_, rest)) = StateOnlySpendPrefix::parse_from_proof(bytes) {
        assert!(rest.len() <= bytes.len());
    }
    if let Ok((_, rest)) = StateOnlyProfile21Prefix::parse_from_proof(bytes) {
        assert!(rest.len() <= bytes.len());
    }

    // The bounded cursor must never read past its slice.
    let mut cursor = Cursor::new(bytes);
    let _ = cursor.take_u32();
    let _ = cursor.take_hash();
    let _ = cursor.take_u64();
    assert!(cursor.position() <= bytes.len());
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// Arbitrary bytes must never panic any parser or offset helper.
    #[test]
    fn arbitrary_bytes_never_panic(bytes in proptest::collection::vec(any::<u8>(), 0..320)) {
        exercise_all_parsers(&bytes);
    }

    /// Arbitrary bytes carrying a plausible header prefix (correct magic and a
    /// supported version) reach deeper into the parsers than pure noise.
    #[test]
    fn plausible_header_bytes_never_panic(
        mut bytes in proptest::collection::vec(any::<u8>(), HEADER_LEN..320)
    ) {
        bytes[0..4].copy_from_slice(b"ASP0");
        // Restrict the version byte to the two recognised envelopes so parsing
        // proceeds past the header gate more often.
        bytes[4] = if bytes[4] & 1 == 0 { 3 } else { 4 };
        exercise_all_parsers(&bytes);
    }

    /// Single-byte mutations of the committed valid proof: exercises the
    /// accept/reject boundary around a structurally valid input.
    #[test]
    fn single_byte_mutation_of_valid_proof_never_panics(
        index in 0usize..RELEASE_PROOF.len(),
        delta in 1u8..=255,
    ) {
        let mut bytes = RELEASE_PROOF.to_vec();
        bytes[index] = bytes[index].wrapping_add(delta);
        exercise_all_parsers(&bytes);
    }

    /// Truncations of the committed valid proof at arbitrary lengths.
    #[test]
    fn truncations_of_valid_proof_never_panic(len in 0usize..=RELEASE_PROOF.len()) {
        exercise_all_parsers(&RELEASE_PROOF[..len]);
    }
}

/// The unmodified valid fixture parses without panic and its header round-trips.
#[test]
fn valid_release_fixture_header_round_trips() {
    let header = Header::parse(RELEASE_PROOF).expect("release fixture has a valid header");
    let mut written = [0u8; HEADER_LEN];
    header.write(&mut written);
    assert_eq!(&written[..], &RELEASE_PROOF[..HEADER_LEN]);
    // And the whole parser battery is clean on the genuine proof.
    exercise_all_parsers(RELEASE_PROOF);
}
