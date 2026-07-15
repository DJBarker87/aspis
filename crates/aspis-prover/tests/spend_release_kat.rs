//! Frozen release-proof known-answer tests.
//!
//! The fixture pair `spend_q18_g37_release.{bin,statement.json}` is the exact
//! deployment payload: the finalized production proof and its public v4
//! statement sidecar, ground for the mainnet-target deployment domain. The
//! deployment reuses these bytes without a re-grind, so every transcript
//! label, domain separator, Merkle tag, Poseidon2 constant, params table,
//! statement encoding, proof grammar, and grinding predicate must keep
//! verifying these exact bytes. These tests are the consensus gate for that
//! property: they pin the fixture bytes by SHA-256 and run them through the
//! full production host verifier.

use aspis_prover::HOST_HASH;
use aspis_statement::{AtomicPaymentStatementV4, SpendPublic};
use serde_json::Value;
use sha2::{Digest as _, Sha256};

const RELEASE_PROOF: &[u8] = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/fixtures/spend_q18_g37_release.bin"
));
const RELEASE_STATEMENT_SIDECAR: &[u8] = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/fixtures/spend_q18_g37_release.statement.json"
));

const RELEASE_PROOF_LEN: usize = 65_407;
const RELEASE_PROOF_SHA256: &str =
    "32eb419e0c5c3ef4fa2db0d32579e88f1207547d8fb010279efeb6c05981b529";
const RELEASE_STATEMENT_SHA256: &str =
    "c35f6152ce4ffbfa6edeba68b4a6d2738e19b1420181c9500ba73f0c717c8699";

// Frozen sidecar schema values for the aspis-spend release epoch.
const RELEASE_STATEMENT_ARTIFACT: &str = "aspis_spend_production_statement";
const RELEASE_STATEMENT_SELECTION_RULE: &str =
    "least GoodSpend selector from three post-final branches";

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn decode_hex_32(value: &str) -> [u8; 32] {
    assert_eq!(value.len(), 64, "expected 64 hex characters");
    let mut decoded = [0u8; 32];
    for (index, output) in decoded.iter_mut().enumerate() {
        *output = u8::from_str_radix(&value[index * 2..index * 2 + 2], 16).unwrap();
    }
    decoded
}

fn release_statement() -> AtomicPaymentStatementV4 {
    let sidecar: Value = serde_json::from_slice(RELEASE_STATEMENT_SIDECAR).unwrap();
    assert_eq!(
        sidecar["artifact"].as_str().unwrap(),
        RELEASE_STATEMENT_ARTIFACT
    );
    assert_eq!(
        sidecar["selection_rule"].as_str().unwrap(),
        RELEASE_STATEMENT_SELECTION_RULE
    );
    assert!(sidecar["witness_independent_public_metadata"]
        .as_bool()
        .unwrap());
    let digest_field = |field: &str| {
        let bytes = decode_hex_32(sidecar[field].as_str().unwrap());
        aspis_statement::decode_digest_canonical(&bytes).unwrap()
    };
    AtomicPaymentStatementV4 {
        pool: decode_hex_32(sidecar["pool_hex"].as_str().unwrap()),
        sequence: sidecar["sequence"].as_u64().unwrap(),
        spend: SpendPublic {
            anchor: digest_field("current_anchor_hex"),
            nullifier: digest_field("nullifier_hex"),
            output_commitment: digest_field("output_commitment_hex"),
            asset_id: aspis_statement::decode_asset_id_canonical(
                u32::try_from(sidecar["asset_id"].as_u64().unwrap()).unwrap(),
            )
            .unwrap(),
            fee: u32::try_from(sidecar["fee"].as_u64().unwrap()).unwrap(),
        },
        output_anchor: digest_field("output_anchor_hex"),
        deployment_domain: decode_hex_32(sidecar["deployment_domain_hex"].as_str().unwrap()),
    }
}

/// The consensus gate: the frozen production proof must verify end-to-end
/// through the full mined-path host verifier against its frozen statement.
#[test]
fn frozen_spend_release_fixture_verifies_end_to_end() {
    assert_eq!(RELEASE_PROOF.len(), RELEASE_PROOF_LEN);
    assert_eq!(hex(&Sha256::digest(RELEASE_PROOF)), RELEASE_PROOF_SHA256);
    assert_eq!(
        hex(&Sha256::digest(RELEASE_STATEMENT_SIDECAR)),
        RELEASE_STATEMENT_SHA256
    );

    let statement = release_statement();
    aspis_statement::state_only_spend::verify_atomic_state_only_spend_v4(
        RELEASE_PROOF,
        &statement,
        HOST_HASH,
        None,
    )
    .expect("frozen release proof must verify through the production host verifier");
}

/// Full release-grade replay: the frozen proof's serialized query selector
/// must equal the least Good selector recomputed from the proof's own prefix
/// under the production (PoW-checked) transcript schedule.
#[test]
#[ignore = "slow exact q3 complete-product replay; run in --release"]
fn frozen_spend_release_fixture_replays_least_good_selector_with_pow() {
    let statement = release_statement();
    let statement_digest =
        aspis_statement::atomic_payment_statement_digest_v4(&statement, HOST_HASH).unwrap();
    let (prefix, suffix) =
        aspis_core::state_only_prefix::StateOnlySpendPrefix::parse_from_proof(RELEASE_PROOF)
            .unwrap();
    assert!(!suffix.is_empty(), "release proof must carry openings");
    let serialized_selector = prefix.query_selector;

    let evaluation = aspis_prover::state_only_good_spend::evaluate_spend_query_candidates_host(
        HOST_HASH,
        &prefix,
        &statement_digest,
    )
    .unwrap();
    println!("{evaluation:#?}");
    assert_eq!(evaluation.selected_selector, Some(serialized_selector));
}
