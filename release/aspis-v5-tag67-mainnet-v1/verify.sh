#!/usr/bin/env bash
set -euo pipefail

bundle_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
repo_root="$(CDPATH= cd -- "$bundle_dir/../.." && pwd)"

cd "$bundle_dir"
if command -v sha256sum >/dev/null 2>&1; then
    sha256sum -c SHA256SUMS
elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 -c SHA256SUMS
else
    echo "error: sha256sum or shasum is required" >&2
    exit 1
fi

python3 - "$bundle_dir" "$repo_root" <<'PY'
import hashlib
import json
import pathlib
import sys

bundle = pathlib.Path(sys.argv[1])
root = pathlib.Path(sys.argv[2])
manifest = json.loads((bundle / "manifest.json").read_text(encoding="utf-8"))
evidence = json.loads(
    (bundle / "evidence/mainnet-lifecycle.json").read_text(encoding="utf-8")
)
formal = json.loads(
    (bundle / "formal/formal-evidence.json").read_text(encoding="utf-8")
)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

assert manifest["schema_version"] == 2
assert manifest["record_updated_at_utc"] == "2026-08-14T09:24:07Z"

for relative, identity in manifest["objects"].items():
    path = bundle / relative
    assert path.is_file(), relative
    assert path.stat().st_size == identity["bytes"], relative
    assert digest(path) == identity["sha256"], relative

sbf = root / "release/aspis-v5-tag67-frozen-candidate-v1/program/aspis_verifier_v5_tag67.so"
assert sbf.stat().st_size == evidence["artifacts"]["sbf"]["bytes"]
assert digest(sbf) == evidence["artifacts"]["sbf"]["sha256"]

assert evidence["identities"]["nullifier_pda_bump"] == 255
assert evidence["transactions"]["tag67"]["simulation_compute_units"] == 1_334_452
assert evidence["transactions"]["tag67"]["landed_compute_units"] == 1_334_452
assert evidence["transactions"]["tag67"]["exact_signed_wire_simulation_equal_to_landed"]
assert evidence["transaction_accounting"]["core_lifecycle_transactions"] == 84
assert evidence["refund_reconciliation"]["total_direct_receipt_by_pinned_recipient_lamports"] == 10_980_894_882
assert evidence["refund_reconciliation"]["payer_final_lamports"] == 0
assert evidence["retained_accounts"]["total_permanent_lamports"] == 3_981_120

assert formal["release_id"] == manifest["release_id"]
assert formal["schema_version"] == 2
assert formal["release_scope"]["sbf_sha256"] == evidence["artifacts"]["sbf"]["sha256"]
assert formal["release_scope"]["tag67_signature"] == evidence["transactions"]["tag67"]["signature"]
assert formal["release_scope"]["tag67_finalized_slot"] == evidence["transactions"]["tag67"]["finalized_slot"]
assert formal["lean"]["toolchain"] == "leanprover/lean4:v4.32.0"
assert (
    formal["rust_to_lean"]["principal_integration_theorem"]
    == "FormalClosureStream1.current_source_combined_capstone"
)
assert (
    formal["coverage_status"]
    == "selected_component_correspondence_not_end_to_end_acceptance"
)
assert (
    formal["tag67_work_theorem_boundary"]["kind"]
    == "exact_transcript_hash_function_call_equality"
)
assert (
    formal["tag67_work_theorem_boundary"]["statement"]
    == "forall state nonce, actualTranscriptGrindingDigest state nonce = rustHash state ((3 : Byte) :: List.ofFn (nonceLEBytes nonce))"
)

review = formal["post_release_formal_review"]
assert review["date"] == "2026-08-14"
assert review["commit"] == "598fe3389ef492e10437e28c4c013507d405eb1a"
assert review["status"] == "conditional_not_end_to_end"
assert review["review_page"] == "docs/reviews/mathematical-status-20260814.md"
assert review["theorems"] == {
    "normalized_trace_to_spend_relation": "AspisV5AcceptedSpendRelation.extracted_trace_implies_spend_relation",
    "accepted_run_schema": "AspisV5AcceptedSpendRelation.accepted_run_implies_spend_relation_or_bad_event",
    "false_accept_event_bound": "AspisV5AcceptedSpendRelation.false_accept_measure_le_bad_event",
    "wrong_secret_event_bound": "AspisV5TheftResistance.wrong_secret_measure_le_bad_events",
    "same_leaf_different_opening_event_bound": "AspisV5TheftResistance.different_opening_same_leaf_measure_le_bad_events",
}
assert [item["kind"] for item in review["remaining_boundaries"]] == [
    "accepted_tag67_to_normalized_trace_and_public_state",
    "pcs_fri_fiat_shamir_soundness_and_failure_bound",
    "deployed_poseidon2_faithfulness",
    "tag67_transcript_hash_call_equality",
    "deployed_knowledge_and_simulation_extraction",
    "fixed_target_commitment_security_and_numeric_bounds",
    "alternative_leaf_merkle_binding_and_complete_theft_game",
]

for relative, identity in formal["artifacts"].items():
    path = root / relative
    assert path.is_file(), relative
    assert path.stat().st_size == identity["bytes"], relative
    assert digest(path) == identity["sha256"], relative

for relative, identity in review["artifacts"].items():
    path = root / relative
    assert path.is_file(), relative
    assert identity["source_commit"] == review["commit"], relative
    assert path.stat().st_size == identity["bytes"], relative
    assert digest(path) == identity["sha256"], relative

print("PASS: Aspis V5 mainnet bundle files and invariants")
PY
