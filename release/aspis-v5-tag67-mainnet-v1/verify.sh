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
assert formal["release_scope"]["sbf_sha256"] == evidence["artifacts"]["sbf"]["sha256"]
assert formal["release_scope"]["tag67_signature"] == evidence["transactions"]["tag67"]["signature"]
assert formal["release_scope"]["tag67_finalized_slot"] == evidence["transactions"]["tag67"]["finalized_slot"]
assert formal["lean"]["toolchain"] == "leanprover/lean4:v4.32.0"
assert (
    formal["rust_to_lean"]["principal_integration_theorem"]
    == "FormalClosureStream1.current_source_combined_capstone"
)
assert (
    formal["remaining_implementation_boundary"]["kind"]
    == "exact_transcript_hash_function_call_equality"
)

for relative, identity in formal["artifacts"].items():
    path = root / relative
    assert path.is_file(), relative
    assert path.stat().st_size == identity["bytes"], relative
    assert digest(path) == identity["sha256"], relative

print("PASS: Aspis V5 mainnet bundle files and invariants")
PY
