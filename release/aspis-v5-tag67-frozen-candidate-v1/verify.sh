#!/usr/bin/env bash
#
# Offline verifier for the Aspis V5 Tag-67 frozen-candidate bundle.
# Requires Bash, jq, and either sha256sum or shasum.

set -u

SBF_SHA="4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40"
SBF_BYTES="1258496"
CU_CEILING="1353616"
CU_HEADROOM="46384"
SOURCE_COMMIT="06788d44d30ea8cbd391899dddaf6f0acc6e4a3f"
DEVNET_GENESIS="EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG"

BUNDLE_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$BUNDLE_DIR" || { echo "FAIL: cannot enter bundle directory"; exit 1; }

fail() { echo "FAIL: $*"; exit 1; }
ok() { echo "  ok: $*"; }

command -v jq >/dev/null 2>&1 || fail "jq is required"
if command -v sha256sum >/dev/null 2>&1; then
  sha_of() { sha256sum "$1" | awk '{print $1}'; }
  sha_check() { sha256sum -c "$1"; }
elif command -v shasum >/dev/null 2>&1; then
  sha_of() { shasum -a 256 "$1" | awk '{print $1}'; }
  sha_check() { shasum -a 256 -c "$1"; }
else
  fail "neither sha256sum nor shasum is available"
fi

bytes_of() { wc -c < "$1" | tr -d ' '; }
magic_of() { head -c "$1" "$2" | od -An -tx1 | tr -d ' \n'; }

echo "Verifying Aspis V5 Tag-67 frozen-candidate bundle"

echo "[1/7] SHA256SUMS"
[ -f SHA256SUMS ] || fail "SHA256SUMS is missing"
if ! sha_check SHA256SUMS >/dev/null 2>&1; then
  sha_check SHA256SUMS
  fail "SHA256SUMS mismatch"
fi
ok "$(wc -l < SHA256SUMS | tr -d ' ') files match"

echo "[2/7] manifest objects"
[ -f manifest.json ] || fail "manifest.json is missing"
OBJECTS=0
while IFS=$'\t' read -r path want_bytes want_sha; do
  [ -n "$path" ] || continue
  [ -f "$path" ] || fail "missing manifest object: $path"
  [ "$(bytes_of "$path")" = "$want_bytes" ] || fail "byte mismatch: $path"
  [ "$(sha_of "$path")" = "$want_sha" ] || fail "sha256 mismatch: $path"
  OBJECTS=$((OBJECTS + 1))
done < <(jq -r '.objects | to_entries[] | "\(.key)\t\(.value.bytes)\t\(.value.sha256)"' manifest.json)
[ "$OBJECTS" -ge 1 ] || fail "manifest declares no objects"
ok "$OBJECTS manifest objects match"

echo "[3/7] frozen containers"
SBF="program/aspis_verifier_v5_tag67.so"
[ "$(magic_of 4 "$SBF")" = "7f454c46" ] || fail "SBF is not ELF"
[ "$(bytes_of "$SBF")" = "$SBF_BYTES" ] || fail "SBF byte length changed"
[ "$(sha_of "$SBF")" = "$SBF_SHA" ] || fail "SBF hash changed"
for proof in proof/selector-0/proof.bin proof/selector-1/proof.bin proof/selector-2/proof.bin proof/devnet/proof.bin; do
  [ -f "$proof" ] || fail "required proof is missing: $proof"
  [ "$(magic_of 8 "$proof")" = "4156354355503038" ] || fail "unexpected V5 proof magic: $proof"
done
[ -f proof/devnet/statement.json ] || fail "devnet statement is missing"
ok "SBF and four V5 proof containers match"

echo "[4/7] provenance and CU policy"
POLICY="evidence/accepted-topology-cu-policy.json"
PARITY="provenance/source-parity-attestation.json"
BUILD="provenance/build-provenance.json"
[ "$(jq -r '.sbf_sha256' "$POLICY")" = "$SBF_SHA" ] || fail "CU policy SBF mismatch"
[ "$(jq -r '.universal_accepted_input_upper_bound_cu' "$POLICY")" = "$CU_CEILING" ] || fail "CU ceiling mismatch"
[ "$(jq -r '.universal_headroom_cu' "$POLICY")" = "$CU_HEADROOM" ] || fail "CU headroom mismatch"
[ "$(jq -r '.candidate.sha256' "$PARITY")" = "$SBF_SHA" ] || fail "parity candidate mismatch"
[ "$(jq -r '.clean_publication_source_build.source_commit' "$PARITY")" = "$SOURCE_COMMIT" ] || fail "clean-source commit mismatch"
[ "$(jq -r '.clean_publication_source_build.byte_equal_to_frozen_candidate' "$PARITY")" = "true" ] || fail "clean-source parity is not green"
[ "$(jq -r '.sbf_sha256' "$BUILD")" = "$SBF_SHA" ] || fail "build provenance SBF mismatch"
[ "$(jq -r '.source_files | length' "$BUILD")" = "77" ] || fail "source identity count mismatch"
[ "$(jq -r '.toolchain_files | length' "$BUILD")" = "91" ] || fail "toolchain identity count mismatch"
ok "clean source, provenance, and $CU_CEILING-CU ceiling agree"

echo "[5/7] finalized devnet execution"
DEVNET="evidence/devnet-execution.json"
[ -f "$DEVNET" ] || fail "finalized devnet evidence is missing"
[ "$(jq -r '.artifact' "$DEVNET")" = "aspis_v5_tag67_devnet_execution" ] || fail "execution artifact mismatch"
[ "$(jq -r '.network' "$DEVNET")" = "devnet" ] || fail "execution network mismatch"
[ "$(jq -r '.genesis_hash' "$DEVNET")" = "$DEVNET_GENESIS" ] || fail "devnet genesis mismatch"
[ "$(jq -r '.readiness.ready and (.readiness.mutations_performed | not)' "$DEVNET")" = "true" ] || fail "embedded read-only readiness is not green"
[ "$(jq -r '.readiness.sbf_profile' "$DEVNET")" = "frozen-production-tag67" ] || fail "wrong SBF execution profile"
[ "$(jq -r '.sbf_sha256' "$DEVNET")" = "$SBF_SHA" ] || fail "executed SBF mismatch"
[ "$(jq -r '.proof_sha256' "$DEVNET")" = "$(sha_of proof/devnet/proof.bin)" ] || fail "executed proof mismatch"
[ "$(jq -r '.statement_sha256' "$DEVNET")" = "$(sha_of proof/devnet/statement.json)" ] || fail "executed statement mismatch"
[ "$(jq -r '.sequence_before' "$DEVNET")" = "0" ] || fail "pool did not start at sequence zero"
[ "$(jq -r '.sequence_after' "$DEVNET")" = "1" ] || fail "pool did not advance to sequence one"
[ "$(jq -r '.tag67_compute_unit_limit' "$DEVNET")" = "1400000" ] || fail "transaction CU limit mismatch"
[ "$(jq -r '.final_transaction_landed_cu < 1400000' "$DEVNET")" = "true" ] || fail "landed execution exceeded CU cap"
[ "$(jq -r '.final_transaction.compute_units_consumed == .final_transaction_landed_cu' "$DEVNET")" = "true" ] || fail "landed CU evidence is internally inconsistent"
[ "$(jq -r '.final_transaction_submitted_identically_to_simulation and .final_transaction_refetched_wire_exact and .final_transaction_refetched_message_exact and .final_transaction_program_success_log_exact' "$DEVNET")" = "true" ] || fail "signed-wire continuity check failed"
[ "$(jq -r '.post_finalize_upload_rejected and .post_finalize_second_finalize_rejected and .retained_proof_byte_for_byte_exact and .retained_proof_balance_equation.exact_balance_equation_reconciled and .retained_proof_balance_equation.proof_balance_retained_exactly and .replay_simulation_rejected and .replay_expected_nullifier_error_exact and .replay_pool_unchanged and .replay_nullifier_unchanged and .replay_proof_unchanged' "$DEVNET")" = "true" ] || fail "proof retention, poststate, or replay check failed"
[ "$(jq -r '([.upgradeable_program_before_final_simulation_continuity[], .upgradeable_program_after_finality_continuity[]] | all)' "$DEVNET")" = "true" ] || fail "deployed-program continuity check failed"
for key in program_id pool proof_account nullifier_address; do
  [ "$(jq -r --arg key "$key" '.[$key]' "$DEVNET")" = "$(jq -r --arg key "$key" '.devnet[$key]' manifest.json)" ] || fail "manifest/devnet $key mismatch"
done
[ "$(jq -r '.final_transaction.signature' "$DEVNET")" = "$(jq -r '.devnet.finalized_transaction.signature' manifest.json)" ] || fail "devnet signature mismatch"
[ "$(jq -r '.final_transaction.finalized_slot' "$DEVNET")" = "$(jq -r '.devnet.finalized_transaction.slot' manifest.json)" ] || fail "devnet slot mismatch"
[ "$(jq -r '.final_transaction_landed_cu' "$DEVNET")" = "$(jq -r '.devnet.finalized_transaction.compute_units' manifest.json)" ] || fail "devnet CU mismatch"
ok "exact frozen SBF finalized on devnet with atomic poststate and replay rejection"

echo "[6/7] leakage scan"
if grep -rIlE --exclude=verify.sh '\[( *[0-9]{1,3} *,){31,} *[0-9]{1,3} *\]' . 2>/dev/null | grep -q .; then
  fail "possible keypair byte array found"
fi
if grep -rIlE --exclude=verify.sh 'BEGIN [A-Z ]*PRIVATE KEY|-----BEGIN OPENSSH|"secretKey"|mnemonic|seed[_-]?phrase' . 2>/dev/null | grep -q .; then
  fail "possible secret-key marker found"
fi
if grep -rIlE --exclude=verify.sh '/Users/|/private/tmp|/home/[a-z]' . 2>/dev/null | grep -q .; then
  fail "local absolute path found"
fi
ok "no key material or local path leak"

echo "[7/7] complete"
echo "PASS: Aspis V5 Tag-67 frozen-candidate bundle verified offline"
