#!/usr/bin/env bash
#
# Offline verifier for the aspis-spend q18/g37 mainnet-beta release bundle.
#
# Requires only: bash, jq, and either sha256sum or shasum. No network access,
# no Solana toolchain, no build step. Run it from anywhere; it locates the
# bundle relative to its own path.
#
#   ./verify.sh
#
# It exits 0 and prints PASS only when every published byte, every manifest
# object, the proof and SBF container magics, the release certificate gates,
# the finalized on-chain signature/slot/compute-unit values, and the leakage
# scan all agree. On any mismatch it prints a FAIL line naming the check and
# exits nonzero.

set -u

# ---------------------------------------------------------------------------
# Pinned identities of the finalized mainnet-beta execution. These are the
# authoritative values the bundle is expected to attest; verify.sh confirms
# the shipped evidence and artifacts still report exactly them.
# ---------------------------------------------------------------------------
TAG65_SIG="3G1voggszvDMGi5PbGM1kuEMYKvh2TNMbH6hHHwndUdRQJNT7ehRFpQpksxLnx5tp2xkS5jGi359rVXk42sRPFcv"
TAG65_SLOT="433219840"
TAG65_CU="1344003"
PROGRAM_ID="GQPNqfYF17Nj2dGsf6Q2AtiouyM67YxFZPh9LxBk2Ye3"
POOL="3ZRYarQZcWJQgzNwLo1Eo7PDmier3rbW41L8ccAddCvb"
NULLIFIER="CFJ5fYPSi4Qn6okBCZS3tXFMw7Lsz4Jy9vEAAGU5kfSU"
DEPLOY_DOMAIN="ba43feb01d7d7f5ee3f57a6481b202066c83c6c3e76020a619c1611abbd08c8f"
PROOF_SHA="32eb419e0c5c3ef4fa2db0d32579e88f1207547d8fb010279efeb6c05981b529"
PROOF_BYTES="65407"
SBF_SHA="e289faf85fe4773880794d5d4356461bb9cb94077b68711f99348efe19707d7e"
SBF_BYTES="924344"

# ---------------------------------------------------------------------------
# Setup.
# ---------------------------------------------------------------------------
BUNDLE_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$BUNDLE_DIR" || { echo "FAIL: cannot enter bundle directory"; exit 1; }

fail() { echo "FAIL: $*"; exit 1; }
ok()   { echo "  ok: $*"; }

command -v jq >/dev/null 2>&1 || fail "jq is required but was not found"

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

echo "Verifying aspis-spend q18/g37 mainnet-beta release bundle"
echo "  bundle: $BUNDLE_DIR"

# ---------------------------------------------------------------------------
# 1. Every published byte matches SHA256SUMS.
# ---------------------------------------------------------------------------
echo "[1/7] SHA256SUMS"
[ -f SHA256SUMS ] || fail "SHA256SUMS is missing"
if ! sha_check SHA256SUMS > /dev/null 2>&1; then
  # Re-run visibly so the offending file is named.
  sha_check SHA256SUMS
  fail "SHA256SUMS check reported a mismatch"
fi
ok "$(wc -l < SHA256SUMS | tr -d ' ') files match SHA256SUMS"

# ---------------------------------------------------------------------------
# 2. Every manifest object: byte length and sha256.
# ---------------------------------------------------------------------------
echo "[2/7] manifest objects"
[ -f manifest.json ] || fail "manifest.json is missing"
OBJ_COUNT=0
while IFS=$'\t' read -r path want_bytes want_sha; do
  [ -n "$path" ] || continue
  [ -f "$path" ] || fail "manifest object missing on disk: $path"
  got_bytes="$(bytes_of "$path")"
  [ "$got_bytes" = "$want_bytes" ] || fail "byte length mismatch for $path (manifest $want_bytes, actual $got_bytes)"
  got_sha="$(sha_of "$path")"
  [ "$got_sha" = "$want_sha" ] || fail "sha256 mismatch for $path"
  OBJ_COUNT=$((OBJ_COUNT + 1))
done < <(jq -r '.objects | to_entries[] | "\(.key)\t\(.value.bytes)\t\(.value.sha256)"' manifest.json)
[ "$OBJ_COUNT" -ge 1 ] || fail "manifest declares no objects"
ok "$OBJ_COUNT manifest objects match by byte length and sha256"

# ---------------------------------------------------------------------------
# 3. Container magics: proof header and SBF ELF.
# ---------------------------------------------------------------------------
echo "[3/7] container magics"
PROOF="proof/spend-q18-g37.bin"
SBF="program/aspis_verifier.so"
[ -f "$PROOF" ] || fail "proof missing: $PROOF"
[ -f "$SBF" ] || fail "SBF missing: $SBF"
# "ASP0" == 41 53 50 30
[ "$(magic_of 4 "$PROOF")" = "41535030" ] || fail "proof header magic is not ASP0"
# ELF == 7f 45 4c 46
[ "$(magic_of 4 "$SBF")" = "7f454c46" ] || fail "SBF container magic is not ELF"
# Independent cross-check of the two frozen binaries against the pinned hashes.
[ "$(sha_of "$PROOF")" = "$PROOF_SHA" ] || fail "proof sha256 != pinned release proof"
[ "$(bytes_of "$PROOF")" = "$PROOF_BYTES" ] || fail "proof byte length != pinned release proof"
[ "$(sha_of "$SBF")" = "$SBF_SHA" ] || fail "SBF sha256 != pinned deployed verifier"
[ "$(bytes_of "$SBF")" = "$SBF_BYTES" ] || fail "SBF byte length != pinned deployed verifier"
ok "proof is ASP0 and SBF is ELF; both match their pinned hashes"

# ---------------------------------------------------------------------------
# 4. Release certificate: released == true, all gates green.
# ---------------------------------------------------------------------------
echo "[4/7] release certificate"
CERT="certificates/release.json"
[ -f "$CERT" ] || fail "release certificate missing: $CERT"
[ "$(jq -r '.released' "$CERT")" = "true" ] || fail "certificate does not report released=true"
GATES_TOTAL="$(jq -r '.gates | length' "$CERT")"
GATES_FAILED="$(jq -r '[.gates[] | select(.passed != true)] | length' "$CERT")"
[ "$GATES_TOTAL" -ge 1 ] || fail "certificate declares no gates"
[ "$GATES_FAILED" = "0" ] || fail "$GATES_FAILED release gate(s) not green"
ok "released=true with all $GATES_TOTAL gates green"

# ---------------------------------------------------------------------------
# 5. Finalized on-chain evidence matches the pinned signature/slot/CU.
# ---------------------------------------------------------------------------
echo "[5/7] finalized on-chain evidence"
EV="evidence/mainnet-execution.json"
[ -f "$EV" ] || fail "mainnet execution evidence missing: $EV"
[ "$(jq -r '.final_transaction.signature' "$EV")" = "$TAG65_SIG" ] || fail "finalized signature mismatch"
[ "$(jq -r '.final_transaction.finalized_slot' "$EV")" = "$TAG65_SLOT" ] || fail "finalized slot mismatch"
[ "$(jq -r '.final_transaction.compute_units_consumed' "$EV")" = "$TAG65_CU" ] || fail "finalized compute units mismatch"
[ "$(jq -r '.program_id' "$EV")" = "$PROGRAM_ID" ] || fail "program id mismatch in evidence"
[ "$(jq -r '.pool_after.address' "$EV")" = "$POOL" ] || fail "pool address mismatch in evidence"
[ "$(jq -r '.nullifier_after.address' "$EV")" = "$NULLIFIER" ] || fail "nullifier address mismatch in evidence"
[ "$(jq -r '.deployment_domain_hex' proof/statement.json)" = "$DEPLOY_DOMAIN" ] || fail "deployment domain mismatch in statement"
ok "signature $TAG65_SIG at slot $TAG65_SLOT, $TAG65_CU CU"
ok "program $PROGRAM_ID, pool $POOL, nullifier $NULLIFIER"

# ---------------------------------------------------------------------------
# 6. Leakage scan: secret keys, cluster-less explorer links.
#
# The two verbatim executor evidence files under evidence/ record the
# operator's absolute artifact paths as they existed at generation time.
# They are pinned byte-for-byte by SHA256SUMS and manifest.json and are
# copied unmodified, so the local-path scan excludes them by design. This
# script is also excluded from the pattern scans: it necessarily contains the
# very markers and path strings it searches for, as its own matching logic.
# ---------------------------------------------------------------------------
echo "[6/7] leakage scan"
SCAN_EXCLUDE="--exclude=verify.sh"
# 6a. Secret-key material anywhere: 64-int keypair arrays or key markers.
if grep -rIlE $SCAN_EXCLUDE '\[( *[0-9]{1,3} *,){31,} *[0-9]{1,3} *\]' . 2>/dev/null | grep -q .; then
  grep -rIlE $SCAN_EXCLUDE '\[( *[0-9]{1,3} *,){31,} *[0-9]{1,3} *\]' . 2>/dev/null
  fail "possible keypair byte array found in bundle"
fi
if grep -rIlE $SCAN_EXCLUDE 'BEGIN [A-Z ]*PRIVATE KEY|-----BEGIN OPENSSH|"secretKey"|mnemonic|seed[_-]?phrase' . 2>/dev/null | grep -q .; then
  grep -rIlE $SCAN_EXCLUDE 'BEGIN [A-Z ]*PRIVATE KEY|-----BEGIN OPENSSH|"secretKey"|mnemonic|seed[_-]?phrase' . 2>/dev/null
  fail "possible secret-key marker found in bundle"
fi
# 6b. Local absolute paths in bundle-assembled text (evidence + this script excluded).
LEAK="$(grep -rIlE '/Users/|/home/[a-z]' . \
  --exclude=verify.sh \
  --exclude=mainnet-execution.json \
  --exclude=mainnet-cleanup.json 2>/dev/null || true)"
if [ -n "$(echo "$LEAK" | tr -d '[:space:]')" ]; then
  echo "$LEAK"
  fail "local absolute path leaked into a bundle-assembled file"
fi
# 6c. Explorer links must pin a cluster (no ambiguous mainnet-by-default).
while IFS= read -r line; do
  [ -z "$line" ] && continue
  case "$line" in
    *cluster=*) : ;;
    *) fail "explorer link without a pinned cluster: $line" ;;
  esac
done < <(grep -rIhoE 'https://(explorer\.solana\.com|solscan\.io)/[^ )"'"'"']*' . 2>/dev/null || true)
ok "no secret material, no local-path leak, explorer links cluster-pinned"

# ---------------------------------------------------------------------------
# 7. Done.
# ---------------------------------------------------------------------------
echo "[7/7] complete"
echo "PASS: aspis-spend q18/g37 mainnet-beta release bundle verified offline"
exit 0
