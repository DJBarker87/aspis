# Profile 23 artifact guide

This guide describes the frozen q18/g37 Profile 23 release and its finalized
Solana devnet rehearsal from 2026-07-14. It uses only commands that exist in
this repository or standard read-only shell/RPC commands.

## Scope

The released instruction path consumes a finalized, pre-uploaded proof
account, verifies the complete proof, and atomically advances the pool state
and creates the nullifier marker. “One transaction” refers only to that tag-60
verification-and-mutation transaction. The rehearsal first used 109 setup
transactions: pool creation and initialization, proof-account creation and
initialization, 104 proof uploads, and proof finalization.

The release certificate records 35/35 passing gates, q18 queries, batch
grinding g37, a conservative authorizing soundness floor above 100 bits, and
the declared-model hiding bounds. The certificate is the source for the exact
claim values; this guide is an index and reproduction procedure.

Local and devnet compute measurements are separate:

- the frozen local release maximum is 1,314,386 CU, leaving 85,614 CU below
  the 1,400,000-CU limit; and
- the finalized devnet tag-60 transaction consumed 1,314,332 CU in both the
  signed simulation and the landed transaction.

## Frozen byte identities

<!-- markdownlint-disable MD013 -->

| object | path or location | bytes | SHA-256 |
| --- | --- | ---: | --- |
| release certificate | `release/profile23-q18-g37/certificates/release.json` | 20,073 | `b02eae619f685449a84095243f5d07be78f91ca7df67b435fb2c12aef8f39fcf` |
| released proof | `release/profile23-q18-g37/proof/profile23-q18-g37.bin` | 66,367 | `f4e1e81f4a35b6b23f18430598ff98ec1f0db1146fabb4efd3c6715bcc847b53` |
| public statement sidecar | `release/profile23-q18-g37/proof/statement.json` | 667 | `976e9a7e001382025eaf81cfcb28ac609db966d4a9912511f54e2b702077b6de` |
| default SBF | `release/profile23-q18-g37/program/aspis_verifier.so` | 915,656 | `da66a51b1f3ce95e907a87fca15fb9dc0cce66fd47646875ce2dff94879fd254` |
| finalized devnet evidence | `release/profile23-q18-g37/evidence/devnet-finalized.raw.json` | 61,342 | `360e38fc5db3b644586c29e7a872203e8f9507c9ddef52add776fefb5d300275` |
| manuscript PDF | `release/profile23-q18-g37/paper/profile23.pdf` | 588,517 | `c42433cfbfe7cca618a0d240187665ac610cb78f5dcb172e5e5f2634e1fd1abf` |
| finalized proof-account data | devnet account below | 66,407 | `b808f322a16110acb9c88e6f67ecefede33c795e070a369e100bc371d4129f6d` |

<!-- markdownlint-enable MD013 -->

Path fields inside the frozen JSON records preserve the original release and
devnet execution environment. The bundle locations in the table above are the
authoritative checkout paths; `verify.sh` checks their identities without
following the recorded provenance paths.

The statement sidecar binds pool bytes
`504c9d4be70ef96a37d9aff3d9fd1b5080726efd6596c54a12817fd2e2d9c67a`,
sequence 0, and canonical public-input digest
`21d73e39be93112f986f52c7d683f2ab478890360a306af81110852ffb16a30a`.

## Finalized devnet record

<!-- markdownlint-disable MD013 -->

| field | value |
| --- | --- |
| RPC | `https://api.devnet.solana.com` |
| genesis hash | `EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG` |
| program | `7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue` |
| ProgramData | `cdRqe7MGCEJ2Z6iZfWuXtuymRiAhXtyfDgT47sKZr69` |
| pool | `6QTNhChQjQpzL32gdtzR9RBdjZUSR3bQhNS3eTkgM6Fj` |
| sealed proof account | `HTSueSgUJxDbzjjtbeYJcLUzFajb2U3w1SNN25SWiknh` |
| nullifier PDA | `AbWC9vKT7mxRNLeCnFrfi9HFsncF73XfG9TnbJS2jXHy` |
| final signature | `3ofPbzRkqMEJZCM9vwKz96rLqRFtSg4d1GyqqVBEbogtwzmJodsWb2f7V4X83BLvuPXFsT6Yyf87PC1ZbLf1R7bx` |
| finalized slot | 476231605 |
| simulated/landed CU | 1,314,332 / 1,314,332 |
| pool sequence | 0 to 1 |

<!-- markdownlint-enable MD013 -->

The transaction is available in the
[Solana explorer](https://explorer.solana.com/tx/3ofPbzRkqMEJZCM9vwKz96rLqRFtSg4d1GyqqVBEbogtwzmJodsWb2f7V4X83BLvuPXFsT6Yyf87PC1ZbLf1R7bx?cluster=devnet).
The evidence records rejection of post-finalization upload, repeated
finalization, and duplicate spend simulation. It also records unchanged
Program and ProgramData account images from the immediately-before-simulation
checkpoint through finality. The deployment remained upgradeable under the
recorded rehearsal authority.

## Fast frozen-object check

Run from the repository root:

```bash
./release/profile23-q18-g37/verify.sh
```

The verifier checks SHA-256 identities, byte counts, proof framing, every
release gate, devnet transition evidence, and cross-bindings among the proof,
statement, program, certificates, and finalized execution record.

## Completed evidence file

The full executor output is committed unchanged in the frozen release bundle.
Check its principal execution claims with:

```bash
EVIDENCE=release/profile23-q18-g37/evidence/devnet-finalized.raw.json

test "$(wc -c < "$EVIDENCE" | tr -d ' ')" = 61342
shasum -a 256 "$EVIDENCE"

jq -e '
  .network == "devnet" and
  .genesis_hash == "EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG" and
  .program_id == "7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue" and
  .release_certificate_sha256 == "b02eae619f685449a84095243f5d07be78f91ca7df67b435fb2c12aef8f39fcf" and
  .proof_account_finalized and
  .post_finalize_upload_rejected and
  .post_finalize_second_finalize_rejected and
  .duplicate_simulation_rejected and
  .final_transaction_submitted_identically_to_simulation and
  .sequence_before == 0 and .sequence_after == 1 and
  .final_transaction.signature == "3ofPbzRkqMEJZCM9vwKz96rLqRFtSg4d1GyqqVBEbogtwzmJodsWb2f7V4X83BLvuPXFsT6Yyf87PC1ZbLf1R7bx" and
  .final_transaction.finalized_slot == 476231605 and
  .final_transaction.compute_units_consumed == 1314332 and
  .final_transaction_simulation_cu == 1314332 and
  (.upgradeable_program_before_final_simulation_continuity | all(.[]; . == true)) and
  (.upgradeable_program_after_finality_continuity | all(.[]; . == true))
' "$EVIDENCE" >/dev/null
```

## Fetch and extract the sealed proof from devnet

The proof account contains a 40-byte application header followed by the
66,367-byte proof. Header bytes 0--3 are `ASPU`, bytes 4--7 contain the
little-endian proof length, and bytes 8--39 are the upload authority. The
authority is all zero after tag-62 finalization.

The following read-only procedure fetches the account at finalized commitment,
checks its owner and framing, and extracts the proof:

```bash
RPC=https://api.devnet.solana.com
PROGRAM=7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue
PROOF_ACCOUNT=HTSueSgUJxDbzjjtbeYJcLUzFajb2U3w1SNN25SWiknh
FETCH_DIR=artifact-output/profile23-q18-g37-chain-fetch
ACCOUNT_JSON="$FETCH_DIR/proof-account.json"
ACCOUNT_BIN="$FETCH_DIR/proof-account.bin"
FETCHED_PROOF="$FETCH_DIR/profile23-devnet-proof.bin"

mkdir -p "$FETCH_DIR"
jq -n --arg account "$PROOF_ACCOUNT" '
  {
    jsonrpc: "2.0",
    id: 1,
    method: "getAccountInfo",
    params: [$account, {encoding: "base64", commitment: "finalized"}]
  }
' | curl -sS --retry 3 \
  -H 'Content-Type: application/json' \
  --data-binary @- "$RPC" > "$ACCOUNT_JSON"

jq -e --arg program "$PROGRAM" '
  .error == null and
  .result.value != null and
  .result.value.owner == $program and
  (.result.value.executable | not) and
  .result.value.data[1] == "base64"
' "$ACCOUNT_JSON" >/dev/null

jq -r '.result.value.data[0]' "$ACCOUNT_JSON" \
  | openssl base64 -d -A > "$ACCOUNT_BIN"

test "$(wc -c < "$ACCOUNT_BIN" | tr -d ' ')" = 66407
test "$(xxd -p -l 8 "$ACCOUNT_BIN" | tr -d '\n')" = 415350553f030100
cmp -s \
  <(dd if="$ACCOUNT_BIN" bs=1 skip=8 count=32 2>/dev/null) \
  <(dd if=/dev/zero bs=1 count=32 2>/dev/null)
test "$(shasum -a 256 "$ACCOUNT_BIN" | awk '{print $1}')" \
  = b808f322a16110acb9c88e6f67ecefede33c795e070a369e100bc371d4129f6d

dd if="$ACCOUNT_BIN" of="$FETCHED_PROOF" \
  bs=1 skip=40 count=66367 2>/dev/null
test "$(wc -c < "$FETCHED_PROOF" | tr -d ' ')" = 66367
test "$(shasum -a 256 "$FETCHED_PROOF" | awk '{print $1}')" \
  = f4e1e81f4a35b6b23f18430598ff98ec1f0db1146fabb4efd3c6715bcc847b53
```

This recovers the proof bytes only. The 667-byte public statement sidecar and
the complete devnet evidence JSON are supplied by the frozen bundle. Compare
the recovered bytes with `cmp -s
release/profile23-q18-g37/proof/profile23-q18-g37.bin "$FETCHED_PROOF"`.

## Repository checks

The following commands are implemented and exercised by the repository:

```bash
NO_DNA=1 cargo fmt --all -- --check
NO_DNA=1 cargo check -q -p aspis-xtask
NO_DNA=1 cargo test -q -p aspis-xtask profile23_devnet

NO_DNA=1 cargo run -q -p aspis-prover \
  --example profile23_soundness_epro_ledger -- --calculation-only

NO_DNA=1 cargo run --release -q -p aspis-prover \
  --example profile23_complete_good_product

NO_DNA=1 cargo test --release -q -p aspis-prover --lib \
  state_only_good23::tests::frozen_profile23_fixture_runs_exact_good23_on_all_selectors \
  -- --ignored --nocapture
```

The complete local acceptance/mutation replay uses the exact proof and
statement sidecar through the supported environment overrides:

```bash
PROOF=release/profile23-q18-g37/proof/profile23-q18-g37.bin
STATEMENT=release/profile23-q18-g37/proof/statement.json

ASPIS_PROFILE23_PROOF="$PWD/$PROOF" \
ASPIS_PROFILE23_STATEMENT="$PWD/$STATEMENT" \
NO_DNA=1 cargo run --release -p aspis-xtask -- \
  stage2-atomic-profile23-acceptance

ASPIS_PROFILE23_PROOF="$PWD/$PROOF" \
ASPIS_PROFILE23_STATEMENT="$PWD/$STATEMENT" \
NO_DNA=1 cargo run --release -p aspis-xtask -- \
  stage2-atomic-profile23-mutation

NO_DNA=1 cargo run --release -p aspis-xtask -- \
  stage2-profile23-one-transaction-release
```

These three commands rewrite result JSON, and the release command removes and
rebuilds the default SBF. Run them in a disposable copy after preserving the
frozen objects. A regenerated release certificate has a new generation
timestamp, so semantic gate/source equality is the regeneration criterion;
the devnet evidence remains bound to the frozen `b02e...9fcf` certificate
bytes.

The standalone default SBF build used by the release command is:

```bash
NO_DNA=1 cargo-build-sbf \
  --manifest-path programs/aspis-verifier/Cargo.toml
```

## Fresh-proof experiment

The repository also contains the real q18/g37 production-path miner. A fresh
run uses new entropy and a new durable nonce ledger, so it tests the procedure
rather than reproducing the frozen proof hash:

```bash
RUN_ID=$(date -u +%Y%m%dT%H%M%SZ)
FRESH_PROOF="artifact-output/profile23-fresh-$RUN_ID.bin"
FRESH_LEDGER="artifact-output/profile23-fresh-$RUN_ID-nonce-ledger"

ASPIS_PROFILE23_POOL_HEX=504c9d4be70ef96a37d9aff3d9fd1b5080726efd6596c54a12817fd2e2d9c67a \
ASPIS_PROFILE23_SEQUENCE=0 \
ASPIS_PROFILE23_FIXTURE_SEED=0 \
NO_DNA=1 cargo run --release -p aspis-prover -- \
  --example profile23_production_miner -- \
  "$FRESH_PROOF" "$FRESH_LEDGER" 480
```

At the fixed 480-second release boundary this command publishes exactly one
`Proof` or `Abort`. It never emits a partial proof. A successful run also
creates the matching `.statement.json` sidecar. Repeated devnet rehearsals
must use a fresh public `ASPIS_PROFILE23_FIXTURE_SEED` so that the sample
witness derives a new nullifier; seed zero is the frozen release fixture.

## Expected broad costs

<!-- markdownlint-disable MD013 -->

| operation | expected scale |
| --- | --- |
| frozen hashes and `jq` predicates | seconds; negligible compared with a Rust build |
| soundness calculation and focused xtask tests | seconds to about a minute on a warm development machine |
| complete-Good products and all-selector replay | tens of seconds to several minutes, CPU dependent |
| acceptance/mutation/release replay | several minutes plus first-build cost; uses local validator/SBF tooling and rewrites generated results |
| fresh q18/g37 proof | 480-second public boundary plus compilation and follow-up verification; allow roughly ten minutes on the recorded class of machine |
| frozen devnet lifecycle | 109 setup transactions, including 104 sequential uploads; the recorded upload interval was 24 minutes 44 seconds |
| current devnet uploader | 70 uploads in five 16-transaction finality windows; the recorded public-RPC timing projects roughly 80--120 seconds for upload |

<!-- markdownlint-enable MD013 -->

Build cache, host CPU, Metal availability, RPC throttling, and network finality
affect wall time. Proof length, frozen hashes, release gates, and landed CU are
not inferred from those timings.

## Interpretation of the bundle

A review bundle is complete for this frozen run only when it includes the
release certificate, proof, statement sidecar, default SBF, and the completed
devnet evidence file with the hashes above. The chain fetch independently
recovers the sealed proof payload and current account data. The evidence file
adds the setup transaction ledger, exact signed-message and wire hashes,
pre/post account-image hashes, continuity checks, and rejected-operation
results that are not encoded in the proof payload itself.
