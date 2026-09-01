# V7 TxV1 4-KiB devnet lifecycle harness — 2026-09-01

## Result

The disposable feature-active cluster and genuine Tag-73 proof-account upload
are reproducible and finalized. The combined terminal lifecycle matrix remains
**BLOCKED BY FEATURE/IDENTITY/ARTIFACT**. No terminal transaction was executed
in this phase, and setup simulation or proof upload is not classified as a
combined lifecycle.

| Classification | Established |
|---|---:|
| PUBLIC DEVNET FEATURE INACTIVE | yes |
| DISPOSABLE FEATURE-ACTIVE CLUSTER READY | yes |
| LOCAL FINALIZED LIFECYCLE COMPLETE | no |
| PUBLIC FINALIZED DEVNET LIFECYCLE COMPLETE | no |
| MAINNET READY | no |

Public-devnet probe evidence under
`results/v7-txv1-devnet-harness-20260901/public-devnet-probe-r2/` is unchanged.
The frozen reference remains 1,201,757 CU, 997 serialized bytes, one terminal
transaction, and eight lanes; it was not rerun or modified.

## Branch inspection

The isolated branch includes the wallet handoff at `174ce6ac`, Registry V2
release audit at `64ec7148`, and later relevant remote branch work already
represented in base `a2db2237`. Inspection covered the TxV1 builder, immutable
Registry V2 terminal account shapes, proof lifecycle tags 0/1/62/64, Pool
init/deposit interfaces, eight-lane state and checkpoint types, ciphertext
carrier, frozen binaries, and earlier finalized local/public-probe evidence.
No verifier mathematics, cryptographic parameters, Lean/Aeneas files,
production Pool/verifier source, or frozen SBF/CU implementation changed.

The repository's GitHub `Spend integration` workflow (workflow ID
`313976600`) was manually disabled after failed-run email spam was reported.
This changed GitHub workflow state only; its YAML and all other workflows were
left intact.

## HARNESS TESTED LOCALLY

`scripts/v7_txv1_disposable_feature_cluster.sh` creates only a validated
`mktemp -d` ledger, installs strict cleanup traps, binds loopback RPC, requires
the exact disposable audit-identity acknowledgement, checks Agave 4.2+, and
fails unless the precise TxV1 feature account is active. It records genesis,
runtime feature set, feature data, loaders, executable accounts, and freshly
dumped program hashes. It never accepts an existing ledger.

The successful run used:

- Agave `solana-cli 4.2.0 (src:ac82b5d4; feat:21b0d33a, client:Agave)`;
- runtime feature set `565236538`;
- genesis `biNtLxt3kJREjFStDxVZje9xRvp78MKx3QLFHJVrWuB`;
- feature `txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL`, active at slot 0;
- audit Pool/Registry/verifier hashes `0e94c98d…cd4f6`,
  `0f14c7b…8f11b`, and `97df1293…cc6d`.

The ledger and disposable payer were destroyed by the wrapper's trap.

## Genuine proof and finalized upload

`tools/v7-txv1-honest-proof` calls
`build_v7_pool_pair_forest_private_transfer_onefold_proof_production`. It
generated a mined, cryptographically valid Tag-73 proof without verifier
bypass, copied verifier result, or trusted ASR8 account. The fixture-only
entropy feature is explicitly recorded; this is not represented as a
production wallet entropy path.

| Artifact | Measurement |
|---|---:|
| ASQ8 | 320 bytes, SHA-256 `73246bcf…e03f47` |
| ASF8 | 1,880 bytes, SHA-256 `f6bcd494…05c331` |
| statement digest | `caf7a432…b89bf9` |
| proof body | 30,504 bytes, SHA-256 `cba819e2…4ce43` |
| ASJA + proof payload | 31,192 bytes, SHA-256 `e4ab4c43…b8c13b` |
| prover | 94.808 s; 197,345,280-byte maximum RSS; zero swaps |

The fresh account `HcSnx3qkc7ZJr3NmzVj4vdZ8LtMVuq1U3bn11RG54Cc8`
was created through the System program, initialized normally, filled by 33
ordered 960-byte verifier upload instructions, and sealed normally. The 35
signed legacy setup transactions were each simulated and then submitted using
the byte-identical base64 wire. All finalized without error in slots 151–185.

| Setup measurement | Value |
|---|---:|
| signed transactions | 35 (1 create/init, 33 upload, 1 finalize) |
| serialized transaction bytes | 204 minimum, 1,173 maximum |
| simulation CU | 210,601 sum; 591 minimum; 188,131 maximum |
| landed CU | 210,601 sum; 591 minimum; 188,131 maximum |
| landed proof-account SHA-256 | `57f7a916…ce41f0` |

Exact signed bytes, wire hashes, signatures, simulation responses, finalized
slots/logs/CU, and the finalized account image are under
`results/v7-txv1-devnet-harness-20260901/local-feature-active/proof-upload/`.
The temporary signing key existed only in task-owned mode-0600 directories and
was destroyed locally and on the NUC after evidence capture. No private key was
printed or committed.

## PUBLIC DEVNET FEATURE INACTIVE

True as observed on 2026-09-01. At finalized commitment, canonical devnet
genesis was `EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG`, RPC core reported
`4.3.0-beta.2`, and the authoritative feature account was absent. No public
transaction was built, signed, simulated, submitted, or deployed. The feature
account—not an RPC version string—is the activation authority.

## Why the terminal matrix is still blocked

The smallest missing honest integration is a live eight-lane witness adapter.
There is no executable path that takes a freshly initialized/deposited Pool,
its finalized checkpoint/history/lane accounts, and a wallet note opening and
constructs `PoolV1PairForestInputNoteWitnessV1` plus the exact Tag-73
ASQ8/ASF8 terminal statement. The available mined helper constructs a
deterministic synthetic tree, checkpoint, witness, and fixture entropy. Its
valid proof cannot authenticate a separately initialized live Pool snapshot.

Completing that adapter also requires production attempt entropy plumbing and
a withdrawal-side live witness adapter. Without those pieces, substituting
genesis-loaded state, mutating the fixture after proving, or pre-authorizing an
ASR8 would manufacture a green result. None was done.

Consequently none of the newly requested terminal cases—init/deposit through
proof close/refund—was marked complete in this phase. Their exact blocked
statuses and non-applicable invariant values are in
`local-feature-active/evidence.json`. The older frozen 11-case local subset
remains separately valid evidence but was not rerun and does not close this
live-fixture gap.

## Replay commands

Disposable feature gate (default-off because it requires the acknowledgement):

```sh
scripts/v7_txv1_disposable_feature_cluster.sh \
  /absolute/agave-4.2+-bin \
  /absolute/new-evidence-directory \
  I_ACKNOWLEDGE_AUDIT_ONLY_IDENTITIES_AND_DISPOSABLE_FUNDS
```

Generate a fresh proof after creating an uncommitted keypair and retaining
only its public key in logs:

```sh
NO_DNA=1 CARGO_BUILD_JOBS=2 cargo run --release --locked \
  --manifest-path tools/v7-txv1-honest-proof/Cargo.toml -- \
  <fresh-proof-account-pubkey> <new-proof-output-directory>
```

Run the normal proof-account upload inside the wrapper:

```sh
scripts/v7_txv1_disposable_feature_cluster.sh \
  /absolute/agave-4.2+-bin /absolute/new-run-evidence \
  I_ACKNOWLEDGE_AUDIT_ONLY_IDENTITIES_AND_DISPOSABLE_FUNDS -- \
  scripts/v7_txv1_upload_honest_proof_child.sh \
  /absolute/uncommitted-proof-keypair.json \
  /absolute/proof-payload.bin \
  /absolute/new-run-evidence/proof-upload
```

The successful NUC invocation ran in a user systemd scope with
`MemoryHigh=8G`, `MemoryMax=12G`, and `MemorySwapMax=0`; the service reported
zero swap. No SBF build or broad regression suite was run.

Verify the evidence bundle:

```sh
cd results/v7-txv1-devnet-harness-20260901/local-feature-active
shasum -a 256 -c SHA256SUMS
jq -e '.classifications.disposableFeatureActiveClusterReady and
  (.classifications.localFinalizedLifecycleComplete | not) and
  (.mainnetReady | not)' evidence.json
```

Public execution remains fail-closed on feature and production identity
checks. Audit-only identities are never selected for public devnet or mainnet.
