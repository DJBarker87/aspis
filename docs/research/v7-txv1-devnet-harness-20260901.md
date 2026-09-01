# V7 TxV1 4-KiB devnet lifecycle harness — 2026-09-01

## Result

**BLOCKED BY FEATURE/IDENTITY/ARTIFACT.** Public devnet is the canonical
devnet cluster and its RPC is new enough to report Agave `4.3.0-beta.2`, but
the authoritative TxV1 feature account
`txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL` was absent at finalized
commitment during this audit. No public transaction was built, signed,
simulated, submitted, or deployed.

The new command is
`scripts/v7_txv1_devnet_lifecycle_harness.sh`. Its configuration and identity
allowlist are in `config/v7-txv1-devnet-harness-20260901.json`. The captured
read-only public result is under
`results/v7-txv1-devnet-harness-20260901/public-devnet-probe-r2/`.

The result remains explicitly `mainnetReady: false`. The configured Pool,
Registry, verifier, Registry entry, profile, release, and policy identities are
the audit-only RC1 identities. The public path never accepts that identity set.

## Branch inspection and baseline

The worktree branch was created from registry release-audit HEAD
`64ec7148885695f801f857e5f1a4bd95f17af6b4`. Remote refs were refreshed before
implementation. The relevant non-proof development is:

- `research/v7-registry-v2-release-audit-20260831` at `64ec7148`: frozen
  Registry V2 SBF identities, public feature gate, deterministic Agave bundle,
  and signed/finalized local 11-case runner;
- `research/v7-wallet-runtime-handoff-20260831` at `174ce6ac`: finalized TxV1
  wallet ingestion and the signed `ASC8` ciphertext carrier;
- `research/v7-registry-v2-caller-source-20260831` and
  `research/v7-one-tx-activate-20260828`: no later harness/client work not
  already represented by the two heads above.

The two named heads were merged. Their only substantive merge conflict was in
wallet transaction plumbing. That exposed an actual compatibility defect: the
ciphertext-carrier proof-account locator accepted the earlier 9/10 and 14/15
terminal account layouts, while immutable Registry V2 terminals use 11/12 and
16/17 accounts. The locator and focused tests now use the immutable layouts.
No verifier mathematics, Lean/Aeneas proof, cryptographic relation, SBF/CU
optimization, or production program source was changed.

## HARNESS TESTED LOCALLY

Focused wallet transaction tests passed:

```text
CARGO_BUILD_JOBS=2 CARGO_NET_OFFLINE=true /usr/bin/time -lp \
  cargo test --locked \
  --manifest-path crates/aspis-pool-wallet-v1/Cargo.toml \
  --features eight-lane-plumbing-v2 --lib lane_forest_transaction_v1

8 passed; 0 failed; 177 filtered out
wall 60.26 s; maximum RSS 843,186,176 bytes; swaps 0
```

This proves the merged builder retains the exact immutable Registry V2
terminal shapes, keeps every carrier transaction below the 3,500-byte review
threshold, binds both required signatures to the exact two-instruction
`ASC8 -> ASQ8` message, and rejects carrier mutation or instruction reordering.
It is not a finalized cluster lifecycle result.

The earlier registry release audit contains a real disposable Agave 4.2
signed/simulated/submitted/finalized 11-case subset. The new
`run-disposable` mode wraps that runner only after an exact disposable-test
acknowledgement. It preserves the earlier evidence label as a subset and emits
`finalizedComplete: false`, because those cases use genesis-loaded fixture
accounts rather than observing proof upload and Pool init/deposit.

## PUBLIC DEVNET FEATURE ACTIVE

False as observed on 2026-09-01. The captured probe recorded:

| Field | Value |
|---|---|
| RPC | `https://api.devnet.solana.com` |
| Genesis hash | `EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG` |
| RPC core | `4.3.0-beta.2` |
| Feature set | `2409014235` |
| Feature account | absent at finalized commitment |
| Mutation/signing/submission | none |

The feature account, not the RPC version string, is authoritative. The harness
requires canonical activated feature data owned by the Feature program and
records the activation slot when present. An absent, pending, malformed, or
wrongly owned account fails closed.

## FINALIZED DEVNET LIFECYCLE COMPLETE

False. No component measurement or simulation is reported as a combined
finalized lifecycle. The frozen measured reference remains 1,201,757 CU and a
997-byte terminal transaction; it was neither rerun nor modified here.

Before any public execution, the harness checks the genesis hash, feature
state, program account existence, executable flags, loaders, local frozen
binary hashes, remotely dumped binary hashes, and exact Registry/entry account
data hashes. Public execution also requires a non-audit, production-approved
identity manifest. The current checked-in manifest intentionally cannot pass
that gate.

For an admitted execution, the evidence schema reserves exact transaction
bytes and wire hash, CU, signature, slot, logs, before/after account hashes,
per-invariant results, toolchain versions, cluster/feature identifiers, and
program/binary identities. The existing disposable subset already enforces
simulation of the signed wire followed by byte-identical submission and
finalized confirmation.

## BLOCKED BY FEATURE/IDENTITY/ARTIFACT

Three independent blockers remain:

1. Public devnet has not activated the TxV1 4-KiB feature at finalized
   commitment.
2. Only audit-only Pool/Registry/policy identities exist. They are rejected on
   the public path and accepted only by the exact disposable-test
   acknowledgement.
3. The complete lifecycle artifact set is incomplete. The frozen proof account
   address is a fixture public key without an available disposable signing key,
   so its exact proof cannot be created/uploaded on a non-genesis cluster.
   Frozen cases are also missing deposit/init, two different lanes, wrong
   historical checkpoint, malformed request, and malformed ciphertext-carrier
   non-stalling fixtures.

Until all three clear, the honest status is neither “PUBLIC DEVNET FEATURE
ACTIVE” nor “FINALIZED DEVNET LIFECYCLE COMPLETE.”

## Commands

Read-only public probe:

```sh
scripts/v7_txv1_devnet_lifecycle_harness.sh probe \
  https://api.devnet.solana.com \
  EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG \
  /absolute/new-evidence-directory
```

Default-off disposable subset (audit identities and ephemeral local funds
only):

```sh
scripts/v7_txv1_devnet_lifecycle_harness.sh run-disposable \
  /absolute/agave-4.2+-bin \
  /absolute/materialized-bundle \
  /absolute/new-evidence-directory \
  I_ACKNOWLEDGE_AUDIT_ONLY_IDENTITIES_AND_DISPOSABLE_FUNDS
```

Any transaction at or above 4,096 bytes is rejected. The disposable runner
also rejects a transaction at or above 3,500 bytes unless
`ASPIS_TXV1_RESEARCH_OVER_3500` is set to the exact value
`I_ACKNOWLEDGE_RESEARCH_TX_OVER_3500_BYTES`.
