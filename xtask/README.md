# Spend commands

Run commands from the repository root with:

```text
cargo run --release -p aspis-xtask -- <command> [arguments]
```

Exact release-certificate regeneration uses `solana-cargo-build-sbf 2.3.0`,
platform-tools `v1.48`, and its bundled Rust `1.84.1`. A toolchain that emits a
different SBF fails the release's byte-identity gate.

## Current release and deployment surface

| Command | Purpose | Network effect |
|---|---|---|
| `spend-release` | Reconstruct the fail-closed q18 release certificate from source artifacts. | None |
| `spend-devnet-readiness` | Validate an exact release instance, keys, accounts, funding, and devnet genesis. | Read-only |
| `spend-devnet-execute` | Deploy and exercise the exact tag65 proof-verification and state-transition path on devnet. | Mutates devnet; explicit interlock required |
| `spend-devnet-upload-smoke` | Exercise only the proof-account upload/finalization pipeline on devnet. | Mutates devnet; explicit interlock required |
| `spend-devnet-close-smoke` | Validate tag64 recovery of a sealed proof account on devnet. | Mutates devnet; explicit interlock required |
| `spend-mainnet-readiness` | Apply the read-only mainnet policy, identity, freshness, rent, and fee checks. | Read-only |
| `spend-mainnet-execute` | Run the separately interlocked exact-instance executor with a hash-chained top-level run checkpoint journal. | Mutates mainnet; explicit interlock required |
| `spend-mainnet-cleanup` | Close the disposable ProgramData account and produce linked immutable reconciliation receipts. | Mutates mainnet; destructive acknowledgement required |

Certificates and measurement artifacts are read from and written to
`results/spend/`. The evaluator fails closed when an input artifact is
absent; fresh certificates are produced against a freshly built SBF.

The readiness commands do not inherit Solana CLI configuration. Execution
commands require explicit absolute artifact and key paths, an explicit RPC
URL, and their literal acknowledgement strings. Mainnet execution additionally
requires `ASPIS_SPEND_MAINNET_RUN_DIR`; policy inputs are documented by the
readiness report rather than supplied implicitly.

Mainnet readiness is a read-only preflight report, not an execution
attestation. Its `required_future_*` fields define the per-wire persistence,
restart reconciliation, live fee-ledger, resource-lifecycle, and cleanup-only
contract required of a future crash-recoverable executor. The current executor
does not implement or attest those controls. Its journal records only the run
start, the read-only preflight checkpoint, the finalized-success checkpoint,
and the completed outcome; it is not durable per-wire recovery. An interrupted
run therefore requires explicit operator reconciliation and cleanup rather than
a blind restart.

The current release instance is the frozen 64,447-byte proof at
`crates/aspis-prover/fixtures/spend_q18_g37_release.bin`; the first mainnet
execution was abandoned and will be re-executed against a freshly built SBF
using this exact proof.

## Removed research tooling

The commands above are the complete surface. The historical `stage0-*`,
`stage1-*`, and `stage2-*` measurement, KAT, and migration commands were
removed from the working tree; they are preserved at the git tags
`research-archive-2026-07-14` and `research-archive-2026-07-15` and in git
history. Historical experiments removed from the default branch are indexed by
[`archive/README.md`](../archive/README.md).
