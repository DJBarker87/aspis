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
| `spend-measure` | Measure the production tag59/tag65 compute and run the production acceptance/mutation KATs against a local validator, writing the release-certificate measurement inputs. | Local test validator only |
| `spend-release` | Reconstruct the fail-closed q18 release certificate from source artifacts. | None |
| `spend-bundle` | Deterministically assemble the offline-verifiable q18/g37 mainnet release bundle from the finalized source artifacts. | None |
| `spend-devnet-readiness` | Validate an exact release instance, keys, accounts, funding, and devnet genesis. | Read-only |
| `spend-devnet-execute` | Deploy and exercise the exact tag65 proof-verification and state-transition path on devnet. | Mutates devnet; explicit interlock required |
| `spend-devnet-upload-smoke` | Exercise only the proof-account upload/finalization pipeline on devnet. | Mutates devnet; explicit interlock required |
| `spend-devnet-close-smoke` | Validate tag64 recovery of a sealed proof account on devnet. | Mutates devnet; explicit interlock required |
| `spend-mainnet-readiness` | Apply the read-only mainnet policy, identity, freshness, rent, and fee checks. | Read-only |
| `spend-mainnet-execute` | Run the separately interlocked exact-instance executor with a hash-chained top-level run checkpoint journal. | Mutates mainnet; explicit interlock required |
| `spend-mainnet-cleanup` | Close the disposable ProgramData account and produce linked immutable reconciliation receipts. | Mutates mainnet; destructive acknowledgement required |
| `v5-devnet-build` | Build the isolated V5 Tag-67 SBF and its provenance record. | None |
| `v5-devnet-artifact` | Generate a V5 proof and strict statement sidecar for devnet. | None |
| `v5-devnet-readiness` | Validate the V5 SBF, provenance, proof, statement, keys, accounts, funding, and devnet genesis. | Read-only |
| `v5-devnet-execute` | Deploy and exercise the exact retained-proof Tag-67 atomic path on devnet. | Mutates devnet; explicit interlock required |
| `v5-mainnet-artifact` | Generate a V5 proof and strict statement sidecar bound to the canonical mainnet program identity. | None |
| `v5-mainnet-readiness` | Validate the mainnet genesis, runtime identity, frozen SBF and provenance, proof, statement, keys, accounts, and funding. | Read-only |
| `v5-mainnet-execute` | Run the one-shot Tag-67 mainnet executor with signed-wire persistence and a hash-chained recovery journal. | Mutates mainnet; explicit interlock required |

Certificates and measurement artifacts are read from and written to
`results/spend/`. The evaluator fails closed when an input artifact is
absent; fresh certificates are produced against a freshly built SBF.

The readiness commands do not inherit Solana CLI configuration. Execution
commands require explicit absolute artifact and key paths, an explicit RPC
URL, and their literal acknowledgement strings. Mainnet execution additionally
requires `ASPIS_SPEND_MAINNET_RUN_DIR`; policy inputs are documented by the
readiness report rather than supplied implicitly.

Mainnet readiness is a read-only preflight report, not an execution
attestation. For q18/g37, the `required_future_*` fields describe controls that
the original `spend-mainnet-execute` path does not implement; its top-level
journal records checkpoints rather than every signed wire. The dedicated V5
executor uses a fresh one-shot run directory, persists every signed wire before
submission, and records submission and finalization in a hash-chained journal.
It never resumes an incomplete run automatically, so an interruption requires
explicit operator reconciliation.

The finalized q18/g37 release uses the 65,407-byte proof at
`crates/aspis-prover/fixtures/spend_q18_g37_release.bin`. Its Tag-65 mainnet
transaction finalized at slot `433219840`, consuming 1,344,003 CU. The frozen
V5 release uses a 1,258,496-byte SBF with SHA-256
`4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40`.
That binary finalized the retained-proof Tag-67 path on devnet at slot
`478299357`, consuming 1,335,952 CU. The current Agave 4.1.0 accepted-state
ceiling is 1,356,912 CU.

## Removed research tooling

The table above covers the current release and deployment commands. The
historical `stage0-*`, `stage1-*`, and `stage2-*` measurement, KAT, and
migration commands were removed from the working tree; they are preserved at
the git tags `research-archive-2026-07-14` and
`research-archive-2026-07-15` and in git history. Historical experiments
removed from the default branch are indexed by
[`archive/README.md`](../archive/README.md).
