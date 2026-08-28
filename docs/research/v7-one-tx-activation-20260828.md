# V7 one-transaction eight-lane activation — 2026-08-28

## Result

The complete eight-lane Pool path is executable as one TxV1 transaction:

`Pool -> authenticated registry/release -> Tag-73 verifier CPI -> 792-byte ASR8 -> lane/history/nullifier settlement -> optional SPL withdrawal CPI`.

These are real combined LiteSVM measurements at an exact 1,400,000-CU runtime limit. They are not sums of component measurements. Simulation and execution agree in every case.

| Operation | History case | CU | CU headroom | TxV1 bytes | 4,096-byte headroom | Evidence |
|---|---:|---:|---:|---:|---:|---|
| Private transfer | Same page | 1,304,642 | 95,358 | 799 | 3,297 | `results/v7-one-tx-activation-20260828/transfer-same-page.json` |
| Private transfer | Rollover | 1,350,384 | 49,616 | 832 | 3,264 | `results/v7-one-tx-activation-20260828/transfer-rollover.json` |
| Withdrawal | Same page | 1,295,050 | 104,950 | 964 | 3,132 | `results/v7-one-tx-activation-20260828/withdrawal-same-page-counter0.json` |
| Withdrawal | Rollover | 1,360,604 | 39,396 | 997 | 3,099 | `results/v7-one-tx-activation-20260828/withdrawal-rollover-counter0.json` |

The unmined-work proof rejects after 61,309 CU. All transaction accounts remain byte-exact and return data is empty: `results/v7-one-tx-activation-20260828/unmined-proof-rollback.json`.

The accepted transitions also check that the checkpoint, proof, registry, and master accounts remain unchanged; the selected lane and nullifier marker change exactly; the correct history page changes; and withdrawal moves exactly 250 tokens from the vault to the bound destination without changing the mint.

## Frozen source and artifacts

- Base revision: `df22542fe58e536b890cfc7f81250609d5829368`
- Activation branch: `research/v7-one-tx-activate-20260828`
- Pool SBF: 524,328 bytes, SHA-256 `61f80ab33bff36b38716df944d7851a473be0ed065b2d57864082fd966ec8810`
- Verifier SBF: 1,673,288 bytes, SHA-256 `3c77bad385518fac4c7aea3695081eaaad5dfa710a09339510665b1b6c93bac6`

The build uses one explicit default-off feature on each program: `v7-pair-forest-one-tx-candidate`. Each aggregate feature selects the exact audited eight-lane optimization set. Production defaults remain unchanged until the remaining formal/source gates close.

Activation exposed and fixed a real integration defect: the Pool verifier-CPI runtime abstraction accepted only a five-account array, while the exact selected-lane invariant requires seven accounts. The abstraction now accepts a slice; the instruction still fixes and authenticates the precise account list.

## Reproduction

The SBF binaries were built on `nuc.local` under `MemoryHigh=22G`, `MemoryMax=28G`, and `MemorySwapMax=0`:

```sh
NO_DNA=1 cargo build-sbf --manifest-path programs/aspis-pool/Cargo.toml \
  --no-default-features --features v7-pair-forest-one-tx-candidate \
  --sbf-out-dir results/v7-one-tx-candidate-build/pool
NO_DNA=1 cargo build-sbf --manifest-path programs/aspis-verifier/Cargo.toml \
  --no-default-features --features v7-pair-forest-one-tx-candidate \
  --sbf-out-dir results/v7-one-tx-candidate-build/verifier
```

The measurement harness is built from this branch:

```sh
NO_DNA=1 cargo build --release \
  --manifest-path results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/Cargo.toml
```

Each evidence JSON embeds the binary hashes, proof hash, exact TxV1 message size, runtime limit, execution logs, simulation/execution equality, and account-level atomicity checks.

## Honest release boundary

This activates and measures the complete executable candidate; it does not silently declare it mainnet-ready.

- The run is deterministic local LiteSVM 0.16 evidence. It uses no RPC, signing service, devnet, or mainnet.
- The transfer fixtures execute all 35/31/34-bit work checks without a threshold bypass.
- The withdrawal fixtures are valid accepted proofs selected with q16 counter zero for measurement. Production withdrawal activation still requires closure of the correlated-grinding/final-nonce selection argument; the verifier was not weakened for this measurement.
- The history-page writer invariant and the newest semantic/pattern Rust-to-Lean/Aeneas bridges remain release gates.
- The audit profile still pins audit program/release identities. Generated deployment identities and exact registry/release binding must replace them before devnet activation.
- No transaction was signed or submitted.

The architecture is one transaction, remains transparent, and preserves the Tag-73 cryptography. The remaining work is proof/source closure and deployment binding, not another execution-model redesign.
