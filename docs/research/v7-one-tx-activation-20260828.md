# V7 one-transaction eight-lane activation — 2026-08-28

## Result

The complete eight-lane Pool path is executable as one TxV1 transaction:

`Pool -> authenticated registry/release -> Tag-73 verifier CPI -> 792-byte ASR8 -> lane/history/nullifier settlement -> optional SPL withdrawal CPI`.

These are real combined LiteSVM measurements at an exact 1,400,000-CU runtime limit. They are not sums of component measurements. Simulation and execution agree in every case.

| Operation | History case | CU | Headroom to 1.3M | TxV1 bytes | 4,096-byte headroom | Evidence |
|---|---:|---:|---:|---:|---:|---|
| Private transfer | Same page | 1,145,890 | 154,110 | 799 | 3,297 | `results/v7-one-tx-sparsity-current-20260828/transfer-same-page.json` |
| Private transfer | Rollover | 1,191,463 | 108,537 | 832 | 3,264 | `results/v7-one-tx-sparsity-current-20260828/transfer-rollover.json` |
| Withdrawal | Same page | 1,136,135 | 163,865 | 964 | 3,132 | `results/v7-one-tx-sparsity-current-20260828/withdrawal-same-page-counter0.json` |
| Withdrawal | Rollover | 1,201,718 | 98,282 | 997 | 3,099 | `results/v7-one-tx-sparsity-current-20260828/withdrawal-rollover-counter0.json` |

The unmined-work proof rejects after 61,309 CU. All transaction accounts remain byte-exact and return data is empty: `results/v7-one-tx-sparsity-current-20260828/unmined-proof-rollback.json`.

The selected verifier saves 158,752--158,889 CU per complete transaction. It preserves the same expressions while exploiting the frozen basis and support: 14 Copy patterns, seven active masks, tensorized endpoint and digest selectors, grouped tag/finish dot products, packed range residuals, and four-slot gamma loop interchange. The worst case is 1,718 CU above the preferred 1.2M target and 98,282 CU below the hard 1.3M gate.

### Post-lock q16 source-refinement check

The Aeneas q16 caller bridge requires the source-shaped helper/control-flow
refactor now present at commit `2d32d47e`. Because that production Rust edit
landed after the four-case CU lock, it was not accepted on semantic inspection
alone. The verifier was rebuilt and the single worst release-relevant shape was
remeasured against the unchanged frozen Pool binary and exact proof fixture:

| Shape | Previous CU | Refactored CU | Delta | Headroom to 1.3M | TxV1 bytes |
|---|---:|---:|---:|---:|---:|
| Withdrawal, rollover, 255 populated pairs | 1,201,718 | 1,201,757 | +39 | 98,243 | 997 |

This is a real combined LiteSVM execution, not a component sum. The evidence is
`results/v7-q16-source-refactor-cu-check-20260828/withdrawal-rollover-counter0.json`.
The rebuilt verifier is 1,703,976 bytes with SHA-256
`125bba2ebe121d1bda87ba90943904ed866ba02502fc011f7156246ebb871a77`.
The build completed on `nuc.local` in 30.98 seconds with 550,488 KiB maximum
RSS, zero swap and exit status zero. The 39-CU movement is immaterial, so the
source-refinement refactor is retained and the hard sub-1.3M runtime gate
remains locked. No broad regression replay was performed for this decision.

The accepted transitions also check that the checkpoint, proof, registry, and master accounts remain unchanged; the selected lane and nullifier marker change exactly; the correct history page changes; and withdrawal moves exactly 250 tokens from the vault to the bound destination without changing the mint.

## Frozen source and artifacts

- Base revision: `df22542fe58e536b890cfc7f81250609d5829368`
- Activation branch: `research/v7-one-tx-activate-20260828`
- Pool SBF: 524,328 bytes, SHA-256 `61f80ab33bff36b38716df944d7851a473be0ed065b2d57864082fd966ec8810`
- Verifier SBF: 1,703,624 bytes, SHA-256 `fc830df85f25d4bae02138cf82a31273eda8e46b56fbfa51c00959ba26c968db`

The build uses one explicit default-off feature on each program: `v7-pair-forest-one-tx-candidate`. Each aggregate feature selects the exact audited eight-lane optimization set. Production defaults remain unchanged until the remaining formal/source gates close.

Activation exposed and fixed a real integration defect: the Pool verifier-CPI runtime abstraction accepted only a five-account array, while the exact selected-lane invariant requires seven accounts. The abstraction now accepts a slice; the instruction still fixes and authenticates the precise account list.

## Reproduction

The selected SBF binaries were rebuilt independently on `nuc.local` under `MemoryHigh=4G`, `MemoryMax=6G`, and `MemorySwapMax=0`:

```sh
NO_DNA=1 cargo build-sbf --manifest-path programs/aspis-pool/Cargo.toml \
  --no-default-features --features v7-pair-forest-one-tx-candidate \
  --sbf-out-dir results/v7-one-tx-sparsity-build/pool
NO_DNA=1 cargo build-sbf --manifest-path programs/aspis-verifier/Cargo.toml \
  --no-default-features --features v7-pair-forest-one-tx-candidate \
  --sbf-out-dir results/v7-one-tx-sparsity-build/verifier
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
