# V7 pair-forest withdrawal rollover CU margin

This checkpoint is deterministic local LiteSVM/Apple-Metal evidence for the
real Pool -> selected Tag-73 verifier -> SPL Token -> settlement path. It uses
true Solana TxV1 messages, the strict three-stage work verifier, the exact
792-byte ASR8 result, and the counter-zero honest fixtures described in
`COUNTER0-WITHDRAWAL-EVIDENCE.md`.

Counter-zero final-nonce selection remains measurement-only until the separate
K1.6 audit establishes that its conditioning on the later public q16 schedule
is inside the quantified adversarial grinding model. None of the CU changes in
this file changes that schedule, the first-cap-203 verifier rule, proof bytes,
or work checks.

## Exact results

| configuration | same-page CU | rollover CU | rollover headroom | verifier CPI rollover |
|---|---:|---:|---:|---:|
| selected verifier, strict history page | 1,367,025 | 1,395,583 | 4,417 | 1,260,740 |
| Pool history invariant | 1,319,969 | 1,385,553 | 14,447 | 1,260,740 |
| + semantic common factors | - | 1,379,831 | 20,169 | 1,255,018 |
| + Copy-pattern window CSE | **1,295,086** | **1,360,640** | **39,360** | **1,235,827** |

The final same-page transaction also accepts unchanged under an exact
1,300,000-CU runtime limit, leaving 4,914 CU. The release ceiling measurement
retains 1,400,000 CU for both shapes.

Exact transaction/proof sizes remain:

| operation | TxV1 bytes | proof bytes | headroom to 4,096 bytes |
|---|---:|---:|---:|
| withdrawal, same page | 964 | 30,824 | 3,132 |
| withdrawal, rollover | 997 | 30,772 | 3,099 |

Both successful executions preserve the authenticated master/checkpoint/
registry/proof accounts, apply the exact verifier afterstate, create the exact
nullifier marker, mutate only the selected history shape, and execute SPL
`TransferChecked` with vault `10,000 -> 9,750` and destination `17 -> 267`.
Simulation and execution metadata are identical.

## Attribution

The history-page reader saves 47,056 CU on a partially filled same page and
10,030 CU on rollover. It retains the exact page header and exact current-root
binding but does not rescan prior persisted roots or untouched zero capacity.
It is gated by `pair-forest-history-page-invariant-audit`; production selection
requires the fresh-page/only-writers Rust-to-Lean/Aeneas invariant bridge.

The two verifier rewrites are ordinary field identities:

- `v7-pair-forest-semantic-factor-audit` extracts shared selectors in the
  absorption, path, and occupancy residuals. It saves 5,722 CU on rollover.
- `v7-pair-forest-pattern-window-audit` evaluates four frozen eight-limb Copy
  tuple windows once and derives exact subwindows by subtraction. It saves a
  further 19,191 CU on rollover.

Together they save 24,913 verifier CU on rollover and 24,883 verifier CU on
same-page withdrawal. They change no wire byte, transcript operation,
cryptographic relation, theta lane, proof size, ASR8 byte, or state transition.

Focused teeth passed:

- 128 random off-domain schedule/path/occupancy comparisons against the
  literal kernels;
- 256 random off-domain generated Copy-pattern comparisons against the
  literal fourteen-pattern evaluator;
- the complete compiled Copy lane against the typed host reference;
- honest private-transfer and withdrawal terminal vanishing on all 1,024
  Boolean rows.

The attempted 32-byte-wide fresh-page zero scan was rejected: it measured
exactly 0 CU improvement and is not retained in source.

## Frozen SBF artifacts

| artifact | bytes | SHA-256 |
|---|---:|---|
| semantic-factor verifier | 1,899,480 | `083e4e09b09c6c718e1cc6b3dd113c082b9c6a5de4b6ce5f0bf1eb7ae0975006` |
| final history-invariant Pool | 526,656 | `f3ae8d96164189bec2e134b659e4fc5bd39a6b16488cde1bbd23f278a9369c76` |
| final semantic + pattern-factor verifier | 1,938,536 | `b5ee420e63aafd35d3b60a1577d740ef84be005a2bd6bee05da4ab7f485e3d87` |

SBF builds ran on the dedicated Linux build host under `MemoryHigh=4G`, `MemoryMax=6G`, and
`MemorySwapMax=0`. No devnet, signing, deployment, or push was performed.

## Exact evidence

- `evidence/withdrawal-same-page-counter0-history-invariant-txv1-1400000.json`
- `evidence/withdrawal-rollover-counter0-history-invariant-txv1-1400000.json`
- `evidence/withdrawal-rollover-counter0-history-semantic-factor-txv1-1400000.json`
- `evidence/withdrawal-same-page-counter0-final-txv1-1300000.json`
- `evidence/withdrawal-rollover-counter0-final-txv1-1400000.json`
