# Pool V1 prepared-settlement runtime checkpoint (2026-08-27)

## Historical-anchor/current-append concurrency result

The stronger populated-tree fixture now separates the two root roles across
three history pages:

- the verified proof binds retained membership root sequence 100 on page zero;
- 410 intervening appends advance the live Pool to sequence 510 on page one;
- authenticated preparation reads that live append source and prepares the
  exact two-output transition; and
- atomic settlement writes sequence 511 to page one and sequence 512 to a new
  page two.

| Step | Compute units | Transaction bytes |
|---|---:|---:|
| `ASPP` authenticated preparation | 1,256,357 | 997 |
| `ASPF` atomic settlement | 643,108 | 765 |
| consumed-plan replay rejection | 488,106 | n/a |

The old membership root is therefore fixed before expensive proving, while
the append root/index is selected from live state only when `ASPP` executes.
Deposits and spends that land during proving do not stale the proof while its
retained anchor remains available. The prepared plan then binds the exact
current Pool/page images: if another append wins after `ASPP` but before
`ASPF`, `ASPF` rejects and the authority can cancel/refund the stale plan.
Account locks serialize each instruction, but do not remove this intentionally
short preparation-to-settlement race window.

Preparation leaves the historical page, current page, next page, and Pool
byte-exact. Settlement preserves the historical page, advances the live Pool,
creates a nullifier marker that retains the sequence-100 membership anchor,
applies both chronological roots, and closes/refunds both plan accounts.
Replay is rejected without changing Pool, any page, or the marker. Simulation
and execution metadata are byte-identical, and both successful transactions
fit the current 1,232-byte serialized transaction ceiling.

The replayable evidence is
`results/pool-v1-prepared-runtime-litesvm-20260827/evidence-historical-anchor-rollover.json`.
The clean-worktree profiled SBF is 415,784 bytes with SHA-256
`5f590a11bcf4c5006afcb4caa2a6a9cf6d81091df8296002be53b3e18e0a2605`.
It is a focused build, not yet the two-independent-build release certificate.

## Earlier same-page rollover result

The worst non-custody private-transfer page shape now fits the present Solana
transaction limits in deterministic LiteSVM execution.  The fixture starts at
root sequence 254, prepares two ordered outputs across the page-zero/page-one
boundary, then atomically settles to sequence 256.

| Step | Compute units | Transaction bytes |
|---|---:|---:|
| `ASPP` authenticated preparation | 1,212,764 | 964 |
| `ASPF` atomic settlement | 628,107 | 765 |
| consumed-plan replay rejection | 480,602 | n/a |

The preparation leaves the live Pool and both history pages byte-exact.  Final
settlement writes both chronological roots, advances the Pool tree from 254 to
256, creates the exact nullifier marker, closes/refunds both authenticated plan
accounts, and emits the 200-byte `ASTR` receipt.  Replaying the consumed plan is
rejected with Pool/history/marker state unchanged.  Simulation and execution
metadata are byte-identical, and both successful transactions fit the current
1,232-byte serialized transaction ceiling.

The earlier replayable evidence is
`results/pool-v1-prepared-runtime-litesvm-20260827/evidence-rollover-final.json`.
The profiled SBF is 415,784 bytes with SHA-256
`5f590a11bcf4c5006afcb4caa2a6a9cf6d81091df8296002be53b3e18e0a2605`.
It is a current-worktree profile, not the later clean-source reproducible
release artifact.

## Cryptography-preserving CU changes

No Poseidon permutation, Merkle-tree definition, statement, root, receipt,
history order, nullifier rule, or atomic settlement rule changed.

- Sequence zero is checked against the one exact pinned recursive empty-tree
  image instead of recomputing the same 20 empty parents.
- Append reconstruction starts at the carry level.  Cleared lower levels are
  already the pinned recursive empty root, so one append now evaluates exactly
  depth parent hashes independently of the cursor's trailing-one count.
- `ASPP` parses the exact Pool-owned canonical PDA under the Pool program's
  inductive state-write invariant instead of recomputing the already-persisted
  root before computing the two new roots.
- Sealed fresh-account and page-validation results are reused only across code
  with no intervening CPI.  A newly created account still receives one full
  post-CPI owner/shape/zero/rent check.
- The internal canonical plan encoder carries its exact PDA seed fields to the
  persistence step.  The program no longer SHA-hashes and decodes the just-
  encoded 10,000-byte core and optional 8,504-byte shard in the same call.
  Final settlement still fully authenticates untrusted persisted plan bytes.

## Explicit remaining proof boundary

The optimized `ASPP` source loader deliberately omits one runtime check for a
non-genesis Pool: recomputing the active frontier/root relation.  It remains
strict on owner, canonical PDA, account shape, every format byte, canonical
field encodings, cursor metadata, inactive frontier slots, and the unique
genesis image.  The omitted relation must be closed before release by the
Rust-to-Lean/Aeneas global invariant:

1. Pool initialization writes the exact valid genesis tree.
2. Every successful instruction capable of writing the Pool state receives a
   valid tree and writes exactly the checked append result.
3. No other program can modify the Pool-owned PDA under the Solana runtime
   boundary.

The focused Rust equivalence test checks the invariant-carried append against
the fully validated reference across 260 consecutive cursors and carry
boundaries.  The complete prepared-settlement test group is green: 20 passed,
0 failed.  This is implementation evidence; the inductive Lean/Aeneas theorem,
clean reproducible SBF build, full verifier-connected lifecycle, and finalized
devnet run remain release gates.
