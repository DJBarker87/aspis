# V7 pair-forest deposit invariant/CU audit — 2026-09-01

## Status

This is a **default-off, disposable-cluster audit**, not a promotion proposal.
The feature is `pair-forest-deposit-invariant-audit`; it is absent from both
Cargo `default` and `v7-pair-forest-one-tx-candidate`. It does not modify the
verifier, TxV1, tree depth, proof format, cryptographic relation or CPI order.

Source base: `bb7c509d02c72477652c2a27c4f3ad469e95f360`

Audit implementation/SBF source: `74cc65d4f0da48ea8a49e833c0f35398195b3ec4`

Branch: `research/v7-live-pool-witness-adapter-20260901`

Promotion status: **not proposed**. CU deltas and the invariant review must be
reviewed first; production identities and release approval remain absent.

Formal closure follow-up: validated implementation commit
`4915d88114896fa2cf618451f685de777edc4679` adds the main Lean persisted-lane
reachability induction and the translated writer/byte-image induction. Its
focused source, Lean, Aeneas and Rust gates are green; see
`docs/research/v7-persisted-lane-source-formal-closure-20260901.md`. This closes
the named source/formal invariant boundary but does not enable the feature or
change the promotion status above.

## Why the second deposit hit 1.4M CU

The frozen generic deposit path validates the same depth-20 relation more than
once:

1. strict lane decode reconstructs the persisted root from the active
   frontier (20 pair-tree parent hashes for a populated lane);
2. `append_one_with_empty_roots` first validates that source again, then
   computes the successor (20 + 20 hashes for a populated lane);
3. strict successor encoding validates the newly computed root/frontier again
   (20 hashes).

At source index 0 the strict genesis shortcuts remove two of those traversals,
so the path performs 40 parent hashes and landed at 1,112,399 CU. At source
index 1 it performs all 80 and consumed the entire 1,399,850 CU available to
the Pool program before reaching the Token CPI; the transaction reported the
1,400,000 CU ceiling. This is repeated validation, not growth in transaction
bytes: the blocked index-1 wire was 617 bytes.

The earlier frozen evidence remains unchanged under
`results/v7-live-pool-witness-adapter-20260901/local-feature-active-live-stale-selected-lane-blocked/`.

## Persisted-state induction

The claim is scoped to a fixed authenticated Pool binary/program ID and the
ordinary Solana account-owner and transaction-atomicity rules. It does not
claim safety across an unauthenticated program upgrade or arbitrary genesis
injection of an already Pool-owned account.

Let `ReachableLane(x)` mean that `x` is the byte image of a canonical lane PDA
after a successful transaction admitted by that fixed Pool binary.

Base case: `AS8I` derives every lane PDA from the authenticated program ID,
master and lane number; accepts only a fresh System-owned empty account or an
exact-size rent-exempt Pool-owned zero image; constructs each lane with the
strict pair-domain genesis codec; and writes that frozen byte image. Therefore
every lane introduced by initialization is a byte-exact genesis image.

Inductive deposit step: assume the source is reachable. `AS8D` requires the
Pool owner, exact lane/master PDA and identity, canonical header/version/format
binding and digest encodings, capacity, inactive-frontier empties, and the
retained current history-page PDA/header/fill/root. It derives the occupied /
algebraically empty pair leaf from the request, computes the exact pair-domain
binary-carry successor, executes the unchanged Token CPI, and requires the
exact custody delta before copying the frozen successor bytes to the lane.
Any error rolls back account preparation, CPI and writes atomically. Thus a
success adds only the exact output of an authenticated deposit transition.

Inductive terminal step: `ASQ8` (and audit-only `ASF8`) authenticates the
master, checkpoint, selected current lane, Registry release/profile/program,
proof account and verifier return program. Only the exact ASR8-bound
afterstate is encoded and persisted; marker/page/vault changes share the same
atomic transaction. Thus a success adds only the byte-exact output of an
authenticated proof-authorized transition.

Closure: `AS8C` treats all lanes as read-only. The native dispatcher exposes no
raw pair-forest append, close or realloc instruction. The complete production
lane persistence surface in `pair_forest.rs` is one genesis copy plus the
deposit and terminal successor copies. Solana rejects writes by non-owners,
and failed transactions do not extend reachability. By induction, every
reachable persisted lane is genesis or a byte-exact authenticated-transition
output.

`pair_forest_lane_persistence_surface_remains_closed` mechanically guards the
three persistence sites. The source-level proof record is
`results/v7-pair-forest-deposit-invariant-cu-audit-20260901/persisted-state-proof.json`.

## Exact audit substitution

Only two redundant validations change when the new feature is explicitly
enabled:

- deposit lane decode treats the active root/frontier reconstruction as the
  established persisted-state invariant;
- successor encoding writes the exact output of the already checked append
  without reconstructing its root a second time.

The append still computes the successor root and frontier using the existing
pair-domain empty roots and exact depth-20 carry rule. The first attempted
implementation used the ordinary-tree empty-root domain and the byte-exact
equivalence test failed at index 0; it was discarded and replaced with the
pair-domain construction. No check was weakened to make that test pass.

Preserved checks are exact account length, magic, versions and format binding;
Pool ownership; lane/master PDA and identity; canonical digest encodings;
capacity; inactive-frontier empties; strict genesis root; exact current
history-page PDA/header/fill/root; fresh/rollover page PDA, zero-image and rent
rules; algebraic occupied/empty pair encoding; account cardinality/aliasing;
Token program/mint/vault/authority binding; and exact custody delta. The Token
CPI remains before Pool lane/history persistence.

## Focused validation and resources

The audit feature passed these focused tests:

- strict receipt and byte-image equivalence at source indices
  0, 1, 2, 3, 7, 15 and 255;
- invariant decoder boundary and authenticated encoder byte exactness;
- retained-history-root mismatch rejection before CPI with unchanged state;
- genesis/same-page deposit and page-rollover behavior;
- exactly three production lane persistence sites.

The pre-existing generic path separately passed its focused deposit and
rollover tests. The combined frozen V7 feature set plus the new opt-in feature
passed `cargo check`. The focused harness builders also passed `cargo check`.
No broad regression, verifier build, frozen CU profile or proof replay ran.

The largest local focused command used 943,734,784 bytes peak RSS and zero
swap. The one justified NUC SBF build used `MemoryHigh=8G`, `MemoryMax=12G`,
`MemorySwapMax=0`, completed in 30.89 seconds, and used 558,194,688 bytes peak
RSS. Its 536,752-byte artifact SHA-256 is
`9cd1401327493134ca42ed13a7e72d7e6c375c488f7aa2ede42b39f402b6c89d`.

## Sequential finalized CU results

The production-shaped run creates a fresh disposable eight-lane Pool, routes
256 independently generated 1,000-token deposits to lane 0, simulates each
exact signed wire, submits those identical bytes, waits for finalization, and
checks every custody delta and account hash. It reaches the page boundary by
executing all prior authenticated transitions; no state jump is used.

| Source index | Page mode | Bytes | Simulated CU | Landed CU | Generic-path comparison |
| ---: | --- | ---: | ---: | ---: | --- |
| 0 | genesis | 651 | 640,272 | 640,272 | 1,112,399; delta **−472,127 CU (−42.44%)** |
| 1 | same page | 617 | 594,743 | 594,743 | generic simulation hit 1,400,000; new path has **805,257 CU ceiling headroom** |
| 2 | same page | 617 | 594,683 | 594,683 | no reachable generic baseline |
| 3 | same page | 617 | 594,776 | 594,776 | no reachable generic baseline |
| 7 | same page | 617 | 594,730 | 594,730 | no reachable generic baseline |
| 15 | same page | 617 | 594,714 | 594,714 | no reachable generic baseline |
| 255 | rollover | 684 | 643,854 | 643,854 | no reachable generic baseline |

All 256 deposits finalized. Across populated same-page states, landed CU was
594,215–594,776. The highest value in the entire deposit run was the rollover
at 643,854 CU, leaving 756,146 CU below the 1.4M transaction ceiling. The
source token account moved from 256,000 to zero and the vault from zero to
256,000; every individual delta was exactly 1,000. Lanes 1–7 were byte-exactly
unchanged. The initialize transaction was 784 bytes and used 131,942 CU.

The run took 58 minutes 37.71 seconds. `/usr/bin/time` observed 1,480,093,696
bytes maximum resident set; the encompassing cgroup peaked at 6,742,413,312
bytes including reclaimable cache, with zero swap under `MemoryHigh=8G`,
`MemoryMax=12G` and `MemorySwapMax=0`.

The only exact frozen comparison points are index 0 (1,112,399 CU) and the
index-1 failure (the 1,400,000 transaction ceiling / 1,399,850 Pool CU). Later
generic-path deltas are intentionally not invented because the generic path
cannot land index 1 and therefore cannot reach those states.

Exact wires, signatures, finalized slots, account hashes, simulated/landed CU
and checksums are under
`results/v7-pair-forest-deposit-invariant-cu-audit-20260901/local-feature-active/`.

## Network classification

The Solana Foundation's canonical upgrade page reports transaction-v1 / larger
transactions **live on public Testnet in epoch 1025**, while Devnet and Mainnet
remain not activated. This audit did not submit to Testnet, so that activation
is a network capability fact, not V7 lifecycle evidence. The existing public
Devnet evidence and its blocked classification are unchanged.

The Foundation page still gives only a tentative Agave v4.2 rollout target for
Mainnet, not a canonical activation date. Anza's tracker, edited 2026-09-01,
still labels SIMD-0385 pending Testnet activation and requires Agave v4.2.2;
that tracker therefore lags the Foundation status page.

- Foundation: <https://solana.com/upgrades/larger-transaction-sizes>
- Anza tracker: <https://github.com/anza-xyz/agave/wiki/Feature-Gate-Tracker-Schedule>

Current classification: Testnet feature active; Devnet feature inactive;
Mainnet feature inactive; local deposit audit only; `mainnetReady: false`.

## Replay

The exact default-off replay command is recorded in
`results/v7-pair-forest-deposit-invariant-cu-audit-20260901/replay-command.txt`.
It requires both disposable-cluster acknowledgements, an Agave 4.2+ binary
directory, the hash-pinned audit SBF, prebuilt focused builders and a new
evidence directory. Temporary ledger and keys are created only under
`mktemp -d` and removed by validated cleanup traps.
