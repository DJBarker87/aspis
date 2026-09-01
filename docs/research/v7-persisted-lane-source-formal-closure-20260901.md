# V7 persisted-lane source/formal closure — 2026-09-01

## Result

The default-off deposit invariant audit now has a focused persisted-state
induction in both the main mathematical model and the translated production
writer model. The closure is green at validated implementation commit
`4915d88114896fa2cf618451f685de777edc4679`.

This branch is based on integrated main commit
`fc5c5b8ddff7f3387861e3a811ec43bb0d0d7b39`. Both requested predecessors are
ancestors:

- `74cc65d4f0da48ea8a49e833c0f35398195b3ec4`: default-off deposit invariant
  source path;
- `5bd2e3e433a13f5b3243cf3762b47b34d73abad9`: sequential finalized deposit CU
  evidence.

The feature remains absent from Cargo `default` and
`v7-pair-forest-one-tx-candidate`. This is source/formal closure for an audit
feature, not a production promotion or mainnet-readiness claim.

## What is proved

`AspisFormal/Pool/V7PairForestPersistedReachability.lean` defines the only two
mathematical lane advances admitted after initialization:

1. a checked deposit carrying the exact append relation for the occupied /
   algebraically empty output pair; and
2. an authenticated terminal settlement carrying the exact Tag-73/ASR8 append
   relation.

`PersistedLaneReachable` starts only at the canonical genesis state and extends
only through those transitions. Its principal results prove:

- every reachable lane retains the full chronological frontier witness,
  sequence/index equality and root reconstruction invariant;
- every reachable lane is exactly genesis or an authenticated transition
  output from a reachable predecessor;
- accepted deposit and accepted terminal relations introduce exactly the
  corresponding reachability constructor.

The translated-source proof
`V7ForestLanePersistedReachability.lean` independently closes the hash-pinned
writer model. Every translated reachable output is either initialization or a
checked-deposit/authenticated-ASR8 result, and each mutation result has the
same 768-byte image accepted by the strict encoder. The named invariant
capability is propagated through the identical induction.

The production source audit fixes the persistence surface at exactly three
byte writes in `pair_forest.rs`: deposit successor, authenticated terminal
successor, and the eight-lane initialization loop. Checkpointing does not write
lane data. Owner/PDA/identity, canonical codec, capacity, inactive-frontier,
genesis, retained-history and feature-composition checks remain pinned.

## Exact trust boundary

The source and mathematical proofs deliberately do different jobs:

- Lean 4.32 proves the generic Merkle/frontier invariant from genesis and the
  exact append relation.
- The Lean 4.31 Aeneas project proves the translated Rust writer control flow,
  reachability classification, byte-exact strict image and fail-closed
  capability use.
- The source audit and focused Rust equivalence tests bind those models to the
  current production-shaped source and codec.

Because the projects use different pinned Lean versions, there is no dishonest
cross-version `.olean` import. The correspondence is explicit and hash-pinned.
The Aeneas writer model still treats the mathematical root/frontier fact as a
named capability; the new main theorem is the proof that discharges that
capability at the exact genesis/deposit/terminal transition boundary.

## Focused validation

All gates passed. No broad regression, SBF rebuild, CU rerun, verifier replay,
proof generation or q16/K1.3 work ran.

| Gate | Result | Wall | Peak RSS | Swap |
| --- | --- | ---: | ---: | ---: |
| production source/write inventory | PASS | 1.36 s | 7.1 MB | 0 |
| existing mathematical predecessor | PASS | 13.97 s | 6,366,408 KiB | 0 |
| new mathematical reachability target | PASS | 4.50 s | 6,447,500 KiB | 0 |
| translated Aeneas focused replay | PASS | 20.24 s | 2,573,640 KiB | 0 |
| optimized focused Rust replay | PASS | 363.23 s | 615,268 KiB | 0 |
| corrected exact source-decoder test | PASS | 2.68 s | 263,708 KiB | 0 |

The source decoder, authenticated encoder, sequential boundary equivalence,
retained-history rejection and closed persistence-surface tests each selected
and passed at least one test. The arithmetic tests used optimized release
binaries. The NUC jobs used explicit systemd scopes, hard memory limits and
`MemorySwapMax=0`.

The main reachability classification theorem is axiom-free. All other printed
main and translated theorem axiom sets are subsets of `propext`,
`Classical.choice` and `Quot.sound`. Compiled proof sources contain no `sorry`,
`admit`, `native_decide` or project-specific axiom.

## Existing finalized CU measurements

The integrated evidence was not rerun. It already contains 256 sequential,
production-shaped deposits finalized on a disposable Agave 4.2.0 cluster,
including all predecessor transitions required to reach rollover.

| Source index | Mode | Bytes | Simulated CU | Landed CU |
| ---: | --- | ---: | ---: | ---: |
| 0 | genesis | 651 | 640,272 | 640,272 |
| 1 | same page | 617 | 594,743 | 594,743 |
| 2 | same page | 617 | 594,683 | 594,683 |
| 3 | same page | 617 | 594,776 | 594,776 |
| 7 | same page | 617 | 594,730 | 594,730 |
| 15 | same page | 617 | 594,714 | 594,714 |
| 255 | page rollover | 684 | 643,854 | 643,854 |

At index 0 the exact generic baseline was 1,112,399 CU, so the audit path saves
472,127 CU (42.44%). At index 1 the generic path exhausted the 1,400,000-CU
transaction ceiling before Token CPI; the audit path uses 594,743 CU, leaving
805,257 CU of ceiling headroom. Later generic deltas remain unavailable and are
not invented.

The reduction removes only duplicate validation: source-root reconstruction
already supplied by reachable persisted state, and successor-root
reconstruction already supplied by the exact checked append. The successor is
still computed with the existing pair-domain depth-20 carry rule. Canonicality,
PDA/identity, capacity, inactive frontier, current retained history, custody
delta, page rollover and CPI ordering remain checked.

## Network and promotion classification

- Public Testnet TxV1 feature: active in epoch 1025; no V7 execution claimed.
- Public Devnet TxV1 feature: inactive; existing blocked evidence unchanged.
- Public Mainnet TxV1 feature: inactive.
- Deposit invariant audit: source/formal closure green, still default-off.
- Promotion proposed: false.
- `mainnetReady`: false.

The branch changes no verifier, TxV1 builder, cryptographic relation,
parameters, proof format, tree depth, CPI ordering, production deployment or
K1.3/q16 source. It is safe to cherry-pick as a focused proof/replay/evidence
package; enabling the audit feature requires a separate reviewed promotion.

## Evidence

Machine-readable closure evidence and replay commands are under
`results/v7-persisted-lane-source-formal-closure-20260901/`. The existing wire,
signature, slot, account-hash and CU artifacts remain under
`results/v7-pair-forest-deposit-invariant-cu-audit-20260901/` and are referenced
by checksum rather than duplicated.
