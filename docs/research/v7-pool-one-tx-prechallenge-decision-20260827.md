# V7 Pool one-terminal pre-challenge commitment decision

Date: 2026-08-27

Status: selected conservative route; production implementation and combined
CU measurement remain open.

## Decision

The one-terminal Pool proof will commit the complete pair transition as one
pre-challenge semantic trace. The exact transcript prefix is:

```text
base spend statement
canonical 1,520-byte live-transition record
full 26-column C1 root
lambda
chi
3-column helper C2 root
remaining Tag-73 challenges and proof
```

The live-transition record is public. It contains a 32-byte typed header, the
exact 800-byte locked old Pool snapshot, and the exact 688-byte candidate
`ASJA` afterstate. The relation proves that the public output pair transforms
that old snapshot into that candidate afterstate. The verifier exposes the
`ASJA` bytes only after the entire transparent proof accepts; the Pool then
atomically writes the state/history/nullifier/custody effects in the same
terminal transaction.

## Why the post-challenge staged route is rejected

The earlier candidate put sixteen late main-trace columns beside `H1/G/D` in
a seven-lane C2 commitment after `lambda, chi`. Those late values participate
in randomized copy constraints. Letting the prover select them after seeing
the copy-compression challenges is not the standard sound copy-argument
ordering, and no uniqueness theorem had removed that adaptive freedom.

The fix is structural and cheaper: stable work occupies rows `0..544` and
`864..976`; live append work occupies rows `544..864`. They are disjoint, so
both banks overlay losslessly in the same sixteen semantic columns before the
copy challenges. The existing ten selected mask-only columns and three helper
columns are unchanged.

## Exact consequences

```text
semantic columns                 16
selected mask-only C1 columns    10
total C1 columns                 26
helper C2 columns                 3
gamma width                      29
fixed QM31 claims               641
maximum proof body           30,504 bytes
allocated semantic rows         976
unused rows                      48
```

The former seven-lane candidate was 35,216 bytes. It is not the production
target and its extra 4,712 bytes are eliminated rather than optimized.

## Concurrency tradeoff

This route is sound and economical but deliberately pessimistic about
concurrency. The live root/index/frontier are fixed before the full C1 root.
If another append lands first, the completed proof is stale and the entire
proof must be regenerated. Historical membership remains independent: the
input may still spend against any retained anchor permitted by policy.

No preparation transaction authorizes or changes Pool state. Proof-account
creation/uploads are data transport only. The single terminal transaction
must verify the proof and atomically apply every economic/state effect.

## Formal evidence

`AspisFormal/Pool/V7PoolOneTxPreChallengeCommitment.lean` kernel-checks the
safe prefix order, rejects the old post-challenge order, proves the disjoint
656+320 row partition with 48 rows unused, pins the 1,520-byte public record,
and derives the unchanged 30,504-byte maximum wire. Its printed axiom union is
only the ordinary Lean foundation subset (`propext`, `Quot.sound`); there is
no `sorryAx` or project-specific axiom.

## Remaining one-transaction gates

1. Merge and mask the honest pair trace in production prover source.
2. Compile the exact pair semantic terminal/copy registry and verifier.
3. Bind the 1,520-byte record at the selected pre-C1 transcript position.
4. Run the real verifier and optimized Pool suffix in one LiteSVM transaction.
5. Measure same-page, rollover and withdrawal custody paths, plus stale/replay
   rollback.
6. Source-bridge the accepted Rust path through Aeneas and close its Lean
   acceptance/security composition.
