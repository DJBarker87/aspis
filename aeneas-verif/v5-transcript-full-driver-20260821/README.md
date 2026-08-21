# Complete V5 transcript join

This bundle composes the three independently checked production transcript
segments in one Lean theorem:

1. the generated successful prefix call sequence and all six generated helper
   bodies;
2. the unchanged generated four-round relation replay, including exact byte
   windows, fold nonces, roots, salts, and call order; and
3. the unchanged generated final polynomial, work check, selector, and query
   tail.

The principal results are:

- `AspisV5TranscriptFullDriverJoin.generated_full_trace_eq_complete`;
- `AspisV5TranscriptFullDriverJoin.generated_projected_driver_eq_source`;
- `AspisV5TranscriptFullDriverJoin.generated_full_tail_return_is_exact`.

The relation portion uses
`AspisV5TranscriptRelationFinalJoin.ExactRelationParsedProjection` directly.
It does not introduce another parser proposition.  The unchanged
`parse_probe_data` extraction proves that same proposition for a successful
generated parser result.

The prefix theorem still accepts
`PinnedOuterSuccessfulPathBoundary`.  This join does not prove that boundary
by itself.  It is discharged only when this result is connected to the full
accepted-entry extraction, which proves that the production caller makes the
recorded successful prefix calls in that order.

## Cross-bundle import normalization

The independent Aeneas snapshots each contain their own namespaced copy of
Solana's `ProgramError`.  Aeneas's `discriminant` attribute nevertheless asks
Lean to generate the same process-global instance name for each copy.  Lean
therefore rejects a direct three-way import before checking the join.

The two patches in `import-normalization/` remove only that unused attribute
from temporary copies of the relation and tail generated `Types.lean` files.
The raw generated snapshots in the repository remain byte-for-byte unchanged.
After this one-line import normalization, the complete join compiles in one
Lean 4.32 environment.

The checked endpoint reports only Lean's standard foundations:

```text
propext
Classical.choice
Quot.sound
```

It contains no unfinished proof placeholder, custom axiom, compiled-evaluation
shortcut, or unchecked declaration.

## What this theorem does and does not say

The theorem establishes the complete accepted transcript call order and the
exact bytes supplied by the extracted helpers at the maintained projection
boundary.  It also records the exact generated tail return shape.

It does not turn SHA-256 or Poseidon2 security, field arithmetic, the compiler,
or the Solana runtime into Lean theorems.  Those remain separately named
cryptographic and toolchain assumptions.
