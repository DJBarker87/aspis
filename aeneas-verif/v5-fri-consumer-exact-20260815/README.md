# Exact production V5 FRI consumer proof

This package contains the Lean translation of the unchanged production
`check_v5_fri_queries` Rust function and proofs about the query-opening reads
performed by that translation. Unlike the older diagnostic trace package, no
temporary rewrite of the production `while` loop is used here.

The extraction is pinned to:

- source commit `f0bf37b216e426878623ba6ddec2127e9f6f4748`;
- source tree `a0f99ac9591fb568b6fce9fda5ef4dd7ac32e5f0`;
- `programs/aspis-verifier/src/v5_fri_checks.rs` blob
  `3b1f37f2504aa2b309cad82605c88cab11afcb85`;
- extracted LLBC SHA-256
  `a4688d49da6868234f3631c77f1ace49df3811a3dacfca85df76cc1be371abaf`.

The checked Lean files have these SHA-256 identities:

| File | SHA-256 |
|---|---|
| `TypesExternal.lean` | `ce5dd8d1a02924721a8102696e7b5ad94db22d7ed2b2cf61e501155bf1ca163c` |
| `Types.lean` | `c121162321fc5f7bfc00bb58f18b342d182529dca03eb4534157fcaf085cd58e` |
| `FunsExternal.lean` | `a412449bf88bcb439c5cc8c5d32220c1984a7d454e3c86bb5b08e88e046e3b3f` |
| `Funs.lean` | `370be7ac485d08bef17844e240b3d759f639cb078c91b2880c6e2747d21b3745` |

`Funs.lean` includes only the narrow compatibility expansion required for
the mutable enumerated slice iterator and two translated shift literals.
`FunsExternal.lean` replaces the relevant generated standard-library
placeholders with their transparent definitions. The production verifier
source is unchanged.

## What is proved

The proof currently establishes directly about the generated production
definitions:

- the unchanged monotone parent-opening scan reaches the requested sorted
  entry and returns the byte slice at that exact ordinal;
- an enumerated slice iterator returns the current ordinal and value and
  advances both positions together;
- each of the four generated loop bodies, whenever it continues, has made
  the exact opening reads selected by its source arguments;
- an active loop body cannot return successful completion without finishing
  its iterator;
- accepted execution visits every query in the first pass, both middle
  passes, and the final pass;
- the generated outer loop invokes the three later passes exactly in order;
- top-level acceptance reaches those loops through the actual generated shape
  checks, query count, inverse derivation, alpha powers, and initial iterator;
  and
- every query position in all four passes has an exact witness for the Rust
  opening calls made at that position.

The main declarations are:

- `production_monotone_loop_hits`;
- `production_opening_value_for_monotone_index_hits`;
- `production_layerZero_body_cont_reads`;
- `production_later_body_cont_reads`;
- `production_terminal_body_cont_reads`;
- `production_layerZero_active_body_ne_accepting_done`;
- `production_layerZero_accepted_loop_head`; and
- `production_layerZero_accepted_loop_reads_target`;
- `production_later_completed_loop_reads_target`;
- `production_terminal_completed_loop_reads_target`; and
- `unchanged_source_acceptance_yields_complete_fri_execution`.

The proof contains no `sorry`, `admit`, `native_decide`, or unsafe proof
shortcut.

## Maintained observation connection

`V5FriConsumerObservationBridge.lean` supplies the explicit adapter required
by `OpeningAndFriObservation.friReads`. The field is proof instrumentation,
not a value returned by Rust. The adapter therefore emits an observation only
with a proof that the exact generated top-level function accepted, and records
the four source-shaped query loops over the returned opening views.

The bridge proves:

- `accepted_resolver_read_trace_equality`: the concrete adapter satisfies the
  maintained `CheckV5FriQueriesSuccessfulReadTraceEquality` statement;
- `accepted_resolver_has_complete_source_execution`: every emitted
  observation has the complete exact-source execution proof above; and
- `opening_parser_and_accepted_resolver_imply_consumer_equality`: together
  with the separately maintained parser-output equality, the adapter proves
  the combined parser-and-FRI consumer equality.

There is no longer an independent assumption that the four Rust FRI loops
read the maintained schedule. The remaining source input to this composition
is the parser-output theorem connecting the returned Rust opening views and
index arrays to the authenticated run.

## Opaque called operations

The generated translation treats several called operations as opaque:
shape validation and column counts, inverse derivation and the supplied
inverse callback, fixed-array mapping for alpha powers, circle-to-line
normalisation, line and terminal transition checks, field decoding and
arithmetic, prepared multiplication, and fixed proof-system constants. These
operations determine whether a run accepts and are covered elsewhere by the
mathematical and arithmetic proofs. This package proves a conditional source
statement: whenever the exact generated top-level function accepts, none of
those calls can change which source indices were already passed to the opening
accessors.

## Replay

Use Lean 4.32 and the Lean library built from the matching patched Aeneas:

```sh
LEAN432_BIN=/path/to/lean-4.32.0/bin/lean \
AENEAS_LEAN_LIB=/path/to/aeneas/backends/lean/.lake/build/lib/lean \
./aeneas-verif/v5-fri-consumer-exact-20260815/replay-lean432.sh
```

The replay checks all recorded source and generated-file identities and then
compiles the generated definitions, the complete accepted-execution proof,
and the maintained observation bridge. It does not regenerate the LLBC; that
requires the pinned Charon/Aeneas extraction environment.
