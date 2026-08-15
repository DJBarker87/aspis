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

## What is proved in this checkpoint

The proof currently establishes directly about the generated production
definitions:

- the unchanged monotone parent-opening scan reaches the requested sorted
  entry and returns the byte slice at that exact ordinal;
- an enumerated slice iterator returns the current ordinal and value and
  advances both positions together;
- each of the four generated loop bodies, whenever it continues, has made
  the exact opening reads selected by its source arguments;
- an active first-layer body cannot return successful completion;
- an accepted first-layer loop must therefore continue through every active
  iterator entry; and
- every requested position from the current cursor through an arbitrary
  in-bounds target is actually visited and read by that accepted production
  loop.

The main declarations are:

- `production_monotone_loop_hits`;
- `production_opening_value_for_monotone_index_hits`;
- `production_layerZero_body_cont_reads`;
- `production_later_body_cont_reads`;
- `production_terminal_body_cont_reads`;
- `production_layerZero_active_body_ne_accepting_done`;
- `production_layerZero_accepted_loop_head`; and
- `production_layerZero_accepted_loop_reads_target`.

The proof contains no `sorry`, `admit`, `native_decide`, or unsafe proof
shortcut.

## Remaining work for the direct accepted-run theorem

This checkpoint does not claim the complete production-consumer connection.
The following source proof remains:

1. repeat the accepted-loop argument for the two intermediate passes and the
   final pass;
2. prove that the generated outer loop invokes those three passes in order;
3. connect the generated top-level preparation steps to the first loop,
   including shape validation, query count, inverse derivation, alpha powers,
   and the initial iterator; and
4. connect the resulting concrete read lists to the maintained
   `OpeningAndFriObservation.friReads` observation through an explicit
   execution adapter. That field is proof instrumentation, not a value
   returned by the Rust function, so it cannot be inferred for an arbitrary
   observation without such an adapter.

The generated translation still treats several called operations as opaque:
shape validation and column counts, inverse derivation and the supplied
inverse callback, fixed-array mapping for alpha powers, circle-to-line
normalisation, line and terminal transition checks, field decoding and
arithmetic, prepared multiplication, and fixed proof-system constants. These
operations determine whether a run accepts and belong to the mathematical
soundness proof. They cannot change which source indices are passed to the
opening accessors once a particular loop iteration continues. The read-order
theorems therefore expose them honestly without assuming a semantic result
about them.

## Replay

Use Lean 4.32 and the Lean library built from the matching patched Aeneas:

```sh
LEAN432_BIN=/path/to/lean-4.32.0/bin/lean \
AENEAS_LEAN_LIB=/path/to/aeneas/backends/lean/.lake/build/lib/lean \
./aeneas-verif/v5-fri-consumer-exact-20260815/replay-lean432.sh
```

The replay checks all recorded source and generated-file identities and then
compiles the generated definitions and proof. It does not regenerate the
LLBC; that requires the pinned Charon/Aeneas extraction environment.
