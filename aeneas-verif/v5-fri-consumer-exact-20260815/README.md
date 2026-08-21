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
| `TypesExternal.lean` | `8184109b4cf2fe609835f1cab610516276f575afeef53793f12d7ecc589b7c37` |
| `Types.lean` | `c121162321fc5f7bfc00bb58f18b342d182529dca03eb4534157fcaf085cd58e` |
| `FunsExternal.lean` | `d9781f69ad77b8d453e86c818c1978643f719ccab3425e0c50dcaf88dc053318` |
| `Funs.lean` | `370be7ac485d08bef17844e240b3d759f639cb078c91b2880c6e2747d21b3745` |

`Funs.lean` includes only the narrow compatibility expansion required for
the mutable enumerated slice iterator and two translated shift literals.
`FunsExternal.lean` replaces the relevant generated standard-library
placeholders with transparent definitions, including the state-threading
semantics of fixed-array `map` and `Result::map_err`. Its generated external
declarations are kept inside the extraction namespace so that this snapshot
can be imported beside the independent arithmetic snapshot; the derived
`QM31` equality is the transparent four-limb equality implemented by Rust.
The production verifier source is unchanged.

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

`V5FriConsumerValueSemantics.lean` then joins each accepted source read to
the independently extracted arithmetic helpers. It proves the exact circle
fold, line fold, and final-polynomial comparison for an accepted read. Its
only cross-extraction input is equality of the literal helper calls after
structural conversion of the duplicate generated types; it does not assume a
fold equation or a `ForestFriChecks` conclusion.

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

## Opening-byte adapter

`V5FriConsumerValueAdapter.lean` connects each successful generated Rust
opening accessor call to the byte-level returned-opening model used by the
authenticated FRI schedule. In particular,
`generatedOpeningToReturned_value_of_success` proves that a successful
`StateOnlyPrivateOpening::value(ordinal)` call returns exactly the model's
value bytes at the same ordinal, assuming the parser-established record-width
and record-length bounds. The proof unfolds the generated checked arithmetic
and slice access; it is not a trace-test assumption.

## Accepted proof to the four FRI checks

`V5FriAcceptedForestChecks.lean` now joins the source facts above to the exact
field arithmetic, the authenticated Merkle values, and the released coordinate
tables.  For every accepted query it proves the circle fold, both middle line
folds, and the final polynomial comparison.  The combined theorem is
`accepted_production_execution_yields_released_forest_fri_checks`.

It also proves that a second accepted Merkle forest cannot make those checks
different unless the already named SHA-256 Merkle-collision event occurs.
`remove_released_fri_arithmetic_failure_into_collision` therefore removes the
old generic "FRI arithmetic failed" branch from the released security event.

The result does not hide its remaining code connections. Four FRI
source/model inputs remain visible:

- equality between six opaque helper calls in this extraction and the
  separately proved arithmetic helpers;
- agreement between the accepted call's byte decoding and the mathematical
  decoder, scoped to the one prepared claim object used by that call;
- equality between the challenges and final polynomial passed by the
  transcript driver and the values used by the FRI model; and
- the shape validator's property that success returns the input shape.

The first two are code-to-code or code-to-value statements. The third is the
remaining outer-driver value connection. The fourth is a small Rust
control-flow fact. None assumes a FRI fold equation or a cryptographic
security claim. The production full-leaf and selected-slot transition
decoders are now proved in Lean to equal the independently extracted,
loop-free decoder references for every successful 64-byte input and every
slot below four. `V5FriProductionDecoderEquality.lean` supplies this theorem
directly to the accepted-forest proof; it is no longer a caller parameter or
a Kani-only boundary. The shape property is checked for every input by
`../v5-shape-validation-20260821/`; that universal check does not itself
produce a Lean proof term, so the proposition remains a visible parameter
here.

The theorem also takes a coordinate source certificate for the successful
call in the accepted execution. It deliberately does not claim equality for
every possible coordinate-helper input. The unchanged private parent helper
has a reproducible Charon/Aeneas extraction in
`../v5-fri-coordinate-source-20260820/`; the surrounding public driver's
mutable fixed-array construction remains the narrowly stated source-tool
boundary.

## Opaque called operations

The generated translation still treats several called operations as opaque:
shape validation and column counts, inverse derivation and the supplied
inverse callback, circle-to-line normalisation, line and terminal transition
checks, field decoding and arithmetic, prepared multiplication, and fixed
proof-system constants. Fixed-array mapping for alpha powers is no longer in
that list: its exact state-threading and pointwise semantics are defined and
proved in this bundle. These
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
the maintained observation bridge, and the byte/accessor adapter. It does not
regenerate the LLBC; that requires the pinned Charon/Aeneas extraction
environment.

The larger replay below compiles the arithmetic, coordinate, decoder,
consumer, and accepted-forest proofs together from clean output directories:

```sh
LEAN432_BIN=/path/to/lean-4.32.0/bin/lean \
AENEAS_LEAN_LIB=/path/to/aeneas/backends/lean/.lake/build/lib/lean \
V5_FRI_ARITHMETIC_BASE_LEAN_OUT=/path/to/checked-field-oleans \
V5_FRI_COMPONENTB_LEAN_OUT=/path/to/checked-component-b-oleans \
./aeneas-verif/v5-fri-consumer-exact-20260815/replay-accepted-forest-lean432.sh
```

After replaying both this bundle and
`v5-merkle-unchanged-full-20260820`, check the returned-value bridge with:

```sh
AENEAS_LEAN_LIB=/path/to/aeneas-lean432-oleans \
V5_MERKLE_UNCHANGED_LEAN_OUT=/path/to/merkle-replay-output \
V5_FRI_CONSUMER_REPLAY_OUT=/path/to/fri-replay-output \
  ./aeneas-verif/v5-fri-consumer-exact-20260815/replay-returned-output-lean432.sh
```

`V5MerkleFriReturnedOutputBridge.lean` proves field-for-field that the opening
value returned by the independently translated Merkle driver has exactly the
view consumed by the independently translated FRI verifier. The conversion
changes only Lean namespace types; opening bytes, offsets, query indices, and
the consumed-byte count are unchanged.
