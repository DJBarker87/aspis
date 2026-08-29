# Aeneas nested-return drop-flag fix

## Diagnostic

The pinned LLBC function
`aspis_core::v6_transcript::decode_and_absorb_point_claims` (function 47)
contains the nested fallible row/column loops from
`crates/aspis-core/src/v6_transcript.rs:407-413`.  On the
`fields.next_qm31()?` error arm, LLBC call 8099 writes return local zero and
rustc emits this function-exit suffix:

- storage cleanup 8100-8116;
- `Drop encoded` 8154 and `StorageDead encoded` 8155;
- `Drop claims` 8172;
- plain-local Boolean drop-flag assignment 8173 (`_61 := false`);
- final storage cleanup and `Return` 8190.

`lower_nested_loop_returns.take_return_cleanup` already recognizes storage
cleanup and, when Aeneas is in its default `drop_as_no_op` mode, `Drop`.
It stopped at statement 8173, however, so the owned-value cleanup ran before
the nested return was carried through the loop nest.  The resulting synthetic
`pending_return = Some ...` break context had `encoded = bottom`; joining that
context with the normal inner-loop exit lost the enclosing range iterator.
The next outer-loop fixed-point iteration then failed while evaluating LLBC
statement 7688 (`&mut iter^13`) with `There should be no bottoms in the value`.

The diagnostic LLBC is
`d05f26ee7b8bbd4f16c3bccd50348b129d1c25dd51a950730141a9e418d479e3`.
The full fixed-point trace is pinned by SHA-256
`5750489c64207d6fcc7871b37e8c8137e4b02170c83abfdc371158cd7c7a9e46`.

## Patch boundary and soundness

`aeneas-d860ac47-loop-return-drop-flag.patch` changes only
`src/PrePasses.ml`.  In `take_return_cleanup`, and only when
`Config.drop_as_no_op` is active, it treats a Boolean-literal assignment to a
plain local as part of a prospective return-cleanup suffix.  The existing
consumer accepts that suffix only when it is followed by a terminal `Return`;
it then replaces the suffix with the established normal loop-exit cleanup
before carrying the already-computed return value.

The rule cannot discard a write through a reference or projection, does not
change Rust or LLBC, and does not weaken Aeneas's bottom checks or join rules.
The ignored assignment has no observable value in the default drop-as-no-op
semantics: it updates only rustc's local destructor guard immediately before
leaving the function.  With `-eval-drops`, the new rule is disabled and Aeneas
retains the complete cleanup.
