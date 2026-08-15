# V5 FRI source-loop extraction

This package records the order in which the released Rust verifier reads the
four sets of FRI openings after they have been checked and prepared.

The replay script copies the pinned production sources to a temporary
directory, applies `extraction/v5-fri-loop-order.patch` there, runs Charon and
Aeneas, compares the resulting Lean files with the checked-in snapshots, and
compiles the Lean proof with Lean 4.32.0. It never changes the production
source tree.

## What the temporary patch changes

The patch makes two narrowly scoped changes to the temporary copy of
`programs/aspis-verifier/src/v5_fri_checks.rs`:

1. It rewrites the monotone `while` loop used to find a parent opening as the
   equivalent recursive function `advance_monotone_ordinal`, because this is
   the form Aeneas can translate.
2. It adds a diagnostic function,
   `trace_v5_fri_reads_after_preparation`, plus small helper functions and
   fixed-size trace records. The function performs the same four read passes,
   in this order: layer zero to line one, line one to line two, line two to
   line three, and line three to the final value.

Each successful trace entry records the input index, its position, the parent
index and position where applicable, the radix-four slot, and the number of
bytes read. The release has at most 18 entries in each pass, so the extraction
uses a fixed 18-entry record and a separate count.

The replay script pins the Git blob identities of the two verifier files and
the two core opening files, as well as the Charon and Aeneas commits. The
production FRI-check file used by this package has Git blob
`3b1f37f2504aa2b309cad82605c88cab11afcb85`.

## What is proved

Charon and Aeneas successfully translate all 19 transparent functions needed
by the diagnostic driver. The checked Lean proof establishes:

- writing an entry below position 18 changes exactly that position in the
  fixed trace;
- the full fixed trace has length 18; and
- taking a prefix with an allowed count has exactly that count as its length.

The generated driver also visibly calls the four recursive passes once and in
the production order. `ExactRustV5FriSourceLoopTrace` states the exact list
equality needed to connect those generated traces to the maintained FRI
read-schedule theorem.

The proof contains no `sorry`, declared axiom, `native_decide`, or compiled
evaluation shortcut. Its printed dependencies are Lean's standard
propositional and quotient foundations.

## What remains open

`ExactGeneratedV5FriSourceLoopTrace` is currently a named proposition, not a
proved theorem. Closing it requires induction over the four generated
recursive passes to show that every successful trace prefix equals the four
expected maps.

There is also an explicit source-review boundary between the unchanged
production `while` loop and the recursive spelling used only in the temporary
copy. This package does not prove the arithmetic FRI checks, coordinate
calculations, transition equations, cryptographic assumptions, or any theft
probability. Those operations were deliberately left outside the diagnostic
trace. Existing accessor and monotone-lookup packages cover the bytes returned
for a requested index under their stated sorted-list assumptions; this package
only covers their call order and numeric read metadata.

## Replay

The paths below match the pinned local tool builds used for this release. They
may be replaced by equivalent paths to the same commits and Lean library.

```sh
LEAN432_BIN=/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
AENEAS_LEAN_LIB=/private/tmp/aspis-aeneas-lean432-check.ZOGKhi/aeneas/backends/lean/.lake/build/lib/lean \
ASPIS_CHARON_REPO=/private/tmp/aspis-transcript-aeneas-20260814/charon \
ASPIS_AENEAS_REPO=/private/tmp/aspis-transcript-aeneas-20260814/aeneas \
./aeneas-verif/v5-fri-loop-order-source-20260815/replay-lean432.sh
```

A successful run ends with:

```text
Lean 4.32 V5 four-pass FRI read-order extraction: PASS
```
