# V5 monotone opening lookup proof

This package checks the small helper that chooses the authenticated opening
used for a requested FRI index.

The production Rust advances an ordinal through a sorted index list with a
`while` loop, checks that the resulting entry is the requested index, and then
calls `StateOnlyPrivateOpening::value` at that ordinal.  The pinned Aeneas
version stops with an internal translation error on that `while` body.  The
replay therefore applies
`extraction/v5-fri-monotone-recursion.patch` to a temporary source copy.  The
patch replaces only that scan with the same guard and update written as a
recursive helper.  Repository Rust is not changed.

The generated Lean and proof establish, for arbitrary inputs:

- `advance_monotone_ordinal_hits`: if a requested entry occurs at `target`,
  the scan starts no later than `target`, and every intervening entry is
  smaller, the extracted scan returns exactly `target`;
- `opening_value_for_monotone_index_hits`: after that scan, a successful
  helper call returns exactly the value slice at `target`, together with that
  same ordinal.

The proof uses no project axiom.  `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## What this does not prove

This package does not claim that Aeneas translated the production `while`
loop: it did not.  Exact equivalence between that loop and the temporary
recursive spelling remains a named source-level step.  It also does not prove
that the four outer FRI loops call the helper and direct opening accessor in
the required order; that is the remaining loop-dataflow step in
`V5MerkleConsumedValueBridge.lean`.

## Replay

```sh
LEAN432_BIN=/path/to/lean-4.32.0/bin/lean \
AENEAS_LEAN_LIB=/path/to/patched-aeneas-lean-library \
ASPIS_CHARON_REPO=/path/to/charon-cb50ff16 \
ASPIS_AENEAS_REPO=/path/to/aeneas-b59d5188 \
./aeneas-verif/v5-fri-monotone-source-20260815/replay-lean432.sh
```

The replay checks the production source identities, applies the patch only in
a new temporary directory, reruns Charon and Aeneas, compares the generated
Lean byte-for-byte, compiles the proof with Lean 4.32, and rejects unapproved
axioms or proof shortcuts.
