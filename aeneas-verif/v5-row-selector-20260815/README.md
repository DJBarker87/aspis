# V5 terminal row selector

This bundle isolates the row selector used by the accepted V5 atomic
terminal. It is unrelated to the three-way query-candidate byte.

The production selector uses ten transcript coordinates. It builds a
64-entry table from coordinates 0 through 5, a 16-entry table from
coordinates 6 through 9, and returns:

```text
high[row >> 4] * low[row & 15]
```

`AspisFormal.V5ProductionRowSelector` proves that this is the ordinary
ten-coordinate multilinear equality selector and that, at the Boolean point
for any physical row, it is one on that row and zero on each of the other
1,023 rows. This discharges `SelectsExactRow` for the exact factored formula
used by the source.

## Source extraction

The replay extracts two private methods from the unchanged production file
`crates/aspis-statement/src/atomic_state_only_terminal.rs`:

- `AtomicSelectors::expand`, including the exact reverse-index update loop;
- `AtomicSemanticSelectors::row`, including `row >> 4`, `row & 15`, the two
  array reads, and the source field multiplication.

The reachable field operations are extracted from
`crates/aspis-core/src/field.rs` rather than replaced by handwritten axioms.
The checked snapshots are regenerated in release mode and compared after
removing comments, import spelling, and whitespace.

Pinned Aeneas gives the unsuffixed shift count in `row >> 4` the Lean type
`I32`, although both Rust's shift trait and Aeneas's `wrapping_shr` model use
`U32`. The replay applies the single mechanical correction `4#i32` to
`4#u32` before comparison and compilation. It changes only the generated
literal's Lean type, not its value or the Rust operation.

Both private selector structs have a method named `row`. The replay starts
from that name and then excludes the older copy-selector method, retaining
only `AtomicSemanticSelectors::row`. Pinned Aeneas reports an error for the
excluded method and emits a partial file containing the complete retained
method plus an unused external marker. The replay accepts only that named
error, rejects any generated function that refers to the excluded method, and
uses a deliberately empty `FunsExternal.lean`. No axiom is introduced for
the excluded code.

## What Lean proves

`proof/V5RowSelectorImplementationProof.lean` proves the implementation link,
not just the Boolean algebra:

- the extracted reverse mutable loop computes the exact child weights;
- the extracted outer loop computes the complete product table for every
  valid field representation with the stated table size;
- the production cases are exactly six coordinates to 64 entries and four
  coordinates to 16 entries;
- the extracted `row` method reads entry `row / 16` and entry `row % 16`;
- the extracted QM31 multiplication returns the product of those entries;
- the result equals `factoredSourceRowSelector`; and
- at a Boolean point it is one for the selected row and zero for all other
  rows.

The final two theorem names are:

```text
extracted_expand_and_row_agree
extracted_expand_and_row_select_exactly_one
```

The two methods are extracted into separate generated namespaces so their
otherwise identical Rust structs become different Lean types. The proof uses
an explicit field-for-field conversion between those generated types. No
equality or arithmetic assumption is introduced by that conversion.

The theorem takes as input the two slices passed to `expand` and requires them
to contain valid field values matching coordinates 0 through 5 and 6 through
9. It does not cover the unrelated `poseidon_block` and `path_block` fields,
which the row method never reads. Charon, Aeneas, Lean, and the Rust compiler
remain part of the toolchain that must be trusted.

## Replay

With the pinned Charon, Aeneas, and Lean 4.32 installations:

```bash
ASPIS_CHARON_REPO=/path/to/charon \
ASPIS_AENEAS_REPO=/path/to/aeneas \
AENEAS_LEAN_LIB=/path/to/aeneas-lean/lib/lean \
  ./aeneas-verif/v5-row-selector-20260815/replay-lean432.sh
```
