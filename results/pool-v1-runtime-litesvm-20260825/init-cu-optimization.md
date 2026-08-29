# Pool V1 initialization CU gate

## Pre-optimization runtime observation

The pre-optimization Pool SBF artifact was executed with LiteSVM 0.16.0
(Agave 4.2.1) and an explicit 1,400,000-CU transaction limit. Initialization
created the Pool state PDA, root-page PDA and vault PDA, and successfully
invoked SPL Token `InitializeAccount3`, but then exhausted the transaction
meter before returning:

- artifact bytes: `284512`
- artifact SHA-256:
  `71f92f74bbf0afba995b862fce6d6d3bf8ad5d31500631d5ae7e738838d4eed2`
- Pool instruction index: `1` (after the compute-budget instruction)
- Pool CU reported at failure: `1399850 / 1399850`
- runtime error: `ProgramFailedToComplete` / `exceeded CUs meter at BPF instruction`

The artifact's `programs/aspis-pool` Rust inputs were byte-identical to the
then-current local source tree when copied from the prior isolated NUC build.

## Cause and narrow semantic optimization

Sequence zero has exactly one canonical tree image. The Pool binary pins the
complete recursive empty-root table in `empty_roots.rs`, whose focused KAT
checks it against the same Poseidon parent construction. Nevertheless, the
genesis path repeatedly called the general non-full-tree validator, and that
validator reconstructed the depth-20 root with twenty Poseidon parents on
each call.

`programs/aspis-pool/src/state.rs` now specializes only sequence zero:

1. Genesis constructs the exact root and frontier from the pinned table.
2. Encoding validation requires exact equality with every corresponding
   pinned entry and fails closed on any root or frontier difference.
3. Every state with a nonzero sequence retains the complete generic
   reconstruction check.

For the authenticated recursive table this is the same predicate as the old
genesis reconstruction, not a change to the tree hash, depth, root, frontier,
account encoding or accepted non-genesis state set.

Focused host evidence:

```text
cargo test -p aspis-pool \
  state::tests::specialized_genesis_is_exactly_the_generic_checked_tree_and_fails_closed \
  --lib -- --exact

running 1 test
... ok
test result: ok. 1 passed; 0 failed; 45 filtered out
```

The test compares the specialized genesis tree to the generic checked
constructor and separately proves that a changed root or changed frontier is
rejected. The pre-existing focused table KAT was also run exactly:

```text
cargo test -p aspis-pool \
  empty_roots::tests::pinned_table_matches_recursive_poseidon_v3_construction \
  --lib -- --exact

running 1 test
... ok
test result: ok. 1 passed; 0 failed; 45 filtered out
```

A fresh SBF build and strict-cap LiteSVM initialization measurement must
replace this section's pre-optimization artifact before release.
