# Pool V1 tree/history production-source bridge

This bundle is an implementation-refinement lane for the Pool V1 incremental
tree and retained-root history. It does not replace or weaken the existing
mathematical tree/history predicates.

## Frozen source inventory

The extraction harness calls production code without duplicating its body:

- `IncrementalMerkleTreeV1::empty` in
  `crates/aspis-statement/src/pool_v1/incremental_merkle.rs`;
- `append_one_with_empty_roots` and `append_two_with_empty_roots` in that same
  pure kernel;
- `root_history_location` in
  `crates/aspis-statement/src/pool_v1/root_history.rs`;
- the program-level preparation and persistence path in
  `programs/aspis-pool/src/transition.rs`, with account writes in `history.rs`
  and canonical state/account decoding in `state.rs`.

No production Rust is changed by this bundle.

## Green checkpoint: retained-root address

`proof/PoolV1RootHistoryLocationBridge.lean` starts from the literal
Charon/Aeneas translation of the production wrapper. Its strongest theorem is:

```text
production_root_history_location_source_exact
```

For every successful translated call it proves that the returned page number
and slot are exactly `sequence / 256` and `sequence % 256`, i.e. the existing
`AspisPool.RootHistoryV1.location` predicate. The theorem has no
project-specific axiom and `#print axioms` reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The translated root-history function is transparent. There is no cryptographic
callback or external function in this checkpoint. The remaining trust base is
the ordinary Rust/Charon/Aeneas/Lean toolchain provenance.

## Green checkpoint: production genesis

`proof/PoolV1TreeGenesisBridge.lean` starts from the literal translation of
`IncrementalMerkleTreeV1::empty()`. It proves all three implementation facts
needed at sequence zero:

- the cursor is exactly zero;
- the explicit root is the depth-20 recursive empty root;
- the concrete canonical frontier maps to 20 inactive mathematical slots.

The capstone theorem
`production_tree_genesis_establishes_pool_tree_history` concludes the existing
`PoolTreeHistoryInvariantV1.PoolTreeHistoryInvariant` predicate, including the
retained sequence-zero root and exact history length. The empty-root loop and
the 20-element `core::array::from_fn` call are transparent. The sole semantic
premise is `ParentCallbackExact`, naming the Poseidon tree-parent boundary
directly. All three genesis theorem groups report only
`[propext, Classical.choice, Quot.sound]`; the premise is not a hidden axiom.

## Green checkpoint: production one-append carry step

`generated/PoolV1TreeAppendOne/Funs.lean` is a complete transparent
translation of the literal `production_tree_append_one` wrapper and its
production validation, carry loop, root reconstruction and receipt path. The
focused bridge currently closes the exact three-way semantics of one carry
loop step:

- `append_loop_body_stops_at_depth` proves the depth-20 terminal case;
- `append_loop_body_stops_at_zero_bit` proves that a zero cursor bit retains
  the frontier and current carry;
- `append_loop_body_carries_at_one_bit` proves that a one cursor bit reads the
  exact frontier slot, hashes it on the left of the carry, replaces that slot
  with the authenticated empty root at the same level, and increments the
  level exactly once.

All three theorems report exactly
`[propext, Classical.choice, Quot.sound]`. `ParentCallbackExact` is again the
only semantic premise, and it is used only at the translated production
Poseidon call.

The capstone `append_loop_has_exact_source_trace` lifts those steps through
the literal generated loop with a decreasing depth measure. Every successful
loop execution therefore has an explicit finite prefix of exact one-bit carry
steps and terminates only at depth 20 or at the deployed non-one low-bit
branch. It reports the same three standard Lean axioms and introduces no
abstract loop function, trace-cover premise or termination assumption.

The append translation uses the committed Aeneas constructor tool branch at
`e9d20a64aa4dcbbc20ba8742a6ddf720f0c575cd` (`aeneas
aspis-v5-constructor-e9d20a64`). That branch contains the already committed
nested-borrow and owned-result preservation fixes needed to translate this
production loop. The generated proof target is Lean `v4.31.0` and contains no
translation error or opaque loop declaration.

Pinned extraction tools:

- Charon `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`;
- Aeneas `b59d5188c082f704a418c7cb4e52ad69328002d1`;
- Lean `v4.32.0`, using the repository's pinned Aeneas Lean-4.32 patch.

The LLBC was extracted with the Aeneas preset, starting only from
`production_root_history_location` and explicitly including the production
`aspis_statement::pool_v1::root_history` module. JSON hash-cons tables can be
emitted in a different order by Charon, so replay compares the translated
declarations rather than treating raw JSON byte order as semantics.

## Remaining implementation boundary

The smallest next boundary is the representation bridge from the now-proved
finite production carry trace to the existing hash-parametric `appendCarry`
predicate, including the caller's final carry-slot write.
After that, the work is:

1. derive two-append as the exact ordered composition of two successful
   production one-appends;
2. connect program transition success to the exact tree/account after-images;
3. prove root-page append persistence and retained-root lookup from literal
   program source;
4. carry pool identity, owner, PDA and same-writable-account checks through the
   successful program path.

The only intended cryptographic semantic boundary is the already-frozen
Poseidon tree-parent primitive. Account-runtime behavior remains the ordinary
Solana execution boundary; the source proof must still show the program passes
the exact account identities and bytes to it.
