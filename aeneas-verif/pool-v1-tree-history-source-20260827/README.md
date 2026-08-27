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

## Green checkpoint: production one-append carry and abstract frontier

`generated/PoolV1TreeAppendOne/Funs.lean` is a complete transparent
translation of the literal `production_tree_append_one` wrapper and its
production validation, carry loop, root reconstruction and receipt path. The
focused source bridge closes the exact three-way semantics of one carry
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

The capstone `append_loop_has_recursive_source_trace` lifts those steps through
the literal generated loop with a decreasing depth measure. Every successful
loop execution therefore has an explicit recursive sequence of exact one-bit
carry steps and terminates only at depth 20 or at the deployed non-one low-bit
branch. It reports the same three standard Lean axioms and introduces no
abstract loop function, trace-cover premise or termination assumption.

`proof/PoolV1TreeAppendOneAbstractBridge.lean` then discharges the complete
carry representation argument. `appendCarry_modelFrom_exact` proves the pure
concrete carry is exactly the existing hash-parametric `appendCarry` kernel.
`CarryTrace.concreteCarry_exact` connects every translated recursive trace to
that pure carry, including the caller's final carry-slot write. Finally,
`translated_append_loop_implies_modelFrontier_appendCarry` starts from literal
translated loop success and concludes `appendCarry` over the exact depth-20
range/test-bit frontier representation consumed by the Pool tree/history
invariant. Open and full results are both covered. All theorem groups report
exactly `[propext, Classical.choice, Quot.sound]`.

`proof/PoolV1TreeAppendOneCallerBridge.lean` lifts that result through the
literal translated `ValidatedIncrementalMerkleTreeV1::append_one` caller.
Successful caller execution now proves the exact cursor increment, retained
empty-table identity, final concrete frontier, receipt leaf/sequence/root
identity, exact history page/slot quotient-remainder and the same open/full
abstract `appendCarry` result over the
returned tree's cursor and frontier. The proof follows the actual full and
non-full branches, array update, root-call result propagation and receipt
construction. It uses only `[propext, Classical.choice, Quot.sound]`.

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

The carry trace, mathematical representation and outer caller's structural
after-image are complete. The translated non-full root reconstruction is also
closed at the exact source boundary:
`proof/PoolV1TreeReconstructBridge.lean` now proves the literal translated
range loop equals the existing `reconstructFrom` kernel for its exact suffix,
and lifts that equality through the production reconstruction wrapper and the
accepted non-terminal outer append branch. The only remaining mathematical
step inside one append is the pure lower-empty-prefix/suffix composition from
that exact `reconstructFrom` suffix to `reconstructRoot` of the full returned
frontier.

`proof/PoolV1TreePublicWrapperBridge.lean` closes the public one-append source
boundary. From literal `production_tree_append_one` success, it constructs the
exact successful `ValidatedIncrementalMerkleTreeV1::from_parts` and
`ValidatedIncrementalMerkleTreeV1::append_one` calls, proves that validation
preserves the concrete source tree and authenticated empty table, and lifts
the already-proved abstract `appendCarry` result to the returned public tree.
Both public-wrapper theorem groups report only
`[propext, Classical.choice, Quot.sound]`.

`proof/PoolV1TreeAppendTwoBridge.lean` closes the ordered two-append kernel and
public-wrapper source boundary. The new focused extraction begins at literal
`production_tree_append_two`; the translated `append_two` first performs its
capacity check, then calls the same production `append_one` exactly twice.
Successful public execution is proved to factor into validation, the first
append, the second append from the first returned tree, and the public inner
tree conversion. Receipt order is exact: the first receipt binds the first
leaf and intermediate sequence, the second begins at that intermediate
sequence and binds the returned tree root/sequence. The returned cursor is the
source cursor plus exactly two, and both receipt history locations are the
deployed quotient/remainder values. Every theorem group reports only
`[propext, Classical.choice, Quot.sound]`; the two-append decomposition adds no
semantic premise.

`proof/PoolV1ProgramPreparedAfterimageBridge.lean` begins the literal program
transition lift. Its capstone
`production_validate_success_implies_exact_afterimage` starts from successful
translated execution of production
`PreparedAuthorizedAppendV1::validate_inherited_state_and_cursor` and proves:

- exact inheritance of pool identity and verifier policy;
- checked cursor motion by exactly one or two, according to the request;
- exact one/two receipt cardinality and ordering;
- exact leaf indices and root sequence numbers; and
- equality of the terminal receipt root to the returned tree root.

The array-equality callback is given a transparent proof that `true` implies
actual digest equality. The two structural equality callbacks have transparent
executable interpretations. The capstone and callback theorems report only
`[propext, Classical.choice, Quot.sound]`.

`proof/PoolV1HistoryPersistBridge.lean` now starts the literal byte-persistence
lift from the two production loops in `programs/aspis-pool/src/history.rs`.
The focused Charon/Aeneas translation keeps both loop bodies and both outer
functions transparent.  For every successful active loop-body execution,
`write_loop_body_exact_root_slot` and
`append_loop_body_exact_root_slot` prove that the canonical 32-byte digest is
written at exactly `64 + slot * 32`; the append form proves the slot is
exactly `header.filled + enumerated_offset`.  The inactive branches are proved
to terminate without changing the page bytes.  Every theorem reports only
`[propext, Classical.choice, Quot.sound]`; there is no byte-write callback or
semantic persistence premise.

The recursive capstones `write_loop_success_has_exact_trace` and
`append_loop_success_has_exact_trace` now lift those byte writes through every
literal iterator step to the source loop's terminal result.  The trace is
indexed by the actual source slice and enumerated cursor, so it records the
canonical encoded root and exact page slot for every input root in order.
`append_roots_success_has_exact_persistence` additionally peels the complete
existing-page production function: it proves the capacity check, full loop
trace, exact `filled := old_filled + roots.len()` arithmetic, and the final
little-endian two-byte write at page offsets 56--57.  These capstones retain
the same three standard Lean axioms and add no premise beyond the fixed
8,256-byte account-page length supplied by the caller.

`write_new_page_success_has_exact_persistence` now closes the complete
rollover/new-page function as well.  Starting from literal translated source
success, it exposes the exact zero-fill and every static header after-image:
magic, version, capacity log, digest encoding version, pool public key, page
number, first sequence and initial filled count.  It then connects that exact
header to the recursive ordered root-write trace.  Consequently the new-page
and existing-page persistence functions are both source-closed, including the
canonical root slots and their deployed byte offsets.  Its `#print axioms`
result is exactly `[propext, Classical.choice, Quot.sound]`.

`proof/PoolV1HistoryReadBridge.lean` closes the successful retained-root read
path from literal production source.  Its capstone
`read_retained_root_success_has_exact_source_slice` proves the exact deployed
page and filled-slot checks, checked byte offset `64 + slot * 32`, fixed
32-byte source slice and canonical decoder result.  No retained-root lookup or
decoder callback is assumed.

`proof/PoolV1HistoryCodecRoundTripBridge.lean` then connects the literal
production encoder called by both persistence functions to that exact decoder.
`encode_digest_canonical_loop_exact` follows all eight ordered little-endian
limb writes, and `source_encoder_decoder_round_trip` proves that every
canonically encoded production digest decodes to exactly the original digest.
This is an actual source-level codec theorem rather than an abstract
serialization premise.  Both focused theorem groups report only
`[propext, Classical.choice, Quot.sound]`.

`proof/PoolV1HistoryReadAfterWriteBridge.lean` closes the byte-persistence
composition for both routing outcomes.  It proves that all later ordered
writes preserve a selected earlier 32-byte root slot, and that the final
existing-page filled-count update at offsets 56--57 preserves every root slot
beginning at offset 64.  The capstones
`new_page_success_selected_root_decodes` and
`existing_page_success_selected_root_decodes` start from literal production
persistence success and conclude that every selected stored root decodes to
exactly its original digest.  Their axiom union is exactly
`[propext, Classical.choice, Quot.sound]`.

`proof/PoolV1CheckedHistoryDistributionBridge.lean` closes the pure production
current-page/rollover distribution gate used by prepared settlement planning
and replay.  It begins at the literal translated
`prepared_settlement::checked_history_distribution` source function, including
both checked sequence additions and both calls to the deployed
`root_history_location`.  Successful execution proves:

- the first and final retained sequences are exactly `source + 1` and
  `source + count`;
- the first root cannot precede the current page and the final root cannot
  exceed the immediately following page;
- the current-page count is exactly the source's nested page-equality split;
- the next-page count is exactly `count - current`; and
- `header.filled + current <= 256`, from the literal source capacity gate.

The generated helper and its `root_history_location` dependency are fully
transparent.  The capstone
`checked_history_distribution_success_exact` reports exactly
`[propext, Classical.choice, Quot.sound]`; it has no routing callback,
trace-cover premise, `sorry`, `admit` or project-specific axiom.

`proof/PoolV1AccountGatesBridge.lean` closes the three literal production
account-identity helpers in `history.rs`.  Successful
`require_program_account` now proves exact owner equality, non-executable
status and the requested writable bit.  Successful `require_program_owned`
proves exact owner equality and non-executable status.  Successful
`require_root_page_address` proves that the supplied account key is exactly
the address returned by the production page-address derivation for the given
program, pool and page number.  The owner/writable theorem groups report only
`[propext, Classical.choice, Quot.sound]`.  The address theorem additionally
reports the deliberately named Solana runtime boundary
`solana_pubkey.Pubkey.find_program_address`; no other project-specific axiom is
present.

`proof/PoolV1PrevalidateNewPageBridge.lean` lifts the literal outer
`transition::prevalidate_new_history_page_v1` constructor.  Successful source
execution is possible only when the combined new-page validator returns
success, and the private authorization token is proved to contain exactly the
input program id, pool id, page account key and page number.  The outer
constructor, `Result` propagation and all four token fields are transparent.

The combined validator is now closed by the minimal extraction-only
normalization permitted at the Solana runtime boundary.  The literal
production caller composes the already source-closed owner/writable and PDA
gates with `normalized_validate_new_page_borrowed_data`, extracted from
`harness/src/lib.rs`.  That Rust function begins at the byte slice returned by
the borrow and retains the production test verbatim: exact length 8,256 and no
nonzero byte.  Its bridge proves the whole iterator scan, rather than assuming
an `all-zero` predicate.

The capstone
`literal_prevalidate_success_has_exact_gates_borrow_data_and_token` starts from
literal production caller success and an explicit runtime result
`SolanaAccountDataBorrow.tryBorrowData page = ok (Ok data)`.  It proves exact
owner identity, non-executable and writable status, the PDA key returned by the
named Solana PDA primitive, all 8,256 zero bytes, and all four token identities.
Its complete axiom report is the standard Lean trio plus only the two ordinary
Solana runtime interfaces `SolanaAccountDataBorrow.tryBorrowData` and
`SolanaPdaRuntime.findProgramAddress`.  There is no Pool semantic axiom,
whole-validator axiom, `sorry`, `admit`, abstract iterator, trace-cover premise
or conclusion-shaped callback.  The normalized checker LLBC is
`extraction/PoolV1NormalizedNewPageData.llbc`, SHA-256
`a7c0cdf0c4582540e842cb415247e6dbde246e7854e4525cf8615876459de0a2`.

`proof/PoolV1HistoryResultImagesRoutingBridge.lean` lifts the literal
production `prepared_settlement::history_result_images_match` checker. From
successful source execution its capstone
`history_result_images_success_has_exact_page_route` exposes the exact
production root-history location, current-page validation, transition root
count and `checked_history_distribution` result. It then proves the deployed
option grammar directly from the translated control flow:

- zero rollover roots requires `next_page_address`, the supplied next account
  image and `next_rollover_page_image` all to be absent; and
- a nonzero rollover count requires all three values to be present.

The proof also follows the literal current-page after-image computation far
enough to establish that routing is reached only after successful ordered
receipt encoding, zero-page allocation, current-page copy/append and exact
current-image comparison. Its axiom report contains the standard Lean trio,
the Solana PDA runtime boundary, and the two canonical digest codec names.
Those codec equations are not open mathematics: they are independently
source-closed by `PoolV1HistoryCodecRoundTripBridge.lean`. No iterator,
account-routing, trace-cover or conclusion-shaped axiom appears in the
capstone.

The retained-root reader passes through Rust's formatting machinery only on
an impossible `Result::unwrap` failure after a successful fixed-array
conversion.  Aeneas otherwise exposes its placeholder `core::fmt::Formatter`
as an axiom even though its state is unobservable.  The bundle therefore pins
the same formatter-as-`Unit` tool-model patch already used by the frozen V5
source replay in
`aeneas-patches/0001-model-formatter-as-unobservable-unit-state.patch`.

The remaining implementation lift is:

1. lift the now-closed prepared-afterimage validator through the caller that
   constructs it and through the state/root account writes;
2. connect the already-proved result-image routing and byte-persistence
   capstones through the literal transition caller's mutable `AccountInfo`
   borrows, including current-page write-back, optional rollover-page
   write-back, pool-state root/cursor update and root-history identity
   preservation.

The full literal transition router has been extracted successfully, but the
current Aeneas frontend cannot translate its mutable `AccountInfo` borrowing
path transparently. The nested `Option` routing itself is now closed by the
literal result-image checker above. Mutable account borrowing, non-aliasing
and write-back are therefore the smallest explicit source-to-persistence
boundary. New-page immutable borrowing is no longer in that gap: it is isolated
at the named Solana byte-slice interface and every subsequent check is proved.
This is a source-tool lift, not an unproved root-distribution, option-routing,
new-page validation or byte-persistence equation: all four are independently
source-closed above.

The only intended cryptographic semantic boundary is the already-frozen
Poseidon tree-parent primitive. Account-runtime behavior remains the ordinary
Solana execution boundary; the source proof must still show the program passes
the exact account identities and bytes to it.
