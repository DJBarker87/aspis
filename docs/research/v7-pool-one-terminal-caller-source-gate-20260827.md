# V7 one-terminal Pool caller source gate

Date: 2026-08-27

This audit covers the production-inactive proof-carried-ASJA prototype. It does
not claim that the current Rust caller is safe to enable. The exact blocker is
the live-state binding at the immediate verifier CPI.

## Decisive gap

`plan_pair_verifier_dispatch_v1` binds the Pool identity, selected verifier,
proof account, statement payload and proof length. The resulting CPI supplies
the verifier only the proof account and encoded base request. It does not
supply the canonical 800-byte `ASPLIVE1` snapshot decoded from the Pool account,
nor an authenticated digest of that snapshot.

The staged pair verifier's parser already has the right semantic interface:
`parse_v7_staged_pair_inputs_v1` takes `account_derived_live_snapshot` and
combines it with the proof-carried ASJA candidate. The current Pool caller does
not instantiate that argument.

After the CPI, `apply_authenticated_afterstate_from_program_invariant` checks:

- capacity has not been exhausted;
- `candidate.next_pair_index = current.next_pair_index + 1`; and
- inactive candidate frontier slots contain the canonical empty roots.

Those checks do not inspect the current root or current frontier. Consequently,
two distinct live trees with the same cursor accept the same syntactically
valid returned afterstate. The Lean theorem
`current_pool_gate_does_not_determine_live_snapshot` gives an explicit
kernel-checked countermodel. Cursor equality therefore provides staleness
rejection only after another transaction advances the cursor; it does not bind
the transition to the actual source tree.

## Smallest sufficient production change

The Pool must derive the canonical `ASPLIVE1` bytes from the same locked pair
state account that it later writes and bind them to the selected verifier's
pre-C1 transcript input. Two implementation shapes are sound in principle:

1. pass that Pool-derived snapshot in the CPI request and require the verifier
   to compare it byte-for-byte with the proof-bound pre-C1 snapshot; or
2. pass a domain-separated digest of the canonical bytes, provided the
   verifier recomputes/compares the same digest and the hash premise is stated
   explicitly.

The byte-exact route has the smaller formal trust boundary. The Pool account
must remain locked by the same atomic terminal transaction across CPI and
writeback. The verifier must return ASJA only after that comparison succeeds.
The existing immediate return-program/length/decoder check can then remain the
capability boundary.

The formal structure `AuthenticatedLiveSnapshotBinding` names exactly this
obligation. `bound_snapshot_transports_exact_transition` proves that equality
of the proof-bound and account-derived snapshots transports the existing exact
pair-transition theorem to the locked source state. No cryptographic theorem
is changed.

## Source-verified components which remain reusable

The following existing Aeneas/Lean bridges remain valid building blocks:

- verifier registry selection:
  `corrected_production_success_implies_exact_authorization`;
- pair-tree source kernels:
  `production_append_two_success_is_exact_ordered_composition` and
  `production_append_two_success_exact_receipt_afterimage`;
- chronological same-page and rollover routing:
  `history_result_images_success_has_exact_page_route`;
- exact history persistence/read-after-write:
  `existing_page_success_selected_root_decodes`,
  `new_page_success_selected_root_decodes`,
  `persisted_writable_current_page_selected_root_decodes`, and
  `persisted_rollover_page_selected_root_decodes`;
- account gates and new-page prevalidation:
  `literal_prevalidate_success_has_exact_gates_borrow_data_and_token`.

The pure formal modules also prove the intended nullifier single-use, atomic
rollback, exact pair-afterstate transition and withdrawal conservation
properties. These are semantic theorems, not yet literal source bridges for
the new caller.

## Remaining source/runtime boundaries

End-to-end production caller closure still requires:

1. literal source proof that the canonical `ASPLIVE1` encoding is derived from
   the already-decoded, locked `CanonicalPairPoolStateV1`;
2. source proof of the snapshot's CPI request transport and the verifier's
   exact pre-C1 comparison;
3. source proof of immediate selected-program ASJA authentication and
   `apply_authenticated_afterstate_from_program_invariant`;
4. source proof for canonical pair-state encoding/writeback and the exact
   same-page/rollover call made by the new caller;
5. source proof for nullifier marker planning, one-time creation and exact
   marker write;
6. on withdrawal, source proof for the canonical SPL `TransferChecked`
   instruction, Pool-PDA signer seeds and exact pre/post token delta; and
7. the accepted verifier path's exact transition result, supplied by the
   separate cryptographic/Aeneas verifier lane.

Solana `AccountInfo` borrow/release, CPI and return-data behavior, PDA
derivation, transaction rollback, and SPL Token execution remain named runtime
primitives. Existing Aeneas bundles explain the interior-mutable `AccountInfo`
translation boundary; this audit does not conceal it behind a caller-shaped
axiom.

## Status

The proof-carried ASJA architecture remains the viable one-terminal design,
but its current Rust entry path is explicitly production-inactive and must not
be enabled before items 1-3 above are closed. The live-snapshot binding is a
soundness prerequisite, not an optional hardening measure.
