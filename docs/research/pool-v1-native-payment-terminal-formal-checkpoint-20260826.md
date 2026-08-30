# Pool V1 native payment terminal formal checkpoint (2026-08-26)

## Scope and audit result

This checkpoint covers the native Pool V1 Tag-73 payment trace in
`crates/aspis-statement/src/pool_v1/payment_*` and the application relation in
`AspisFormal/Pool/PaymentRelationV1.lean`.

The closest pre-existing Lean terminal bridge was not reusable.  It models the
older Tag-73 atomic one-input/one-output statement (77 source positions and 20
packed semantic lanes), whereas the production native payment trace has three
30-bit values, 94 source semantic lanes, 24 packed semantic lanes, one copy
lane and four Poseidon lanes.  Treating the old bridge as the Pool payment
profile would therefore establish the wrong relation.

The smallest non-circular missing bridge was the deterministic step after
randomized row extraction: exact native value/copy/Poseidon/public row facts
must imply `PaymentRelationV1.ValidPrivateTransfer` or
`PaymentRelationV1.ValidWithdrawal`.

## Kernel-checked checkpoint

`AspisFormal.Pool.NativePaymentTerminalBridgeV1` pins the production geometry,
lane inventory, registry cardinalities, Tag-73 proof grammar, native
profile/release bindings, source/value/conservation cells and public digest
rows.  In particular it pins:

- 1,024 rows, 16 C1 columns, 49 16-row permutation blocks and auxiliary rows
  784 through 879;
- source rows 44, 444 and 492; value auxiliary base rows 864, 866 and 868;
  xor-12 high-bit rows 876, 878 and 872; and conservation rows 870 and 871;
- 94 source semantic lanes, 24 packed lanes, one copy lane, four Poseidon
  lanes and theta width 29;
- native ASVQ length 600, proof length 30,504 at two 203-node frontiers, and
  the exact 32-byte profile and release bindings used by production Rust.

The value theorem reconstructs each auxiliary source from `Nat.ofBits` over
the exact thirty Boolean trace cells.  Its bound is derived with
`Nat.ofBits_lt_two_pow`, rather than assumed.  Transfer and withdrawal
conservation are derived through the exact copy aliases and the two residuals
at rows 870 and 871.

Main theorems:

- `auxiliary_value_lt_valueLimit`
- `private_transfer_value_rows_imply_bounds_and_conservation`
- `withdrawal_value_rows_imply_bounds_and_conservation`
- `native_private_transfer_semantic_rows_imply_valid`
- `native_withdrawal_semantic_rows_imply_valid`

`#print axioms` reports only Lean/Mathlib foundations `propext` and
`Quot.sound` for the main implications.  There is no project-specific axiom,
`sorry`, `admit`, `#exit`, or compiled-decision shortcut.

## Remaining boundary

This is deliberately not yet a theorem that a bare randomized Tag-73 terminal
equality implies the payment relation.  The remaining work is to prove, under
the production Fiat--Shamir freshness and non-collision conditions, that:

1. the degree-27 masked terminal and degree-22 zerocheck equality extract the
   row-local Poseidon and 94 source-semantic residuals;
2. theta width 29 (collision degree 28) separates the four Poseidon, 24 packed
   semantic and one copy lanes;
3. the degree-two mu aggregate separates the helper total and inactive-row
   constraints;
4. the LogUp challenge is outside its collision set, so the 78 transfer or 75
   withdrawal copy endpoints yield the exact aliases used here; and
5. the Rust field/digest/path decoders refine the typed `TraceProjection`.

Those are extraction and Rust-refinement obligations, not conclusion-shaped
application assumptions.  Receipt encoding/Aeneas work is outside this
checkpoint.

## Focused build evidence

The focused module was built on the dedicated Linux build host from the isolated offload
`<build-root>` with:

```text
systemd-run --user --scope --quiet \
  -p MemoryHigh=20G -p MemoryMax=24G -p MemorySwapMax=0 \
  /usr/bin/time -v env LEAN_NUM_THREADS=1 \
  lake -Kjobs=1 build AspisFormal.Pool.NativePaymentTerminalBridgeV1
```

Final run: exit status 0, 9.39 seconds elapsed, maximum RSS 6,484,512 KiB,
and zero swaps.  No broad Lean regression suite was run.
