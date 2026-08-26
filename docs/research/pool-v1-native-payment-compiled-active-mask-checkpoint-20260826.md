# Pool V1 native compiled active-mask checkpoint (2026-08-26)

## Result

`AspisFormal.Pool.NativePaymentCompiledActiveMaskV1` closes the mathematical
compiled-active-mask boundary immediately below
`NativePaymentMaskedTerminalBridgeV1`.

The module pins the two production `[u16; 64]` tables from
`payment_semantic_terminal_constants.rs`, models the exact runtime lookup

```text
active(row) = testBit(masks[row / 16], row % 16)
```

for all 1,024 rows, and proves that the production-shaped 64-by-16 selector
factorization is the expanded active-row equality-selector MLE at every
terminal point.  At a Boolean point selecting one physical row, the evaluator
therefore returns exactly that row's compiled active bit embedded in the
field.

The exact tables contain 128 active transfer rows and 123 active withdrawal
rows.  Withdrawal is a subset of transfer, and the exact transfer-only set is
`{427, 432, 443, 444, 448}`.  These are kernel `decide` proofs over the literal
tables, not `native_decide` results.

Finally, the literal variant table specializes the strengthened terminal to

```text
nativeConstraintMLE
  + mu * tableSum(H1)
  + mu^2 * tableSum(if active(row) then 0 else H1(row))
```

and an extracted masked boundary constructs the exact
`NativeAcceptedRandomizedTerminal` consumed by
`NativePaymentRandomizedExtractionV1`.

## Production pins

The checkpoint pins:

- 1,024 physical rows, split into 64 blocks of 16 rows;
- `row / 16` for the block and `row % 16` for the local bit;
- big-endian high-table coordinate order `5 - coordinate` and low-table order
  `3 - coordinate`, matching `Selectors::expand` and `Selectors::row`;
- all 64 literal `u16` words for private transfer and withdrawal;
- the 128/123 exact cardinalities and exact five-row variant delta; and
- the inactive-helper contribution used by the production
  `mu^2 * (1 - copy_active) * h1_z` strengthening term.

The already-pinned production fingerprints are
`0xe858c4c0d4e22b94` for private transfer and
`0xe9de6f8fae7f1793` for withdrawal.

## Main theorems

- `compiled_active_masks_fit_u16`
- `private_transfer_active_row_count`
- `withdrawal_active_row_count`
- `exact_variant_active_row_difference`
- `compiledCopyActiveAtPoint_eq_expanded`
- `compiledCopyActiveAtPoint_booleanPoint`
- `nativeInactiveHelperSum_compiled`
- `tableSum_compiledStrengthenedUnmaskedTerminalTable`
- `native_accepted_randomized_terminal_of_compiled_masked_boundary`

`#print axioms` reports only Lean's standard `propext`, `Classical.choice`,
and `Quot.sound`.  There is no project axiom, `sorryAx`, `Lean.ofReduceBool`,
`sorry`, or `admit`.

## Exact remaining boundary

This checkpoint proves the field algebra after interpreting the optimized
Rust loops.  The next executable refinement obligations remain explicit:

1. prove that `Selectors::expand` produces the modeled high and low tables;
2. prove that `selector_mask_sum_16`, including its dense-mask complement
   branch and bit-scanning loop, equals the selected low-weight sum;
3. combine those facts with `Selectors::copy_active` and the accepted native
   Rust control flow to project the executable result into the evaluator
   proved here; and
4. separately refine the remaining Poseidon/semantic residual lanes, Copy
   LogUp endpoints, transcript/PCS authentication, and Fiat--Shamir repair
   events needed for the full payment relation.

No receipt bridge, wallet, program, K1.6, prover, verifier, or unrelated dirty
file is part of this checkpoint.

## Focused NUC evidence

Only the new target was built on `nuc.local`, in
`/home/dombarker/project-offloads/aspis-native-payment-terminal-20260826`,
under a bounded zero-swap user scope:

```text
systemd-run --user --scope --quiet \
  -p MemoryHigh=20G -p MemoryMax=24G -p MemorySwapMax=0 \
  /usr/bin/time -v env LEAN_NUM_THREADS=1 \
  /home/dombarker/.elan/bin/lake -Kjobs=1 build \
  AspisFormal.Pool.NativePaymentCompiledActiveMaskV1
```

Final run: exit status 0, 21.92 seconds elapsed, maximum RSS 7,687,988 KiB,
and zero swaps.  No broad regression suite was run.
