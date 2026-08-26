# Pool V1 native active-selector executable checkpoint (2026-08-26)

## Result

`AspisFormal.Pool.NativePaymentCompiledActiveExecutableV1` closes the three
source-loop seams left by the compiled active-mask checkpoint:

1. `Selectors::expand` over the first six and final four terminal coordinates;
2. `selector_mask_sum_16`, including `count_ones > 8`, 16-bit complement,
   ascending trailing-zero scan order, and add/subtract accumulation; and
3. the zero-mask filter and fold in `Selectors::copy_active`.

The strongest result is:

```text
rustCopyActiveAtPoint variant point
  = compiledCopyActiveAtPoint variant point
```

for either exact payment variant, every commutative-ring terminal point, and
all 64 compiled mask words.  Combined with the preceding checkpoint, the same
source-shaped executable evaluator returns the literal compiled active bit at
every Boolean physical-row point.

## Exact source behavior pinned

The expansion model starts from `[1]`.  For each coordinate and every saved
parent it writes the adjacent pair

```text
[parent - coordinate * parent, coordinate * parent]
```

in the same observable order as the Rust reverse-index in-place loop.  Finite
kernel normalization proves all 64 high-table and 16 low-table entries equal
the already-pinned big-endian selector products.  A separate invariant proves
each expansion step preserves total weight, so the 16 low weights sum to one.

For any value fitting a `u16`, `u16SetBits_complement` proves that
`2^16 - (mask + 1)` has exactly the complementary low sixteen bits.
`u16TrailingZeroScanOrder` is the sorted, duplicate-free enumeration of the
mask's set bits, which is the observable order produced by repeated
`trailing_zeros` and clearing the lowest set bit.  `rustBitScanFold` then models
the exact source accumulator updates.

`rustSelectorMaskSum16_eq_selected` is general over all 65,536 masks.  Sparse
masks start at zero and add selected weights.  Dense masks complement their
bits, start at one, and subtract unselected weights; the proved low-weight
total of one makes both branches exactly the selected-weight sum.  This is not
only a finite check of the currently generated masks (which happen not to use
the dense branch).

Finally, `rustCopyActiveAtPoint` retains the production zero-mask filter and
64-block fold.  Its equality theorem discharges the filter, expansion, and
mask-scan layers together.

## Main theorems

- `rustExpandedHighWeight_eq_compiled`
- `rustExpandedLowWeight_eq_compiled`
- `rustSelectorExpandStep_sum`
- `rustSelectorExpand_sum`
- `sum_rustExpandedLowWeight_eq_one`
- `u16SetBits_complement`
- `u16TrailingZeroScanOrder_sorted`
- `u16TrailingZeroScanOrder_nodup`
- `u16TrailingZeroScanOrder_toFinset`
- `rustBitScanFold_eq_set_sum`
- `rustSelectorMaskSum16_eq_selected`
- `selected_u16_sum_eq_indicator_sum`
- `rustCopyActiveAtPoint_eq_compiled`
- `rustCopyActiveAtBooleanPoint_eq_compiled_bit`

The module's `#print axioms` audit reports only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`; `rustSelectorExpand_sum` needs only
`propext`.  There is no project axiom, `sorryAx`, `Lean.ofReduceBool`, `sorry`,
or `admit`.

## Exact remaining boundary

This closes the active-selector loop algebra at the field-operation level.  It
does not claim a compiler theorem for Rust array mutation or the machine-word
implementation of `PreparedQm31Multiplier`; those remain part of the ordinary
Rust-to-pure-model and QM31-representation boundary.

For the full native payment terminal, the remaining formal work is elsewhere:

- refine the executable Poseidon and packed semantic residual lanes into the
  `NativeConstraintRowResiduals` consumed by the terminal bridge;
- refine the compiled Copy LogUp endpoints and helper totals;
- project successful native Tag-73 parse/control flow and authenticated
  transcript/PCS openings into the accepted masked boundary; and
- discharge the separately named Fiat--Shamir collision/repair events.

No K1.6, wallet/RPC, program Rust, receipt/Aeneas, prover, verifier, or existing
dirty file is part of this checkpoint.

## Focused NUC evidence

Only the new target was built on `nuc.local` in
`/home/dombarker/project-offloads/aspis-native-payment-terminal-20260826`,
under the established bounded zero-swap scope:

```text
systemd-run --user --scope --quiet \
  -p MemoryHigh=20G -p MemoryMax=24G -p MemorySwapMax=0 \
  /usr/bin/time -v env LEAN_NUM_THREADS=1 \
  /home/dombarker/.elan/bin/lake -Kjobs=1 build \
  AspisFormal.Pool.NativePaymentCompiledActiveExecutableV1
```

Green run: exit status 0, 42.91 seconds elapsed, maximum RSS 7,121,584 KiB,
and zero swaps.  No broad regression suite was run.
