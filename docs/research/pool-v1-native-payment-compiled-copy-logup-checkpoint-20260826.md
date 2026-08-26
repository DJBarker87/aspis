# Pool V1 native compiled Copy LogUp checkpoint (2026-08-26)

## Result

`AspisFormal.Pool.NativePaymentCompiledCopyLogUpV1` closes the native-payment
Copy LogUp endpoint and helper-total boundary immediately downstream of the
compiled active-selector checkpoint.

The module pins the complete checked-in tables:

- 78 private-transfer links and 75 withdrawal links;
- sequential tags `1090519040 + link_index`;
- both producer and consumer `(row, slot, pattern)` endpoints;
- all thirteen shared affine tuple patterns, including pattern eight's
  generated `1051521018` offset; and
- the two-entry producer and two-entry consumer row shape.

Kernel evaluation proves that each side's `(row, slot)` placement is injective
and that the compiled `[u16; 64]` activity bit is exactly equivalent to a row
being occupied by a producer or consumer endpoint. This connects the source
loop refinement from commit `686b5668` to the exact Boolean Copy row table.

## Helper-total closure

The native row residual is modeled in the same four-denominator factored form
as `payment_semantic_terminal.rs::copy_residual` and
`logup.rs::copy_logup_residual`. Outside an active endpoint pole and the
separate inactive-slot degeneracy `chi = 0`, a zero active-row residual fixes
that helper value to the row's rational contribution.

The strengthened Tag-73 terminal authenticates two sums:

```text
tableSum helper = 0
tableSum (compiledInactiveHelperTable variant helper) = 0
```

Their difference is the active helper sum. Consequently random inactive
padding remains permitted cellwise, while the active helper sum is zero and
the local rational contributions telescope to the exact global 78- or
75-link rational balance.

The strongest aggregate theorem is:

```text
native_copy_rational_balance_zero_of_accepted_terminal
```

It consumes `NativeAcceptedRandomizedTerminal`, the existing explicit
mu/zerocheck/theta collision exclusions, exact Copy-lane refinement, and the
two denominator exclusions. It introduces no new acceptance assumption.

## Endpoint isolation

The module retains the full producer and consumer multisets. A zero rational
balance yields equality of compressed multisets outside
`NativeCopyChiCollision`; equality of compressed multisets yields equality of
the underlying tagged 16-limb tuples outside
`NativeCopyTupleCompressionCollision`. Since every native tag is unique, the
kernel isolates every link, and in particular the exact scalar tail links:

- transfer indices 71--77: three source-to-auxiliary aliases, three
  auxiliary-to-conservation aliases, and partial-to-carried-partial;
- withdrawal indices 69--74: input/change source aliases, the same three
  conservation aliases, and partial-to-carried-partial.

These produce `NativePrivateTransferFieldEndpointEquations` and
`NativeCommonFieldEndpointEquations`. A conclusion-independent
`NativeNatCellBinding` record then converts the authenticated field-cell
equalities into the existing `PrivateTransferLogUpEndpointEquations` and
`CommonLogUpEndpointEquations` consumed by
`NativePaymentRandomizedExtractionV1`.

## Main theorems

- `nativeProducerRowSlot_injective`
- `nativeConsumerRowSlot_injective`
- `compiledCopyRowActive_iff_endpoint`
- `helper_eq_nativeCopyRowRationalContribution_of_residual_zero`
- `tableSum_nativeCopyRowRationalContribution_eq_balance`
- `native_helper_sum_eq_active_add_inactive`
- `native_copy_rational_balance_zero_of_local_residuals`
- `native_copy_rational_balance_zero_of_accepted_terminal`
- `native_all_link_tuples_equal_outside_collisions`
- `native_private_transfer_field_endpoints_of_logup`
- `native_withdrawal_field_endpoints_of_logup`
- `common_logup_endpoints_of_field_binding`
- `private_transfer_logup_endpoints_of_field_binding`

The module's `#print axioms` audit reports only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`. There is no project axiom, `sorryAx`,
`Lean.ofReduceBool`, `sorry`, `admit`, or `native_decide` shortcut.

## Exact remaining boundary

The compiled Copy LogUp algebra and endpoint isolation are closed. The
remaining native-payment closure is now limited to source/authentication
refinement outside this leaf:

1. prove the production Rust `copy_lane` Boolean restriction equals
   `nativeCompiledCopyLane` (`copyExact` in the aggregate theorem); this is the
   same executable evaluator/refinement boundary retained for the Poseidon and
   packed semantic lanes;
2. bind authenticated C1 field cells to the typed Nat trace projection and
   prove the production M31 encoding is injective on those recovered cells,
   supplying `NativeNatCellBinding`;
3. connect successful Tag-73 parse/transcript/PCS control flow to the accepted
   masked boundary; and
4. discharge or probabilistically bound the separately named mu, theta,
   zerocheck, active-pole, chi-rational, and lambda-compression events.

No K1.6, wallet/RPC, program Rust, receipt/Aeneas, prover, verifier, or existing
dirty file is part of this checkpoint.

## Focused NUC evidence

Only the new target was built on `nuc.local`, in
`/home/dombarker/project-offloads/aspis-native-payment-terminal-20260826`,
under the established bounded zero-swap scope:

```text
systemd-run --user --scope --quiet \
  -p MemoryHigh=20G -p MemoryMax=24G -p MemorySwapMax=0 \
  /usr/bin/time -v env LEAN_NUM_THREADS=1 \
  /home/dombarker/.elan/bin/lake -Kjobs=1 build \
  AspisFormal.Pool.NativePaymentCompiledCopyLogUpV1
```

Green run: exit status 0, 2:28.49 elapsed, maximum RSS 15,657,356 KiB, and
zero swaps. No broad regression suite was run.
