# Pool V1 native randomized extraction checkpoint (2026-08-26)

## Result

`AspisFormal.Pool.NativePaymentRandomizedExtractionV1` adds the next
kernel-checked layer above `NativePaymentTerminalBridgeV1`.

The module models the production native payment composition as exactly:

- four tower-packed Poseidon lanes at theta powers 0 through 3;
- twenty-four tower-packed semantic lanes at powers 4 through 27, containing
  94 source residuals and two zero padding coordinates;
- one extension-field Copy LogUp lane at power 28;
- a ten-coordinate, 1,024-row big-endian Boolean zerocheck evaluation; and
- the strengthened mu aggregate
  `constraintMLE + mu * helperSum + mu^2 * inactiveHelperSum`.

Tower-pack injectivity exposes every base-field coordinate after the native
29-lane row polynomial is shown identically zero.  The exact production degree
bounds are proved: a fixed nonzero theta vector has at most 28 cancelling
challenges, and a fixed nonzero mu coefficient triple has at most two.

## Explicit bad events

The extraction never treats unrelated failures as one opaque assumption.  It
uses three distinct propositions:

- `NativeMuAggregateCollision`: nonzero aggregate coefficients cancel at the
  sampled `mu`;
- `NativeZerocheckEvaluationCollision`: a nonzero theta-batched Boolean table
  evaluates to zero at the sampled ten-coordinate point;
- `NativeThetaLaneCollision`: the fixed selected nonzero 29-lane row
  polynomial evaluates to zero at `theta`.

`native_private_transfer_premises_or_collision` and
`native_withdrawal_premises_or_collision` return those events as separate
disjuncts before returning the exact premises consumed by the previous bridge.

## LogUp endpoint bridge

The module spells the value endpoint equations used by the native 78-link
transfer and 75-link withdrawal registries:

- input and change source-to-value-auxiliary aliases;
- the transfer-only recipient source alias;
- all three value-auxiliary-to-conservation aliases; and
- the row-870 partial-to-row-871 carried-partial alias.

`common_value_copy_and_conservation_of_endpoints` combines those endpoint
equations with the two local conservation residual equations at rows 870 and
871 to construct `CommonValueCopyAndConservation`.  No global LogUp balance is
silently equated with endpoint equality.

## Main theorems

- `all_native_row_residuals_zero_of_polynomial_zero`
- `native_theta_table_zero_outside_zerocheck_collision`
- `native_row_polynomials_zero_outside_theta_collision`
- `native_rows_vanish_of_accepted_randomized_terminal`
- `native_theta_collision_card_le_twenty_eight`
- `native_mu_collision_card_le_two`
- `common_value_copy_and_conservation_of_endpoints`
- `native_private_transfer_premises_of_accepted_terminal`
- `native_withdrawal_premises_of_accepted_terminal`
- `native_private_transfer_valid_of_accepted_terminal`
- `native_withdrawal_valid_of_accepted_terminal`
- `native_private_transfer_premises_or_collision`
- `native_withdrawal_premises_or_collision`

The two `*_valid_of_accepted_terminal` theorems invoke the exact row-to-relation
theorems from commit `d4c09d51`, so the current formal chain reaches
`PaymentRelationV1.ValidPrivateTransfer` and `ValidWithdrawal` once the
explicit residual-refinement and endpoint inputs are supplied.

`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for
the randomized extraction and capstone theorems.  There is no project-specific
axiom, `sorry`, `admit`, `#exit`, or `native_decide` shortcut.

## Exact remaining boundary

The following obligations remain deliberately outside this checkpoint:

1. connect accepted production masked-sumcheck/terminal openings to
   `NativeAcceptedRandomizedTerminal`'s exact aggregate equation;
2. prove the Rust `payment_semantic_oracle` and Poseidon evaluator refine
   `PrivateTransferResidualRefinement` and `WithdrawalResidualRefinement`,
   including the 94-source-lane order and the two final zero padding slots;
3. derive `CommonLogUpEndpointEquations` and
   `PrivateTransferLogUpEndpointEquations` from the native compiled registry's
   global rational balance outside pole, chi and tuple-compression events;
4. bind the typed trace projection to authenticated C1/H1 openings and the
   production M31/QM31 tower basis; and
5. supply Fiat--Shamir ordering/uniformity for the fixed-vector theta/mu root
   counts and a bound for the ten-variable zerocheck collision event.

The receipt encoder/Aeneas lane, wallet code and K1.6 are not part of this
checkpoint.

## Focused NUC evidence

The target was built only on the dedicated Linux build host, in
`<build-root>`, with:

```text
systemd-run --user --scope --quiet \
  -p MemoryHigh=20G -p MemoryMax=24G -p MemorySwapMax=0 \
  /usr/bin/time -v env LEAN_NUM_THREADS=1 \
  lake -Kjobs=1 build AspisFormal.Pool.NativePaymentRandomizedExtractionV1
```

Final run: exit status 0, 11.37 seconds elapsed, maximum RSS 6,486,312 KiB,
and zero swaps.  No broad regression suite was run.
