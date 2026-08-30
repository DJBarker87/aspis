# Pool V1 native masked-terminal checkpoint (2026-08-26)

## Result

`AspisFormal.Pool.NativePaymentMaskedTerminalBridgeV1` closes the first
remaining boundary named by commit `8e4199a3`: an authenticated accepted
masked sumcheck for the exact native Boolean terminal now yields the
`NativeAcceptedRandomizedTerminal` aggregate consumed by
`NativePaymentRandomizedExtractionV1`.

The exact unmasked Boolean table is:

```text
eq(zerocheckPoint, row) * thetaBatch(row)
  + mu * H1(row)
  + mu^2 * (1 - copyActive(row)) * H1(row)
```

The masked table is `mask(row) + eta * real(row)`, matching the production
Rust terminal's `state_only_selected_mask_value + eta * original`.  The Lean
kernel proves that its Boolean sum is exactly:

```text
nativeConstraintMLE
  + mu * tableSum(H1)
  + mu^2 * tableSum((1 - copyActive) * H1)
```

Nonzero `eta` and equality of the mixed sum with the authenticated mask sum
cancel the mask and produce precisely `NativeAcceptedRandomizedTerminal`.
There is no conclusion-shaped terminal or aggregate premise.

## Production pins

The checkpoint pins the production dimensions and ordering used by
`payment_semantic_terminal.rs`:

- 1,024 Boolean rows and ten big-endian zerocheck coordinates;
- 16 C1 columns, ten mask-only C1 columns, H1 and G: 28 selected columns;
- three selected opening points and 84 selected claims;
- four Poseidon theta lanes at powers 0 through 3, 24 semantic lanes at
  powers 4 through 27, and Copy LogUp at power 28;
- ten degree-27 sumcheck rounds, 28 QM31 coefficients per round, 16 bytes per
  coefficient and 448 bytes per round message;
- degree-two mu strengthening, 13 copy patterns, 78 transfer copy links and
  75 withdrawal copy links;
- one fixed selector allocation of 1,280 bytes; and
- active-row mask fingerprints `0xe858c4c0d4e22b94` for transfer and
  `0xe9de6f8fae7f1793` for withdrawal.

## Main theorems

- `native_masked_terminal_layout_pinned`
- `tableSum_nativeStrengthenedUnmaskedTerminalTable`
- `native_accepted_randomized_terminal_of_masked_boundary`
- `native_accepted_randomized_terminal_of_authenticated_wire`
- `native_aggregate_or_three_named_failures`

The last theorem is the strongest deterministic statement.  Given an
accepted ten-round wire and a fixed reference trace for the exact native
masked table, it returns one of four alternatives:

1. the exact native randomized-terminal aggregate;
2. `MaskInitialClaimAuthenticationFailure`;
3. `FixedTerminalOpeningAuthenticationFailure`; or
4. `TenRoundRepair`.

Thus commitment/opening authentication and the adaptive Fiat--Shamir repair
event are not silently assumed.  The outside-repair theorem takes the two
literal authentication equalities in `NativeMaskedTerminalAuthentication`
and a separately named `¬ TenRoundRepair`; the latter is exactly where a
hash/ROM argument belongs.

`#print axioms` reports no project axiom, `sorryAx`, `Lean.ofReduceBool`, or
other conclusion-shaped assumption.  The nontrivial theorems use only
`propext`, `Classical.choice`, and `Quot.sound`; the dimension pin theorem has
no axioms.

## Exact remaining boundary

This checkpoint deliberately leaves the following obligations explicit:

1. project a successful native Tag-73 Rust parse/control-flow execution into
   `AcceptedProductionTenRoundWire`, including the exact native transcript
   schedule and nonzero-eta rejection;
2. authenticate the initial mask-sum claim and the fixed terminal opening
   against the committed native polynomial/PCS;
3. prove that the Rust Boolean restriction of
   `evaluate_pool_v1_*_selected_masked_terminal_compiled_tag73_v1` is the
   modeled table, including equality-value bit order, the compiled
   transfer/withdrawal active-row mask, H1, and the 29-lane theta order;
4. supply the adaptive Fiat--Shamir/ROM argument that bounds the ten
   degree-27 repair events rather than merely naming them; and
5. continue the separate residual-refinement and LogUp endpoint obligations
   already listed by `8e4199a3` after the aggregate has reached
   `NativePaymentRandomizedExtractionV1`.

Wallet code, K1.6, receipt/Aeneas work and existing dirty files are outside
this checkpoint.

## Focused NUC evidence

Only the new target was requested, on the dedicated Linux build host in
`<build-root>`,
under a bounded zero-swap user scope:

```text
systemd-run --user --scope --quiet \
  -p MemoryHigh=20G -p MemoryMax=24G -p MemorySwapMax=0 \
  /usr/bin/time -v env LEAN_NUM_THREADS=1 \
  <lean-toolchain>/bin/lake -Kjobs=1 build \
  AspisFormal.Pool.NativePaymentMaskedTerminalBridgeV1
```

Final run: exit status 0, 10.45 seconds elapsed, maximum RSS 6,497,388 KiB,
and zero swaps.  No broad regression suite was run.
