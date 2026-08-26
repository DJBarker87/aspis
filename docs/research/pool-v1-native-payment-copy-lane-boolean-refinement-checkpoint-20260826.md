# Pool V1 native payment Copy-lane Boolean refinement checkpoint

Date: 2026-08-26

This checkpoint closes item 1 of the executable Copy LogUp boundary: the
compiled Rust `copy_lane` evaluator, restricted to a Boolean terminal point,
is the exact `nativeCompiledCopyLane` value used by the downstream Copy LogUp
theorem. It covers both native Tag-73 variants and does not change production
Rust.

## Kernel-checked result

The new module
`AspisFormal.Pool.NativePaymentCopyLaneBooleanRefinementV1` proves:

- `rustCopyRowSelectorAtBooleanPoint`: the source reads
  `high[row >> 4] * low[row & 15]`, after the already-checked source expansion
  loops, and obtains the exact Kronecker row selector;
- `rustCompiledEndpointValue_eq_native_at_selected`: the source
  `pattern_values` compression, sequential Copy tag, and all thirteen pinned
  affine patterns equal `nativeCompressTuple` on the selected trace row;
- `rustEndpointSlotValueAtBooleanPoint_eq_native` and
  `rustEndpointSlotWeightAtBooleanPoint_eq_native`: the two nested endpoint
  loops populate exactly the two producer and two consumer cells represented
  by `nativeSlotValue` and `nativeSlotWeight`;
- `rustCompiledCopyRowsAtBooleanPoint_eq_native`: the full Rust
  `CopyRowExtension` equals `nativeCompiledCopyRows`;
- `rustCopyResidual_eq_native`: Rust's denominator/numerator operation order
  is algebraically identical to `nativeCopyLocalResidual`;
- `rustCompiledCopyLaneAtBooleanPoint_eq_native`: the returned `(copy,
  copy_active)` pair is exactly `(nativeCompiledCopyLane,
  compiledCopyActiveField)`;
- `native_copyExact_of_rust_boolean_copy_lane`: successful exact Boolean-row
  source evaluations discharge the `copyExact` premise consumed by
  `native_copy_rational_balance_zero_of_accepted_terminal`;
- `extractedRustBooleanCopyLane_eq_native`: the same conclusion from a
  successful generated-root call satisfying the explicit source-equality
  interface.

The evaluator retains the production dimensions and ordering:

- 1,024 physical rows, factored as 64 high weights by 16 low weights;
- 16 C1 opening limbs and 13 generated Copy patterns;
- two producer and two consumer slots;
- 78 private-transfer or 75 withdrawal links, in checked-in array order;
- link tag `1090519040 + link_index`;
- checked-in active masks and the executable dense-complement/bit-scan
  `copy_active` implementation from the preceding checkpoint.

## Exact external boundary

`AuthenticatedC1BooleanOpenings trace selected openings` is the one
unavoidable PCS boundary:

```text
forall column, openings[column] = trace[selected][column]
```

The pure Copy evaluator has no hash, ROM, release, or proof-opening behavior,
so no such premise is hidden in this theorem. Authentication of that opening
vector by the terminal's C1 PCS remains outside this leaf.

The repository currently has no Charon/Aeneas generated harness rooted at the
private `payment_semantic_terminal::copy_lane` function. The module therefore
follows the existing source-refinement pattern explicitly:

- `ExtractedRustBooleanCopyLane.evaluate` is the expected generated root;
- `AeneasBooleanCopyLaneSourceEquality` says only that a successful generated
  call returns the concrete source-shaped evaluator;
- no theorem assumes arbitrary output, acceptance, PCS validity, or the
  desired semantic conclusion.

Producing and checking that narrow generated harness is the remaining source
correspondence boundary. Once present, `extractedRustBooleanCopyLane_eq_native`
consumes it directly.

## Source identity audit

The audited committed source revision is
`4ff47268a8b7a69aacd7917706520fc2bc016c80`, tree
`d8887822d0a0dda089e51ed2dba2c8fbce702b72`. It is the last commit touching
the evaluator, generated constants, or generator. The Lean module kernel-pins
these SHA-256 identities:

- `payment_semantic_terminal.rs`:
  `77e63ade4699b4805dd061aac6d42517c96f842274c713b98d1e48282baa0594`;
- `payment_semantic_terminal_constants.rs`:
  `8e042b07ed259f8b408d097453dff1a9f946b0e21423e0f746f84806bd3898d7`;
- `generate_pool_v1_payment_terminal_constants.rs`:
  `9f121ae21e9ce7d7db8300b794f12374a182d06a36da9412e0081078cf0240ed`.

It also pins the generated transfer registry/active fingerprints
`e3f3ce154db0f662` / `e858c4c0d4e22b94` and withdrawal fingerprints
`fb77daf4328c134e` / `e9de6f8fae7f1793`.

## Axiom and build audit

The focused module's `#print axioms` results contain only standard Lean
quotient/extensionality infrastructure:

```text
propext, Classical.choice, Quot.sound
```

`rustCopyResidual_eq_native` needs only `propext, Quot.sound`. There is no
`sorryAx`, `Lean.ofReduceBool`, `admit`, project-specific axiom, or
conclusion-shaped premise.

Only the new target was built on `nuc.local`, in
`/home/dombarker/project-offloads/aspis-native-payment-terminal-20260826`,
under the established bounded zero-swap scope:

```text
systemd-run --user --scope --quiet \
  -p MemoryHigh=20G -p MemoryMax=24G -p MemorySwapMax=0 \
  /usr/bin/time -v env LEAN_NUM_THREADS=1 \
  /home/dombarker/.elan/bin/lake -Kjobs=1 build \
  AspisFormal.Pool.NativePaymentCopyLaneBooleanRefinementV1
```

Green run: exit status 0, 10.96 seconds elapsed, maximum RSS 6,670,940 KiB,
and zero swaps. No broad regression suite was run.

No K1.6, wallet/RPC/finality, program Rust, receipt/Aeneas, prover, verifier,
or existing dirty file is part of this checkpoint.
