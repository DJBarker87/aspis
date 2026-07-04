# ML-DSA Solana STARK Stage B Keccak Framework Gate

Date of check: `2026-04-20`

Question:

- does pinned `Winterfell 0.12` expose a binary-field or other narrow-column field mode that can
  rescue a Keccak AIR under the framework's trace-width limit?

## Source Checks

Primary source files inspected:

- `winter-air 0.12.3`
- `winter-math 0.12.0`
- `winterfell 0.12.0`
- local pinned Yano-derived prover / verifier code

## Verified Findings

### 1. Winterfell 0.12 imposes a hard 255-column trace cap

`TraceInfo::MAX_TRACE_WIDTH` is `255`, and this cap applies to the total width across main and
auxiliary trace segments.

Implication:

- a naive Keccak-f bit-sliced layout with one bit per column for the full `1600`-bit state does
  not fit in Winterfell 0.12 at all

### 2. Winterfell 0.12 does not expose a binary-field backend

The exposed base fields in `winter-math 0.12.0` are:

- `f62`
- `f64`
- `f128`

The exposed extensions are:

- quadratic extensions over supported base fields
- cubic extensions over `f62` and `f64`

I did **not** find source evidence for:

- binary fields
- `GF(2^k)` backends
- `M31`
- tower fields
- cargo features selecting alternate field families

Implication:

- the natural "switch to a binary-field Keccak AIR inside the same pinned Winterfell stack" path
  is not available from the exposed `0.12` feature surface

### 3. Field choice is a type-level code choice, not a cargo-feature switch

`winterfell 0.12.0` crate features are limited to:

- `async`
- `concurrent`
- `std`

`winter-math 0.12.0` crate features are limited to:

- `concurrent`
- `std`

There is no field-family feature flag exposed in the pinned crates.

Implication:

- choosing `f62`, `f64`, or `f128` happens in AIR/prover code by selecting the concrete
  `BaseElement` type
- there is no hidden cargo-feature route to a binary-field Keccak backend

### 4. The local Yano-derived stack currently uses `f128::BaseElement`

The pinned local prover / verifier and related host probes are all instantiated over
`math::fields::f128::BaseElement`.

Implication:

- even the already-vendored Solana path is not set up around a smaller prime field
- moving to `f62` or `f64` would already be a measurable stack change
- moving to a binary field would require framework work beyond what the pinned stack exposes

## Stage B Interpretation

This is a framework-level feasibility constraint, not a cryptographic one.

What it rules out directly:

- the obvious one-row-per-round, one-bit-per-column Keccak AIR inside pinned `Winterfell 0.12`

What it does **not** rule out yet:

- a serialized Keccak AIR over the exposed prime fields
- a lane-packed / decomposition-heavy arithmetization that stays under `255` columns
- a version change away from pinned `Winterfell 0.12`

What it does rule out as an in-scope shortcut:

- "just switch Winterfell 0.12 to a binary-field Keccak mode"

## Gate Decision

`AMBER-BLOCKED`

Reason:

- a straightforward Keccak AIR does not fit the framework width cap
- the most obvious rescue path, binary-field packing within the same pinned framework, is not
  exposed by the checked `Winterfell 0.12` field surface
- the remaining in-scope path is a serialized prime-field Keccak layout, which still needs
  explicit row/column and proof-size modeling before the project can proceed honestly

## Consequences For Project Framing

If the serialized prime-field path also fails the proof-size envelope, a scoped negative result is
already defensible at the framework level:

- `Pinned Winterfell 0.12 does not expose a Keccak-friendly field/layout surface that keeps`
  `ML-DSA-44 verification plausible under the target Solana constraints.`

## Immediate Next Work

1. Record this framework constraint as a first-class Stage B artifact.
2. Decide whether to:
   - stop with a scoped framework-level negative result, or
   - measure one explicit serialized prime-field Keccak candidate under the `255`-column cap.
3. Treat any move to a different Winterfell version or a different STARK framework as a scope
   deviation, not as a silent continuation of the same plan.
