# Source-authentic CM31 multiplicative proofs

This lane checks the actual Rust implementations of `CM31::mul`,
`CM31::square`, and `CM31::mul_m31` from
`crates/aspis-core/src/field.rs`.

## Frozen inputs

- Aeneas: `b59d5188c082f704a418c7cb4e52ad69328002d1`
- Charon: `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`
- Rust: `nightly-2026-06-01`
- Lean: `v4.31.0`
- Audited `field.rs` blob: `96e8c04efee6a8231adb2723dac9acf975993e06`

The generated module records the source spans 245–253 (`mul`), 258–263
(`square`), and 266–271 (`mul_m31`).  Its namespace is isolated as
`AspisCoreCM31Multiplicative` because independent Rust extractions otherwise
redeclare the same Lean constants.

## Kernel results

- `AspisAeneasCM31Multiplicative.extracted_cm31_mul_corresponds`
- `AspisAeneasCM31Square.extracted_cm31_square_corresponds`
- `AspisAeneasCM31MulM31.extracted_cm31_mul_m31_corresponds`

Each theorem establishes canonical output limbs and exact semantics in
`QuadraticAlgebra (ZMod 2147483647) (-1) 0`.  The multiplication proof follows
the deployed three-product Karatsuba call graph; the square proof follows the
deployed two-product formula; scalar multiplication follows both deployed
coordinate multiplications.  Concrete negative theorems reject reversed
subtraction, a wrong Karatsuba cross-term sign, a missing square doubling, and
a scalar-limb swap.

These theorems report only `[propext, Classical.choice, Quot.sound]`; the
counterexample theorems require the smaller `[propext, Quot.sound]` set. The
hand-written files contain no `sorry`, `admit`, `axiom`, `unsafe`,
`native_decide`, or raised resource limits.

## Reproduction

Set `ASPIS_AENEAS_REPO` and `ASPIS_CHARON_REPO` to official clones at the
commits above, then run:

```sh
./scripts/extract-cm31-multiplicative.sh
./scripts/check-cm31-multiplicative.sh
```

The extraction script refuses any other `field.rs` blob and checks the exact
Rust source text, generated source spans, and LLBC declaration counts before
installing the staged artifacts.

## Boundary

This proves source blob `96e8c04e…` exactly, including the type-explicit
`31u32` shift counts. Their equivalence to the former unsuffixed literals is
recorded by the Rust/MIR evidence in `evidence/`. The generated project remains
replayable on pinned Lean 4.31, and the same correspondence theorem is also
replayed by the isolated Lean 4.32 arithmetic bundle in
`component-b-weight-at/arithmetic-lean432/`. Import into maintained
`AspisFormal` remains a separate integration step.
