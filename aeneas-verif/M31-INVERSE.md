# Source-authentic M31 inverse proof

This lane checks the actual production `M31::inv` addition chain and its
`square_n` iterator loop from `crates/aspis-core/src/field.rs`.

## Frozen inputs

- Aeneas: `b59d5188c082f704a418c7cb4e52ad69328002d1`
- Charon: `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`
- Rust: `nightly-2026-06-01`
- Lean: `v4.31.0`
- Audited `field.rs` blob: `96e8c04efee6a8231adb2723dac9acf975993e06`

The generated `M31::inv` declaration records source lines 154–170 and the
complete source text is authenticated by the extraction script.

## Kernel result

`AspisAeneasM31Inverse.extracted_m31_inv_corresponds` proves, for every
canonical nonzero M31 word, that:

- the actual generated Rust function succeeds;
- its complete 17-node multiplication/squaring trace runs as extracted;
- every intermediate word remains canonical;
- every intermediate carries the exponent dictated by the Rust schedule;
- the final exponent is exactly `2^31 - 3 = P - 2`;
- the returned residue is the inverse in `ZMod P`; and
- both left and right cancellation equations equal one.

The generic theorem
`AspisAeneasM31Inverse.extracted_square_n_loop_corresponds` proves the actual
generated iterator loop for every representable count, rather than merely
checking its deployed counts 2, 4, and 8.  The separate theorem
`extracted_m31_inv_zero_assertion_failure` proves that input zero reaches
Aeneas's `Error.assertionFailure`, while
`extracted_m31_inv_assertion_failure_iff_zero` proves the converse on every
canonical representative. Concrete negative theorems reject the wrong `t28`
dependency and show that it changes the final exponent.

All reported axioms lie in `[propext, Classical.choice, Quot.sound]`; the
natural-number negative tooth uses only `[propext]`.  The hand-written proof
contains no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `extern`,
`native_decide`, `sorryAx`, `ofReduceBool`, or raised resource limits.

## Authenticated LLBC-order projection

Pinned Charon cannot select an inherent method by receiver type.  The wildcard
`_::inv` extraction reaches later CM31/QM31 inverse functions, and Aeneas 0.2
cannot translate the function-pointer argument in `CM31::inv_with`.

The extraction script therefore authenticates the unique production M31
inverse by exact source span and source-text hash, then keeps the first 35
groups of Charon's already-topological `ordered_decls` schedule, ending at that
non-recursive declaration.  It mechanically proves that:

- the target is uniquely group 34 of the 49-group wildcard schedule;
- the selected schedule is literally the raw schedule prefix;
- every other serialized declaration map/body/span/source string is unchanged;
- the prefix excludes all later extension-field inverse roots; and
- pinned Aeneas translates and Lean compiles the resulting model.

This is an authenticated ordering projection, not untouched wildcard LLBC.
Raw LLBC byte hashes are not stable because Cargo paths and map serialization
vary; the semantic maps, schedule, source, and generated Lean are the guarded
objects.

## Reproduction

Set `ASPIS_AENEAS_REPO` and `ASPIS_CHARON_REPO` to official clones at the
commits above, then run:

```sh
./scripts/extract-m31-inverse.sh
./scripts/check-m31-inverse.sh
```

The checker rebuilds every generated/proved dependency, machine-rejects any
unapproved axiom report or forbidden construct, and requires reports for the
loop, assertion, negative tooth, and capstone.

## Remaining boundaries

The independent Lean 4.32 `V5M31InverseAdditionChain` result was used only as a
schedule cross-check; it is not silently imported into this source-authentic
proof. The generated Lean 4.31 theorem chain is separately replayed by the
isolated Lean 4.32 arithmetic bundle in
`component-b-weight-at/arithmetic-lean432/`.

This proof authenticates source blob `96e8c04e…`, including the type-explicit
`31u32` shift counts. Their equivalence to the former unsuffixed literals is
recorded by the Rust/MIR evidence in `evidence/`.
