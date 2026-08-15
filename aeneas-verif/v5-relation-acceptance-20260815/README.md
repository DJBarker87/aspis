# V5 relation acceptance: Rust-to-Lean checkpoint

This bundle records the largest production-source extraction that the pinned
Charon/Aeneas toolchain currently accepts around the V5 relation checker and
its caller.  The extraction harnesses import the repository's Rust modules by
path; they do not copy or replace the verifier logic.

Tool versions:

- Rust: `nightly-2026-06-01`
- Charon: `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`
- Aeneas: `b59d5188c082f704a418c7cb4e52ad69328002d1`
- Lean: `v4.32.0`

## What is extracted

The checked generated files contain production definitions for:

- the indexed QM31 tail decoder and its QM31 decoder dependencies;
- `boundary_sum`;
- `evaluate`;
- the direct four-value branch of `WeightAccumulator::dot`;
- `CompactBTerminalWeights::new`;
- the complete per-block loop used by `CompactBTerminalWeights::fold`;
- `CompactBTerminalWeights::final_weights`; and
- `verify_mode9_relation_phase`, including its final four-coefficient equality
  gate.

The bundle also contains a checked, temporary source rewrite which replaces
the fixed two-sample and seven-coefficient loops in one relation round with
the corresponding explicit statements, and replaces the fixed four-round
outer loop with four calls.  The rewrite is applied only in the replay's
temporary directory.  Aeneas then translates the complete one-round body,
including the real byte reads, circle-versus-line branch, both weight updates,
claim arithmetic, seven coefficient reads, boundary check, polynomial
evaluation, and both folds.  The released Rust file and compiled program are
not changed.

`V5RelationAcceptanceSourceProof.lean` proves that, for every input and every
possible result of the still-opaque nested relation call, an extracted
`verify_mode9_relation_phase` success implies that the relation result's four
final coefficients equal the polynomial already accepted by FRI.  It also
proves that the caller returns that result's terminal claim.  This is a
universal theorem, not a test of selected traces.

`V5RelationTailDecoderProof.lean` proves two further source connections.  The
extracted `decode_indexed` body computes `offset + index * 16` and calls the
production QM31 decoder.  The already source-extracted QM31 decoder is then
proved equal to the maintained little-endian model for every one of the 58
sixteen-byte fields in every possible 928-byte relation tail.

The extraction-only layout wrapper reads the public constants from the
unchanged production module.  Its Lean translation proves the byte starts are
exactly `0, 64, 160, 288, 416, 864`, with total length `928`.  Separate
theorems prove that the exact index formula used by each circle-coordinate,
line-point, OOD-value, OOD-mix, polynomial, and final-coefficient read selects
the corresponding maintained field number.

`V5RelationRoundKernelProof.lean` removes the generated-loop uncertainty from
the two arithmetic calls made in every relation round.  For every possible
seven-coefficient polynomial, the extracted `boundary_sum` reads words zero
and four, adds them, and multiplies by four.  For every polynomial and point,
the extracted `evaluate` is exactly the six ordered multiply/add steps of
seven-coefficient Horner evaluation.  These are universal equalities over the
generated production field calls, not fixture tests.

`V5RelationTerminalKernelProof.lean` records the exact extracted route into
the main four-value terminal dot and proves that exhausting its generated
component iterator returns the accumulated value.  On the compact side, it
proves the exact ten production selectors, their fixed routing to output slots
zero and three, and that every successful `final_weights` call applies
`delta_scale` to slot three after the ten-block loop.  The theorem is
universal over the generated production operations; the standard-array
iterator functions that Aeneas emitted as declarations remain visible in its
printed axiom list.

## Exact remaining boundary

The production function
`verify_v5_relation_stress_with_additive` is present in Charon's LLBC, but the
pinned Aeneas translator rejects it with:

```text
Returns inside of nested loops are not supported yet
```

Therefore this bundle does **not** claim the remaining universal equality
between that four-round Rust loop and
`AspisV5RelationStressSourceBridge.runSourceRelationVerifier`.  The remaining
statement is split into two named parts:

1. every successful execution of the released nested loops is preserved by
   the checked fixed-loop rewrite; and
2. a successful translated round agrees with the maintained model for the
   decoder, field, sumcheck, and weight operations which were left opaque to
   Aeneas.

The Lean relation theorem below those two statements is proved.  The
statements themselves remain explicit implementation assumptions; the
temporary rewrite and generated body make them smaller and inspectable, but
do not turn source review into a formal proof.

Three additional translator limitations encountered while extracting the
supporting operations are kept explicit:

- the generic `WeightAccumulator::fold` translation fails on an internal
  bottom value;
- Aeneas emits an ill-typed mutable-iterator back-function for only the outer
  wrapper of the compact fold (the complete loop body is retained here); and
- Charon rejects the compact dot's standard-library `Zip` iterator trait
  clause.

No released verifier Rust was changed, and no test result is used in place of
one of these universal equalities.

## Replay

`replay-lean432.sh` pins the source blobs, temporary rewrite, and the Charon,
Aeneas, and Lean versions used by this checkpoint.  It regenerates the five
Solana-free roots that the pinned translators accept—the tail decoder, byte
layout, boundary check, polynomial evaluator, and main terminal dot.  It also
applies the fixed-loop rewrite in a temporary source tree and regenerates the
complete one-round definition.  Each result is compared with its checked Lean
snapshot.  The script then rebuilds the maintained relation-model dependency
chain, the production QM31 decoder, all ten generated modules, and all proof
files with Lean 4.32.

The comparison normalizes only source-root comments, the split Lean 4.32
Aeneas imports, and the pinned translator's signed annotation on wrapping
shift literals whose Rust callee takes `u32`.  It does not replace a generated
function body.

The compact-state and mode-9-caller snapshots are compiled and tied to the
pinned production and harness source hashes, but are not regenerated by this
script.  Their original extraction needs a temporary `solana-program` host
patch, and the exact remaining translator failures are listed above.  This
distinction is intentional: a successful replay does not claim that Aeneas
accepted the enclosing four-round function.

Example:

```bash
LEAN432_BIN=/path/to/lean-4.32.0/bin/lean \
AENEAS_LEAN_LIB=/path/to/patched-aeneas-lean-lib \
ASPIS_CHARON_REPO=/path/to/charon-cb50ff16 \
ASPIS_AENEAS_REPO=/path/to/aeneas-b59d5188 \
./aeneas-verif/v5-relation-acceptance-20260815/replay-lean432.sh
```

If this checkout does not already have the unchanged earlier `AspisFormal`
modules built, set `ASPIS_FORMAL_BUILD_ROOT` to a checkout with the same
release sources and a completed Lean build.

## Files

- `harness/`: Solana-free extraction roots for the relation checker and generic
  arithmetic helpers.
- `production-harness/`: extraction root for the unchanged program modules and
  the private compact state/caller.
- `extraction/`: the exact temporary fixed-loop rewrite used only during
  replay.
- `generated/`: normalized, Lean-4.32-compiling Aeneas output.
- `proof/`: the universal caller-success theorem and exact array-equality
  supporting lemmas, the universal 58-field decoder connection, and the
  complete extracted boundary/Horner and terminal-routing proofs.
- `replay-lean432.sh`: source-identity, regeneration, and proof replay.
