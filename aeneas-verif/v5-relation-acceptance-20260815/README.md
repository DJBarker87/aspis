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

## Exact remaining boundary

The production function
`verify_v5_relation_stress_with_additive` is present in Charon's LLBC, but the
pinned Aeneas translator rejects it with:

```text
Returns inside of nested loops are not supported yet
```

Therefore this bundle does **not** claim the remaining universal equality
between that four-round Rust loop and
`AspisV5RelationStressSourceBridge.runSourceRelationVerifier`.  The separately
extracted decoder, boundary evaluation, polynomial evaluation, main final dot,
compact fold body, compact final weights, and caller equality gate narrow that
boundary; they do not silently discharge it.

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

## Files

- `harness/`: Solana-free extraction roots for the relation checker and generic
  arithmetic helpers.
- `production-harness/`: extraction root for the unchanged program modules and
  the private compact state/caller.
- `generated/`: normalized, Lean-4.32-compiling Aeneas output.
- `proof/`: the universal caller-success theorem and exact array-equality
  supporting lemmas, plus the universal 58-field decoder connection.
