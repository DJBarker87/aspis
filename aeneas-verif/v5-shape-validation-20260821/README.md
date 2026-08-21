# V5 shape-validation proof

The production FRI verifier calls `CirclePcsShape::validate` before it uses a
shape. The earlier Lean proof had to assume one small fact about that call:

> If validation succeeds and returns `output`, then `output` is the original
> `input`.

This directory now proves that fact from the selected production Rust.

`formal_validate_shape` is an extraction-only wrapper around the unchanged
Rust method. Charon extracts that wrapper and the validator it calls. Aeneas
translates the extracted functions into Lean. The checked-in `ShapeSource`
files contain the resulting validator, including every rejecting check and
the loop that rejects duplicate tree tags.

`ShapePreservesInput.lean` proves two facts:

1. The loop can only return the shape assembled from the nine original input
   fields on its successful branch.
2. Therefore the complete generated validator can only return its input on
   success.

`ConsumerShapeClosure.lean` connects that result to the exact FRI-consumer
type and proves the previously requested
`ValidationSuccessPreservesShape` proposition. The consumer's former opaque
`validate` declaration is replaced, for this replay, by the generated
validator definition.

The final theorem reports only Lean's standard logical foundations:

```text
propext, Classical.choice, Quot.sound
```

It does not depend on a Kani result or a new mathematical or cryptographic
assumption. The small Kani harness remains as an optional independent check;
it is not used by the Lean theorem.

## Replay

First run the maintained V5 FRI-consumer replay. Then provide its output and
the matching Aeneas Lean library:

```sh
export V5_FRI_ACCEPTED_FOREST_REPLAY_OUT=/path/to/fri-replay-output
export AENEAS_LEAN_LIB=/path/to/aeneas/.lake/build/lib/lean
./aeneas-verif/v5-shape-validation-20260821/verify.sh
```

The replay compiles the generated validator, the return-value proof, the
consumer with the transparent validator, the affected consumer proofs, and
the final connection theorem under Lean 4.32.
