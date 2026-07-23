# Component-C runtime downstream correspondence

## Verdict

**SOUND-CONDITIONAL; SOURCE-AUTHENTIC SCHEDULE SAFETY AND FOLD PRIMITIVES
CLOSED.**  The current feature-gated Component-C runtime implementation has
source-authentic Charon/Aeneas definitions for its dynamic wire packer,
schedule validator, and complete relation/fold evaluator.  The accepted Lean
4.32 proofs establish:

- the exact `40 + 4*(n1+n2+n3)` runtime row grammar and value order;
- exact query-derived later-fibre counts and ordinal order;
- the executable `len <= 18` and layer-range checks in both directions;
- exact four-value later-fibre release order;
- the extracted arity-four line and circle folds against the maintained field
  model, using the independently authenticated M31/CM31/QM31 arithmetic.

The strongest maintained capstone,
`generated_validated_schedule_dimension_and_direct_model`, no longer takes
free range or count premises.  It consumes the three actual generated
validator successes.  Its only remaining executable-math interface is
`RustRuntimeArithmeticCorrespondence`: the outer relation-accumulator and
runtime evaluator must still be composed with the maintained deployed map.

This module remains candidate v5 code behind `v5-mask`.  It is not reachable
from production tag-67 dispatch and this report makes no freeze, deployed-v4,
zero-knowledge, PCS, hash/RO, or release claim.

## Rust change

`crates/aspis-prover/src/v5_component_c_runtime.rs` now validates every
derived later-layer vector at the schedule boundary:

```text
layer 1: count <= 18, fibre < 32768
layer 2: count <= 18, fibre < 8192
layer 3: count <= 18, fibre < 2048
```

The three limits are derived from `V5_LAYER_ZERO_LEAVES` and the shared
`CIRCLE_LINE_QUERY_SHIFTS`, then guarded by compile-time equalities.  This does
not change any valid schedule, transcript, proof byte, or arithmetic result;
it rejects only malformed or regressed derived schedules.  The focused Rust
test exercises all three success paths plus count and range failures.

Current source SHA-256:

```text
327be85bea18701dcb5eb9ab7d6303f3453b2e6fbc6a1de9a67b414ae87f9d76  crates/aspis-prover/src/v5_component_c_runtime.rs
8c3fe1a4a60d037e7c6bd251ac451fd314991528f3831f7f892c5fb376da821a  crates/aspis-core/src/circle_line_merkle.rs
```

No verifier, protocol, Cargo manifest, production dispatch, staging, commit,
or push was performed by this lane.

## Extraction provenance

```text
HEAD at final replay  27e8265d28de88e7967626a2d2432ef161fb4f49
Charon                cb50ff16b9f1066b8a97dc06da704de2da2fa41c
Aeneas                b59d5188c082f704a418c7cb4e52ad69328002d1
Rust                  nightly-2026-06-01
Generated backend     Lean 4.31
Authenticated replay  Lean 4.32
```

Current accepted artifacts:

```text
25972bda8bf819ba833cba44959aed66da7e8647329e32d758b1d25add4999b3  llbc/runtime_component_c_wire.llbc
39c71967074f797f482316317a542f5bfc3acae4a80b9909c7513acc3ac0b24c  llbc/runtime_evaluator_full_v28.llbc
4188544dd53c3b328dcc47910c1f7fb800c81b884cb3c87d73d0067d7e4c366f  llbc/runtime_schedule.llbc
f14cab955f3d701f1ed85cada76db1d7b31582f71833895e63c4bde8edc93b25  generated/runtime_component_c_wire/RuntimeComponentCWire.lean
34e41c8153010cf029c1fafb2c3411f4e7ed9daa6ff72cdd8cb7afa8093cb6f5  generated/runtime_evaluator_full_v28/ComponentCRuntimeGenerated/Types.lean
0fb293344b82f0efb4aa424dfdd73c70b32ad18cc45c80f636c3a70ebb4ca8e2  generated/runtime_evaluator_full_v28/ComponentCRuntimeGenerated/FunsExternal.lean
b8ff93734425e396472b58fca6b1391ff92f0f2629d47349a82c8a930aaa0399  generated/runtime_evaluator_full_v28/ComponentCRuntimeGenerated/Funs.lean
```

The combined wire LLBC has 45 ordered declarations.  The full evaluator LLBC
has 339.  Both report `has_errors = false` and embed the current
`v5_component_c_runtime.rs` byte-for-byte.  The schedule LLBC similarly embeds
the current `circle_line_merkle.rs` byte-for-byte.

The normalized generated modules differ from raw Aeneas output only by narrow
Aeneas imports, removal of generated resource limits, the documented generated
shift-count/type adapters, one generated boolean equality repair, and the
filled external bodies.  The accepted proof closure contains no external
axiom from those templates.  Raw templates are retained as provenance but are
not imported by an accepted theorem.

## Kernel results

The proof bundle is `proof/`:

- `RuntimePackerCorrespondence.lean`: dynamic row count, all six row segments,
  value dispatch, packer loop, and the concrete 76-vs-256 obstruction.
- `RuntimeScheduleCorrespondence.lean`: authentic query output to maintained
  counts and ordinal order.
- `RuntimeScheduleValidatorCorrespondence.lean`: generated validator success
  iff the exact count/range contract needed by the maintained finite types.
- `RuntimeValidatedScheduleBridge.lean`: the three actual validator calls
  discharge `GeneratedLaterFibresInRange` and all q18 count bounds.
- `RuntimeEvaluatorSourceAuthentic.lean`: exact message/codeword shape errors
  and runtime row count from the real evaluator entrypoint.
- `RuntimeFoldPrimitiveReduction.lean`: generated line/circle folds reduced to
  the precise primitive laws they call.
- `RuntimeFoldPrimitiveInstantiation.lean`: those primitive laws instantiated
  from authenticated M31/CM31/QM31 source correspondences; the prepared line
  and circle fold theorems are unconditional.
- `RuntimeLaterFibreCorrespondence.lean`: exact four consecutive released
  values for every runtime later fibre.
- `RuntimeDownstreamMaintainedBridge.lean`: the maintained conditional direct-C
  capstone with schedule safety closed by generated execution.

`check-lean432.sh` re-authenticates tool commits, LLBC/source byte identity,
artifact hashes, rebuilds every accepted generated module and proof with one
Lean worker, and checks all 55 explicit `#print axioms` results.  Every result
is contained in `{propext, Classical.choice, Quot.sound}`.  Accepted files have
no `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `sorryAx`,
`ofReduceBool`, or raised handwritten resource limits.

## Exact remaining graph

```text
generated query schedule                         CLOSED
  -> exact runtime counts/order                  CLOSED
  -> generated count/range validation            CLOSED

generated runtime evaluator                     CLOSED as source definition
  -> shape and dynamic row grammar               CLOSED
  -> later-fibre four-slot release               CLOSED
  -> line/circle fold primitive arithmetic       CLOSED
  -> relation accumulator + outer evaluator
       equals maintained deployedEvaluate        OPEN
       (RustRuntimeArithmeticCorrespondence)

validated schedule + arithmetic correspondence
  -> maintained runtime dimension/direct model   KERNEL-CHECKED CONDITIONAL
```

The remaining interface is correspondence work over the current construction,
not permission to invent a new masking construction or theorem.  It includes
the outer `WeightAccumulator`/relation polynomial composition and the exact
connection to the maintained runtime evaluator.  It does not re-open schedule
counts, schedule order, fibre ranges, fixed-256 layout, or the fold primitive
algebra.

## Validation

- focused runtime validator Rust test: pass (1/1);
- `rustfmt --edition 2021 --check` on the owned Rust file: pass;
- current LLBC embedded-source comparisons: pass;
- generated Lean 4.32 module replay: pass;
- all accepted proof files at default handwritten limits: pass;
- 55 explicit axiom audits: allowed trio only;
- forbidden-token scan: pass;
- `git diff --check`: pass;
- staged-file count: zero at lane handoff.
