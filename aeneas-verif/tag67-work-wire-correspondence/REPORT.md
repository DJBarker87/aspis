# Tag-67 work/wire source-authentic continuation

Status: the Tag-67 work-wire projection and six-step verifier correspondence
close on Lean 4.32.  The maintained wire view is existentially constructed
from the six generated `U64` reads; no arbitrary `WorkWireView` or
`ExactWorkWireProjection` premise remains.  The extracted digest predicate
equals the maintained predicate, and the extracted six-deep short-circuit
chain accepts iff the six positioned check/absorb/next steps execute.  The
only remaining boundary is the unavoidable `HashFn` application equation
identifying the actual computed digest with the maintained arbitrary hash on
`state, DOM_GRIND, nonce_le64`.

This is feature-gated candidate code (`v5-cu-probe`), not the deployed v4
verifier.  Nothing here establishes selector least-good enforcement,
Fiat--Shamir security, v5 ZK, or freeze readiness.

## Authenticated source and tools

- workspace HEAD: `27e8265d28de88e7967626a2d2432ef161fb4f49`
- source status: untracked (`?? programs/aspis-verifier/src/v5_cu_probe.rs`)
- source SHA-256: `1c1df4c8c1d86de2d2d950002effdd7151abf50b5a6e514fac576507c9323c21`
- full untracked-source binary-diff SHA-256:
  `c6d520a1fa0a2591e19a5e953902f81660cf397649abc130260c2951a5655aee`
- Charon commit: `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`
- Charon binary SHA-256:
  `8e422e8a0624bb12314210b655d5788f9e32a597cae17f4e402006e5dc0391a2`
- Aeneas commit: `b59d5188c082f704a418c7cb4e52ad69328002d1`
- Aeneas binary SHA-256:
  `99800c72be8f65a0e3357afd4905c6556d0db9c3ef41601991685b0c6e15c2c4`
- Rust: `nightly-2026-06-01`
- retained replay: Lean `4.32.0`

The source body embedded in `llbc/tag67_work_wire.llbc` hashes to the exact
current source SHA above.

## Successful extraction

Owning package and feature:

```text
aspis-verifier --features v5-cu-probe,no-entrypoint
```

The exact Charon matcher was:

```text
crate::v5_cu_probe::v5_work_wire_magic_is_valid,
crate::v5_cu_probe::v5_work_wire_u64,
crate::v5_cu_probe::project_v5_work_wire,
crate::v5_cu_probe::v5_batch_work_difficulty,
crate::v5_cu_probe::v5_fold_work_difficulty,
crate::v5_cu_probe::v5_final_work_difficulty,
crate::v5_cu_probe::v5_fold_work_record,
crate::v5_cu_probe::v5_batch_work_record,
crate::v5_cu_probe::v5_final_work_record,
crate::v5_cu_probe::v5_fold_work_absorb_input,
crate::v5_cu_probe::v5_batch_work_absorb_input,
crate::v5_cu_probe::v5_final_work_absorb_input,
crate::v5_cu_probe::v5_relation_final_zero_tail_is_valid,
crate::v5_cu_probe::v5_query_selector_is_valid
```

Charon reports `has_errors=false` and 35 ordered declarations.  Pinned Aeneas
generates a nonempty `Tag67WorkWire.lean`.  Principal exact source spans in
`programs/aspis-verifier/src/v5_cu_probe.rs` are:

- magic 370--380; LE64 reader 383--394; projector 400--412;
- difficulties 613--631; records 634--657;
- executed absorb-input helpers 660--678;
- zero tail 745--757; selector 931--933.

The raw generated module retains the exact Aeneas names under
`aspis_verifier.v5_cu_probe`; the mechanically normalized Lean-4.32 replay uses
the same names and definitions without generated raised proof limits.

## Strongest retained statements

`Tag67WorkWireProof.lean` proves directly about generated definitions:

- offsets 11048, 11080, 19127, and 19135;
- difficulties 37, 34/33/30/25, and 32, including out-of-range fold 4;
- batch/final LE64 records;
- fold/batch/final absorb labels 20/28/5 and payload order;
- selector acceptance exactly for values below 3, with rejection teeth 3 and
  255;
- distinct fold slots and batch/final slots/difficulties;
- `extracted_projection_preserves_exact_order`, which consumes executions of
  the generated LE64 reader and proves the generated projector returns folds
  0,1,2,3, then batch, then final, plus selector.

`Tag67WorkWireMaintainedCapstone.lean` instantiates the maintained
`serializeRuntimeExact` byte list and proves the generated
offset/difficulty/label maps equal the maintained `WorkKind` maps.

`Tag67WorkWireLE64Bridge.lean` proves `generated_read_zero`, generated
`U64::from_le_bytes` round-trip, `nonceLEByte(s)` correspondence, and
`BitVec.fromLEBytes` recovery.  Its capstone
`generated_acceptance_constructs_exact_work_wire_view` consumes only actual
generated guard/read executions, existentially builds the maintained view,
and proves both `projectWorkWire = canonicalWorkWire` and the exact generated
projector result.

`Tag67DigestPredicateProof.lean` proves
`extracted_digest_predicate_iff_maintained` plus all-six difficulty boundary,
zero-work, and byte-reversal teeth.  `Tag67SixActualStepsExtractedProof.lean`
connects the generated `Result<Option<Array 6>>` chain to the maintained
six-step trace; `Tag67SixActualStepsProof.lean` exposes exact before/after
states and next results in batch/fold0--3/final order.

`Tag67WorkVerifierClosure.lean` discharges the internal computed-boolean
boundary with the extracted digest theorem.  `acceptanceIffExactSixSteps` has
no correspondence premise.  `exactGrindingHashInput` consumes only the
single concrete hash-application equation, and
`tag67AcceptedWireAndVerifierClosure` composes the existential wire view with
the six-step verifier.

All old and new exported theorems have `#print axioms` audits; direct Lean-4.32
replay closes in `{propext, Classical.choice, Quot.sound}` or less. Retained
handwritten/generated-normalized sources contain no `sorry`, `admit`,
`native_decide`, `axiom`, `unsafe`, or raised heartbeat/recursion limits.

## Exact remaining seams

1. `ExactRustAcceptedWorkWireProjection` is eliminated from the owned closure:
   no theorem takes that seam, an arbitrary view, or
   `ExactWorkWireProjection`. Generated acceptance constructs the view.
2. `ExactRustWorkVerifierCorrespondence` is reduced to exactly:

   ```text
   actual Transcript grinding digest state nonce
     = rustHash state ((3 : Byte) :: nonceLEBytes nonce)
   ```

   This is the irreducible pinned-Aeneas Arrow boundary. `HashFn` remains an
   arbitrary supplied function; SHA/random-oracle faithfulness is neither
   assumed nor claimed.

## Tests

- Differential extraction tests: 3 passed, 0 failed.
- Focused core grinding tests: 2 passed, 0 failed.
- Proof-facing six-step Rust tests: 3 passed, 0 failed.
- Pinned Charon/Aeneas extraction and translation passed for both the digest
  predicate and six-step helper.
- Full `aspis-verifier` library test with
  `v5-cu-probe,no-entrypoint`: see `logs/rust-full-lib.log`.
- Charon/Aeneas core logs, grind blocker log, and Lean replay evidence are
  retained under `logs/`.
- The wire bridge, digest predicate, extracted six-step chain, coordinator
  closure, and final capstone audit compile at Lean 4.32 default limits with
  warnings as errors and only `{propext, Classical.choice, Quot.sound}`.
