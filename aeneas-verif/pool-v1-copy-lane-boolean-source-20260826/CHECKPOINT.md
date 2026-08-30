# Native Pool V1 Boolean Copy-lane source checkpoint

This bundle targets the remaining
`AeneasBooleanCopyLaneSourceEquality` boundary.  It is intentionally limited
to the production native payment `copy_lane` Boolean restriction and the
minimal reachable field operations, tables, and loop helpers.

## Authenticated source root

`pool_v1_payment_copy_lane_boolean_extraction_v1` is a thin production-side
extraction entry with the exact raw Rust arguments:

- `variant: u8` (`0` private transfer, `1` withdrawal; every other byte is
  rejected);
- `selected_row: u16` (values outside the 1,024-row terminal are rejected);
- sixteen `QM31` C1 openings; and
- `h1_z`, `lambda`, and `chi` as `QM31` values.

The wrapper constructs the exact high/low one-hot selector arrays and invokes
the actual private `copy_lane`.  It does not implement the registry, endpoint
accumulation, active-mask evaluator, or residual a second time.  The focused
Rust test `boolean_extraction_wrapper_is_the_private_copy_lane` compares both
valid variants at boundary and representative rows with the private call and
also checks both rejection branches.

The extracted Charon root is
`crate::pool_v1::payment_semantic_terminal::pool_v1_payment_copy_lane_boolean_extraction_v1`.
The extraction includes `aspis_core::field`, so every reached M31/CM31/QM31
operation is transparent.  Aeneas produced only `Types.lean` and `Funs.lean`;
there is no generated external-function template and no field-operation axiom.

## Generated normalization

`normalization/normalize-generated.pl` performs only these Lean-environment
normalizations:

1. replace the umbrella `Aeneas` import with the exact `Aeneas.Std` and Rust
   attribute imports used by the focused Lean 4.32 environment;
2. give the generated types module its required discriminant import and rename
   the split-module import to the checked namespace;
3. remove only the derived `global_simps` attribute from enormous literal
   constants, retaining the generated definitions, `irreducible`, and
   `rust_const`; and
4. change the three generated shift-count annotations `4#i32` to `4#u32`.
   Rust infers `u32` for these `Usize`/`U16` shifts; the pinned translator emits
   only the annotation incorrectly.  The operation and literal value are
   unchanged.

After those normalizations, `split-generated-funs.pl` places the 55 generated
declaration blocks into sequential modules and replaces `Funs.lean` with an
import-only facade. Ordinary declarations retain their names, attributes, and
bodies. The two 13-pattern registry constants are definitionally factored:
each of the 15 repeated base arrays and each individual pattern record receives
its own private helper definition, while the original public constant remains
an `Array.make` of those helpers. This produces 111 small sequential modules
without changing either public constant's value. It prevents Lean from
retaining every large literal registry array in one elaborator process.

## Proof decomposition

The kernel work is split so the exact source boundary can be checked before
the large loop refinement:

1. `PoolV1CopyLaneBooleanRoot.lean` adapts the generated wrapper directly to
   `ExtractedRustBooleanCopyLane`.  Its first target is
   `generatedEvaluate_success_iff`.
2. `PoolV1CopyLaneBooleanFieldSemantics.lean` proves canonical raw-field
   execution agrees with the exact QM31 tower for add, subtract, multiply,
   scalar multiply, and lift.
3. `PoolV1CopyLaneBooleanSourceBridge.lean` pins every generated pattern,
   link, and active mask before refining the power/pattern loops, the two
   endpoint accumulators, `copy_residual`, and `copy_active` into
   `rustCompiledCopyLaneAtPoint`.
4. The final theorem will instantiate
   `AeneasBooleanCopyLaneSourceEquality canonicalQM31 qm31View
   generatedRustBooleanCopyLane`; authenticated C1 openings remain the
   explicit downstream PCS boundary.

No hash/PCS security premise is used by this source evaluator proof.  No
terminal-acceptance conclusion is assumed.

## Focused replay order

The next deliberately small Lean target is:

```text
PoolV1CopyLaneBooleanGenerated/Types.lean
PoolV1CopyLaneBooleanGenerated/Funs.lean
PoolV1CopyLaneBooleanRoot.lean
```

Only after that target is green should the field-semantics module run. Heavy
Lean replay uses `LEAN_NUM_THREADS=1` in a dedicated build-host cgroup with
`MemoryHigh=18G`, `MemoryMax=20G`, and `MemorySwapMax=0`. The full source bridge
is not part of either small target.

The extraction itself previously completed in 8.13 seconds at 494,300 KiB
maximum RSS, and Aeneas translation completed in 2.01 seconds at 288,476 KiB,
both with zero swaps. Generated `Types.lean` compiled in 1.21 seconds at
2,422,184 KiB with zero swaps.

The original monolithic `Funs.lean` process was stopped after 22:50:20 wall
time, 24,315,452 KiB resident memory, and 90,398,497 `memory.high` events; it
had produced no `Funs.olean`. The retained proof uses the smaller symbolic
split described above; raw process and journal snapshots are intentionally
omitted.

The clean split-generated replay passes all 111 modules plus the `Funs.lean`
facade in 2:37.79 wall time at 2,635,008 KiB maximum RSS with zero swaps. The
subsequent root replay also passes `PoolV1CopyLaneBooleanRoot.lean` in 2:15.72
at 6,963,840 KiB maximum RSS with zero swaps. Its complete `#print axioms`
output for `generatedEvaluate_success_iff` is:

```text
[propext, Classical.choice, Quot.sound]
```

Both clean runs used an 18/20 GiB, zero-swap cgroup. The figures above and the
printed axiom set are the retained replay record.
