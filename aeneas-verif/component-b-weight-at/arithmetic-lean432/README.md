# Lean 4.32 shared-field replay

This directory is the durable Lean 4.32 replay of the source-authentic
M31/CM31/QM31 arithmetic used by the Component-B `weight_at` extraction.  It
contains no object files or Lake cache.  `SOURCE_MANIFEST.sha256` authenticates
all 42 source modules; the manifest itself has SHA-256
`7832fe9d7ed7ce56aedc2c568d40354330790af6197720edb58a2f6b0e438a01`.

## What is now checked by the Lean 4.32 kernel

The Lane-5 correspondences that were previously checked only by Lean 4.31
are replayed unchanged at the theorem level:

- `mul_by_r`, `QM31::mul`, optimized `QM31::square`, `QM31::mul_m31`, and
  `QM31::mul_cm31`;
- `M31::half`, `CM31::half`, and `QM31::half`;
- `M31::mul_pow2`, `M31::reduce_u62`, public `M31::reduce_u64`, and
  `M31::reduce_u128`;
- `M31::pow`, `CM31::pow`, and `QM31::pow`;
- `M31::is_zero`, `CM31::is_zero`, and `QM31::is_zero`;
- `PreparedQm31Multiplier::new` and `PreparedQm31Multiplier::mul`;
- `CM31::new`, `CM31::from_m31`, and `QM31::from_cm31`; and
- `qm31_from_karatsuba_channel_sums`; and
- the extracted `qm31_accumulate_product_channels` helper, generic
  `qm31_sum_products_small` for every valid `N ≤ 4`, and the public arity-2,
  arity-3, and arity-4 wrappers.

The small-product theorem is not a finite KAT: it proves the two nested
channel loops, the three-component helper loop, the outer input-index loop,
the exact Karatsuba reconstruction, and equality with the ordinary QM31 dot
product for arbitrary canonical inputs. Separate non-vacuity and
omit-one-product counterexamples show that the outer loop affects the result.

The same run also replays the prerequisite M31 reduction/multiplication,
CM31 multiplication/square/scalar multiplication, M31 inverse, and the full
M31/CM31/QM31 add/sub/neg chain.  In particular, the QM31 subtraction used by
the generic `weight_at` path is part of this 4.32 replay rather than a named
two-kernel assumption.

All `#print axioms` results are checked against exactly
`{propext, Classical.choice, Quot.sound}`.  The handwritten sources retain
default proof limits and contain no `sorry`, `admit`, `native_decide`, new
axiom, or unsafe declaration.

## Normalization boundary

The recorded Rust source is `crates/aspis-core/src/field.rs`, Git blob
`a28ff94de05265102ca819849805a7f73c675800` and SHA-256
`dadd6bac7c6c44fcb13e1a1ca26e9d2b6f767370bb6e802640948f15fc795836`.
The extraction tools remain Charon
`cb50ff16b9f1066b8a97dc06da704de2da2fa41c` and Aeneas
`b59d5188c082f704a418c7cb4e52ad69328002d1`.

The proof-relevant generated bodies are not rewritten for Lean 4.32.  Narrow
staged normalizations replace the broad `import Aeneas` with `import Aeneas.Std`
(and `Aeneas.Tactic.RustAttributes` where a generated loop marker needs it).
Charon's unsuffixed positive shift literals remain generated as `I32`; the
two tiny adapters provide the exact bit-preserving `I32 -> U32` and
zero-extending `U8 -> U32` coercions expected by the pinned Aeneas model.
Their concrete one/31 and arbitrary-u8 facts are kernel checked.

The three newly preserved LLBCs are
`aspis_core_prepared_qm31.llbc` (SHA-256 `c754e053...64e0`),
`aspis_core_tower_embeddings.llbc` (`61970ab8...21b`), and
`aspis_core_qm31_sum_products_small.llbc` (`82d8d607...cb37`).  The checker
validates their complete embedded `field.rs`, declaration counts, start
patterns, and exact hashes.  It reverse-normalizes each tracked generated
module and requires the authenticated raw Aeneas output hash.  Prepared and
tower generation originally requested `1000000/2048`; their replayed generated
defaults are reduced to the bundle's standard `200000/1000`.  Handwritten
proofs retain Lean defaults.  The sum-products proof has only the mechanical
Lean-4.32 linter normalization of three fixed-array bound witnesses
(`simpa`/`norm_num` to `simp`); its statements and proof dependencies are
unchanged.

Prepared multiplication is replayed in an isolated generated world because
its raw module deliberately shares the earlier CM31 namespace while having a
different dependency closure.  The checker retargets exactly one import in
the already-audited CM31 proof, pins that transformed source hash, and proves
the reverse substitution recovers the original byte-for-byte.  The broad
Prepared and tower generated modules each retain one Aeneas environment axiom
for `core.array.from_fn`; it is explicitly classified, and every integration
or counterexample theorem is checked not to depend on it.

## Status boundary

This closes the old Lean-4.31-to-4.32 compatibility seam for the listed
arithmetic correspondences.  It does **not** by itself satisfy the Lane-5
report's stronger definition of Level 4, which requires importing the chain
into maintained `AspisFormal`; this isolated bundle deliberately avoids an
aggregator edit.  It also does not prove the complete generic
`WeightAccumulator::weight_at` caller or production dispatch.  In particular,
`qm31_sum_products_small` and its public arity-2/3/4 wrappers now have their
Level-3 source-authentic theorem in both kernels, while
`CM31::{inv,inv_with}` and `QM31::{try_inv,inv}` remain Level 1 because the
pinned translator does not support the function-pointer dependency.  Their
presence in a broad generated closure does not promote those functions.

Run `../check-arithmetic-lean432.sh`.  By default it first creates and
authenticates the pinned base Lean 4.32 Aeneas work tree.  A previously
authenticated retained tree can be supplied for a fast replay:

```sh
ASPIS_AENEAS_432_WORK=<temporary> \
  ../check-arithmetic-lean432.sh
```

The accepted release replay produces 126 `#print axioms` reports. The checker
parses them during the run and fails on any token outside the three-item
allowlist above; build logs and object files are intentionally not retained in
this source bundle.
