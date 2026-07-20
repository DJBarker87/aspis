# Lean 4.32 shared-field replay

This directory is the durable Lean 4.32 replay of the source-authentic
M31/CM31/QM31 arithmetic used by the Component-B `weight_at` extraction.  It
contains no object files or Lake cache.  `SOURCE_MANIFEST.sha256` authenticates
all 33 source modules; the manifest itself has SHA-256
`8ed6cdb1479c4a3df680e615350af310baf3397e15030ab4d4ef35630b828e36`.

## What is now checked by the Lean 4.32 kernel

The 18 Lane-5 correspondences that were previously checked only by Lean 4.31
are replayed unchanged at the theorem level:

- `mul_by_r`, `QM31::mul`, optimized `QM31::square`, `QM31::mul_m31`, and
  `QM31::mul_cm31`;
- `M31::half`, `CM31::half`, and `QM31::half`;
- `M31::mul_pow2`, `M31::reduce_u62`, public `M31::reduce_u64`, and
  `M31::reduce_u128`;
- `M31::pow`, `CM31::pow`, and `QM31::pow`; and
- `M31::is_zero`, `CM31::is_zero`, and `QM31::is_zero`.

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

The frozen Rust source is `crates/aspis-core/src/field.rs`, Git blob
`96e8c04efee6a8231adb2723dac9acf975993e06` and SHA-256
`b424ea2c70902e477a2580d683279645b3dd0423bfa1c9043494bc6a99dfad1e`.
The extraction tools remain Charon
`cb50ff16b9f1066b8a97dc06da704de2da2fa41c` and Aeneas
`b59d5188c082f704a418c7cb4e52ad69328002d1`.

The generated proof bodies are not rewritten for Lean 4.32.  Narrow staged
normalizations replace the broad `import Aeneas` with `import Aeneas.Std`
(and `Aeneas.Tactic.RustAttributes` where a generated loop marker needs it).
Charon's unsuffixed positive shift literals remain generated as `I32`; the
two tiny adapters provide the exact bit-preserving `I32 -> U32` and
zero-extending `U8 -> U32` coercions expected by the pinned Aeneas model.
Their concrete one/31 and arbitrary-u8 facts are kernel checked.

## Status boundary

This closes the old Lean-4.31-to-4.32 compatibility seam for the listed
arithmetic correspondences.  It does **not** by itself satisfy the Lane-5
report's stronger definition of Level 4, which requires importing the chain
into maintained `AspisFormal`; this isolated bundle deliberately avoids an
aggregator edit.  It also does not prove the optional
`PreparedQm31Multiplier::mul` extraction, the complete generic
`WeightAccumulator::weight_at` caller, or production dispatch.

Run `../check-arithmetic-lean432.sh`.  By default it first creates and
authenticates the pinned base Lean 4.32 Aeneas work tree.  A previously
authenticated retained tree can be supplied for a fast replay:

```sh
ASPIS_AENEAS_432_WORK=/private/tmp/aspis-aeneas-lean432-check.example \
  ../check-arithmetic-lean432.sh
```

The accepted release replay produces 95 `#print axioms` reports. The checker
parses them during the run and fails on any token outside the three-item
allowlist above; build logs and object files are intentionally not retained in
this source bundle.
