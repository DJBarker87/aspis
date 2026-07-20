# Source-authentic M31 sub, negation, and multiplication extraction

These artifacts extract the deployed base-field operations directly from the
tracked `crates/aspis-core/src/field.rs`. No Rust function is copied into a
pilot crate.

## Exact toolchain

- Aeneas: `b59d5188c082f704a418c7cb4e52ad69328002d1`
- Charon: `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`
- Rust: `nightly-2026-06-01`
- Lean backend: `v4.31.0`
- audited `field.rs` blob: `96e8c04efee6a8231adb2723dac9acf975993e06`

The reproducible command is:

```sh
ASPIS_AENEAS_REPO=/path/to/aeneas \
ASPIS_CHARON_REPO=/path/to/charon \
./aeneas-verif/scripts/extract-field-sub-neg-mul.sh
```

The script verifies the two tool revisions and Aeneas's `charon-pin`, checks
the exact production source blob, extracts with `--preset=aeneas`, and invokes
Cargo with `--release --locked -p aspis-core` and a fresh target directory.

## Charon roots and generated definitions

| Rust operation | Charon root | Generated Lean definition |
| --- | --- | --- |
| `M31::sub` | `aspis_core::field::_::sub` | `aspis_core.field.M31.sub` |
| `M31::neg` | `aspis_core::field::_::neg` | `aspis_core.field.M31.neg` |
| private `reduce_u64` | `aspis_core::field::reduce_u64` | `aspis_core.field.reduce_u64` |
| `M31::mul` | `aspis_core::field::_::mul` | `aspis_core.field.M31.mul` |

Pinned Charon cannot select one inherent impl by its type. Its documented
narrow workaround is `crate::module::_::method`. Consequently, the `sub` and
`neg` artifacts also contain the CM31 and QM31 methods with those names. The
`mul` artifact additionally contains the other in-module inherent `mul`
methods and the dependencies reachable from them. This is selector overreach,
not a different source model: the required `M31::mul` and private
`reduce_u64` definitions have exact production source spans and bodies.

`reduce_u64` is also extracted under its exact free-function path, producing a
minimal three-declaration artifact (`P`, its initializer, and `reduce_u64`).
This isolates the Mersenne-reduction model used by `M31::mul`.

Generated and elaborated artifacts:

- `llbc/aspis_core_field_sub.llbc` and `proof/AspisCoreFieldSub.lean`
- `llbc/aspis_core_field_neg.llbc` and `proof/AspisCoreFieldNeg.lean`
- `llbc/aspis_core_field_reduce_u64.llbc` and
  `proof/AspisCoreFieldReduceU64.lean`
- `llbc/aspis_core_field_mul.llbc` and
  `proof/AspisCoreFieldMul.lean`
- the same multiplication LLBC translated under the collision-free namespace
  `AspisCoreMul` as `proof/AspisCoreFieldMulNamespaced.lean`

All four generated files compile cleanly against the pinned Aeneas Lean
library. Direct subtraction and negation correspondence theorems are in
`proof/M31SubProof.lean` and `proof/M31NegProof.lean`.

The namespaced multiplication translation is generated from the identical
checked LLBC, not from another Rust copy. It permits one proof module to import
the minimal reduction extraction and multiplication extraction together
without redeclaring `aspis_core.field.P` and `aspis_core.field.reduce_u64`.

The script rejects an empty declaration order and checks the exact Rust source
text, generated definition names, source spans, and load-bearing wrapping
arithmetic/shift calls before replacing these artifacts.

## Shift-type source normalization

Rust inferred the unsuffixed count in the two former production expressions
`x >> 31` as `i32`. Exact pinned Charon serialized that type and exact pinned
Aeneas emitted:

```lean
Std.U64.wrapping_shr x 31#i32
```

The production source now spells both counts as `31u32`. This changes only the
static type of the constant operand: both operands denote the natural number
31, and Rust's `u64 >> RHS` result is unchanged for a count below 64. The new
source blob is pinned above. Exact pinned Aeneas consequently emits the
well-typed `31#u32`; there is no generated-file postprocess.

For an independent compiler-level check, release MIR was emitted before and
after with:

```sh
cargo rustc -p aspis-core --lib --release --locked -- --emit=mir
```

Extracting the private `reduce_u64` MIR body and diffing it produced exactly
two changed tokens, `31_i32` to `31_u32`; all instructions, operands, branches,
and results are otherwise byte-for-byte identical. The captured function-body
diff is `evidence/reduce-u64-shift-type-only.diff`.

This closes the selected Rust-source-to-Lean-functional-model edges. The
proof layer is now provided by:

- `proof/M31ReduceU64Proof.lean`, whose capstone
  `extracted_reduce_u64_corresponds` covers every Rust `u64`, proves canonical
  output, and proves equality in `ZMod (2^31 - 1)`;
- `proof/M31MulProof.lean`, whose capstone `extracted_m31_mul_corresponds`
  covers every pair of canonical production M31 words and proves exact field
  multiplication.

The multiplication proof also kernel-checks equality between the reduction
function emitted in the minimal reduction artifact and the same function
emitted in the namespaced multiplication artifact. That composition edge is a
theorem, not an assumed correspondence.
