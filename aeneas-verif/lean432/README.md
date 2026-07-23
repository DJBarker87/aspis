# Lean 4.32 Aeneas compatibility harness

This harness checks the source-generated CM31 multiplicative and M31 inverse
proof chain with the same Lean 4.32 kernel used by `AspisFormal`. It does not
modify or reuse the existing `aeneas-verif/proof/.lake` Lean 4.31 package.

## Pinned inputs

- Aeneas: `b59d5188c082f704a418c7cb4e52ad69328002d1`
- Lean: `4.32.0`, compiler commit
  `8c9756b28d64dab099da31a4c09229a9e6a2ef35`
- mathlib: tag `v4.32.0`, commit
  `81a5d257c8e410db227a6665ed08f64fea08e997`
- Rust source `crates/aspis-core/src/field.rs`: git blob
  `96e8c04efee6a8231adb2723dac9acf975993e06`, SHA-256
  `b424ea2c70902e477a2580d683279645b3dd0423bfa1c9043494bc6a99dfad1e`
- dependency lock: `lake-manifest.json`, SHA-256
  `5d15524cf34ff705bebbd037e80baec63683d5d5a3a37a539a62f17405a2fc62`

The compatibility patch has SHA-256
`04e9c2cf33d941b8e8959c9bc4b27607164e69a5d182377d8708b59f9eca2dc4`.
It changes the Lean and mathlib pins plus exactly three Aeneas source files:

1. `AeneasMeta/BvEnumToBitVec.lean`: use the Lean 4.32 import path. Lean 4.32
   privatized the former eager-realization helpers. This scoped build retains
   enum validation and its marker but intentionally omits eager realization;
   the checked chain is rejected if it invokes `bv_tac` or `bv_decide`. The
   patched module labels the surrounding eager-realization explanation as
   historical Lean 4.31 rationale and explicitly overrides it for this build.
2. `AeneasMeta/Simp/Simp.lean`: adapt the changed optional-fvar result and add
   the now-required `HashSet FVarId` annotation.
3. `Aeneas/Tactic/Simproc/ReduceZMod/ReduceZMod.lean`: use the Lean 4.32-safe
   `ZMod` power pattern.

`Aeneas/Data/Array.lean` is deliberately not patched. It is outside the
`Aeneas.Std` plus `Aeneas.Tactic.RustAttributes` import closure used here.

## Run

From the workspace root:

```sh
aeneas-verif/scripts/check-cm31-inverse-lean432.sh
```

The default clones the official Aeneas HTTPS repository and checks out the
exact commit. For an offline/local-object-cache run, point at any Git clone
that contains the commit; the checker makes a fresh detached clone and rejects
a dirty result:

```sh
ASPIS_AENEAS_432_SOURCE=/path/to/aeneas \
  aeneas-verif/scripts/check-cm31-inverse-lean432.sh
```

The build tree is ephemeral by default. To preserve it for an independent
import or Lake-collision audit, request retention. The final output contains a
machine-readable `LEAN432_WORK_DIR=...` line:

```sh
ASPIS_KEEP_LEAN432_WORK=1 \
  aeneas-verif/scripts/check-cm31-inverse-lean432.sh
```

An agent can also request the path in a file:

```sh
ASPIS_KEEP_LEAN432_WORK=1 \
ASPIS_LEAN432_PATH_FILE=/private/tmp/aspis-lean432-path \
  aeneas-verif/scripts/check-cm31-inverse-lean432.sh
```

The preserved tree contains:

- `aeneas/backends/lean/`: the isolated patched Aeneas Lake package;
- `gate-inputs/`: the pre-clone authenticated snapshot of every harness input;
- `staged-proof/`: all eleven authenticated Lean sources;
- `olean/`: the eleven Lean 4.32 object files;
- `axioms.log`: all 30 `#print axioms` reports; and
- `aeneas-std-build.log`: the scoped dependency build log.

## Generated-source normalization

The canonical generated files remain byte-for-byte Aeneas output with
`import Aeneas`. Only isolated copies are normalized:

| Generated module | Raw SHA-256 | Lean 4.32 SHA-256 |
| --- | --- | --- |
| `AspisCoreFieldReduceU64` | `19aa7ddaa802eb7b1de7c94b704d9ac2fc61e06f239d7b851d172363529e9c98` | `9290a5242dbca963e9215ef68393f671ac8f3fb5343213df6d8acd42a062bcdf` |
| `AspisCoreFieldMulNamespaced` | `109d4a653d3741628f33a751bc7ef4db4ed15ff9e14220176d03f3c734733ac3` | `2faaa967154a82f6614b5d0b124fad43eadd976c9ab06d745055bfc3fb7fe3e6` |
| `AspisCoreCm31Multiplicative` | `ee7dff85178503afd4ae59b04bb8639fad34bcbd58ecc27fc91cf56e124851f7` | `9a79864040dc29aaef42d0b811aab2d68c9e67d1c113930c24e015e50acefc2c` |
| `AspisCoreM31Inverse` | `5e07bb6326376e4e3eb75d93cf6ffd32dbf23ec8aa8916ffa1ab9837cc43daa1` | `9b6c49b4868c2e9f18f300e37c01f3d4c30382498e9880fadd40b1301ccf93e4` |

The first three replace exactly line 3, `import Aeneas`, with
`import Aeneas.Std`. The inverse makes the same replacement and inserts
`import Aeneas.Tactic.RustAttributes` on line 4 to retain its generated
`@[rust_loop]` marker. The checker reverse-normalizes every staged file and
byte-compares it to the raw source, checks line counts, and checks both hash
manifests. The seven hand proofs are copied and byte-compared unchanged. A
third manifest, `staged-hashes.sha256`, authenticates all eleven final staged
files immediately after normalization and again after compilation.

Before cloning Aeneas, the checker snapshots the compatibility patch, Lake
lock, all hash manifests, all eleven Lean sources, and `field.rs` into the work
directory. Hard-coded hashes authenticate that snapshot, and all build steps
read only from it. The snapshot is authenticated again after the build; the
live `field.rs` blob and SHA-256 are also rechecked before the PASS line. This
prevents a workspace edit during a long dependency build from changing what
the gate actually proves.

## Security scope

The gate compiles all eleven modules in dependency order into an isolated
object directory. Besides `Aeneas.Std` and `Aeneas.Tactic.RustAttributes`, it
explicitly builds the five directly imported Mathlib modules
`Data.ZMod.Basic`, `Algebra.QuadraticAlgebra.Basic`, `Algebra.Field.ZMod`,
`FieldTheory.Finite.Basic`, and `Tactic.NormNum.Prime`. It rejects logical
escape constructs in all source files,
requires the exact multiset of 30 axiom reports, and parses every reported
identifier against the exact allowlist:

```text
propext, Classical.choice, Quot.sound
```

The upstream `Aeneas.Std` import closure contains unrelated declarations that
use `sorry`. Therefore this harness does not claim the dependency is globally
`sorry`-free. Its checked claim is narrower: none of the 30
audited theorem dependency closures contains `sorryAx`, `ofReduceBool`, or any
axiom outside the allowlist.

The chain uses Aeneas runtime definitions and lemmas for `Result`, scalar
operations, `partial_fixpoint`, `RangeIter`, `WP.spec_imp_exists`, and
`massert`. The hand proofs use mathlib tactics, not Aeneas `step`, `progress`,
`scalar_tac`, or `bv_tac`. Building `Aeneas.Std` still transitively compiles a
small amount of Aeneas meta/tactic code, which is why the three scoped
compatibility changes above are necessary.

## Verification record

A clean run from the official Aeneas HTTPS repository at the pinned commit
completed in the retained directory
`/private/tmp/aspis-aeneas-lean432-check.p116iK`. During that run the initial
scoped Aeneas build exposed that direct Mathlib objects also had to be named;
after building the exact five targets listed above in the same clean checkout,
all eleven modules compiled and all 30 axiom reports parsed to exactly
`{propext, Classical.choice, Quot.sound}` with no `sorryAx` or `ofReduceBool`.

The durable script now includes those targets, the full input snapshot, and
the end-of-build hash rechecks. Per the sprint stop directive, that hardened
from-zero wrapper has not been launched a second time; only offline patch,
hash, syntax, and warm-cache smoke checks were run after hardening. The next
release gate should execute the command in **Run** once from zero.
