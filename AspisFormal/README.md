# AspisFormal — Lean 4 formalization

Kernel-checked lemmas for the Aspis construction. The point is to move
security-relevant claims off "an AI/script proved it" and onto the Lean kernel.
Build: `lake exe cache get && lake build` (Lean 4, mathlib). CI:
`.github/workflows/lean.yml` (builds/kernel-checks this project) and
`.github/workflows/param-binding.yml` (fails if Rust/Python/Lean disagree on the
deployed parameters).

**Every theorem below depends only on `[propext, Classical.choice, Quot.sound]`
(mathlib's standard base) — no `sorry`, no `native_decide`, no custom axioms.**

## Proof-status table — read this honestly

### Hiding
| Statement | File | Status |
|---|---|---|
| Surjective mask map ⟹ witness-independent fibre **counts** | `CoreHiding.lean` | **Proved** (counting, not `PMF`) |
| Same, upgraded to a **`PMF` distribution** equality over a finite field | `CoreHidingPMF.lean` | **Proved** |
| `det M ≠ 0` ⟹ surjective ⟹ hidden, for a square matrix `M` | `MaskingHiding.lean` | **Proved** (arbitrary `M`) |
| Schwartz–Zippel liveness bridge; b=2 to `2/|K|`; b=4 `det≠0` | `CircleVandermonde.lean` | **Proved** |
| Circle liveness at arbitrary even `b` (free coords `K^{2b}`); b=128 ⟹ `≤8192/|K|` | `CircleVandermondeGeneral.lean` | **Proved** |
| Circle liveness over the **real circle-point distribution** (`t`-param, poles handled); b=128 ⟹ `≤16640/|K| ≈ 2⁻¹¹⁰` | `CirclePointLiveness.lean` | **Proved** (closes the free-coord gap) |
| Hiding for the **concrete circle mask matrix** (not arbitrary `M`) + view interface | `AspisViewBinding.lean` | **Proved** + named interface |
| Byte-exact released-view model; view completeness arithmetic; sampler uniformity ⟹ `PMF`-level perfect hiding; (a) closure spec | `ViewModel.lean` | **Proved** + named interface |

### Soundness
| Statement | File | Status |
|---|---|---|
| No field-wraparound `v'+f=v` over ℤ (no inflation) | `ValueConservation.lean` | **Proved** |
| Range (both) + balance + asset **from the constraint residuals**; hash/Merkle as interface | `ArithmetizationCore.lean` | **Proved** (5/10 relation clauses) |
| Johnson threshold `ρ≤α²`; agreement cap `A=⌊αN⌋=6082` (manifest-bound) | `SoundnessParams.lean` | **Proved** |
| Constants, regime `ρ<√ρ≤α`, every ledger degree, per-event SZ bits, fold/coarse unions, ×3 inflation (`≤2⁻¹⁰⁴`) | `SoundnessLedger.lean` | **Proved** (floor bounds) |
| Circle fibre-root distinctness / root≠1 (structural, no brute force) | `CircleFibreRoots.lean` | **Proved** (modulo the group-order interface) |

## What is NOT (yet) proved — the honest gaps

Substantial progress, but these remain and a reviewer will ask for them:

- **Obligation (a): deployed mask map = circle matrix.** Provably reduced to a
  single `decide` against the v5 encoder's coefficient tables — but v4 uses the
  `H/G/D` masking, so this **awaits the v5 circle-block-form implementation**.
  Correctly left as a named interface field, never faked.
- **The hash/Merkle relation clauses (6 of 10).** The four Poseidon2 hash
  equations and two Merkle same-path roots are stated as the explicit
  `ArithmetizationModels` interface. Closing them needs a Poseidon2/Merkle model
  in Lean or an exhaustive symbolic check of the deployed gate bytes.
- **The BCS work-normalized endpoint** (~100.16 bit) needs `Real.logb` + additive
  `2⁻²⁵⁶` terms; we kernel-check the coarse union `≤2⁻¹⁰⁶` and its ×3 `≤2⁻¹⁰⁴`,
  and the endpoint erosion stays Python-verified.
- **Serialization faithfulness.** The byte-exact view model matches the paper's
  wire table by `decide`; that it matches the *deployed serializer bytes* is the
  `serialization_complete` interface field.
- **The circle-group order** (`g` has order exactly `2³¹`) underpinning the
  fibre-root and node-distinctness facts is a named interface, not yet built.
- **The published theorems** (Johnson/MCA/WHIR/BCS list decoding, the ZK
  simulator template) are **cited, not formalized**. Intentional and normal, but
  it means the hiding/soundness *arguments* are not end-to-end formal.

## What has been closed since the first draft

- Parameters are now **manifest-bound and CI-enforced** across Rust, Python, and
  Lean (was: "Lean is about intended, not deployed, params").
- Hiding is now a **distribution-level** statement (was: fibre counts only).
- The liveness bound now holds over the **real circle-point distribution** (was:
  free coordinates only).
- The soundness ledger arithmetic and fibre-root distinctness are **in the
  kernel** (were: Python-only).
- The value-conservation core is proven **from the constraints up** (was:
  abstract).
- The frontier (items 4–6) is reduced to a **short list of named, human-readable
  obligations**, several with their tractable halves already proved and a
  runnable closure spec for the rest.

The honest bottom line: the finite mathematics is increasingly in the kernel;
what remains is (i) code-correspondence obligations that need the v5
implementation or a Poseidon2/Merkle model, and (ii) the cited published
theorems. None of it is faked; all of it is named.
