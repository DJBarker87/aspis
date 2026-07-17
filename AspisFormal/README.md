# AspisFormal — Lean 4 formalization

Kernel-checked lemmas for the Aspis construction. The point is to move
security-relevant claims off "an AI/script proved it" and onto the Lean kernel.
Build: `lake exe cache get && lake build` (Lean 4, mathlib). CI: `.github/workflows/lean.yml`.

**Every theorem below depends only on `[propext, Classical.choice, Quot.sound]`
(mathlib's standard base) — no `sorry`, no custom axioms.**

## Proof-status table — read this honestly

| Statement | File | Status |
|---|---|---|
| No field-wraparound: `v'+f=v` over ℤ (no inflation) | `ValueConservation.lean` | **Proved** |
| Surjective mask map ⟹ witness-independent fibre counts | `CoreHiding.lean` | **Proved** (fibre-cardinality equality; not a `PMF`/simulator statement) |
| `det M ≠ 0` ⟹ surjective ⟹ witness-independent, for a square matrix `M` | `MaskingHiding.lean` | **Proved** (for an *arbitrary* `M`) |
| Schwartz–Zippel liveness: bad-schedule fraction ≤ `det.totalDegree/|K|` | `CircleVandermonde.lean` | **Proved** (general bridge; b=2 to `2/|K|`; b=4 `det≠0`) |
| Circle liveness at arbitrary even `b`; b=128 ⟹ `≤ 8192/|K|` | `CircleVandermondeGeneral.lean` | **Proved** (over *free* coordinates `K^{2b}`) |
| Johnson threshold `ρ ≤ α²`; agreement cap `A = ⌊αN⌋ = 6082` | `SoundnessParams.lean` | **Proved** (two facts only; see below) |

## What is NOT (yet) proved — the honest gaps

These are the load-bearing obligations a reviewer will ask for. None is done:

- **Implementation binding.** The Lean constants (`ρ, α, N`) and matrices are
  Lean-defined literals. Nothing proves they equal the constants / schedule /
  transcript in the Rust verifier. Intended fix: generate Lean + Rust constants
  from one frozen manifest and make CI reject disagreement.
- **The actual Aspis view.** `MaskingHiding`/`CoreHiding` take an *arbitrary*
  matrix `A`/`M`. There is no definition of Aspis's complete released view, no
  proof that this matrix *is* that view, and no `PMF`-level simulator.
- **Most of the soundness instantiation.** `SoundnessParams` kernel-checks only
  the Johnson threshold and the cap 6082. The rest of the finite-parameter check
  (fibre-root distinctness, circle-to-line transport, the width-29 MCA generator
  condition, event degrees, union/BCS arithmetic) is still done by
  `tools/verify_soundness_params.py`, **not** in Lean.
- **The circle-point distribution.** `CircleVandermondeGeneral` bounds a fraction
  over *free* coordinates `K^{2b}`; real Fiat–Shamir points lie on the circle
  `x²+y²=1`. Tying the bound to that actual distribution (via the
  `t`-parameterization) is in progress.
- **Circle-FFT basis equivalence.** The block form `{p(x)+y·q(x)}` is used as a
  model of the mask space; equivalence to the deployed circle-FFT basis is not
  formalized.
- **The published theorems** (Johnson/MCA/WHIR/BCS, the ZK simulator template)
  are *cited*, not formalized. That is intentional and normal, but it means the
  hiding/soundness *arguments* are not end-to-end formal.

So this directory currently contains **correct, kernel-checked building blocks**
that are not yet bound to the deployed protocol. The next work is the binding
(manifest-generated constants + CI, the real released-view type, the mask matrix
from the real schedule, and a theorem that the matrix models the Rust transcript).
