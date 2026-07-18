import AspisFormal.V5ComponentCDeployedCDec

/-!
# v5 Component C, deployed C-DEC: corrected accounting for blockers B1/B2

**Verdict: NOT CERTIFIED (unchanged).**  This file proves nothing new about
the deployed system and discharges no blocker.  It corrects the dependency
accounting of `AspisFormal.V5ComponentCDeployedCDec`, which it imports and
does not modify.

## The accounting defect in the original file

`AspisFormal.V5ComponentCDeployedCDec` defines four blocker interfaces in
`DeployedBlockers` and prints all four in its axiom audit, but only two of
them are consumed by any theorem:

* CONSUMED: `DeployedBlockers.EncoderIntertwines` (B4) — the `hEenc`/`hFenc`
  hypotheses of `cDecAudit_of_frozen_certificate` and of
  `frozen_certificate_yields_full_fold_decoupling`.
* CONSUMED: `DeployedBlockers.DeltaImageCovered` (B3) — the `hΔ` hypothesis
  of the same two theorems.
* UNCONSUMED: `DeployedBlockers.EMatrixFaithful` (B1) and
  `DeployedBlockers.FMatrixFaithful` (B2) — defined and axiom-printed, but
  hypotheses of no theorem in that file or anywhere else in this
  repository.  The original docstring's description of the assembled path —
  "certificate plus the named blocker interfaces imply the audit's
  `CDecAudit`" — over-counts, and its closing "B1–B4 are discharged against
  the real artifacts" reads as if all four feed the path: formally,
  discharging B1/B2 would have had no effect on any proved theorem, because
  no theorem mentioned them.

## The correction: make B1/B2 load-bearing (not merely re-labelled)

The gap between B1/B2 and the consumed B4 is a genuine, already-named edge,
not an invented premise.  B1/B2 quantify over abstract evaluators
`rustE`/`rustF` whose docstrings read `rust… i v` as "the deployed Rust
evaluation of … row `i` … on the mask with free coordinates `v`", and B4's
docstring locates its own missing content in the parent file's
`UnresolvedInterfaces.RustLeanRowCorrespondence332` obligation.  The edge
is exactly that correspondence, transported to free coordinates along the
deployed encoder (`V5ComponentCLane::encode_free_coordinates`):

* `RustEvaluatorEncoderCorrespondence` (NEW INTERFACE, UNMET): the deployed
  row evaluator, run on free coordinates, computes the abstract word-space
  row of the encoder image — `rust i v = wordMap (enc v) i`.  This is where
  the unexecutable cross-language content of B4 now lives.  Nothing in this
  file proves it, and no artifact discharges it today.

With that edge named, the derivations are proved in-kernel:

* `encoderIntertwines_of_matrices_faithful` — B1 + B2 + the edge (for `E`
  and for `F`) imply BOTH `EncoderIntertwines` instances consumed by the
  original assembled path.  B1 and B2 are now genuinely load-bearing.
* `rowFaithful_iff_encoderIntertwines` and its packaging
  `matrices_faithful_of_encoderIntertwines` — given the edge, matrix
  faithfulness is *equivalent* to `EncoderIntertwines`, so the hypothesis
  set {B1, B2, edge} is interderivable with {B4 for `E`, B4 for `F`, edge}:
  the factorisation splits B4 into an executable numeric residue (B1/B2:
  emitted bytes against evaluator runs) plus the single named modeling
  edge, and neither weakens nor strengthens the total obligation.
* `cDecAudit_of_frozen_certificate_via_faithful_matrices` — the assembled
  path re-expressed: certificate + B1 + B2 + B3 + edge imply the audit's
  `CDecAudit`; B4 is derived inside instead of independently assumed.
* `frozen_certificate_matrices_faithful_yield_full_fold_decoupling` — the
  same hypotheses composed to the parent headline law; the statement is
  identical to the original `frozen_certificate_yields_full_fold_decoupling`.

## Honest status after this file

* Load-bearing hypotheses of the re-expressed path: B1 `EMatrixFaithful`,
  B2 `FMatrixFaithful`, B3 `DeltaImageCovered`,
  `RustEvaluatorEncoderCorrespondence` (twice: the `E` and `F` instances),
  and the numeric `FrozenQ18Certificate`.  Every one is UNMET today.
* B4 `EncoderIntertwines`: still the directly assumed hypothesis of the
  original path, which is unchanged; on the re-expressed path it is a
  derived intermediate.  It is consumed on both paths.
* Each of the four original blocker `Prop`s is now consumed by at least one
  theorem across the two files.  This was NOT true before this file — B1
  and B2 were consumed by none — and this file does not claim otherwise.
* No blocker is discharged, the unmet-obligation set is refactored rather
  than reduced, every item of the parent `UnresolvedInterfaces` remains
  open, and the honest status of deployed Component-C decoupling remains
  the audit's: OPEN.  This file adds no axioms.
-/

open AspisV5ComponentCConditionalDecoupling
open AspisV5ComponentCDeployedCDec

namespace AspisV5ComponentCDeployedCDecAccounting

section Accounting

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- **NEW INTERFACE (unmet): Rust-evaluator/encoder correspondence.**  The
deployed row evaluator `rust` — the same abstraction blockers B1/B2 already
quantify over, with `rust i v` the deployed Rust evaluation of row `i` on
the mask with free coordinates `v` — computes the abstract word-space row
of the deployed encoder's image: `rust i v = wordMap (enc v) i`.  This is
the free-coordinate transport of the parent file's
`UnresolvedInterfaces.RustLeanRowCorrespondence332` obligation along
`V5ComponentCLane::encode_free_coordinates`, i.e. exactly the
cross-language modeling content that `DeployedBlockers.EncoderIntertwines`
(B4) carries beyond B1/B2.  It is instantiated once with the `E` data
(`n = 76`) and once with the `F` data (`n = 256`).  UNMET: no artifact
discharges it, and nothing in this file proves it. -/
def RustEvaluatorEncoderCorrespondence {n : ℕ}
    (ell : M →ₗ[K] K) (enc : (Fin 1023 → K) →ₗ[K] LinearMap.ker ell)
    (wordMap : M →ₗ[K] (Fin n → K))
    (rust : Fin n → (Fin 1023 → K) → K) : Prop :=
  ∀ (i : Fin n) (v : Fin 1023 → K),
    rust i v = wordMap ((enc v : LinearMap.ker ell) : M) i

/-- **The exact factorisation of blocker B4.**  Under the named
correspondence edge, row-by-row matrix faithfulness — literally the
statement body of `DeployedBlockers.EMatrixFaithful` (at `n = 76`) and of
`DeployedBlockers.FMatrixFaithful` (at `n = 256`) — is equivalent to the
`DeployedBlockers.EncoderIntertwines` instance consumed by the original
assembled path.  The forward direction is what makes B1/B2 load-bearing;
the backward direction shows the factorisation is exact, so replacing the
direct B4 assumption by {faithfulness, edge} smuggles in no strengthening
beyond the edge itself. -/
theorem rowFaithful_iff_encoderIntertwines {n : ℕ}
    {ell : M →ₗ[K] K} {enc : (Fin 1023 → K) →ₗ[K] LinearMap.ker ell}
    {wordMap : M →ₗ[K] (Fin n → K)} {rust : Fin n → (Fin 1023 → K) → K}
    {mat : Matrix (Fin n) (Fin 1023) K}
    (hcorr : RustEvaluatorEncoderCorrespondence ell enc wordMap rust) :
    (∀ (i : Fin n) (v : Fin 1023 → K), rust i v = mat.mulVec v i)
      ↔ DeployedBlockers.EncoderIntertwines ell enc wordMap
          (Matrix.mulVecLin mat) := by
  constructor
  · intro hfaith
    refine LinearMap.ext fun v => funext fun i => ?_
    simp only [LinearMap.comp_apply, LinearMap.domRestrict_apply,
      Matrix.mulVecLin_apply]
    exact (hcorr i v).symm.trans (hfaith i v)
  · intro henc i v
    have henc' : (wordMap.domRestrict (LinearMap.ker ell)) ∘ₗ enc
        = Matrix.mulVecLin mat := henc
    have h : ((wordMap.domRestrict (LinearMap.ker ell)) ∘ₗ enc) v i
        = Matrix.mulVecLin mat v i := by rw [henc']
    simp only [LinearMap.comp_apply, LinearMap.domRestrict_apply,
      Matrix.mulVecLin_apply] at h
    exact (hcorr i v).trans h

/-- **The derivation that makes B1/B2 load-bearing.**
`DeployedBlockers.EMatrixFaithful` and `DeployedBlockers.FMatrixFaithful` —
consumed by no theorem in the original file — together with the named
correspondence edge for `E` and for `F` imply both
`DeployedBlockers.EncoderIntertwines` hypotheses of
`cDecAudit_of_frozen_certificate`.  Every hypothesis is an unmet
interface; the theorem is transport, not evidence. -/
theorem encoderIntertwines_of_matrices_faithful
    (ell : M →ₗ[K] K) (E : M →ₗ[K] (Fin 76 → K)) (F : M →ₗ[K] (Fin 256 → K))
    (enc : (Fin 1023 → K) →ₗ[K] LinearMap.ker ell)
    {rustE : Fin 76 → (Fin 1023 → K) → K}
    {rustF : Fin 256 → (Fin 1023 → K) → K}
    {Emat : Matrix (Fin 76) (Fin 1023) K}
    {Fmat : Matrix (Fin 256) (Fin 1023) K}
    (hEcorr : RustEvaluatorEncoderCorrespondence ell enc E rustE)
    (hFcorr : RustEvaluatorEncoderCorrespondence ell enc F rustF)
    (hEfaith : DeployedBlockers.EMatrixFaithful rustE Emat)
    (hFfaith : DeployedBlockers.FMatrixFaithful rustF Fmat) :
    DeployedBlockers.EncoderIntertwines ell enc E (Matrix.mulVecLin Emat) ∧
      DeployedBlockers.EncoderIntertwines ell enc F (Matrix.mulVecLin Fmat) :=
  ⟨(rowFaithful_iff_encoderIntertwines hEcorr).mp hEfaith,
    (rowFaithful_iff_encoderIntertwines hFcorr).mp hFfaith⟩

/-- **Converse packaging: no covert strengthening.**  Given the
correspondence edge, the two `DeployedBlockers.EncoderIntertwines`
instances give back `DeployedBlockers.EMatrixFaithful` and
`DeployedBlockers.FMatrixFaithful`, so the re-expressed path's hypothesis
set {B1, B2, edge} is interderivable with {B4 for `E`, B4 for `F`,
edge}. -/
theorem matrices_faithful_of_encoderIntertwines
    (ell : M →ₗ[K] K) (E : M →ₗ[K] (Fin 76 → K)) (F : M →ₗ[K] (Fin 256 → K))
    (enc : (Fin 1023 → K) →ₗ[K] LinearMap.ker ell)
    {rustE : Fin 76 → (Fin 1023 → K) → K}
    {rustF : Fin 256 → (Fin 1023 → K) → K}
    {Emat : Matrix (Fin 76) (Fin 1023) K}
    {Fmat : Matrix (Fin 256) (Fin 1023) K}
    (hEcorr : RustEvaluatorEncoderCorrespondence ell enc E rustE)
    (hFcorr : RustEvaluatorEncoderCorrespondence ell enc F rustF)
    (hEenc : DeployedBlockers.EncoderIntertwines ell enc E
      (Matrix.mulVecLin Emat))
    (hFenc : DeployedBlockers.EncoderIntertwines ell enc F
      (Matrix.mulVecLin Fmat)) :
    DeployedBlockers.EMatrixFaithful rustE Emat ∧
      DeployedBlockers.FMatrixFaithful rustF Fmat :=
  ⟨(rowFaithful_iff_encoderIntertwines hEcorr).mpr hEenc,
    (rowFaithful_iff_encoderIntertwines hFcorr).mpr hFenc⟩

/-- **The assembled path, re-expressed so that B1/B2 are consumed.**
Certificate plus B1 (`EMatrixFaithful`), B2 (`FMatrixFaithful`), B3
(`DeltaImageCovered`) and the correspondence edge imply the audit's
`CDecAudit`; B4 (`EncoderIntertwines`) is derived inside via
`encoderIntertwines_of_matrices_faithful` instead of being independently
assumed.  Every hypothesis is a currently non-existent artifact or unmet
interface; the conclusion certifies nothing until they exist. -/
theorem cDecAudit_of_frozen_certificate_via_faithful_matrices
    (ell : M →ₗ[K] K) (E : M →ₗ[K] (Fin 76 → K)) (F : M →ₗ[K] (Fin 256 → K))
    (Δw : Submodule K M)
    (enc : (Fin 1023 → K) →ₗ[K] LinearMap.ker ell)
    {rustE : Fin 76 → (Fin 1023 → K) → K}
    {rustF : Fin 256 → (Fin 1023 → K) → K}
    {Emat : Matrix (Fin 76) (Fin 1023) K}
    {Fmat : Matrix (Fin 256) (Fin 1023) K}
    {d : ℕ} {g : Fin d → Fin 256 → K} {w : Fin d → Fin 1023 → K}
    (hEcorr : RustEvaluatorEncoderCorrespondence ell enc E rustE)
    (hFcorr : RustEvaluatorEncoderCorrespondence ell enc F rustF)
    (hEfaith : DeployedBlockers.EMatrixFaithful rustE Emat)
    (hFfaith : DeployedBlockers.FMatrixFaithful rustF Fmat)
    (hΔ : DeployedBlockers.DeltaImageCovered F Δw g)
    (hcert : FrozenQ18Certificate Emat Fmat g w) :
    CDecAudit ell E F Δw := by
  obtain ⟨hEenc, hFenc⟩ := encoderIntertwines_of_matrices_faithful
    ell E F enc hEcorr hFcorr hEfaith hFfaith
  exact cDecAudit_of_frozen_certificate ell E F Δw enc hEenc hFenc hΔ hcert

/-- **End-to-end with the corrected accounting.**  The statement is
identical to the original `frozen_certificate_yields_full_fold_decoupling`;
the direct B4 hypotheses are replaced by B1 + B2 + the correspondence edge.
Pure composition with the parent headline; the missing inputs remain the
blocker artifacts, and only they. -/
theorem frozen_certificate_matrices_faithful_yield_full_fold_decoupling
    [DecidableEq K] [Fintype M]
    (ell : M →ₗ[K] K) (E : M →ₗ[K] (Fin 76 → K)) (F : M →ₗ[K] (Fin 256 → K))
    {Δw : Submodule K M}
    (enc : (Fin 1023 → K) →ₗ[K] LinearMap.ker ell)
    {rustE : Fin 76 → (Fin 1023 → K) → K}
    {rustF : Fin 256 → (Fin 1023 → K) → K}
    {Emat : Matrix (Fin 76) (Fin 1023) K}
    {Fmat : Matrix (Fin 256) (Fin 1023) K}
    {d : ℕ} {g : Fin d → Fin 256 → K} {w : Fin d → Fin 1023 → K}
    (hEcorr : RustEvaluatorEncoderCorrespondence ell enc E rustE)
    (hFcorr : RustEvaluatorEncoderCorrespondence ell enc F rustF)
    (hEfaith : DeployedBlockers.EMatrixFaithful rustE Emat)
    (hFfaith : DeployedBlockers.FMatrixFaithful rustF Fmat)
    (hΔ : DeployedBlockers.DeltaImageCovered F Δw g)
    (hcert : FrozenQ18Certificate Emat Fmat g w)
    {γ : K} (hγ : γ ≠ 0) {x₁ x₂ : M} (hlegal : x₂ - x₁ ∈ Δw) (e : Fin 76 → K)
    [Nonempty {c : LinearMap.ker ell //
      E.domRestrict (LinearMap.ker ell) c = e}] :
    (PMF.uniformOfFintype {c : LinearMap.ker ell //
        E.domRestrict (LinearMap.ker ell) c = e}).map
        (fun c : {c : LinearMap.ker ell //
            E.domRestrict (LinearMap.ker ell) c = e} =>
          F (x₁ + γ ^ 18 • ((c : LinearMap.ker ell) : M)))
      = (PMF.uniformOfFintype {c : LinearMap.ker ell //
          E.domRestrict (LinearMap.ker ell) c = e}).map
          (fun c : {c : LinearMap.ker ell //
              E.domRestrict (LinearMap.ker ell) c = e} =>
            F (x₂ + γ ^ 18 • ((c : LinearMap.ker ell) : M))) :=
  componentC_full_fold_conditional_decoupling ell E F hγ
    (cDecAudit_of_frozen_certificate_via_faithful_matrices ell E F Δw enc
      hEcorr hFcorr hEfaith hFfaith hΔ hcert)
    hlegal e

end Accounting

/-! ## Axiom audit -/

#print axioms RustEvaluatorEncoderCorrespondence
#print axioms rowFaithful_iff_encoderIntertwines
#print axioms encoderIntertwines_of_matrices_faithful
#print axioms matrices_faithful_of_encoderIntertwines
#print axioms cDecAudit_of_frozen_certificate_via_faithful_matrices
#print axioms frozen_certificate_matrices_faithful_yield_full_fold_decoupling

end AspisV5ComponentCDeployedCDecAccounting
