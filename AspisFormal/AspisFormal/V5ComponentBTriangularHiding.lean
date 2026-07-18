import Mathlib
import AspisFormal.V5RankOneOpeningHiding

/-!
# Component B: triangular hiding without double-counting the terminal

Component B has two different kinds of released data.  Its masked sumcheck
state is released (through the committed round messages), and the structured
terminal is a deterministic function of that same masked state.  The remaining
released coordinates are independently padded.  Consequently the terminal is
not a second rank target.

This file isolates that dependency exactly.  Over a field, with finite state
and pad sampling spaces, let

* `S` be the sumcheck-state space (271 deployed coordinates),
* `P` be the pad-plus-pivot sampling space,
* `V` be the independent residual view (76 coordinates: the inactive claim,
  72 raw observations, and 3 MLE claims), and
* `terminal : S → T` be any deterministic terminal calculation.

For a witness contribution `(wS, wV)` and a uniform sample `(s, p)`, the full
abstract view is

`(wS + s, terminal (wS + s), wV + R s + A p)`.

To couple two witnesses, first translate the state sample by
`ds = wS₂ - wS₁`.  This makes their masked states literally equal, so their
terminals agree without spending a rank direction.  Then choose `dp` with

`A dp = wV₂ - wV₁ - R ds`.

Surjectivity of `A` supplies this second translation.  Translation is a
bijection of the finite product sample space, so it preserves the uniform law.

The proved result is finite linear algebra plus finite uniform-PMF transport.
It does not identify the abstract spaces, maps, sampler, transcript, or bytes
with Rust.  The final namespace records those deployment edges as named,
unproved propositions.  In particular, the theorem does not turn a measured
rank into a code-correspondence claim.
-/

open scoped ENNReal

namespace AspisV5ComponentBTriangularHiding

open AspisV5RankOneOpeningHiding

variable {K S P V T : Type*}
variable [Field K]
variable [AddCommGroup S] [Module K S]
variable [AddCommGroup P] [Module K P]
variable [AddCommGroup V] [Module K V]

/-! ## The triangular view -/

/-- The complete abstract Component-B view.  The structured terminal is
computed from the already-released masked state; it is deliberately not an
independent affine coordinate. -/
def triangularView
    (terminal : S → T) (R : S →ₗ[K] V) (A : P →ₗ[K] V)
    (wS : S) (wV : V) (sample : S × P) : S × T × V :=
  let maskedState := wS + sample.1
  (maskedState, terminal maskedState, wV + R sample.1 + A sample.2)

/-- Translation of both independent sampling components.  Its inverse
subtracts the same pair of shifts. -/
def productTranslationEquiv (ds : S) (dp : P) : S × P ≃ S × P where
  toFun sample := (sample.1 + ds, sample.2 + dp)
  invFun sample := (sample.1 - ds, sample.2 - dp)
  left_inv sample := by simp
  right_inv sample := by simp

@[simp]
theorem productTranslationEquiv_apply (ds : S) (dp : P) (sample : S × P) :
    productTranslationEquiv ds dp sample = (sample.1 + ds, sample.2 + dp) :=
  rfl

/-- Surjectivity gives the exact pad shift needed after the state shift is
fixed.  This is exported separately so the construction is visible rather
than hidden behind choice inside the PMF theorem. -/
theorem exists_padShift
    (R : S →ₗ[K] V) (A : P →ₗ[K] V)
    (hA : Function.Surjective A)
    (wS₁ wS₂ : S) (wV₁ wV₂ : V) :
    ∃ dp : P, A dp = wV₂ - wV₁ - R (wS₂ - wS₁) :=
  hA (wV₂ - wV₁ - R (wS₂ - wS₁))

/-- The constructive pointwise coupling.  Translating the first witness's
sample by `ds = wS₂ - wS₁` and a pad shift satisfying the displayed equation
makes all three released coordinates equal.  The terminal equality follows
only because the masked states have become equal. -/
theorem triangularView_translate
    (terminal : S → T) (R : S →ₗ[K] V) (A : P →ₗ[K] V)
    (wS₁ wS₂ : S) (wV₁ wV₂ : V) (dp : P)
    (hdp : A dp = wV₂ - wV₁ - R (wS₂ - wS₁))
    (sample : S × P) :
    triangularView terminal R A wS₁ wV₁
        (productTranslationEquiv (wS₂ - wS₁) dp sample)
      = triangularView terminal R A wS₂ wV₂ sample := by
  rcases sample with ⟨s, p⟩
  simp only [productTranslationEquiv_apply, triangularView, map_add, hdp]
  have hs : wS₁ + (s + (wS₂ - wS₁)) = wS₂ + s := by abel_nf
  apply Prod.ext
  · exact hs
  · apply Prod.ext
    · exact congrArg terminal hs
    · abel_nf

/-- Function-level form of `triangularView_translate`, convenient for PMF
transport and downstream composition. -/
theorem triangularView_comp_productTranslation
    (terminal : S → T) (R : S →ₗ[K] V) (A : P →ₗ[K] V)
    (wS₁ wS₂ : S) (wV₁ wV₂ : V) (dp : P)
    (hdp : A dp = wV₂ - wV₁ - R (wS₂ - wS₁)) :
    triangularView terminal R A wS₁ wV₁ ∘
        productTranslationEquiv (wS₂ - wS₁) dp
      = triangularView terminal R A wS₂ wV₂ := by
  funext sample
  exact triangularView_translate terminal R A wS₁ wS₂ wV₁ wV₂ dp hdp sample

/-! ## Uniform product law -/

section Distribution

variable [Fintype S] [Fintype P]

/-- Uniform sampling of `(s, p)` hides every witness contribution when the
pad-plus-pivot map covers the independent residual view.  No condition is
placed on `terminal`: after the state translation it receives the same masked
state on both sides.

Every hypothesis is computationally relevant: without `hA`, the residual
view can leak (see the negative model below); the additive/module structures
define the two translations and the linear correction. -/
theorem triangularView_uniform_pmf_eq
    (terminal : S → T) (R : S →ₗ[K] V) (A : P →ₗ[K] V)
    (hA : Function.Surjective A)
    (wS₁ wS₂ : S) (wV₁ wV₂ : V) :
    (PMF.uniformOfFintype (S × P)).map
        (triangularView terminal R A wS₁ wV₁)
      = (PMF.uniformOfFintype (S × P)).map
        (triangularView terminal R A wS₂ wV₂) := by
  obtain ⟨dp, hdp⟩ := exists_padShift R A hA wS₁ wS₂ wV₁ wV₂
  let shift := productTranslationEquiv (wS₂ - wS₁) dp
  have huniform :
      (PMF.uniformOfFintype (S × P)).map shift
        = PMF.uniformOfFintype (S × P) :=
    uniform_map_equiv shift
  have hintertwine :
      triangularView terminal R A wS₁ wV₁ ∘ shift
        = triangularView terminal R A wS₂ wV₂ := by
    exact triangularView_comp_productTranslation
      terminal R A wS₁ wS₂ wV₁ wV₂ dp hdp
  calc
    (PMF.uniformOfFintype (S × P)).map
          (triangularView terminal R A wS₁ wV₁)
        = ((PMF.uniformOfFintype (S × P)).map shift).map
            (triangularView terminal R A wS₁ wV₁) := by rw [huniform]
    _ = (PMF.uniformOfFintype (S × P)).map
          (triangularView terminal R A wS₁ wV₁ ∘ shift) :=
      PMF.map_comp _ _ _
    _ = (PMF.uniformOfFintype (S × P)).map
          (triangularView terminal R A wS₂ wV₂) := by rw [hintertwine]

end Distribution

/-! ## Concrete non-vacuity and a leak when pads do not cover `V` -/

namespace Model

abbrev F := ZMod 2

/-- An arbitrary deterministic terminal; identity is enough to exercise the
fact that it follows the matched state. -/
def terminal : F → F := id

/-- The state-to-residual contribution in the positive model. -/
def stateMap : F →ₗ[F] F := LinearMap.id

/-- A surjective one-coordinate pad map. -/
def fullPadMap : F →ₗ[F] F := LinearMap.id

theorem fullPadMap_surjective : Function.Surjective fullPadMap := by
  intro v
  exact ⟨v, rfl⟩

/-- The headline theorem is non-vacuous over a concrete finite field, with
both the state and residual witness contributions changed. -/
theorem hiding_nonvacuous :
    (PMF.uniformOfFintype (F × F)).map
        (triangularView terminal stateMap fullPadMap 0 0)
      = (PMF.uniformOfFintype (F × F)).map
        (triangularView terminal stateMap fullPadMap 1 1) :=
  triangularView_uniform_pmf_eq terminal stateMap fullPadMap
    fullPadMap_surjective 0 1 0 1

/-- A pad map with no image except zero. -/
def zeroPadMap : F →ₗ[F] F := 0

theorem zeroPadMap_not_surjective : ¬ Function.Surjective zeroPadMap := by
  intro hsurj
  obtain ⟨p, hp⟩ := hsurj 1
  simp [zeroPadMap] at hp

/-- Without pad surjectivity, two witnesses can have the same masked-state
and terminal laws while the independent residual coordinate reveals the
witness.  Thus terminal determinism alone is not a hiding argument. -/
theorem no_pad_coverage_leaks :
    (PMF.uniformOfFintype (F × F)).map
        (triangularView terminal (0 : F →ₗ[F] F) zeroPadMap 0 0)
      ≠ (PMF.uniformOfFintype (F × F)).map
        (triangularView terminal (0 : F →ₗ[F] F) zeroPadMap 0 1) := by
  intro hcontra
  let residual : F × F × F → F := fun view => view.2.2
  have hprojected := congrArg (fun q : PMF (F × F × F) => q.map residual) hcontra
  have hleft :
      residual ∘ triangularView terminal (0 : F →ₗ[F] F) zeroPadMap 0 0
        = fun _ : F × F => (0 : F) := by
    funext sample
    simp [residual, triangularView, zeroPadMap]
  have hright :
      residual ∘ triangularView terminal (0 : F →ₗ[F] F) zeroPadMap 0 1
        = fun _ : F × F => (1 : F) := by
    funext sample
    simp [residual, triangularView, zeroPadMap]
  rw [PMF.map_comp, PMF.map_comp, hleft, hright] at hprojected
  have hzero :
      (PMF.uniformOfFintype (F × F)).map (fun _ : F × F => (0 : F))
        = PMF.pure 0 := by
    simpa [Function.const_def] using
      (PMF.map_const (PMF.uniformOfFintype (F × F)) (0 : F))
  have hone :
      (PMF.uniformOfFintype (F × F)).map (fun _ : F × F => (1 : F))
        = PMF.pure 1 := by
    simpa [Function.const_def] using
      (PMF.map_const (PMF.uniformOfFintype (F × F)) (1 : F))
  rw [hzero, hone] at hprojected
  have hvalue := congrArg (fun q : PMF F => q 0) hprojected
  rw [PMF.pure_apply, PMF.pure_apply, if_pos (by decide),
    if_neg (by decide)] at hvalue
  exact one_ne_zero hvalue

end Model

/-! ## Named deployment interfaces

These propositions are deliberately not proved here.  They state the exact
code/model seams required before the abstract PMF theorem may be applied to
the deployed Component-B wire. -/

namespace UnmetDeployment

/-- Deployed Component B has exactly 271 committed state coordinates. -/
abbrev StateCoordinate := Fin 271

/-- The ten deployed degree-27 round messages release 280 field
coordinates. -/
abbrev RoundMessageCoordinate := Fin 280

/-- The raw part of the independent released view has 72 coordinates. -/
abbrev RawCoordinate := Fin 72

/-- The MLE-claim part of the independent released view has 3 coordinates. -/
abbrev MLECoordinate := Fin 3

/-- The complete independent view has `1 + 72 + 3 = 76` coordinates. -/
abbrev ResidualCoordinate := Fin 76

/-- The abstract state coordinates are exactly the 271 coordinates committed
by Rust, and their stated encoder produces exactly the 280 Rust round-message
coordinates.  Both equalities include order and field representation.  This
interface does not claim that the 271 coordinates and 280 messages are the
same vector. -/
def StateCoordinatesMatchRust271
    (abstractCoordinates rustCommittedCoordinates : S → StateCoordinate → K)
    (encodeRoundMessages :
      (StateCoordinate → K) → RoundMessageCoordinate → K)
    (rustRoundMessages : S → RoundMessageCoordinate → K) : Prop :=
  abstractCoordinates = rustCommittedCoordinates ∧
    ∀ state,
      encodeRoundMessages (abstractCoordinates state) = rustRoundMessages state

/-- The abstract residual space is exactly the inactive claim, 72 raw
observations, and 3 MLE claims—no terminal coordinate and no omitted released
coordinate.  Bijectivity rules out both duplication and omission. -/
def ResidualViewIsExactlyOnePlus72Plus3
    (coordinates : V →ₗ[K]
      (K × (RawCoordinate → K) × (MLECoordinate → K))) : Prop :=
  Function.Bijective coordinates

/-- The deployed structured terminal evaluator is the stated deterministic
function of the 271 masked-state coordinates. -/
def StructuredTerminalIsFunctionOfState
    (terminalModel terminalRust : S → T) : Prop :=
  terminalModel = terminalRust

/-- The current pad-plus-pivot map covers all 76 independent coordinates.
The finrank clause pins the measured target size; surjectivity is the exact
premise consumed by `triangularView_uniform_pmf_eq`. -/
def CurrentPadsPlusPivotMapHasRank76
    [FiniteDimensional K V] (A : P →ₗ[K] V) : Prop :=
  Module.finrank K V = 76 ∧ Function.Surjective A

/-- The Rust sampler is uniform on the product state/pad space used by the
theorem. -/
def RustSamplerIsUniformProduct [Fintype S] [Fintype P]
    (rustSampler : PMF (S × P)) : Prop :=
  rustSampler = PMF.uniformOfFintype (S × P)

/-- For every concrete state/pad sample, the bytes emitted by the Rust run are
exactly serialization of this file's `triangularView`, including coordinate
order and field encoding. -/
def RustSerializationCorrespondence
    (terminal : S → T) (R : S →ₗ[K] V) (A : P →ₗ[K] V)
    (wS : S) (wV : V)
    (abstractSerialize : (S × T × V) → ByteArray)
    (rustRunBytes : S × P → ByteArray) : Prop :=
  ∀ sample,
    rustRunBytes sample =
      abstractSerialize (triangularView terminal R A wS wV sample)

/-- The committed 271-state and pad material are fixed before the Fiat–Shamir
challenges used by the round messages and terminal evaluation, with the same
absorb order in host and verifier. -/
def FiatShamirCommitBeforeChallengeCorrespondence
    {Transcript Challenge : Type*}
    (CommittedBeforeChallenge :
      (Transcript → Transcript) → (Transcript → Challenge) → Prop)
    (abstractAbsorb rustAbsorb : Transcript → Transcript)
    (abstractChallenge rustChallenge : Transcript → Challenge) : Prop :=
  CommittedBeforeChallenge abstractAbsorb abstractChallenge ∧
    abstractAbsorb = rustAbsorb ∧ abstractChallenge = rustChallenge

end UnmetDeployment

#print axioms productTranslationEquiv_apply
#print axioms exists_padShift
#print axioms triangularView_translate
#print axioms triangularView_comp_productTranslation
#print axioms triangularView_uniform_pmf_eq
#print axioms Model.fullPadMap_surjective
#print axioms Model.hiding_nonvacuous
#print axioms Model.zeroPadMap_not_surjective
#print axioms Model.no_pad_coverage_leaks
#print axioms UnmetDeployment.StateCoordinatesMatchRust271
#print axioms UnmetDeployment.ResidualViewIsExactlyOnePlus72Plus3
#print axioms UnmetDeployment.StructuredTerminalIsFunctionOfState
#print axioms UnmetDeployment.CurrentPadsPlusPivotMapHasRank76
#print axioms UnmetDeployment.RustSamplerIsUniformProduct
#print axioms UnmetDeployment.RustSerializationCorrespondence
#print axioms UnmetDeployment.FiatShamirCommitBeforeChallengeCorrespondence

end AspisV5ComponentBTriangularHiding
