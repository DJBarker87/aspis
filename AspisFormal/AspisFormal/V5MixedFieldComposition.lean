import AspisFormal.V5ConditionalHidingCapstoneV3
import AspisFormal.V5AtomicComponentACorrespondence

/-!
# v5 mixed-field composition seam

The v3 hiding capstone is stated with one scalar field `K` for every outer
coin space.  That is not the deployed type boundary: Component-A coins and
their rational view are products of `M31`, while Component B, Component C,
and the Fiat--Shamir challenge `gamma` live in `QM31`.

This file removes that artificial common-scalar requirement.  Component A is
linear over an independent field `FA`; Hcopy, B, and C remain linear over
`K`.  The composition proof only needs the additive translation furnished by
Component A's own surjective `FA`-linear map.  It never gives the M31 coin
space a QM31-module structure and never claims surjectivity onto an arbitrary
QM31 vector space.

The second half proves the mathematical coordinate transports and lists the
remaining code/model interfaces: the deployed decoder, emitted basis tables,
Rust evaluator, mixed outer joint sampler, M31-to-QM31 coordinate embedding,
codec, and serialization.  A final conditional wrapper consumes those named
interfaces; this file does not prove that the deployed artifacts satisfy them.
-/

open scoped ENNReal

namespace AspisV5MixedFieldComposition

open AspisV5ComponentBTriangularHiding
  AspisV5ComponentCUnconditionedComposition
  AspisV5ComponentCConditionalDecoupling
  AspisV5RankOneOpeningHiding
  AspisV5AtomicComponentA
  AspisV5AtomicComponentACorrespondence
  AspisCircleRectangularMasking

/-! ## A genuinely mixed-field outer experiment -/

/-- The outer coins are heterogeneous.  Only the first factor is an
`FA`-module; the remaining factors are `K`-modules. -/
abbrev MixedOuterSample (MA MH SB PB : Type*) := MA × MH × SB × PB

/-- The released outer tuple preserves the M31-rational Component-A view as
its own type.  A faithful coordinate embedding into the wire representation
is handled separately below. -/
abbrev MixedOuterVisible (VA VH SB TB VB : Type*) := VA × VH × SB × TB × VB

variable {FA K MA MH SB PB VA VH VB TB MC U Y : Type*}
variable [Field FA] [Field K]
variable [AddCommGroup MA] [Module FA MA]
variable [AddCommGroup VA] [Module FA VA]
variable [AddCommGroup MH] [Module K MH]
variable [AddCommGroup SB] [Module K SB]
variable [AddCommGroup PB] [Module K PB]
variable [AddCommGroup VH] [Module K VH]
variable [AddCommGroup VB] [Module K VB]
variable [AddCommGroup MC] [Module K MC]
variable [AddCommGroup U] [Module K U]
variable [AddCommGroup Y] [Module K Y]

/-- The complete heterogeneous outer visible tuple.  Component A is evaluated
by an `FA`-linear map; every other linear map is over `K`. -/
def mixedOuterVisible
    (LA : MA →ₗ[FA] VA) (wA : VA)
    (LH : MH →ₗ[K] VH) (wH : VH)
    (terminalB : SB → TB) (RB : SB →ₗ[K] VB) (AB : PB →ₗ[K] VB)
    (wBS : SB) (wBV : VB) :
    MixedOuterSample MA MH SB PB → MixedOuterVisible VA VH SB TB VB :=
  fun sample =>
    (wA + LA sample.1,
      wH + LH sample.2.1,
      triangularView terminalB RB AB wBS wBV
        (sample.2.2.1, sample.2.2.2))

/-- Translate all four coin factors, each in its own additive group. -/
def mixedOuterTranslationEquiv
    (dA : MA) (dH : MH) (dS : SB) (dP : PB) :
    MixedOuterSample MA MH SB PB ≃ MixedOuterSample MA MH SB PB where
  toFun sample :=
    (sample.1 + dA, sample.2.1 + dH,
      sample.2.2.1 + dS, sample.2.2.2 + dP)
  invFun sample :=
    (sample.1 - dA, sample.2.1 - dH,
      sample.2.2.1 - dS, sample.2.2.2 - dP)
  left_inv sample := by
    rcases sample with ⟨a, h, s, p⟩
    simp
  right_inv sample := by
    rcases sample with ⟨a, h, s, p⟩
    simp

@[simp]
theorem mixedOuterTranslationEquiv_apply
    (dA : MA) (dH : MH) (dS : SB) (dP : PB)
    (sample : MixedOuterSample MA MH SB PB) :
    mixedOuterTranslationEquiv dA dH dS dP sample =
      (sample.1 + dA, sample.2.1 + dH,
        sample.2.2.1 + dS, sample.2.2.2 + dP) :=
  rfl

/-- The three independent released maps supply the translation shifts.  The
Component-A surjectivity premise is over `FA`, not `K`. -/
theorem exists_mixed_outer_shifts
    (LA : MA →ₗ[FA] VA) (hLA : Function.Surjective LA)
    (LH : MH →ₗ[K] VH) (hLH : Function.Surjective LH)
    (RB : SB →ₗ[K] VB) (AB : PB →ₗ[K] VB)
    (hAB : Function.Surjective AB)
    (wA₁ wA₂ : VA) (wH₁ wH₂ : VH)
    (wBS₁ wBS₂ : SB) (wBV₁ wBV₂ : VB) :
    ∃ dA dH dP,
      LA dA = wA₂ - wA₁
        ∧ LH dH = wH₂ - wH₁
        ∧ AB dP = wBV₂ - wBV₁ - RB (wBS₂ - wBS₁) := by
  obtain ⟨dA, hdA⟩ := hLA (wA₂ - wA₁)
  obtain ⟨dH, hdH⟩ := hLH (wH₂ - wH₁)
  obtain ⟨dP, hdP⟩ := hAB (wBV₂ - wBV₁ - RB (wBS₂ - wBS₁))
  exact ⟨dA, dH, dP, hdA, hdH, hdP⟩

/-- Pointwise matching of the heterogeneous outer view.  The proof uses
`FA`-linearity only for Component A and `K`-linearity for Hcopy/B. -/
theorem mixedOuterVisible_translate
    (LA : MA →ₗ[FA] VA) (LH : MH →ₗ[K] VH)
    (terminalB : SB → TB) (RB : SB →ₗ[K] VB) (AB : PB →ₗ[K] VB)
    (wA₁ wA₂ : VA) (wH₁ wH₂ : VH)
    (wBS₁ wBS₂ : SB) (wBV₁ wBV₂ : VB)
    (dA : MA) (hdA : LA dA = wA₂ - wA₁)
    (dH : MH) (hdH : LH dH = wH₂ - wH₁)
    (dP : PB)
    (hdP : AB dP = wBV₂ - wBV₁ - RB (wBS₂ - wBS₁))
    (sample : MixedOuterSample MA MH SB PB) :
    mixedOuterVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁
        (mixedOuterTranslationEquiv dA dH (wBS₂ - wBS₁) dP sample)
      = mixedOuterVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂
          sample := by
  apply Prod.ext
  · simp only [mixedOuterVisible, mixedOuterTranslationEquiv_apply, map_add, hdA]
    abel_nf
  · apply Prod.ext
    · simp only [mixedOuterVisible, mixedOuterTranslationEquiv_apply, map_add, hdH]
      abel_nf
    · exact triangularView_translate terminalB RB AB wBS₁ wBS₂ wBV₁ wBV₂
        dP hdP (sample.2.2.1, sample.2.2.2)

/-! ## Residual projection bridge and mixed-field capstone -/

/-- Both Component-C residual coordinates are deterministic projections of
the heterogeneous outer visible tuple.  The projection itself performs any
required M31-to-QM31 embedding; no scalar action on the M31 coin space is
assumed. -/
def MixedResidualsAreVisibleProjections
    (visible : MixedOuterSample MA MH SB PB → MixedOuterVisible VA VH SB TB VB)
    (preC : MixedOuterSample MA MH SB PB → MC)
    (ell : MC →ₗ[K] K) (E : MC →ₗ[K] U)
    (publishedInactive : MixedOuterVisible VA VH SB TB VB → K)
    (publishedE : MixedOuterVisible VA VH SB TB VB → U) : Prop :=
  ∀ sample,
    ell (preC sample) = publishedInactive (visible sample)
      ∧ E (preC sample) = publishedE (visible sample)

omit [AddCommGroup MA] [Module FA MA]
  [AddCommGroup VA] [Module FA VA]
  [AddCommGroup MH] [Module K MH]
  [AddCommGroup SB] [Module K SB]
  [AddCommGroup PB] [Module K PB]
  [AddCommGroup VH] [Module K VH]
  [AddCommGroup VB] [Module K VB] in
/-- Matching the heterogeneous visible tuple transports the two Component-C
residuals through their exact published projections. -/
theorem mixed_residual_invariants_of_visible_projections
    (tau : MixedOuterSample MA MH SB PB ≃ MixedOuterSample MA MH SB PB)
    (visible₁ visible₂ :
      MixedOuterSample MA MH SB PB → MixedOuterVisible VA VH SB TB VB)
    (preC₁ preC₂ : MixedOuterSample MA MH SB PB → MC)
    (ell : MC →ₗ[K] K) (E : MC →ₗ[K] U)
    (publishedInactive : MixedOuterVisible VA VH SB TB VB → K)
    (publishedE : MixedOuterVisible VA VH SB TB VB → U)
    (hvisible : ∀ sample, visible₁ sample = visible₂ (tau sample))
    (hprojection₁ : MixedResidualsAreVisibleProjections visible₁ preC₁ ell E
      publishedInactive publishedE)
    (hprojection₂ : MixedResidualsAreVisibleProjections visible₂ preC₂ ell E
      publishedInactive publishedE) :
    ∀ sample,
      ell (preC₁ sample) = ell (preC₂ (tau sample))
        ∧ E (preC₁ sample) = E (preC₂ (tau sample)) := by
  intro sample
  exact ⟨
    (hprojection₁ sample).1 |>.trans
      ((congrArg publishedInactive (hvisible sample)).trans
        (hprojection₂ (tau sample)).1.symm),
    (hprojection₁ sample).2 |>.trans
      ((congrArg publishedE (hvisible sample)).trans
        (hprojection₂ (tau sample)).2.symm)⟩

section Capstone

variable [DecidableEq K] [Fintype MC]
variable [Fintype MA] [Fintype MH] [Fintype SB] [Fintype PB]

/-- **Conditional complete-view hiding with the deployed scalar split.**

Component A is an `FA`-linear experiment.  B, C, and `gamma` are over `K`.
The conclusion is the same complete joint-law equality as v3, without the
false requirement that the Component-A coin and view spaces be `K`-modules.
All code/model and serialization edges remain outside this implication. -/
theorem conditional_complete_joint_hiding_mixed_fields
    (LA : MA →ₗ[FA] VA) (hLA : Function.Surjective LA)
    (LH : MH →ₗ[K] VH) (hLH : Function.Surjective LH)
    (terminalB : SB → TB) (RB : SB →ₗ[K] VB) (AB : PB →ₗ[K] VB)
    (hAB : Function.Surjective AB)
    (wA₁ wA₂ : VA) (wH₁ wH₂ : VH)
    (wBS₁ wBS₂ : SB) (wBV₁ wBV₂ : VB)
    (preC₁ preC₂ : MixedOuterSample MA MH SB PB → MC)
    (ell : MC →ₗ[K] K) (E : MC →ₗ[K] U) (F : MC →ₗ[K] Y)
    (gamma : K) (hgamma : gamma ≠ 0)
    (publishedInactive : MixedOuterVisible VA VH SB TB VB → K)
    (publishedE : MixedOuterVisible VA VH SB TB VB → U)
    (hprojection₁ : MixedResidualsAreVisibleProjections
      (mixedOuterVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁)
      preC₁ ell E publishedInactive publishedE)
    (hprojection₂ : MixedResidualsAreVisibleProjections
      (mixedOuterVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂)
      preC₂ ell E publishedInactive publishedE) :
    (PMF.uniformOfFintype (MixedOuterSample MA MH SB PB)).bind
        (fun sample => unconditionedCJointKernel ell E F gamma
          (mixedOuterVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁ sample)
          (preC₁ sample))
      = (PMF.uniformOfFintype (MixedOuterSample MA MH SB PB)).bind
        (fun sample => unconditionedCJointKernel ell E F gamma
          (mixedOuterVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂ sample)
          (preC₂ sample)) := by
  obtain ⟨dA, dH, dP, hdA, hdH, hdP⟩ :=
    exists_mixed_outer_shifts LA hLA LH hLH RB AB hAB
      wA₁ wA₂ wH₁ wH₂ wBS₁ wBS₂ wBV₁ wBV₂
  let shift := mixedOuterTranslationEquiv dA dH (wBS₂ - wBS₁) dP
  let tau := shift.symm
  let visible₁ := mixedOuterVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁
  let visible₂ := mixedOuterVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂
  have hmeasure :
      (PMF.uniformOfFintype (MixedOuterSample MA MH SB PB)).map tau
        = PMF.uniformOfFintype (MixedOuterSample MA MH SB PB) :=
    uniform_map_equiv tau
  have hvisible : ∀ sample, visible₁ sample = visible₂ (tau sample) := by
    intro sample
    have hpoint := mixedOuterVisible_translate LA LH terminalB RB AB
      wA₁ wA₂ wH₁ wH₂ wBS₁ wBS₂ wBV₁ wBV₂
      dA hdA dH hdH dP hdP (tau sample)
    change visible₁ sample = visible₂ (tau sample)
    simpa only [tau, shift, Equiv.apply_symm_apply] using hpoint
  have hresidual := mixed_residual_invariants_of_visible_projections
    tau visible₁ visible₂ preC₁ preC₂ ell E publishedInactive publishedE
    hvisible hprojection₁ hprojection₂
  exact sampleAware_unconditioned_componentC_joint_law
    (PMF.uniformOfFintype (MixedOuterSample MA MH SB PB)) tau hmeasure
    preC₁ preC₂ visible₁ visible₂ ell E F hgamma hvisible
    (fun sample => (hresidual sample).1)
    (fun sample => (hresidual sample).2)

end Capstone

/-! ## The already-proved deployed M31 input

`V5AtomicComponentACorrespondence` already proves two mathematical facts used
at this boundary.  `deployedAtomicV3ComponentA_surjective` is surjectivity on
the M31 coefficient-sum hyperplane.  Its
`embeddedAtomicComponentA_hits_rational_views` theorem proves that an
arbitrary M31-to-extension ring hom preserves that hyperplane and commutes
with the matrix action.  Crucially, the latter hits **embedded M31-rational
views**, not every vector over the extension field.  The mixed-field capstone
uses exactly the former M31 surjectivity and only embeds the resulting view at
the wire boundary.  Neither theorem identifies a Rust table, decoder, sampler,
or serialized byte string with these mathematical objects.
-/

/-- The actual atomic-v3 M31 coin space: the coefficient-sum hyperplane. -/
abbrev DeployedAtomicM31CoinSpace := LinearMap.ker coefficientSum

/-- The deployed 72-by-96 evaluator restricted to the atomic-v3 M31 coin
hyperplane. -/
def deployedAtomicM31ViewMap
    (queries : Fin AspisCircleDiscreteAvailability.queryCount →
      Fin AspisCircleDiscreteAvailability.fibreCount)
    (weight : FibreIndex → DeployedField) :
    DeployedAtomicM31CoinSpace →ₗ[DeployedField]
      (FibreIndex → DeployedField) :=
  (deployedFibreRectangularEval queries weight).mulVecLin.comp
    (LinearMap.ker coefficientSum).subtype

/-- The committed atomic-v3 theorem supplies precisely the Component-A
surjectivity premise needed by the mixed-field capstone, over M31. -/
theorem deployedAtomicM31ViewMap_surjective
    (queries : Fin AspisCircleDiscreteAvailability.queryCount →
      Fin AspisCircleDiscreteAvailability.fibreCount)
    (hqueries : Function.Injective queries)
    (weight : FibreIndex → DeployedField)
    (hweight : ∀ row, weight row ≠ 0) :
    Function.Surjective (deployedAtomicM31ViewMap queries weight) := by
  intro w
  obtain ⟨c, hsum, heval⟩ :=
    deployedAtomicV3ComponentA_surjective queries hqueries weight hweight w
  refine ⟨⟨c, LinearMap.mem_ker.mpr hsum⟩, ?_⟩
  exact heval

/-- The two existing atomic results assembled without strengthening either
one: M31 surjectivity for the mixed capstone, and exact transport of those
same rational views through a specified extension-field ring hom.  This does
not assert extension-field surjectivity. -/
theorem deployed_atomic_mixed_input_and_rational_embedding
    {L : Type*} [CommRing L]
    (phi : DeployedField →+* L)
    (queries : Fin AspisCircleDiscreteAvailability.queryCount →
      Fin AspisCircleDiscreteAvailability.fibreCount)
    (hqueries : Function.Injective queries)
    (weight : FibreIndex → DeployedField)
    (hweight : ∀ row, weight row ≠ 0) :
    Function.Surjective (deployedAtomicM31ViewMap queries weight)
      ∧ ∀ w : FibreIndex → DeployedField,
        ∃ c : Fin originalWidth → DeployedField,
          (∑ i, phi (c i)) = 0 ∧
          ∀ r, ((deployedFibreRectangularEval queries weight).map phi).mulVec
            (fun i => phi (c i)) r = phi (w r) := by
  exact ⟨deployedAtomicM31ViewMap_surjective queries hqueries weight hweight,
    embeddedAtomicComponentA_hits_rational_views phi queries hqueries weight hweight⟩

/-! ## Exact coordinate and basis transport for Component A -/

variable {RawCoin RawView WireA : Type*}
variable [AddCommGroup RawCoin] [Module FA RawCoin]
variable [AddCommGroup RawView] [Module FA RawView]

/-- A commuting evaluator square is the exact algebraic code/model edge:
decode the emitted view in the declared basis, or decode the coins and apply
the Lean map.  The two results must agree pointwise. -/
def AtomicAEvaluatorSquareCommutes
    (coinCoordinates : RawCoin ≃ₗ[FA] MA)
    (viewCoordinates : RawView ≃ₗ[FA] VA)
    (rustEvaluator : RawCoin → RawView)
    (leanEvaluator : MA →ₗ[FA] VA) : Prop :=
  ∀ raw, viewCoordinates (rustEvaluator raw) = leanEvaluator (coinCoordinates raw)

/-- A coordinate equivalence carries the uniform raw-coin law to the uniform
mathematical coin law. -/
theorem uniform_atomic_coins_transport
    [Fintype RawCoin] [Fintype MA]
    (coinCoordinates : RawCoin ≃ₗ[FA] MA) :
    (PMF.uniformOfFintype RawCoin).map coinCoordinates
      = PMF.uniformOfFintype MA :=
  uniform_map_linearEquiv coinCoordinates

/-- Under the exact evaluator square, the decoded Rust view law is literally
the mathematical Component-A view law.  This is a basis/coordinate transport,
not a new hiding assumption. -/
theorem atomic_view_law_transport
    [Fintype RawCoin] [Fintype MA]
    (coinCoordinates : RawCoin ≃ₗ[FA] MA)
    (viewCoordinates : RawView ≃ₗ[FA] VA)
    (rustEvaluator : RawCoin → RawView)
    (leanEvaluator : MA →ₗ[FA] VA)
    (hcommute : AtomicAEvaluatorSquareCommutes coinCoordinates viewCoordinates
      rustEvaluator leanEvaluator)
    (w : VA) :
    (PMF.uniformOfFintype RawCoin).map
        (fun raw => w + viewCoordinates (rustEvaluator raw))
      = (PMF.uniformOfFintype MA).map
        (fun coin => w + leanEvaluator coin) := by
  let decodedView : MA → VA := fun coin => w + leanEvaluator coin
  have hfunctions :
      (fun raw => w + viewCoordinates (rustEvaluator raw))
        = decodedView ∘ coinCoordinates := by
    funext raw
    simp only [decodedView, Function.comp_apply, hcommute raw]
  rw [hfunctions, ← PMF.map_comp, uniform_atomic_coins_transport coinCoordinates]

/-- Surjectivity of the M31-linear evaluator gives the usual affine hiding
law entirely over `FA`. -/
theorem atomic_affine_view_uniform_pmf_eq
    [Fintype MA]
    (leanEvaluator : MA →ₗ[FA] VA)
    (hsurjective : Function.Surjective leanEvaluator)
    (w₁ w₂ : VA) :
    (PMF.uniformOfFintype MA).map (fun coin => w₁ + leanEvaluator coin)
      = (PMF.uniformOfFintype MA).map
          (fun coin => w₂ + leanEvaluator coin) := by
  obtain ⟨d, hd⟩ := hsurjective (w₂ - w₁)
  exact uniform_map_eq_of_equiv_comp (Equiv.addRight d) (by
    intro coin
    change w₁ + leanEvaluator (coin + d) = w₂ + leanEvaluator coin
    rw [map_add, hd]
    abel_nf)

/-- The decoded Rust Component-A view law is witness-independent once the
coordinate square and M31-linear surjectivity are both supplied. -/
theorem decoded_atomic_view_hiding
    [Fintype RawCoin] [Fintype MA]
    (coinCoordinates : RawCoin ≃ₗ[FA] MA)
    (viewCoordinates : RawView ≃ₗ[FA] VA)
    (rustEvaluator : RawCoin → RawView)
    (leanEvaluator : MA →ₗ[FA] VA)
    (hcommute : AtomicAEvaluatorSquareCommutes coinCoordinates viewCoordinates
      rustEvaluator leanEvaluator)
    (hsurjective : Function.Surjective leanEvaluator)
    (w₁ w₂ : VA) :
    (PMF.uniformOfFintype RawCoin).map
        (fun raw => w₁ + viewCoordinates (rustEvaluator raw))
      = (PMF.uniformOfFintype RawCoin).map
          (fun raw => w₂ + viewCoordinates (rustEvaluator raw)) := by
  rw [atomic_view_law_transport coinCoordinates viewCoordinates rustEvaluator
      leanEvaluator hcommute w₁,
    atomic_view_law_transport coinCoordinates viewCoordinates rustEvaluator
      leanEvaluator hcommute w₂]
  exact atomic_affine_view_uniform_pmf_eq leanEvaluator hsurjective w₁ w₂

/-! ## Faithful embedding of the rational A view into the wire view -/

/-- Embed only the Component-A coordinate; the H/B tail is unchanged. -/
def embedAtomicVisible (embedA : VA → WireA) :
    MixedOuterVisible VA VH SB TB VB → MixedOuterVisible WireA VH SB TB VB :=
  fun visible => (embedA visible.1, visible.2)

omit [AddCommGroup VA] [Module FA VA]
  [AddCommGroup VH] [Module K VH]
  [AddCommGroup SB] [Module K SB]
  [AddCommGroup VB] [Module K VB] in
/-- An injective M31-to-wire embedding gives an injective map of the whole
outer visible tuple. -/
theorem embedAtomicVisible_injective
    (embedA : VA → WireA) (hinjective : Function.Injective embedA) :
    Function.Injective (embedAtomicVisible (VH := VH) (SB := SB) (TB := TB)
      (VB := VB) embedA) := by
  intro x y hxy
  rcases x with ⟨xA, xrest⟩
  rcases y with ⟨yA, yrest⟩
  have hA : xA = yA := hinjective (congrArg Prod.fst hxy)
  have hrest : xrest = yrest := congrArg Prod.snd hxy
  rw [hA, hrest]

/-- Embed Component A in the complete output while leaving C's released
coordinates unchanged. -/
def embedAtomicCompleteOutput (embedA : VA → WireA) :
    (MixedOuterVisible VA VH SB TB VB × U × Y) →
      (MixedOuterVisible WireA VH SB TB VB × U × Y) :=
  fun output => (embedAtomicVisible embedA output.1, output.2)

omit [AddCommGroup VA] [Module FA VA]
  [AddCommGroup VH] [Module K VH]
  [AddCommGroup SB] [Module K SB]
  [AddCommGroup VB] [Module K VB]
  [AddCommGroup U] [Module K U]
  [AddCommGroup Y] [Module K Y] in
/-- Complete-view law equality is preserved exactly by the deterministic
M31-to-wire coordinate embedding. -/
theorem complete_law_transport_to_wire
    (embedA : VA → WireA)
    (q₁ q₂ : PMF (MixedOuterVisible VA VH SB TB VB × U × Y))
    (h : q₁ = q₂) :
    q₁.map (embedAtomicCompleteOutput embedA)
      = q₂.map (embedAtomicCompleteOutput embedA) := by
  rw [h]

/-! ## A genuinely two-field model and a load-bearing premise -/

namespace Model

abbrev FA₂ := ZMod 2
abbrev K₃ := ZMod 3
abbrev Sample := MixedOuterSample FA₂ K₃ K₃ K₃
abbrev Visible := MixedOuterVisible FA₂ K₃ K₃ K₃ K₃

def terminal : K₃ → K₃ := id

def view (wA : FA₂) (wH wBS wBV : K₃) : Sample → Visible :=
  mixedOuterVisible (LinearMap.id : FA₂ →ₗ[FA₂] FA₂) wA
    (LinearMap.id : K₃ →ₗ[K₃] K₃) wH terminal
    (LinearMap.id : K₃ →ₗ[K₃] K₃)
    (LinearMap.id : K₃ →ₗ[K₃] K₃) wBS wBV

def preC (wA : FA₂) (wH wBS wBV : K₃) : Sample → K₃ :=
  fun sample => (view wA wH wBS wBV sample).2.1

def projection : Visible → K₃ := fun visible => visible.2.1

theorem projection_correspondence (wA : FA₂) (wH wBS wBV : K₃) :
    MixedResidualsAreVisibleProjections (view wA wH wBS wBV)
      (preC wA wH wBS wBV)
      (LinearMap.id : K₃ →ₗ[K₃] K₃)
      (LinearMap.id : K₃ →ₗ[K₃] K₃) projection projection := by
  intro sample
  exact ⟨rfl, rfl⟩

/-- All capstone premises are satisfiable with different scalar fields
(`FA = ZMod 2`, `K = ZMod 3`) while every outer witness contribution changes.
This confirms that the theorem is not a disguised common-field statement. -/
theorem mixed_field_capstone_nonvacuous :
    (PMF.uniformOfFintype Sample).bind
        (fun sample => unconditionedCJointKernel
          (LinearMap.id : K₃ →ₗ[K₃] K₃)
          (LinearMap.id : K₃ →ₗ[K₃] K₃)
          (LinearMap.id : K₃ →ₗ[K₃] K₃) 1
          (view 0 0 0 0 sample) (preC 0 0 0 0 sample))
      = (PMF.uniformOfFintype Sample).bind
        (fun sample => unconditionedCJointKernel
          (LinearMap.id : K₃ →ₗ[K₃] K₃)
          (LinearMap.id : K₃ →ₗ[K₃] K₃)
          (LinearMap.id : K₃ →ₗ[K₃] K₃) 1
          (view 1 1 1 1 sample) (preC 1 1 1 1 sample)) :=
  conditional_complete_joint_hiding_mixed_fields
    (LinearMap.id : FA₂ →ₗ[FA₂] FA₂) (fun x => ⟨x, rfl⟩)
    (LinearMap.id : K₃ →ₗ[K₃] K₃) (fun x => ⟨x, rfl⟩)
    terminal (LinearMap.id : K₃ →ₗ[K₃] K₃)
    (LinearMap.id : K₃ →ₗ[K₃] K₃) (fun x => ⟨x, rfl⟩)
    0 1 0 1 0 1 0 1
    (preC 0 0 0 0) (preC 1 1 1 1)
    (LinearMap.id : K₃ →ₗ[K₃] K₃)
    (LinearMap.id : K₃ →ₗ[K₃] K₃)
    (LinearMap.id : K₃ →ₗ[K₃] K₃)
    1 one_ne_zero projection projection
    (projection_correspondence 0 0 0 0)
    (projection_correspondence 1 1 1 1)

/-- Component-A surjectivity remains load-bearing in the mixed-field setting:
the zero evaluator over M31 leaves the witness shift exposed. -/
theorem atomic_surjectivity_is_loadBearing :
    (PMF.uniformOfFintype FA₂).map
        (fun coin => (0 : FA₂) + (0 : FA₂ →ₗ[FA₂] FA₂) coin)
      ≠ (PMF.uniformOfFintype FA₂).map
        (fun coin => (1 : FA₂) + (0 : FA₂ →ₗ[FA₂] FA₂) coin) := by
  intro h
  have hzero := congrArg (fun q : PMF FA₂ => q 0) h
  simp at hzero

end Model

/-! ## Explicit, currently unproved deployment interfaces -/

namespace UnmetDeployment

/-- The emitted M31 free-coin table and the Lean natural-basis coordinate map
are the same linear equivalence.  This is a named code/data edge. -/
def RustAtomicACoinBasisCorrespondence
    (rustCoinBasis leanCoinBasis : RawCoin ≃ₗ[FA] MA) : Prop :=
  rustCoinBasis = leanCoinBasis

/-- The emitted M31 released-view table and the Lean view coordinates use the
same row order, signs, natural basis, and aligned weights. -/
def RustAtomicAViewBasisCorrespondence
    (rustViewBasis leanViewBasis : RawView ≃ₗ[FA] VA) : Prop :=
  rustViewBasis = leanViewBasis

/-- The decoded production Component-A coins are exactly uniform in the raw
M31 coordinate space.  Deterministic fixtures do not establish this premise. -/
def RustAtomicACoinSamplerIsUniform
    [Fintype RawCoin] (rustSampler : PMF RawCoin) : Prop :=
  rustSampler = PMF.uniformOfFintype RawCoin

/-- The concrete Rust evaluator commutes with the two declared coordinate
equivalences and the Lean M31-linear map. -/
def RustAtomicAEvaluatorCorrespondence
    (coinCoordinates : RawCoin ≃ₗ[FA] MA)
    (viewCoordinates : RawView ≃ₗ[FA] VA)
    (rustEvaluator : RawCoin → RawView)
    (leanEvaluator : MA →ₗ[FA] VA) : Prop :=
  AtomicAEvaluatorSquareCommutes coinCoordinates viewCoordinates
    rustEvaluator leanEvaluator

/-- The M31-rational Component-A view is embedded faithfully into the QM31
wire coordinates, and the byte decoder/encoder agree with that exact map.
No field-extension or codec implementation is defined in this corpus, so the
three clauses remain a deployment interface. -/
def M31ViewToQM31WireCorrespondence {Bytes : Type*}
    (embedA : VA → WireA) (encodeWire : WireA → Bytes)
    (decodeWire : Bytes → Option WireA)
    (rustEmbed : VA → WireA) : Prop :=
  Function.Injective embedA
    ∧ rustEmbed = embedA
    ∧ ∀ v, decodeWire (encodeWire (embedA v)) = some (embedA v)

/-- The serialized complete Rust view is the deterministic image of the
heterogeneous mathematical output, with its typed B/C coordinates supplied to
the serializer alongside the faithful A-coordinate embedding. This interface
does not itself assert serializer injectivity or byte-level completeness. -/
def RustMixedCompleteSerializationCorrespondence {Bytes : Type*}
    (embedA : VA → WireA)
    (serialize : (MixedOuterVisible WireA VH SB TB VB × U × Y) → Bytes)
    (rustBytes : (MixedOuterVisible VA VH SB TB VB × U × Y) → Bytes) : Prop :=
  ∀ output, rustBytes output = serialize (embedAtomicCompleteOutput embedA output)

/-! ### The actual mixed outer law and evaluator seam -/

/-- Rust's outer sample before converting the Component-A M31 coordinates.
The Hcopy and B factors already use their `K`-module model types. -/
abbrev RawMixedOuterSample (RawCoin MH SB PB : Type*) :=
  RawCoin × MH × SB × PB

/-- Decode only the Component-A coin coordinate table. -/
def decodeRawMixedOuter
    (coinCoordinates : RawCoin ≃ₗ[FA] MA) :
    RawMixedOuterSample RawCoin MH SB PB → MixedOuterSample MA MH SB PB :=
  fun raw =>
    (coinCoordinates raw.1, raw.2.1, raw.2.2.1, raw.2.2.2)

/-- The actual Rust outer evaluator after decoding its emitted Component-A
view coordinates.  The tail contains Hcopy and the one triangular B view. -/
def rustDecodedMixedOuterVisible
    (viewCoordinates : RawView ≃ₗ[FA] VA)
    (rustEvaluator : RawCoin → RawView)
    (rustTail : RawMixedOuterSample RawCoin MH SB PB →
      VH × SB × TB × VB)
    (wA : VA) :
    RawMixedOuterSample RawCoin MH SB PB →
      MixedOuterVisible VA VH SB TB VB :=
  fun raw => (wA + viewCoordinates (rustEvaluator raw.1), rustTail raw)

/-- Exact mixed outer joint-independence correspondence.  This is stronger
than four marginal-uniformity claims: after applying the actual Component-A
coin basis, the complete Rust outer law must be the uniform product law used
by the capstone. -/
def RustMixedOuterJointIndependenceCorrespondence
    [Fintype MA] [Fintype MH] [Fintype SB] [Fintype PB]
    (coinCoordinates : RawCoin ≃ₗ[FA] MA)
    (rustASampler : PMF RawCoin)
    (rustOuterSampler : PMF (RawMixedOuterSample RawCoin MH SB PB)) : Prop :=
  rustOuterSampler.map Prod.fst = rustASampler
    ∧ rustOuterSampler.map (decodeRawMixedOuter coinCoordinates)
      = PMF.uniformOfFintype (MixedOuterSample MA MH SB PB)

/-- Exact tail-evaluator and pre-C correspondence for one run.  Component A's
head is intentionally absent: it is derived from the separate basis and
evaluator-square premises rather than repeated here. -/
def RustMixedOuterTailAndPreCCorrespondence
    (coinCoordinates : RawCoin ≃ₗ[FA] MA)
    (LA : MA →ₗ[FA] VA) (wA : VA)
    (LH : MH →ₗ[K] VH) (wH : VH)
    (terminalB : SB → TB) (RB : SB →ₗ[K] VB) (AB : PB →ₗ[K] VB)
    (wBS : SB) (wBV : VB)
    (preC : MixedOuterSample MA MH SB PB → MC)
    (rustTail : RawMixedOuterSample RawCoin MH SB PB →
      VH × SB × TB × VB)
    (rustPreC : RawMixedOuterSample RawCoin MH SB PB → MC) : Prop :=
  ∀ raw,
    rustTail raw =
        (mixedOuterVisible LA wA LH wH terminalB RB AB wBS wBV
          (decodeRawMixedOuter coinCoordinates raw)).2
      ∧ rustPreC raw = preC (decodeRawMixedOuter coinCoordinates raw)

/-- The decoded complete law produced from the actual Rust outer sampler and
its per-run evaluator functions.  Component C is still the conditional
uniform-kernel model; binding a production C sampler remains one of the v3
capstone's separately named deployment obligations. -/
noncomputable def rustDecodedCompleteLaw
    [DecidableEq K] [Fintype MC]
    {RustOuter Visible : Type*}
    (rustOuterSampler : PMF RustOuter)
    (rustVisible : RustOuter → Visible) (rustPreC : RustOuter → MC)
    (ell : MC →ₗ[K] K) (E : MC →ₗ[K] U) (F : MC →ₗ[K] Y)
    (gamma : K) : PMF (Visible × U × Y) :=
  rustOuterSampler.bind fun raw =>
    unconditionedCJointKernel ell E F gamma (rustVisible raw) (rustPreC raw)

section DeploymentWrapper

variable [DecidableEq K] [Fintype MC]
variable [Fintype MA] [Fintype MH] [Fintype SB] [Fintype PB]
variable [Fintype RawCoin]

/-- **Conditional deployed mixed-field wrapper.**

The first conclusion is the actual decoded Component-A marginal law.  The
second is the actual decoded complete law.  The third is equality after the
two run-specific Rust serializers.  The last two conclusions certify that
the M31-to-QM31 outer-view embedding is faithful and round-trips through the
declared wire codec.

Every deployment premise is consumed:

* the two basis equalities and evaluator square identify the Rust A head;
* A sampler uniformity proves the decoded A marginal equality;
* mixed joint independence reindexes the actual outer sampler;
* the two tail/pre-C correspondences identify both run kernels;
* the embedding correspondence supplies equality, injectivity, and codec
  round-trip;
* the two serialization correspondences identify the run-specific byte laws.

This remains conditional.  In particular, it does not prove any of these
facts for production artifacts and it still uses the abstract uniform
Component-C kernel inside `rustDecodedCompleteLaw`. -/
theorem conditional_deployed_mixed_serialized_hiding
    {Bytes : Type*}
    (LA : MA →ₗ[FA] VA) (hLA : Function.Surjective LA)
    (LH : MH →ₗ[K] VH) (hLH : Function.Surjective LH)
    (terminalB : SB → TB) (RB : SB →ₗ[K] VB) (AB : PB →ₗ[K] VB)
    (hAB : Function.Surjective AB)
    (wA₁ wA₂ : VA) (wH₁ wH₂ : VH)
    (wBS₁ wBS₂ : SB) (wBV₁ wBV₂ : VB)
    (preC₁ preC₂ : MixedOuterSample MA MH SB PB → MC)
    (ell : MC →ₗ[K] K) (E : MC →ₗ[K] U) (F : MC →ₗ[K] Y)
    (gamma : K) (hgamma : gamma ≠ 0)
    (publishedInactive : MixedOuterVisible VA VH SB TB VB → K)
    (publishedE : MixedOuterVisible VA VH SB TB VB → U)
    (hprojection₁ : MixedResidualsAreVisibleProjections
      (mixedOuterVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁)
      preC₁ ell E publishedInactive publishedE)
    (hprojection₂ : MixedResidualsAreVisibleProjections
      (mixedOuterVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂)
      preC₂ ell E publishedInactive publishedE)
    (rustCoinBasis leanCoinBasis : RawCoin ≃ₗ[FA] MA)
    (rustViewBasis leanViewBasis : RawView ≃ₗ[FA] VA)
    (rustASampler : PMF RawCoin)
    (rustOuterSampler : PMF (RawMixedOuterSample RawCoin MH SB PB))
    (rustEvaluator : RawCoin → RawView)
    (rustTail₁ rustTail₂ : RawMixedOuterSample RawCoin MH SB PB →
      VH × SB × TB × VB)
    (rustPreC₁ rustPreC₂ : RawMixedOuterSample RawCoin MH SB PB → MC)
    (embedA rustEmbed : VA → WireA)
    (encodeWire : WireA → Bytes) (decodeWire : Bytes → Option WireA)
    (serialize : (MixedOuterVisible WireA VH SB TB VB × U × Y) → Bytes)
    (rustBytes₁ rustBytes₂ :
      (MixedOuterVisible VA VH SB TB VB × U × Y) → Bytes)
    (hcoinBasis : RustAtomicACoinBasisCorrespondence rustCoinBasis leanCoinBasis)
    (hviewBasis : RustAtomicAViewBasisCorrespondence rustViewBasis leanViewBasis)
    (hASampler : RustAtomicACoinSamplerIsUniform rustASampler)
    (hEvaluator : RustAtomicAEvaluatorCorrespondence
      leanCoinBasis leanViewBasis rustEvaluator LA)
    (hJoint : RustMixedOuterJointIndependenceCorrespondence
      rustCoinBasis rustASampler rustOuterSampler)
    (hTail₁ : RustMixedOuterTailAndPreCCorrespondence
      leanCoinBasis LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁
      preC₁ rustTail₁ rustPreC₁)
    (hTail₂ : RustMixedOuterTailAndPreCCorrespondence
      leanCoinBasis LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂
      preC₂ rustTail₂ rustPreC₂)
    (hEmbed : M31ViewToQM31WireCorrespondence
      embedA encodeWire decodeWire rustEmbed)
    (hSerialize₁ : RustMixedCompleteSerializationCorrespondence
      rustEmbed serialize rustBytes₁)
    (hSerialize₂ : RustMixedCompleteSerializationCorrespondence
      rustEmbed serialize rustBytes₂) :
    (rustOuterSampler.map Prod.fst).map
        (fun raw => wA₁ + rustViewBasis (rustEvaluator raw))
      = (rustOuterSampler.map Prod.fst).map
        (fun raw => wA₂ + rustViewBasis (rustEvaluator raw))
      ∧ rustDecodedCompleteLaw rustOuterSampler
          (rustDecodedMixedOuterVisible rustViewBasis rustEvaluator rustTail₁ wA₁)
          rustPreC₁ ell E F gamma
        = rustDecodedCompleteLaw rustOuterSampler
          (rustDecodedMixedOuterVisible rustViewBasis rustEvaluator rustTail₂ wA₂)
          rustPreC₂ ell E F gamma
      ∧ (rustDecodedCompleteLaw rustOuterSampler
          (rustDecodedMixedOuterVisible rustViewBasis rustEvaluator rustTail₁ wA₁)
          rustPreC₁ ell E F gamma).map rustBytes₁
        = (rustDecodedCompleteLaw rustOuterSampler
          (rustDecodedMixedOuterVisible rustViewBasis rustEvaluator rustTail₂ wA₂)
          rustPreC₂ ell E F gamma).map rustBytes₂
      ∧ Function.Injective
        (embedAtomicVisible (VH := VH) (SB := SB) (TB := TB) (VB := VB) embedA)
      ∧ ∀ v, decodeWire (encodeWire (rustEmbed v)) = some (rustEmbed v) := by
  have hcoinEq : rustCoinBasis = leanCoinBasis := hcoinBasis
  have hviewEq : rustViewBasis = leanViewBasis := hviewBasis
  subst leanCoinBasis
  subst leanViewBasis
  have hevaluator : AtomicAEvaluatorSquareCommutes
      rustCoinBasis rustViewBasis rustEvaluator LA := hEvaluator
  have hA :
      (rustOuterSampler.map Prod.fst).map
          (fun raw => wA₁ + rustViewBasis (rustEvaluator raw))
        = (rustOuterSampler.map Prod.fst).map
          (fun raw => wA₂ + rustViewBasis (rustEvaluator raw)) := by
    rw [hJoint.1, hASampler]
    exact decoded_atomic_view_hiding rustCoinBasis rustViewBasis rustEvaluator
      LA hevaluator hLA wA₁ wA₂
  let decode : RawMixedOuterSample RawCoin MH SB PB →
      MixedOuterSample MA MH SB PB :=
    decodeRawMixedOuter (MH := MH) (SB := SB) (PB := PB) rustCoinBasis
  let modelVisible₁ := mixedOuterVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁
  let modelVisible₂ := mixedOuterVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂
  let rustVisible₁ := rustDecodedMixedOuterVisible
    rustViewBasis rustEvaluator rustTail₁ wA₁
  let rustVisible₂ := rustDecodedMixedOuterVisible
    rustViewBasis rustEvaluator rustTail₂ wA₂
  have hvisible₁ : ∀ raw, rustVisible₁ raw = modelVisible₁ (decode raw) := by
    intro raw
    apply Prod.ext
    · exact congrArg (wA₁ + ·) (hevaluator raw.1)
    · exact (hTail₁ raw).1
  have hvisible₂ : ∀ raw, rustVisible₂ raw = modelVisible₂ (decode raw) := by
    intro raw
    apply Prod.ext
    · exact congrArg (wA₂ + ·) (hevaluator raw.1)
    · exact (hTail₂ raw).1
  have hpreC₁ : ∀ raw, rustPreC₁ raw = preC₁ (decode raw) :=
    fun raw => (hTail₁ raw).2
  have hpreC₂ : ∀ raw, rustPreC₂ raw = preC₂ (decode raw) :=
    fun raw => (hTail₂ raw).2
  let modelKernel₁ := fun sample => unconditionedCJointKernel ell E F gamma
    (modelVisible₁ sample) (preC₁ sample)
  let modelKernel₂ := fun sample => unconditionedCJointKernel ell E F gamma
    (modelVisible₂ sample) (preC₂ sample)
  let rustKernel₁ := fun raw => unconditionedCJointKernel ell E F gamma
    (rustVisible₁ raw) (rustPreC₁ raw)
  let rustKernel₂ := fun raw => unconditionedCJointKernel ell E F gamma
    (rustVisible₂ raw) (rustPreC₂ raw)
  have hkernel₁ : rustKernel₁ = modelKernel₁ ∘ decode := by
    funext raw
    simp only [rustKernel₁, modelKernel₁, Function.comp_apply,
      hvisible₁ raw, hpreC₁ raw]
  have hkernel₂ : rustKernel₂ = modelKernel₂ ∘ decode := by
    funext raw
    simp only [rustKernel₂, modelKernel₂, Function.comp_apply,
      hvisible₂ raw, hpreC₂ raw]
  have hmodel :
      (PMF.uniformOfFintype (MixedOuterSample MA MH SB PB)).bind modelKernel₁
        = (PMF.uniformOfFintype (MixedOuterSample MA MH SB PB)).bind modelKernel₂ :=
    conditional_complete_joint_hiding_mixed_fields
      LA hLA LH hLH terminalB RB AB hAB
      wA₁ wA₂ wH₁ wH₂ wBS₁ wBS₂ wBV₁ wBV₂
      preC₁ preC₂ ell E F gamma hgamma publishedInactive publishedE
      hprojection₁ hprojection₂
  have hdecoded :
      rustDecodedCompleteLaw rustOuterSampler rustVisible₁ rustPreC₁ ell E F gamma
        = rustDecodedCompleteLaw rustOuterSampler rustVisible₂ rustPreC₂ ell E F gamma := by
    change rustOuterSampler.bind rustKernel₁ = rustOuterSampler.bind rustKernel₂
    calc
      rustOuterSampler.bind rustKernel₁
          = rustOuterSampler.bind (modelKernel₁ ∘ decode) := by rw [hkernel₁]
      _ = (rustOuterSampler.map decode).bind modelKernel₁ :=
        (PMF.bind_map rustOuterSampler decode modelKernel₁).symm
      _ = (PMF.uniformOfFintype (MixedOuterSample MA MH SB PB)).bind
          modelKernel₁ := by rw [hJoint.2]
      _ = (PMF.uniformOfFintype (MixedOuterSample MA MH SB PB)).bind
          modelKernel₂ := hmodel
      _ = (rustOuterSampler.map decode).bind modelKernel₂ := by rw [hJoint.2]
      _ = rustOuterSampler.bind (modelKernel₂ ∘ decode) :=
        PMF.bind_map rustOuterSampler decode modelKernel₂
      _ = rustOuterSampler.bind rustKernel₂ := by rw [hkernel₂]
  have hembedEq : rustEmbed = embedA := hEmbed.2.1
  have hbytes₁ : rustBytes₁ =
      fun output => serialize (embedAtomicCompleteOutput embedA output) := by
    funext output
    rw [hSerialize₁ output, hembedEq]
  have hbytes₂ : rustBytes₂ =
      fun output => serialize (embedAtomicCompleteOutput embedA output) := by
    funext output
    rw [hSerialize₂ output, hembedEq]
  have hserialized :
      (rustDecodedCompleteLaw rustOuterSampler rustVisible₁ rustPreC₁
          ell E F gamma).map rustBytes₁
        = (rustDecodedCompleteLaw rustOuterSampler rustVisible₂ rustPreC₂
          ell E F gamma).map rustBytes₂ := by
    rw [hbytes₁, hbytes₂, hdecoded]
  refine ⟨hA, hdecoded, hserialized,
    embedAtomicVisible_injective embedA hEmbed.1, ?_⟩
  intro v
  rw [hembedEq]
  exact hEmbed.2.2 v

end DeploymentWrapper

/-! ### Tiny instantiation and a joint-independence deletion test -/

namespace WrapperModel

abbrev F := ZMod 2
abbrev RawOuter := RawMixedOuterSample F Unit Unit Unit
abbrev Outer := MixedOuterSample F Unit Unit Unit
abbrev Visible := MixedOuterVisible F Unit Unit Unit Unit

def coinBasis : F ≃ₗ[F] F := LinearEquiv.refl F F
def viewBasis : F ≃ₗ[F] F := LinearEquiv.refl F F
def evaluator : F → F := id
noncomputable def outerSampler : PMF RawOuter := PMF.uniformOfFintype RawOuter

def modelVisible : Outer → Visible :=
  mixedOuterVisible (LinearMap.id : F →ₗ[F] F) 0
    (LinearMap.id : Unit →ₗ[F] Unit) () id
    (LinearMap.id : Unit →ₗ[F] Unit)
    (LinearMap.id : Unit →ₗ[F] Unit) () ()

def tail (raw : RawOuter) : Unit × Unit × Unit × Unit :=
  (modelVisible (decodeRawMixedOuter coinBasis raw)).2

def preC : Outer → Unit := fun _ => ()
def rustPreC (raw : RawOuter) : Unit := preC (decodeRawMixedOuter coinBasis raw)

def embed : F → F := id
def wireEncode : F → F := id
def wireDecode : F → Option F := some
def serialize : (Visible × Unit × Unit) → F := fun output => output.1.1
def rustBytes : (Visible × Unit × Unit) → F :=
  fun output => serialize (embedAtomicCompleteOutput embed output)

/-- With three singleton tail factors, the first projection is an
equivalence. -/
def firstEquiv : RawOuter ≃ F where
  toFun raw := raw.1
  invFun a := (a, (), (), ())
  left_inv raw := by
    rcases raw with ⟨a, ⟨⟩, ⟨⟩, ⟨⟩⟩
    rfl
  right_inv a := rfl

theorem joint_instantiable :
    RustMixedOuterJointIndependenceCorrespondence coinBasis
      (PMF.uniformOfFintype F) outerSampler := by
  constructor
  · change (PMF.uniformOfFintype RawOuter).map firstEquiv =
      PMF.uniformOfFintype F
    exact uniform_map_equiv firstEquiv
  · change (PMF.uniformOfFintype RawOuter).map id = PMF.uniformOfFintype Outer
    exact PMF.map_id _

/-- Every deployment interface consumed by the wrapper is simultaneously
satisfiable in one finite model.  The two run-specific tail and serialization
premises use the same functions here; the wrapper itself permits them to
differ. -/
theorem deployment_bundle_instantiable :
    RustAtomicACoinBasisCorrespondence coinBasis coinBasis
      ∧ RustAtomicAViewBasisCorrespondence viewBasis viewBasis
      ∧ RustAtomicACoinSamplerIsUniform
        (PMF.uniformOfFintype F)
      ∧ RustAtomicAEvaluatorCorrespondence coinBasis viewBasis evaluator
        (LinearMap.id : F →ₗ[F] F)
      ∧ RustMixedOuterJointIndependenceCorrespondence coinBasis
        (PMF.uniformOfFintype F) outerSampler
      ∧ RustMixedOuterTailAndPreCCorrespondence coinBasis
        (LinearMap.id : F →ₗ[F] F) 0
        (LinearMap.id : Unit →ₗ[F] Unit) () id
        (LinearMap.id : Unit →ₗ[F] Unit)
        (LinearMap.id : Unit →ₗ[F] Unit) () () preC tail rustPreC
      ∧ RustMixedOuterTailAndPreCCorrespondence coinBasis
        (LinearMap.id : F →ₗ[F] F) 0
        (LinearMap.id : Unit →ₗ[F] Unit) () id
        (LinearMap.id : Unit →ₗ[F] Unit)
        (LinearMap.id : Unit →ₗ[F] Unit) () () preC tail rustPreC
      ∧ M31ViewToQM31WireCorrespondence
        embed wireEncode wireDecode embed
      ∧ RustMixedCompleteSerializationCorrespondence
        embed serialize rustBytes
      ∧ RustMixedCompleteSerializationCorrespondence
        embed serialize rustBytes := by
  refine ⟨rfl, rfl, rfl, ?_, joint_instantiable, ?_, ?_, ?_, ?_, ?_⟩
  · intro raw
    rfl
  · intro raw
    exact ⟨rfl, rfl⟩
  · intro raw
    exact ⟨rfl, rfl⟩
  · exact ⟨Function.injective_id, rfl, fun v => rfl⟩
  · intro output
    rfl
  · intro output
    rfl

/-- A diagonal outer sampler has a uniform Component-A marginal but is not
the independent uniform joint law.  Shifting only the A witness changes the
joint `(A,H)` view.  Thus marginal A uniformity cannot replace the explicit
mixed joint-independence premise. -/
theorem joint_independence_is_loadBearing :
    let CorrelatedOuter := RawMixedOuterSample F F Unit Unit
    let rho : PMF CorrelatedOuter :=
      (PMF.uniformOfFintype F).map fun a => (a, a, (), ())
    rho.map (fun raw => raw.1) = PMF.uniformOfFintype F
      ∧ ¬ RustMixedOuterJointIndependenceCorrespondence coinBasis
        (PMF.uniformOfFintype F) rho
      ∧ rho.map (fun raw => (raw.1, raw.2.1))
        ≠ rho.map (fun raw => (1 + raw.1, raw.2.1)) := by
  dsimp
  constructor
  · rw [PMF.map_comp]
    exact PMF.map_id _
  constructor
  · intro hjoint
    have hsupport := congrArg PMF.support hjoint.2
    have hoff : (0, 1, (), ()) ∈
        (PMF.uniformOfFintype (MixedOuterSample F F Unit Unit)).support := by simp
    rw [← hsupport] at hoff
    simp [decodeRawMixedOuter, coinBasis] at hoff
  · intro hlaw
    have hsupport := congrArg PMF.support hlaw
    have hleft : (0, 0) ∈
        (((PMF.uniformOfFintype F).map fun a => (a, a, (), ())).map
          (fun raw : RawMixedOuterSample F F Unit Unit =>
            (raw.1, raw.2.1))).support := by simp
    rw [hsupport] at hleft
    simp at hleft

end WrapperModel

end UnmetDeployment

#print axioms mixedOuterTranslationEquiv_apply
#print axioms exists_mixed_outer_shifts
#print axioms mixedOuterVisible_translate
#print axioms MixedResidualsAreVisibleProjections
#print axioms mixed_residual_invariants_of_visible_projections
#print axioms conditional_complete_joint_hiding_mixed_fields
#print axioms deployedAtomicM31ViewMap_surjective
#print axioms deployed_atomic_mixed_input_and_rational_embedding
#print axioms AtomicAEvaluatorSquareCommutes
#print axioms uniform_atomic_coins_transport
#print axioms atomic_view_law_transport
#print axioms atomic_affine_view_uniform_pmf_eq
#print axioms decoded_atomic_view_hiding
#print axioms embedAtomicVisible_injective
#print axioms complete_law_transport_to_wire
#print axioms Model.projection_correspondence
#print axioms Model.mixed_field_capstone_nonvacuous
#print axioms Model.atomic_surjectivity_is_loadBearing
#print axioms UnmetDeployment.RustAtomicACoinBasisCorrespondence
#print axioms UnmetDeployment.RustAtomicAViewBasisCorrespondence
#print axioms UnmetDeployment.RustAtomicACoinSamplerIsUniform
#print axioms UnmetDeployment.RustAtomicAEvaluatorCorrespondence
#print axioms UnmetDeployment.M31ViewToQM31WireCorrespondence
#print axioms UnmetDeployment.RustMixedCompleteSerializationCorrespondence
#print axioms UnmetDeployment.RustMixedOuterJointIndependenceCorrespondence
#print axioms UnmetDeployment.RustMixedOuterTailAndPreCCorrespondence
#print axioms UnmetDeployment.rustDecodedCompleteLaw
#print axioms UnmetDeployment.conditional_deployed_mixed_serialized_hiding
#print axioms UnmetDeployment.WrapperModel.joint_instantiable
#print axioms UnmetDeployment.WrapperModel.deployment_bundle_instantiable
#print axioms UnmetDeployment.WrapperModel.joint_independence_is_loadBearing

end AspisV5MixedFieldComposition
