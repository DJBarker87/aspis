import Mathlib
import AspisFormal.CoreHidingPMF
import AspisFormal.SumcheckMasking
import AspisFormal.CircleRectangularMasking

/-!
# The v5 complete-view obligation

This file is an obligation ledger, not a model of a completed v5 prover,
verifier or serialiser.  In particular, it contains no proposed production
field inventory: the commitment and opening formats for components B and C
have not yet been selected, so their point claims, authentication data and
wire sizes cannot honestly be counted.

The current status is deliberately asymmetric.

* Component A has a provisional algebraic result.  For every injective q18
  fibre schedule and every nonzero abstract row weighting, the M31 72-by-96
  layer-zero evaluation map is surjective.  The Rust index order, basis
  conversion, actual row weights, sampler, field representation and transcript
  binding remain separate obligations.
* Component B has only the chained zero-boundary algebra in
  `SumcheckMasking`.  Its distribution theorems use externally supplied round
  labels.  No pre-eta binding commitment, adaptive Fiat--Shamir composition or
  authenticated terminal opening is instantiated here.
* Component C is still a protocol construction obligation.  Neither its mask
  source nor a commitment-consistency and opening argument is supplied here.

Sixteen M31 C1 lanes are the provisional Component-A width.  Three auxiliary
QM31 C2 lanes are recorded only as a CU envelope: this file does not assert
that three lanes suffice for, or are used by, the eventual B/C construction.

The generic affine lemmas below are conditional sufficient templates.  They
do not require the eventual protocol to decompose into three independent
affine blocks, and they make no claim about hash roots, salts, Merkle paths or
other commitment bytes.
-/

open scoped ENNReal

namespace AspisV5CompleteView

open AspisCircleDiscreteAvailability
open AspisCircleRectangularMasking

/-! ## Provisional dimensions, not a wire inventory -/

/-- Provisional number of M31 semantic lanes covered by Component A. -/
def componentAC1LaneCount : ℕ := 16

/-- Upper budget for auxiliary QM31 lanes in the current CU envelope.  This is
not a theorem that a sound B/C commitment fits in that budget. -/
def auxiliaryC2LaneBudget : ℕ := 3

theorem provisional_lane_counts :
    componentAC1LaneCount = 16 ∧ auxiliaryC2LaneBudget = 3 := by
  decide

/-- Field elements in the algebraic ten-round degree-27 B transcript: one
initial claim and 28 coefficients in each round.  This is not a commitment or
wire-size count. -/
def algebraicBTranscriptWords : ℕ := 1 + 10 * (27 + 1)

/-- Independent field coordinates in the ideal B mask-state type: one initial
state and 27 freely sampled tail coefficients in each round.  The arithmetic
identity below compares this parameter count with ten 28-coefficient messages;
it does not prove a transcript embedding or adaptive composition. -/
def algebraicBMaskCoordinates : ℕ := 1 + 10 * 27

theorem algebraicB_dimensions :
    algebraicBTranscriptWords = 281 ∧
      algebraicBMaskCoordinates = 271 ∧
      algebraicBTranscriptWords = algebraicBMaskCoordinates + 10 := by
  norm_num [algebraicBTranscriptWords, algebraicBMaskCoordinates]

/-- The coefficient-vector type used by the degree-27 algebraic model. -/
abbrev Degree27RoundMessage (K : Type*) [Field K] :=
  AspisSumcheckMasking.RoundCoeff K 27

/-- The ten-round zero-boundary family from `SumcheckMasking`.  This alias does
not supply a commitment, opening scheme or adaptive transcript theorem. -/
abbrev TenRoundZeroBoundaryMasks (K : Type*) [Field K] :=
  AspisSumcheckMasking.RoundMaskFamily K 10 27

theorem degree27_message_coefficient_count : Fintype.card (Fin (27 + 1)) = 28 := by
  decide

/-! ## Generic conditional block composition -/

section BlockMaps

variable {K : Type*} [Field K]
variable {MA MB MC VA VB VC : Type*}
variable [AddCommMonoid MA] [Module K MA]
variable [AddCommMonoid MB] [Module K MB]
variable [AddCommMonoid MC] [Module K MC]
variable [AddCommMonoid VA] [Module K VA]
variable [AddCommMonoid VB] [Module K VB]
variable [AddCommMonoid VC] [Module K VC]

/-- Block-diagonal map for three independent ideal mask components.  No
production decomposition is asserted. -/
def threeBlockMap (A : MA →ₗ[K] VA) (B : MB →ₗ[K] VB)
    (C : MC →ₗ[K] VC) :
    (MA × (MB × MC)) →ₗ[K] (VA × (VB × VC)) where
  toFun mask := (A mask.1, (B mask.2.1, C mask.2.2))
  map_add' x y := by ext <;> simp
  map_smul' scalar x := by ext <;> simp

/-- Independent surjectivity of three ideal components is sufficient for
surjectivity of their block-diagonal map. -/
theorem threeBlockMap_surjective
    (A : MA →ₗ[K] VA) (B : MB →ₗ[K] VB) (C : MC →ₗ[K] VC)
    (hA : Function.Surjective A) (hB : Function.Surjective B)
    (hC : Function.Surjective C) :
    Function.Surjective (threeBlockMap A B C) := by
  rintro ⟨va, vb, vc⟩
  obtain ⟨ma, hma⟩ := hA va
  obtain ⟨mb, hmb⟩ := hB vb
  obtain ⟨mc, hmc⟩ := hC vc
  refine ⟨⟨ma, mb, mc⟩, ?_⟩
  simp [threeBlockMap, hma, hmb, hmc]

/-- Surjective pre-processing, three surjective ideal blocks and a surjective
flattening compose to a surjective flat legal-view map.  This is a generic
linear-algebra fact, not a statement about the v5 wire. -/
theorem composed_threeBlockMap_surjective
    {FlatMask FlatView : Type*}
    [AddCommMonoid FlatMask] [Module K FlatMask]
    [AddCommMonoid FlatView] [Module K FlatView]
    (split : FlatMask →ₗ[K] (MA × (MB × MC)))
    (A : MA →ₗ[K] VA) (B : MB →ₗ[K] VB) (C : MC →ₗ[K] VC)
    (flatten : (VA × (VB × VC)) →ₗ[K] FlatView)
    (hsplit : Function.Surjective split)
    (hA : Function.Surjective A) (hB : Function.Surjective B)
    (hC : Function.Surjective C)
    (hflatten : Function.Surjective flatten) :
    Function.Surjective
      (flatten.comp ((threeBlockMap A B C).comp split)) := by
  exact hflatten.comp ((threeBlockMap_surjective A B C hA hB hC).comp hsplit)

/-- Apply one linear map independently in each lane. -/
def laneFamilyMap (lanes : ℕ) (A : MA →ₗ[K] VA) :
    (Fin lanes → MA) →ₗ[K] (Fin lanes → VA) where
  toFun masks lane := A (masks lane)
  map_add' x y := by ext; simp
  map_smul' scalar x := by ext; simp

theorem laneFamilyMap_surjective (lanes : ℕ) (A : MA →ₗ[K] VA)
    (hA : Function.Surjective A) :
    Function.Surjective (laneFamilyMap lanes A) := by
  intro values
  choose masks hmasks using fun lane => hA (values lane)
  exact ⟨masks, by funext lane; exact hmasks lane⟩

end BlockMaps

/-! ## What a complete ideal affine map would imply -/

section CompleteAffineHiding

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {W : Type*} {maskCoordinates viewCoordinates : ℕ}

/-- Once a complete flat ideal mask map is surjective, its affine view is
witness-independent.  This does not prove that an adaptive Fiat--Shamir
transcript is such a view. -/
theorem completeAffineView_pmf_indep
    (maskMap : (Fin maskCoordinates → K) →ₗ[K]
      (Fin viewCoordinates → K))
    (hmaskMap : Function.Surjective maskMap)
    (witnessShift : W → (Fin viewCoordinates → K))
    (w₁ w₂ : W) :
    (PMF.uniformOfFintype (Fin maskCoordinates → K)).map
        (fun mask => witnessShift w₁ + maskMap mask) =
      (PMF.uniformOfFintype (Fin maskCoordinates → K)).map
        (fun mask => witnessShift w₂ + maskMap mask) :=
  view_pmf_indep_of_witness maskMap hmaskMap
    (witnessShift w₁) (witnessShift w₂)

/-- Any deterministic observation of a hidden ideal affine view remains
witness-independent.  This does not establish that the observer is the Rust
transcript. -/
theorem observedCompleteAffineView_pmf_indep
    {View : Type*}
    (observe : (Fin viewCoordinates → K) → View)
    (maskMap : (Fin maskCoordinates → K) →ₗ[K]
      (Fin viewCoordinates → K))
    (hmaskMap : Function.Surjective maskMap)
    (witnessShift : W → (Fin viewCoordinates → K))
    (w₁ w₂ : W) :
    (PMF.uniformOfFintype (Fin maskCoordinates → K)).map
        (fun mask => observe (witnessShift w₁ + maskMap mask)) =
      (PMF.uniformOfFintype (Fin maskCoordinates → K)).map
        (fun mask => observe (witnessShift w₂ + maskMap mask)) := by
  have h := congrArg
    (fun distribution : PMF (Fin viewCoordinates → K) => distribution.map observe)
    (completeAffineView_pmf_indep maskMap hmaskMap witnessShift w₁ w₂)
  simpa only [PMF.map_comp, Function.comp_def] using h

/-- Factorised sufficient form of the ideal affine theorem.  None of its map
hypotheses is instantiated for components B or C in this file. -/
theorem completeAffineView_pmf_indep_of_three_blocks
    {MA MB MC VA VB VC : Type*}
    [AddCommMonoid MA] [Module K MA]
    [AddCommMonoid MB] [Module K MB]
    [AddCommMonoid MC] [Module K MC]
    [AddCommMonoid VA] [Module K VA]
    [AddCommMonoid VB] [Module K VB]
    [AddCommMonoid VC] [Module K VC]
    (split : (Fin maskCoordinates → K) →ₗ[K] (MA × (MB × MC)))
    (A : MA →ₗ[K] VA) (B : MB →ₗ[K] VB) (C : MC →ₗ[K] VC)
    (flatten : (VA × (VB × VC)) →ₗ[K]
      (Fin viewCoordinates → K))
    (hsplit : Function.Surjective split)
    (hA : Function.Surjective A) (hB : Function.Surjective B)
    (hC : Function.Surjective C)
    (hflatten : Function.Surjective flatten)
    (witnessShift : W → (Fin viewCoordinates → K))
    (w₁ w₂ : W) :
    (PMF.uniformOfFintype (Fin maskCoordinates → K)).map
        (fun mask => witnessShift w₁ +
          flatten (threeBlockMap A B C (split mask))) =
      (PMF.uniformOfFintype (Fin maskCoordinates → K)).map
        (fun mask => witnessShift w₂ +
          flatten (threeBlockMap A B C (split mask))) := by
  let completeMap : (Fin maskCoordinates → K) →ₗ[K]
      (Fin viewCoordinates → K) :=
    flatten.comp ((threeBlockMap A B C).comp split)
  apply completeAffineView_pmf_indep completeMap
    (composed_threeBlockMap_surjective split A B C flatten
      hsplit hA hB hC hflatten) witnessShift w₁ w₂

/-- The preceding conditional theorem followed by an arbitrary deterministic
observer.  A separate correspondence theorem would have to identify that
observer with an executable transcript. -/
theorem observedCompleteAffineView_pmf_indep_of_three_blocks
    {View MA MB MC VA VB VC : Type*}
    [AddCommMonoid MA] [Module K MA]
    [AddCommMonoid MB] [Module K MB]
    [AddCommMonoid MC] [Module K MC]
    [AddCommMonoid VA] [Module K VA]
    [AddCommMonoid VB] [Module K VB]
    [AddCommMonoid VC] [Module K VC]
    (split : (Fin maskCoordinates → K) →ₗ[K] (MA × (MB × MC)))
    (A : MA →ₗ[K] VA) (B : MB →ₗ[K] VB) (C : MC →ₗ[K] VC)
    (flatten : (VA × (VB × VC)) →ₗ[K]
      (Fin viewCoordinates → K))
    (observe : (Fin viewCoordinates → K) → View)
    (hsplit : Function.Surjective split)
    (hA : Function.Surjective A) (hB : Function.Surjective B)
    (hC : Function.Surjective C)
    (hflatten : Function.Surjective flatten)
    (witnessShift : W → (Fin viewCoordinates → K))
    (w₁ w₂ : W) :
    (PMF.uniformOfFintype (Fin maskCoordinates → K)).map
        (fun mask => observe (witnessShift w₁ +
          flatten (threeBlockMap A B C (split mask)))) =
      (PMF.uniformOfFintype (Fin maskCoordinates → K)).map
        (fun mask => observe (witnessShift w₂ +
          flatten (threeBlockMap A B C (split mask)))) := by
  have h := congrArg
    (fun distribution : PMF (Fin viewCoordinates → K) => distribution.map observe)
    (completeAffineView_pmf_indep_of_three_blocks split A B C flatten
      hsplit hA hB hC hflatten witnessShift w₁ w₂)
  simpa only [PMF.map_comp, Function.comp_def] using h

end CompleteAffineHiding

/-! ## Provisional Component A result -/

/-- The rank-72 theorem gives surjectivity of the abstract M31 72-by-96
layer-zero map.  The name of the imported matrix records its deployed field
constants, not a Rust/Lean correspondence theorem. -/
theorem deployedM31LayerZero_mulVec_surjective
    (queries : Fin AspisCircleDiscreteAvailability.queryCount →
      Fin AspisCircleDiscreteAvailability.fibreCount)
    (hqueries : Function.Injective queries)
    (weight : AspisCircleRectangularMasking.FibreIndex →
      AspisCircleRectangularMasking.DeployedField)
    (hweight : ∀ row, weight row ≠ 0) :
    Function.Surjective
      (AspisCircleRectangularMasking.deployedFibreRectangularEval
        queries weight).mulVec := by
  change Function.Surjective
    ⇑(AspisCircleRectangularMasking.deployedFibreRectangularEval
      queries weight).mulVecLin
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  change (AspisCircleRectangularMasking.deployedFibreRectangularEval
      queries weight).rank =
    Module.finrank AspisCircleRectangularMasking.DeployedField
      (AspisCircleRectangularMasking.FibreIndex →
        AspisCircleRectangularMasking.DeployedField)
  rw [AspisCircleRectangularMasking.deployedFibreRectangularEval_rank_eq_openedWidth
    queries hqueries weight hweight]
  rw [Module.finrank_pi]
  norm_num [AspisCircleRectangularMasking.FibreIndex,
    AspisCircleDiscreteAvailability.FibreSign,
    AspisCircleDiscreteAvailability.queryCount,
    AspisCircleRectangularMasking.openedWidth]

/-- Sixteen independent copies of the abstract Component-A map cover sixteen
ideal M31 lanes.  The new Rust `M31BlockMask` is not linked to this theorem:
sampler/domain separation, encoder entries, row and slot order, and executable
wire correspondence remain open. -/
theorem idealisedSixteenLaneM31LayerZero_surjective
    (queries : Fin AspisCircleDiscreteAvailability.queryCount →
      Fin AspisCircleDiscreteAvailability.fibreCount)
    (hqueries : Function.Injective queries)
    (weight : AspisCircleRectangularMasking.FibreIndex →
      AspisCircleRectangularMasking.DeployedField)
    (hweight : ∀ row, weight row ≠ 0) :
    Function.Surjective
      (laneFamilyMap componentAC1LaneCount
        (AspisCircleRectangularMasking.deployedFibreRectangularEval
          queries weight).mulVecLin) :=
  laneFamilyMap_surjective componentAC1LaneCount _
    (deployedM31LayerZero_mulVec_surjective queries hqueries weight hweight)

/-! ## Named protocol-boundary obligations -/

/-- Exact uniform product law assumed by an ideal finite-mask theorem.  A
finite-seed hash expander is not asserted to satisfy it. -/
def IdealUniformMaskLaw
    {Mask : Type*} [Fintype Mask] [Nonempty Mask]
    (idealMaskLaw : PMF Mask) : Prop :=
  idealMaskLaw = PMF.uniformOfFintype Mask

/-- Named real-to-ideal sampler boundary.  The supplied computational relation
must be instantiated by a concrete game and include retry-abort behaviour. -/
def RustMaskSamplerComputationalHybrid
    {Mask View : Type*}
    (realMaskLaw idealMaskLaw : PMF Mask)
    (observe : Mask → View)
    (ComputationallyIndistinguishable : PMF View → PMF View → Prop) : Prop :=
  ComputationallyIndistinguishable
    (realMaskLaw.map observe) (idealMaskLaw.map observe)

/-- Ideal uniqueness abstraction for openings of one pre-eta root.  Collision
resistance does not itself establish this set-theoretic proposition. -/
def IdealPreEtaOpeningUniqueness {Root Mask Challenge : Type*}
    (AdmissibleOpening : Root → Mask → Prop)
    (DerivesChallenge : Root → Challenge → Prop)
    (challengeFromRoot : Root → Challenge) : Prop :=
  (∀ root mask₁ mask₂,
      AdmissibleOpening root mask₁ → AdmissibleOpening root mask₂ → mask₁ = mask₂) ∧
    (∀ root challenge,
      DerivesChallenge root challenge ↔ challenge = challengeFromRoot root)

/-- Named computational binding boundary together with challenge dependence on
the committed root.  The binding game is a parameter, not a theorem here. -/
def ComputationalPreEtaCommitmentBinding {Root Mask Challenge : Type*}
    (AdmissibleOpening : Root → Mask → Prop)
    (DerivesChallenge : Root → Challenge → Prop)
    (challengeFromRoot : Root → Challenge)
    (ComputationallyBinding : (Root → Mask → Prop) → Prop) : Prop :=
  ComputationallyBinding AdmissibleOpening ∧
    (∀ root challenge,
      DerivesChallenge root challenge ↔ challenge = challengeFromRoot root)

/-- Missing adaptive Fiat--Shamir bridge.  The prefix is fixed before the
challenge; the second conjunct asks for equality with a supplied ideal law.
Neither equality is proved for v5 here. -/
def AdaptiveFiatShamirComposition
    {W Mask Prefix Challenge View : Type*}
    [Fintype Mask] [Nonempty Mask]
    (preEtaPrefix : W → Mask → Prefix)
    (deriveEta : Prefix → Challenge)
    (postEtaView : Prefix → Challenge → W → Mask → View)
    (protocolView idealAffineView : W → Mask → View) : Prop :=
  (∀ witness mask,
      protocolView witness mask =
        postEtaView (preEtaPrefix witness mask)
          (deriveEta (preEtaPrefix witness mask)) witness mask) ∧
    (∀ witness,
      (PMF.uniformOfFintype Mask).map (protocolView witness) =
        (PMF.uniformOfFintype Mask).map (idealAffineView witness))

/-- Component-B terminal authentication obligation: the accepted terminal mask
value must evaluate the same mask state bound before eta. -/
def AuthenticatedTerminalMaskEvaluation
    {Root Mask Point Value : Type*}
    (AdmissibleOpening : Root → Mask → Prop)
    (AuthenticatedEvaluation : Root → Point → Value → Prop)
    (evaluate : Mask → Point → Value) : Prop :=
  ∀ root mask point value,
    AdmissibleOpening root mask →
      AuthenticatedEvaluation root point value →
        value = evaluate mask point

/-- Component-C commitment-consistency obligation for every released mask
functional.  No concrete relation instantiates this predicate here. -/
def AuthenticatedReleasedMaskEvaluations
    {Root Mask Coordinate Value : Type*}
    (AdmissibleOpening : Root → Mask → Prop)
    (AuthenticatedEvaluation : Root → Coordinate → Value → Prop)
    (evaluate : Mask → Coordinate → Value) : Prop :=
  ∀ root mask coordinate value,
    AdmissibleOpening root mask →
      AuthenticatedEvaluation root coordinate value →
        value = evaluate mask coordinate

/-- Ideal affine coverage predicate for correlated released functionals.  Even
when true, it is not a commitment, opening or consistency theorem. -/
def CorrelatedPcsOodFoldJointRank
    {K : Type*} [Field K] {maskCoordinates legalCoordinates : ℕ}
    (jointMap : (Fin maskCoordinates → K) →ₗ[K]
      (Fin legalCoordinates → K)) : Prop :=
  Function.Surjective jointMap

/-- Exact executable-wire correspondence.  This is only a named proposition;
no v5 serialiser or decoder instantiates it in this file. -/
def RustLeanWireCorrespondence
    {W Mask Bytes View : Type*}
    (rustSerialise : W → Mask → Bytes)
    (decode : Bytes → Option View)
    (leanView : W → Mask → View) : Prop :=
  ∀ witness mask,
    decode (rustSerialise witness mask) = some (leanView witness mask)

/-- Encoder correspondence below the byte layer.  A non-permutation basis
conversion belongs in the entry map or in another explicit linear map; it
cannot be represented by a column permutation alone. -/
def RustEncoderIndexSlotBasisCorrespondence
    {Query Slot Lane Coefficient Row Column Value : Type*}
    (rustRow leanRow : Query → Slot → Row)
    (rustColumn leanColumn : Lane → Coefficient → Column)
    (rustEntry leanEntry : Row → Column → Value) : Prop :=
  (∀ query slot, rustRow query slot = leanRow query slot) ∧
    (∀ lane coefficient, rustColumn lane coefficient = leanColumn lane coefficient) ∧
    (∀ query slot lane coefficient,
      rustEntry (rustRow query slot) (rustColumn lane coefficient) =
        leanEntry (leanRow query slot) (leanColumn lane coefficient))

/-!
`SumcheckMasking.maskedRoundFamily_pmf_indep` proves only the externally
labelled Component-B algebraic hybrid.  The endpoint-collision theorems in that
file show why Boolean boundary data alone do not authenticate a non-Boolean
degree-27 evaluation.  No concrete B commitment discharges
`ComputationalPreEtaCommitmentBinding` or
`AuthenticatedTerminalMaskEvaluation`.

Component C has no construction in this file, and in particular no
instantiation of `AuthenticatedReleasedMaskEvaluations`.  The provisional
Component-A theorem closes only its abstract layer-zero map.  Consequently
there is no complete v5 hiding theorem, production field inventory or
serialisation-completeness claim here.
-/

end AspisV5CompleteView

#print axioms AspisV5CompleteView.algebraicB_dimensions
#print axioms AspisV5CompleteView.threeBlockMap_surjective
#print axioms AspisV5CompleteView.composed_threeBlockMap_surjective
#print axioms AspisV5CompleteView.completeAffineView_pmf_indep_of_three_blocks
#print axioms AspisV5CompleteView.observedCompleteAffineView_pmf_indep_of_three_blocks
#print axioms AspisV5CompleteView.deployedM31LayerZero_mulVec_surjective
#print axioms AspisV5CompleteView.idealisedSixteenLaneM31LayerZero_surjective
#print axioms AspisV5CompleteView.IdealUniformMaskLaw
#print axioms AspisV5CompleteView.RustMaskSamplerComputationalHybrid
#print axioms AspisV5CompleteView.ComputationalPreEtaCommitmentBinding
#print axioms AspisV5CompleteView.AdaptiveFiatShamirComposition
#print axioms AspisV5CompleteView.AuthenticatedTerminalMaskEvaluation
#print axioms AspisV5CompleteView.AuthenticatedReleasedMaskEvaluations
#print axioms AspisV5CompleteView.RustEncoderIndexSlotBasisCorrespondence
