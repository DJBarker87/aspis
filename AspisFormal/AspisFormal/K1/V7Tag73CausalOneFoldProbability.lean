import AspisFormal.K1.V7Tag73CompleteCausalOrdinaryProbability
import AspisFormal.K1.V7Tag73ExactOneFoldRestorationStrategy

/-!
# Causal one-fold probability for adaptive post-alpha responses

The prover discloses `final256` after alpha, so a sound K1.3 argument cannot
freeze the accepted terminal vector before sampling alpha.  This file models
one restoration-wide response strategy whose candidate and support may both
depend on alpha.  The authenticated initial word and decoded coefficient
lanes remain fixed before alpha.

The published degree-three theorem is applied once to that complete strategy.
If too many alpha values are genuine one-fold failures, its root-union output
reconstructs a supported predecessor for one selected failing alpha, a direct
contradiction.  Thus adaptivity of `final256` creates no extra list factor.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CausalOneFoldProbability

open MeasureTheory
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73ExactOneFoldRestorationStrategy
open AspisV5ComponentCQM31TowerExact
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriCompatibleCandidateChain
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV6OneFoldCandidateExtraction
open AspisV6PublishedTheoremInterfaces

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

noncomputable section

/-- The transcript at one restored alpha.  Only the disclosed terminal is
response-dependent; the authenticated initial word is fixed. -/
def causalOneFoldTranscriptAt
    (base : IdealTranscript K)
    (strategy : ProximateStrategy K (Fin 262144) (FinalCoefficients K))
    (alpha : K) : IdealTranscript K where
  initial := base.initial
  disclosedFinal := strategy.candidate alpha

/-- A genuine adaptive one-fold failure: the response is dense and consistent,
but no supported initial predecessor folds to that alpha-specific terminal. -/
def CausalOneFoldBadResponse
    [Fintype K] [DecidableEq K]
    (schedule : OneFoldSchedule F K) (encoders : CodeEncoders K)
    (binding : OneFoldAlgebraBinding schedule encoders)
    (base : IdealTranscript K)
    (strategy : ProximateStrategy K (Fin 262144) (FinalCoefficients K))
    (alpha : K) : Prop :=
  ValidResponse binding.finalLinear outputAgreementThreshold
      (oneFoldDecodedLanes schedule base) strategy alpha ∧
    ¬ ∃ candidate : InitialCoefficients K,
      SupportedNearInitial (scheduleAtAlpha schedule alpha) encoders
          (causalOneFoldTranscriptAt base strategy alpha) candidate ∧
        foldInitial (scheduleAtAlpha schedule alpha) candidate =
          strategy.candidate alpha

/-- Mask all non-failing responses while retaining the alpha-dependent
candidate of the complete restored strategy. -/
noncomputable def causalOneFoldBadMaskedStrategy
    [Fintype K] [DecidableEq K]
    (schedule : OneFoldSchedule F K) (encoders : CodeEncoders K)
    (binding : OneFoldAlgebraBinding schedule encoders)
    (base : IdealTranscript K)
    (strategy : ProximateStrategy K (Fin 262144) (FinalCoefficients K)) :
    ProximateStrategy K (Fin 262144) (FinalCoefficients K) := by
  classical
  exact {
    candidate := strategy.candidate
    support := fun alpha =>
      if CausalOneFoldBadResponse schedule encoders binding base strategy alpha
      then strategy.support alpha else ∅
  }

theorem valid_causalOneFoldBadMaskedStrategy_iff
    [Fintype K] [DecidableEq K]
    (schedule : OneFoldSchedule F K) (encoders : CodeEncoders K)
    (binding : OneFoldAlgebraBinding schedule encoders)
    (base : IdealTranscript K)
    (strategy : ProximateStrategy K (Fin 262144) (FinalCoefficients K))
    (alpha : K) :
    ValidResponse binding.finalLinear outputAgreementThreshold
        (oneFoldDecodedLanes schedule base)
        (causalOneFoldBadMaskedStrategy schedule encoders binding base strategy)
        alpha ↔
      CausalOneFoldBadResponse schedule encoders binding base strategy alpha := by
  classical
  by_cases bad :
      CausalOneFoldBadResponse schedule encoders binding base strategy alpha
  · constructor
    · intro _
      exact bad
    · intro _
      rcases bad.1 with ⟨dense, agrees⟩
      constructor
      · simpa [causalOneFoldBadMaskedStrategy, bad] using dense
      · intro index member
        have originalMember : index ∈ strategy.support alpha := by
          simpa [causalOneFoldBadMaskedStrategy, bad] using member
        have exactAgreement := agrees index originalMember
        simpa [causalOneFoldBadMaskedStrategy] using exactAgreement
  · have supportEq :
        (causalOneFoldBadMaskedStrategy schedule encoders binding base strategy
          |>.support alpha) = ∅ := by
      simp [causalOneFoldBadMaskedStrategy, bad]
    constructor
    · intro valid
      have impossible : outputAgreementThreshold < 0 := by
        simpa only [supportEq, Finset.card_empty] using valid.1
      exact (Nat.not_lt_zero _ impossible).elim
    · exact fun impossible => (bad impossible).elim

/-- Fixed pre-alpha target of all genuine adaptive one-fold failures. -/
noncomputable def causalOneFoldFailureTarget
    [Fintype K] [DecidableEq K]
    (schedule : OneFoldSchedule F K) (encoders : CodeEncoders K)
    (binding : OneFoldAlgebraBinding schedule encoders)
    (base : IdealTranscript K)
    (strategy : ProximateStrategy K (Fin 262144) (FinalCoefficients K)) :
    Finset K :=
  goodChallenges binding.finalLinear outputAgreementThreshold
    (oneFoldDecodedLanes schedule base)
    (causalOneFoldBadMaskedStrategy schedule encoders binding base strategy)

@[simp] theorem mem_causalOneFoldFailureTarget_iff
    [Fintype K] [DecidableEq K]
    (schedule : OneFoldSchedule F K) (encoders : CodeEncoders K)
    (binding : OneFoldAlgebraBinding schedule encoders)
    (base : IdealTranscript K)
    (strategy : ProximateStrategy K (Fin 262144) (FinalCoefficients K))
    (alpha : K) :
    alpha ∈ causalOneFoldFailureTarget schedule encoders binding base strategy ↔
      CausalOneFoldBadResponse schedule encoders binding base strategy alpha := by
  rw [causalOneFoldFailureTarget, mem_goodChallenges_iff]
  exact valid_causalOneFoldBadMaskedStrategy_iff schedule encoders binding
    base strategy alpha

/-- The published degree-three result bounds the complete adaptive response
family with the same single `foldChallengeCap`. -/
theorem causalOneFoldFailureTarget_card_le
    [Fintype K] [DecidableEq K]
    (schedule : OneFoldSchedule F K) (encoders : CodeEncoders K)
    (binding : OneFoldAlgebraBinding schedule encoders)
    (base : IdealTranscript K)
    (strategy : ProximateStrategy K (Fin 262144) (FinalCoefficients K))
    (published : PublishedOneFoldCurveDecodability binding.finalLinear) :
    (causalOneFoldFailureTarget schedule encoders binding base strategy).card ≤
      foldChallengeCap := by
  classical
  by_contra notBounded
  have many : foldChallengeCap <
      (causalOneFoldFailureTarget schedule encoders binding base strategy).card :=
    Nat.lt_of_not_ge notBounded
  let lanes := oneFoldDecodedLanes schedule base
  let masked := causalOneFoldBadMaskedStrategy schedule encoders binding base
    strategy
  obtain ⟨components, selected, selectedGood, selectedLarge, onCurve⟩ :=
    published lanes masked many
  obtain ⟨alpha, alphaSelected, notResolving⟩ :=
    exists_selected_not_resolving binding.finalLinear lanes components
      selected selectedLarge
  have alphaBadMember : alpha ∈
      causalOneFoldFailureTarget schedule encoders binding base strategy :=
    selectedGood alphaSelected
  have alphaBad :
      CausalOneFoldBadResponse schedule encoders binding base strategy alpha :=
    (mem_causalOneFoldFailureTarget_iff schedule encoders binding base strategy
      alpha).mp alphaBadMember
  have maskedValid : ValidResponse binding.finalLinear outputAgreementThreshold
      lanes masked alpha :=
    (mem_goodChallenges_iff binding.finalLinear outputAgreementThreshold lanes
      masked alpha).mp alphaBadMember
  have maskedSubset : masked.support alpha ⊆
      jointAgreementSet binding.finalLinear lanes components :=
    support_subset_jointAgreement binding.finalLinear outputAgreementThreshold
      lanes masked components alpha maskedValid (onCurve alpha alphaSelected)
      notResolving
  have supportEq : masked.support alpha = strategy.support alpha := by
    dsimp [masked]
    simp [causalOneFoldBadMaskedStrategy, alphaBad]
  have strategySubset : strategy.support alpha ⊆
      jointAgreementSet binding.finalLinear lanes components := by
    rw [← supportEq]
    exact maskedSubset
  let candidate : InitialCoefficients K :=
    assembleCoefficientLanes components
  have reconstruct : ∀ index ∈ strategy.support alpha, ∀ slot : Fin 4,
      encoders.initial candidate (childIndex index slot) =
        base.initial (childIndex index slot) := by
    intro index indexMember slot
    exact initial_assembled_eq_received_on_joint schedule encoders binding base
      components index (strategySubset indexMember) slot
  have consistent : ∀ index ∈ strategy.support alpha,
      QueryConsistent (scheduleAtAlpha schedule alpha) encoders
        (causalOneFoldTranscriptAt base strategy alpha) index := by
    intro index indexMember
    have response := alphaBad.1.2 index indexMember
    rw [curve_oneFoldDecodedLanes_eq_circleFold schedule encoders binding base
      alpha index] at response
    change circleFoldLayer 262144 alpha schedule.circleInv2x
        schedule.circleInv2y base.initial index =
      encoders.final (strategy.candidate alpha) index
    rw [binding.finalEncoderEq]
    exact response
  have supportedCard : (strategy.support alpha).card * 4 ≤
      (supportedAgreementInitial (scheduleAtAlpha schedule alpha) encoders
        (causalOneFoldTranscriptAt base strategy alpha) candidate).card :=
    four_response_fibres_card_le_supportedAgreement
      (scheduleAtAlpha schedule alpha) encoders
      (causalOneFoldTranscriptAt base strategy alpha) candidate
      (strategy.support alpha) consistent reconstruct
  have supportLarge : 9557 < (strategy.support alpha).card := alphaBad.1.1
  have candidateSupported : SupportedNearInitial
      (scheduleAtAlpha schedule alpha) encoders
      (causalOneFoldTranscriptAt base strategy alpha) candidate := by
    unfold SupportedNearInitial
    have enough : 38230 ≤ (strategy.support alpha).card * 4 := by omega
    exact enough.trans supportedCard
  have candidateFold : foldInitial (scheduleAtAlpha schedule alpha) candidate =
      strategy.candidate alpha := by
    have foldEq := fold_assembled_eq_candidate_of_onCurve
      binding.finalLinear binding.finalInjective masked components alpha
      (onCurve alpha alphaSelected)
    change coefficientFoldLayer 256 alpha
        (assembleCoefficientLanes components) = strategy.candidate alpha
    simpa [masked, causalOneFoldBadMaskedStrategy] using foldEq
  exact alphaBad.2 ⟨candidate, candidateSupported, candidateFold⟩

/-- Pointwise membership used by the source/restoration adapter. -/
theorem causal_oneFold_bad_response_mem_target
    [Fintype K] [DecidableEq K]
    (schedule : OneFoldSchedule F K) (encoders : CodeEncoders K)
    (binding : OneFoldAlgebraBinding schedule encoders)
    (base : IdealTranscript K)
    (strategy : ProximateStrategy K (Fin 262144) (FinalCoefficients K))
    (alpha : K)
    (failure : CausalOneFoldBadResponse schedule encoders binding base strategy
      alpha) :
    alpha ∈ causalOneFoldFailureTarget schedule encoders binding base
      strategy :=
  (mem_causalOneFoldFailureTarget_iff schedule encoders binding base strategy
    alpha).mpr failure

/-- One complete pre-value causal context for alpha.  It may depend on every
ordinary-sampler rejection position and duplex-advance answer, while its
response strategy ranges over all returned alpha values. -/
structure CausalOneFoldSamplerContext (F : Type*) [Field F]
    [Algebra F QM31Exact] where
  schedule : OneFoldSchedule F QM31Exact
  encoders : CodeEncoders QM31Exact
  binding : OneFoldAlgebraBinding schedule encoders
  base : IdealTranscript QM31Exact
  strategy : ProximateStrategy QM31Exact (Fin 262144)
    (FinalCoefficients QM31Exact)
  published : PublishedOneFoldCurveDecodability binding.finalLinear

noncomputable def causalOneFoldSamplerTarget
    {F : Type*} [Field F] [Algebra F QM31Exact]
    (context : Tag73CompleteOrdinarySamplerSkeleton →
      CausalOneFoldSamplerContext F)
    (skeleton : Tag73CompleteOrdinarySamplerSkeleton) : Finset QM31Exact :=
  let current := context skeleton
  causalOneFoldFailureTarget current.schedule current.encoders current.binding
    current.base current.strategy

theorem causalOneFoldSamplerTarget_card_le
    {F : Type*} [Field F] [Algebra F QM31Exact]
    (context : Tag73CompleteOrdinarySamplerSkeleton →
      CausalOneFoldSamplerContext F)
    (skeleton : Tag73CompleteOrdinarySamplerSkeleton) :
    (causalOneFoldSamplerTarget context skeleton).card ≤ foldChallengeCap := by
  let current := context skeleton
  exact causalOneFoldFailureTarget_card_le current.schedule current.encoders
    current.binding current.base current.strategy current.published

/-- Exact raw K1.3 one-fold probability for the full causal alpha response.
No work normalization and no frozen-post-alpha transcript assumption is used. -/
theorem causal_oneFold_duplex_alpha_probability_le
    {F : Type*} [Field F] [Algebra F QM31Exact]
    (context : Tag73CompleteOrdinarySamplerSkeleton →
      CausalOneFoldSamplerContext F) :
    (PMF.uniformOfFintype SuccessfulTag73DuplexOrdinaryAttempt).toOuterMeasure
        (duplexOrdinaryDependentEvent
          (causalOneFoldSamplerTarget context)) ≤
      (foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  exact duplex_ordinary_dependent_probability_le
    (causalOneFoldSamplerTarget context) foldChallengeCap
    (causalOneFoldSamplerTarget_card_le context)

end

#print axioms valid_causalOneFoldBadMaskedStrategy_iff
#print axioms causalOneFoldFailureTarget_card_le
#print axioms causal_oneFold_bad_response_mem_target
#print axioms causalOneFoldSamplerTarget_card_le
#print axioms causal_oneFold_duplex_alpha_probability_le

end AspisK1.V7Tag73CausalOneFoldProbability
