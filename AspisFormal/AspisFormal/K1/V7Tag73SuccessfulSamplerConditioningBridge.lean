import AspisFormal.K1.V7Tag73CausalK14FailureProbability
import AspisFormal.K1.V7Tag73HiddenTapeAveraging

/-!
# Uniform-tape conditioning bridge for the Tag-73 gamma sampler

The deployed gamma sampler occupies a fixed finite region of the compiler's
fresh SHA-answer tape.  An accepting execution necessarily lies in the
successful-sampler subtype.  This file supplies the generic finite-measure
glue needed by the source bridge: an unconditioned uniform experiment cannot
assign more mass to a successful bad event than the corresponding experiment
conditioned on sampler success.

The theorem below is deliberately independent of Tag-73 parsing.  The source
bridge must still provide the exact coordinate equivalence and prove that a
literal K1.4 error maps into the causal gamma event.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SuccessfulSamplerConditioningBridge

open MeasureTheory
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73CausalK14FailureProbability
open AspisK1.V7Tag73RawNonzeroSamplerFactorization

noncomputable section

/-- Restrict an event on a successful subtype back to the total sampler
space. -/
def successfulSubtypeEvent
    {A : Type} (success : A → Prop)
    (event : Set {a : A // success a}) : Set A :=
  {a | ∃ h : success a, (⟨a, h⟩ : {a : A // success a}) ∈ event}

def successfulSubtypeEventEquiv
    {A : Type} (success : A → Prop)
    (event : Set {a : A // success a}) :
    {a : A // a ∈ successfulSubtypeEvent success event} ≃
      {a : {a : A // success a} // a ∈ event} where
  toFun a := ⟨⟨a.1, Classical.choose a.2⟩, Classical.choose_spec a.2⟩
  invFun a := ⟨a.1.1, ⟨a.1.2, a.2⟩⟩
  left_inv a := by ext; rfl
  right_inv a := by ext; rfl

/-- Conditioning a finite uniform sampler on a nonempty successful subset can
only increase the probability of an event contained in that subset. -/
theorem uniform_successful_subtype_event_probability_le
    {A : Type} [Fintype A] [Nonempty A]
    (success : A → Prop) [DecidablePred success]
    [Nonempty {a : A // success a}]
    (event : Set {a : A // success a}) :
    (PMF.uniformOfFintype A).toOuterMeasure
        (successfulSubtypeEvent success event) ≤
      (PMF.uniformOfFintype {a : A // success a}).toOuterMeasure event := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply,
    PMF.toOuterMeasure_uniformOfFintype_apply]
  rw [Fintype.card_congr (successfulSubtypeEventEquiv success event)]
  gcongr
  exact Fintype.card_subtype_le success

/-- A fixed coordinate equivalence can expose the total sampler region and an
independent residual tape.  Any event covered by a successful sampler event
inherits the latter's conditional probability bound. -/
theorem uniform_tape_event_probability_le_successful_sampler_event
    {Tape Total Residual : Type}
    [Fintype Tape] [Nonempty Tape]
    [Fintype Total] [Nonempty Total]
    [Fintype Residual] [Nonempty Residual]
    (success : Total → Prop) [DecidablePred success]
    [Nonempty {a : Total // success a}]
    (coordinates : Tape ≃ Total × Residual)
    (event : Set Tape)
    (successfulEvent : Set {a : Total // success a})
    (covered : event ⊆ coordinates ⁻¹'
      (Prod.fst ⁻¹' successfulSubtypeEvent success successfulEvent)) :
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
      (PMF.uniformOfFintype {a : Total // success a}).toOuterMeasure
        successfulEvent := by
  classical
  calc
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
        (PMF.uniformOfFintype Tape).toOuterMeasure
          (coordinates ⁻¹'
            (Prod.fst ⁻¹' successfulSubtypeEvent success successfulEvent)) :=
      (PMF.uniformOfFintype Tape).toOuterMeasure.mono covered
    _ = ((PMF.uniformOfFintype Tape).map coordinates).toOuterMeasure
          (Prod.fst ⁻¹' successfulSubtypeEvent success successfulEvent) := by
      rw [PMF.toOuterMeasure_map_apply]
    _ = (PMF.uniformOfFintype (Total × Residual)).toOuterMeasure
          (Prod.fst ⁻¹' successfulSubtypeEvent success successfulEvent) := by
      rw [AspisV5RankOneOpeningHiding.uniform_map_equiv coordinates]
    _ = ((PMF.uniformOfFintype (Total × Residual)).map Prod.fst).toOuterMeasure
          (successfulSubtypeEvent success successfulEvent) := by
      rw [PMF.toOuterMeasure_map_apply]
    _ = (PMF.uniformOfFintype Total).toOuterMeasure
          (successfulSubtypeEvent success successfulEvent) := by
      rw [AspisV5ComponentCRejectionSampler.uniform_prod_map_fst]
    _ ≤ (PMF.uniformOfFintype {a : Total // success a}).toOuterMeasure
          successfulEvent :=
      uniform_successful_subtype_event_probability_le success successfulEvent

/-- Specialize the generic conditioning bridge to the complete Tag-73 gamma
sampler and transport the successful subtype through an exact source-provided
equivalence.  This theorem has no probability or independence premise. -/
theorem uniform_tape_k14_event_probability_le
    {Tape Total Residual : Type}
    [Fintype Tape] [Nonempty Tape]
    [Fintype Total] [Nonempty Total]
    [Fintype Residual] [Nonempty Residual]
    (success : Total → Prop) [DecidablePred success]
    [Nonempty {a : Total // success a}]
    (coordinates : Tape ≃ Total × Residual)
    (successfulCoordinates :
      {a : Total // success a} ≃ SuccessfulTag73DuplexNonzeroAttempts)
    {decoder : AspisPool.AlgorithmicCircleDecoderV7.ExactDecoderInstantiation
      AspisV5ComponentCQM31TowerExact.QM31Exact}
    (published :
      AspisV6PublishedTheoremInterfaces.PublishedInitialWidth29CurveDecodability
        decoder.initialEncoder)
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : AspisK1.V7Tag73RawNonzeroSamplerFactorization.Tag73CompleteSamplerSkeleton →
      AspisK1.V7Tag73CausalRestoredFamily.RestoredSelectedBranchProvider
        decoder words)
    (event : Set Tape)
    (covered : event ⊆ coordinates ⁻¹'
      (Prod.fst ⁻¹' successfulSubtypeEvent success
        (successfulCoordinates ⁻¹'
          causalK14FailureDuplexGammaEvent provider))) :
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
      (AspisV6PublishedTheoremInterfaces.initialBatchChallengeCap : ENNReal) /
        ((AspisV5ComponentCQM31TowerExact.P ^ 4 - 1 : Nat) : ENNReal) := by
  calc
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
        (PMF.uniformOfFintype {a : Total // success a}).toOuterMeasure
          (successfulCoordinates ⁻¹'
            causalK14FailureDuplexGammaEvent provider) :=
      uniform_tape_event_probability_le_successful_sampler_event success
        coordinates event _ covered
    _ = (PMF.uniformOfFintype
          SuccessfulTag73DuplexNonzeroAttempts).toOuterMeasure
            (causalK14FailureDuplexGammaEvent provider) := by
      calc
        _ = ((PMF.uniformOfFintype {a : Total // success a}).map
              successfulCoordinates).toOuterMeasure
                (causalK14FailureDuplexGammaEvent provider) := by
            rw [PMF.toOuterMeasure_map_apply]
        _ = _ := by
          rw [AspisV5RankOneOpeningHiding.uniform_map_equiv
            successfulCoordinates]
    _ ≤ _ := causal_k14_failure_duplex_gamma_probability_le published provider

/-- Average the source-provided fixed-hidden coordinate/inclusion bridges over
the exact compiler's arbitrary hidden-tape law. -/
theorem exact_compiler_k14_event_probability_le
    {HiddenTape Total Residual : Type} [Fintype HiddenTape]
    [Fintype Total] [Nonempty Total]
    [Fintype Residual] [Nonempty Residual]
    (hiddenLaw : PMF HiddenTape) (freshExposures : Nat)
    (success : Total → Prop) [DecidablePred success]
    [Nonempty {a : Total // success a}]
    (coordinates : HiddenTape →
      AspisK1.V7Tag73AdaptiveLazyOracle.FreshAnswerTape
        AspisK1.V7Tag73TranscriptSchedule.Digest256 freshExposures ≃
        Total × Residual)
    (successfulCoordinates :
      {a : Total // success a} ≃ SuccessfulTag73DuplexNonzeroAttempts)
    {decoder : AspisPool.AlgorithmicCircleDecoderV7.ExactDecoderInstantiation
      AspisV5ComponentCQM31TowerExact.QM31Exact}
    (published :
      AspisV6PublishedTheoremInterfaces.PublishedInitialWidth29CurveDecodability
        decoder.initialEncoder)
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : HiddenTape →
      AspisK1.V7Tag73RawNonzeroSamplerFactorization.Tag73CompleteSamplerSkeleton →
        AspisK1.V7Tag73CausalRestoredFamily.RestoredSelectedBranchProvider
          decoder words)
    (event : Set (HiddenTape ×
      AspisK1.V7Tag73AdaptiveLazyOracle.FreshAnswerTape
        AspisK1.V7Tag73TranscriptSchedule.Digest256 freshExposures))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      coordinates hidden ⁻¹'
        (Prod.fst ⁻¹' successfulSubtypeEvent success
          (successfulCoordinates ⁻¹'
            causalK14FailureDuplexGammaEvent (provider hidden)))) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw freshExposures).toOuterMeasure
        event ≤
      (AspisV6PublishedTheoremInterfaces.initialBatchChallengeCap : ENNReal) /
        ((AspisV5ComponentCQM31TowerExact.P ^ 4 - 1 : Nat) : ENNReal) := by
  apply joint_event_probability_le_of_every_slice_le
  intro hidden
  exact uniform_tape_k14_event_probability_le success (coordinates hidden)
    successfulCoordinates published (provider hidden)
    (jointEventSlice event hidden) (covered hidden)

end

#print axioms uniform_successful_subtype_event_probability_le
#print axioms uniform_tape_event_probability_le_successful_sampler_event
#print axioms uniform_tape_k14_event_probability_le
#print axioms exact_compiler_k14_event_probability_le

end AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
