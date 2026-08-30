import AspisFormal.K1.V7Tag73CausalK14FailureProbability
import AspisFormal.K1.V7Tag73SuccessfulSamplerConditioningCore

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
set_option maxRecDepth 10000

namespace AspisK1.V7Tag73SuccessfulSamplerConditioningBridge

open MeasureTheory
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73CausalK14FailureProbability
open AspisK1.V7Tag73RawNonzeroSamplerFactorization

noncomputable section

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
    (initialEncoderExact : decoder.initialEncoder =
      AspisPool.V7C1ConcreteProjectionBinding.exactInitialEncoder)
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
    _ ≤ _ := causal_k14_failure_duplex_gamma_probability_le
      initialEncoderExact provider

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
    (initialEncoderExact : decoder.initialEncoder =
      AspisPool.V7C1ConcreteProjectionBinding.exactInitialEncoder)
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
    successfulCoordinates initialEncoderExact (provider hidden)
    (jointEventSlice event hidden) (covered hidden)

/-- The actual causal context may depend on every fresh answer outside gamma's
fixed raw region.  Once a source-level coordinate equivalence separates that
residual context from the total raw gamma sample, every residual slice is
bounded by the same degree-28 theorem and averaging introduces no loss. -/
theorem uniform_tape_dependent_k14_event_probability_le
    {Tape Total Residual : Type}
    [Fintype Tape] [Nonempty Tape]
    [Fintype Total] [Nonempty Total]
    [Fintype Residual] [Nonempty Residual]
    (success : Total → Prop) [DecidablePred success]
    [Nonempty {a : Total // success a}]
    (coordinates : Tape ≃ Residual × Total)
    (successfulCoordinates :
      {a : Total // success a} ≃ SuccessfulTag73DuplexNonzeroAttempts)
    {decoder : AspisPool.AlgorithmicCircleDecoderV7.ExactDecoderInstantiation
      AspisV5ComponentCQM31TowerExact.QM31Exact}
    (initialEncoderExact : decoder.initialEncoder =
      AspisPool.V7C1ConcreteProjectionBinding.exactInitialEncoder)
    (words : Residual → AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (provider : ∀ residual,
      AspisK1.V7Tag73RawNonzeroSamplerFactorization.Tag73CompleteSamplerSkeleton →
        AspisK1.V7Tag73CausalRestoredFamily.RestoredSelectedBranchProvider
          decoder (words residual))
    (event : Set Tape)
    (covered : event ⊆ coordinates ⁻¹'
      dependentSuccessfulSubtypeEvent success (fun residual =>
        successfulCoordinates ⁻¹'
          causalK14FailureDuplexGammaEvent (provider residual))) :
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
      (AspisV6PublishedTheoremInterfaces.initialBatchChallengeCap : ENNReal) /
        ((AspisV5ComponentCQM31TowerExact.P ^ 4 - 1 : Nat) : ENNReal) := by
  let successfulEvent : Residual → Set {a : Total // success a} :=
    fun residual => successfulCoordinates ⁻¹'
      causalK14FailureDuplexGammaEvent (provider residual)
  let dependentEvent : Set (Residual × Total) :=
    dependentSuccessfulSubtypeEvent success successfulEvent
  calc
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
        (PMF.uniformOfFintype Tape).toOuterMeasure
          (coordinates ⁻¹' dependentEvent) :=
      (PMF.uniformOfFintype Tape).toOuterMeasure.mono covered
    _ = (PMF.uniformOfFintype (Residual × Total)).toOuterMeasure
          dependentEvent := by
      calc
        _ = ((PMF.uniformOfFintype Tape).map coordinates).toOuterMeasure
              dependentEvent := by rw [PMF.toOuterMeasure_map_apply]
        _ = _ := by
          rw [AspisV5RankOneOpeningHiding.uniform_map_equiv coordinates]
    _ ≤ _ := by
      apply uniform_product_event_probability_le_of_every_slice_le
      intro residual
      calc
        (PMF.uniformOfFintype Total).toOuterMeasure
            (productEventFstSlice dependentEvent residual) =
          (PMF.uniformOfFintype Total).toOuterMeasure
            (successfulSubtypeEvent success (successfulEvent residual)) := by
              rw [show dependentEvent =
                dependentSuccessfulSubtypeEvent success successfulEvent by rfl,
                productEventFstSlice_dependentSuccessfulSubtypeEvent]
        _ ≤ (PMF.uniformOfFintype {a : Total // success a}).toOuterMeasure
              (successfulEvent residual) :=
          uniform_successful_subtype_event_probability_le success
            (successfulEvent residual)
        _ = (PMF.uniformOfFintype
              SuccessfulTag73DuplexNonzeroAttempts).toOuterMeasure
                (causalK14FailureDuplexGammaEvent (provider residual)) := by
          calc
            _ = ((PMF.uniformOfFintype {a : Total // success a}).map
                  successfulCoordinates).toOuterMeasure
                    (causalK14FailureDuplexGammaEvent
                      (provider residual)) := by
                rw [PMF.toOuterMeasure_map_apply]
            _ = _ := by
              rw [AspisV5RankOneOpeningHiding.uniform_map_equiv
                successfulCoordinates]
        _ ≤ _ := causal_k14_failure_duplex_gamma_probability_le
          initialEncoderExact (provider residual)

/-- Hidden-tape averaging of the residual-dependent source bridge. -/
theorem exact_compiler_dependent_k14_event_probability_le
    {HiddenTape Total Residual : Type} [Fintype HiddenTape]
    [Fintype Total] [Nonempty Total]
    [Fintype Residual] [Nonempty Residual]
    (hiddenLaw : PMF HiddenTape) (freshExposures : Nat)
    (success : Total → Prop) [DecidablePred success]
    [Nonempty {a : Total // success a}]
    (coordinates : HiddenTape →
      AspisK1.V7Tag73AdaptiveLazyOracle.FreshAnswerTape
        AspisK1.V7Tag73TranscriptSchedule.Digest256 freshExposures ≃
          Residual × Total)
    (successfulCoordinates :
      {a : Total // success a} ≃ SuccessfulTag73DuplexNonzeroAttempts)
    {decoder : AspisPool.AlgorithmicCircleDecoderV7.ExactDecoderInstantiation
      AspisV5ComponentCQM31TowerExact.QM31Exact}
    (initialEncoderExact : decoder.initialEncoder =
      AspisPool.V7C1ConcreteProjectionBinding.exactInitialEncoder)
    (words : HiddenTape → Residual →
      AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (provider : ∀ hidden residual,
      AspisK1.V7Tag73RawNonzeroSamplerFactorization.Tag73CompleteSamplerSkeleton →
        AspisK1.V7Tag73CausalRestoredFamily.RestoredSelectedBranchProvider
          decoder (words hidden residual))
    (event : Set (HiddenTape ×
      AspisK1.V7Tag73AdaptiveLazyOracle.FreshAnswerTape
        AspisK1.V7Tag73TranscriptSchedule.Digest256 freshExposures))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      coordinates hidden ⁻¹'
        dependentSuccessfulSubtypeEvent success (fun residual =>
          successfulCoordinates ⁻¹'
            causalK14FailureDuplexGammaEvent (provider hidden residual))) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw freshExposures).toOuterMeasure
        event ≤
      (AspisV6PublishedTheoremInterfaces.initialBatchChallengeCap : ENNReal) /
        ((AspisV5ComponentCQM31TowerExact.P ^ 4 - 1 : Nat) : ENNReal) := by
  apply joint_event_probability_le_of_every_slice_le
  intro hidden
  exact uniform_tape_dependent_k14_event_probability_le success
    (coordinates hidden) successfulCoordinates initialEncoderExact (words hidden)
    (provider hidden) (jointEventSlice event hidden) (covered hidden)

end

#print axioms uniform_tape_k14_event_probability_le
#print axioms exact_compiler_k14_event_probability_le
#print axioms uniform_tape_dependent_k14_event_probability_le
#print axioms exact_compiler_dependent_k14_event_probability_le

end AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
