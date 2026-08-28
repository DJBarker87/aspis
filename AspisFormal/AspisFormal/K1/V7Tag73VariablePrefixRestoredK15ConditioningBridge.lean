import AspisFormal.K1.V7Tag73VariablePrefixGammaFlatProbability
import AspisFormal.K1.V7Tag73HiddenTapeAveraging

/-!
# Exact compiler conditioning for the variable-prefix Tag-73 gamma sampler

The production outer sampler stops at the first successful nonzero ordinary
decode.  This bridge therefore uses the literal twelve-output/twelve-advance
total tape and `GammaPrefixSucceeds`; it does not require any unread suffix
attempt to decode successfully.

All probability and root-counting work is discharged here.  A source use must
still expose this exact total tape as finite coordinates of the compiler's
fresh-answer tape and prove the deterministic inclusion of the concrete
residual event.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73VariablePrefixRestoredK15ConditioningBridge

open MeasureTheory
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFlatProbability
open AspisK1.V7Tag73VariablePrefixGammaProbability
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

/-- Transport the gated residual event through the exact chronological
variable-prefix coordinates of one finite uniform tape.  Unread sampler
suffixes stay inside `TotalGammaDuplexTape` and remain arbitrary. -/
theorem uniform_tape_dependent_variable_prefix_restored_k15_residual_event_probability_le
    {Tape Residual : Type}
    [Fintype Tape] [Nonempty Tape]
    [Fintype Residual] [Nonempty Residual]
    (coordinates : Equiv Tape (Residual × TotalGammaDuplexTape))
    {decoder : ExactDecoderInstantiation QM31Exact}
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    (words : Residual → AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (provider : ∀ residual,
      VariablePrefixRestoredK15PreGammaProvider decoder (words residual))
    (event : Set Tape)
    (covered : event ⊆ coordinates ⁻¹'
      dependentSuccessfulSubtypeEvent GammaPrefixSucceeds (fun residual =>
        variablePrefixRestoredK15ResidualFlatEvent (provider residual))) :
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
      (initialBatchChallengeCap : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal) := by
  let successfulEvent : Residual → Set SuccessfulGammaPrefixTape :=
    fun residual =>
      variablePrefixRestoredK15ResidualFlatEvent (provider residual)
  let dependentEvent : Set (Residual × TotalGammaDuplexTape) :=
    dependentSuccessfulSubtypeEvent GammaPrefixSucceeds successfulEvent
  calc
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
        (PMF.uniformOfFintype Tape).toOuterMeasure
          (coordinates ⁻¹' dependentEvent) :=
      (PMF.uniformOfFintype Tape).toOuterMeasure.mono covered
    _ = (PMF.uniformOfFintype
          (Residual × TotalGammaDuplexTape)).toOuterMeasure
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
        (PMF.uniformOfFintype TotalGammaDuplexTape).toOuterMeasure
            (productEventFstSlice dependentEvent residual) =
          (PMF.uniformOfFintype TotalGammaDuplexTape).toOuterMeasure
            (successfulSubtypeEvent GammaPrefixSucceeds
              (successfulEvent residual)) := by
                rw [show dependentEvent =
                  dependentSuccessfulSubtypeEvent GammaPrefixSucceeds
                    successfulEvent by rfl,
                  productEventFstSlice_dependentSuccessfulSubtypeEvent]
        _ ≤ _ := variablePrefix_restored_k15_residual_total_probability_le
          published (provider residual)

/-- Average the exact variable-prefix source coordinates over the compiler's
arbitrary hidden-tape law.  The remaining `covered` argument is deterministic
source/semantic binding, not a probability premise. -/
theorem exact_compiler_dependent_variable_prefix_restored_k15_residual_event_probability_le
    {HiddenTape Residual : Type}
    [Fintype HiddenTape]
    [Fintype Residual] [Nonempty Residual]
    (hiddenLaw : PMF HiddenTape) (freshExposures : Nat)
    (coordinates : HiddenTape →
      Equiv (FreshAnswerTape Digest256 freshExposures)
        (Residual × TotalGammaDuplexTape))
    {decoder : ExactDecoderInstantiation QM31Exact}
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    (words : HiddenTape → Residual →
      AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (provider : ∀ hidden residual,
      VariablePrefixRestoredK15PreGammaProvider decoder
        (words hidden residual))
    (event : Set (HiddenTape × FreshAnswerTape Digest256 freshExposures))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      coordinates hidden ⁻¹'
        dependentSuccessfulSubtypeEvent GammaPrefixSucceeds (fun residual =>
          variablePrefixRestoredK15ResidualFlatEvent
            (provider hidden residual))) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw freshExposures).toOuterMeasure
        event ≤
      (initialBatchChallengeCap : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal) := by
  apply joint_event_probability_le_of_every_slice_le
  intro hidden
  exact
    uniform_tape_dependent_variable_prefix_restored_k15_residual_event_probability_le
      (coordinates hidden) published (words hidden) (provider hidden)
      (jointEventSlice event hidden) (covered hidden)

end

#print axioms
  uniform_tape_dependent_variable_prefix_restored_k15_residual_event_probability_le
#print axioms
  exact_compiler_dependent_variable_prefix_restored_k15_residual_event_probability_le

end AspisK1.V7Tag73VariablePrefixRestoredK15ConditioningBridge
