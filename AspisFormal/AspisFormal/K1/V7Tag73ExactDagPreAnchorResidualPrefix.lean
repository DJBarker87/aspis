import AspisFormal.K1.V7Tag73CausalResidualCoordinatePrefix
import AspisFormal.K1.V7Tag73ExactDagQ16ChainRouting

/-!
# Exact q16 pre-anchor residual-prefix bridge

The final-work/q16 coordinate router reserves 513 named values and retains
every other chronological answer in its residual component.  The selected
pair's earlier source record is the anchor at which named routing begins.
This file proves the useful source-neutral consequence: equal residual
coordinates retain the identical literal answer prefix before that anchor.

This is not a claim that a replayed adversary returns the same proof after a
named coordinate is changed.  In particular, an adversary can have queried an
anchor coordinate first.  That cache-or-future causal step remains explicit.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactDagPreAnchorResidualPrefix

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalResidualCoordinatePrefix
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73CausalFinalWorkQ16UsedForest
open AspisK1.V7Tag73ExactCausalRouterTapeAlignment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactDagQ16ChainRouting
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- The literal root prefix before a trial anchor consumes only residual
positions and fits in the exact compiler's residual component. -/
theorem exact_dag_pre_anchor_residual_enough
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (trial : ExactCompilerExposureTrial parameters)
    (prior later : List UnifiedExposureRecord)
    (rootExact : exactFixedRootRecords input.package.root = prior ++ later)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap) :
    residualTraceSteps
      (indexedControllerLabeledRecords transitionFuel
        (exactDagTrialController transitionFuel trial)
        (exactDagCandidateInitialState input) prior) ≤
      (exactCompilerTargetCaps parameters).length - 513 := by
  let controller := exactDagTrialController transitionFuel trial
  let initial := exactDagCandidateInitialState input
  let prefixLabels := indexedControllerLabeledRecords transitionFuel
    controller initial prior
  let suffixLabels := indexedControllerLabeledRecords transitionFuel
    controller (indexedStateAfterRecords transitionFuel controller prior initial)
      later
  have labelsExact : exactDagCandidateRootLabels input trial =
      prefixLabels ++ suffixLabels := by
    unfold exactDagCandidateRootLabels
    rw [rootExact, indexed_controller_labeled_records_append]
  have fullEnough := exact_dag_candidate_root_residual_enough_of_programmed_cover
    input trial programmedCover
  rw [labelsExact, residual_trace_steps_append] at fullEnough
  have prefixLe : residualTraceSteps prefixLabels ≤
      residualTraceSteps prefixLabels + residualTraceSteps suffixLabels := by
    omega
  simpa only [prefixLabels, suffixLabels] using prefixLe.trans fullEnough

/-- Equality of the residual coordinate forces the literal answer prefix
strictly before the selected pair anchor to be replayed verbatim.  The right
tape is not assumed to be an accepted source execution; this is the exact
router-level fact needed before a separate cache-aware source replay can be
applied. -/
theorem exact_dag_residual_coordinate_forces_pre_anchor_tape_prefix
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (trial : ExactCompilerExposureTrial parameters)
    (prior later : List UnifiedExposureRecord)
    (rootExact : exactFixedRootRecords input.package.root = prior ++ later)
    (trialExact : trial.val = prior.length)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (coordinateExact :
      ((exactCompilerExposureTrialDagRouter parameters transitionFuel trial
        (exactPlainRomCursor configuration sample.1).erase).coordinateEquiv
        (finalWorkQ16NamedSlotInputTape
          (exactCompilerFinalWorkQ16InputTape parameters sample.2))).2 =
      ((exactCompilerExposureTrialDagRouter parameters transitionFuel trial
        (exactPlainRomCursor configuration sample.1).erase).coordinateEquiv
        (finalWorkQ16NamedSlotInputTape
          (exactCompilerFinalWorkQ16InputTape parameters right))).2) :
    ∃ rightRemaining,
      freshAnswerTapeToList
        (finalWorkQ16NamedSlotInputTape
          (exactCompilerFinalWorkQ16InputTape parameters right)) =
        prior.map UnifiedExposureRecord.answer ++ rightRemaining := by
  let controller := exactDagTrialController transitionFuel trial
  let initial := exactDagCandidateInitialState input
  let prefixLabels := indexedControllerLabeledRecords transitionFuel
    controller initial prior
  let suffixLabels := indexedControllerLabeledRecords transitionFuel
    controller (indexedStateAfterRecords transitionFuel controller prior initial)
      later
  have labelsExact : exactDagCandidateRootLabels input trial =
      prefixLabels ++ suffixLabels := by
    unfold exactDagCandidateRootLabels
    rw [rootExact, indexed_controller_labeled_records_append]
  obtain ⟨prefixState, prefixTrace⟩ : ∃ prefixState,
      MachineLabeledTrace (controller.machine transitionFuel) initial
        prefixLabels prefixState := by
    have rootTrace := exact_dag_candidate_root_labels_form_trace input trial
    have splitTrace : MachineLabeledTrace (controller.machine transitionFuel)
        initial (prefixLabels ++ suffixLabels)
        (indexedStateAfterRecords transitionFuel controller
          (exactFixedRootRecords input.package.root) initial) := by
      simpa only [controller, initial, labelsExact] using rootTrace
    obtain ⟨_middle, prefixTracePart, _suffix⟩ :=
      machine_labeled_trace_append_split prefixLabels suffixLabels splitTrace
    exact ⟨_middle, prefixTracePart⟩
  have allResidual : namedTraceSlots prefixLabels = [] := by
    apply dag_labeled_records_before_anchor_all_residual transitionFuel trial.val
      prior initial
    · simp [initial, exactDagCandidateInitialState, trialExact]
    · rfl
  have residualEnough : residualTraceSteps prefixLabels ≤
      (exactCompilerTargetCaps parameters).length - 513 := by
    simpa only [controller, initial, prefixLabels] using
      exact_dag_pre_anchor_residual_enough input trial prior later rootExact
        programmedCover
  have leftPrefix : freshAnswerTapeToList
      (finalWorkQ16NamedSlotInputTape
        (exactCompilerFinalWorkQ16InputTape parameters sample.2)) =
      prefixLabels.map Prod.snd ++
        (suffixLabels.map Prod.snd ++
          input.package.root.full.projection.rootPrefixes.verifier.remaining) := by
    rw [exact_dag_candidate_root_labels_tape_prefix input trial, labelsExact,
      List.map_append, List.append_assoc]
  have leftTraceExact : freshAnswerTapeToList
      (finalWorkQ16NamedSlotInputTape
        (exactCompilerFinalWorkQ16InputTape parameters sample.2)) =
      prefixLabels.map Prod.snd ++
        (freshAnswerTapeToList
          (finalWorkQ16NamedSlotInputTape
            (exactCompilerFinalWorkQ16InputTape parameters sample.2))).drop
          prefixLabels.length := by
    rw [leftPrefix]
    have prefixLength : (prefixLabels.map Prod.snd).length =
        prefixLabels.length := by simp
    rw [← prefixLength, List.drop_append_of_le_length (Nat.le_refl _)]
    simp
  have routerCoordinateExact :
      (((controller.machine transitionFuel).fullRouter
        ((exactCompilerTargetCaps parameters).length - 513) initial).coordinateEquiv
        (finalWorkQ16NamedSlotInputTape
          (exactCompilerFinalWorkQ16InputTape parameters sample.2))).2 =
      (((controller.machine transitionFuel).fullRouter
        ((exactCompilerTargetCaps parameters).length - 513) initial).coordinateEquiv
        (finalWorkQ16NamedSlotInputTape
          (exactCompilerFinalWorkQ16InputTape parameters right))).2 := by
    change
      ((exactCompilerExposureTrialDagRouter parameters transitionFuel trial
        (exactPlainRomCursor configuration sample.1).erase).coordinateEquiv
        (finalWorkQ16NamedSlotInputTape
          (exactCompilerFinalWorkQ16InputTape parameters sample.2))).2 =
      ((exactCompilerExposureTrialDagRouter parameters transitionFuel trial
        (exactPlainRomCursor configuration sample.1).erase).coordinateEquiv
        (finalWorkQ16NamedSlotInputTape
          (exactCompilerFinalWorkQ16InputTape parameters right))).2 at coordinateExact
    exact coordinateExact
  obtain ⟨rightRemaining, rightPrefix⟩ :=
    all_residual_trace_forces_right_prefix prefixTrace allResidual residualEnough
      (finalWorkQ16NamedSlotInputTape
        (exactCompilerFinalWorkQ16InputTape parameters sample.2))
      (finalWorkQ16NamedSlotInputTape
        (exactCompilerFinalWorkQ16InputTape parameters right)) leftTraceExact
      routerCoordinateExact
  have prefixAnswers : prefixLabels.map Prod.snd =
      prior.map UnifiedExposureRecord.answer := by
    exact indexed_controller_labeled_records_answers transitionFuel controller
      initial prior
  refine ⟨rightRemaining, ?_⟩
  rw [prefixAnswers] at rightPrefix
  exact rightPrefix

#print axioms exact_dag_pre_anchor_residual_enough
#print axioms exact_dag_residual_coordinate_forces_pre_anchor_tape_prefix

end

end AspisK1.V7Tag73ExactDagPreAnchorResidualPrefix
