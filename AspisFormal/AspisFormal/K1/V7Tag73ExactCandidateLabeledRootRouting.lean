import AspisFormal.K1.V7Tag73ExactFinalWorkPairControllerCompletion
import AspisFormal.K1.V7Tag73IndexedControllerLabeledRecords

/-!
# Exact accepted root as a causal final-work/q16 label trace

The accepted adversary-then-verifier root prefix is replayed through the same
exposure-indexed candidate controller used by the exact compiler router.  This
module identifies its chronological labelled list and proves a conditional
but fully operational routing endpoint: once source lemmas establish label
uniqueness, residual capacity, and the selected pre-answer label, the named
router coordinate is exactly the literal root answer.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCandidateLabeledRootRouting

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalFinalWorkQ16UsedForest
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73ExactCausalRouterTapeAlignment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactProbabilityCoverageAudit
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- The literal controller selected by one chronological exposure trial. -/
def exactCandidateTrialController
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat) (trial : ExactCompilerExposureTrial parameters) :=
  finalWorkQ16CandidateController
    (globalFull256OracleCallCap parameters) transitionFuel trial.val

/-- Pre-answer labels and literal answers across the exact root prefix. -/
def exactCandidateRootLabels
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
    (trial : ExactCompilerExposureTrial parameters) :
    List (Option FinalWorkQ16DigestSlot × Digest256) :=
  indexedControllerLabeledRecords transitionFuel
    (exactCandidateTrialController transitionFuel trial)
    (exactPairControllerInitialState input)
    (exactFixedRootRecords input.package.root)

/-- Projected machine-fresh records retain the underlying answer list. -/
theorem projected_machine_fresh_records_map_answer
    (actor : QueryActor) :
    ∀ queries : List (ShaInput × Digest256),
      (projectedMachineFreshRecords actor queries).map
          UnifiedExposureRecord.answer =
        queries.map Prod.snd := by
  intro queries
  induction queries with
  | nil => rfl
  | cons query queries ih =>
      rcases query with ⟨input, answer⟩
      simp [projectedMachineFreshRecords, UnifiedExposureRecord.answer, ih]

/-- The exact actor-tagged root records carry exactly the combined root query
answers. -/
theorem exact_fixed_root_records_map_answer
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    (exactFixedRootRecords input.package.root).map
        UnifiedExposureRecord.answer =
      (exactRootFreshQueries input).map Prod.snd := by
  unfold exactFixedRootRecords fullProjectedRootRecords exactRootFreshQueries
  rw [List.map_append, projected_machine_fresh_records_map_answer,
    projected_machine_fresh_records_map_answer, List.map_append]

/-- The exact root labels form a genuine execution of the same pre-answer
machine compiled into the trial router. -/
theorem exact_candidate_root_labels_form_trace
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
    (trial : ExactCompilerExposureTrial parameters) :
    MachineLabeledTrace
      ((exactCandidateTrialController transitionFuel trial).machine
        transitionFuel)
      (exactPairControllerInitialState input)
      (exactCandidateRootLabels input trial)
      (indexedStateAfterRecords transitionFuel
        (exactCandidateTrialController transitionFuel trial)
        (exactFixedRootRecords input.package.root)
        (exactPairControllerInitialState input)) := by
  exact indexed_controller_labeled_records_form_trace transitionFuel
    (exactCandidateTrialController transitionFuel trial)
    (exactPairControllerInitialState input)
    (exactFixedRootRecords input.package.root)

/-- The labelled exact root reads the chronological prefix of the causal
router tape, followed by the untouched post-root answer suffix. -/
theorem exact_candidate_root_labels_tape_prefix
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
    (trial : ExactCompilerExposureTrial parameters) :
    freshAnswerTapeToList
        (finalWorkQ16NamedSlotInputTape
          (exactCompilerFinalWorkQ16InputTape parameters sample.2)) =
      (exactCandidateRootLabels input trial).map Prod.snd ++
        input.package.root.full.projection.rootPrefixes.verifier.remaining := by
  unfold exactCandidateRootLabels
  rw [indexed_controller_labeled_records_answers,
    exact_fixed_root_records_map_answer]
  exact exact_causal_router_tape_has_literal_root_prefix input

/-- Operational conditional endpoint for one selected root record.  The
remaining source-specific work is expressed only as exact finite facts about
the generated label list and the controller's pre-answer choice. -/
theorem exact_candidate_router_routes_selected_root_answer
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
    (actor : QueryActor) (queryInput : ShaInput) (answer : Digest256)
    (target : FinalWorkQ16DigestSlot)
    (decomposition : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh actor queryInput answer : UnifiedExposureRecord) ::
        later)
    (namedNodup :
      (namedTraceSlots (exactCandidateRootLabels input trial)).Nodup)
    (residualEnough :
      residualTraceSteps (exactCandidateRootLabels input trial) ≤
        (exactCompilerTargetCaps parameters).length - 513)
    (preferred :
      (exactCandidateTrialController transitionFuel trial).preferredSlot
        (indexedStateAfterRecords transitionFuel
          (exactCandidateTrialController transitionFuel trial) prior
          (exactPairControllerInitialState input)) = some target) :
    causalRoutedAnswer? target
        (exactCompilerExposureTrialFinalWorkQ16Router parameters
          transitionFuel trial
          (exactPlainRomCursor configuration sample.1).erase)
        (finalWorkQ16NamedSlotInputTape
          (exactCompilerFinalWorkQ16InputTape parameters sample.2)) =
      some answer := by
  let controller := exactCandidateTrialController transitionFuel trial
  let initial := exactPairControllerInitialState input
  let selected : UnifiedExposureRecord :=
    .machineFresh actor queryInput answer
  let priorLabels := indexedControllerLabeledRecords transitionFuel controller
    initial prior
  let reached := indexedStateAfterRecords transitionFuel controller prior initial
  let laterLabels := indexedControllerLabeledRecords transitionFuel controller
    (controller.afterAnswer transitionFuel reached answer) later
  have labelsDecomposition : exactCandidateRootLabels input trial =
      priorLabels ++ (some target, answer) :: laterLabels := by
    unfold exactCandidateRootLabels
    rw [decomposition,
      indexed_controller_labeled_records_append]
    simpa only [indexedControllerLabeledRecords,
      UnifiedExposureRecord.answer, controller, initial, reached,
      laterLabels, priorLabels, preferred]
  have routed := machine_labeled_trace_routes_named_answer
    (exact_candidate_root_labels_form_trace input trial) namedNodup
    (fun slot _member => Finset.mem_univ slot) residualEnough
    (finalWorkQ16NamedSlotInputTape
      (exactCompilerFinalWorkQ16InputTape parameters sample.2))
    input.package.root.full.projection.rootPrefixes.verifier.remaining
    (exact_candidate_root_labels_tape_prefix input trial)
    priorLabels laterLabels target answer labelsDecomposition
  exact routed

#print axioms projected_machine_fresh_records_map_answer
#print axioms exact_fixed_root_records_map_answer
#print axioms exact_candidate_root_labels_form_trace
#print axioms exact_candidate_root_labels_tape_prefix
#print axioms exact_candidate_router_routes_selected_root_answer

end

end AspisK1.V7Tag73ExactCandidateLabeledRootRouting
