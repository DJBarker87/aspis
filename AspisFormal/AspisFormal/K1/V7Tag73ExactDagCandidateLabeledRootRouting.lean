import AspisFormal.K1.V7Tag73CausalDagFinalWorkQ16Controller
import AspisFormal.K1.V7Tag73CausalDagProducerInvariant
import AspisFormal.K1.V7Tag73ExactCandidateLabeledRootRouting
import AspisFormal.K1.V7Tag73ExactFinalWorkPairControllerCompletion
import AspisFormal.K1.V7Tag73IndexedAlignedRecordReplay

/-!
# Exact accepted root routed by the causal-DAG controller

This specialization replaces the sequential branch cell with the causal q16
producer DAG.  It inherits the exact root/tape chronology and discharges
named-slot noduplication internally through the controller's monotone used set.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalDagProducerInvariant
open AspisK1.V7Tag73CausalFinalWorkQ16UsedForest
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73ExactCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactCausalRouterTapeAlignment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactPlainRomTraceResourceCaps
open AspisK1.V7Tag73ExactProbabilityCoverageAudit
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

def exactDagCandidateInitialState
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (_input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    IndexedUnifiedExposureState (globalFull256OracleCallCap parameters)
      FinalWorkQ16DagMemory :=
  { exposureIndex := 0
    cursor := (exactPlainRomCursor configuration sample.1).erase
    memory := inactiveDagMemory }

def exactDagTrialController
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat) (trial : ExactCompilerExposureTrial parameters) :=
  finalWorkQ16DagController
    (globalFull256OracleCallCap parameters) transitionFuel trial.val

theorem nonpadding_exposure_answers_append
    (first second : List UnifiedExposureRecord) :
    nonpaddingExposureAnswers (first ++ second) =
      nonpaddingExposureAnswers first ++ nonpaddingExposureAnswers second := by
  induction first with
  | nil => rfl
  | cons record records ih =>
      cases record <;> simp [nonpaddingExposureAnswers, ih]

theorem projected_machine_fresh_nonpadding_answers
    (actor : QueryActor) (queries : List (ShaInput × Digest256)) :
    nonpaddingExposureAnswers (projectedMachineFreshRecords actor queries) =
      queries.map Prod.snd := by
  induction queries with
  | nil => rfl
  | cons query queries ih =>
      rcases query with ⟨input, answer⟩
      simp [projectedMachineFreshRecords, nonpaddingExposureAnswers, ih,
        UnifiedExposureRecord.answer]

/-- Clean exact-root answers are pairwise distinct.  This is the source fact
that makes the executable producer scan unambiguous. -/
theorem exact_root_record_answers_nodup
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
    ((exactFixedRootRecords input.package.root).map
      UnifiedExposureRecord.answer).Nodup := by
  have fullNodup :=
    input.package.root.wholeTraceClean.nonpaddingAnswersNodup
  rw [exact_compiler_unified_exposure_trace_is_actual_plain_rom_trace
    transitionFuel configuration sample] at fullNodup
  rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
    configuration projection fixedInstance sample input.package] at fullNodup
  unfold exactFixedOperationalStateMapTrace at fullNodup
  rw [nonpadding_exposure_answers_append] at fullNodup
  have rootNodup := (List.nodup_append.mp fullNodup).1
  have rootAnswersExact :
      nonpaddingExposureAnswers (exactFixedRootRecords input.package.root) =
        (exactFixedRootRecords input.package.root).map
          UnifiedExposureRecord.answer := by
    unfold exactFixedRootRecords fullProjectedRootRecords
    rw [nonpadding_exposure_answers_append,
      projected_machine_fresh_nonpadding_answers,
      projected_machine_fresh_nonpadding_answers]
    simp [projectedMachineFreshRecords, List.map_append]
  rw [rootAnswersExact] at rootNodup
  exact rootNodup

/-- The exact accepted root trace is cursor-aligned with the causal-DAG
controller at every fixed trial anchor. -/
theorem exact_root_records_aligned_for_dag_controller
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
    (anchor : Nat) :
    IndexedRecordsAligned transitionFuel
      (finalWorkQ16DagController
        (globalFull256OracleCallCap parameters) transitionFuel anchor)
      (exactDagCandidateInitialState input)
      (exactFixedRootRecords input.package.root) := by
  let controller := finalWorkQ16DagController
    (globalFull256OracleCallCap parameters) transitionFuel anchor
  let rootTape := operationalTapeCoordinates
    (globalFull256OracleCallCap parameters) 1
    (unifiedFull256ExposureCap parameters)
    (exactCompilerOperationalIndexedTape parameters sample.2)
  have traceExact :
      runUnifiedExposureTrace transitionFuel
          (unifiedFull256ExposureCap parameters)
          (exactPlainRomCursor configuration sample.1).erase rootTape =
        (runExactPlainRom transitionFuel configuration sample).trace := by
    simpa [rootTape, exactCompilerUnifiedExposureTrace] using
      exact_compiler_unified_exposure_trace_is_actual_plain_rom_trace
        transitionFuel configuration sample
  have fullAligned := indexed_records_aligned_of_trace transitionFuel
    controller (exactDagCandidateInitialState input) rootTape
      (runExactPlainRom transitionFuel configuration sample).trace traceExact
  have fullSplit :
      (runExactPlainRom transitionFuel configuration sample).trace =
        [] ++ exactFixedRootRecords input.package.root ++
          (exactFixedComputedClientTailRun transitionFuel configuration sample
            input.package.root).trace := by
    rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
      configuration projection fixedInstance sample input.package]
    rfl
  have rootAligned := indexed_records_aligned_segment transitionFuel controller
    (exactDagCandidateInitialState input)
    (runExactPlainRom transitionFuel configuration sample).trace []
    (exactFixedRootRecords input.package.root)
    (exactFixedComputedClientTailRun transitionFuel configuration sample
      input.package.root).trace fullAligned fullSplit
  simpa only [indexed_state_after_records_nil] using rootAligned

def exactCompilerExposureTrialDagRouter
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat) (trial : ExactCompilerExposureTrial parameters)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    ExactCompilerCausalFinalWorkQ16Router parameters :=
  exactCompilerIndexedFinalWorkQ16Router parameters transitionFuel
    (exactDagTrialController transitionFuel trial) inactiveDagMemory cursor

def exactCompilerExposureTrialDagCoordinates
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat) (trial : ExactCompilerExposureTrial parameters)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactCompilerFinalWorkQ16Residual parameters ×
        (Digest256 × Q16CandidateDigestForest) :=
  exactCompilerIndexedFinalWorkQ16Coordinates parameters transitionFuel
    (exactDagTrialController transitionFuel trial) inactiveDagMemory cursor

def exactDagCandidateRootLabels
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
    (exactDagTrialController transitionFuel trial)
    (exactDagCandidateInitialState input)
    (exactFixedRootRecords input.package.root)

theorem exact_dag_candidate_root_labels_form_trace
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
      ((exactDagTrialController transitionFuel trial).machine transitionFuel)
      (exactDagCandidateInitialState input)
      (exactDagCandidateRootLabels input trial)
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial)
        (exactFixedRootRecords input.package.root)
        (exactDagCandidateInitialState input)) := by
  exact indexed_controller_labeled_records_form_trace transitionFuel
    (exactDagTrialController transitionFuel trial)
    (exactDagCandidateInitialState input)
    (exactFixedRootRecords input.package.root)

theorem exact_dag_candidate_root_named_slots_nodup
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
    (namedTraceSlots (exactDagCandidateRootLabels input trial)).Nodup := by
  exact dag_labeled_records_named_slots_nodup transitionFuel trial.val
    (exactFixedRootRecords input.package.root)
    (exactDagCandidateInitialState input)

/-- The final exact-root causal inventory has no duplicate producer digest. -/
theorem exact_dag_candidate_root_producer_digests_nodup
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
    (((indexedStateAfterRecords transitionFuel
      (exactDagTrialController transitionFuel trial)
      (exactFixedRootRecords input.package.root)
      (exactDagCandidateInitialState input)).memory.producers).map
        Q16DagProducer.digest).Nodup := by
  apply dag_indexed_state_producer_digests_nodup transitionFuel trial.val
    (exactFixedRootRecords input.package.root)
    (exactDagCandidateInitialState input)
  · exact exact_root_record_answers_nodup input
  · simp [exactDagCandidateInitialState, inactiveDagMemory]
  · simp [exactDagCandidateInitialState, inactiveDagMemory]

/-- The full exact-root replay satisfies recursive producer provenance and
has duplicate-free source inputs and slots.  This is obtained from literal
root-input freshness, not from a sequential ordering assumption on q16
siblings. -/
theorem exact_dag_candidate_root_producer_invariant
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
    Q16DagMemoryProducerInvariant
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial)
        (exactFixedRootRecords input.package.root)
        (exactDagCandidateInitialState input)).memory := by
  apply aligned_machine_records_preserve_dag_producer_invariant
    transitionFuel trial.val
      (exactFixedRootRecords input.package.root)
      (exactDagCandidateInitialState input)
  · exact exact_root_records_aligned_for_dag_controller input trial.val
  · exact exact_root_records_only_machine_fresh input
  · exact exact_root_record_causal_inputs_nodup input
  · exact inactive_dag_memory_producer_invariant
  · simp [exactDagCandidateInitialState, inactiveDagMemory]

/-- The same producer invariant holds at every exact root prefix, which is
the form needed immediately before a selected q16 output record. -/
theorem exact_dag_candidate_prefix_producer_invariant
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
    (decomposition : exactFixedRootRecords input.package.root = prior ++ later) :
    Q16DagMemoryProducerInvariant
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial) prior
        (exactDagCandidateInitialState input)).memory := by
  let controller := exactDagTrialController transitionFuel trial
  let initial := exactDagCandidateInitialState input
  have priorAligned : IndexedRecordsAligned transitionFuel controller initial
      prior := by
    apply indexed_records_aligned_segment transitionFuel controller initial
      (exactFixedRootRecords input.package.root) [] prior later
      (by simpa [controller, exactDagTrialController, initial] using
        exact_root_records_aligned_for_dag_controller input trial.val)
    simpa using decomposition
  have priorOnly : OnlyMachineFreshRecords prior := by
    apply only_machine_fresh_records_segment
      (exactFixedRootRecords input.package.root) [] prior later
      (exact_root_records_only_machine_fresh input)
    simpa using decomposition
  have priorInputsNodup : (prior.map causalInput?).Nodup := by
    have rootNodup := exact_root_record_causal_inputs_nodup input
    rw [decomposition, List.map_append] at rootNodup
    exact (List.nodup_append.mp rootNodup).1
  simpa [controller, exactDagTrialController, initial] using
    aligned_machine_records_preserve_dag_producer_invariant
      transitionFuel trial.val prior initial priorAligned priorOnly
      priorInputsNodup inactive_dag_memory_producer_invariant (by
        simp [initial, exactDagCandidateInitialState, inactiveDagMemory])

/-- Clean answer uniqueness likewise restricts to every exact root prefix. -/
theorem exact_dag_candidate_prefix_producer_digests_nodup
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
    (decomposition : exactFixedRootRecords input.package.root = prior ++ later) :
    (((indexedStateAfterRecords transitionFuel
      (exactDagTrialController transitionFuel trial) prior
      (exactDagCandidateInitialState input)).memory.producers).map
        Q16DagProducer.digest).Nodup := by
  have priorAnswersNodup :
      (prior.map UnifiedExposureRecord.answer).Nodup := by
    have rootNodup := exact_root_record_answers_nodup input
    rw [decomposition, List.map_append] at rootNodup
    exact (List.nodup_append.mp rootNodup).1
  simpa [exactDagTrialController] using
    dag_indexed_state_producer_digests_nodup transitionFuel trial.val prior
      (exactDagCandidateInitialState input) priorAnswersNodup
      (by simp [exactDagCandidateInitialState, inactiveDagMemory])
      (by simp [exactDagCandidateInitialState, inactiveDagMemory])

/-- Every exact prefix also retains the canonical key widths established by
the raw final-work parsers. -/
theorem exact_dag_candidate_prefix_anchor_well_formed
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
    (prior : List UnifiedExposureRecord) :
    Q16DagAnchorWellFormed
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial) prior
        (exactDagCandidateInitialState input)).memory.anchor := by
  simpa [exactDagTrialController] using
    dag_indexed_state_anchor_well_formed transitionFuel trial.val prior
      (exactDagCandidateInitialState input) (by
        simp [exactDagCandidateInitialState, inactiveDagMemory,
          Q16DagAnchorWellFormed])

theorem exact_dag_candidate_root_labels_tape_prefix
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
      (exactDagCandidateRootLabels input trial).map Prod.snd ++
        input.package.root.full.projection.rootPrefixes.verifier.remaining := by
  unfold exactDagCandidateRootLabels
  rw [indexed_controller_labeled_records_answers,
    exact_fixed_root_records_map_answer]
  exact exact_causal_router_tape_has_literal_root_prefix input

/-- For the deployed restoration regime, the two programmed coordinates per
fork already provide at least the 513-coordinate named inventory.  Hence the
entire root machine-fresh prefix fits in the joint router's residual even
before crediting any actual named labels.  This deliberately conservative
bound avoids circular dependence on q16 label classification. -/
theorem exact_dag_candidate_root_residual_enough_of_programmed_cover
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
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap) :
    residualTraceSteps (exactDagCandidateRootLabels input trial) ≤
      (exactCompilerTargetCaps parameters).length - 513 := by
  let rootRecords := exactFixedRootRecords input.package.root
  let labels := exactDagCandidateRootLabels input trial
  have labelsLength : labels.length = rootRecords.length := by
    have answers := congrArg List.length
      (indexed_controller_labeled_records_answers transitionFuel
        (exactDagTrialController transitionFuel trial)
        (exactDagCandidateInitialState input) rootRecords)
    simpa [labels, exactDagCandidateRootLabels, rootRecords] using answers
  have residualLeLabels : residualTraceSteps labels ≤ labels.length := by
    have split := labeled_trace_length_split labels
    omega
  have projectedLength (actor : QueryActor) :
      ∀ queries : List (ShaInput × Digest256),
        (projectedMachineFreshRecords actor queries).length = queries.length := by
    intro queries
    induction queries with
    | nil => rfl
    | cons query queries ih =>
        rcases query with ⟨queryInput, answer⟩
        simp [projectedMachineFreshRecords, ih]
  have rootCountExact : rootRecords.length =
      machineFreshCoordinateCount rootRecords := by
    unfold rootRecords exactFixedRootRecords fullProjectedRootRecords
    simp [projectedLength]
  have rootMachineLe : machineFreshCoordinateCount rootRecords ≤
      machineFreshCoordinateCount
        (runExactPlainRom transitionFuel configuration sample).trace := by
    rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
      configuration projection fixedInstance sample input.package]
    unfold exactFixedOperationalStateMapTrace
    simp [rootRecords]
  have rootLengthLe : rootRecords.length ≤
      full256MachineFreshCap parameters := by
    rw [rootCountExact]
    exact rootMachineLe.trans input.package.root.traceCaps.1
  have fullCapLe : full256MachineFreshCap parameters ≤
      (exactCompilerTargetCaps parameters).length - 513 := by
    rw [exact_compiler_target_caps_length]
    unfold unifiedFull256ExposureCap sameTapeStartCap
    omega
  exact residualLeLabels.trans
    (labelsLength.le.trans (rootLengthLe.trans fullCapLe))

/-- The operational root-routing endpoint now has no caller-supplied label
uniqueness premise. -/
theorem exact_dag_candidate_router_routes_selected_root_answer
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
    (residualEnough :
      residualTraceSteps (exactDagCandidateRootLabels input trial) ≤
        (exactCompilerTargetCaps parameters).length - 513)
    (preferred :
      (exactDagTrialController transitionFuel trial).preferredSlot
        (indexedStateAfterRecords transitionFuel
          (exactDagTrialController transitionFuel trial) prior
          (exactDagCandidateInitialState input)) = some target) :
    causalRoutedAnswer? target
        (exactCompilerExposureTrialDagRouter parameters transitionFuel trial
          (exactPlainRomCursor configuration sample.1).erase)
        (finalWorkQ16NamedSlotInputTape
          (exactCompilerFinalWorkQ16InputTape parameters sample.2)) =
      some answer := by
  let controller := exactDagTrialController transitionFuel trial
  let initial := exactDagCandidateInitialState input
  let priorLabels := indexedControllerLabeledRecords transitionFuel controller
    initial prior
  let reached := indexedStateAfterRecords transitionFuel controller prior initial
  let laterLabels := indexedControllerLabeledRecords transitionFuel controller
    (controller.afterAnswer transitionFuel reached answer) later
  have labelsDecomposition : exactDagCandidateRootLabels input trial =
      priorLabels ++ (some target, answer) :: laterLabels := by
    unfold exactDagCandidateRootLabels
    rw [decomposition, indexed_controller_labeled_records_append]
    simpa only [indexedControllerLabeledRecords,
      UnifiedExposureRecord.answer, controller, initial, reached,
      laterLabels, priorLabels, preferred]
  exact machine_labeled_trace_routes_named_answer
    (exact_dag_candidate_root_labels_form_trace input trial)
    (exact_dag_candidate_root_named_slots_nodup input trial)
    (fun slot _member => Finset.mem_univ slot) residualEnough
    (finalWorkQ16NamedSlotInputTape
      (exactCompilerFinalWorkQ16InputTape parameters sample.2))
    input.package.root.full.projection.rootPrefixes.verifier.remaining
    (exact_dag_candidate_root_labels_tape_prefix input trial)
    priorLabels laterLabels target answer labelsDecomposition

#print axioms exactDagCandidateInitialState
#print axioms exact_root_record_answers_nodup
#print axioms exact_root_records_aligned_for_dag_controller
#print axioms exactCompilerExposureTrialDagRouter
#print axioms exactCompilerExposureTrialDagCoordinates
#print axioms exact_dag_candidate_root_labels_form_trace
#print axioms exact_dag_candidate_root_named_slots_nodup
#print axioms exact_dag_candidate_root_producer_digests_nodup
#print axioms exact_dag_candidate_root_producer_invariant
#print axioms exact_dag_candidate_prefix_producer_invariant
#print axioms exact_dag_candidate_prefix_producer_digests_nodup
#print axioms exact_dag_candidate_prefix_anchor_well_formed
#print axioms exact_dag_candidate_root_labels_tape_prefix
#print axioms exact_dag_candidate_root_residual_enough_of_programmed_cover
#print axioms exact_dag_candidate_router_routes_selected_root_answer

end

end AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
