import AspisFormal.K1.V7Tag73ExactDagCandidateLabeledRootRouting

/-!
# Exact q16 output labels for the causal DAG

An exact q16 output can be exposed only once.  If its logical slot had already
been consumed, the controller's used-set provenance supplies an earlier
labelled output.  Unique producer slots then identify the same producer, and
clean-root input uniqueness contradicts two occurrences of its literal
squeeze input.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactDagQ16OutputLabel

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalDagProducerInvariant
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- A producer-backed exact-root output slot is absent from the used set at
its literal pre-answer state. -/
theorem exact_dag_q16_output_slot_unused
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
    (actor : QueryActor) (answer : Digest256)
    (producer : Q16DagProducer)
    (decomposition : exactFixedRootRecords input.package.root =
      prior ++
        (.machineFresh actor
          (bytes producer.digest ++ [domSqueeze]) answer :
            UnifiedExposureRecord) :: later)
    (producerMember : producer ∈
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial) prior
        (exactDagCandidateInitialState input)).memory.producers) :
    some producer.slot ∉
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial) prior
        (exactDagCandidateInitialState input)).memory.usedSlots := by
  let controller := exactDagTrialController transitionFuel trial
  let initial := exactDagCandidateInitialState input
  let selected : UnifiedExposureRecord :=
    .machineFresh actor (bytes producer.digest ++ [domSqueeze]) answer
  let reached := indexedStateAfterRecords transitionFuel controller prior initial
  intro used
  have initialFresh : some producer.slot ∉ initial.memory.usedSlots := by
    simp [initial, exactDagCandidateInitialState, inactiveDagMemory]
  have used' : some producer.slot ∈ reached.memory.usedSlots := by
    simpa [reached, controller, initial] using used
  obtain ⟨before, earlierRecord, after, priorExact, earlierPreferred⟩ :=
    dag_used_slot_has_prior_record transitionFuel trial.val prior initial
      (some producer.slot) initialFresh (by
        simpa [controller, exactDagTrialController, reached] using used')
  have fullExact : exactFixedRootRecords input.package.root =
      before ++ earlierRecord :: after ++ selected :: later := by
    rw [decomposition, priorExact]
  have earlierMember : earlierRecord ∈
      exactFixedRootRecords input.package.root := by
    rw [fullExact]
    simp
  obtain ⟨earlierActor, earlierInput, earlierAnswer, earlierExact⟩ :=
    exact_root_records_only_machine_fresh input earlierRecord earlierMember
  subst earlierRecord
  let beforeEarlier := indexedStateAfterRecords transitionFuel controller
    before initial
  have earlierAligned : unifiedRecordAtAnswer transitionFuel
      beforeEarlier.cursor earlierAnswer =
        .machineFresh earlierActor earlierInput earlierAnswer := by
    have aligned := exact_root_records_aligned_for_dag_controller input
      trial.val before
        (.machineFresh earlierActor earlierInput earlierAnswer)
        (after ++ selected :: later) (by
          simpa only [selected, List.cons_append, List.append_assoc] using
            fullExact)
    simpa [beforeEarlier, controller, exactDagTrialController, initial,
      UnifiedExposureRecord.answer] using aligned
  have earlierInputExact : unifiedInputBeforeAnswer? transitionFuel
      beforeEarlier.cursor = some earlierInput := by
    exact aligned_machine_record_has_exact_input transitionFuel
      beforeEarlier.cursor earlierActor earlierInput earlierAnswer
        earlierAligned
  have earlierPreferred' :
      dagPreferredSlotForInput trial.val beforeEarlier.exposureIndex
        beforeEarlier.memory earlierInput = some (some producer.slot) := by
    have preferredController : controller.preferredSlot beforeEarlier =
        some (some producer.slot) := by
      simpa [controller, exactDagTrialController, beforeEarlier, initial] using
        earlierPreferred
    change dagCandidatePreferredSlot transitionFuel trial.val beforeEarlier =
      some (some producer.slot) at preferredController
    unfold dagCandidatePreferredSlot at preferredController
    rw [earlierInputExact] at preferredController
    exact preferredController
  obtain ⟨earlierProducer, earlierProducerMember, earlierInputSource,
      earlierSlot⟩ :=
    dag_preferred_q16_slot_has_producer trial.val
      beforeEarlier.exposureIndex beforeEarlier.memory earlierInput
        producer.slot earlierPreferred'
  have producerPrefix : beforeEarlier.memory.producers <+:
      reached.memory.producers := by
    have producerGrowth := dag_indexed_state_producers_prefix transitionFuel
      trial.val
      ((.machineFresh earlierActor earlierInput earlierAnswer :
        UnifiedExposureRecord) :: after) beforeEarlier
    simpa [reached, beforeEarlier, controller, exactDagTrialController,
      initial, priorExact, indexed_state_after_records_append] using
        producerGrowth
  have earlierProducerInReached : earlierProducer ∈
      reached.memory.producers := producerPrefix.subset earlierProducerMember
  have reachedInvariant : Q16DagMemoryProducerInvariant reached.memory := by
    simpa [reached, controller, initial] using
      exact_dag_candidate_prefix_producer_invariant input trial prior
        (selected :: later) (by
          simpa [selected] using decomposition)
  have sameProducer : earlierProducer = producer :=
    q16_dag_producer_eq_of_slot_eq earlierProducer producer
      reached.memory.producers reachedInvariant.slotsNodup
      earlierProducerInReached (by
        simpa [reached, controller, initial] using producerMember) earlierSlot
  subst earlierProducer
  have repeatedInput : earlierInput =
      bytes producer.digest ++ [domSqueeze] := earlierInputSource
  have rootNodup := exact_root_record_causal_inputs_nodup input
  let suffix : List UnifiedExposureRecord :=
    (.machineFresh earlierActor earlierInput earlierAnswer :
      UnifiedExposureRecord) :: after ++ selected :: later
  have rootAtSuffix : exactFixedRootRecords input.package.root =
      before ++ suffix := by
    simpa only [suffix, List.cons_append, List.append_assoc] using fullExact
  rw [rootAtSuffix] at rootNodup
  have splitRootNodup : (before.map causalInput? ++
      suffix.map causalInput?).Nodup := by
    simpa only [List.map_append] using rootNodup
  have suffixNodup :
      (((.machineFresh earlierActor earlierInput earlierAnswer :
          UnifiedExposureRecord) :: after ++ selected :: later).map
        causalInput?).Nodup := by
    simpa only [suffix] using (List.nodup_append.mp splitRootNodup).2.1
  have earlierFresh := (List.nodup_cons.mp suffixNodup).1
  apply earlierFresh
  simp [selected, causalInput?, repeatedInput]

/-- Therefore a producer-backed exact output receives its literal q16 label
at the aligned pre-answer state. -/
theorem exact_dag_q16_output_has_preferred_slot
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
    (actor : QueryActor) (answer : Digest256)
    (producer : Q16DagProducer)
    (decomposition : exactFixedRootRecords input.package.root =
      prior ++
        (.machineFresh actor
          (bytes producer.digest ++ [domSqueeze]) answer :
            UnifiedExposureRecord) :: later)
    (producerMember : producer ∈
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial) prior
        (exactDagCandidateInitialState input)).memory.producers) :
    (exactDagTrialController transitionFuel trial).preferredSlot
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial) prior
        (exactDagCandidateInitialState input)) =
      some (some producer.slot) := by
  let reached := indexedStateAfterRecords transitionFuel
    (exactDagTrialController transitionFuel trial) prior
    (exactDagCandidateInitialState input)
  have inputExact : unifiedInputBeforeAnswer? transitionFuel reached.cursor =
      some (bytes producer.digest ++ [domSqueeze]) := by
    have aligned : unifiedRecordAtAnswer transitionFuel reached.cursor answer =
        .machineFresh actor (bytes producer.digest ++ [domSqueeze]) answer := by
      have rootAligned := exact_root_records_aligned_for_dag_controller input
        trial.val prior
          (.machineFresh actor (bytes producer.digest ++ [domSqueeze]) answer)
          later decomposition
      simpa [reached, exactDagTrialController,
        UnifiedExposureRecord.answer] using rootAligned
    exact aligned_machine_record_has_exact_input transitionFuel reached.cursor
      actor (bytes producer.digest ++ [domSqueeze]) answer aligned
  have invariant : Q16DagMemoryProducerInvariant reached.memory := by
    simpa [reached] using
      exact_dag_candidate_prefix_producer_invariant input trial prior
        ((.machineFresh actor (bytes producer.digest ++ [domSqueeze]) answer :
          UnifiedExposureRecord) :: later) decomposition
  have anchorWellFormed : Q16DagAnchorWellFormed reached.memory.anchor := by
    simpa [reached] using
      exact_dag_candidate_prefix_anchor_well_formed input trial prior
  have digestNodup :
      (reached.memory.producers.map Q16DagProducer.digest).Nodup := by
    simpa [reached] using
      exact_dag_candidate_prefix_producer_digests_nodup input trial prior
        ((.machineFresh actor (bytes producer.digest ++ [domSqueeze]) answer :
          UnifiedExposureRecord) :: later) decomposition
  have slotUnused : some producer.slot ∉ reached.memory.usedSlots := by
    simpa [reached] using
      exact_dag_q16_output_slot_unused input trial prior later actor answer
        producer decomposition producerMember
  have direct := dag_q16_output_is_preferred_of_producer trial.val
    reached.exposureIndex reached.memory producer invariant anchorWellFormed
      digestNodup (by simpa [reached] using producerMember) slotUnused
  change dagCandidatePreferredSlot transitionFuel trial.val reached =
    some (some producer.slot)
  unfold dagCandidatePreferredSlot
  rw [inputExact]
  exact direct

#print axioms exact_dag_q16_output_slot_unused
#print axioms exact_dag_q16_output_has_preferred_slot

end

end AspisK1.V7Tag73ExactDagQ16OutputLabel
