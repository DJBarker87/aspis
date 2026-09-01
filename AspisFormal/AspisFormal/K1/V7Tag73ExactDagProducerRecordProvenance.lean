import AspisFormal.K1.V7Tag73ExactDagCandidateLabeledRootRouting

/-!
# Literal record provenance for causal-DAG q16 producers

The executable q16 controller remembers only digests, logical slots, and the
source input that created each producer.  This file recovers the corresponding
literal machine-fresh record from an aligned replay.  The result is deliberately
generic: it uses only the controller transition and does not assume that the
machine, rather than the adversary, first exposed the coordinate.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactDagProducerRecordProvenance

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure

noncomputable section

/-- Every producer present after an aligned machine-fresh replay was either
already present initially or was created by one literal record in the replay.
Both the remembered source input and digest agree with that record. -/
theorem dag_indexed_state_producer_has_literal_record
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FinalWorkQ16DagMemory),
      IndexedRecordsAligned transitionFuel
          (finalWorkQ16DagController globalOracleCalls transitionFuel
            anchorIndex) state records →
      OnlyMachineFreshRecords records →
      ∀ producer,
        producer ∈
          (indexedStateAfterRecords transitionFuel
            (finalWorkQ16DagController globalOracleCalls transitionFuel
              anchorIndex) records state).memory.producers →
        producer ∈ state.memory.producers ∨
          ∃ actor input answer,
            (.machineFresh actor input answer : UnifiedExposureRecord) ∈
                records ∧
              producer.sourceInput = input ∧ producer.digest = answer := by
  intro records
  induction records with
  | nil =>
      intro state _aligned _onlyMachine producer member
      exact Or.inl (by
        simpa only [indexed_state_after_records_nil] using member)
  | cons head tail ih =>
      intro state aligned onlyMachine producer member
      obtain ⟨actor, input, answer, headExact⟩ :=
        onlyMachine head (by simp)
      subst head
      let controller := finalWorkQ16DagController globalOracleCalls
        transitionFuel anchorIndex
      let next := controller.afterAnswer transitionFuel state answer
      have headAligned := aligned [] (.machineFresh actor input answer) tail
        (by rfl)
      have inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
          some input := by
        simpa only [indexed_state_after_records_nil] using
          aligned_machine_record_has_exact_input transitionFuel state.cursor
            actor input answer headAligned
      have tailAligned : IndexedRecordsAligned transitionFuel controller next
          tail := by
        apply indexed_records_aligned_segment transitionFuel controller state
          ((.machineFresh actor input answer) :: tail)
          [(.machineFresh actor input answer)] tail [] aligned
        simp
      have tailOnly : OnlyMachineFreshRecords tail := by
        intro record recordMember
        exact onlyMachine record (by simp [recordMember])
      have tailMember : producer ∈
          (indexedStateAfterRecords transitionFuel controller tail next).memory.producers := by
        simpa [controller, next, indexed_state_after_records_cons,
          UnifiedExposureRecord.answer] using member
      rcases ih next tailAligned tailOnly producer tailMember with
        nextMember | ⟨recordActor, recordInput, recordAnswer, recordMember,
          sourceExact, digestExact⟩
      · change producer ∈
          (dagCandidateAfterMemory transitionFuel anchorIndex state
            answer).producers at nextMember
        rcases dag_candidate_memory_producers_eq_or_append transitionFuel
            anchorIndex state answer with unchanged | ⟨slot, appended⟩
        · rw [unchanged] at nextMember
          exact Or.inl nextMember
        · rw [appended, List.mem_append] at nextMember
          rcases nextMember with old | added
          · exact Or.inl old
          · simp only [List.mem_singleton] at added
            subst producer
            exact Or.inr ⟨actor, input, answer, by simp,
              by simp [inputExact], rfl⟩
      · exact Or.inr ⟨recordActor, recordInput, recordAnswer,
          by simp [recordMember], sourceExact, digestExact⟩

/-- In the exact accepted execution the initial DAG inventory is empty, so a
producer present at any root prefix has one literal source record in that
prefix.  This is the form used to compare producer digests with transcript
states under the clean-root answer-uniqueness event. -/
theorem exact_dag_prefix_producer_has_literal_record
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
    (decomposition : exactFixedRootRecords input.package.root = prior ++ later)
    (producer : Q16DagProducer)
    (member : producer ∈
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial) prior
        (exactDagCandidateInitialState input)).memory.producers) :
    ∃ actor,
      (.machineFresh actor producer.sourceInput producer.digest :
          UnifiedExposureRecord) ∈ prior := by
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
  have provenance := dag_indexed_state_producer_has_literal_record
    transitionFuel trial.val prior initial priorAligned priorOnly producer (by
      simpa [controller, exactDagTrialController, initial] using member)
  rcases provenance with initialMember |
      ⟨actor, recordInput, recordAnswer, recordMember, sourceExact,
        digestExact⟩
  · simpa [initial, exactDagCandidateInitialState, inactiveDagMemory] using
      initialMember
  · subst recordInput
    subst recordAnswer
    exact ⟨actor, recordMember⟩

#print axioms dag_indexed_state_producer_has_literal_record
#print axioms exact_dag_prefix_producer_has_literal_record

end

end AspisK1.V7Tag73ExactDagProducerRecordProvenance
