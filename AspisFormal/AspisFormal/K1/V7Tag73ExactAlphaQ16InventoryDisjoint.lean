import AspisFormal.K1.V7Tag73AlphaQ16InventoryDisjoint
import AspisFormal.K1.V7Tag73ExactAlphaQ16ProducerSeparation
import AspisFormal.K1.V7Tag73ExactAlphaZeroControllerAlignment
import AspisFormal.K1.V7Tag73ExactDagQ16ChainRouting

/-!
# Exact accepted-root alpha/q16 inventory disjointness

The structural grammar theorem is instantiated at one literal accepted-root
prefix.  Both producer inventories are replayed from the same prefix, and
clean-root answer uniqueness turns a hypothetical equal digest into equality
of the two literal source records.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactAlphaQ16InventoryDisjoint

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaQ16InventoryDisjoint
open AspisK1.V7Tag73AlphaZeroBoundaryInvariant
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AlphaZeroProducerInvariant
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalDagProducerInvariant
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73ExactAlphaZeroControllerAlignment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactDagProducerRecordProvenance
open AspisK1.V7Tag73ExactDagQ16ChainRouting
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

theorem exact_alpha_prefix_producer_has_literal_record
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
    (boundaryIndex : Nat)
    (prior later : List UnifiedExposureRecord)
    (decomposition : exactFixedRootRecords input.package.root = prior ++ later)
    (producer : AlphaZeroProducer)
    (member : producer ∈
      (AspisK1.V7Tag73IndexedControllerTraceAlignment.indexedStateAfterRecords
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        (Slot := Fin 4) (Memory := AlphaZeroControllerMemory)
        transitionFuel
        (alphaZeroCausalController transitionFuel boundaryIndex) prior
        (exactAlphaZeroInitialState input)).memory.producers) :
    ∃ actor,
      (.machineFresh actor producer.sourceInput producer.digest :
          UnifiedExposureRecord) ∈ prior := by
  let controller := alphaZeroCausalController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel boundaryIndex
  let initial := exactAlphaZeroInitialState input
  have priorAligned : IndexedRecordsAligned transitionFuel controller initial
      prior := by
    apply indexed_records_aligned_segment transitionFuel controller initial
      (exactFixedRootRecords input.package.root) [] prior later
      (by simpa [controller, initial] using
        exact_root_records_aligned_for_alpha_zero_controller input boundaryIndex)
    simpa using decomposition
  have priorOnly : OnlyMachineFreshRecords prior := by
    apply only_machine_fresh_records_segment
      (exactFixedRootRecords input.package.root) [] prior later
      (exact_root_records_only_machine_fresh input)
    simpa using decomposition
  have provenance := alpha_zero_indexed_state_producer_has_literal_record
    transitionFuel boundaryIndex prior initial priorAligned priorOnly producer (by
      simpa [controller, initial] using member)
  rcases provenance with initialMember |
      ⟨actor, recordInput, recordAnswer, recordMember, sourceExact,
        digestExact⟩
  · simpa [initial, exactAlphaZeroInitialState, inactiveAlphaZeroMemory] using
      initialMember
  · subst recordInput
    subst recordAnswer
    exact ⟨actor, recordMember⟩

theorem exact_alpha_q16_prefix_producer_digests_disjoint
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
    (boundaryIndex : Nat)
    (prior later : List UnifiedExposureRecord)
    (decomposition : exactFixedRootRecords input.package.root = prior ++ later) :
    ∀ alpha ∈
        (AspisK1.V7Tag73IndexedControllerTraceAlignment.indexedStateAfterRecords
          (globalOracleCalls := globalFull256OracleCallCap parameters)
          (Slot := Fin 4) (Memory := AlphaZeroControllerMemory)
          transitionFuel
          (alphaZeroCausalController
            (globalOracleCalls := globalFull256OracleCallCap parameters)
            transitionFuel boundaryIndex) prior
          (exactAlphaZeroInitialState input)).memory.producers,
      ∀ q16 ∈
        (AspisK1.V7Tag73IndexedControllerTraceAlignment.indexedStateAfterRecords
          (globalOracleCalls := globalFull256OracleCallCap parameters)
          (Slot := FinalWorkQ16DigestSlot)
          (Memory := FinalWorkQ16DagMemory)
          transitionFuel
          (exactDagTrialController (parameters := parameters)
            transitionFuel trial) prior
          (exactDagCandidateInitialState input)).memory.producers,
        alpha.digest ≠ q16.digest := by
  let alphaState : IndexedUnifiedExposureState
      (globalFull256OracleCallCap parameters) AlphaZeroControllerMemory :=
    AspisK1.V7Tag73IndexedControllerTraceAlignment.indexedStateAfterRecords
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      (Slot := Fin 4) (Memory := AlphaZeroControllerMemory)
      transitionFuel
      (alphaZeroCausalController
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        transitionFuel boundaryIndex) prior
      (exactAlphaZeroInitialState input)
  let dagState : IndexedUnifiedExposureState
      (globalFull256OracleCallCap parameters) FinalWorkQ16DagMemory :=
    AspisK1.V7Tag73IndexedControllerTraceAlignment.indexedStateAfterRecords
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      (Slot := FinalWorkQ16DigestSlot) (Memory := FinalWorkQ16DagMemory)
      transitionFuel
      (exactDagTrialController (parameters := parameters)
        transitionFuel trial) prior
      (exactDagCandidateInitialState input)
  have alphaInvariant : AlphaZeroMemoryProducerInvariant
      alphaState.memory := by
    simpa [alphaState] using exact_alpha_zero_prefix_producer_invariant input
      boundaryIndex prior later decomposition
  have alphaBoundary : AlphaZeroBlockZeroBoundaryValid
      alphaState.memory.producers := by
    simpa [alphaState] using
      alpha_zero_indexed_state_preserves_block_zero_boundary transitionFuel
        boundaryIndex prior (exactAlphaZeroInitialState input)
          (by simpa [exactAlphaZeroInitialState] using
            inactive_alpha_zero_block_zero_boundary_valid)
  have dagInvariant : Q16DagMemoryProducerInvariant dagState.memory := by
    simpa [dagState] using exact_dag_candidate_prefix_producer_invariant input
      trial prior later decomposition
  intro alpha alphaMember q16 q16Member
  change alpha ∈ alphaState.memory.producers at alphaMember
  change q16 ∈ dagState.memory.producers at q16Member
  obtain ⟨key, base, workSeen, anchorExact, baseExact⟩ :=
    producer_member_implies_tracks_some_base dagState.memory q16 dagInvariant
      q16Member
  have q16Valid : Q16DagProducerInventoryValid base
      dagState.memory.producers := dagInvariant.inventoryValid base baseExact
  apply alpha_q16_producer_digests_disjoint alphaState.memory.producers
    dagState.memory.producers base alphaInvariant.inventoryValid alphaBoundary
      q16Valid
  · intro candidate candidateMember dagProducer dagProducerMember digestEqual
    have candidateMemberRaw := candidateMember
    change candidate ∈
      (AspisK1.V7Tag73IndexedControllerTraceAlignment.indexedStateAfterRecords
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        (Slot := Fin 4) (Memory := AlphaZeroControllerMemory)
        transitionFuel
        (alphaZeroCausalController
          (globalOracleCalls := globalFull256OracleCallCap parameters)
          transitionFuel boundaryIndex) prior
        (exactAlphaZeroInitialState input)).memory.producers at candidateMemberRaw
    obtain ⟨alphaActor, alphaRecord⟩ :=
      exact_alpha_prefix_producer_has_literal_record input boundaryIndex prior
        later decomposition candidate candidateMemberRaw
    have dagProducerMemberRaw := dagProducerMember
    change dagProducer ∈
      (AspisK1.V7Tag73IndexedControllerTraceAlignment.indexedStateAfterRecords
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        (Slot := FinalWorkQ16DigestSlot) (Memory := FinalWorkQ16DagMemory)
        transitionFuel
        (exactDagTrialController (parameters := parameters)
          transitionFuel trial) prior
        (exactDagCandidateInitialState input)).memory.producers at dagProducerMemberRaw
    obtain ⟨dagActor, dagRecord⟩ :=
      AspisK1.V7Tag73ExactDagProducerRecordProvenance.exact_dag_prefix_producer_has_literal_record
        (parameters := parameters) (transitionFuel := transitionFuel)
        input trial prior later decomposition dagProducer dagProducerMemberRaw
    have alphaRoot :
        (.machineFresh alphaActor candidate.sourceInput candidate.digest :
            UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root := by
      rw [decomposition, List.mem_append]
      exact Or.inl alphaRecord
    have dagRoot :
        (.machineFresh dagActor dagProducer.sourceInput dagProducer.digest :
            UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root := by
      rw [decomposition, List.mem_append]
      exact Or.inl dagRecord
    have recordExact :
        (.machineFresh alphaActor candidate.sourceInput candidate.digest :
            UnifiedExposureRecord) =
          (.machineFresh dagActor dagProducer.sourceInput dagProducer.digest :
            UnifiedExposureRecord) :=
      List.inj_on_of_nodup_map (exact_root_record_answers_nodup input)
        alphaRoot dagRoot digestEqual
    injection recordExact
  · exact alphaMember
  · exact q16Member

#print axioms exact_alpha_prefix_producer_has_literal_record
#print axioms exact_alpha_q16_prefix_producer_digests_disjoint

end

end AspisK1.V7Tag73ExactAlphaQ16InventoryDisjoint
