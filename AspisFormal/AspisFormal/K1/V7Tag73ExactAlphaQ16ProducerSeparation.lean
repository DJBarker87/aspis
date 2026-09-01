import AspisFormal.K1.V7Tag73ExactAlphaZeroRootOrder
import AspisFormal.K1.V7Tag73ExactDagProducerRecordProvenance
import AspisFormal.K1.V7Tag73IndexedAlignedRecordReplay

/-!
# Alpha-chain separation from causal-DAG q16 producers

The final-work/q16 router recognizes q16 output coordinates from remembered
producer digests.  This module proves that the consumed alpha-zero duplex
chain cannot collide with any such producer under the exact clean-root event.
The proof uses literal source-record provenance and root-answer uniqueness; it
does not assume SHA-256 injectivity and remains valid when the adversary first
queried either coordinate.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactAlphaQ16ProducerSeparation

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalDagProducerInvariant
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactAlphaZeroPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactDagProducerRecordProvenance
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SqueezeInputStateInjectivity
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- All state digests traversed by a duplex chain avoid the q16 producer
inventory.  The list is the initial digest followed by the advance answers. -/
def ChainStatesAvoidQ16Producers (producers : List Q16DagProducer)
    (digest : Digest256) (advances : List Digest256) : Prop :=
  ∀ state ∈ digest :: advances, ∀ producer ∈ producers,
    state ≠ producer.digest

/-- Equal clean-root answers identify their literal source inputs.  One side
is supplied as a table lookup and the other as an actor-tagged root record. -/
theorem clean_root_answer_eq_fixes_source_input
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
    (leftInput rightInput : ShaInput) (leftAnswer rightAnswer : Digest256)
    (leftLookup : tableLookup (exactOperationalTable input) leftInput =
      some leftAnswer)
    (rightActor : QueryActor)
    (rightMember :
      (.machineFresh rightActor rightInput rightAnswer :
          UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root)
    (answersEqual : leftAnswer = rightAnswer) :
    leftInput = rightInput := by
  obtain ⟨leftActor, leftMember⟩ :=
    exact_final_table_lookup_has_root_record input leftInput leftAnswer
      leftLookup
  have recordExact :
      (.machineFresh leftActor leftInput leftAnswer : UnifiedExposureRecord) =
        (.machineFresh rightActor rightInput rightAnswer :
          UnifiedExposureRecord) :=
    List.inj_on_of_nodup_map (exact_root_record_answers_nodup input)
      leftMember rightMember answersEqual
  injection recordExact

/-- An advance coordinate is shorter than every block-zero q16 candidate
coordinate, so the two literal grammars are disjoint. -/
theorem gamma_advance_input_ne_q16_candidate
    (state base : Digest256) (counter : Fin 64) :
    gammaAdvanceInput state ≠
      bytes base ++ [domAbsorb, queryCandidateLabel,
        UInt8.ofNat counter.val] := by
  intro equal
  have lengths := congrArg List.length equal
  simp [gammaAdvanceInput] at lengths

/-- A duplex output coordinate has 33 bytes, so it cannot be parsed as the
41-byte final-work coordinate. -/
theorem raw_final_work_key_of_gamma_output_input_none
    (state : Digest256) :
    rawFinalWorkKeyOfWorkInput? (gammaOutputInput state) = none := by
  simp [rawFinalWorkKeyOfWorkInput?, gammaOutputInput]

/-- An advance coordinate also has 33 bytes, so it cannot be parsed as the
41-byte final-work coordinate. -/
theorem raw_final_work_key_of_gamma_advance_input_none
    (state : Digest256) :
    rawFinalWorkKeyOfWorkInput? (gammaAdvanceInput state) = none := by
  simp [rawFinalWorkKeyOfWorkInput?, gammaAdvanceInput]

/-- If a duplex state avoids the current q16 producer inventory, its output
coordinate is residual for the deployed final-work/q16 controller.  The two
named cases are excluded independently: final work by exact input length and
q16 by literal producer provenance. -/
theorem dag_preferred_slot_none_of_gamma_state_avoids_producers
    (anchorIndex exposureIndex : Nat) (memory : FinalWorkQ16DagMemory)
    (state : Digest256)
    (wellFormed : Q16DagAnchorWellFormed memory.anchor)
    (avoids : ∀ producer ∈ memory.producers,
      state ≠ producer.digest) :
    dagPreferredSlotForInput anchorIndex exposureIndex memory
      (gammaOutputInput state) = none := by
  cases preferred : dagPreferredSlotForInput anchorIndex exposureIndex memory
      (gammaOutputInput state) with
  | none => rfl
  | some slot =>
      exfalso
      cases slot with
      | none =>
          have rawPreferred :
              dagRawPreferredSlot anchorIndex exposureIndex memory
                (gammaOutputInput state) = some none := by
            unfold dagPreferredSlotForInput at preferred
            cases raw : dagRawPreferredSlot anchorIndex exposureIndex memory
                (gammaOutputInput state) with
            | none => simp [raw] at preferred
            | some rawSlot =>
                by_cases used : rawSlot ∈ memory.usedSlots
                · simp [raw, used] at preferred
                · simp only [raw, used, if_false] at preferred
                  have slotExact : rawSlot = none := Option.some.inj preferred
                  simpa [slotExact] using raw
          cases anchorExact : memory.anchor with
          | inactive =>
              unfold dagRawPreferredSlot at rawPreferred
              rw [anchorExact] at rawPreferred
              by_cases atAnchor : exposureIndex = anchorIndex
              · simp [atAnchor,
                  raw_final_work_key_of_gamma_output_input_none] at rawPreferred
              · simp [atAnchor] at rawPreferred
          | tracked key workSeen =>
              have keyWellFormed :
                  key.digest.length = 32 ∧ key.nonce.length = 8 := by
                simpa [anchorExact, Q16DagAnchorWellFormed] using wellFormed
              unfold dagRawPreferredSlot at rawPreferred
              rw [anchorExact] at rawPreferred
              by_cases work :
                  workSeen = false ∧ gammaOutputInput state = key.workInput
              · have lengths := congrArg List.length work.2
                simp [gammaOutputInput, RawFinalWorkKey.workInput,
                  keyWellFormed.1, keyWellFormed.2] at lengths
              · simp [work] at rawPreferred
      | some q16Slot =>
          obtain ⟨producer, producerMember, inputExact, _slotExact⟩ :=
            dag_preferred_q16_slot_has_producer anchorIndex exposureIndex
              memory (gammaOutputInput state) q16Slot preferred
          exact (avoids producer producerMember)
            (output_input_eq_implies_state_eq state producer.digest inputExact)

/-- Every duplex advance coordinate is residual for the deployed router.
Unlike an output half, no producer-inventory premise is needed: q16 outputs
use the globally disjoint squeeze-output tag, while final work has a different
fixed width. -/
theorem dag_preferred_slot_none_of_gamma_advance
    (anchorIndex exposureIndex : Nat) (memory : FinalWorkQ16DagMemory)
    (state : Digest256)
    (wellFormed : Q16DagAnchorWellFormed memory.anchor) :
    dagPreferredSlotForInput anchorIndex exposureIndex memory
      (gammaAdvanceInput state) = none := by
  cases preferred : dagPreferredSlotForInput anchorIndex exposureIndex memory
      (gammaAdvanceInput state) with
  | none => rfl
  | some slot =>
      exfalso
      cases slot with
      | none =>
          have rawPreferred :
              dagRawPreferredSlot anchorIndex exposureIndex memory
                (gammaAdvanceInput state) = some none := by
            unfold dagPreferredSlotForInput at preferred
            cases raw : dagRawPreferredSlot anchorIndex exposureIndex memory
                (gammaAdvanceInput state) with
            | none => simp [raw] at preferred
            | some rawSlot =>
                by_cases used : rawSlot ∈ memory.usedSlots
                · simp [raw, used] at preferred
                · simp only [raw, used, if_false] at preferred
                  have slotExact : rawSlot = none := Option.some.inj preferred
                  simpa [slotExact] using raw
          cases anchorExact : memory.anchor with
          | inactive =>
              unfold dagRawPreferredSlot at rawPreferred
              rw [anchorExact] at rawPreferred
              by_cases atAnchor : exposureIndex = anchorIndex
              · simp [atAnchor,
                  raw_final_work_key_of_gamma_advance_input_none] at rawPreferred
              · simp [atAnchor] at rawPreferred
          | tracked key workSeen =>
              have keyWellFormed :
                  key.digest.length = 32 ∧ key.nonce.length = 8 := by
                simpa [anchorExact, Q16DagAnchorWellFormed] using wellFormed
              unfold dagRawPreferredSlot at rawPreferred
              rw [anchorExact] at rawPreferred
              by_cases work :
                  workSeen = false ∧ gammaAdvanceInput state = key.workInput
              · have lengths := congrArg List.length work.2
                simp [gammaAdvanceInput, RawFinalWorkKey.workInput,
                  keyWellFormed.1, keyWellFormed.2] at lengths
              · simp [work] at rawPreferred
      | some q16Slot =>
          obtain ⟨producer, _producerMember, inputExact, _slotExact⟩ :=
            dag_preferred_q16_slot_has_producer anchorIndex exposureIndex
              memory (gammaAdvanceInput state) q16Slot preferred
          exact advance_input_ne_output_input state producer.digest inputExact

/-- The fold-nonce alpha boundary has 43 bytes, while q16 candidate and
advance producer coordinates have 35 and 33 bytes respectively. -/
theorem alpha_zero_boundary_avoids_q16_producer_sources
    (messages : Messages) (producerState base : Digest256)
    (producers : List Q16DagProducer)
    (inventory : Q16DagProducerInventoryValid base producers) :
    ∀ producer ∈ producers,
      bytes producerState ++
          [domAbsorb, (alphaZeroBoundaryPayload messages).label] ++
          (alphaZeroBoundaryPayload messages).data ≠ producer.sourceInput := by
  intro producer producerMember equal
  rcases inventory producer producerMember with candidate | advanced
  · rw [candidate.2] at equal
    have lengths := congrArg List.length equal
    simp [alphaZeroBoundaryPayload, Payload.data] at lengths
  · obtain ⟨parent, _parentMember, _counterExact, _blockExact,
      sourceExact⟩ := advanced
    rw [sourceExact] at equal
    have lengths := congrArg List.length equal
    simp [alphaZeroBoundaryPayload, Payload.data, gammaAdvanceInput] at lengths

/-- Source separation at the first block propagates through every alpha
advance.  If a later alpha advance equalled a q16 producer source, recursive
producer provenance would force the preceding alpha state to equal the
producer's parent digest, contradicting the induction hypothesis. -/
theorem exact_root_ordered_chain_avoids_q16_producers
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
    (base : Digest256) (producers : List Q16DagProducer)
    (inventory : Q16DagProducerInventoryValid base producers)
    (provenance : ∀ producer ∈ producers,
      ∃ actor,
        (.machineFresh actor producer.sourceInput producer.digest :
            UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root)
    {producerInput : ShaInput} {digest : Digest256}
    {outputs advances : List Digest256}
    (chain : ExactRootOrderedQ16Chain input producerInput digest outputs
      advances)
    (sourceSeparated : ∀ producer ∈ producers,
      producerInput ≠ producer.sourceInput) :
    ChainStatesAvoidQ16Producers producers digest advances := by
  induction chain with
  | done producerInput digest producerFound =>
      intro state stateMember producer producerMember
      have stateExact : state = digest := by simpa using stateMember
      subst state
      intro answersEqual
      obtain ⟨actor, producerRecord⟩ := provenance producer producerMember
      have sourceExact := clean_root_answer_eq_fixes_source_input input
        producerInput producer.sourceInput digest producer.digest producerFound
        actor producerRecord answersEqual
      exact sourceSeparated producer producerMember sourceExact
  | @next producerInput digest output advanced outputs advances producerFound
      outputFound advanceFound producerBeforeOutput producerBeforeAdvance tail
      ih =>
      have currentAvoid : ∀ producer ∈ producers,
          digest ≠ producer.digest := by
        intro producer producerMember answersEqual
        obtain ⟨actor, producerRecord⟩ := provenance producer producerMember
        have sourceExact := clean_root_answer_eq_fixes_source_input input
          producerInput producer.sourceInput digest producer.digest
          producerFound actor producerRecord answersEqual
        exact sourceSeparated producer producerMember sourceExact
      have nextSourceSeparated : ∀ producer ∈ producers,
          gammaAdvanceInput digest ≠ producer.sourceInput := by
        intro producer producerMember
        rcases inventory producer producerMember with candidate | nextProducer
        · rw [candidate.2]
          exact gamma_advance_input_ne_q16_candidate digest base producer.slot.1
        · obtain ⟨parent, parentMember, _counterExact, _blockExact,
            sourceExact⟩ := nextProducer
          rw [sourceExact]
          intro inputsEqual
          exact currentAvoid parent parentMember
            (advance_input_eq_implies_state_eq digest parent.digest inputsEqual)
      have tailAvoid := ih nextSourceSeparated
      intro state stateMember producer producerMember
      simp only [List.mem_cons] at stateMember
      rcases stateMember with current | later
      · exact current ▸ currentAvoid producer producerMember
      · exact tailAvoid state (by
          simpa only [List.mem_cons] using later) producer producerMember

/-- The abstract separation theorem instantiated with the complete accepted
root replay.  No assumption about which actor first exposed an alpha or q16
coordinate remains: literal record provenance covers both actors. -/
theorem exact_alpha_chain_avoids_full_dag_producers
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
    {producerInput : ShaInput} {digest : Digest256}
    {outputs advances : List Digest256}
    (chain : ExactRootOrderedQ16Chain input producerInput digest outputs
      advances)
    (boundary : ∃ (producerDigest : Digest256),
      producerInput =
        bytes producerDigest ++
          [domAbsorb,
            (alphaZeroBoundaryPayload
              (exactOperationalTape input).messages).label] ++
          (alphaZeroBoundaryPayload
            (exactOperationalTape input).messages).data) :
    ChainStatesAvoidQ16Producers
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial)
        (exactFixedRootRecords input.package.root)
        (exactDagCandidateInitialState input)).memory.producers
      digest advances := by
  let reached := indexedStateAfterRecords transitionFuel
    (exactDagTrialController transitionFuel trial)
    (exactFixedRootRecords input.package.root)
    (exactDagCandidateInitialState input)
  have invariant : Q16DagMemoryProducerInvariant reached.memory := by
    simpa [reached] using exact_dag_candidate_root_producer_invariant input trial
  cases baseExact : reached.memory.q16Base with
  | none =>
      have empty := invariant.noBaseHasNoProducers baseExact
      simp [reached, empty, ChainStatesAvoidQ16Producers]
  | some base =>
      obtain ⟨producerDigest, producerInputExact⟩ := boundary
      have inventory : Q16DagProducerInventoryValid base
          reached.memory.producers :=
        invariant.inventoryValid base baseExact
      have provenance : ∀ producer ∈ reached.memory.producers,
          ∃ actor,
            (.machineFresh actor producer.sourceInput producer.digest :
                UnifiedExposureRecord) ∈
              exactFixedRootRecords input.package.root := by
        intro producer producerMember
        apply exact_dag_prefix_producer_has_literal_record input trial
          (exactFixedRootRecords input.package.root) [] (by simp) producer
        simpa [reached] using producerMember
      apply exact_root_ordered_chain_avoids_q16_producers input base
        reached.memory.producers inventory provenance chain
      intro producer producerMember
      rw [producerInputExact]
      exact alpha_zero_boundary_avoids_q16_producer_sources
        (exactOperationalTape input).messages producerDigest base
        reached.memory.producers inventory producer producerMember

/-- Every consumed alpha output is residual at its literal pre-answer root
prefix.  The important point is temporal: the proof restricts the avoidance
result for the complete producer inventory to the monotone inventory already
installed when this exact alpha coordinate was first exposed.  It therefore
does not classify the coordinate retrospectively and is independent of which
actor made the first query. -/
theorem exact_alpha_output_is_residual_at_literal_root_prefix
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
    {producerInput : ShaInput} {digest : Digest256}
    {outputs advances : List Digest256}
    (chain : ExactRootOrderedQ16Chain input producerInput digest outputs
      advances)
    (boundary : ∃ (producerDigest : Digest256),
      producerInput =
        bytes producerDigest ++
          [domAbsorb,
            (alphaZeroBoundaryPayload
              (exactOperationalTape input).messages).label] ++
          (alphaZeroBoundaryPayload
            (exactOperationalTape input).messages).data)
    (state : Digest256)
    (stateMember : state ∈ digest :: advances)
    (output : Digest256) (actor : QueryActor)
    (prior later : List UnifiedExposureRecord)
    (decomposition : exactFixedRootRecords input.package.root =
      prior ++
        (.machineFresh actor (gammaOutputInput state) output :
          UnifiedExposureRecord) :: later) :
    (exactDagTrialController transitionFuel trial).preferredSlot
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial) prior
        (exactDagCandidateInitialState input)) = none := by
  let controller := exactDagTrialController transitionFuel trial
  let initial := exactDagCandidateInitialState input
  let reached := indexedStateAfterRecords transitionFuel controller prior initial
  let completed := indexedStateAfterRecords transitionFuel controller
    (exactFixedRootRecords input.package.root) initial
  have fullAvoid := exact_alpha_chain_avoids_full_dag_producers input trial
    chain boundary state stateMember
  have producerGrowth : reached.memory.producers <+:
      completed.memory.producers := by
    have growth := dag_indexed_state_producers_prefix transitionFuel trial.val
      ((.machineFresh actor (gammaOutputInput state) output :
          UnifiedExposureRecord) :: later) reached
    have growth' : reached.memory.producers <+:
        (indexedStateAfterRecords transitionFuel controller
          ((.machineFresh actor (gammaOutputInput state) output :
            UnifiedExposureRecord) :: later) reached).memory.producers := by
      simpa [controller, exactDagTrialController] using growth
    have completedExact : completed =
        indexedStateAfterRecords transitionFuel controller
          ((.machineFresh actor (gammaOutputInput state) output :
            UnifiedExposureRecord) :: later) reached := by
      simp [completed, decomposition, reached,
        indexed_state_after_records_append]
    rw [completedExact]
    exact growth'
  have prefixAvoid : ∀ producer ∈ reached.memory.producers,
      state ≠ producer.digest := by
    intro producer producerMember
    exact fullAvoid producer (producerGrowth.subset producerMember)
  have anchorWellFormed : Q16DagAnchorWellFormed reached.memory.anchor := by
    simpa [reached, controller, initial] using
      exact_dag_candidate_prefix_anchor_well_formed input trial prior
  have inputExact : unifiedInputBeforeAnswer? transitionFuel reached.cursor =
      some (gammaOutputInput state) := by
    have aligned : unifiedRecordAtAnswer transitionFuel reached.cursor output =
        .machineFresh actor (gammaOutputInput state) output := by
      have rootAligned := exact_root_records_aligned_for_dag_controller input
        trial.val prior
          (.machineFresh actor (gammaOutputInput state) output)
          later decomposition
      simpa [reached, controller, initial, exactDagTrialController,
        UnifiedExposureRecord.answer] using rootAligned
    exact aligned_machine_record_has_exact_input transitionFuel reached.cursor
      actor (gammaOutputInput state) output aligned
  change dagCandidatePreferredSlot transitionFuel trial.val reached = none
  unfold dagCandidatePreferredSlot
  rw [inputExact]
  exact dag_preferred_slot_none_of_gamma_state_avoids_producers
    trial.val reached.exposureIndex reached.memory state anchorWellFormed
      prefixAvoid

/-- Every consumed alpha advance is likewise residual at its literal
pre-answer root prefix.  This half is unconditional because the advance tag
is disjoint from the q16-output tag. -/
theorem exact_alpha_advance_is_residual_at_literal_root_prefix
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
    (state advanced : Digest256) (actor : QueryActor)
    (prior later : List UnifiedExposureRecord)
    (decomposition : exactFixedRootRecords input.package.root =
      prior ++
        (.machineFresh actor (gammaAdvanceInput state) advanced :
          UnifiedExposureRecord) :: later) :
    (exactDagTrialController transitionFuel trial).preferredSlot
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial) prior
        (exactDagCandidateInitialState input)) = none := by
  let controller := exactDagTrialController transitionFuel trial
  let initial := exactDagCandidateInitialState input
  let reached := indexedStateAfterRecords transitionFuel controller prior initial
  have anchorWellFormed : Q16DagAnchorWellFormed reached.memory.anchor := by
    simpa [reached, controller, initial] using
      exact_dag_candidate_prefix_anchor_well_formed input trial prior
  have inputExact : unifiedInputBeforeAnswer? transitionFuel reached.cursor =
      some (gammaAdvanceInput state) := by
    have aligned : unifiedRecordAtAnswer transitionFuel reached.cursor advanced =
        .machineFresh actor (gammaAdvanceInput state) advanced := by
      have rootAligned := exact_root_records_aligned_for_dag_controller input
        trial.val prior
          (.machineFresh actor (gammaAdvanceInput state) advanced)
          later decomposition
      simpa [reached, controller, initial, exactDagTrialController,
        UnifiedExposureRecord.answer] using rootAligned
    exact aligned_machine_record_has_exact_input transitionFuel reached.cursor
      actor (gammaAdvanceInput state) advanced aligned
  change dagCandidatePreferredSlot transitionFuel trial.val reached = none
  unfold dagCandidatePreferredSlot
  rw [inputExact]
  exact dag_preferred_slot_none_of_gamma_advance trial.val
    reached.exposureIndex reached.memory state anchorWellFormed

#print axioms clean_root_answer_eq_fixes_source_input
#print axioms gamma_advance_input_ne_q16_candidate
#print axioms raw_final_work_key_of_gamma_output_input_none
#print axioms raw_final_work_key_of_gamma_advance_input_none
#print axioms dag_preferred_slot_none_of_gamma_state_avoids_producers
#print axioms dag_preferred_slot_none_of_gamma_advance
#print axioms alpha_zero_boundary_avoids_q16_producer_sources
#print axioms exact_root_ordered_chain_avoids_q16_producers
#print axioms exact_alpha_chain_avoids_full_dag_producers
#print axioms exact_alpha_output_is_residual_at_literal_root_prefix
#print axioms exact_alpha_advance_is_residual_at_literal_root_prefix

end

end AspisK1.V7Tag73ExactAlphaQ16ProducerSeparation
