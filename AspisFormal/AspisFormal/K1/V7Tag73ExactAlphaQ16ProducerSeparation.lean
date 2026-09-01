import AspisFormal.K1.V7Tag73ExactAlphaZeroRootOrder
import AspisFormal.K1.V7Tag73ExactDagProducerRecordProvenance

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
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerNativeGammaReplay
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

#print axioms clean_root_answer_eq_fixes_source_input
#print axioms gamma_advance_input_ne_q16_candidate
#print axioms alpha_zero_boundary_avoids_q16_producer_sources
#print axioms exact_root_ordered_chain_avoids_q16_producers
#print axioms exact_alpha_chain_avoids_full_dag_producers

end

end AspisK1.V7Tag73ExactAlphaQ16ProducerSeparation
