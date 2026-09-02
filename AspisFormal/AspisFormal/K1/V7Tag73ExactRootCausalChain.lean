import AspisFormal.K1.V7Tag73ExactAdversaryAnchorPrefinalChronology
import AspisFormal.K1.V7Tag73ExactCompilerGammaPrefixCoordinates
import AspisFormal.K1.V7Tag73ExactDagCandidateLabeledRootRouting
import AspisFormal.K1.V7Tag73ExactFinal256DigestRootOrigin
import AspisFormal.K1.V7Tag73ExactQ16CausalCoordinateOrder
import AspisFormal.K1.V7Tag73ExactRootLookupCausalOrder
import AspisFormal.K1.V7Tag73ExactRootRecordOrderLift
import AspisFormal.K1.V7Tag73SqueezeInputStateInjectivity

/-!
# Generic reverse closure for retained causal digest chains

This module factors the common argument used when two accepted Tag-73 fork
fibres retain the same first-creation record prefix.  Starting at a typed
absorption boundary, every later state-changing oracle input literally begins
with the preceding transcript digest.  If the terminal answers agree and the
retained answers are unique, the chains can be walked backwards without any
SHA-256 injectivity assumption.

The only grammar premise is cross-chain boundary separation.  It rules out
one chain reaching its typed boundary while the other still points at a later
state-changing input.  For the K1.3 application the boundary is the C2-root
absorption, whose label/length is disjoint from every later transition.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactRootCausalChain

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactAdversaryAnchorPrefinalChronology
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerFinalWorkTraceOccurrence
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFinal256DigestRootOrigin
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactRootRecordOrderLift
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SqueezeInputStateInjectivity
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- A retained causal chain of transcript-state answers.  The boundary record
produces the initial state.  Every later record has an input whose first 32
bytes are exactly the preceding state digest. -/
inductive ExactRetainedDigestChain
    (prior : List UnifiedExposureRecord) (boundaryInput : ShaInput)
    (allowedInput : ShaInput → Prop) :
    Digest256 → Digest256 → Prop
  | boundary (initial : Digest256) (actor : QueryActor)
      (member : (.machineFresh actor boundaryInput initial :
        UnifiedExposureRecord) ∈ prior) :
      ExactRetainedDigestChain prior boundaryInput allowedInput initial initial
  | step (initial current next : Digest256) (input : ShaInput)
      (actor : QueryActor)
      (chain : ExactRetainedDigestChain prior boundaryInput allowedInput initial
        current)
      (causalPrefix : HasLiteralStatePrefix current input)
      (allowed : allowedInput input)
      (member : (.machineFresh actor input next : UnifiedExposureRecord) ∈
        prior) :
      ExactRetainedDigestChain prior boundaryInput allowedInput initial next

/-- The lookup-only form of a causal digest chain.  It is extracted directly
from a successful evaluator run before chronology is used to retain every
record inside a selected pre-anchor prefix. -/
inductive ExactLookupDigestChain
    (table : FixedOracleTable) (boundaryInput : ShaInput)
    (allowedInput : ShaInput → Prop) : Digest256 → Digest256 → Prop
  | boundary (initial : Digest256)
      (lookup : tableLookup table boundaryInput = some initial) :
      ExactLookupDigestChain table boundaryInput allowedInput initial initial
  | step (initial current next : Digest256) (input : ShaInput)
      (chain : ExactLookupDigestChain table boundaryInput allowedInput initial
        current)
      (causalPrefix : HasLiteralStatePrefix current input)
      (allowed : allowedInput input)
      (lookup : tableLookup table input = some next) :
      ExactLookupDigestChain table boundaryInput allowedInput initial next

theorem exact_lookup_digest_chain_terminal_lookup
    {table : FixedOracleTable} {boundaryInput : ShaInput}
    {allowedInput : ShaInput → Prop} {initial terminal : Digest256}
    (chain : ExactLookupDigestChain table boundaryInput allowedInput initial
      terminal) :
    ∃ input, tableLookup table input = some terminal := by
  cases chain with
  | boundary lookup => exact ⟨boundaryInput, lookup⟩
  | step current next input previous causalPrefix allowed lookup =>
      exact ⟨input, lookup⟩

/-- State-changing inputs permitted after an absorption boundary with the
given forbidden label.  Duplex advances have their fixed shape; later
absorptions must use a different label. -/
def IsPostRootStateInput (forbiddenLabel : UInt8) (input : ShaInput) : Prop :=
  (∃ state : Digest256, input = gammaAdvanceInput state) ∨
    ∃ (state : Digest256)
        (payload : AspisK1.V7Tag73TranscriptSchedule.Payload),
      payload.label ≠ forbiddenLabel ∧
      input = bytes state ++ [domAbsorb, payload.label] ++ payload.data

/-- Event-local grammar condition used while extracting a post-root chain. -/
def IsPostRootMachineEvent (forbiddenLabel : UInt8) : MachineEvent → Prop
  | .absorb payload => payload.label ≠ forbiddenLabel
  | .challenge _ _ | .grind _ _ | .check _ => True

abbrev IsPostC2StateInput := IsPostRootStateInput c2RootLabel
abbrev IsPostC2MachineEvent := IsPostRootMachineEvent c2RootLabel
abbrev IsPostC1StateInput := IsPostRootStateInput c1RootLabel
abbrev IsPostC1MachineEvent := IsPostRootMachineEvent c1RootLabel

theorem prefix_after_c2_before_final256_is_post_c2
    (messages : Messages) :
    ∀ event, event ∈ prefixAfterC2BeforeFinal256 messages →
      IsPostC2MachineEvent event := by
  simp [prefixAfterC2BeforeFinal256, semanticEvents, oodEvents,
    IsPostC2MachineEvent, IsPostRootMachineEvent, challengeEvent,
    AspisK1.V7Tag73TranscriptSchedule.Payload.label, c2RootLabel,
    constraintRegistryLabel, helperSumLabel, initialMaskClaimLabel,
    semanticRoundLabel, pointClaimsLabel, batchWorkNonceLabel,
    inactiveClaimLabel, circleOodValueLabel, relationRoundLabel,
    foldWorkNonceLabel]

theorem prefix_after_c2_before_final256_is_post_c1
    (messages : Messages) :
    ∀ event, event ∈ prefixAfterC2BeforeFinal256 messages →
      IsPostC1MachineEvent event := by
  simp [prefixAfterC2BeforeFinal256, semanticEvents, oodEvents,
    IsPostC1MachineEvent, IsPostRootMachineEvent, challengeEvent,
    AspisK1.V7Tag73TranscriptSchedule.Payload.label, c1RootLabel,
    constraintRegistryLabel, helperSumLabel, initialMaskClaimLabel,
    semanticRoundLabel, pointClaimsLabel, batchWorkNonceLabel,
    inactiveClaimLabel, circleOodValueLabel, relationRoundLabel,
    foldWorkNonceLabel]

theorem absorb_input_avoids_post_root_state_input
    (forbiddenLabel : UInt8) (before : Digest256)
    (boundaryData : ByteString) (boundaryNonempty : boundaryData ≠ []) :
    ∀ input, IsPostRootStateInput forbiddenLabel input →
      bytes before ++ [domAbsorb, forbiddenLabel] ++ boundaryData ≠ input := by
  intro input allowed equal
  rcases allowed with ⟨state, inputExact⟩ |
      ⟨state, payload, labelNe, inputExact⟩
  · rw [inputExact] at equal
    have lengths := congrArg List.length equal
    simp [gammaAdvanceInput] at lengths
    have emptyLength : boundaryData.length = 0 := by omega
    exact boundaryNonempty (List.length_eq_zero_iff.mp emptyLength)
  · rw [inputExact] at equal
    have leftDrop :
        (bytes before ++ [domAbsorb, forbiddenLabel] ++ boundaryData).drop 33 =
          forbiddenLabel :: boundaryData := by
      convert List.drop_append_length
        (l₁ := bytes before ++ [domAbsorb])
        (l₂ := forbiddenLabel :: boundaryData) using 1 <;> simp
    have rightDrop :
        (bytes state ++ [domAbsorb, payload.label] ++ payload.data).drop 33 =
          payload.label :: payload.data := by
      convert List.drop_append_length
        (l₁ := bytes state ++ [domAbsorb])
        (l₂ := payload.label :: payload.data) using 1 <;> simp
    have dropped := congrArg (List.drop 33) equal
    rw [leftDrop, rightDrop] at dropped
    exact labelNe (List.cons.inj dropped).1.symm

theorem c2_absorb_input_avoids_post_c2_state_input
    (before salt : Digest256) (root : Digest208) :
    ∀ input, IsPostC2StateInput input →
      bytes before ++ [domAbsorb, c2RootLabel] ++
          (AspisK1.V7Tag73TranscriptSchedule.Payload.c2Root root salt).data ≠
        input :=
  absorb_input_avoids_post_root_state_input c2RootLabel before
    (AspisK1.V7Tag73TranscriptSchedule.Payload.c2Root root salt).data (by
      intro empty
      have lengths := congrArg List.length empty
      simp [AspisK1.V7Tag73TranscriptSchedule.Payload.data] at lengths)

/-- Append all state-changing advance halves of one ordered duplex chain to
an existing lookup chain.  Output halves do not change the transcript state
and therefore do not appear in this state chain. -/
theorem exact_lookup_digest_chain_append_ordered_q16
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {forbiddenLabel : UInt8} {boundaryInput : ShaInput}
    {initial digest : Digest256}
    (prefixChain : ExactLookupDigestChain (exactOperationalTable input)
      boundaryInput (IsPostRootStateInput forbiddenLabel) initial digest)
    {producerInput : ShaInput} {outputs advances : List Digest256}
    (ordered : ExactRootOrderedQ16Chain input producerInput digest outputs
      advances) :
    ExactLookupDigestChain (exactOperationalTable input) boundaryInput
      (IsPostRootStateInput forbiddenLabel) initial
        (gammaTerminalDigest digest advances) := by
  induction ordered generalizing initial with
  | done producerInput digest producerFound =>
      simpa [gammaTerminalDigest] using prefixChain
  | @next producerInput digest output advanced outputs advances producerFound
      outputFound advanceFound producerBeforeOutput producerBeforeAdvance tail
      ih =>
      have causalPrefix : HasLiteralStatePrefix digest
          (gammaAdvanceInput digest) := by
        simp [HasLiteralStatePrefix, gammaAdvanceInput]
      have allowed : IsPostRootStateInput forbiddenLabel
          (gammaAdvanceInput digest) := by
        exact Or.inl ⟨digest, rfl⟩
      have advancedPrefix : ExactLookupDigestChain
          (exactOperationalTable input) boundaryInput
          (IsPostRootStateInput forbiddenLabel) initial advanced :=
        .step initial digest advanced (gammaAdvanceInput digest) prefixChain
          causalPrefix allowed advanceFound
      simpa [gammaTerminalDigest] using ih advancedPrefix

/-- Extend a post-C2 lookup chain across one successful machine event. -/
theorem exact_lookup_digest_chain_through_machine_event
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    {forbiddenLabel : UInt8} {boundaryInput : ShaInput}
    {initial : Digest256}
    (state next : EvalState) (event : MachineEvent)
    (chain : ExactLookupDigestChain (exactOperationalTable input)
      boundaryInput (IsPostRootStateInput forbiddenLabel) initial state.digest)
    (allowedEvent : IsPostRootMachineEvent forbiddenLabel event)
    (run : runMachineEvent (exactOperationalTable input) state event =
      some next) :
    ExactLookupDigestChain (exactOperationalTable input) boundaryInput
      (IsPostRootStateInput forbiddenLabel) initial next.digest := by
  cases event with
  | absorb payload =>
      let absorbInput :=
        bytes state.digest ++ [domAbsorb, payload.label] ++ payload.data
      have lookup : tableLookup (exactOperationalTable input) absorbInput =
          some next.digest := by
        simpa [absorbInput] using absorb_step_exposes_literal_lookup
          (exactOperationalTable input) state next payload run
      have causalPrefix : HasLiteralStatePrefix state.digest absorbInput := by
        simp [HasLiteralStatePrefix, absorbInput]
      have allowed : IsPostRootStateInput forbiddenLabel absorbInput := by
        unfold IsPostRootMachineEvent at allowedEvent
        exact Or.inr ⟨state.digest, payload, allowedEvent, rfl⟩
      exact .step initial state.digest next.digest absorbInput chain causalPrefix
        allowed lookup
  | challenge id use =>
      rw [runMachineEvent] at run
      obtain ⟨samplePair, squeezeRun, result⟩ :=
        Option.bind_eq_some_iff.mp run
      rcases samplePair with ⟨outputs, sampled⟩
      have nextExact :
          { sampled with
              samples := sampled.samples ++ [{ id := id, blocks := outputs }] } =
            next := by
        simpa only [pure, Option.some.injEq] using result
      subst next
      obtain ⟨advances, _advancesLength, coordinates, terminalExact,
          _callsExact⟩ :=
        squeeze_many_coordinates_with_terminal (exactOperationalTable input)
          (.challenge id) use.blocksUsed state sampled outputs squeezeRun
      obtain ⟨producerInput, producerLookup⟩ :=
        exact_lookup_digest_chain_terminal_lookup chain
      have ordered := gamma_table_coordinate_chain_has_exact_root_order
        transitionRoom input producerInput state.digest producerLookup
          coordinates
      have appended := exact_lookup_digest_chain_append_ordered_q16 chain
        ordered
      simpa [terminalExact] using appended
  | grind stage choice =>
      have digestExact := grinding_choice_does_not_advance
        (exactOperationalTable input) state next stage choice run
      simpa [digestExact] using chain
  | check checkpoint =>
      have nextExact : next = state := by
        simpa [runMachineEvent] using (Option.some.inj run).symm
      subst next
      exact chain

/-- Iterate the event-local extraction over a successful post-C2 event list. -/
theorem exact_lookup_digest_chain_through_machine_events
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    {forbiddenLabel : UInt8} {boundaryInput : ShaInput}
    {initial : Digest256}
    (events : List MachineEvent) (state final : EvalState)
    (chain : ExactLookupDigestChain (exactOperationalTable input)
      boundaryInput (IsPostRootStateInput forbiddenLabel) initial state.digest)
    (allowedEvents : ∀ event, event ∈ events →
      IsPostRootMachineEvent forbiddenLabel event)
    (run : runMachineEvents (exactOperationalTable input) events state =
      some final) :
    ExactLookupDigestChain (exactOperationalTable input) boundaryInput
      (IsPostRootStateInput forbiddenLabel) initial final.digest := by
  induction events generalizing state with
  | nil =>
      have finalExact : final = state := by
        simpa [runMachineEvents] using (Option.some.inj run).symm
      subst final
      exact chain
  | cons event rest ih =>
      rw [runMachineEvents] at run
      obtain ⟨next, eventRun, restRun⟩ := Option.bind_eq_some_iff.mp run
      have eventAllowed : IsPostRootMachineEvent forbiddenLabel event :=
        allowedEvents event (by simp)
      have nextChain := exact_lookup_digest_chain_through_machine_event
        transitionRoom input state next event chain eventAllowed eventRun
      apply ih next nextChain
      · intro later laterMember
        exact allowedEvents later (by simp [laterMember])
      · exact restRun

private theorem mem_prefix_of_strict_record_order
    {Record : Type} [DecidableEq Record]
    (records prior anchorLater before middle after : List Record)
    (first second anchorRecord : Record)
    (recordsNodup : records.Nodup)
    (anchorExact : records = prior ++ anchorRecord :: anchorLater)
    (orderedExact : records =
      before ++ first :: middle ++ second :: after)
    (secondMember : second ∈ prior) :
    first ∈ prior := by
  obtain ⟨insideBefore, insideAfter, priorExact⟩ :=
    (List.mem_iff_append).mp secondMember
  have secondPivotExact : records =
      insideBefore ++ second :: (insideAfter ++ anchorRecord :: anchorLater) := by
    rw [anchorExact, priorExact]
    simp only [List.cons_append, List.append_assoc]
  have orderedExact' : records =
      (before ++ first :: middle) ++ second :: after := by
    simpa only [List.cons_append, List.append_assoc] using orderedExact
  have prefixExact : insideBefore = before ++ first :: middle :=
    nodup_equal_pivot_prefixes second insideBefore
      (insideAfter ++ anchorRecord :: anchorLater)
      (before ++ first :: middle) after
      (by simpa only [← secondPivotExact] using recordsNodup)
      (secondPivotExact.symm.trans orderedExact')
  rw [priorExact, prefixExact]
  simp

private theorem equal_answer_root_records
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
    {leftActor rightActor : QueryActor} {leftInput rightInput : ShaInput}
    {answer : Digest256}
    (leftMember :
      (.machineFresh leftActor leftInput answer : UnifiedExposureRecord) ∈
        exactFixedRootRecords input.package.root)
    (rightMember :
      (.machineFresh rightActor rightInput answer : UnifiedExposureRecord) ∈
        exactFixedRootRecords input.package.root) :
    (.machineFresh leftActor leftInput answer : UnifiedExposureRecord) =
      .machineFresh rightActor rightInput answer := by
  exact List.inj_on_of_nodup_map (exact_root_record_answers_nodup input)
    leftMember rightMember rfl

/-- A lookup-only causal chain whose terminal answer feeds a retained consumer
can be moved wholesale into that consumer's canonical pre-anchor prefix. -/
theorem exact_lookup_digest_chain_retained_before_consumer
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (prior anchorLater : List UnifiedExposureRecord)
    (anchorRecord : UnifiedExposureRecord)
    (anchorExact : exactFixedRootRecords input.package.root =
      prior ++ anchorRecord :: anchorLater)
    {boundaryInput : ShaInput} {allowedInput : ShaInput → Prop}
    {initial terminal : Digest256}
    (chain : ExactLookupDigestChain (exactOperationalTable input)
      boundaryInput allowedInput initial terminal)
    (consumerInput : ShaInput) (consumerAnswer : Digest256)
    (consumerActor : QueryActor)
    (consumerLookup : tableLookup (exactOperationalTable input) consumerInput =
      some consumerAnswer)
    (consumerMember :
      (.machineFresh consumerActor consumerInput consumerAnswer :
        UnifiedExposureRecord) ∈ prior)
    (terminalPrefix : HasLiteralStatePrefix terminal consumerInput) :
    ExactRetainedDigestChain prior boundaryInput allowedInput initial
      terminal := by
  classical
  induction chain generalizing consumerInput consumerAnswer consumerActor with
  | boundary boundaryLookup =>
      obtain ⟨before, middle, after, pairOrder⟩ :=
        exact_compiler_literal_dependency_has_strict_root_order transitionRoom
          input boundaryInput consumerInput initial consumerAnswer
          boundaryLookup consumerLookup terminalPrefix
      obtain ⟨beforeRecords, middleRecords, afterRecords, boundaryActor,
          orderedConsumerActor, recordOrder⟩ :=
        exact_root_pair_order_lifts_to_records input boundaryInput
          consumerInput initial consumerAnswer before middle after pairOrder
      have orderedConsumerRootMember :
          (.machineFresh orderedConsumerActor consumerInput consumerAnswer :
            UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root := by
        rw [recordOrder]
        simp
      have consumerRootMember :
          (.machineFresh consumerActor consumerInput consumerAnswer :
            UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root := by
        rw [anchorExact]
        exact List.mem_append_left _ consumerMember
      have consumerRecordExact := equal_answer_root_records input
        orderedConsumerRootMember consumerRootMember
      have orderedConsumerMember :
          (.machineFresh orderedConsumerActor consumerInput consumerAnswer :
            UnifiedExposureRecord) ∈ prior := by
        simpa [consumerRecordExact] using consumerMember
      have rootNodup : (exactFixedRootRecords input.package.root).Nodup :=
        List.Nodup.of_map UnifiedExposureRecord.answer
          (exact_root_record_answers_nodup input)
      have boundaryMember := mem_prefix_of_strict_record_order
        (exactFixedRootRecords input.package.root) prior anchorLater
        beforeRecords middleRecords afterRecords
        (.machineFresh boundaryActor boundaryInput initial)
        (.machineFresh orderedConsumerActor consumerInput consumerAnswer)
        anchorRecord rootNodup anchorExact recordOrder orderedConsumerMember
      exact .boundary initial boundaryActor boundaryMember
  | step current next stepInput previous causalPrefix allowed
      stepLookup ih =>
      obtain ⟨before, middle, after, pairOrder⟩ :=
        exact_compiler_literal_dependency_has_strict_root_order transitionRoom
          input stepInput consumerInput next consumerAnswer stepLookup
          consumerLookup terminalPrefix
      obtain ⟨beforeRecords, middleRecords, afterRecords, stepActor,
          orderedConsumerActor, recordOrder⟩ :=
        exact_root_pair_order_lifts_to_records input stepInput consumerInput
          next consumerAnswer before middle after pairOrder
      have orderedConsumerRootMember :
          (.machineFresh orderedConsumerActor consumerInput consumerAnswer :
            UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root := by
        rw [recordOrder]
        simp
      have consumerRootMember :
          (.machineFresh consumerActor consumerInput consumerAnswer :
            UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root := by
        rw [anchorExact]
        exact List.mem_append_left _ consumerMember
      have consumerRecordExact := equal_answer_root_records input
        orderedConsumerRootMember consumerRootMember
      have orderedConsumerMember :
          (.machineFresh orderedConsumerActor consumerInput consumerAnswer :
            UnifiedExposureRecord) ∈ prior := by
        simpa [consumerRecordExact] using consumerMember
      have rootNodup : (exactFixedRootRecords input.package.root).Nodup :=
        List.Nodup.of_map UnifiedExposureRecord.answer
          (exact_root_record_answers_nodup input)
      have stepMember := mem_prefix_of_strict_record_order
        (exactFixedRootRecords input.package.root) prior anchorLater
        beforeRecords middleRecords afterRecords
        (.machineFresh stepActor stepInput next)
        (.machineFresh orderedConsumerActor consumerInput consumerAnswer)
        anchorRecord rootNodup anchorExact recordOrder orderedConsumerMember
      have retainedPrevious := ih stepInput next stepActor stepLookup stepMember
        causalPrefix
      exact .step initial current next stepInput stepActor retainedPrevious
        causalPrefix allowed stepMember

private theorem equal_answer_records_fix_input
    {prior : List UnifiedExposureRecord}
    (answersNodup : (prior.map UnifiedExposureRecord.answer).Nodup)
    {leftActor rightActor : QueryActor}
    {leftInput rightInput : ShaInput} {answer : Digest256}
    (leftMember :
      (.machineFresh leftActor leftInput answer : UnifiedExposureRecord) ∈
        prior)
    (rightMember :
      (.machineFresh rightActor rightInput answer : UnifiedExposureRecord) ∈
        prior) :
    leftInput = rightInput := by
  have recordExact :
      (.machineFresh leftActor leftInput answer : UnifiedExposureRecord) =
        .machineFresh rightActor rightInput answer := by
    apply List.inj_on_of_nodup_map answersNodup leftMember rightMember
    rfl
  injection recordExact

theorem literal_prefix_input_eq_fixes_digest
    {leftDigest rightDigest : Digest256} {leftInput rightInput : ShaInput}
    (leftPrefix : HasLiteralStatePrefix leftDigest leftInput)
    (rightPrefix : HasLiteralStatePrefix rightDigest rightInput)
    (inputExact : leftInput = rightInput) :
    leftDigest = rightDigest := by
  apply digest_bytes_injective
  calc
    bytes leftDigest = leftInput.take 32 := leftPrefix
    _ = rightInput.take 32 := by rw [inputExact]
    _ = bytes rightDigest := rightPrefix.symm

/-- Reverse two retained causal chains from a common terminal answer to their
typed boundary inputs.  This is a random-oracle first-creation argument, not
hash injectivity: equal answers select one retained record, and literal state
prefixes expose the predecessor digest.

The cross-chain allowed-input separation premises rule out unequal chain
lengths.  They are intentionally stated in both directions because the two
boundary payloads may contain different prover-supplied bytes before equality
is proved. -/
theorem exact_retained_digest_chains_boundary_input_eq
    {prior : List UnifiedExposureRecord}
    (answersNodup : (prior.map UnifiedExposureRecord.answer).Nodup)
    {leftBoundary rightBoundary : ShaInput}
    {leftAllowed rightAllowed : ShaInput → Prop}
    {leftInitial rightInitial terminal : Digest256}
    (leftChain : ExactRetainedDigestChain prior leftBoundary leftAllowed
      leftInitial terminal)
    (rightChain : ExactRetainedDigestChain prior rightBoundary rightAllowed
      rightInitial terminal)
    (leftBoundaryAvoidsRight : ∀ input, rightAllowed input →
      leftBoundary ≠ input)
    (rightBoundaryAvoidsLeft : ∀ input, leftAllowed input →
      rightBoundary ≠ input) :
    leftBoundary = rightBoundary := by
  revert rightInitial rightChain leftBoundaryAvoidsRight
    rightBoundaryAvoidsLeft
  induction leftChain with
  | boundary leftActor leftMember =>
      intro rightInitial rightChain leftBoundaryAvoidsRight
        rightBoundaryAvoidsLeft
      cases rightChain with
      | boundary rightActor rightMember =>
          exact equal_answer_records_fix_input answersNodup leftMember
            rightMember
      | step rightCurrent terminal rightInput rightActor
          rightPrevious rightPrefix rightAllowedInput rightMember =>
          have inputExact : leftBoundary = rightInput :=
            equal_answer_records_fix_input answersNodup leftMember rightMember
          have inputNe : leftBoundary ≠ rightInput :=
            leftBoundaryAvoidsRight rightInput rightAllowedInput
          exact (inputNe inputExact).elim
  | step leftCurrent terminal leftInput leftActor leftPrevious
      leftPrefix leftAllowedInput leftMember ih =>
      intro rightInitial rightChain leftBoundaryAvoidsRight
        rightBoundaryAvoidsLeft
      cases rightChain with
      | boundary rightActor rightMember =>
          have inputExact : leftInput = rightBoundary :=
            equal_answer_records_fix_input answersNodup leftMember rightMember
          have inputNe : rightBoundary ≠ leftInput :=
            rightBoundaryAvoidsLeft leftInput leftAllowedInput
          exact (inputNe inputExact.symm).elim
      | step rightCurrent terminal rightInput rightActor
          rightPrevious rightPrefix rightAllowedInput rightMember =>
          have inputExact : leftInput = rightInput :=
            equal_answer_records_fix_input answersNodup leftMember rightMember
          have currentExact : leftCurrent = rightCurrent :=
            literal_prefix_input_eq_fixes_digest leftPrefix rightPrefix
              inputExact
          subst rightCurrent
          exact ih rightPrevious leftBoundaryAvoidsRight
            rightBoundaryAvoidsLeft

#print axioms exact_lookup_digest_chain_retained_before_consumer
#print axioms exact_lookup_digest_chain_append_ordered_q16
#print axioms exact_lookup_digest_chain_through_machine_event
#print axioms exact_lookup_digest_chain_through_machine_events
#print axioms exact_retained_digest_chains_boundary_input_eq

end

end AspisK1.V7Tag73ExactRootCausalChain
