import AspisFormal.K1.V7Tag73CausalEventReplay
import AspisFormal.K1.V7Tag73SamplerExactValue

/-!
# Exact replay of a causal Tag-73 semantic-round list

This file connects a successful fixed-table execution of serialized semantic
messages to the prefix-only exact-QM31 runner used by the Tag-73 Fiat--Shamir
schedule.  The proof is by one induction over the message list; it does not
special-case or duplicate the ten deployed rounds.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SemanticRoundReplay

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73SemanticTranscriptBridge
open AspisK1.V7Tag73CausalEventReplay
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SamplerExactValue
open AspisK1.V7Tag73FixedFieldMessageBridge
open AspisK1.V7Tag73RawProverMessages
open AspisV5ComponentCQM31TowerExact
open AspisV5AcceptedSumcheckSourceBridge
open AspisPool.V7CompactSemanticBinding
open AspisV6AcceptedPathObligations

/-- The evaluator event list corresponding to the exact-message list consumed
by `runSemanticMessages`. -/
def semanticEventsForMessages
    (uses : (id : ChallengeId) -> SamplerUse id) :
    Nat -> List (Degree27Message QM31Exact) -> List MachineEvent
  | _, [] => []
  | index, message :: rest =>
      if inRange : index < 10 then
        let round : Fin 10 := ⟨index, inRange⟩
        [.absorb (.semanticRound round (sentFieldsOfMessage message)),
         .challenge (.semantic round) (uses (.semantic round))] ++
          semanticEventsForMessages uses (index + 1) rest
      else
        []

/-- Exact values expected from the same ordered semantic challenge list. -/
def semanticValuesForMessages
    (exactValue : ChallengeId -> QM31Exact) :
    Nat -> List (Degree27Message QM31Exact) -> List QM31Exact
  | _, [] => []
  | index, _ :: rest =>
      if inRange : index < 10 then
        exactValue (.semantic ⟨index, inRange⟩) ::
          semanticValuesForMessages exactValue (index + 1) rest
      else
        []

theorem semanticEventsForMessages_are_causal
    (uses : (id : ChallengeId) -> SamplerUse id)
    (index : Nat) (messages : List (Degree27Message QM31Exact)) :
    ∀ event ∈ semanticEventsForMessages uses index messages,
      CausalMachineEvent event := by
  induction messages generalizing index with
  | nil => simp [semanticEventsForMessages]
  | cons message rest ih =>
      by_cases inRange : index < 10
      · simp only [semanticEventsForMessages, dif_pos inRange]
        intro event member
        rw [List.mem_append] at member
        rcases member with head | tail
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at head
          rcases head with rfl | rfl <;> trivial
        · exact ih (index + 1) event tail
      · simp [semanticEventsForMessages, inRange]

/-- At the deployed ten-round length, the recursive exact-message schedule is
the same list as the verifier's `List.ofFn`/`flatten` presentation. -/
theorem semanticEventsForMessages_ofFn
    (uses : (id : ChallengeId) -> SamplerUse id)
    (messages : Fin 10 -> Degree27Message QM31Exact) :
    semanticEventsForMessages uses 0 (List.ofFn messages) =
      (List.ofFn fun round : Fin 10 =>
        [.absorb (.semanticRound round
          (sentFieldsOfMessage (messages round))),
         .challenge (.semantic round) (uses (.semantic round))]).flatten := by
  simp [semanticEventsForMessages]

/-- Exact decoding of the fixed prover section identifies the generic replay
list with the literal production `semanticEvents` list. -/
theorem compact_semantic_events_are_production_events
    (messages : Messages) (decoded : Fin 641 -> QM31Exact)
    (decodeExact : FixedFieldDecodeExact (rawOfMessages messages) decoded)
    (point : Fin 10 -> QM31Exact) :
    semanticEventsForMessages messages.challengeUse 0
        (List.ofFn (compactSemanticMessages
          (decodedFixedFieldView decoded) point)) =
      semanticEvents messages := by
  rw [semanticEventsForMessages_ofFn]
  unfold semanticEvents
  congr 1
  apply congrArg List.ofFn
  funext round
  simp only [challengeEvent]
  have sentEq : sentFieldsOfMessage
      (compactSemanticMessage (decodedFixedFieldView decoded) point round) =
        messages.semanticSent round := by
    simpa [rawOfMessages] using
      sentFieldsOfDecodedCompactMessage_eq_raw decodeExact point round
  simpa only [compactSemanticMessages, sentEq]

/-- If a causal challenge event occurs in a successful list execution, the
record emitted by that exact occurrence remains in the final sample ledger. -/
theorem challenge_record_in_final_of_event_mem
    (table : FixedOracleTable) (events : List MachineEvent)
    (eval final : EvalState) (id : ChallengeId) (use : SamplerUse id)
    (causal : ∀ event ∈ events, CausalMachineEvent event)
    (member : .challenge id use ∈ events)
    (run : runMachineEvents table events eval = some final) :
    ∃ blocks, { id := id, blocks := blocks } ∈ final.samples := by
  induction events generalizing eval with
  | nil => simp at member
  | cons event rest ih =>
      simp only [runMachineEvents] at run
      obtain ⟨next, eventRun, restRun⟩ := Option.bind_eq_some_iff.mp run
      have restCausal : ∀ tail ∈ rest, CausalMachineEvent tail := by
        intro tail tailMember
        exact causal tail (by simp [tailMember])
      have included := causalMachineEvents_samples_included table rest next
        final restCausal restRun
      rcases List.mem_cons.mp member with head | tail
      · subst event
        obtain ⟨blocks, _afterBlocks, _squeezeRun, emitted⟩ :=
          challengeEvent_exposes_record table eval next id use eventRun
        exact ⟨blocks, included _ emitted⟩
      · exact ih (eval := next) restCausal tail restRun

/-- A challenge value recorded by a successful causal execution is a
canonical exact-tower element, not merely an arbitrary sixteen-byte string. -/
theorem challenge_value_has_exact_tower_of_event_mem
    (table : FixedOracleTable) (valueAt : ChallengeId -> Qm31Bytes)
    (events : List MachineEvent) (eval final : EvalState)
    (id : ChallengeId) (use : SamplerUse id)
    (causal : ∀ event ∈ events, CausalMachineEvent event)
    (member : .challenge id use ∈ events)
    (run : runMachineEvents table events eval = some final)
    (decoded : SamplesDecodeAs valueAt final) :
    ∃ value : QM31Exact,
      decodeTagQM31ExactLE (valueAt id) = some value := by
  obtain ⟨blocks, recordMember⟩ :=
    challenge_record_in_final_of_event_mem table events eval final id use
      causal member run
  have parameterDecoded := decoded { id := id, blocks := blocks } recordMember
  exact decodeChallengeParameter_has_exact_tower_value
    exactSecureCircleParameterMap id blocks (valueAt id) parameterDecoded

/-- Canonical exact value selected from the deployed challenge bytes.  The
default branch is eliminated whenever the corresponding event accepted. -/
noncomputable def exactChallengeValue (valueAt : ChallengeId -> Qm31Bytes)
    (id : ChallengeId) : QM31Exact :=
  (decodeTagQM31ExactLE (valueAt id)).getD 0

@[simp] theorem encodeTagQM31ExactLE_zero :
    encodeTagQM31ExactLE (0 : QM31Exact) = zeroBytes 16 := by
  funext index
  fin_cases index <;> rfl

/-- Successful nonzero-sampler bytes decode to a nonzero element of the exact
QM31 tower. -/
theorem exactChallengeValue_ne_zero_of_nonzero_run
    (valueAt : ChallengeId -> Qm31Bytes) (id : ChallengeId)
    (blocks : List Digest256)
    (run : decodeNonzeroExact blocks = some (valueAt id))
    (decoded : decodeTagQM31ExactLE (valueAt id) =
      some (exactChallengeValue valueAt id)) :
    exactChallengeValue valueAt id ≠ 0 := by
  intro valueZero
  have roundtrip := encodeTagQM31ExactLE_of_decode (valueAt id)
    (exactChallengeValue valueAt id) decoded
  have bytesZero : valueAt id = zeroBytes 16 := by
    calc
      valueAt id = encodeTagQM31ExactLE (exactChallengeValue valueAt id) :=
        roundtrip.symm
      _ = encodeTagQM31ExactLE 0 := congrArg encodeTagQM31ExactLE valueZero
      _ = zeroBytes 16 := encodeTagQM31ExactLE_zero
  exact decodeNonzeroExact_value_ne_zero blocks (valueAt id) run bytesZero

theorem semantic_challenge_event_mem
    (uses : (id : ChallengeId) -> SamplerUse id)
    (messages : Fin 10 -> Degree27Message QM31Exact) (round : Fin 10) :
    .challenge (.semantic round) (uses (.semantic round)) ∈
      semanticEventsForMessages uses 0 (List.ofFn messages) := by
  fin_cases round <;> simp [semanticEventsForMessages]

/-- Successful execution of all ten semantic rounds proves canonical exact
decoding for the selected exact value of every semantic challenge. -/
theorem semantic_challenge_values_decode
    (table : FixedOracleTable) (uses : (id : ChallengeId) -> SamplerUse id)
    (encodedValue : ChallengeId -> Qm31Bytes)
    (messages : Fin 10 -> Degree27Message QM31Exact)
    (eval final : EvalState)
    (run : runMachineEvents table
      (semanticEventsForMessages uses 0 (List.ofFn messages)) eval =
        some final)
    (decoded : SamplesDecodeAs encodedValue final) (round : Fin 10) :
    decodeTagQM31ExactLE (encodedValue (.semantic round)) =
      some (exactChallengeValue encodedValue (.semantic round)) := by
  have causal := semanticEventsForMessages_are_causal uses 0
    (List.ofFn messages)
  obtain ⟨value, valueRun⟩ := challenge_value_has_exact_tower_of_event_mem
    table encodedValue
      (semanticEventsForMessages uses 0 (List.ofFn messages)) eval final
      (.semantic round) (uses (.semantic round)) causal
      (semantic_challenge_event_mem uses messages round) run decoded
  simp [exactChallengeValue, valueRun]

/-- A successful causal evaluator run and its accepted final sample ledger
produce the exact schedule runner, including every decoded QM31 value. -/
theorem runMachineSemanticEvents_matches_runSemanticMessages
    (table : FixedOracleTable)
    (uses : (id : ChallengeId) -> SamplerUse id)
    (encodedValue : ChallengeId -> Qm31Bytes)
    (exactValue : ChallengeId -> QM31Exact)
    (exactDecode : ∀ round : Fin 10,
      decodeTagQM31ExactLE (encodedValue (.semantic round)) =
        some (exactValue (.semantic round)))
    (index : Nat) (messages : List (Degree27Message QM31Exact))
    (within : index + messages.length ≤ 10)
    (eval final : EvalState) (machine : MachineState)
    (aligned : machine.digest = eval.digest)
    (run : runMachineEvents table
      (semanticEventsForMessages uses index messages) eval = some final)
    (decoded : SamplesDecodeAs encodedValue final) :
    ∃ finalMachine,
      runSemanticMessages (tableHashOracle table) index messages machine =
        some (semanticValuesForMessages exactValue index messages,
          finalMachine) ∧
      finalMachine.digest = final.digest := by
  induction messages generalizing index eval machine with
  | nil =>
      have evalEq : eval = final := by
        simpa [semanticEventsForMessages, runMachineEvents] using
          Option.some.inj run
      subst final
      exact ⟨machine, by simp [runSemanticMessages, semanticValuesForMessages],
        aligned⟩
  | cons message rest ih =>
      have inRange : index < 10 := by
        simp only [List.length_cons] at within
        omega
      have restWithin : (index + 1) + rest.length ≤ 10 := by
        simp only [List.length_cons] at within
        omega
      let round : Fin 10 := ⟨index, inRange⟩
      simp only [semanticEventsForMessages, dif_pos inRange,
        List.cons_append, runMachineEvents] at run
      obtain ⟨afterMessageEval, absorbRun, run⟩ :=
        Option.bind_eq_some_iff.mp run
      obtain ⟨afterChallengeEval, challengeRun, restRun⟩ :=
        Option.bind_eq_some_iff.mp run
      have restCausal := semanticEventsForMessages_are_causal uses
        (index + 1) rest
      have restIncluded := causalMachineEvents_samples_included table
        (semanticEventsForMessages uses (index + 1) rest)
        afterChallengeEval final restCausal restRun
      have challengeDecoded := samplesDecodeAs_of_included encodedValue
        afterChallengeEval final restIncluded decoded
      have challengeAgreement := eventDecoderAgreement_of_success table
        encodedValue (.challenge (.semantic round)
          (uses (.semantic round))) afterMessageEval afterChallengeEval
        (by trivial) challengeRun challengeDecoded
      let afterMessageMachine := absorb (tableHashOracle table) machine
        (.semanticRound round (sentFieldsOfMessage message))
      have afterMessageAligned :
          afterMessageMachine.digest = afterMessageEval.digest :=
        absorbStep_matches_tableHashOracle_digest table eval afterMessageEval
          machine (.semanticRound round (sentFieldsOfMessage message))
            aligned absorbRun
      obtain ⟨afterChallengeMachine, sampled, challengeAligned⟩ :=
        runMachineChallenge_matches_sampleExactChallenge table
          (.semantic round) (uses (.semantic round)) afterMessageEval
          afterChallengeEval afterMessageMachine
          (encodedValue (.semantic round)) (exactValue (.semantic round))
          afterMessageAligned challengeRun challengeAgreement
          (exactDecode round)
      obtain ⟨finalMachine, restMatched, finalAligned⟩ :=
        ih (index := index + 1) (within := restWithin)
          (eval := afterChallengeEval) (machine := afterChallengeMachine)
          challengeAligned restRun
      refine ⟨finalMachine, ?_, finalAligned⟩
      simp only [runSemanticMessages, dif_pos inRange,
        semanticValuesForMessages]
      rw [show sampleExactChallenge (tableHashOracle table)
          (.semantic ⟨index, inRange⟩)
          (absorb (tableHashOracle table) machine
            (.semanticRound ⟨index, inRange⟩
              (sentFieldsOfMessage message))) =
          some (exactValue (.semantic ⟨index, inRange⟩),
            afterChallengeMachine) by
        simpa [round, afterMessageMachine] using sampled]
      change Option.bind
          (runSemanticMessages (tableHashOracle table) (index + 1) rest
            afterChallengeMachine)
          (fun result => some
            (exactValue (.semantic ⟨index, inRange⟩) :: result.1,
              result.2)) = _
      rw [restMatched]
      rfl

/-- A successful exact semantic execution of `first ++ second` exposes the
same exact-value execution of `first`. -/
theorem runSemanticMessages_exact_prefix_of_append
    (oracle : HashOracle) (exactValue : ChallengeId -> QM31Exact)
    (index : Nat)
    (first second : List (Degree27Message QM31Exact))
    (within : index + (first ++ second).length ≤ 10)
    (state final : MachineState)
    (run : runSemanticMessages oracle index (first ++ second) state =
      some (semanticValuesForMessages exactValue index (first ++ second),
        final)) :
    ∃ middle,
      runSemanticMessages oracle index first state =
        some (semanticValuesForMessages exactValue index first, middle) := by
  induction first generalizing index state final with
  | nil => exact ⟨state, by simp [runSemanticMessages,
      semanticValuesForMessages]⟩
  | cons message rest ih =>
      have inRange : index < 10 := by
        simp only [List.cons_append, List.length_cons, List.length_append] at within
        omega
      have restWithin : (index + 1) + (rest ++ second).length ≤ 10 := by
        simp only [List.cons_append, List.length_cons, List.length_append] at within ⊢
        omega
      simp only [List.cons_append, runSemanticMessages, dif_pos inRange,
        semanticValuesForMessages] at run
      obtain ⟨sampledPair, sampled, run⟩ := Option.bind_eq_some_iff.mp run
      rcases sampledPair with ⟨challenge, afterChallenge⟩
      obtain ⟨tailPair, tailRun, resultEq⟩ := Option.bind_eq_some_iff.mp run
      rcases tailPair with ⟨tailValues, tailFinal⟩
      have pairEq :
          (challenge :: tailValues, tailFinal) =
            (exactValue (.semantic ⟨index, inRange⟩) ::
              semanticValuesForMessages exactValue (index + 1)
                (rest ++ second), final) := by
        simpa only [pure, Option.some.injEq] using resultEq
      have challengeEq : challenge =
          exactValue (.semantic ⟨index, inRange⟩) :=
        (List.cons.inj (congrArg Prod.fst pairEq)).1
      have tailValuesEq : tailValues =
          semanticValuesForMessages exactValue (index + 1)
            (rest ++ second) :=
        (List.cons.inj (congrArg Prod.fst pairEq)).2
      have tailFinalEq : tailFinal = final := congrArg Prod.snd pairEq
      subst challenge
      subst tailValues
      subst tailFinal
      obtain ⟨middle, prefixRun⟩ := ih (index := index + 1)
        (state := afterChallenge) (final := final) restWithin tailRun
      refine ⟨middle, ?_⟩
      simp only [runSemanticMessages, dif_pos inRange,
        semanticValuesForMessages]
      rw [sampled]
      change Option.bind
        (runSemanticMessages oracle (index + 1) rest afterChallenge)
        (fun result => some
          (exactValue (.semantic ⟨index, inRange⟩) :: result.1,
            result.2)) = _
      rw [prefixRun]
      rfl

theorem semanticValuesForMessages_ofFn_prefix
    (exactValue : ChallengeId -> QM31Exact)
    (messages : Fin 10 -> Degree27Message QM31Exact) (round : Fin 10) :
    semanticValuesForMessages exactValue 0
        (List.ofFn fun earlier : Fin (round.val + 1) =>
          messages ⟨earlier.val, by omega⟩) =
      List.ofFn (fun earlier : Fin (round.val + 1) =>
        exactValue (.semantic ⟨earlier.val, by omega⟩)) := by
  fin_cases round <;> simp [semanticValuesForMessages]

#print axioms semanticEventsForMessages_are_causal
#print axioms semanticEventsForMessages_ofFn
#print axioms compact_semantic_events_are_production_events
#print axioms challenge_value_has_exact_tower_of_event_mem
#print axioms encodeTagQM31ExactLE_zero
#print axioms exactChallengeValue_ne_zero_of_nonzero_run
#print axioms semantic_challenge_values_decode
#print axioms runMachineSemanticEvents_matches_runSemanticMessages
#print axioms runSemanticMessages_exact_prefix_of_append
#print axioms semanticValuesForMessages_ofFn_prefix

end AspisK1.V7Tag73SemanticRoundReplay
