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

/-- A successful causal evaluator run and its accepted final sample ledger
produce the exact schedule runner, including every decoded QM31 value. -/
theorem runMachineSemanticEvents_matches_runSemanticMessages
    (table : FixedOracleTable)
    (uses : (id : ChallengeId) -> SamplerUse id)
    (encodedValue : ChallengeId -> Qm31Bytes)
    (exactValue : ChallengeId -> QM31Exact)
    (exactDecode : ∀ id,
      decodeTagQM31ExactLE (encodedValue id) = some (exactValue id))
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
          (exactDecode (.semantic round))
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

#print axioms semanticEventsForMessages_are_causal
#print axioms semanticEventsForMessages_ofFn
#print axioms compact_semantic_events_are_production_events
#print axioms runMachineSemanticEvents_matches_runSemanticMessages

end AspisK1.V7Tag73SemanticRoundReplay
