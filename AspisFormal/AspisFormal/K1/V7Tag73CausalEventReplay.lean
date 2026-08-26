import AspisFormal.K1.V7Tag73SemanticTranscriptBridge

/-!
# Causal Tag-73 event replay

This file lifts the single-challenge table/oracle equivalence to ordered
absorb/challenge/check segments.  Grinding is excluded from this local runner:
the semantic prefix contains no grinding, while the three deployed grinding
sites are already accounted for separately by K1.6.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73CausalEventReplay

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73SemanticTranscriptBridge

/-- Exactly the event forms allowed in the pre-eta and semantic segments. -/
def CausalMachineEvent : MachineEvent -> Prop
  | .absorb _ => True
  | .challenge _ _ => True
  | .check _ => True
  | .grind _ _ => False

/-- One total-oracle causal event.  A challenge is accepted only when the
incremental deployed decoder returns the designated value for its identifier. -/
def runHashEvent (oracle : HashOracle) (valueAt : ChallengeId -> Qm31Bytes)
    (state : MachineState) : MachineEvent -> Option MachineState
  | .absorb payload => some (absorb oracle state payload)
  | .challenge id _ => do
      let (value, next) <- sampleChallenge oracle id state
      if value = valueAt id then some next else none
  | .check _ => some state
  | .grind _ _ => none

def runHashEvents (oracle : HashOracle) (valueAt : ChallengeId -> Qm31Bytes) :
    List MachineEvent -> MachineState -> Option MachineState
  | [], state => some state
  | event :: rest, state => do
      let next <- runHashEvent oracle valueAt state event
      runHashEvents oracle valueAt rest next

/-- Decoder agreement at one exact fixed-table state. -/
def EventDecoderAgreement (table : FixedOracleTable)
    (valueAt : ChallengeId -> Qm31Bytes) (eval : EvalState) :
    MachineEvent -> Prop
  | .challenge id use =>
      ∀ blocks squeezedEval,
        squeezeMany table (.challenge id) use.blocksUsed eval =
            some (blocks, squeezedEval) ->
          decodeChallengeParameter exactSecureCircleParameterMap id blocks =
            some (valueAt id)
  | _ => True

/-- Every successful state reached through the list carries the corresponding
decoder agreement.  The universal successor is not an abstraction leak:
`runMachineEvent` is a deterministic function, and only its successful result
is used by the alignment theorem. -/
def CausalDecoderAgreement (table : FixedOracleTable)
    (valueAt : ChallengeId -> Qm31Bytes) :
    List MachineEvent -> EvalState -> Prop
  | [], _ => True
  | event :: rest, eval =>
      CausalMachineEvent event ∧
        ∀ next, runMachineEvent table eval event = some next ->
          EventDecoderAgreement table valueAt eval event ∧
            CausalDecoderAgreement table valueAt rest next

theorem runMachineEvent_matches_runHashEvent
    (table : FixedOracleTable) (valueAt : ChallengeId -> Qm31Bytes)
    (event : MachineEvent) (eval next : EvalState)
    (machine : MachineState) (causal : CausalMachineEvent event)
    (agreement : EventDecoderAgreement table valueAt eval event)
    (aligned : machine.digest = eval.digest)
    (run : runMachineEvent table eval event = some next) :
    ∃ nextMachine,
      runHashEvent (tableHashOracle table) valueAt machine event =
        some nextMachine ∧
      nextMachine.digest = next.digest := by
  cases event with
  | absorb payload =>
      let nextMachine := absorb (tableHashOracle table) machine payload
      exact ⟨nextMachine, rfl,
        absorbStep_matches_tableHashOracle_digest table eval next machine
          payload aligned run⟩
  | challenge id use =>
      obtain ⟨nextMachine, sampled, digestEq⟩ :=
        runMachineChallenge_matches_sampleChallenge table id use eval next
          machine (valueAt id) aligned run agreement
      refine ⟨nextMachine, ?_, digestEq⟩
      simp [runHashEvent, sampled]
  | grind stage choice => exact False.elim causal
  | check checkpoint =>
      have nextEq : eval = next := by
        simpa [runMachineEvent] using Option.some.inj run
      subst next
      exact ⟨machine, rfl, aligned⟩

/-- Ordered causal segments replay identically under the totalized table
oracle, at the exact digest level used by every subsequent transcript query. -/
theorem runMachineEvents_match_runHashEvents
    (table : FixedOracleTable) (valueAt : ChallengeId -> Qm31Bytes)
    (events : List MachineEvent) (eval next : EvalState)
    (machine : MachineState)
    (agreement : CausalDecoderAgreement table valueAt events eval)
    (aligned : machine.digest = eval.digest)
    (run : runMachineEvents table events eval = some next) :
    ∃ nextMachine,
      runHashEvents (tableHashOracle table) valueAt events machine =
        some nextMachine ∧
      nextMachine.digest = next.digest := by
  induction events generalizing eval machine next with
  | nil =>
      have nextEq : eval = next := by
        simpa [runMachineEvents] using Option.some.inj run
      subst next
      exact ⟨machine, rfl, aligned⟩
  | cons event rest ih =>
      simp only [runMachineEvents] at run
      obtain ⟨middle, eventRun, restRun⟩ := Option.bind_eq_some_iff.mp run
      simp only [CausalDecoderAgreement] at agreement
      obtain ⟨causal, agreement⟩ := agreement
      obtain ⟨headAgreement, tailAgreement⟩ := agreement middle eventRun
      obtain ⟨middleMachine, hashEvent, middleAligned⟩ :=
        runMachineEvent_matches_runHashEvent table valueAt event eval middle
          machine causal headAgreement aligned eventRun
      obtain ⟨nextMachine, hashRest, nextAligned⟩ :=
        ih (eval := middle) (machine := middleMachine) (next := next)
          tailAgreement middleAligned restRun
      refine ⟨nextMachine, ?_, nextAligned⟩
      simp [runHashEvents, hashEvent, hashRest]

#print axioms runMachineEvent_matches_runHashEvent
#print axioms runMachineEvents_match_runHashEvents

end AspisK1.V7Tag73CausalEventReplay
