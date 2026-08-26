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

/-! ## Decoder agreement inherited from the accepted final ledger -/

def SamplesIncluded (before after : EvalState) : Prop :=
  ∀ record ∈ before.samples, record ∈ after.samples

def SamplesDecodeAs (valueAt : ChallengeId -> Qm31Bytes)
    (state : EvalState) : Prop :=
  ∀ record ∈ state.samples,
    decodeChallengeParameter exactSecureCircleParameterMap record.id
        record.blocks = some (valueAt record.id)

theorem queryStep_preserves_samples
    (table : FixedOracleTable) (state next : EvalState)
    (role : RawQueryRole) (output : Digest256)
    (run : queryStep table state role = some (output, next)) :
    next.samples = state.samples := by
  simp only [queryStep] at run
  cases found : tableLookup table (role.input state.digest) with
  | none => simp [found] at run
  | some actual =>
      rw [found] at run
      cases Option.some.inj run
      rfl

theorem squeezeManyFrom_preserves_samples
    (table : FixedOracleTable) (owner : SqueezeOwner)
    (first count : Nat) (state final : EvalState)
    (outputs : List Digest256)
    (run : squeezeManyFrom table owner first count state =
      some (outputs, final)) :
    final.samples = state.samples := by
  induction count generalizing first state outputs final with
  | zero =>
      simp only [squeezeManyFrom] at run
      cases Option.some.inj run
      rfl
  | succ count ih =>
      simp only [squeezeManyFrom] at run
      obtain ⟨firstPair, firstRun, run⟩ := Option.bind_eq_some_iff.mp run
      rcases firstPair with ⟨output, afterBlock⟩
      obtain ⟨restPair, restRun, result⟩ := Option.bind_eq_some_iff.mp run
      rcases restPair with ⟨restOutputs, restState⟩
      cases Option.some.inj result
      have firstPreserved : afterBlock.samples = state.samples := by
        rw [squeezeStep] at firstRun
        obtain ⟨outputPair, outputRun, firstRun⟩ :=
          Option.bind_eq_some_iff.mp firstRun
        rcases outputPair with ⟨actualOutput, afterOutput⟩
        obtain ⟨advancePair, advanceRun, result⟩ :=
          Option.bind_eq_some_iff.mp firstRun
        rcases advancePair with ⟨advanceOutput, afterAdvance⟩
        have pairEq := Option.some.inj result
        have stateEq := congrArg Prod.snd pairEq
        dsimp at stateEq
        subst afterBlock
        exact
          (queryStep_preserves_samples table afterOutput afterAdvance
            (.squeezeAdvance owner first) advanceOutput advanceRun).trans
          (queryStep_preserves_samples table state afterOutput
            (.squeezeOutput owner first) actualOutput outputRun)
      exact (ih (first := first + 1) (state := afterBlock)
        (outputs := restOutputs) (final := restState) restRun).trans
          firstPreserved

theorem squeezeMany_preserves_samples
    (table : FixedOracleTable) (owner : SqueezeOwner) (count : Nat)
    (state final : EvalState) (outputs : List Digest256)
    (run : squeezeMany table owner count state = some (outputs, final)) :
    final.samples = state.samples :=
  squeezeManyFrom_preserves_samples table owner 0 count state final outputs run

theorem causalMachineEvent_samples_included
    (table : FixedOracleTable) (state next : EvalState)
    (event : MachineEvent) (causal : CausalMachineEvent event)
    (run : runMachineEvent table state event = some next) :
    SamplesIncluded state next := by
  intro record member
  cases event with
  | absorb payload =>
      simp only [runMachineEvent, absorbStep] at run
      obtain ⟨pair, stepRun, result⟩ := Option.bind_eq_some_iff.mp run
      rcases pair with ⟨output, stepped⟩
      have steppedEq : stepped = next := Option.some.inj result
      subst next
      rw [queryStep_preserves_samples table state stepped
        (.absorb payload) output stepRun]
      exact member
  | challenge id use =>
      simp only [runMachineEvent] at run
      obtain ⟨pair, squeezeRun, result⟩ := Option.bind_eq_some_iff.mp run
      rcases pair with ⟨blocks, afterBlocks⟩
      have nextEq :
          { afterBlocks with
            samples := afterBlocks.samples ++ [{ id := id, blocks := blocks }] } =
            next := Option.some.inj result
      rw [← nextEq]
      simp only [List.mem_append]
      exact Or.inl (by
        rw [squeezeMany_preserves_samples table (.challenge id)
          use.blocksUsed state afterBlocks blocks squeezeRun]
        exact member)
  | grind stage choice => exact False.elim causal
  | check checkpoint =>
      have stateEq : state = next := by
        simpa [runMachineEvent] using Option.some.inj run
      rw [← stateEq]
      exact member

theorem causalMachineEvents_samples_included
    (table : FixedOracleTable) (events : List MachineEvent)
    (state final : EvalState)
    (causal : ∀ event ∈ events, CausalMachineEvent event)
    (run : runMachineEvents table events state = some final) :
    SamplesIncluded state final := by
  induction events generalizing state with
  | nil =>
      have stateEq : state = final := by
        simpa [runMachineEvents] using Option.some.inj run
      subst final
      intro record member
      exact member
  | cons event rest ih =>
      simp only [runMachineEvents] at run
      obtain ⟨next, eventRun, restRun⟩ := Option.bind_eq_some_iff.mp run
      have headCausal : CausalMachineEvent event := causal event (by simp)
      have tailCausal : ∀ tail ∈ rest, CausalMachineEvent tail := by
        intro tail member
        exact causal tail (by simp [member])
      have headIncluded := causalMachineEvent_samples_included table state next
        event headCausal eventRun
      have tailIncluded := ih (state := next) tailCausal restRun
      intro record member
      exact tailIncluded record (headIncluded record member)

theorem samplesDecodeAs_of_included
    (valueAt : ChallengeId -> Qm31Bytes) (before after : EvalState)
    (included : SamplesIncluded before after)
    (decoded : SamplesDecodeAs valueAt after) :
    SamplesDecodeAs valueAt before := by
  intro record member
  exact decoded record (included record member)

theorem challengeEvent_exposes_record
    (table : FixedOracleTable) (state next : EvalState)
    (id : ChallengeId) (use : SamplerUse id)
    (run : runMachineEvent table state (.challenge id use) = some next) :
    ∃ blocks afterBlocks,
      squeezeMany table (.challenge id) use.blocksUsed state =
        some (blocks, afterBlocks) ∧
      { id := id, blocks := blocks } ∈ next.samples := by
  simp only [runMachineEvent] at run
  obtain ⟨pair, squeezeRun, result⟩ := Option.bind_eq_some_iff.mp run
  rcases pair with ⟨blocks, afterBlocks⟩
  have nextEq :
      { afterBlocks with
        samples := afterBlocks.samples ++ [{ id := id, blocks := blocks }] } =
        next := Option.some.inj result
  refine ⟨blocks, afterBlocks, squeezeRun, ?_⟩
  rw [← nextEq]
  simp

theorem eventDecoderAgreement_of_success
    (table : FixedOracleTable) (valueAt : ChallengeId -> Qm31Bytes)
    (event : MachineEvent) (eval next : EvalState)
    (causal : CausalMachineEvent event)
    (run : runMachineEvent table eval event = some next)
    (decoded : SamplesDecodeAs valueAt next) :
    EventDecoderAgreement table valueAt eval event := by
  cases event with
  | absorb payload => trivial
  | challenge id use =>
      intro blocks squeezedEval squeezeRun
      obtain ⟨actualBlocks, actualAfter, actualRun, member⟩ :=
        challengeEvent_exposes_record table eval next id use run
      have pairEq : (blocks, squeezedEval) = (actualBlocks, actualAfter) :=
        Option.some.inj (squeezeRun.symm.trans actualRun)
      have blocksEq : blocks = actualBlocks := congrArg Prod.fst pairEq
      have exactMember : { id := id, blocks := blocks } ∈ next.samples := by
        simpa [blocksEq] using member
      exact decoded { id := id, blocks := blocks } exactMember
  | grind stage choice => exact False.elim causal
  | check checkpoint => trivial

/-- The final accepted sample ledger is sufficient to construct the complete
causal decoder agreement; no intermediate decoding premise is required. -/
theorem causalDecoderAgreement_of_final_ledger
    (table : FixedOracleTable) (valueAt : ChallengeId -> Qm31Bytes)
    (events : List MachineEvent) (eval final : EvalState)
    (causal : ∀ event ∈ events, CausalMachineEvent event)
    (run : runMachineEvents table events eval = some final)
    (decoded : SamplesDecodeAs valueAt final) :
    CausalDecoderAgreement table valueAt events eval := by
  induction events generalizing eval with
  | nil => trivial
  | cons event rest ih =>
      simp only [runMachineEvents] at run
      obtain ⟨next, eventRun, restRun⟩ := Option.bind_eq_some_iff.mp run
      have headCausal : CausalMachineEvent event := causal event (by simp)
      have tailCausal : ∀ tail ∈ rest, CausalMachineEvent tail := by
        intro tail member
        exact causal tail (by simp [member])
      have tailIncluded := causalMachineEvents_samples_included table rest next
        final tailCausal restRun
      have nextDecoded := samplesDecodeAs_of_included valueAt next final
        tailIncluded decoded
      have headAgreement := eventDecoderAgreement_of_success table valueAt
        event eval next headCausal eventRun nextDecoded
      have tailAgreement := ih (eval := next) tailCausal restRun
      simp only [CausalDecoderAgreement]
      refine ⟨headCausal, ?_⟩
      intro actualNext actualRun
      have nextEq : actualNext = next := by
        exact Option.some.inj (actualRun.symm.trans eventRun)
      subst actualNext
      exact ⟨headAgreement, tailAgreement⟩

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
#print axioms causalDecoderAgreement_of_final_ledger

end AspisK1.V7Tag73CausalEventReplay
