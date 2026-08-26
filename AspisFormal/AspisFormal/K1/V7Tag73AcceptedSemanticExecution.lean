import AspisFormal.K1.V7Tag73SemanticRoundReplay
import AspisFormal.K1.V7Tag73CheckedRefinementFullFutureFreePath

/-!
# Exact semantic segment exposed by accepted Tag-73 execution

This file cuts the eta and ten semantic rounds out of the literal successful
fixed-table evaluator run.  It also transports the accepted final decoder
ledger back to that segment and constructs its canonical exact QM31 values.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73AcceptedSemanticExecution

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73CausalEventReplay
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SemanticRoundReplay
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73SemanticTranscriptBridge
open AspisK1.V7Tag73FixedFieldMessageBridge
open AspisK1.V7Tag73RawProverMessages
open AspisV5AcceptedSumcheckSourceBridge
open AspisV5ComponentCQM31TowerExact
open AspisV5SumcheckCommitment
open AspisV5SumcheckTranscriptBinding
open AspisPool.V7CompactSemanticBinding
open AspisV6AcceptedPathObligations
open AspisV6TranscriptRelationGrammar

noncomputable section

/-- Exact linear prefix after C2 and before the eta challenge. -/
def beforeEtaTailEvents (messages : Messages) : List MachineEvent :=
  [.absorb .constraintRegistry,
   .absorb .helperSum,
   challengeEvent messages .theta] ++
  (List.ofFn fun coordinate : Fin 10 =>
    challengeEvent messages (.zerocheckPoint coordinate)) ++
  [challengeEvent messages .mu,
   .absorb (.initialMaskClaim messages.initialClaim)]

/-- The portion of `prefixAfterC2` strictly following the ten semantic
rounds. -/
def afterSemanticTailEvents (messages : Messages) : List MachineEvent :=
  [.absorb (.pointClaims messages.pointClaims),
   .check .semanticTerminal,
   .grind .batch messages.batchGrinding,
   .check .batchWork,
   .absorb (.batchNonce messages.batchGrinding.selected),
   challengeEvent messages .gamma,
   .absorb (.inactiveClaim messages.inactiveClaim),
   challengeEvent messages .kappa] ++
  oodEvents messages ++
  [.absorb (.relationRound 0 (messages.relationSent 0)),
   .grind .fold messages.foldGrinding,
   .check .foldWork,
   .absorb (.foldNonce messages.foldGrinding.selected),
   challengeEvent messages (.alpha 0),
   .absorb (.final256 messages.finalValues),
   .grind .final messages.finalGrinding,
   .check .finalWork,
   .absorb (.finalNonce messages.finalGrinding.selected)]

theorem prefixAfterC2_exact_semantic_factorization (messages : Messages) :
    prefixAfterC2 messages =
      beforeEtaTailEvents messages ++
        [challengeEvent messages .eta] ++
          semanticEvents messages ++ afterSemanticTailEvents messages := by
  rfl

theorem production_semantic_events_are_causal (messages : Messages) :
    ∀ event ∈ semanticEvents messages, CausalMachineEvent event := by
  simp [semanticEvents, challengeEvent, CausalMachineEvent]

theorem production_semantic_challenge_mem
    (messages : Messages) (round : Fin 10) :
    challengeEvent messages (.semantic round) ∈ semanticEvents messages := by
  fin_cases round <;> simp [semanticEvents, challengeEvent]

/-- Concrete pre-eta transcript determined by one accepted fixed-table
instance. -/
def semanticPreEtaOf (table : FixedOracleTable) (messages : Messages) :
    SemanticPreEta where
  publicPrefix :=
    { oracle := tableHashOracle table
      context := messages.context
      c1Root := messages.c1Root
      initialClaim := messages.initialClaim }
  maskRoot := messages.c2.root

/-- Full transcript-advancing event list through the initial masked claim.
The two public-root-salt calls are represented by their exact oracle answers
inside the following absorb payloads because those calls do not advance the
duplex digest. -/
def beforeEtaFullEvents (table : FixedOracleTable)
    (messages : Messages) : List MachineEvent :=
  prefixBeforeC1 messages ++
  [.absorb (.c1Root messages.c1Root
      (publicRootSalt (tableHashOracle table) messages.context c1TreeTag)),
   challengeEvent messages .lambda,
   challengeEvent messages .chi,
   .absorb (.c2Root messages.c2.root
      (publicRootSalt (tableHashOracle table) messages.context c2TreeTag))] ++
  beforeEtaTailEvents messages

/-- Erase only the equality assertion attached to a challenge event.  Any
successful `runHashEvent` execution implies this runner succeeds at the same
state. -/
def runOnlyEvent (oracle : HashOracle) (state : MachineState) :
    MachineEvent -> Option MachineState
  | .absorb payload => some (absorb oracle state payload)
  | .challenge id _ => sampleOnly oracle id state
  | .check _ => some state
  | .grind _ _ => none

def runOnlyEvents (oracle : HashOracle) :
    List MachineEvent -> MachineState -> Option MachineState
  | [], state => some state
  | event :: rest, state => do
      let next <- runOnlyEvent oracle state event
      runOnlyEvents oracle rest next

theorem runOnlyEvents_append (oracle : HashOracle)
    (first second : List MachineEvent) (state : MachineState) :
    runOnlyEvents oracle (first ++ second) state = (do
      let middle <- runOnlyEvents oracle first state
      runOnlyEvents oracle second middle) := by
  induction first generalizing state with
  | nil => rfl
  | cons event rest ih =>
      cases eventRun : runOnlyEvent oracle state event with
      | none => simp [List.cons_append, runOnlyEvents, eventRun]
      | some next =>
          simp [List.cons_append, runOnlyEvents, eventRun, ih next]

theorem runOnlyEvents_challengeList (oracle : HashOracle)
    (uses : (id : ChallengeId) -> SamplerUse id)
    (ids : List ChallengeId) (state : MachineState) :
    runOnlyEvents oracle
        (ids.map fun id => MachineEvent.challenge id (uses id)) state =
      sampleIds oracle ids state := by
  induction ids generalizing state with
  | nil => rfl
  | cons id rest ih =>
      simp only [List.map_cons, runOnlyEvents, runOnlyEvent, sampleIds,
        sampleOnly]
      congr 1
      funext pair
      exact ih pair

theorem runHashEvents_success_implies_runOnlyEvents
    (oracle : HashOracle) (valueAt : ChallengeId -> Qm31Bytes)
    (events : List MachineEvent) (state final : MachineState)
    (run : runHashEvents oracle valueAt events state = some final) :
    runOnlyEvents oracle events state = some final := by
  induction events generalizing state with
  | nil => simpa [runHashEvents, runOnlyEvents] using run
  | cons event rest ih =>
      simp only [runHashEvents] at run
      obtain ⟨next, eventRun, restRun⟩ := Option.bind_eq_some_iff.mp run
      have onlyEvent : runOnlyEvent oracle state event = some next := by
        cases event with
        | absorb payload => simpa [runHashEvent, runOnlyEvent] using eventRun
        | challenge id use =>
            simp only [runHashEvent] at eventRun
            obtain ⟨pair, sampled, accepted⟩ :=
              Option.bind_eq_some_iff.mp eventRun
            rcases pair with ⟨value, sampledState⟩
            have stateEq : sampledState = next := by
              split at accepted
              · simpa using Option.some.inj accepted
              · simp at accepted
            subst sampledState
            simpa [runOnlyEvent, sampleOnly, sampled]
        | grind stage choice => simp [runHashEvent] at eventRun
        | check checkpoint => simpa [runHashEvent, runOnlyEvent] using eventRun
      have tail := ih (state := next) restRun
      simp [runOnlyEvents, onlyEvent, tail]

theorem runHashEvents_append (oracle : HashOracle)
    (valueAt : ChallengeId -> Qm31Bytes)
    (first second : List MachineEvent) (state : MachineState) :
    runHashEvents oracle valueAt (first ++ second) state = (do
      let middle <- runHashEvents oracle valueAt first state
      runHashEvents oracle valueAt second middle) := by
  induction first generalizing state with
  | nil => rfl
  | cons event rest ih =>
      cases eventRun : runHashEvent oracle valueAt state event with
      | none => simp [List.cons_append, runHashEvents, eventRun]
      | some next =>
          simp [List.cons_append, runHashEvents, eventRun, ih next]

def runBeforeEtaTail (oracle : HashOracle) (messages : Messages)
    (state : MachineState) : Option MachineState := do
  let afterRegistry := absorb oracle state .constraintRegistry
  let afterHelper := absorb oracle afterRegistry .helperSum
  let afterTheta <- sampleOnly oracle .theta afterHelper
  let afterPoint <- sampleIds oracle
    (List.ofFn fun coordinate : Fin 10 => .zerocheckPoint coordinate)
      afterTheta
  let afterMu <- sampleOnly oracle .mu afterPoint
  pure (absorb oracle afterMu (.initialMaskClaim messages.initialClaim))

theorem runOnlyEvents_beforeEtaTailEvents
    (oracle : HashOracle) (messages : Messages) (state : MachineState) :
    runOnlyEvents oracle (beforeEtaTailEvents messages) state =
      runBeforeEtaTail oracle messages state := by
  let ids : List ChallengeId :=
    List.ofFn fun coordinate : Fin 10 => .zerocheckPoint coordinate
  have zeroEvents :
      (List.ofFn fun coordinate : Fin 10 =>
        challengeEvent messages (.zerocheckPoint coordinate)) =
      ids.map (fun id => MachineEvent.challenge id
        (messages.challengeUse id)) := by
    rw [List.map_ofFn]
    rfl
  rw [beforeEtaTailEvents, runOnlyEvents_append,
    runOnlyEvents_append, zeroEvents]
  simp_rw [runOnlyEvents_challengeList oracle messages.challengeUse ids]
  dsimp only [ids]
  cases thetaRun : sampleOnly oracle .theta
      (absorb oracle (absorb oracle state .constraintRegistry) .helperSum) with
  | none =>
      simp [runBeforeEtaTail, runOnlyEvents, runOnlyEvent, challengeEvent,
        thetaRun]
  | some afterTheta =>
      cases pointRun : sampleIds oracle ids afterTheta with
      | none =>
          dsimp only [ids] at pointRun
          simp [runBeforeEtaTail, runOnlyEvents, runOnlyEvent, challengeEvent,
            thetaRun, pointRun]
      | some afterPoint =>
          dsimp only [ids] at pointRun
          cases muRun : sampleOnly oracle .mu afterPoint with
          | none =>
              simp [runBeforeEtaTail, runOnlyEvents, runOnlyEvent,
                challengeEvent, thetaRun, pointRun, muRun]
          | some afterMu =>
              simp [runBeforeEtaTail, runOnlyEvents, runOnlyEvent,
                challengeEvent, thetaRun, pointRun, muRun]

/-- The event-list presentation computes exactly the pre-eta state used by
the mathematical Fiat--Shamir schedule. -/
theorem runOnlyEvents_beforeEtaFullEvents
    (table : FixedOracleTable) (messages : Messages) :
    runOnlyEvents (tableHashOracle table) (beforeEtaFullEvents table messages)
        initialState =
      stateBeforeEta (semanticPreEtaOf table messages) := by
  rw [beforeEtaFullEvents, runOnlyEvents_append, runOnlyEvents_append]
  simp_rw [runOnlyEvents_beforeEtaTailEvents]
  simp only [prefixBeforeC1, runOnlyEvents, runOnlyEvent, challengeEvent,
    runBeforeEtaTail, stateBeforeEta, semanticPreEtaOf, fixedPrefixBeforeC1]
  let oracle := tableHashOracle table
  let beforeC1 := fixedPrefixBeforeC1
    (semanticPreEtaOf table messages).publicPrefix
  let afterC1 := absorb oracle beforeC1
    (.c1Root messages.c1Root
      (publicRootSalt oracle messages.context c1TreeTag))
  cases lambdaRun : sampleOnly oracle .lambda afterC1 with
  | none =>
      have lambdaRun' := lambdaRun
      simp only [oracle, afterC1, beforeC1, semanticPreEtaOf,
        fixedPrefixBeforeC1] at lambdaRun'
      simp [lambdaRun']
  | some afterLambda =>
      have lambdaRun' := lambdaRun
      simp only [oracle, afterC1, beforeC1, semanticPreEtaOf,
        fixedPrefixBeforeC1] at lambdaRun'
      cases chiRun : sampleOnly oracle .chi afterLambda with
      | none =>
          have chiRun' := chiRun
          simp only [oracle] at chiRun'
          simp [lambdaRun', chiRun']
      | some afterChi =>
          have chiRun' := chiRun
          simp only [oracle] at chiRun'
          simp [lambdaRun', chiRun']

/-- Work erasure changes only grinding events, hence it is definitionally
irrelevant on a causal absorb/challenge/check segment. -/
theorem runMachineEventsWorkErased_eq_of_causal
    (table : FixedOracleTable) (events : List MachineEvent)
    (state : EvalState)
    (causal : ∀ event ∈ events, CausalMachineEvent event) :
    runMachineEventsWorkErased table events state =
      runMachineEvents table events state := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      have headCausal : CausalMachineEvent event := causal event (by simp)
      have tailCausal : ∀ tail ∈ rest, CausalMachineEvent tail := by
        intro tail member
        exact causal tail (by simp [member])
      cases event with
      | absorb payload =>
          simp only [runMachineEventsWorkErased, runMachineEvents,
            runMachineEventWorkErased, runMachineEvent]
          congr 1
          funext next
          exact ih next tailCausal
      | challenge id use =>
          simp only [runMachineEventsWorkErased, runMachineEvents,
            runMachineEventWorkErased, runMachineEvent]
          congr 1
          funext next
          exact ih next tailCausal
      | grind stage choice => exact False.elim headCausal
      | check checkpoint =>
          simp only [runMachineEventsWorkErased, runMachineEvents,
            runMachineEventWorkErased, runMachineEvent]
          exact ih state tailCausal

/-- A successful public-root-salt table step returns the totalized oracle's
literal salt and leaves the duplex digest unchanged. -/
theorem rootSaltStep_matches_tableHashOracle
    (table : FixedOracleTable) (state next : EvalState)
    (context : Context) (treeTag : UInt8) (salt : Digest256)
    (run : rootSaltStep table state context treeTag = some (salt, next)) :
    salt = publicRootSalt (tableHashOracle table) context treeTag ∧
      next.digest = state.digest := by
  obtain ⟨found, _calls, digestEq⟩ := query_step_appends_one table state next
    (.publicRootSalt context treeTag) salt run
  constructor
  · exact (tableHashOracle_answer_of_lookup table _ salt found).symm
  · simpa [RawQueryRole.nextDigest] using digestEq

/-- The three exact states and runs cut out of the accepted pre-q16 prefix. -/
structure SemanticExecutionSegments
    (table : FixedOracleTable) (messages : Messages)
    (afterC2 prefixState : EvalState) where
  beforeEta : EvalState
  afterEta : EvalState
  afterSemantic : EvalState
  beforeEtaRun : runMachineEventsWorkErased table
    (beforeEtaTailEvents messages) afterC2 = some beforeEta
  etaRun : runMachineEventsWorkErased table
    [challengeEvent messages .eta] beforeEta = some afterEta
  semanticRun : runMachineEventsWorkErased table
    (semanticEvents messages) afterEta = some afterSemantic
  afterSemanticRun : runMachineEventsWorkErased table
    (afterSemanticTailEvents messages) afterSemantic = some prefixState

theorem complete_evaluator_exposes_semantic_segments
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace)
    (run : CompleteWorkErasedEvaluatorRun table tape rawTrace) :
    Nonempty (SemanticExecutionSegments table tape.messages run.afterC2
      run.prefixState) := by
  have factored : runMachineEventsWorkErased table
      (beforeEtaTailEvents tape.messages ++
        [challengeEvent tape.messages .eta] ++
          semanticEvents tape.messages ++
            afterSemanticTailEvents tape.messages)
      run.afterC2 = some run.prefixState := by
    rw [← prefixAfterC2_exact_semantic_factorization]
    exact run.beforeQ16Run
  obtain ⟨beforeEta, beforeEtaRun, restRun⟩ :=
    (run_machine_events_work_erased_append_iff table
      (beforeEtaTailEvents tape.messages)
      ([challengeEvent tape.messages .eta] ++
        semanticEvents tape.messages ++ afterSemanticTailEvents tape.messages)
      run.afterC2 run.prefixState).mp factored
  obtain ⟨afterEta, etaRun, restRun⟩ :=
    (run_machine_events_work_erased_append_iff table
      [challengeEvent tape.messages .eta]
      (semanticEvents tape.messages ++ afterSemanticTailEvents tape.messages)
      beforeEta run.prefixState).mp restRun
  obtain ⟨afterSemantic, semanticRun, afterSemanticRun⟩ :=
    (run_machine_events_work_erased_append_iff table
      (semanticEvents tape.messages) (afterSemanticTailEvents tape.messages)
      afterEta run.prefixState).mp restRun
  exact ⟨⟨beforeEta, afterEta, afterSemantic, beforeEtaRun, etaRun,
    semanticRun, afterSemanticRun⟩⟩

theorem semantic_segments_decode_from_final_ledger
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace)
    (evaluator : CompleteWorkErasedEvaluatorRun table tape rawTrace)
    (segments : SemanticExecutionSegments table tape.messages
      evaluator.afterC2 evaluator.prefixState)
    (finalDecoded : StateSamplesDecodeAs tape.messages evaluator.finalState) :
    SamplesDecodeAs tape.messages.challengeValue segments.afterSemantic := by
  have toPrefix := machine_events_work_erased_samples_included table
    (afterSemanticTailEvents tape.messages) segments.afterSemantic
      evaluator.prefixState segments.afterSemanticRun
  have throughQ16 := run_q16_preserves_prior_samples table
    evaluator.prefixState evaluator.afterQ16 (q16TapeOfSearch tape.search)
      evaluator.q16Run
  have afterQ16 := machine_events_work_erased_samples_included table
    (afterAcceptedQueryScan tape.messages) evaluator.afterQ16
      evaluator.finalState evaluator.afterQ16Run
  have included := samples_included_trans toPrefix
    (samples_included_trans throughQ16 afterQ16)
  have decodedAtSegment := state_samples_decode_of_included tape.messages
    segments.afterSemantic evaluator.finalState included finalDecoded
  simpa [StateSamplesDecodeAs, SamplesDecodeAs] using decodedAtSegment

theorem evaluator_afterPhase_samples_included_final
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace)
    (evaluator : CompleteWorkErasedEvaluatorRun table tape rawTrace) :
    AspisK1.V7Tag73CheckedRefinementFullFutureFreePath.SamplesIncluded
      evaluator.afterPhaseChallenges evaluator.finalState := by
  have saltPreserved := root_salt_step_preserves_samples_and_candidates table
    evaluator.afterPhaseChallenges evaluator.withC2Salt
      tape.messages.context c2TreeTag evaluator.c2Salt evaluator.c2SaltRun
  have absorbPreserved := absorb_step_preserves_samples_and_candidates table
    evaluator.withC2Salt evaluator.afterC2
      (.c2Root tape.messages.c2.root evaluator.c2Salt) evaluator.c2AbsorbRun
  have phaseToAfterC2 :
      AspisK1.V7Tag73CheckedRefinementFullFutureFreePath.SamplesIncluded
        evaluator.afterPhaseChallenges evaluator.afterC2 := by
    intro record member
    rw [absorbPreserved.1, saltPreserved.1]
    exact member
  have afterC2ToPrefix := machine_events_work_erased_samples_included table
    (prefixAfterC2 tape.messages) evaluator.afterC2 evaluator.prefixState
      evaluator.beforeQ16Run
  have throughQ16 := run_q16_preserves_prior_samples table
    evaluator.prefixState evaluator.afterQ16 (q16TapeOfSearch tape.search)
      evaluator.q16Run
  have afterQ16 := machine_events_work_erased_samples_included table
    (afterAcceptedQueryScan tape.messages) evaluator.afterQ16
      evaluator.finalState evaluator.afterQ16Run
  exact samples_included_trans phaseToAfterC2
    (samples_included_trans afterC2ToPrefix
      (samples_included_trans throughQ16 afterQ16))

theorem evaluator_afterLambda_samples_included_final
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace)
    (evaluator : CompleteWorkErasedEvaluatorRun table tape rawTrace) :
    AspisK1.V7Tag73CheckedRefinementFullFutureFreePath.SamplesIncluded
      evaluator.afterLambda evaluator.finalState := by
  have chiIncluded := machine_event_work_erased_samples_included table
    evaluator.afterLambda evaluator.afterPhaseChallenges
      (challengeEvent tape.messages .chi) evaluator.chiRun
  exact samples_included_trans chiIncluded
    (evaluator_afterPhase_samples_included_final table tape rawTrace evaluator)

theorem evaluator_beforeC1_samples_included_final
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace)
    (evaluator : CompleteWorkErasedEvaluatorRun table tape rawTrace) :
    AspisK1.V7Tag73CheckedRefinementFullFutureFreePath.SamplesIncluded
      evaluator.beforeC1 evaluator.finalState := by
  have saltPreserved := root_salt_step_preserves_samples_and_candidates table
    evaluator.beforeC1 evaluator.withC1Salt tape.messages.context c1TreeTag
      evaluator.c1Salt evaluator.c1SaltRun
  have absorbPreserved := absorb_step_preserves_samples_and_candidates table
    evaluator.withC1Salt evaluator.afterC1
      (.c1Root tape.messages.c1Root evaluator.c1Salt) evaluator.c1AbsorbRun
  have lambdaIncluded := machine_event_work_erased_samples_included table
    evaluator.afterC1 evaluator.afterLambda
      (challengeEvent tape.messages .lambda) evaluator.lambdaRun
  have beforeToLambda :
      AspisK1.V7Tag73CheckedRefinementFullFutureFreePath.SamplesIncluded
        evaluator.beforeC1 evaluator.afterLambda := by
    intro record member
    apply lambdaIncluded
    rw [absorbPreserved.1, saltPreserved.1]
    exact member
  exact samples_included_trans beforeToLambda
    (evaluator_afterLambda_samples_included_final table tape rawTrace evaluator)

theorem semantic_beforeEta_samples_included_final
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace)
    (evaluator : CompleteWorkErasedEvaluatorRun table tape rawTrace)
    (segments : SemanticExecutionSegments table tape.messages
      evaluator.afterC2 evaluator.prefixState) :
    AspisK1.V7Tag73CheckedRefinementFullFutureFreePath.SamplesIncluded
      segments.beforeEta evaluator.finalState := by
  have etaIncluded := machine_events_work_erased_samples_included table
    [challengeEvent tape.messages .eta] segments.beforeEta segments.afterEta
      segments.etaRun
  have semanticIncluded := machine_events_work_erased_samples_included table
    (semanticEvents tape.messages) segments.afterEta segments.afterSemantic
      segments.semanticRun
  have tailIncluded := machine_events_work_erased_samples_included table
    (afterSemanticTailEvents tape.messages) segments.afterSemantic
      evaluator.prefixState segments.afterSemanticRun
  have throughQ16 := run_q16_preserves_prior_samples table
    evaluator.prefixState evaluator.afterQ16 (q16TapeOfSearch tape.search)
      evaluator.q16Run
  have afterQ16 := machine_events_work_erased_samples_included table
    (afterAcceptedQueryScan tape.messages) evaluator.afterQ16
      evaluator.finalState evaluator.afterQ16Run
  exact samples_included_trans etaIncluded
    (samples_included_trans semanticIncluded
      (samples_included_trans tailIncluded
        (samples_included_trans throughQ16 afterQ16)))

theorem causalSamplesDecodeAs_of_included_final
    (messages : Messages) (state final : EvalState)
    (included :
      AspisK1.V7Tag73CheckedRefinementFullFutureFreePath.SamplesIncluded
        state final)
    (decoded : StateSamplesDecodeAs messages final) :
    SamplesDecodeAs messages.challengeValue state := by
  have atState := state_samples_decode_of_included messages state final
    included decoded
  simpa [StateSamplesDecodeAs, SamplesDecodeAs] using atState

theorem prefixBeforeC1_events_are_causal (messages : Messages) :
    ∀ event ∈ prefixBeforeC1 messages, CausalMachineEvent event := by
  simp [prefixBeforeC1, CausalMachineEvent]

theorem beforeEtaTail_events_are_causal (messages : Messages) :
    ∀ event ∈ beforeEtaTailEvents messages, CausalMachineEvent event := by
  simp [beforeEtaTailEvents, challengeEvent, CausalMachineEvent]

/-- The literal accepted evaluator prefix constructs the exact machine state
returned by the mathematical `stateBeforeEta` computation.  The two salt
queries are bridged at their real non-advancing positions. -/
theorem complete_evaluator_constructs_stateBeforeEta
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace)
    (evaluator : CompleteWorkErasedEvaluatorRun table tape rawTrace)
    (segments : SemanticExecutionSegments table tape.messages
      evaluator.afterC2 evaluator.prefixState)
    (finalDecoded : StateSamplesDecodeAs tape.messages evaluator.finalState) :
    ∃ machineBeforeEta,
      stateBeforeEta (semanticPreEtaOf table tape.messages) =
        some machineBeforeEta ∧
      machineBeforeEta.digest = segments.beforeEta.digest := by
  let oracle := tableHashOracle table
  let valueAt := tape.messages.challengeValue
  have beforeDecoded := causalSamplesDecodeAs_of_included_final tape.messages
    evaluator.beforeC1 evaluator.finalState
      (evaluator_beforeC1_samples_included_final table tape rawTrace evaluator)
      finalDecoded
  have afterLambdaDecoded := causalSamplesDecodeAs_of_included_final
    tape.messages evaluator.afterLambda evaluator.finalState
      (evaluator_afterLambda_samples_included_final table tape rawTrace
        evaluator) finalDecoded
  have afterPhaseDecoded := causalSamplesDecodeAs_of_included_final
    tape.messages evaluator.afterPhaseChallenges evaluator.finalState
      (evaluator_afterPhase_samples_included_final table tape rawTrace
        evaluator) finalDecoded
  have beforeEtaDecoded := causalSamplesDecodeAs_of_included_final
    tape.messages segments.beforeEta evaluator.finalState
      (semantic_beforeEta_samples_included_final table tape rawTrace evaluator
        segments) finalDecoded

  have prefixCausal := prefixBeforeC1_events_are_causal tape.messages
  have prefixStandard : runMachineEvents table
      (prefixBeforeC1 tape.messages) initialEvalState =
        some evaluator.beforeC1 := by
    rw [← runMachineEventsWorkErased_eq_of_causal table _ _ prefixCausal]
    exact evaluator.beforeC1Run
  have prefixAgreement := causalDecoderAgreement_of_final_ledger table valueAt
    (prefixBeforeC1 tape.messages) initialEvalState evaluator.beforeC1
      prefixCausal prefixStandard beforeDecoded
  obtain ⟨machineBeforeC1, prefixHash, beforeC1Aligned⟩ :=
    runMachineEvents_match_runHashEvents table valueAt
      (prefixBeforeC1 tape.messages) initialEvalState evaluator.beforeC1
      initialState prefixAgreement rfl prefixStandard

  obtain ⟨c1SaltEq, c1DigestEq⟩ := rootSaltStep_matches_tableHashOracle table
    evaluator.beforeC1 evaluator.withC1Salt tape.messages.context c1TreeTag
      evaluator.c1Salt evaluator.c1SaltRun
  have c1AbsorbRun : absorbStep table evaluator.withC1Salt
      (.c1Root tape.messages.c1Root
        (publicRootSalt oracle tape.messages.context c1TreeTag)) =
        some evaluator.afterC1 := by
    simpa [oracle, c1SaltEq] using evaluator.c1AbsorbRun
  let machineAfterC1 := absorb oracle machineBeforeC1
    (.c1Root tape.messages.c1Root
      (publicRootSalt oracle tape.messages.context c1TreeTag))
  have withC1Aligned : machineBeforeC1.digest =
      evaluator.withC1Salt.digest := beforeC1Aligned.trans c1DigestEq.symm
  have afterC1Aligned : machineAfterC1.digest = evaluator.afterC1.digest :=
    absorbStep_matches_tableHashOracle_digest table evaluator.withC1Salt
      evaluator.afterC1 machineBeforeC1
      (.c1Root tape.messages.c1Root
        (publicRootSalt oracle tape.messages.context c1TreeTag))
      withC1Aligned c1AbsorbRun

  have lambdaStandard : runMachineEvent table evaluator.afterC1
      (challengeEvent tape.messages .lambda) = some evaluator.afterLambda := by
    simpa [challengeEvent, runMachineEventWorkErased, runMachineEvent] using
      evaluator.lambdaRun
  have lambdaAgreement := eventDecoderAgreement_of_success table valueAt
    (challengeEvent tape.messages .lambda) evaluator.afterC1
      evaluator.afterLambda (by simp [challengeEvent, CausalMachineEvent])
      lambdaStandard afterLambdaDecoded
  obtain ⟨machineAfterLambda, lambdaHash, afterLambdaAligned⟩ :=
    runMachineEvent_matches_runHashEvent table valueAt
      (challengeEvent tape.messages .lambda) evaluator.afterC1
      evaluator.afterLambda machineAfterC1
      (by simp [challengeEvent, CausalMachineEvent]) lambdaAgreement
      afterC1Aligned lambdaStandard

  have chiStandard : runMachineEvent table evaluator.afterLambda
      (challengeEvent tape.messages .chi) =
        some evaluator.afterPhaseChallenges := by
    simpa [challengeEvent, runMachineEventWorkErased, runMachineEvent] using
      evaluator.chiRun
  have chiAgreement := eventDecoderAgreement_of_success table valueAt
    (challengeEvent tape.messages .chi) evaluator.afterLambda
      evaluator.afterPhaseChallenges
      (by simp [challengeEvent, CausalMachineEvent]) chiStandard
      afterPhaseDecoded
  obtain ⟨machineAfterChi, chiHash, afterChiAligned⟩ :=
    runMachineEvent_matches_runHashEvent table valueAt
      (challengeEvent tape.messages .chi) evaluator.afterLambda
      evaluator.afterPhaseChallenges machineAfterLambda
      (by simp [challengeEvent, CausalMachineEvent]) chiAgreement
      afterLambdaAligned chiStandard

  obtain ⟨c2SaltEq, c2DigestEq⟩ := rootSaltStep_matches_tableHashOracle table
    evaluator.afterPhaseChallenges evaluator.withC2Salt tape.messages.context
      c2TreeTag evaluator.c2Salt evaluator.c2SaltRun
  have c2AbsorbRun : absorbStep table evaluator.withC2Salt
      (.c2Root tape.messages.c2.root
        (publicRootSalt oracle tape.messages.context c2TreeTag)) =
        some evaluator.afterC2 := by
    simpa [oracle, c2SaltEq] using evaluator.c2AbsorbRun
  let machineAfterC2 := absorb oracle machineAfterChi
    (.c2Root tape.messages.c2.root
      (publicRootSalt oracle tape.messages.context c2TreeTag))
  have withC2Aligned : machineAfterChi.digest = evaluator.withC2Salt.digest :=
    afterChiAligned.trans c2DigestEq.symm
  have afterC2Aligned : machineAfterC2.digest = evaluator.afterC2.digest :=
    absorbStep_matches_tableHashOracle_digest table evaluator.withC2Salt
      evaluator.afterC2 machineAfterChi
      (.c2Root tape.messages.c2.root
        (publicRootSalt oracle tape.messages.context c2TreeTag))
      withC2Aligned c2AbsorbRun

  have tailCausal := beforeEtaTail_events_are_causal tape.messages
  have tailStandard : runMachineEvents table
      (beforeEtaTailEvents tape.messages) evaluator.afterC2 =
        some segments.beforeEta := by
    rw [← runMachineEventsWorkErased_eq_of_causal table _ _ tailCausal]
    exact segments.beforeEtaRun
  have tailAgreement := causalDecoderAgreement_of_final_ledger table valueAt
    (beforeEtaTailEvents tape.messages) evaluator.afterC2 segments.beforeEta
      tailCausal tailStandard beforeEtaDecoded
  obtain ⟨machineBeforeEta, tailHash, beforeEtaAligned⟩ :=
    runMachineEvents_match_runHashEvents table valueAt
      (beforeEtaTailEvents tape.messages) evaluator.afterC2
      segments.beforeEta machineAfterC2 tailAgreement afterC2Aligned
      tailStandard

  have prefixHash' : runHashEvents oracle valueAt
      (prefixBeforeC1 tape.messages) initialState =
        some machineBeforeC1 := by
    simpa [oracle] using prefixHash
  have prefixOnly := runHashEvents_success_implies_runOnlyEvents oracle valueAt
    (prefixBeforeC1 tape.messages) initialState machineBeforeC1 prefixHash'
  have prefixExact : runOnlyEvents oracle (prefixBeforeC1 tape.messages)
      initialState = some
        (fixedPrefixBeforeC1 (semanticPreEtaOf table tape.messages).publicPrefix) := by
    rfl
  have machineBeforeC1Eq : machineBeforeC1 =
      fixedPrefixBeforeC1 (semanticPreEtaOf table tape.messages).publicPrefix :=
    Option.some.inj (prefixOnly.symm.trans prefixExact)

  have lambdaHash' : runHashEvent oracle valueAt machineAfterC1
      (challengeEvent tape.messages .lambda) =
        some machineAfterLambda := by
    simpa [oracle] using lambdaHash
  have lambdaListHash : runHashEvents oracle valueAt
      [challengeEvent tape.messages .lambda] machineAfterC1 =
        some machineAfterLambda := by
    simpa [runHashEvents] using lambdaHash'
  have lambdaOnlyList := runHashEvents_success_implies_runOnlyEvents oracle
    valueAt [challengeEvent tape.messages .lambda] machineAfterC1
      machineAfterLambda lambdaListHash
  have lambdaOnly : sampleOnly oracle .lambda machineAfterC1 =
      some machineAfterLambda := by
    simpa [runOnlyEvents, runOnlyEvent, challengeEvent] using lambdaOnlyList

  have chiHash' : runHashEvent oracle valueAt machineAfterLambda
      (challengeEvent tape.messages .chi) = some machineAfterChi := by
    simpa [oracle] using chiHash
  have chiListHash : runHashEvents oracle valueAt
      [challengeEvent tape.messages .chi] machineAfterLambda =
        some machineAfterChi := by
    simpa [runHashEvents] using chiHash'
  have chiOnlyList := runHashEvents_success_implies_runOnlyEvents oracle valueAt
    [challengeEvent tape.messages .chi] machineAfterLambda machineAfterChi
      chiListHash
  have chiOnly : sampleOnly oracle .chi machineAfterLambda =
      some machineAfterChi := by
    simpa [runOnlyEvents, runOnlyEvent, challengeEvent] using chiOnlyList

  have tailHash' : runHashEvents oracle valueAt
      (beforeEtaTailEvents tape.messages) machineAfterC2 =
        some machineBeforeEta := by
    simpa [oracle] using tailHash
  have tailOnly := runHashEvents_success_implies_runOnlyEvents oracle valueAt
    (beforeEtaTailEvents tape.messages) machineAfterC2 machineBeforeEta
      tailHash'
  rw [runOnlyEvents_beforeEtaTailEvents] at tailOnly

  have stateRun : stateBeforeEta (semanticPreEtaOf table tape.messages) =
      some machineBeforeEta := by
    unfold stateBeforeEta
    dsimp only [semanticPreEtaOf]
    have machineBeforeC1Eq' : machineBeforeC1 = fixedPrefixBeforeC1
        { oracle := tableHashOracle table
          context := tape.messages.context
          c1Root := tape.messages.c1Root
          initialClaim := tape.messages.initialClaim } := by
      simpa [semanticPreEtaOf] using machineBeforeC1Eq
    rw [← machineBeforeC1Eq']
    change (do
      let afterLambda <- sampleOnly oracle .lambda machineAfterC1
      let afterChi <- sampleOnly oracle .chi afterLambda
      runBeforeEtaTail oracle tape.messages
        (absorb oracle afterChi
          (.c2Root tape.messages.c2.root
            (publicRootSalt oracle tape.messages.context c2TreeTag)))) =
      some machineBeforeEta
    rw [lambdaOnly]
    change (do
      let afterChi <- sampleOnly oracle .chi machineAfterLambda
      runBeforeEtaTail oracle tape.messages
        (absorb oracle afterChi
          (.c2Root tape.messages.c2.root
            (publicRootSalt oracle tape.messages.context c2TreeTag)))) =
      some machineBeforeEta
    rw [chiOnly]
    change runBeforeEtaTail oracle tape.messages machineAfterC2 =
      some machineBeforeEta
    exact tailOnly
  exact ⟨machineBeforeEta, stateRun, beforeEtaAligned⟩

theorem semantic_segments_have_exact_challenge_values
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace)
    (evaluator : CompleteWorkErasedEvaluatorRun table tape rawTrace)
    (segments : SemanticExecutionSegments table tape.messages
      evaluator.afterC2 evaluator.prefixState)
    (finalDecoded : StateSamplesDecodeAs tape.messages evaluator.finalState) :
    (decodeTagQM31ExactLE (tape.messages.challengeValue .eta) =
        some (exactChallengeValue tape.messages.challengeValue .eta)) ∧
      ∀ round : Fin 10,
        decodeTagQM31ExactLE
            (tape.messages.challengeValue (.semantic round)) =
          some (exactChallengeValue tape.messages.challengeValue
            (.semantic round)) := by
  have segmentDecoded := semantic_segments_decode_from_final_ledger table tape
    rawTrace evaluator segments finalDecoded
  have etaCausal : ∀ event ∈ [challengeEvent tape.messages .eta],
      CausalMachineEvent event := by simp [challengeEvent, CausalMachineEvent]
  have etaStandard : runMachineEvents table
      [challengeEvent tape.messages .eta] segments.beforeEta =
        some segments.afterEta := by
    rw [← runMachineEventsWorkErased_eq_of_causal table _ _ etaCausal]
    exact segments.etaRun
  have semanticCausal := production_semantic_events_are_causal tape.messages
  have semanticStandard : runMachineEvents table
      (semanticEvents tape.messages) segments.afterEta =
        some segments.afterSemantic := by
    rw [← runMachineEventsWorkErased_eq_of_causal table _ _ semanticCausal]
    exact segments.semanticRun
  have afterEtaIncluded := causalMachineEvents_samples_included table
    (semanticEvents tape.messages) segments.afterEta segments.afterSemantic
      semanticCausal semanticStandard
  have decodedAfterEta := samplesDecodeAs_of_included
    tape.messages.challengeValue segments.afterEta segments.afterSemantic
      afterEtaIncluded segmentDecoded
  have etaExists := challenge_value_has_exact_tower_of_event_mem table
    tape.messages.challengeValue [challengeEvent tape.messages .eta]
      segments.beforeEta segments.afterEta .eta
      (tape.messages.challengeUse .eta) etaCausal (by simp [challengeEvent])
      etaStandard decodedAfterEta
  have etaDecode : decodeTagQM31ExactLE
      (tape.messages.challengeValue .eta) =
        some (exactChallengeValue tape.messages.challengeValue .eta) := by
    obtain ⟨value, valueRun⟩ := etaExists
    simp [exactChallengeValue, valueRun]
  refine ⟨etaDecode, ?_⟩
  intro round
  obtain ⟨value, valueRun⟩ := challenge_value_has_exact_tower_of_event_mem
    table tape.messages.challengeValue (semanticEvents tape.messages)
      segments.afterEta segments.afterSemantic (.semantic round)
      (tape.messages.challengeUse (.semantic round)) semanticCausal
      (by simpa [challengeEvent] using
        production_semantic_challenge_mem tape.messages round)
      semanticStandard segmentDecoded
  simp [exactChallengeValue, valueRun]

/-- The accepted eta occurrence used the deployed nonzero sampler, so its
canonical exact-tower value is nonzero. -/
theorem semantic_segments_eta_ne_zero
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace)
    (evaluator : CompleteWorkErasedEvaluatorRun table tape rawTrace)
    (segments : SemanticExecutionSegments table tape.messages
      evaluator.afterC2 evaluator.prefixState)
    (finalDecoded : StateSamplesDecodeAs tape.messages evaluator.finalState) :
    exactChallengeValue tape.messages.challengeValue .eta ≠ 0 := by
  have segmentDecoded := semantic_segments_decode_from_final_ledger table tape
    rawTrace evaluator segments finalDecoded
  have etaCausal : ∀ event ∈ [challengeEvent tape.messages .eta],
      CausalMachineEvent event := by simp [challengeEvent, CausalMachineEvent]
  have etaStandard : runMachineEvents table
      [challengeEvent tape.messages .eta] segments.beforeEta =
        some segments.afterEta := by
    rw [← runMachineEventsWorkErased_eq_of_causal table _ _ etaCausal]
    exact segments.etaRun
  have semanticCausal := production_semantic_events_are_causal tape.messages
  have semanticStandard : runMachineEvents table
      (semanticEvents tape.messages) segments.afterEta =
        some segments.afterSemantic := by
    rw [← runMachineEventsWorkErased_eq_of_causal table _ _ semanticCausal]
    exact segments.semanticRun
  have afterEtaIncluded := causalMachineEvents_samples_included table
    (semanticEvents tape.messages) segments.afterEta segments.afterSemantic
      semanticCausal semanticStandard
  have decodedAfterEta := samplesDecodeAs_of_included
    tape.messages.challengeValue segments.afterEta segments.afterSemantic
      afterEtaIncluded segmentDecoded
  obtain ⟨blocks, recordMember⟩ :=
    challenge_record_in_final_of_event_mem table
      [challengeEvent tape.messages .eta] segments.beforeEta segments.afterEta
      .eta (tape.messages.challengeUse .eta) etaCausal
      (by simp [challengeEvent]) etaStandard
  have parameterDecoded := decodedAfterEta { id := .eta, blocks := blocks }
    recordMember
  have nonzeroRun : decodeNonzeroExact blocks =
      some (tape.messages.challengeValue .eta) := by
    simpa [decodeChallengeParameter, samplerMode] using parameterDecoded
  have etaDecode :=
    (semantic_segments_have_exact_challenge_values table tape rawTrace evaluator
      segments finalDecoded).1
  exact exactChallengeValue_ne_zero_of_nonzero_run
    tape.messages.challengeValue .eta blocks nonzeroRun etaDecode

theorem ofFn_prefix_append_drop
    {A : Type*} (values : Fin 10 -> A) (round : Fin 10) :
    (List.ofFn fun earlier : Fin (round.val + 1) =>
        values ⟨earlier.val, by omega⟩) ++
      (List.ofFn values).drop (round.val + 1) = List.ofFn values := by
  fin_cases round <;> simp

/-- Exact accepted transcript data obtained from the compact fixed-field
messages. -/
structure ExactCompactSemanticReplay
    (preEta : SemanticPreEta) (eta : QM31Exact)
    (fields : FixedFieldView QM31Exact) (point : Fin 10 → QM31Exact) : Prop where
  replay : ExactSemanticReplay preEta eta
    (compactSemanticMessages fields point) point
  etaNonzero : eta ≠ 0

def ExactCompactSemanticReplay.acceptedRun
    {preEta : SemanticPreEta} {eta : QM31Exact}
    {fields : FixedFieldView QM31Exact} {point : Fin 10 → QM31Exact}
    (certificate : ExactCompactSemanticReplay preEta eta fields point) :
    AcceptedRun tag73SemanticSchedule :=
  acceptedRunOfExactSemanticReplay certificate.replay

def ExactCompactSemanticReplay.compactEvidence
    {preEta : SemanticPreEta} {eta : QM31Exact}
    {fields : FixedFieldView QM31Exact} {point : Fin 10 → QM31Exact}
    (certificate : ExactCompactSemanticReplay preEta eta fields point) :
    CompactAcceptedRunEvidence fields certificate.acceptedRun where
  messages := rfl
  etaNonzero := certificate.etaNonzero

/-- The checked fixed-table evaluator, canonical fixed-field decoder, and
literal transcript schedule construct the exact future-free accepted run
consumed by K1.5. -/
theorem complete_evaluator_constructs_exactSemanticReplay
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace)
    (evaluator : CompleteWorkErasedEvaluatorRun table tape rawTrace)
    (segments : SemanticExecutionSegments table tape.messages
      evaluator.afterC2 evaluator.prefixState)
    (finalDecoded : StateSamplesDecodeAs tape.messages evaluator.finalState)
    (decoded : Fin 641 -> QM31Exact)
    (fixedDecode : FixedFieldDecodeExact (rawOfMessages tape.messages) decoded) :
    ExactSemanticReplay (semanticPreEtaOf table tape.messages)
      (exactChallengeValue tape.messages.challengeValue .eta)
      (compactSemanticMessages (decodedFixedFieldView decoded)
        (fun round => exactChallengeValue tape.messages.challengeValue
          (.semantic round)))
      (fun round => exactChallengeValue tape.messages.challengeValue
        (.semantic round)) := by
  let exactValue := exactChallengeValue tape.messages.challengeValue
  let point : Fin 10 -> QM31Exact :=
    fun round => exactValue (.semantic round)
  let messages := compactSemanticMessages (decodedFixedFieldView decoded) point
  have segmentDecoded := semantic_segments_decode_from_final_ledger table tape
    rawTrace evaluator segments finalDecoded
  obtain ⟨etaDecode, semanticDecode⟩ :=
    semantic_segments_have_exact_challenge_values table tape rawTrace evaluator
      segments finalDecoded
  obtain ⟨machineBeforeEta, stateRun, beforeEtaAligned⟩ :=
    complete_evaluator_constructs_stateBeforeEta table tape rawTrace evaluator
      segments finalDecoded

  have semanticCausal := production_semantic_events_are_causal tape.messages
  have semanticStandard : runMachineEvents table
      (semanticEvents tape.messages) segments.afterEta =
        some segments.afterSemantic := by
    rw [← runMachineEventsWorkErased_eq_of_causal table _ _ semanticCausal]
    exact segments.semanticRun
  have afterEtaIncluded := causalMachineEvents_samples_included table
    (semanticEvents tape.messages) segments.afterEta segments.afterSemantic
      semanticCausal semanticStandard
  have afterEtaDecoded := samplesDecodeAs_of_included
    tape.messages.challengeValue segments.afterEta segments.afterSemantic
      afterEtaIncluded segmentDecoded
  have etaStandard : runMachineEvent table segments.beforeEta
      (challengeEvent tape.messages .eta) = some segments.afterEta := by
    simpa [runMachineEventsWorkErased, challengeEvent,
      runMachineEventWorkErased, runMachineEvent] using segments.etaRun
  have etaAgreement := eventDecoderAgreement_of_success table
    tape.messages.challengeValue (challengeEvent tape.messages .eta)
      segments.beforeEta segments.afterEta
      (by simp [challengeEvent, CausalMachineEvent]) etaStandard
      afterEtaDecoded
  obtain ⟨machineAfterEta, etaSample, afterEtaAligned⟩ :=
    runMachineChallenge_matches_sampleExactChallenge table .eta
      (tape.messages.challengeUse .eta) segments.beforeEta segments.afterEta
      machineBeforeEta (tape.messages.challengeValue .eta) (exactValue .eta)
      beforeEtaAligned etaStandard etaAgreement (by
        simpa [exactValue] using etaDecode)
  have etaRun : runEta (semanticPreEtaOf table tape.messages) =
      some (exactValue .eta, machineAfterEta) := by
    unfold runEta
    rw [stateRun]
    exact etaSample

  have semanticGenericRun : runMachineEvents table
      (semanticEventsForMessages tape.messages.challengeUse 0
        (List.ofFn messages)) segments.afterEta =
        some segments.afterSemantic := by
    rw [compact_semantic_events_are_production_events tape.messages decoded
      fixedDecode point]
    exact semanticStandard
  have fullRun := runMachineSemanticEvents_matches_runSemanticMessages table
    tape.messages.challengeUse tape.messages.challengeValue exactValue
    (by
      intro round
      simpa [exactValue, point] using semanticDecode round)
    0 (List.ofFn messages) (by simp) segments.afterEta
      segments.afterSemantic machineAfterEta
      (by simpa [exactValue] using afterEtaAligned) semanticGenericRun
      segmentDecoded
  obtain ⟨machineAfterSemantic, fullSemanticRun, _finalAligned⟩ := fullRun
  refine
    { etaRun := ⟨machineAfterEta, by simpa [exactValue] using etaRun⟩
      roundRun := ?_ }
  intro round
  have roundLt : round.val < 10 := by
    simpa [roundCount] using round.isLt
  let round10 : Fin 10 := ⟨round.val, roundLt⟩
  let messagePrefix : List (Degree27Message QM31Exact) :=
    List.ofFn fun earlier : Fin (round.val + 1) =>
      messages ⟨earlier.val, by omega⟩
  let messageSuffix := (List.ofFn messages).drop (round.val + 1)
  have decomposition : messagePrefix ++ messageSuffix =
      List.ofFn messages := by
    simpa [messagePrefix, messageSuffix, round10] using
      ofFn_prefix_append_drop messages round10
  have decomposedRun : runSemanticMessages (tableHashOracle table) 0
      (messagePrefix ++ messageSuffix) machineAfterEta =
        some (semanticValuesForMessages exactValue 0
          (messagePrefix ++ messageSuffix),
          machineAfterSemantic) := by
    rw [decomposition]
    exact fullSemanticRun
  have within : 0 + (messagePrefix ++ messageSuffix).length ≤ 10 := by
    rw [decomposition]
    simp
  obtain ⟨prefixState, prefixRun⟩ :=
    runSemanticMessages_exact_prefix_of_append (tableHashOracle table)
      exactValue 0 messagePrefix messageSuffix within machineAfterEta
        machineAfterSemantic decomposedRun
  refine ⟨prefixState, ?_⟩
  unfold runSemanticPrefix
  rw [etaRun]
  simp only [bind, Bind.bind, Option.bind, exactValue, if_pos rfl]
  change runSemanticMessages (tableHashOracle table) 0 messagePrefix
      machineAfterEta =
    some (List.ofFn (fun earlier : Fin (round.val + 1) =>
      point ⟨earlier.val, by omega⟩), prefixState)
  have valuesEq : semanticValuesForMessages exactValue 0 messagePrefix =
      List.ofFn (fun earlier : Fin (round.val + 1) =>
        point ⟨earlier.val, by omega⟩) := by
    simpa [messagePrefix, round10] using
      semanticValuesForMessages_ofFn_prefix exactValue messages round10
  rw [valuesEq] at prefixRun
  simpa only [messagePrefix, messages, point, exactValue, semanticPreEtaOf]
    using prefixRun

/-- The literal accepted evaluator constructs both the exact transcript replay
and the nonzero evidence required by the K1.5 compact accepted-run interface. -/
theorem complete_evaluator_constructs_exactCompactSemanticReplay
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace)
    (evaluator : CompleteWorkErasedEvaluatorRun table tape rawTrace)
    (segments : SemanticExecutionSegments table tape.messages
      evaluator.afterC2 evaluator.prefixState)
    (finalDecoded : StateSamplesDecodeAs tape.messages evaluator.finalState)
    (decoded : Fin 641 → QM31Exact)
    (fixedDecode : FixedFieldDecodeExact (rawOfMessages tape.messages) decoded) :
    ExactCompactSemanticReplay (semanticPreEtaOf table tape.messages)
      (exactChallengeValue tape.messages.challengeValue .eta)
      (decodedFixedFieldView decoded)
      (fun round => exactChallengeValue tape.messages.challengeValue
        (.semantic round)) := by
  exact {
    replay := complete_evaluator_constructs_exactSemanticReplay table tape
      rawTrace evaluator segments finalDecoded decoded fixedDecode
    etaNonzero := semantic_segments_eta_ne_zero table tape rawTrace evaluator
      segments finalDecoded }

#print axioms prefixAfterC2_exact_semantic_factorization
#print axioms production_semantic_events_are_causal
#print axioms runHashEvents_success_implies_runOnlyEvents
#print axioms runOnlyEvents_beforeEtaFullEvents
#print axioms runMachineEventsWorkErased_eq_of_causal
#print axioms complete_evaluator_exposes_semantic_segments
#print axioms semantic_segments_decode_from_final_ledger
#print axioms semantic_segments_have_exact_challenge_values
#print axioms complete_evaluator_constructs_stateBeforeEta
#print axioms complete_evaluator_constructs_exactSemanticReplay
#print axioms semantic_segments_eta_ne_zero
#print axioms complete_evaluator_constructs_exactCompactSemanticReplay

end

end AspisK1.V7Tag73AcceptedSemanticExecution
