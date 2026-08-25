import AspisFormal.K1.V7Tag73InteractiveExecution
import AspisFormal.K1.V7Tag73DeterministicRefinement

/-!
# Bridge from deterministic Tag-73 refinement to the interactive execution

The table-driven interactive execution must not assume that its table lookups
are covered.  This module derives that coverage from the already executable
work-erased deterministic refinement.  The proof is compositional: literal
absorbs, paired squeezes, work probes, event lists, root-salt calls, and q16
branches are related to their exact ancestor action lists.

There is no restore interface, trace-cover premise, acceptance predicate, or
extraction conclusion here.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73RefinementExecutionBridge

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73InteractiveExecution

/-! ## A small executable action runner -/

def runActionCore (table : FixedOracleTable) (bindings : FixedBindings)
    (core : RuntimeCore) (action : VerifierAction) : Option RuntimeCore := do
  let reply ← deriveReply table bindings core action
  applyActionWorkErased core action reply

def runActionCores (table : FixedOracleTable) (bindings : FixedBindings) :
    List VerifierAction → RuntimeCore → Option RuntimeCore
  | [], core => some core
  | action :: rest, core => do
      let next ← runActionCore table bindings core action
      runActionCores table bindings rest next

theorem run_action_cores_append
    (table : FixedOracleTable) (bindings : FixedBindings)
    (first second : List VerifierAction) (core final : RuntimeCore)
    (run : runActionCores table bindings (first ++ second) core = some final) :
    ∃ middle,
      runActionCores table bindings first core = some middle ∧
      runActionCores table bindings second middle = some final := by
  induction first generalizing core with
  | nil => exact ⟨core, rfl, run⟩
  | cons action rest ih =>
      rw [List.cons_append, runActionCores] at run
      obtain ⟨next, haction, hrest⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨middle, hfirst, hsecond⟩ := ih (core := next) hrest
      refine ⟨middle, ?_, hsecond⟩
      rw [runActionCores]
      exact Option.bind_eq_some_iff.mpr ⟨next, haction, hfirst⟩

theorem run_action_cores_append_of_runs
    (table : FixedOracleTable) (bindings : FixedBindings)
    (first second : List VerifierAction)
    (core middle final : RuntimeCore)
    (firstRun : runActionCores table bindings first core = some middle)
    (secondRun : runActionCores table bindings second middle = some final) :
    runActionCores table bindings (first ++ second) core = some final := by
  induction first generalizing core middle with
  | nil =>
      have coreEq : core = middle := by
        simpa [runActionCores] using firstRun
      subst middle
      exact secondRun
  | cons action rest ih =>
      rw [runActionCores] at firstRun
      obtain ⟨next, haction, hrest⟩ := Option.bind_eq_some_iff.mp firstRun
      rw [List.cons_append, runActionCores]
      apply Option.bind_eq_some_iff.mpr
      exact ⟨next, haction,
        ih (core := next) (middle := middle) hrest secondRun⟩

/-- A successful core run constructs the dependent trace directly; table
coverage is therefore a consequence, not a premise.  We deliberately do not
claim definitional equality to the particular recursive implementation
`buildTrace`, whose dependent proof fields are proof-irrelevant downstream. -/
theorem table_execution_trace_of_run_action_cores
    (table : FixedOracleTable) (bindings : FixedBindings)
    (actions : List VerifierAction) (core final : RuntimeCore)
    (run : runActionCores table bindings actions core = some final) :
    Nonempty (TableExecutionTrace table bindings core actions) := by
  induction actions generalizing core with
  | nil =>
      exact ⟨.done core⟩
  | cons action rest ih =>
      rw [runActionCores] at run
      obtain ⟨next, haction, hrest⟩ := Option.bind_eq_some_iff.mp run
      rw [runActionCore] at haction
      obtain ⟨reply, hreply, happly⟩ := Option.bind_eq_some_iff.mp haction
      obtain ⟨tail⟩ := ih (core := next) hrest
      exact ⟨.step reply hreply happly tail⟩

/-- Once the complete literal plan runner succeeds, the exact tape- and
table-indexed first-execution object exists without any coverage premise. -/
theorem concrete_first_execution_of_full_plan_run
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (final : RuntimeCore)
    (run : runActionCores table
      (FixedBindings.ofContext tape.messages.context)
      (fullPlan tape) initialCore = some final) :
    Nonempty (ConcreteFirstExecution table tape) := by
  obtain ⟨trace⟩ := table_execution_trace_of_run_action_cores table
    (FixedBindings.ofContext tape.messages.context)
    (fullPlan tape) initialCore final run
  exact ⟨⟨trace⟩⟩

/-! ## Primitive agreement with deterministic evaluation -/

def SameDigest (core : RuntimeCore) (state : EvalState) : Prop :=
  core.digest = state.digest

theorem absorb_action_agrees
    (table : FixedOracleTable) (bindings : FixedBindings)
    (core : RuntimeCore) (state next : EvalState) (payload : Payload)
    (same : SameDigest core state)
    (run : absorbStep table state payload = some next) :
    runActionCore table bindings core (.absorb payload) =
      some { core with digest := next.digest } := by
  rw [absorbStep] at run
  obtain ⟨pair, hstep, hnext⟩ := Option.bind_eq_some_iff.mp run
  rcases pair with ⟨output, stepped⟩
  have steppedEquals : stepped = next := by
    simpa only [pure, Option.some.injEq] using hnext
  subst stepped
  obtain ⟨lookup, _, digest⟩ :=
    query_step_appends_one table state next (.absorb payload) output hstep
  have outputEquals : output = next.digest := by
    simpa only [RawQueryRole.nextDigest] using digest.symm
  subst output
  rw [runActionCore]
  apply Option.bind_eq_some_iff.mpr
  refine ⟨.single next.digest, ?_, rfl⟩
  change core.digest = state.digest at same
  have normalized : tableLookup table
      (bytes state.digest ++ [domAbsorb, payload.label] ++ payload.data) =
      some next.digest := by
    simpa only [RawQueryRole.input] using lookup
  simp only [deriveReply, actionInputs, lookupSingleInput]
  rw [same, normalized]
  rfl

theorem work_probe_action_agrees
    (table : FixedOracleTable) (bindings : FixedBindings)
    (core : RuntimeCore) (state next : EvalState)
    (stage : WorkStage) (nonce : NonceBytes) (kind : WorkProbeKind)
    (output : Digest256) (same : SameDigest core state)
    (run : grindProbe table state stage nonce = some (output, next)) :
    runActionCore table bindings core (.workProbe stage nonce kind) =
      some core := by
  obtain ⟨lookup, _, _⟩ :=
    query_step_appends_one table state next (.grind stage nonce) output run
  rw [runActionCore]
  apply Option.bind_eq_some_iff.mpr
  refine ⟨.single output, ?_, rfl⟩
  change core.digest = state.digest at same
  have normalized : tableLookup table
      (bytes state.digest ++ [domGrind] ++ bytes nonce) = some output := by
    simpa only [RawQueryRole.input] using lookup
  simp only [deriveReply, actionInputs, lookupSingleInput]
  rw [same, normalized]
  rfl

theorem squeeze_action_agrees
    (table : FixedOracleTable) (bindings : FixedBindings)
    (core : RuntimeCore) (state next : EvalState)
    (owner : SqueezeOwner) (block : Nat) (output : Digest256)
    (same : SameDigest core state)
    (run : squeezeStep table state owner block = some (output, next)) :
    runActionCore table bindings core (.squeezePair owner block) =
      some { core with digest := next.digest } := by
  obtain ⟨outputLookup, advanceLookup, _⟩ :=
    squeeze_step_emits_two_distinct_queries
      table state next owner block output run
  rw [runActionCore]
  apply Option.bind_eq_some_iff.mpr
  refine ⟨.squeeze output next.digest, ?_, rfl⟩
  change core.digest = state.digest at same
  simp only [deriveReply, actionInputs, domSqueeze, domAdvance]
  rw [same, outputLookup, advanceLookup]
  rfl

def squeezeActionsFrom (owner : SqueezeOwner) (first count : Nat) :
    List VerifierAction :=
  (List.range' first count).map fun block => .squeezePair owner block

theorem squeeze_many_actions_agree
    (table : FixedOracleTable) (bindings : FixedBindings)
    (owner : SqueezeOwner) (first count : Nat)
    (core : RuntimeCore) (state next : EvalState)
    (outputs : List Digest256) (same : SameDigest core state)
    (run : squeezeManyFrom table owner first count state = some (outputs, next)) :
    runActionCores table bindings (squeezeActionsFrom owner first count) core =
      some { core with digest := next.digest } := by
  induction count generalizing first core state outputs with
  | zero =>
      rw [squeezeManyFrom] at run
      have result := Option.some.inj run
      cases result
      cases core
      simp_all [SameDigest, squeezeActionsFrom, runActionCores]
  | succ count ih =>
      rw [squeezeManyFrom] at run
      obtain ⟨firstPair, hfirst, run⟩ := Option.bind_eq_some_iff.mp run
      rcases firstPair with ⟨output, blockState⟩
      obtain ⟨restPair, hrest, hresult⟩ := Option.bind_eq_some_iff.mp run
      rcases restPair with ⟨restOutputs, finalState⟩
      have resultEquals := Option.some.inj hresult
      cases resultEquals
      have firstAction := squeeze_action_agrees table bindings core state
        blockState owner first output same hfirst
      have restSame : SameDigest { core with digest := blockState.digest }
          blockState := rfl
      have restActions := ih (first := first + 1)
        (core := { core with digest := blockState.digest })
        (state := blockState) (outputs := restOutputs) restSame hrest
      simp only [squeezeActionsFrom, List.range'_succ,
        List.map_cons, runActionCores]
      apply Option.bind_eq_some_iff.mpr
      refine ⟨{ core with digest := blockState.digest }, firstAction, ?_⟩
      change runActionCores table bindings
        (squeezeActionsFrom owner (first + 1) count)
        { core with digest := blockState.digest } =
          some { core with digest := next.digest }
      exact restActions

theorem challenge_actions_agree
    (table : FixedOracleTable) (bindings : FixedBindings)
    (id : ChallengeId) (use : SamplerUse id)
    (core : RuntimeCore) (state next : EvalState)
    (blocks : List Digest256) (same : SameDigest core state)
    (run : squeezeMany table (.challenge id) use.blocksUsed state =
      some (blocks, next)) :
    runActionCores table bindings (challengeActions id use) core =
      some { core with digest := next.digest } := by
  have generalized := squeeze_many_actions_agree table bindings
    (.challenge id) 0 use.blocksUsed core state next blocks same run
  simpa [challengeActions, squeezeActionsFrom, List.range_eq_range'] using generalized

/-! ## Root-salt and typed-root agreement -/

theorem request_c1_root_salt_agrees
    (table : FixedOracleTable) (context : Context)
    (core : RuntimeCore) (state next : EvalState) (salt : Digest256)
    (same : SameDigest core state)
    (run : rootSaltStep table state context c1TreeTag = some (salt, next)) :
    runActionCore table (FixedBindings.ofContext context) core
        (.requestRootSalt .initialC1) =
      some { core with c1Salt := some salt } ∧
    SameDigest { core with c1Salt := some salt } next := by
  obtain ⟨lookup, _, digest⟩ := query_step_appends_one table state next
    (.publicRootSalt context c1TreeTag) salt run
  have nextDigest : next.digest = state.digest := by
    simpa only [RawQueryRole.nextDigest] using digest
  constructor
  · rw [runActionCore]
    apply Option.bind_eq_some_iff.mpr
    refine ⟨.single salt, ?_, rfl⟩
    simp only [deriveReply, actionInputs, lookupSingleInput,
      fixed_bindings_recover_context, AuthenticatedTree.tag]
    have normalized : tableLookup table
        (rootSaltInput context c1TreeTag) = some salt := by
      simpa only [RawQueryRole.input] using lookup
    rw [normalized]
    rfl
  · change core.digest = next.digest
    exact same.trans nextDigest.symm

theorem request_c2_root_salt_agrees
    (table : FixedOracleTable) (context : Context)
    (core : RuntimeCore) (state next : EvalState) (salt : Digest256)
    (same : SameDigest core state)
    (run : rootSaltStep table state context c2TreeTag = some (salt, next)) :
    runActionCore table (FixedBindings.ofContext context) core
        (.requestRootSalt .foldedC2) =
      some { core with c2Salt := some salt } ∧
    SameDigest { core with c2Salt := some salt } next := by
  obtain ⟨lookup, _, digest⟩ := query_step_appends_one table state next
    (.publicRootSalt context c2TreeTag) salt run
  have nextDigest : next.digest = state.digest := by
    simpa only [RawQueryRole.nextDigest] using digest
  constructor
  · rw [runActionCore]
    apply Option.bind_eq_some_iff.mpr
    refine ⟨.single salt, ?_, rfl⟩
    simp only [deriveReply, actionInputs, lookupSingleInput,
      fixed_bindings_recover_context, AuthenticatedTree.tag]
    have normalized : tableLookup table
        (rootSaltInput context c2TreeTag) = some salt := by
      simpa only [RawQueryRole.input] using lookup
    rw [normalized]
    rfl
  · change core.digest = next.digest
    exact same.trans nextDigest.symm

theorem absorb_c1_root_action_agrees
    (table : FixedOracleTable) (context : Context)
    (core : RuntimeCore) (state next : EvalState)
    (root : TypedMerkleRoot .initialC1) (salt : Digest256)
    (saved : core.c1Salt = some salt) (same : SameDigest core state)
    (run : absorbStep table state (.c1Root root.value salt) = some next) :
    runActionCore table (FixedBindings.ofContext context) core (.absorbC1 root) =
      some { core with digest := next.digest } := by
  rw [absorbStep] at run
  obtain ⟨pair, hstep, hnext⟩ := Option.bind_eq_some_iff.mp run
  rcases pair with ⟨output, stepped⟩
  have steppedEquals : stepped = next := by
    simpa only [pure, Option.some.injEq] using hnext
  subst stepped
  obtain ⟨lookup, _, digest⟩ := query_step_appends_one table state next
    (.absorb (.c1Root root.value salt)) output hstep
  have outputEquals : output = next.digest := by
    simpa only [RawQueryRole.nextDigest] using digest.symm
  subst output
  have normalized : tableLookup table
      (bytes state.digest ++ [domAbsorb, c1RootLabel] ++
        (Payload.c1Root root.value salt).data) = some next.digest := by
    simpa only [RawQueryRole.input, Payload.label] using lookup
  rw [runActionCore]
  apply Option.bind_eq_some_iff.mpr
  refine ⟨.single next.digest, ?_, ?_⟩
  · simp only [deriveReply, actionInputs, saved, lookupSingleInput]
    change core.digest = state.digest at same
    rw [same, normalized]
    rfl
  · simp [applyActionWorkErased, saved]

theorem absorb_c2_root_action_agrees
    (table : FixedOracleTable) (context : Context)
    (core : RuntimeCore) (state next : EvalState)
    (lambda chi : Qm31Bytes) (commitment : C2Commitment lambda chi)
    (salt : Digest256) (saved : core.c2Salt = some salt)
    (same : SameDigest core state)
    (run : absorbStep table state (.c2Root commitment.root salt) = some next) :
    runActionCore table (FixedBindings.ofContext context) core
        (.absorbC2 lambda chi commitment) =
      some { core with digest := next.digest } := by
  rw [absorbStep] at run
  obtain ⟨pair, hstep, hnext⟩ := Option.bind_eq_some_iff.mp run
  rcases pair with ⟨output, stepped⟩
  have steppedEquals : stepped = next := by
    simpa only [pure, Option.some.injEq] using hnext
  subst stepped
  obtain ⟨lookup, _, digest⟩ := query_step_appends_one table state next
    (.absorb (.c2Root commitment.root salt)) output hstep
  have outputEquals : output = next.digest := by
    simpa only [RawQueryRole.nextDigest] using digest.symm
  subst output
  have normalized : tableLookup table
      (bytes state.digest ++ [domAbsorb, c2RootLabel] ++
        (Payload.c2Root commitment.root salt).data) = some next.digest := by
    simpa only [RawQueryRole.input, Payload.label] using lookup
  rw [runActionCore]
  apply Option.bind_eq_some_iff.mpr
  refine ⟨.single next.digest, ?_, ?_⟩
  · simp only [deriveReply, actionInputs, saved, lookupSingleInput]
    change core.digest = state.digest at same
    rw [same, normalized]
    rfl
  · simp [applyActionWorkErased, saved]

theorem grinding_probe_actions_agree
    (table : FixedOracleTable) (bindings : FixedBindings)
    (stage : WorkStage) (probes : List NonceBytes)
    (core : RuntimeCore) (state next : EvalState)
    (same : SameDigest core state)
    (run : runGrindingProbes table stage probes state = some next) :
    runActionCores table bindings
      (probes.map fun nonce =>
        VerifierAction.workProbe stage nonce .adversaryHistory)
      core = some core := by
  induction probes generalizing core state with
  | nil => simp [runActionCores]
  | cons nonce rest ih =>
      rw [runGrindingProbes.eq_def] at run
      obtain ⟨pair, hprobe, hrest⟩ := Option.bind_eq_some_iff.mp run
      rcases pair with ⟨output, afterProbe⟩
      have first := work_probe_action_agrees table bindings core state
        afterProbe stage nonce .adversaryHistory output same hprobe
      have digest := grind_probe_does_not_advance table state afterProbe
        stage nonce output hprobe
      have restSame : SameDigest core afterProbe := same.trans digest.symm
      have restRun := ih (core := core) (state := afterProbe) restSame hrest
      simp only [List.map_cons, runActionCores]
      exact Option.bind_eq_some_iff.mpr ⟨core, first, restRun⟩

/-! ## Event-list agreement -/

theorem machine_event_actions_agree
    (table : FixedOracleTable) (bindings : FixedBindings)
    (core : RuntimeCore) (state next : EvalState) (event : MachineEvent)
    (same : SameDigest core state)
    (run : runMachineEventWorkErased table state event = some next) :
    ∃ nextCore,
      runActionCores table bindings (eventActions event) core = some nextCore ∧
      SameDigest nextCore next ∧
      nextCore.c1Salt = core.c1Salt ∧
      nextCore.c2Salt = core.c2Salt ∧
      nextCore.q16Base = core.q16Base := by
  cases event with
  | absorb payload =>
      refine ⟨{ core with digest := next.digest }, ?_, rfl, rfl, rfl, rfl⟩
      simpa [eventActions, runActionCores] using
        absorb_action_agrees table bindings core state next payload same run
  | challenge id use =>
      rw [runMachineEventWorkErased] at run
      obtain ⟨pair, hsqueeze, hnext⟩ := Option.bind_eq_some_iff.mp run
      rcases pair with ⟨blocks, squeezed⟩
      have nextEquation : { squeezed with
          samples := squeezed.samples ++ [{ id, blocks }] } = next := by
        simpa only [pure, Option.some.injEq] using hnext
      have digestEquals : squeezed.digest = next.digest := by
        rw [← nextEquation]
      refine ⟨{ core with digest := next.digest }, ?_, rfl, rfl, rfl, rfl⟩
      have actions := challenge_actions_agree table bindings id use core state
        squeezed blocks same hsqueeze
      rw [digestEquals] at actions
      simpa [eventActions] using actions
  | grind stage choice =>
      rw [runMachineEventWorkErased] at run
      -- The list of exploratory probes is handled by induction below.
      unfold runGrindingChoiceWorkErased at run
      obtain ⟨queried, hprobes, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨selectedPair, hselected, hnext⟩ :=
        Option.bind_eq_some_iff.mp run
      rcases selectedPair with ⟨selectedOutput, selectedState⟩
      have selectedEquals : selectedState = next := by
        simpa only [pure, Option.some.injEq] using hnext
      subst selectedState
      have probesDigest := grinding_probes_do_not_advance table stage
        choice.probesBeforeSelected state queried hprobes
      have selectedDigest := grind_probe_does_not_advance table queried next
        stage choice.selected selectedOutput hselected
      have nextDigest : next.digest = state.digest :=
        selectedDigest.trans probesDigest
      refine ⟨core, ?_, ?_, rfl, rfl, rfl⟩
      · have probeList : runActionCores table bindings
            (choice.probesBeforeSelected.map
              (fun nonce => VerifierAction.workProbe stage nonce
                .adversaryHistory)) core = some core := by
          exact grinding_probe_actions_agree table bindings stage
            choice.probesBeforeSelected core state queried same hprobes
        have selectedAction := work_probe_action_agrees table bindings core queried
          next stage choice.selected .verifierSelected selectedOutput
          (same.trans probesDigest.symm) hselected
        unfold eventActions grindingActions
        exact run_action_cores_append_of_runs table bindings _ _ core core core
          probeList (by simpa [runActionCores] using selectedAction)
      · exact same.trans nextDigest.symm
  | check checkpoint =>
      have stateEquals : state = next := by
        simpa [runMachineEventWorkErased] using run
      subst next
      exact ⟨core, by simp [eventActions, runActionCores, runActionCore,
        deriveReply, applyActionWorkErased], same, rfl, rfl, rfl⟩

theorem machine_events_actions_agree
    (table : FixedOracleTable) (bindings : FixedBindings)
    (events : List MachineEvent) (core : RuntimeCore)
    (state next : EvalState) (same : SameDigest core state)
    (run : runMachineEventsWorkErased table events state = some next) :
    ∃ nextCore,
      runActionCores table bindings (eventsToActions events) core = some nextCore ∧
      SameDigest nextCore next ∧
      nextCore.c1Salt = core.c1Salt ∧
      nextCore.c2Salt = core.c2Salt ∧
      nextCore.q16Base = core.q16Base := by
  induction events generalizing core state with
  | nil =>
      have stateEquals : state = next := by
        simpa [runMachineEventsWorkErased] using run
      subst next
      exact ⟨core, by simp [eventsToActions, runActionCores], same,
        rfl, rfl, rfl⟩
  | cons event rest ih =>
      rw [runMachineEventsWorkErased] at run
      obtain ⟨eventState, hevent, hrest⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨eventCore, hactions, hsame, hc1, hc2, hbase⟩ :=
        machine_event_actions_agree table bindings core state eventState event
          same hevent
      obtain ⟨finalCore, hrestActions, hfinalSame, hfinalC1,
          hfinalC2, hfinalBase⟩ :=
        ih (core := eventCore) (state := eventState) hsame hrest
      refine ⟨finalCore, ?_, hfinalSame, hfinalC1.trans hc1,
        hfinalC2.trans hc2, hfinalBase.trans hbase⟩
      simp only [eventsToActions, List.flatMap_cons]
      exact run_action_cores_append_of_runs table bindings _ _ core eventCore
        finalCore hactions hrestActions

/-! ## Exact prefix composition -/

theorem adaptive_prefix_plan_expansion (tape : DeployedFixedTape) :
    adaptivePrefixPlan tape =
      eventsToActions (prefixBeforeC1 tape.messages) ++
      [.requestRootSalt .initialC1, .absorbC1 (c1TypedRoot tape.messages)] ++
      eventsToActions
        [challengeEvent tape.messages .lambda,
         challengeEvent tape.messages .chi] ++
      [.requestRootSalt .foldedC2,
       .absorbC2 (tape.messages.challengeValue .lambda)
         (tape.messages.challengeValue .chi) tape.messages.c2] ++
      eventsToActions (prefixAfterC2 tape.messages) := by
  simp [adaptivePrefixPlan, adaptiveRounds, expandAdaptiveRound,
    eventsToActions, eventActions, challengeEvent, List.append_assoc]

theorem run_prefix_work_erased_constructs_exact_actions
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (next : EvalState)
    (run : runPrefixWorkErased table tape.messages = some next) :
    ∃ finalCore,
      runActionCores table
        (FixedBindings.ofContext tape.messages.context)
        (adaptivePrefixPlan tape) initialCore = some finalCore ∧
      SameDigest finalCore next ∧
      ∃ c1Salt c2Salt,
        finalCore.c1Salt = some c1Salt ∧
        finalCore.c2Salt = some c2Salt ∧
        finalCore.q16Base = none := by
  rw [runPrefixWorkErased] at run
  obtain ⟨beforeC1, hbeforeC1, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨c1Pair, hc1Salt, run⟩ := Option.bind_eq_some_iff.mp run
  rcases c1Pair with ⟨c1Salt, withC1SaltQuery⟩
  obtain ⟨afterC1, hafterC1, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨afterPhase, hphase, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨c2Pair, hc2Salt, run⟩ := Option.bind_eq_some_iff.mp run
  rcases c2Pair with ⟨c2Salt, withC2SaltQuery⟩
  obtain ⟨afterC2, hafterC2, hrest⟩ := Option.bind_eq_some_iff.mp run
  let bindings := FixedBindings.ofContext tape.messages.context
  obtain ⟨beforeCore, hbeforeActions, hbeforeSame,
      hbeforeC1Field, hbeforeC2Field, hbeforeBase⟩ :=
    machine_events_actions_agree table bindings
      (prefixBeforeC1 tape.messages) initialCore initialEvalState beforeC1
      rfl hbeforeC1
  have beforeC1None : beforeCore.c1Salt = none := by
    exact hbeforeC1Field.trans rfl
  have beforeC2None : beforeCore.c2Salt = none := by
    exact hbeforeC2Field.trans rfl
  have beforeBaseNone : beforeCore.q16Base = none := by
    exact hbeforeBase.trans rfl
  obtain ⟨hc1Request, hc1RequestSame⟩ :=
    request_c1_root_salt_agrees table tape.messages.context beforeCore beforeC1
      withC1SaltQuery c1Salt hbeforeSame hc1Salt
  let c1RequestCore : RuntimeCore :=
    { beforeCore with c1Salt := some c1Salt }
  have hc1Absorb := absorb_c1_root_action_agrees table tape.messages.context
    c1RequestCore withC1SaltQuery afterC1 (c1TypedRoot tape.messages) c1Salt
    rfl hc1RequestSame hafterC1
  let afterC1Core : RuntimeCore :=
    { c1RequestCore with digest := afterC1.digest }
  obtain ⟨phaseCore, hphaseActions, hphaseSame,
      hphaseC1, hphaseC2, hphaseBase⟩ :=
    machine_events_actions_agree table bindings
      [challengeEvent tape.messages .lambda,
       challengeEvent tape.messages .chi]
      afterC1Core afterC1 afterPhase rfl hphase
  obtain ⟨hc2Request, hc2RequestSame⟩ :=
    request_c2_root_salt_agrees table tape.messages.context phaseCore afterPhase
      withC2SaltQuery c2Salt hphaseSame hc2Salt
  let c2RequestCore : RuntimeCore :=
    { phaseCore with c2Salt := some c2Salt }
  have hc2Absorb := absorb_c2_root_action_agrees table tape.messages.context
    c2RequestCore withC2SaltQuery afterC2
    (tape.messages.challengeValue .lambda)
    (tape.messages.challengeValue .chi) tape.messages.c2 c2Salt rfl
    hc2RequestSame hafterC2
  let afterC2Core : RuntimeCore :=
    { c2RequestCore with digest := afterC2.digest }
  obtain ⟨finalCore, hrestActions, hfinalSame,
      hfinalC1, hfinalC2, hfinalBase⟩ :=
    machine_events_actions_agree table bindings
      (prefixAfterC2 tape.messages) afterC2Core afterC2 next rfl hrest
  have runC1Request : runActionCores table bindings
      [.requestRootSalt .initialC1] beforeCore = some c1RequestCore := by
    simpa [runActionCores, bindings, c1RequestCore] using hc1Request
  have runC1Absorb : runActionCores table bindings
      [.absorbC1 (c1TypedRoot tape.messages)] c1RequestCore =
        some afterC1Core := by
    simpa [runActionCores, bindings, afterC1Core] using hc1Absorb
  have runC2Request : runActionCores table bindings
      [.requestRootSalt .foldedC2] phaseCore = some c2RequestCore := by
    simpa [runActionCores, bindings, c2RequestCore] using hc2Request
  have runC2Absorb : runActionCores table bindings
      [.absorbC2 (tape.messages.challengeValue .lambda)
        (tape.messages.challengeValue .chi) tape.messages.c2]
      c2RequestCore = some afterC2Core := by
    simpa [runActionCores, bindings, afterC2Core] using hc2Absorb
  have combined01 := run_action_cores_append_of_runs table bindings _ _
    initialCore beforeCore c1RequestCore hbeforeActions runC1Request
  have combined02 := run_action_cores_append_of_runs table bindings _ _
    initialCore c1RequestCore afterC1Core combined01 runC1Absorb
  have combined03 := run_action_cores_append_of_runs table bindings _ _
    initialCore afterC1Core phaseCore combined02 hphaseActions
  have combined04 := run_action_cores_append_of_runs table bindings _ _
    initialCore phaseCore c2RequestCore combined03 runC2Request
  have combined05 := run_action_cores_append_of_runs table bindings _ _
    initialCore c2RequestCore afterC2Core combined04 runC2Absorb
  have combined := run_action_cores_append_of_runs table bindings _ _
    initialCore afterC2Core finalCore combined05 hrestActions
  refine ⟨finalCore, ?_, hfinalSame, c1Salt, c2Salt, ?_, ?_, ?_⟩
  · simpa [adaptive_prefix_plan_expansion, List.append_assoc] using combined
  · exact hfinalC1.trans (hphaseC1.trans rfl)
  · exact hfinalC2.trans rfl
  · exact hfinalBase.trans (hphaseBase.trans beforeBaseNone)

/-! ## Exact cloned q16 forest composition -/

theorem candidate_absorb_action_agrees
    (table : FixedOracleTable) (bindings : FixedBindings)
    (core : RuntimeCore) (state next : EvalState)
    (spec : CandidateSpec) (selected : Bool) (base : Digest256)
    (saved : core.q16Base = some base) (same : SameDigest core state)
    (run : absorbStep table state (.queryCandidate spec.counter) = some next) :
    runActionCore table bindings core
        (.q16CandidateAbsorb spec.counter spec.outcome selected) =
      some { core with digest := next.digest } := by
  rw [absorbStep] at run
  obtain ⟨pair, hstep, hnext⟩ := Option.bind_eq_some_iff.mp run
  rcases pair with ⟨output, stepped⟩
  have steppedEquals : stepped = next := by
    simpa only [pure, Option.some.injEq] using hnext
  subst stepped
  obtain ⟨lookup, _, digest⟩ := query_step_appends_one table state next
    (.absorb (.queryCandidate spec.counter)) output hstep
  have outputEquals : output = next.digest := by
    simpa only [RawQueryRole.nextDigest] using digest.symm
  subst output
  have normalized : tableLookup table
      ((bytes state.digest ++ [domAbsorb, queryCandidateLabel]) ++
        [UInt8.ofNat spec.counter.val]) = some next.digest := by
    simpa only [RawQueryRole.input, Payload.label, Payload.data] using lookup
  have normalizedFlat : tableLookup table
      (bytes state.digest ++ [domAbsorb, queryCandidateLabel,
        UInt8.ofNat spec.counter.val]) = some next.digest := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      normalized
  rw [runActionCore]
  apply Option.bind_eq_some_iff.mpr
  refine ⟨.single next.digest, ?_, ?_⟩
  · simp only [deriveReply, actionInputs, lookupSingleInput]
    change core.digest = state.digest at same
    rw [same, normalizedFlat]
    rfl
  · simp [applyActionWorkErased, saved]

theorem candidate_actions_agree
    (table : FixedOracleTable) (bindings : FixedBindings)
    (core : RuntimeCore) (state next : EvalState)
    (spec : CandidateSpec) (selected : Bool) (base : Digest256)
    (saved : core.q16Base = some base) (same : SameDigest core state)
    (run : runCandidate table state spec = some next) :
    runActionCores table bindings (candidateActions spec selected) core =
      some { core with digest := next.digest } := by
  rw [runCandidate] at run
  obtain ⟨afterCounter, hcounter, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨blocksPair, hblocks, hnext⟩ := Option.bind_eq_some_iff.mp run
  rcases blocksPair with ⟨blocks, afterBlocks⟩
  have nextEquation : { afterBlocks with
      candidates := afterBlocks.candidates ++
        [{ counter := spec.counter
           outcome := spec.outcome
           baseDigest := state.digest
           endDigest := afterBlocks.digest
           blocks := blocks }] } = next := by
    simpa only [pure, Option.some.injEq] using hnext
  have nextDigest : afterBlocks.digest = next.digest := by
    rw [← nextEquation]
  have counterAction := candidate_absorb_action_agrees table bindings core
    state afterCounter spec selected base saved same hcounter
  let counterCore : RuntimeCore := { core with digest := afterCounter.digest }
  have blocksSame : SameDigest counterCore afterCounter := rfl
  have blockActions := squeeze_many_actions_agree table bindings
    (.queryCandidate spec.counter) 0 spec.outcome.blocksUsed counterCore
    afterCounter afterBlocks blocks blocksSame hblocks
  rw [nextDigest] at blockActions
  unfold candidateActions
  apply run_action_cores_append_of_runs table bindings _ _ core counterCore
    { counterCore with digest := next.digest }
  · simpa [runActionCores, counterCore] using counterAction
  · simpa [squeezeActionsFrom, List.range_eq_range'] using blockActions

theorem discarded_candidates_actions_restore_shared_base
    (table : FixedOracleTable) (bindings : FixedBindings)
    (base : Digest256) (specs : List CandidateSpec)
    (core : RuntimeCore) (state next : EvalState)
    (saved : core.q16Base = some base)
    (coreAtBase : core.digest = base)
    (same : SameDigest core state)
    (run : runDiscardedCandidates table base specs state = some next) :
    runActionCores table bindings
      (specs.flatMap discardedCandidateActions) core = some core ∧
    next.digest = base := by
  induction specs generalizing state with
  | nil =>
      rw [runDiscardedCandidates] at run
      have stateEquals : state = next := Option.some.inj run
      subst next
      exact ⟨by simp [runActionCores], same.symm.trans coreAtBase⟩
  | cons spec rest ih =>
      rw [runDiscardedCandidates] at run
      obtain ⟨branch, hbranch, hrest⟩ := Option.bind_eq_some_iff.mp run
      have candidateRun := candidate_actions_agree table bindings core state
        branch spec false base saved same hbranch
      let branchCore : RuntimeCore := { core with digest := branch.digest }
      have restoreRun : runActionCores table bindings
          [.q16Restore spec.counter] branchCore = some core := by
        cases core
        simp_all [runActionCores, runActionCore, deriveReply,
          applyActionWorkErased, branchCore]
      have oneDiscard := run_action_cores_append_of_runs table bindings _ _
        core branchCore core candidateRun restoreRun
      have restoredSame : SameDigest core (restoreDigest base branch) := by
        change core.digest = base
        exact coreAtBase
      obtain ⟨restRun, finalDigest⟩ := ih (state := restoreDigest base branch)
        restoredSame hrest
      constructor
      · simp only [List.flatMap_cons, discardedCandidateActions]
        exact run_action_cores_append_of_runs table bindings _ _ core core core
          oneDiscard restRun
      · exact finalDigest

theorem run_q16_constructs_exact_cloned_forest
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (prefixCore : RuntimeCore) (prefixState afterQ16 : EvalState)
    (same : SameDigest prefixCore prefixState)
    (baseEmpty : prefixCore.q16Base = none)
    (run : runQ16 table prefixState (q16TapeOfSearch tape.search) =
      some afterQ16) :
    ∃ finalCore,
      runActionCores table
        (FixedBindings.ofContext tape.messages.context)
        (q16Plan tape) prefixCore = some finalCore ∧
      SameDigest finalCore afterQ16 ∧
      finalCore.q16Base = some prefixState.digest := by
  rw [runQ16] at run
  obtain ⟨beforeSelected, hearlier, hselected⟩ :=
    Option.bind_eq_some_iff.mp run
  let bindings := FixedBindings.ofContext tape.messages.context
  let markedCore : RuntimeCore :=
    { prefixCore with q16Base := some prefixCore.digest }
  have markRun : runActionCores table bindings [.markQ16Base] prefixCore =
      some markedCore := by
    simp [runActionCores, runActionCore, deriveReply,
      applyActionWorkErased, markedCore]
  have markedSaved : markedCore.q16Base = some prefixState.digest := by
    change some prefixCore.digest = some prefixState.digest
    exact congrArg some same
  have markedAtBase : markedCore.digest = prefixState.digest := same
  have markedSame : SameDigest markedCore prefixState := same
  obtain ⟨earlierRun, beforeSelectedDigest⟩ :=
    discarded_candidates_actions_restore_shared_base table bindings
      prefixState.digest (q16TapeOfSearch tape.search).earlier markedCore
      prefixState beforeSelected markedSaved markedAtBase markedSame hearlier
  have beforeSelectedSame : SameDigest markedCore beforeSelected := by
    change prefixCore.digest = beforeSelected.digest
    exact same.trans beforeSelectedDigest.symm
  have selectedRun := candidate_actions_agree table bindings markedCore
    beforeSelected afterQ16 (q16TapeOfSearch tape.search).selected true
    prefixState.digest markedSaved beforeSelectedSame hselected
  let selectedCore : RuntimeCore :=
    { markedCore with digest := afterQ16.digest }
  have selectedMarker : runActionCores table bindings
      [.q16Selected (q16TapeOfSearch tape.search).selected.counter]
      selectedCore = some selectedCore := by
    simp [runActionCores, runActionCore, deriveReply,
      applyActionWorkErased]
  have markedAndEarlier := run_action_cores_append_of_runs table bindings _ _
    prefixCore markedCore markedCore markRun earlierRun
  have throughSelected := run_action_cores_append_of_runs table bindings _ _
    prefixCore markedCore selectedCore markedAndEarlier selectedRun
  have combined := run_action_cores_append_of_runs table bindings _ _
    prefixCore selectedCore selectedCore throughSelected selectedMarker
  refine ⟨selectedCore, ?_, rfl, ?_⟩
  · simpa [q16Plan, bindings, List.append_assoc] using combined
  · exact markedSaved

/-! The after-scan and full-plan composition follows this q16 layer. -/

#print axioms table_execution_trace_of_run_action_cores
#print axioms concrete_first_execution_of_full_plan_run
#print axioms absorb_action_agrees
#print axioms squeeze_action_agrees
#print axioms challenge_actions_agree
#print axioms request_c1_root_salt_agrees
#print axioms request_c2_root_salt_agrees
#print axioms absorb_c1_root_action_agrees
#print axioms absorb_c2_root_action_agrees
#print axioms machine_event_actions_agree
#print axioms machine_events_actions_agree
#print axioms adaptive_prefix_plan_expansion
#print axioms run_prefix_work_erased_constructs_exact_actions
#print axioms candidate_absorb_action_agrees
#print axioms candidate_actions_agree
#print axioms discarded_candidates_actions_restore_shared_base
#print axioms run_q16_constructs_exact_cloned_forest

end AspisK1.V7Tag73RefinementExecutionBridge
