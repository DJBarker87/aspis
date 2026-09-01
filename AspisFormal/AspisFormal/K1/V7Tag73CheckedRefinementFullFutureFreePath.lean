import AspisFormal.K1.V7Tag73CheckedRefinementFutureFreePath
import AspisFormal.K1.V7Tag73Q16LedgerCertificate

/-!
# A complete checked-refinement path through the future-free Tag-73 verifier

This module continues the checked-refinement/future-free bisimulation after
the C1 gate.  Its target is operational schedule exhaustion, not semantic
acceptance: the semantic claims, the two authenticated trees, the exact q16
frontier and the terminal relation remain the explicit K1.2--K1.5
obligations in `futureFreeExternalAcceptanceObligations`.

The fixed-table evaluator is used only as execution evidence.  Challenges and
q16 outcomes are accepted by the future-free controller only after its exact
incremental decoders recompute them from the paired squeeze outputs.  The
three exploratory grinding histories never become verifier actions; each
selected nonce still contributes its selected query, checkpoint and absorb.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73CheckedRefinementFullFutureFreePath

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73Q16LedgerCertificate
open AspisK1.V7Tag73InteractiveExecution
open AspisK1.V7Tag73RefinementExecutionBridge
open AspisK1.V7Tag73ResumeDerivedReplayNode
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73FutureFreeCheckedRefinementBisimulation
open AspisK1.V7Tag73CheckedRefinementFutureFreePath
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7FsAokExperiment

noncomputable section

/-! ## Evaluator records are monotone -/

def SamplesIncluded (before after : EvalState) : Prop :=
  ∀ record ∈ before.samples, record ∈ after.samples

def CandidatesIncluded (before after : EvalState) : Prop :=
  ∀ record ∈ before.candidates, record ∈ after.candidates

theorem query_step_preserves_samples_and_candidates
    (table : FixedOracleTable) (state next : EvalState)
    (role : RawQueryRole) (output : Digest256)
    (run : queryStep table state role = some (output, next)) :
    next.samples = state.samples ∧ next.candidates = state.candidates := by
  simp only [queryStep] at run
  cases hlookup : tableLookup table (role.input state.digest) with
  | none => simp [hlookup] at run
  | some actual =>
      rw [hlookup] at run
      have equal := Option.some.inj run
      cases equal
      exact ⟨rfl, rfl⟩

theorem absorb_step_preserves_samples_and_candidates
    (table : FixedOracleTable) (state next : EvalState) (payload : Payload)
    (run : absorbStep table state payload = some next) :
    next.samples = state.samples ∧ next.candidates = state.candidates := by
  rw [absorbStep] at run
  obtain ⟨pair, step, result⟩ := Option.bind_eq_some_iff.mp run
  rcases pair with ⟨output, stepped⟩
  have equal : stepped = next := Option.some.inj result
  subst next
  exact query_step_preserves_samples_and_candidates table state stepped
    (.absorb payload) output step

theorem root_salt_step_preserves_samples_and_candidates
    (table : FixedOracleTable) (state next : EvalState)
    (context : Context) (treeTag : UInt8) (salt : Digest256)
    (run : rootSaltStep table state context treeTag = some (salt, next)) :
    next.samples = state.samples ∧ next.candidates = state.candidates := by
  exact query_step_preserves_samples_and_candidates table state next
    (.publicRootSalt context treeTag) salt run

theorem squeeze_step_preserves_samples_and_candidates
    (table : FixedOracleTable) (state next : EvalState)
    (owner : SqueezeOwner) (block : Nat) (output : Digest256)
    (run : squeezeStep table state owner block = some (output, next)) :
    next.samples = state.samples ∧ next.candidates = state.candidates := by
  rw [squeezeStep] at run
  obtain ⟨firstPair, firstRun, run⟩ := Option.bind_eq_some_iff.mp run
  rcases firstPair with ⟨actualOutput, afterOutput⟩
  obtain ⟨secondPair, secondRun, result⟩ :=
    Option.bind_eq_some_iff.mp run
  rcases secondPair with ⟨advance, afterAdvance⟩
  have pairEqual := Option.some.inj result
  have outputEqual := congrArg Prod.fst pairEqual
  have stateEqual := congrArg Prod.snd pairEqual
  dsimp at outputEqual stateEqual
  subst output
  subst next
  have first := query_step_preserves_samples_and_candidates table state
    afterOutput (.squeezeOutput owner block) actualOutput firstRun
  have second := query_step_preserves_samples_and_candidates table afterOutput
    afterAdvance (.squeezeAdvance owner block) advance secondRun
  exact ⟨second.1.trans first.1, second.2.trans first.2⟩

theorem squeeze_many_from_preserves_samples_and_candidates
    (table : FixedOracleTable) (owner : SqueezeOwner)
    (first count : Nat) (state final : EvalState)
    (outputs : List Digest256)
    (run : squeezeManyFrom table owner first count state =
      some (outputs, final)) :
    final.samples = state.samples ∧ final.candidates = state.candidates := by
  induction count generalizing first state outputs final with
  | zero =>
      rw [squeezeManyFrom] at run
      cases Option.some.inj run
      exact ⟨rfl, rfl⟩
  | succ count ih =>
      rw [squeezeManyFrom] at run
      obtain ⟨firstPair, firstRun, run⟩ := Option.bind_eq_some_iff.mp run
      rcases firstPair with ⟨output, afterBlock⟩
      obtain ⟨restPair, restRun, result⟩ := Option.bind_eq_some_iff.mp run
      rcases restPair with ⟨restOutputs, restState⟩
      cases Option.some.inj result
      have head := squeeze_step_preserves_samples_and_candidates table state
        afterBlock owner first output firstRun
      have tail := ih (first := first + 1) (state := afterBlock)
        (outputs := restOutputs) (final := final) restRun
      exact ⟨tail.1.trans head.1, tail.2.trans head.2⟩

theorem squeeze_many_preserves_samples_and_candidates
    (table : FixedOracleTable) (owner : SqueezeOwner) (count : Nat)
    (state final : EvalState) (outputs : List Digest256)
    (run : squeezeMany table owner count state = some (outputs, final)) :
    final.samples = state.samples ∧ final.candidates = state.candidates := by
  exact squeeze_many_from_preserves_samples_and_candidates table owner 0 count
    state final outputs run

theorem run_grinding_probes_preserves_samples_and_candidates
    (table : FixedOracleTable) (stage : WorkStage)
    (probes : List NonceBytes) (state final : EvalState)
    (run : runGrindingProbes table stage probes state = some final) :
    final.samples = state.samples ∧ final.candidates = state.candidates := by
  induction probes generalizing state with
  | nil =>
      rw [runGrindingProbes] at run
      cases Option.some.inj run
      exact ⟨rfl, rfl⟩
  | cons nonce rest ih =>
      rw [runGrindingProbes] at run
      obtain ⟨pair, probeRun, restRun⟩ := Option.bind_eq_some_iff.mp run
      rcases pair with ⟨output, afterProbe⟩
      have head := query_step_preserves_samples_and_candidates table state
        afterProbe (.grind stage nonce) output probeRun
      have tail := ih (state := afterProbe) restRun
      exact ⟨tail.1.trans head.1, tail.2.trans head.2⟩

theorem run_grinding_choice_work_erased_preserves_samples_and_candidates
    (table : FixedOracleTable) (state final : EvalState)
    (stage : WorkStage) (choice : GrindingChoice stage)
    (run : runGrindingChoiceWorkErased table state stage choice = some final) :
    final.samples = state.samples ∧ final.candidates = state.candidates := by
  rw [runGrindingChoiceWorkErased] at run
  obtain ⟨queried, probesRun, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨selectedPair, selectedRun, result⟩ :=
    Option.bind_eq_some_iff.mp run
  rcases selectedPair with ⟨output, afterSelected⟩
  have equal : afterSelected = final := Option.some.inj result
  subst final
  have probes := run_grinding_probes_preserves_samples_and_candidates table
    stage choice.probesBeforeSelected state queried probesRun
  have selected := query_step_preserves_samples_and_candidates table queried
    afterSelected (.grind stage choice.selected) output selectedRun
  exact ⟨selected.1.trans probes.1, selected.2.trans probes.2⟩

theorem machine_event_work_erased_samples_included
    (table : FixedOracleTable) (state next : EvalState)
    (event : MachineEvent)
    (run : runMachineEventWorkErased table state event = some next) :
    SamplesIncluded state next := by
  intro record member
  cases event with
  | absorb payload =>
      have preserved := absorb_step_preserves_samples_and_candidates table
        state next payload run
      rw [preserved.1]
      exact member
  | challenge id use =>
      rw [runMachineEventWorkErased] at run
      obtain ⟨pair, squeezeRun, result⟩ := Option.bind_eq_some_iff.mp run
      rcases pair with ⟨blocks, afterBlocks⟩
      have equal := Option.some.inj result
      rw [← equal]
      simp only [List.mem_append]
      exact Or.inl (by
        have preserved := squeeze_many_preserves_samples_and_candidates table
          (.challenge id) use.blocksUsed state afterBlocks blocks squeezeRun
        rw [preserved.1]
        exact member)
  | grind stage choice =>
      have preserved :=
        run_grinding_choice_work_erased_preserves_samples_and_candidates table
          state next stage choice run
      rw [preserved.1]
      exact member
  | check checkpoint =>
      have equal : state = next := Option.some.inj run
      rw [← equal]
      exact member

theorem machine_events_work_erased_samples_included
    (table : FixedOracleTable) (events : List MachineEvent)
    (state final : EvalState)
    (run : runMachineEventsWorkErased table events state = some final) :
    SamplesIncluded state final := by
  induction events generalizing state with
  | nil =>
      rw [runMachineEventsWorkErased] at run
      have equal : state = final := Option.some.inj run
      subst final
      intro record member
      exact member
  | cons event rest ih =>
      rw [runMachineEventsWorkErased] at run
      obtain ⟨next, eventRun, restRun⟩ := Option.bind_eq_some_iff.mp run
      have head := machine_event_work_erased_samples_included table state next
        event eventRun
      have tail := ih (state := next) restRun
      intro record member
      exact tail record (head record member)

theorem machine_event_work_erased_candidates_included
    (table : FixedOracleTable) (state next : EvalState)
    (event : MachineEvent)
    (run : runMachineEventWorkErased table state event = some next) :
    CandidatesIncluded state next := by
  intro record member
  cases event with
  | absorb payload =>
      have preserved := absorb_step_preserves_samples_and_candidates table
        state next payload run
      rw [preserved.2]
      exact member
  | challenge id use =>
      rw [runMachineEventWorkErased] at run
      obtain ⟨pair, squeezeRun, result⟩ := Option.bind_eq_some_iff.mp run
      rcases pair with ⟨blocks, afterBlocks⟩
      have equal := Option.some.inj result
      rw [← equal]
      have preserved := squeeze_many_preserves_samples_and_candidates table
        (.challenge id) use.blocksUsed state afterBlocks blocks squeezeRun
      rw [preserved.2]
      exact member
  | grind stage choice =>
      have preserved :=
        run_grinding_choice_work_erased_preserves_samples_and_candidates table
          state next stage choice run
      rw [preserved.2]
      exact member
  | check checkpoint =>
      have equal : state = next := Option.some.inj run
      rw [← equal]
      exact member

theorem machine_events_work_erased_candidates_included
    (table : FixedOracleTable) (events : List MachineEvent)
    (state final : EvalState)
    (run : runMachineEventsWorkErased table events state = some final) :
    CandidatesIncluded state final := by
  induction events generalizing state with
  | nil =>
      rw [runMachineEventsWorkErased] at run
      have equal : state = final := Option.some.inj run
      subst final
      intro record member
      exact member
  | cons event rest ih =>
      rw [runMachineEventsWorkErased] at run
      obtain ⟨next, eventRun, restRun⟩ := Option.bind_eq_some_iff.mp run
      have head := machine_event_work_erased_candidates_included table state
        next event eventRun
      have tail := ih (state := next) restRun
      intro record member
      exact tail record (head record member)

/-! The finite trace wrapper used below carries literal microstep paths.  These
two induction lemmas expose the same complete-history/fixed-binding invariants
as the fuelled driver without introducing an abstract restoration map. -/

theorem nonterminal_trace_preserves_history_closed
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (state final : FutureFreeVerifierState) (steps : Nat)
    (pairs : List (ShaInput × ShaOutput))
    (closed : FutureFreeHistoryClosed state)
    (trace : NonterminalRawDriverTrace environment raw state steps pairs final) :
    FutureFreeHistoryClosed final := by
  induction trace with
  | stop state => exact closed
  | @next state middle final headPairs tailPairs tailSteps headPath
      _nonterminal rest ih =>
      have middleClosed :=
        raw_future_free_microstep_path_preserves_history_closed environment raw
          state middle headPairs closed headPath
      exact ih middleClosed

theorem nonterminal_trace_preserves_fixed_bindings
    (bindings : FixedBindings) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages)
    (state final : FutureFreeVerifierState) (steps : Nat)
    (pairs : List (ShaInput × ShaOutput))
    (fixed : FutureFreeBindingsFixed bindings state)
    (trace : NonterminalRawDriverTrace environment raw state steps pairs final) :
    FutureFreeBindingsFixed bindings final := by
  induction trace with
  | stop state => exact fixed
  | @next state middle final headPairs tailPairs tailSteps headPath
      _nonterminal rest ih =>
      have middleFixed :=
        raw_future_free_microstep_path_preserves_fixed_bindings bindings
          environment raw state middle headPairs fixed headPath
      exact ih middleFixed

/-! ## Exact challenge records generated by successful event execution -/

theorem challenge_event_work_erased_exposes_record
    (table : FixedOracleTable) (state next : EvalState)
    (id : ChallengeId) (use : SamplerUse id)
    (run : runMachineEventWorkErased table state (.challenge id use) =
      some next) :
    ∃ blocks afterBlocks,
      squeezeMany table (.challenge id) use.blocksUsed state =
        some (blocks, afterBlocks) ∧
      next = { afterBlocks with
        samples := afterBlocks.samples ++ [{ id := id, blocks := blocks }] } ∧
      blocks.length = use.blocksUsed ∧
      { id := id, blocks := blocks } ∈ next.samples := by
  rw [runMachineEventWorkErased] at run
  obtain ⟨pair, squeezeRun, result⟩ := Option.bind_eq_some_iff.mp run
  rcases pair with ⟨blocks, afterBlocks⟩
  have nextEqual :
      { afterBlocks with
        samples := afterBlocks.samples ++ [{ id := id, blocks := blocks }] } =
          next := Option.some.inj result
  have length := (squeeze_many_exact_sizes table (.challenge id)
    use.blocksUsed state afterBlocks blocks squeezeRun).1
  refine ⟨blocks, afterBlocks, squeezeRun, nextEqual.symm, length, ?_⟩
  rw [← nextEqual]
  simp

def StateSamplesDecodeAs (messages : Messages) (state : EvalState) : Prop :=
  ∀ record ∈ state.samples,
    exactDeterministicDecoders.qm31Parameter record.id record.blocks =
      some (messages.challengeValue record.id)

theorem state_samples_decode_of_included
    (messages : Messages) (before after : EvalState)
    (included : SamplesIncluded before after)
    (decoded : StateSamplesDecodeAs messages after) :
    StateSamplesDecodeAs messages before := by
  intro record member
  exact decoded record (included record member)

def StateCandidatesDecodeAs (state : EvalState) : Prop :=
  ∀ record ∈ state.candidates,
    exactDeterministicDecoders.candidate record.counter record.blocks =
      some record.outcome

theorem state_candidates_decode_of_included
    (before after : EvalState) (included : CandidatesIncluded before after)
    (decoded : StateCandidatesDecodeAs after) :
    StateCandidatesDecodeAs before := by
  intro record member
  exact decoded record (included record member)

theorem checked_work_erased_refinement_is_well_formed
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (raw : InteractiveRawTrace)
    (run : checkedRefineWorkErased table exactDeterministicDecoders tape =
      some raw) :
    TraceWellFormed table exactDeterministicDecoders tape raw := by
  classical
  unfold checkedRefineWorkErased at run
  split at run <;> simp_all
  rcases run with ⟨wellFormed, rawEq⟩
  subst raw
  exact wellFormed

theorem run_candidate_exposes_exact_record
    (table : FixedOracleTable) (state final : EvalState)
    (spec : CandidateSpec)
    (run : runCandidate table state spec = some final) :
    ∃ afterCounter blocks afterBlocks,
      absorbStep table state (.queryCandidate spec.counter) =
        some afterCounter ∧
      squeezeMany table (.queryCandidate spec.counter) spec.outcome.blocksUsed
        afterCounter = some (blocks, afterBlocks) ∧
      final = { afterBlocks with
        candidates := afterBlocks.candidates ++
          [{ counter := spec.counter
             outcome := spec.outcome
             baseDigest := state.digest
             endDigest := afterBlocks.digest
             blocks := blocks }] } ∧
      blocks.length = spec.outcome.blocksUsed ∧
      { counter := spec.counter
        outcome := spec.outcome
        baseDigest := state.digest
        endDigest := afterBlocks.digest
        blocks := blocks } ∈ final.candidates := by
  rw [runCandidate] at run
  obtain ⟨afterCounter, absorbRun, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨blockPair, squeezeRun, result⟩ := Option.bind_eq_some_iff.mp run
  rcases blockPair with ⟨blocks, afterBlocks⟩
  have finalEq : { afterBlocks with
      candidates := afterBlocks.candidates ++
        [{ counter := spec.counter
           outcome := spec.outcome
           baseDigest := state.digest
           endDigest := afterBlocks.digest
           blocks := blocks }] } = final := Option.some.inj result
  have length := (squeeze_many_exact_sizes table
    (.queryCandidate spec.counter) spec.outcome.blocksUsed afterCounter
    afterBlocks blocks squeezeRun).1
  refine ⟨afterCounter, blocks, afterBlocks, absorbRun, squeezeRun,
    finalEq.symm, length, ?_⟩
  rw [← finalEq]
  simp

theorem run_candidate_preserves_prior_candidates
    (table : FixedOracleTable) (state final : EvalState)
    (spec : CandidateSpec)
    (run : runCandidate table state spec = some final) :
    CandidatesIncluded state final := by
  obtain ⟨afterCounter, blocks, afterBlocks, absorbRun, squeezeRun,
      finalEq, _length, _member⟩ :=
    run_candidate_exposes_exact_record table state final spec run
  have afterAbsorb := absorb_step_preserves_samples_and_candidates table state
    afterCounter (.queryCandidate spec.counter) absorbRun
  have afterSqueeze := squeeze_many_preserves_samples_and_candidates table
    (.queryCandidate spec.counter) spec.outcome.blocksUsed afterCounter
    afterBlocks blocks squeezeRun
  intro record member
  rw [finalEq]
  simp only [List.mem_append]
  exact Or.inl (by
    rw [afterSqueeze.2, afterAbsorb.2]
    exact member)

theorem run_candidate_preserves_prior_samples
    (table : FixedOracleTable) (state final : EvalState)
    (spec : CandidateSpec)
    (run : runCandidate table state spec = some final) :
    SamplesIncluded state final := by
  obtain ⟨afterCounter, blocks, afterBlocks, absorbRun, squeezeRun,
      finalEq, _length, _member⟩ :=
    run_candidate_exposes_exact_record table state final spec run
  have afterAbsorb := absorb_step_preserves_samples_and_candidates table state
    afterCounter (.queryCandidate spec.counter) absorbRun
  have afterSqueeze := squeeze_many_preserves_samples_and_candidates table
    (.queryCandidate spec.counter) spec.outcome.blocksUsed afterCounter
    afterBlocks blocks squeezeRun
  intro record member
  rw [finalEq]
  rw [afterSqueeze.1, afterAbsorb.1]
  exact member

theorem run_discarded_candidates_preserves_prior_candidates
    (table : FixedOracleTable) (base : Digest256)
    (specs : List CandidateSpec) (state final : EvalState)
    (run : runDiscardedCandidates table base specs state = some final) :
    CandidatesIncluded state final := by
  induction specs generalizing state with
  | nil =>
      rw [runDiscardedCandidates] at run
      have equal : state = final := Option.some.inj run
      subst final
      intro record member
      exact member
  | cons spec rest ih =>
      rw [runDiscardedCandidates] at run
      obtain ⟨branch, branchRun, restRun⟩ := Option.bind_eq_some_iff.mp run
      have head := run_candidate_preserves_prior_candidates table state branch
        spec branchRun
      have tail := ih (state := restoreDigest base branch) restRun
      intro record member
      exact tail record (by
        change record ∈ branch.candidates
        exact head record member)

theorem run_discarded_candidates_preserves_prior_samples
    (table : FixedOracleTable) (base : Digest256)
    (specs : List CandidateSpec) (state final : EvalState)
    (run : runDiscardedCandidates table base specs state = some final) :
    SamplesIncluded state final := by
  induction specs generalizing state with
  | nil =>
      rw [runDiscardedCandidates] at run
      have equal : state = final := Option.some.inj run
      subst final
      intro record member
      exact member
  | cons spec rest ih =>
      rw [runDiscardedCandidates] at run
      obtain ⟨branch, branchRun, restRun⟩ := Option.bind_eq_some_iff.mp run
      have head := run_candidate_preserves_prior_samples table state branch spec
        branchRun
      have tail := ih (state := restoreDigest base branch) restRun
      intro record member
      exact tail record (by
        change record ∈ branch.samples
        exact head record member)

theorem run_q16_preserves_prior_samples
    (table : FixedOracleTable) (state final : EvalState) (tape : Q16Tape)
    (run : runQ16 table state tape = some final) :
    SamplesIncluded state final := by
  rw [runQ16] at run
  obtain ⟨beforeSelected, earlierRun, selectedRun⟩ :=
    Option.bind_eq_some_iff.mp run
  have earlier := run_discarded_candidates_preserves_prior_samples table
    state.digest tape.earlier state beforeSelected earlierRun
  have selected := run_candidate_preserves_prior_samples table beforeSelected
    final tape.selected selectedRun
  intro record member
  exact selected record (earlier record member)

theorem run_q16_preserves_prior_candidates
    (table : FixedOracleTable) (state final : EvalState) (tape : Q16Tape)
    (run : runQ16 table state tape = some final) :
    CandidatesIncluded state final := by
  rw [runQ16] at run
  obtain ⟨beforeSelected, earlierRun, selectedRun⟩ :=
    Option.bind_eq_some_iff.mp run
  have earlier := run_discarded_candidates_preserves_prior_candidates table
    state.digest tape.earlier state beforeSelected earlierRun
  have selected := run_candidate_preserves_prior_candidates table beforeSelected
    final tape.selected selectedRun
  intro record member
  exact selected record (earlier record member)

/-! ## Exact incremental challenge chains -/

inductive EvaluatorSqueezeChain (table : FixedOracleTable)
    (owner : SqueezeOwner) :
    Nat → EvalState → List Digest256 → EvalState → Prop where
  | done (first : Nat) (state : EvalState) :
      EvaluatorSqueezeChain table owner first state [] state
  | next {first : Nat} {state middle final : EvalState}
      {output : Digest256} {outputs : List Digest256}
      (head : squeezeStep table state owner first = some (output, middle))
      (tail : EvaluatorSqueezeChain table owner (first + 1) middle outputs
        final) :
      EvaluatorSqueezeChain table owner first state (output :: outputs) final

theorem evaluator_squeeze_chain_of_run
    (table : FixedOracleTable) (owner : SqueezeOwner)
    (first count : Nat) (state final : EvalState)
    (outputs : List Digest256)
    (run : squeezeManyFrom table owner first count state =
      some (outputs, final)) :
    EvaluatorSqueezeChain table owner first state outputs final := by
  induction count generalizing first state outputs final with
  | zero =>
      rw [squeezeManyFrom] at run
      cases Option.some.inj run
      exact .done first state
  | succ count ih =>
      rw [squeezeManyFrom] at run
      obtain ⟨headPair, headRun, run⟩ := Option.bind_eq_some_iff.mp run
      rcases headPair with ⟨output, middle⟩
      obtain ⟨tailPair, tailRun, result⟩ := Option.bind_eq_some_iff.mp run
      rcases tailPair with ⟨tailOutputs, tailState⟩
      cases Option.some.inj result
      exact .next headRun
        (ih (first := first + 1) (state := middle)
          (outputs := tailOutputs) (final := final) tailRun)

def linearChallengeControl (id : ChallengeId)
    (outputs : List Digest256) (remaining : List FutureFreeSlot) :
    FutureFreeControl :=
  match outputs with
  | [] => .linear (.challenge id :: remaining)
  | outputs => .sampleChallenge id outputs remaining

@[simp] theorem linear_challenge_control_nil
    (id : ChallengeId) (remaining : List FutureFreeSlot) :
    linearChallengeControl id [] remaining =
      .linear (.challenge id :: remaining) := rfl

@[simp] theorem linear_challenge_control_cons
    (id : ChallengeId) (output : Digest256) (outputs : List Digest256)
    (remaining : List FutureFreeSlot) :
    linearChallengeControl id (output :: outputs) remaining =
      .sampleChallenge id (output :: outputs) remaining := rfl

def ChallengeSecureMapAccepted (environment : FutureFreeEnvironment)
    (id : ChallengeId) (value : Qm31Bytes) : Prop :=
  match id with
  | .circlePoint _ => ∃ point, environment.decoders.secureCirclePoint value =
      some point
  | _ => True

theorem accepted_challenge_block_completes_linear_slot
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (id : ChallengeId) (outputs : List Digest256)
    (remaining : List FutureFreeSlot) (output : Digest256)
    (nextCore : RuntimeCore) (value : Qm31Bytes)
    (decoded : environment.decoders.qm31Parameter id (outputs ++ [output]) =
      some value)
    (secure : ChallengeSecureMapAccepted environment id value) :
    (processFutureFreeChallengeBlock environment snapshot id outputs remaining
      output nextCore).control = linearOrDone remaining := by
  cases id <;>
    simp_all [processFutureFreeChallengeBlock, completeFutureFreeChallenge,
      ChallengeSecureMapAccepted]
  case circlePoint sample =>
    obtain ⟨point, pointEq⟩ := secure
    simp [processFutureFreeChallengeBlock, completeFutureFreeChallenge,
      decoded, pointEq]

theorem process_future_free_challenge_block_preserves_core
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (id : ChallengeId) (outputs : List Digest256)
    (remaining : List FutureFreeSlot) (output : Digest256)
    (nextCore : RuntimeCore) :
    (processFutureFreeChallengeBlock environment snapshot id outputs remaining
      output nextCore).core = nextCore := by
  unfold processFutureFreeChallengeBlock
  cases decoded : environment.decoders.qm31Parameter id
      (outputs ++ [output]) with
  | none =>
      simp only [decoded]
      split <;> rfl
  | some value =>
      cases id <;> simp only [decoded, completeFutureFreeChallenge]
      split <;> rfl

theorem undecoded_challenge_block_continues_incrementally
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (id : ChallengeId) (outputs : List Digest256)
    (remaining : List FutureFreeSlot) (output : Digest256)
    (nextCore : RuntimeCore)
    (undecoded : environment.decoders.qm31Parameter id
      (outputs ++ [output]) = none)
    (belowCap : (outputs ++ [output]).length <
      samplerBlockCap (samplerMode id)) :
    (processFutureFreeChallengeBlock environment snapshot id outputs remaining
      output nextCore).control =
        .sampleChallenge id (outputs ++ [output]) remaining := by
  simp only [processFutureFreeChallengeBlock, undecoded, belowCap, if_pos]

/-- One evaluator squeeze block is exactly one table-backed future-free
microstep at a linear challenge site.  The controller itself decides whether
the updated accumulated block list completes or continues the sampler. -/
theorem linear_challenge_squeeze_run_gives_future_free_step
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (before after : EvalState) (id : ChallengeId)
    (outputs : List Digest256) (remaining : List FutureFreeSlot)
    (block : Nat) (output : Digest256)
    (atControl : state.current.control =
      linearChallengeControl id outputs remaining)
    (blockIndex : block = outputs.length)
    (same : SameDigest state.current.core before)
    (run : squeezeStep table before (.challenge id) block =
      some (output, after))
    (resultNonterminal : isDriverHalt
      (processFutureFreeChallengeBlock environment state.current id outputs
        remaining output
        { state.current.core with digest := after.digest }).control = false) :
    ∃ pairs next,
      NonterminalRawDriverTrace environment raw state 1 pairs next ∧
      PathUsesFixedTable table pairs ∧
      next.current.control =
        (processFutureFreeChallengeBlock environment state.current id outputs
          remaining output
          { state.current.core with digest := after.digest }).control ∧
      next.current.core =
        { state.current.core with digest := after.digest } ∧
      SameDigest next.current.core after ∧
      next.current.q16Candidates = state.current.q16Candidates := by
  have noSubmission : submitNextRawMessage raw state = none := by
    cases outputs with
    | nil => simp [submitNextRawMessage, atControl]
    | cons head tail => simp [submitNextRawMessage, atControl]
  have forced : state.current.control.nextVerifierAction? =
      some (.squeezePair (.challenge id) block) := by
    rw [atControl, blockIndex]
    cases outputs <;> rfl
  obtain ⟨derived, applied, _pairs, _replyPath, _supported⟩ :=
    evaluator_squeeze_derives_exact_future_free_reply table state before after
      (.challenge id) block output same run
  let nextCore : RuntimeCore :=
    { state.current.core with digest := after.digest }
  let processed := processFutureFreeChallengeBlock environment state.current
    id outputs remaining output nextCore
  let nextSnapshot : FutureFreeSnapshot :=
    { processed with bindings := state.current.bindings }
  let next := appendFutureFreeSnapshot state
    (.verifier (.squeezePair (.challenge id) block)
      (.squeeze output after.digest)) nextSnapshot
  have updated : afterFutureFreeVerifierReply environment state.current
      (.squeeze output after.digest) nextCore = some nextSnapshot := by
    unfold afterFutureFreeVerifierReply
    cases outputs with
    | nil =>
        simp [rawAfterFutureFreeVerifierReply, atControl, processed,
          nextSnapshot, nextCore]
    | cons head tail =>
        simp [rawAfterFutureFreeVerifierReply, atControl, processed,
          nextSnapshot, nextCore]
  have advanced : advanceFutureFreeVerifier environment state
      (.squeeze output after.digest) = some next := by
    simpa [next] using advance_future_free_verifier_of_components environment
      state (.squeezePair (.challenge id) block)
      (.squeeze output after.digest) nextCore nextSnapshot forced applied updated
  have nextControl : next.current.control = processed.control := by rfl
  have nextCoreEq : next.current.core = nextCore := by
    change processed.core = nextCore
    exact process_future_free_challenge_block_preserves_core environment
      state.current id outputs remaining output nextCore
  have nonterminal : isDriverHalt next.current.control = false := by
    rw [nextControl]
    exact resultNonterminal
  obtain ⟨pairs, trace, supported⟩ :=
    fixed_table_action_gives_one_nonterminal_trace table environment raw
      state next (.squeezePair (.challenge id) block)
      (.squeeze output after.digest) noSubmission forced derived advanced
      nonterminal
  refine ⟨pairs, next, trace, supported, nextControl, nextCoreEq, ?_, ?_⟩
  · rw [nextCoreEq]
    rfl
  · change processed.q16Candidates = state.current.q16Candidates
    unfold processed processFutureFreeChallengeBlock
    dsimp only
    split
    · rename_i value decoded
      cases id <;> simp [completeFutureFreeChallenge] <;> split <;> rfl
    · split <;> rfl

/-- A complete exact evaluator squeeze chain is replayed incrementally.  Exact
decoder prefix-minimality forces every proper prefix to continue and the last
block to finish, so the fixed tape cannot choose a convenient stopping point. -/
theorem evaluator_challenge_chain_gives_future_free_trace
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (before after : EvalState) (id : ChallengeId)
    (already fresh : List Digest256) (remaining : List FutureFreeSlot)
    (first : Nat) (value : Qm31Bytes)
    (chain : EvaluatorSqueezeChain table (.challenge id) first before fresh
      after)
    (atControl : state.current.control =
      linearChallengeControl id already remaining)
    (firstIndex : first = already.length)
    (same : SameDigest state.current.core before)
    (accepted : environment.decoders.qm31Parameter id (already ++ fresh) =
      some value)
    (withinCap : (already ++ fresh).length ≤
      samplerBlockCap (samplerMode id))
    (freshNonempty : fresh ≠ [])
    (remainingNonempty : remaining ≠ [])
    (secure : ChallengeSecureMapAccepted environment id value) :
    ∃ pairs final,
      NonterminalRawDriverTrace environment raw state fresh.length pairs final ∧
      PathUsesFixedTable table pairs ∧
      final.current.control = .linear remaining ∧
      SameDigest final.current.core after ∧
      final.current.q16Candidates = state.current.q16Candidates := by
  induction chain generalizing state already with
  | done first before =>
      exact False.elim (freshNonempty rfl)
  | @next first before middle after output outputs head tail ih =>
      have minimal := accepted_future_free_challenge_is_prefix_minimal
        environment id (already ++ output :: outputs) value accepted
      by_cases tailEmpty : outputs = []
      · subst outputs
        cases tail
        have decodedLast : environment.decoders.qm31Parameter id
            (already ++ [output]) = some value := by
          simpa using accepted
        have completes := accepted_challenge_block_completes_linear_slot
          environment state.current id already remaining output
          { state.current.core with digest := middle.digest } value decodedLast
          secure
        have resultNonterminal : isDriverHalt
            (processFutureFreeChallengeBlock environment state.current id
              already remaining output
              { state.current.core with digest := middle.digest }).control =
              false := by
          rw [completes]
          cases remaining with
          | nil => exact False.elim (remainingNonempty rfl)
          | cons slot rest => rfl
        obtain ⟨pairs, final, trace, supported, finalControl, _finalCore,
            finalSame, finalCandidates⟩ :=
          linear_challenge_squeeze_run_gives_future_free_step table environment
            raw state before middle id already remaining first output atControl
            firstIndex same head resultNonterminal
        refine ⟨pairs, final, ?_, supported, ?_, ?_, finalCandidates⟩
        · simpa using trace
        · rw [finalControl, completes]
          cases remaining with
          | nil => exact False.elim (remainingNonempty rfl)
          | cons slot rest => rfl
        · exact finalSame
      · obtain ⟨nextOutput, restOutputs, outputsEq⟩ :=
          List.exists_cons_of_ne_nil tailEmpty
        subst outputs
        let accumulated := already ++ [output]
        have totalEq : already ++ output :: nextOutput :: restOutputs =
            accumulated ++ nextOutput :: restOutputs := by
          simp [accumulated, List.append_assoc]
        have accumulatedShort : accumulated.length <
            (already ++ output :: nextOutput :: restOutputs).length := by
          simp [accumulated]
        have takeEq :
            (already ++ output :: nextOutput :: restOutputs).take
                accumulated.length = accumulated := by
          rw [totalEq, List.take_append_of_le_length (Nat.le_refl _),
            List.take_length]
        have undecoded : environment.decoders.qm31Parameter id accumulated =
            none := by
          rw [← takeEq]
          exact minimal accumulated.length accumulatedShort
        have accumulatedBelowCap : accumulated.length <
            samplerBlockCap (samplerMode id) := by
          have totalLength :
              (already ++ output :: nextOutput :: restOutputs).length ≤
                samplerBlockCap (samplerMode id) := by
            simpa using withinCap
          omega
        have continues := undecoded_challenge_block_continues_incrementally
          environment state.current id already remaining output
          { state.current.core with digest := middle.digest } undecoded
          (by simpa [accumulated] using accumulatedBelowCap)
        have resultNonterminal : isDriverHalt
            (processFutureFreeChallengeBlock environment state.current id
              already remaining output
              { state.current.core with digest := middle.digest }).control =
              false := by
          rw [continues]
          rfl
        obtain ⟨headPairs, nextState, headTrace, headSupported, nextControl,
            _nextCore, nextSame, nextCandidates⟩ :=
          linear_challenge_squeeze_run_gives_future_free_step table environment
            raw state before middle id already remaining first output atControl
            firstIndex same head resultNonterminal
        have nextAtControl : nextState.current.control =
            linearChallengeControl id accumulated remaining := by
          rw [nextControl, continues]
          simp [linearChallengeControl, accumulated]
        have nextFirstIndex : first + 1 = accumulated.length := by
          simp [accumulated, firstIndex]
        have tailAccepted : environment.decoders.qm31Parameter id
            (accumulated ++ nextOutput :: restOutputs) = some value := by
          rw [← totalEq]
          exact accepted
        have tailWithinCap :
            (accumulated ++ nextOutput :: restOutputs).length ≤
              samplerBlockCap (samplerMode id) := by
          rw [← totalEq]
          exact withinCap
        obtain ⟨tailPairs, final, tailTrace, tailSupported, finalControl,
            finalSame, finalCandidates⟩ :=
          ih (state := nextState) (already := accumulated) nextAtControl
            nextFirstIndex nextSame tailAccepted tailWithinCap (by simp)
        refine ⟨headPairs ++ tailPairs, final, ?_, ?_, finalControl,
          finalSame, ?_⟩
        · have combined := nonterminal_raw_driver_trace_append environment raw
            state nextState final 1 (nextOutput :: restOutputs).length
            headPairs tailPairs headTrace tailTrace
          simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using combined
        · exact path_uses_fixed_table_append table headPairs tailPairs
            headSupported tailSupported
        · exact finalCandidates.trans nextCandidates

/-! ## Exact lambda/chi incremental chains -/

/-- The two early adaptive samplers share one operational shape, but chi
retains the lambda decoded by the immediately preceding sampler. -/
inductive EarlyAdaptiveSampler where
  | lambda
  | chiAfter (lambda : Qm31Bytes)

def EarlyAdaptiveSampler.challengeId : EarlyAdaptiveSampler → ChallengeId
  | .lambda => .lambda
  | .chiAfter _ => .chi

def EarlyAdaptiveSampler.control (site : EarlyAdaptiveSampler)
    (outputs : List Digest256) : OpenAdaptiveControl :=
  match site with
  | .lambda => .sampleLambda outputs
  | .chiAfter lambdaValue => .sampleChi lambdaValue outputs

def EarlyAdaptiveSampler.finished (site : EarlyAdaptiveSampler)
    (value : Qm31Bytes) : OpenAdaptiveControl :=
  match site with
  | .lambda => .sampleChi value []
  | .chiAfter lambdaValue => .awaitingC2 lambdaValue value

@[simp] theorem early_adaptive_sampler_forces_exact_next_block
    (site : EarlyAdaptiveSampler) (outputs : List Digest256) :
    (site.control outputs).nextVerifierAction? =
      some (.squeezePair (.challenge site.challengeId) outputs.length) := by
  cases site <;> simp [EarlyAdaptiveSampler.control,
    EarlyAdaptiveSampler.challengeId, OpenAdaptiveControl.nextVerifierAction?]

@[simp] theorem early_adaptive_finished_remains_adaptive
    (site : EarlyAdaptiveSampler) (value : Qm31Bytes) :
    controlAfterOpenAdaptiveReply (site.finished value) =
      .adaptive (site.finished value) := by
  cases site <;> simp [EarlyAdaptiveSampler.finished,
    controlAfterOpenAdaptiveReply]

@[simp] theorem early_adaptive_accumulator_remains_adaptive
    (site : EarlyAdaptiveSampler) (outputs : List Digest256) :
    controlAfterOpenAdaptiveReply (site.control outputs) =
      .adaptive (site.control outputs) := by
  cases site <;> simp [EarlyAdaptiveSampler.control,
    controlAfterOpenAdaptiveReply]

theorem early_adaptive_decode_success_forces_next_phase
    (environment : FutureFreeEnvironment) (site : EarlyAdaptiveSampler)
    (outputs : List Digest256) (output advance : Digest256)
    (value : Qm31Bytes)
    (decoded : environment.decoders.qm31Parameter site.challengeId
      (outputs ++ [output]) = some value) :
    (site.control outputs).afterVerifierReply environment.decoders
      (.squeeze output advance) = some (site.finished value) := by
  cases site with
  | lambda =>
      simpa [EarlyAdaptiveSampler.control, EarlyAdaptiveSampler.finished,
        EarlyAdaptiveSampler.challengeId] using
        open_lambda_decode_success_forces_chi_next environment.decoders
          outputs output advance value decoded
  | chiAfter lambdaValue =>
      simpa [EarlyAdaptiveSampler.control, EarlyAdaptiveSampler.finished,
        EarlyAdaptiveSampler.challengeId] using
        open_chi_decode_success_is_the_only_c2_gate environment.decoders
          lambdaValue outputs output advance value decoded

theorem early_adaptive_decode_failure_continues_accumulator
    (environment : FutureFreeEnvironment) (site : EarlyAdaptiveSampler)
    (outputs : List Digest256) (output advance : Digest256)
    (undecoded : environment.decoders.qm31Parameter site.challengeId
      (outputs ++ [output]) = none)
    (belowCap : (outputs ++ [output]).length <
      samplerBlockCap (samplerMode site.challengeId)) :
    (site.control outputs).afterVerifierReply environment.decoders
      (.squeeze output advance) =
        some (site.control (outputs ++ [output])) := by
  have belowCap' : outputs.length + 1 <
      samplerBlockCap (samplerMode site.challengeId) := by
    simpa using belowCap
  cases site with
  | lambda =>
      simp only [EarlyAdaptiveSampler.control,
        EarlyAdaptiveSampler.challengeId, samplerMode] at undecoded belowCap' ⊢
      simp [OpenAdaptiveControl.afterVerifierReply, undecoded, belowCap']
  | chiAfter lambda =>
      simp only [EarlyAdaptiveSampler.control,
        EarlyAdaptiveSampler.challengeId, samplerMode] at undecoded belowCap' ⊢
      simp [OpenAdaptiveControl.afterVerifierReply, undecoded, belowCap']

theorem early_adaptive_control_has_no_raw_submission
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (site : EarlyAdaptiveSampler) (outputs : List Digest256)
    (atControl : state.current.control = .adaptive (site.control outputs)) :
    submitNextRawMessage raw state = none := by
  cases site <;> simp [submitNextRawMessage, EarlyAdaptiveSampler.control,
    atControl]

/-- An exact evaluator chain for lambda or chi is consumed one paired squeeze
at a time.  Prefix-minimality proves that no proper block prefix can advance
the adaptive control, while the final block alone opens the next phase. -/
theorem evaluator_early_adaptive_chain_gives_future_free_trace
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (before after : EvalState) (site : EarlyAdaptiveSampler)
    (already fresh : List Digest256) (first : Nat) (value : Qm31Bytes)
    (chain : EvaluatorSqueezeChain table (.challenge site.challengeId) first
      before fresh after)
    (atControl : state.current.control = .adaptive (site.control already))
    (firstIndex : first = already.length)
    (same : SameDigest state.current.core before)
    (accepted : environment.decoders.qm31Parameter site.challengeId
      (already ++ fresh) = some value)
    (withinCap : (already ++ fresh).length ≤
      samplerBlockCap (samplerMode site.challengeId))
    (freshNonempty : fresh ≠ []) :
    ∃ pairs final,
      NonterminalRawDriverTrace environment raw state fresh.length pairs final ∧
      PathUsesFixedTable table pairs ∧
      final.current.control = .adaptive (site.finished value) ∧
      SameDigest final.current.core after ∧
      final.current.q16Candidates = state.current.q16Candidates := by
  induction chain generalizing state already with
  | done first before =>
      exact False.elim (freshNonempty rfl)
  | @next first before middle after output outputs head tail ih =>
      have minimal := accepted_future_free_challenge_is_prefix_minimal
        environment site.challengeId (already ++ output :: outputs) value
          accepted
      cases outputs with
      | nil =>
          cases tail
          have decodedLast : environment.decoders.qm31Parameter
              site.challengeId (already ++ [output]) = some value := by
            simpa using accepted
          have decodedControl := early_adaptive_decode_success_forces_next_phase
            environment site already output middle.digest value decodedLast
          have noSubmission := early_adaptive_control_has_no_raw_submission raw
            state site already atControl
          have nextNonterminal : isDriverHalt
              (controlAfterOpenAdaptiveReply (site.finished value)) = false := by
            rw [early_adaptive_finished_remains_adaptive]
            cases site <;> rfl
          obtain ⟨pairs, final, trace, supported, finalControl, _finalCore,
              finalSame, finalCandidates⟩ :=
            open_adaptive_squeeze_run_gives_future_free_step table environment
              raw state before middle (site.control already)
              (site.finished value) (.challenge site.challengeId) first output
              atControl (by simpa [firstIndex]) same head noSubmission
              decodedControl nextNonterminal
          refine ⟨pairs, final, ?_, supported, ?_, finalSame,
            finalCandidates⟩
          · simpa using trace
          · rw [finalControl, early_adaptive_finished_remains_adaptive]
      | cons nextOutput restOutputs =>
          let accumulated := already ++ [output]
          have totalEq : already ++ output :: nextOutput :: restOutputs =
              accumulated ++ nextOutput :: restOutputs := by
            simp [accumulated, List.append_assoc]
          have accumulatedShort : accumulated.length <
              (already ++ output :: nextOutput :: restOutputs).length := by
            simp [accumulated]
          have takeEq :
              (already ++ output :: nextOutput :: restOutputs).take
                  accumulated.length = accumulated := by
            rw [totalEq, List.take_append_of_le_length (Nat.le_refl _),
              List.take_length]
          have undecoded : environment.decoders.qm31Parameter
              site.challengeId accumulated = none := by
            rw [← takeEq]
            exact minimal accumulated.length accumulatedShort
          have accumulatedBelowCap : accumulated.length <
              samplerBlockCap (samplerMode site.challengeId) := by
            have totalLength :
                (already ++ output :: nextOutput :: restOutputs).length ≤
                  samplerBlockCap (samplerMode site.challengeId) := by
              simpa using withinCap
            omega
          have continues := early_adaptive_decode_failure_continues_accumulator
            environment site already output middle.digest undecoded
              (by simpa [accumulated] using accumulatedBelowCap)
          have noSubmission := early_adaptive_control_has_no_raw_submission raw
            state site already atControl
          have nextNonterminal : isDriverHalt
              (controlAfterOpenAdaptiveReply (site.control accumulated)) =
                false := by
            rw [early_adaptive_accumulator_remains_adaptive]
            cases site <;> rfl
          obtain ⟨headPairs, nextState, headTrace, headSupported,
              nextControl, _nextCore, nextSame, nextCandidates⟩ :=
            open_adaptive_squeeze_run_gives_future_free_step table environment
              raw state before middle (site.control already)
              (site.control accumulated) (.challenge site.challengeId) first
              output atControl (by simpa [firstIndex]) same head noSubmission
              continues nextNonterminal
          have nextAtControl : nextState.current.control =
              .adaptive (site.control accumulated) := by
            rw [nextControl, early_adaptive_accumulator_remains_adaptive]
          have nextFirstIndex : first + 1 = accumulated.length := by
            simp [accumulated, firstIndex]
          have tailAccepted : environment.decoders.qm31Parameter
              site.challengeId
                (accumulated ++ nextOutput :: restOutputs) = some value := by
            rw [← totalEq]
            exact accepted
          have tailWithinCap :
              (accumulated ++ nextOutput :: restOutputs).length ≤
                samplerBlockCap (samplerMode site.challengeId) := by
            rw [← totalEq]
            exact withinCap
          obtain ⟨tailPairs, final, tailTrace, tailSupported, finalControl,
              finalSame, finalCandidates⟩ :=
            ih (state := nextState) (already := accumulated) nextAtControl
              nextFirstIndex nextSame tailAccepted tailWithinCap (by simp)
          refine ⟨headPairs ++ tailPairs, final, ?_, ?_, finalControl,
            finalSame, ?_⟩
          · have combined := nonterminal_raw_driver_trace_append environment raw
              state nextState final 1 (nextOutput :: restOutputs).length
              headPairs tailPairs headTrace tailTrace
            simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using combined
          · exact path_uses_fixed_table_append table headPairs tailPairs
              headSupported tailSupported
          · exact finalCandidates.trans nextCandidates

/-- A successful evaluator challenge event contains the exact block list
recorded by the checked refinement.  When that record is decoder-valid, the
same blocks drive the early future-free sampler to its unique next phase. -/
theorem early_challenge_event_run_gives_future_free_trace
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (messages : Messages) (raw : RawTag73ProverMessages)
    (state : FutureFreeVerifierState) (before eventAfter : EvalState)
    (site : EarlyAdaptiveSampler)
    (atControl : state.current.control = .adaptive (site.control []))
    (same : SameDigest state.current.core before)
    (decoderEq : environment.decoders = exactDeterministicDecoders)
    (eventRun : runMachineEventWorkErased table before
      (challengeEvent messages site.challengeId) = some eventAfter)
    (allDecoded : StateSamplesDecodeAs messages eventAfter) :
    ∃ (blocks : List Digest256)
      (pairs : List (ShaInput × ShaOutput))
      (final : FutureFreeVerifierState),
      blocks.length = (messages.challengeUse site.challengeId).blocksUsed ∧
      NonterminalRawDriverTrace environment raw state blocks.length pairs final ∧
      PathUsesFixedTable table pairs ∧
      final.current.control =
        .adaptive (site.finished (messages.challengeValue site.challengeId)) ∧
      SameDigest final.current.core eventAfter ∧
      final.current.q16Candidates = state.current.q16Candidates := by
  have normalizedRun : runMachineEventWorkErased table before
      (.challenge site.challengeId (messages.challengeUse site.challengeId)) =
        some eventAfter := by
    simpa [challengeEvent] using eventRun
  obtain ⟨blocks, afterBlocks, squeezeRun, eventAfterEq, blocksLength,
      recordMember⟩ :=
    challenge_event_work_erased_exposes_record table before eventAfter
      site.challengeId (messages.challengeUse site.challengeId) normalizedRun
  have acceptedExact : exactDeterministicDecoders.qm31Parameter
      site.challengeId blocks =
        some (messages.challengeValue site.challengeId) :=
    allDecoded { id := site.challengeId, blocks := blocks } recordMember
  have accepted : environment.decoders.qm31Parameter site.challengeId blocks =
      some (messages.challengeValue site.challengeId) := by
    rw [decoderEq]
    exact acceptedExact
  have withinCap : blocks.length ≤
      samplerBlockCap (samplerMode site.challengeId) := by
    rw [blocksLength]
    exact (messages.challengeUse site.challengeId).withinDeployedCap
  have blocksNonempty : blocks ≠ [] := by
    intro empty
    have zero : blocks.length = 0 := by simp [empty]
    have positive := (messages.challengeUse site.challengeId).consumesBlock
    omega
  have chain : EvaluatorSqueezeChain table
      (.challenge site.challengeId) 0 before blocks afterBlocks := by
    exact evaluator_squeeze_chain_of_run table (.challenge site.challengeId) 0
      (messages.challengeUse site.challengeId).blocksUsed before afterBlocks
      blocks (by simpa [squeezeMany] using squeezeRun)
  obtain ⟨pairs, final, trace, supported, finalControl, finalSame,
      finalCandidates⟩ :=
    evaluator_early_adaptive_chain_gives_future_free_trace table environment
      raw state before afterBlocks site [] blocks 0
      (messages.challengeValue site.challengeId) chain atControl rfl same
      (by simpa using accepted) (by simpa using withinCap) blocksNonempty
  refine ⟨blocks, pairs, final, blocksLength, trace, supported, finalControl,
    ?_, finalCandidates⟩
  have digestEq : afterBlocks.digest = eventAfter.digest := by
    rw [eventAfterEq]
  exact finalSame.trans digestEq

/-- The corresponding wrapper for every post-C2 linear challenge, including
the two secure-circle parameters.  Secure-circle admissibility is an explicit
decoder fact, not inferred from schedule exhaustion. -/
theorem linear_challenge_event_run_gives_future_free_trace
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (messages : Messages) (raw : RawTag73ProverMessages)
    (state : FutureFreeVerifierState) (before eventAfter : EvalState)
    (id : ChallengeId) (remaining : List FutureFreeSlot)
    (atControl : state.current.control =
      .linear (.challenge id :: remaining))
    (same : SameDigest state.current.core before)
    (decoderEq : environment.decoders = exactDeterministicDecoders)
    (eventRun : runMachineEventWorkErased table before
      (challengeEvent messages id) = some eventAfter)
    (allDecoded : StateSamplesDecodeAs messages eventAfter)
    (secure : ChallengeSecureMapAccepted environment id
      (messages.challengeValue id))
    (remainingNonempty : remaining ≠ []) :
    ∃ (blocks : List Digest256)
      (pairs : List (ShaInput × ShaOutput))
      (final : FutureFreeVerifierState),
      blocks.length = (messages.challengeUse id).blocksUsed ∧
      NonterminalRawDriverTrace environment raw state blocks.length pairs final ∧
      PathUsesFixedTable table pairs ∧
      final.current.control = .linear remaining ∧
      SameDigest final.current.core eventAfter ∧
      final.current.q16Candidates = state.current.q16Candidates := by
  have normalizedRun : runMachineEventWorkErased table before
      (.challenge id (messages.challengeUse id)) = some eventAfter := by
    simpa [challengeEvent] using eventRun
  obtain ⟨blocks, afterBlocks, squeezeRun, eventAfterEq, blocksLength,
      recordMember⟩ :=
    challenge_event_work_erased_exposes_record table before eventAfter id
      (messages.challengeUse id) normalizedRun
  have acceptedExact : exactDeterministicDecoders.qm31Parameter id blocks =
      some (messages.challengeValue id) :=
    allDecoded { id := id, blocks := blocks } recordMember
  have accepted : environment.decoders.qm31Parameter id blocks =
      some (messages.challengeValue id) := by
    rw [decoderEq]
    exact acceptedExact
  have withinCap : blocks.length ≤
      samplerBlockCap (samplerMode id) := by
    rw [blocksLength]
    exact (messages.challengeUse id).withinDeployedCap
  have blocksNonempty : blocks ≠ [] := by
    intro empty
    have zero : blocks.length = 0 := by simp [empty]
    have positive := (messages.challengeUse id).consumesBlock
    omega
  have chain : EvaluatorSqueezeChain table (.challenge id) 0 before blocks
      afterBlocks := by
    exact evaluator_squeeze_chain_of_run table (.challenge id) 0
      (messages.challengeUse id).blocksUsed before afterBlocks blocks
      (by simpa [squeezeMany] using squeezeRun)
  obtain ⟨pairs, final, trace, supported, finalControl, finalSame,
      finalCandidates⟩ :=
    evaluator_challenge_chain_gives_future_free_trace table environment raw
      state before afterBlocks id [] blocks remaining 0
      (messages.challengeValue id) chain atControl rfl same
      (by simpa using accepted) (by simpa using withinCap) blocksNonempty
      remainingNonempty secure
  refine ⟨blocks, pairs, final, blocksLength, trace, supported, finalControl,
    ?_, finalCandidates⟩
  have digestEq : afterBlocks.digest = eventAfter.digest := by
    rw [eventAfterEq]
  exact finalSame.trans digestEq

/-! ## The live adaptive C2 round -/

/-- Once the incremental chi decoder opens the C2 gate, the raw C2 bytes are
wrapped at the *live* lambda/chi indices.  This zero-query prover transition
does not import either index from the completed fixed tape. -/
theorem awaiting_c2_submits_live_raw_commitment
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (lambda chi : Qm31Bytes)
    (atC2 : state.current.control = .adaptive (.awaitingC2 lambda chi)) :
    ∃ next,
      NonterminalRawDriverTrace environment raw state 1 [] next ∧
      PathUsesFixedTable table [] ∧
      next.current.control = .adaptive
        (.requestC2Salt lambda chi (raw.c2Commitment lambda chi)) ∧
      next.current.c2Root = some raw.c2Root ∧
      next.current.core = state.current.core ∧
      next.current.bindings = state.current.bindings ∧
      next.current.q16Candidates = state.current.q16Candidates := by
  let commitment := raw.c2Commitment lambda chi
  let next := submitFutureFreeC2 state lambda chi commitment atC2
  have submitted : submitNextRawMessage raw state = some next := by
    unfold submitNextRawMessage
    split
    next => simp_all
    next lambdaValue chiValue controlEq =>
      have parameters := controlEq.symm.trans atC2
      cases parameters
      simp [next, commitment, submitFutureFreeC2]
    all_goals simp_all
  have nonterminal : isDriverHalt next.current.control = false := by rfl
  obtain ⟨trace, supported⟩ :=
    raw_submission_gives_one_nonterminal_trace table environment raw state next
      submitted nonterminal
  exact ⟨next, trace, supported, rfl, rfl, rfl, rfl, rfl⟩

/-- The folded-C2 salt is queried from the same fixed context, does not advance
the duplex digest, and is saved only for the immediately following live C2
absorb. -/
theorem c2_root_salt_run_gives_future_free_step
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (before withSalt : EvalState) (salt : Digest256)
    (lambda chi : Qm31Bytes)
    (atRequest : state.current.control = .adaptive
      (.requestC2Salt lambda chi (raw.c2Commitment lambda chi)))
    (bindings : state.current.bindings = FixedBindings.ofContext raw.context)
    (same : SameDigest state.current.core before)
    (run : rootSaltStep table before raw.context c2TreeTag =
      some (salt, withSalt)) :
    ∃ pairs next,
      NonterminalRawDriverTrace environment raw state 1 pairs next ∧
      PathUsesFixedTable table pairs ∧
      next.current.control = .adaptive
        (.absorbC2 lambda chi (raw.c2Commitment lambda chi)) ∧
      next.current.core =
        { state.current.core with c2Salt := some salt } ∧
      SameDigest next.current.core withSalt ∧
      next.current.q16Candidates = state.current.q16Candidates := by
  obtain ⟨lookup, _calls, digest⟩ := query_step_appends_one table before
    withSalt (.publicRootSalt raw.context c2TreeTag) salt run
  have normalized : tableLookup table
      (rootSaltInput raw.context c2TreeTag) = some salt := by
    simpa only [RawQueryRole.input] using lookup
  have derived : deriveReply table state.current.bindings state.current.core
      (.requestRootSalt .foldedC2) = some (.single salt) := by
    rw [bindings]
    simp only [deriveReply, actionInputs, lookupSingleInput,
      fixed_bindings_recover_context, AuthenticatedTree.tag]
    rw [normalized]
    rfl
  let nextCore : RuntimeCore :=
    { state.current.core with c2Salt := some salt }
  have applied : applyActionWorkErased state.current.core
      (.requestRootSalt .foldedC2) (.single salt) = some nextCore := by
    rfl
  let nextSnapshot : FutureFreeSnapshot :=
    { state.current with
      control := .adaptive
        (.absorbC2 lambda chi (raw.c2Commitment lambda chi))
      core := nextCore }
  let next := appendFutureFreeSnapshot state
    (.verifier (.requestRootSalt .foldedC2) (.single salt)) nextSnapshot
  have noSubmission : submitNextRawMessage raw state = none := by
    simp [submitNextRawMessage, atRequest]
  have forced : state.current.control.nextVerifierAction? =
      some (.requestRootSalt .foldedC2) := by
    rw [atRequest]
    rfl
  have advanced : advanceFutureFreeVerifier environment state (.single salt) =
      some next := by
    have updated : afterFutureFreeVerifierReply environment state.current
        (.single salt) nextCore = some nextSnapshot := by
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        atRequest, OpenAdaptiveControl.afterVerifierReply, nextSnapshot]
    simpa [next] using
      advance_future_free_verifier_of_components environment state
        (.requestRootSalt .foldedC2) (.single salt) nextCore nextSnapshot
        forced applied updated
  have nonterminal : isDriverHalt next.current.control = false := by rfl
  obtain ⟨pairs, trace, supported⟩ :=
    fixed_table_action_gives_one_nonterminal_trace table environment raw state
      next (.requestRootSalt .foldedC2) (.single salt) noSubmission forced
      derived advanced nonterminal
  refine ⟨pairs, next, trace, supported, rfl, rfl, ?_, rfl⟩
  change state.current.core.digest = withSalt.digest
  have unchanged : withSalt.digest = before.digest := by
    simpa only [RawQueryRole.nextDigest] using digest
  exact same.trans unchanged.symm

/-- The folded-C2 absorb uses the salt saved at the live lambda/chi pair and
then enters the complete future-free linear schedule. -/
theorem c2_absorb_run_gives_future_free_step
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (before after : EvalState) (salt : Digest256)
    (lambda chi : Qm31Bytes)
    (atAbsorb : state.current.control = .adaptive
      (.absorbC2 lambda chi (raw.c2Commitment lambda chi)))
    (saved : state.current.core.c2Salt = some salt)
    (same : SameDigest state.current.core before)
    (run : absorbStep table before
      (.c2Root (raw.c2Commitment lambda chi).root salt) = some after) :
    ∃ pairs next,
      NonterminalRawDriverTrace environment raw state 1 pairs next ∧
      PathUsesFixedTable table pairs ∧
      next.current.control = .linear fullFutureFreeSlots ∧
      next.current.core =
        { state.current.core with digest := after.digest } ∧
      SameDigest next.current.core after ∧
      next.current.q16Candidates = state.current.q16Candidates := by
  rw [absorbStep] at run
  obtain ⟨queryResult, queryRun, result⟩ := Option.bind_eq_some_iff.mp run
  rcases queryResult with ⟨output, stepped⟩
  have steppedEq : stepped = after := by
    simpa only [pure, Option.some.injEq] using result
  subst stepped
  obtain ⟨lookup, _calls, digest⟩ := query_step_appends_one table before
    after (.absorb (.c2Root (raw.c2Commitment lambda chi).root salt)) output
      queryRun
  have outputEq : output = after.digest := by
    simpa only [RawQueryRole.nextDigest] using digest.symm
  subst output
  have normalized : tableLookup table
      (bytes before.digest ++ [domAbsorb, c2RootLabel] ++
        (Payload.c2Root (raw.c2Commitment lambda chi).root salt).data) =
      some after.digest := by
    simpa only [RawQueryRole.input, Payload.label] using lookup
  have derived : deriveReply table state.current.bindings state.current.core
      (.absorbC2 lambda chi (raw.c2Commitment lambda chi)) =
        some (.single after.digest) := by
    simp only [deriveReply, actionInputs, saved, lookupSingleInput]
    change state.current.core.digest = before.digest at same
    rw [same, normalized]
    rfl
  let nextCore : RuntimeCore :=
    { state.current.core with digest := after.digest }
  have applied : applyActionWorkErased state.current.core
      (.absorbC2 lambda chi (raw.c2Commitment lambda chi))
      (.single after.digest) = some nextCore := by
    simp [applyActionWorkErased, saved, nextCore]
  let nextSnapshot : FutureFreeSnapshot :=
    { state.current with
      control := .linear fullFutureFreeSlots
      core := nextCore }
  let next := appendFutureFreeSnapshot state
    (.verifier (.absorbC2 lambda chi (raw.c2Commitment lambda chi))
      (.single after.digest)) nextSnapshot
  have noSubmission : submitNextRawMessage raw state = none := by
    simp [submitNextRawMessage, atAbsorb]
  have forced : state.current.control.nextVerifierAction? =
      some (.absorbC2 lambda chi (raw.c2Commitment lambda chi)) := by
    rw [atAbsorb]
    rfl
  have advanced : advanceFutureFreeVerifier environment state
      (.single after.digest) = some next := by
    have updated : afterFutureFreeVerifierReply environment state.current
        (.single after.digest) nextCore = some nextSnapshot := by
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        atAbsorb, OpenAdaptiveControl.afterVerifierReply, nextSnapshot]
    simpa [next] using
      advance_future_free_verifier_of_components environment state
        (.absorbC2 lambda chi (raw.c2Commitment lambda chi))
        (.single after.digest) nextCore nextSnapshot forced applied updated
  have nonterminal : isDriverHalt next.current.control = false := by rfl
  obtain ⟨pairs, trace, supported⟩ :=
    fixed_table_action_gives_one_nonterminal_trace table environment raw state
      next (.absorbC2 lambda chi (raw.c2Commitment lambda chi))
      (.single after.digest) noSubmission forced derived advanced nonterminal
  exact ⟨pairs, next, trace, supported, rfl, rfl, rfl, rfl⟩

/-- The complete adaptive C2 message/salt/absorb round uses the commitment
indexed by the just-decoded lambda and chi and ends at the first linear slot. -/
theorem c2_round_run_gives_future_free_trace
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (before withSalt after : EvalState) (salt : Digest256)
    (lambda chi : Qm31Bytes)
    (atC2 : state.current.control = .adaptive (.awaitingC2 lambda chi))
    (bindings : state.current.bindings = FixedBindings.ofContext raw.context)
    (same : SameDigest state.current.core before)
    (saltRun : rootSaltStep table before raw.context c2TreeTag =
      some (salt, withSalt))
    (absorbRun : absorbStep table withSalt
      (.c2Root (raw.c2Commitment lambda chi).root salt) = some after) :
    ∃ pairs final,
      NonterminalRawDriverTrace environment raw state 3 pairs final ∧
      PathUsesFixedTable table pairs ∧
      final.current.control = .linear fullFutureFreeSlots ∧
      SameDigest final.current.core after ∧
      final.current.q16Candidates = state.current.q16Candidates := by
  obtain ⟨submitted, submissionTrace, submissionSupported,
      submittedControl, _submittedRoot, submittedCore, submittedBindings,
      submittedCandidates⟩ :=
    awaiting_c2_submits_live_raw_commitment table environment raw state lambda
      chi atC2
  have submittedBinding : submitted.current.bindings =
      FixedBindings.ofContext raw.context := submittedBindings.trans bindings
  have submittedSame : SameDigest submitted.current.core before := by
    rw [submittedCore]
    exact same
  obtain ⟨saltPairs, salted, saltTrace, saltSupported, saltedControl,
      saltedCore, saltedSame, saltedCandidates⟩ :=
    c2_root_salt_run_gives_future_free_step table environment raw submitted
      before withSalt salt lambda chi submittedControl submittedBinding
      submittedSame saltRun
  have saltedSaved : salted.current.core.c2Salt = some salt := by
    rw [saltedCore]
  obtain ⟨absorbPairs, final, absorbTrace, absorbSupported, finalControl,
      _finalCore, finalSame, finalCandidates⟩ :=
    c2_absorb_run_gives_future_free_step table environment raw salted withSalt
      after salt lambda chi saltedControl saltedSaved saltedSame absorbRun
  have firstTwo : NonterminalRawDriverTrace environment raw state 2
      ([] ++ saltPairs) salted := by
    simpa using nonterminal_raw_driver_trace_append environment raw state
      submitted salted 1 1 [] saltPairs submissionTrace saltTrace
  have allThree : NonterminalRawDriverTrace environment raw state 3
      (([] ++ saltPairs) ++ absorbPairs) final := by
    simpa using nonterminal_raw_driver_trace_append environment raw state
      salted final 2 1 ([] ++ saltPairs) absorbPairs firstTwo absorbTrace
  refine ⟨([] ++ saltPairs) ++ absorbPairs, final, allThree, ?_,
    finalControl, finalSame, ?_⟩
  · exact path_uses_fixed_table_append table ([] ++ saltPairs) absorbPairs
      (path_uses_fixed_table_append table [] saltPairs submissionSupported
        saltSupported) absorbSupported
  · rw [finalCandidates, saltedCandidates, submittedCandidates]

/-- Composition of the complete adaptive segment.  The evaluator may carry a
completed proof record, but only the exact squeeze blocks and raw C1/C2 bytes
are consumed.  In particular the C2 commitment is rebuilt after both live
samplers have completed. -/
theorem adaptive_c1_through_c2_run_gives_future_free_trace
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (state : FutureFreeVerifierState)
    (beforeC1 withC1Salt afterC1 afterLambda afterPhaseChallenges
      withC2Salt afterC2 : EvalState)
    (c1Salt c2Salt : Digest256)
    (atC1 : state.current.control = .adaptive .awaitingC1)
    (fixed : FutureFreeBindingsFixed
      (FixedBindings.ofContext tape.messages.context) state)
    (same : SameDigest state.current.core beforeC1)
    (c1SaltRun : rootSaltStep table beforeC1 tape.messages.context c1TreeTag =
      some (c1Salt, withC1Salt))
    (c1AbsorbRun : absorbStep table withC1Salt
      (.c1Root tape.messages.c1Root c1Salt) = some afterC1)
    (lambdaRun : runMachineEventWorkErased table afterC1
      (challengeEvent tape.messages .lambda) = some afterLambda)
    (chiRun : runMachineEventWorkErased table afterLambda
      (challengeEvent tape.messages .chi) = some afterPhaseChallenges)
    (phaseDecoded : StateSamplesDecodeAs tape.messages afterPhaseChallenges)
    (c2SaltRun : rootSaltStep table afterPhaseChallenges tape.messages.context
      c2TreeTag = some (c2Salt, withC2Salt))
    (c2AbsorbRun : absorbStep table withC2Salt
      (.c2Root tape.messages.c2.root c2Salt) = some afterC2) :
    ∃ steps pairs final,
      NonterminalRawDriverTrace (fixedTapeFutureFreeEnvironment tape)
        (fixedTapeRawMessages tape) state steps pairs final ∧
      PathUsesFixedTable table pairs ∧
      final.current.control = .linear fullFutureFreeSlots ∧
      SameDigest final.current.core afterC2 ∧
      final.current.q16Candidates = state.current.q16Candidates ∧
      steps = 6 +
        (tape.messages.challengeUse .lambda).blocksUsed +
        (tape.messages.challengeUse .chi).blocksUsed := by
  let environment := fixedTapeFutureFreeEnvironment tape
  let raw := fixedTapeRawMessages tape
  obtain ⟨c1Pairs, afterC1State, c1Trace, c1Supported, c1Control,
      c1Same, c1Candidates⟩ :=
    c1_round_run_gives_future_free_trace table environment raw state beforeC1
      withC1Salt afterC1 c1Salt atC1 fixed.1 same
      (by simpa [raw] using c1SaltRun)
      (by
        change absorbStep table withC1Salt
          (.c1Root tape.messages.c1Root c1Salt) = some afterC1
        exact c1AbsorbRun)
  have afterC1Fixed : FutureFreeBindingsFixed
      (FixedBindings.ofContext tape.messages.context) afterC1State :=
    nonterminal_trace_preserves_fixed_bindings
      (FixedBindings.ofContext tape.messages.context) environment raw state
      afterC1State 3 c1Pairs fixed c1Trace
  have lambdaSamplesIncluded : SamplesIncluded afterLambda
      afterPhaseChallenges :=
    machine_event_work_erased_samples_included table afterLambda
      afterPhaseChallenges (challengeEvent tape.messages .chi) chiRun
  have lambdaDecoded : StateSamplesDecodeAs tape.messages afterLambda :=
    state_samples_decode_of_included tape.messages afterLambda
      afterPhaseChallenges lambdaSamplesIncluded phaseDecoded
  obtain ⟨lambdaBlocks, lambdaPairs, afterLambdaState, lambdaLength,
      lambdaTrace, lambdaSupported, lambdaControl, lambdaSame,
      lambdaCandidates⟩ :=
    early_challenge_event_run_gives_future_free_trace table environment
      tape.messages raw afterC1State afterC1 afterLambda
      .lambda c1Control c1Same (by rfl) lambdaRun lambdaDecoded
  have lambdaControl' : afterLambdaState.current.control =
      .adaptive (.sampleChi (tape.messages.challengeValue .lambda) []) := by
    change afterLambdaState.current.control =
      .adaptive (.sampleChi
        (tape.messages.challengeValue ChallengeId.lambda) []) at lambdaControl
    exact lambdaControl
  obtain ⟨chiBlocks, chiPairs, afterChiState, chiLength, chiTrace,
      chiSupported, chiControl, chiSame, chiCandidates⟩ :=
    early_challenge_event_run_gives_future_free_trace table environment
      tape.messages raw afterLambdaState afterLambda afterPhaseChallenges
      (.chiAfter (tape.messages.challengeValue .lambda)) lambdaControl'
      lambdaSame (by rfl) chiRun phaseDecoded
  have chiControl' : afterChiState.current.control = .adaptive
      (.awaitingC2 (tape.messages.challengeValue .lambda)
        (tape.messages.challengeValue .chi)) := by
    change afterChiState.current.control = .adaptive
      (.awaitingC2 (tape.messages.challengeValue ChallengeId.lambda)
        (tape.messages.challengeValue ChallengeId.chi)) at chiControl
    exact chiControl
  have afterLambdaFixed : FutureFreeBindingsFixed
      (FixedBindings.ofContext tape.messages.context) afterLambdaState :=
    nonterminal_trace_preserves_fixed_bindings
      (FixedBindings.ofContext tape.messages.context) environment raw
      afterC1State afterLambdaState lambdaBlocks.length lambdaPairs
      afterC1Fixed lambdaTrace
  have afterChiFixed : FutureFreeBindingsFixed
      (FixedBindings.ofContext tape.messages.context) afterChiState :=
    nonterminal_trace_preserves_fixed_bindings
      (FixedBindings.ofContext tape.messages.context) environment raw
      afterLambdaState afterChiState chiBlocks.length chiPairs
      afterLambdaFixed chiTrace
  obtain ⟨c2Pairs, final, c2Trace, c2Supported, finalControl,
      finalSame, finalCandidates⟩ :=
    c2_round_run_gives_future_free_trace table environment raw afterChiState
      afterPhaseChallenges withC2Salt afterC2 c2Salt
      (tape.messages.challengeValue .lambda)
      (tape.messages.challengeValue .chi) chiControl' afterChiFixed.1 chiSame
      (by simpa [raw] using c2SaltRun)
      (by
        change absorbStep table withC2Salt
          (.c2Root tape.messages.c2.root c2Salt) = some afterC2
        exact c2AbsorbRun)
  have c1Lambda := nonterminal_raw_driver_trace_append environment raw state
    afterC1State afterLambdaState 3 lambdaBlocks.length c1Pairs lambdaPairs
    c1Trace lambdaTrace
  have throughChi := nonterminal_raw_driver_trace_append environment raw state
    afterLambdaState afterChiState (3 + lambdaBlocks.length) chiBlocks.length
    (c1Pairs ++ lambdaPairs) chiPairs c1Lambda chiTrace
  have allTrace := nonterminal_raw_driver_trace_append environment raw state
    afterChiState final
    ((3 + lambdaBlocks.length) + chiBlocks.length) 3
    ((c1Pairs ++ lambdaPairs) ++ chiPairs) c2Pairs throughChi c2Trace
  refine ⟨((3 + lambdaBlocks.length) + chiBlocks.length) + 3,
    ((c1Pairs ++ lambdaPairs) ++ chiPairs) ++ c2Pairs, final, allTrace,
    ?_, finalControl, finalSame, ?_, ?_⟩
  · exact path_uses_fixed_table_append table
      ((c1Pairs ++ lambdaPairs) ++ chiPairs) c2Pairs
      (path_uses_fixed_table_append table (c1Pairs ++ lambdaPairs) chiPairs
        (path_uses_fixed_table_append table c1Pairs lambdaPairs c1Supported
          lambdaSupported) chiSupported) c2Supported
  · exact finalCandidates.trans
      (chiCandidates.trans (lambdaCandidates.trans c1Candidates))
  · change lambdaBlocks.length =
        (tape.messages.challengeUse ChallengeId.lambda).blocksUsed at lambdaLength
    change chiBlocks.length =
        (tape.messages.challengeUse ChallengeId.chi).blocksUsed at chiLength
    rw [lambdaLength, chiLength]
    omega

/-! ## Reusable linear-slot microsteps -/

/-- One fixed action at the head of the linear schedule is forced by the
future-free controller.  The fixed-table runner supplies its actual reply and
successor core; no action or reply is chosen by this theorem. -/
theorem linear_fixed_action_run_gives_future_free_step
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (action : VerifierAction) (remaining : List FutureFreeSlot)
    (bindings : FixedBindings) (core nextCore : RuntimeCore)
    (atControl : state.current.control =
      .linear (.fixed action :: remaining))
    (stateBindings : state.current.bindings = bindings)
    (stateCore : state.current.core = core)
    (run : runActionCore table bindings core action = some nextCore)
    (remainingNonempty : remaining ≠ []) :
    ∃ pairs next,
      NonterminalRawDriverTrace environment raw state 1 pairs next ∧
      PathUsesFixedTable table pairs ∧
      next.current.control = .linear remaining ∧
      next.current.core = nextCore ∧
      next.current.q16Candidates = state.current.q16Candidates := by
  rw [runActionCore] at run
  obtain ⟨reply, derived, applied⟩ := Option.bind_eq_some_iff.mp run
  have noSubmission : submitNextRawMessage raw state = none := by
    simp [submitNextRawMessage, atControl]
  have forced : state.current.control.nextVerifierAction? = some action := by
    rw [atControl]
    rfl
  have derivedState : deriveReply table state.current.bindings
      state.current.core action = some reply := by
    simpa [stateBindings, stateCore] using derived
  have appliedState : applyActionWorkErased state.current.core action reply =
      some nextCore := by
    simpa [stateCore] using applied
  let nextSnapshot : FutureFreeSnapshot :=
    { state.current with control := .linear remaining, core := nextCore }
  let next := appendFutureFreeSnapshot state (.verifier action reply)
    nextSnapshot
  have advanced : advanceFutureFreeVerifier environment state reply =
      some next := by
    have updated : afterFutureFreeVerifierReply environment state.current reply
        nextCore = some nextSnapshot := by
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        atControl, linearOrDone, remainingNonempty, nextSnapshot]
    simpa [next] using
      advance_future_free_verifier_of_components environment state action reply
        nextCore nextSnapshot forced appliedState updated
  have nonterminal : isDriverHalt next.current.control = false := by rfl
  obtain ⟨pairs, trace, supported⟩ :=
    fixed_table_action_gives_one_nonterminal_trace table environment raw state
      next action reply noSubmission forced derivedState advanced nonterminal
  exact ⟨pairs, next, trace, supported, rfl, rfl, rfl⟩

/-- A raw prover payload is submitted first and then absorbed by exactly one
fixed-table query.  The site predicate is evaluated by the controller, so a
payload cannot be moved to a different semantic/OOD/relation slot. -/
theorem linear_payload_run_gives_future_free_trace
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (before after : EvalState) (site : FutureFreePayloadSite)
    (remaining : List FutureFreeSlot)
    (atControl : state.current.control =
      .linear (.payload site :: remaining))
    (same : SameDigest state.current.core before)
    (run : absorbStep table before (rawPayloadAt raw site) = some after)
    (remainingNonempty : remaining ≠ []) :
    ∃ pairs final,
      NonterminalRawDriverTrace environment raw state 2 pairs final ∧
      PathUsesFixedTable table pairs ∧
      final.current.control = .linear remaining ∧
      SameDigest final.current.core after ∧
      final.current.q16Candidates = state.current.q16Candidates := by
  let payload := rawPayloadAt raw site
  let submittedSnapshot : FutureFreeSnapshot :=
    { state.current with
      control := .absorbPayload payload remaining
      receivedPayloads := state.current.receivedPayloads ++ [payload] }
  let submitted := appendFutureFreeSnapshot state (.proverPayload payload)
    submittedSnapshot
  have rawSubmitted : submitNextRawMessage raw state = some submitted := by
    unfold submitNextRawMessage
    split <;> simp_all [submitFutureFreePayload, payload, submitted,
      submittedSnapshot, raw_payload_matches_its_exact_site]
  have submittedNonterminal : isDriverHalt submitted.current.control = false := by
    rfl
  obtain ⟨submissionTrace, submissionSupported⟩ :=
    raw_submission_gives_one_nonterminal_trace table environment raw state
      submitted rawSubmitted submittedNonterminal
  rw [absorbStep] at run
  obtain ⟨queryPair, queryRun, result⟩ := Option.bind_eq_some_iff.mp run
  rcases queryPair with ⟨output, stepped⟩
  have steppedEq : stepped = after := by
    simpa only [pure, Option.some.injEq] using result
  subst stepped
  obtain ⟨lookup, _calls, digest⟩ := query_step_appends_one table before
    after (.absorb payload) output queryRun
  have outputEq : output = after.digest := by
    simpa only [RawQueryRole.nextDigest] using digest.symm
  subst output
  have normalized : tableLookup table
      (bytes before.digest ++ [domAbsorb, payload.label] ++ payload.data) =
        some after.digest := by
    simpa only [RawQueryRole.input] using lookup
  have submittedSame : SameDigest submitted.current.core before := by
    change state.current.core.digest = before.digest
    exact same
  have derived : deriveReply table submitted.current.bindings
      submitted.current.core (.absorb payload) = some (.single after.digest) := by
    simp only [deriveReply, actionInputs, lookupSingleInput]
    change submitted.current.core.digest = before.digest at submittedSame
    rw [submittedSame, normalized]
    rfl
  let nextCore : RuntimeCore :=
    { submitted.current.core with digest := after.digest }
  have applied : applyActionWorkErased submitted.current.core (.absorb payload)
      (.single after.digest) = some nextCore := by
    rfl
  let finalSnapshot : FutureFreeSnapshot :=
    { submitted.current with control := .linear remaining, core := nextCore }
  let final := appendFutureFreeSnapshot submitted
    (.verifier (.absorb payload) (.single after.digest)) finalSnapshot
  have noSubmission : submitNextRawMessage raw submitted = none := by
    simp [submitNextRawMessage, submitted, submittedSnapshot,
      appendFutureFreeSnapshot]
  have forced : submitted.current.control.nextVerifierAction? =
      some (.absorb payload) := by rfl
  have advanced : advanceFutureFreeVerifier environment submitted
      (.single after.digest) = some final := by
    have updated : afterFutureFreeVerifierReply environment submitted.current
        (.single after.digest) nextCore = some finalSnapshot := by
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        submitted, submittedSnapshot, appendFutureFreeSnapshot, linearOrDone,
        finalSnapshot]
    simpa [final] using
      advance_future_free_verifier_of_components environment submitted
        (.absorb payload) (.single after.digest) nextCore finalSnapshot forced
        applied updated
  have finalNonterminal : isDriverHalt final.current.control = false := by rfl
  obtain ⟨absorbPairs, absorbTrace, absorbSupported⟩ :=
    fixed_table_action_gives_one_nonterminal_trace table environment raw
      submitted final (.absorb payload) (.single after.digest) noSubmission
      forced derived advanced finalNonterminal
  have trace := nonterminal_raw_driver_trace_append environment raw state
    submitted final 1 1 [] absorbPairs submissionTrace absorbTrace
  refine ⟨[] ++ absorbPairs, final, by simpa using trace, ?_, rfl, ?_, rfl⟩
  · exact path_uses_fixed_table_append table [] absorbPairs
      submissionSupported absorbSupported
  · rfl

/-- The evaluator may first replay any number of adversary-history work
probes.  Because such probes do not advance the duplex, its final selected
probe is exactly the one verifier-visible query at the live work checkpoint. -/
theorem selected_work_choice_run_gives_future_free_step
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (before after : EvalState) (stage : WorkStage)
    (choice : GrindingChoice stage) (remaining : List FutureFreeSlot)
    (atControl : state.current.control =
      .workCheck stage choice.selected remaining)
    (same : SameDigest state.current.core before)
    (run : runGrindingChoiceWorkErased table before stage choice = some after) :
    ∃ pairs next,
      NonterminalRawDriverTrace environment raw state 1 pairs next ∧
      PathUsesFixedTable table pairs ∧
      next.current.control = .workCheckpoint stage choice.selected remaining ∧
      next.current.core = state.current.core ∧
      SameDigest next.current.core after ∧
      next.current.q16Candidates = state.current.q16Candidates := by
  rw [runGrindingChoiceWorkErased] at run
  obtain ⟨queried, probesRun, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨selectedPair, selectedRun, result⟩ :=
    Option.bind_eq_some_iff.mp run
  rcases selectedPair with ⟨selectedOutput, afterSelected⟩
  have afterEq : afterSelected = after := by
    simpa only [pure, Option.some.injEq] using result
  subst afterSelected
  have probesDigest := grinding_probes_do_not_advance table stage
    choice.probesBeforeSelected before queried probesRun
  obtain ⟨lookup, _calls, selectedDigest⟩ := query_step_appends_one table
    queried after (.grind stage choice.selected) selectedOutput selectedRun
  have afterDigest : after.digest = before.digest := by
    have selectedUnchanged : after.digest = queried.digest := by
      simpa only [RawQueryRole.nextDigest] using selectedDigest
    exact selectedUnchanged.trans probesDigest
  have normalized : tableLookup table
      (bytes before.digest ++ [domGrind] ++ bytes choice.selected) =
        some selectedOutput := by
    have inputLookup : tableLookup table
        (bytes queried.digest ++ [domGrind] ++ bytes choice.selected) =
          some selectedOutput := by
      simpa only [RawQueryRole.input] using lookup
    rw [probesDigest] at inputLookup
    exact inputLookup
  have derived : deriveReply table state.current.bindings state.current.core
      (.workProbe stage choice.selected .verifierSelected) =
        some (.single selectedOutput) := by
    simp only [deriveReply, actionInputs, lookupSingleInput]
    change state.current.core.digest = before.digest at same
    rw [same, normalized]
    rfl
  have applied : applyActionWorkErased state.current.core
      (.workProbe stage choice.selected .verifierSelected)
      (.single selectedOutput) = some state.current.core := by
    rfl
  let nextSnapshot : FutureFreeSnapshot :=
    { state.current with
      control := .workCheckpoint stage choice.selected remaining
      checkedWorkNonces := state.current.checkedWorkNonces ++
        [{ stage := stage, nonce := choice.selected }] }
  let next := appendFutureFreeSnapshot state
    (.verifier (.workProbe stage choice.selected .verifierSelected)
      (.single selectedOutput)) nextSnapshot
  have noSubmission : submitNextRawMessage raw state = none := by
    simp [submitNextRawMessage, atControl]
  have forced : state.current.control.nextVerifierAction? =
      some (.workProbe stage choice.selected .verifierSelected) := by
    rw [atControl]
    rfl
  have advanced : advanceFutureFreeVerifier environment state
      (.single selectedOutput) = some next := by
    have updated : afterFutureFreeVerifierReply environment state.current
        (.single selectedOutput) state.current.core = some nextSnapshot := by
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        atControl, nextSnapshot]
    simpa [next] using
      advance_future_free_verifier_of_components environment state
        (.workProbe stage choice.selected .verifierSelected)
        (.single selectedOutput) state.current.core nextSnapshot forced applied
        updated
  have nonterminal : isDriverHalt next.current.control = false := by rfl
  obtain ⟨pairs, trace, supported⟩ :=
    fixed_table_action_gives_one_nonterminal_trace table environment raw state
      next (.workProbe stage choice.selected .verifierSelected)
      (.single selectedOutput) noSubmission forced derived advanced nonterminal
  refine ⟨pairs, next, trace, supported, rfl, rfl, ?_, rfl⟩
  change state.current.core.digest = after.digest
  change state.current.core.digest = before.digest at same
  exact same.trans afterDigest.symm

/-- The checkpoint following a selected work query is a structural no-query
transition.  It remains distinct for batch, fold and final work. -/
theorem work_checkpoint_gives_future_free_step
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (stage : WorkStage) (nonce : NonceBytes)
    (remaining : List FutureFreeSlot)
    (atControl : state.current.control =
      .workCheckpoint stage nonce remaining) :
    ∃ pairs next,
      NonterminalRawDriverTrace environment raw state 1 pairs next ∧
      PathUsesFixedTable table pairs ∧
      next.current.control = .workAbsorb stage nonce remaining ∧
      next.current.core = state.current.core ∧
      next.current.q16Candidates = state.current.q16Candidates := by
  let action := VerifierAction.checkpoint (checkpointOfWorkStage stage)
  have noSubmission : submitNextRawMessage raw state = none := by
    simp [submitNextRawMessage, atControl]
  have forced : state.current.control.nextVerifierAction? = some action := by
    rw [atControl]
    rfl
  have derived : deriveReply table state.current.bindings state.current.core
      action = some .none := by rfl
  have applied : applyActionWorkErased state.current.core action .none =
      some state.current.core := by rfl
  let nextSnapshot : FutureFreeSnapshot :=
    { state.current with control := .workAbsorb stage nonce remaining }
  let next := appendFutureFreeSnapshot state (.verifier action .none)
    nextSnapshot
  have advanced : advanceFutureFreeVerifier environment state .none =
      some next := by
    have updated : afterFutureFreeVerifierReply environment state.current .none
        state.current.core = some nextSnapshot := by
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        atControl, nextSnapshot]
    simpa [next] using
      advance_future_free_verifier_of_components environment state action .none
        state.current.core nextSnapshot forced applied updated
  have nonterminal : isDriverHalt next.current.control = false := by rfl
  obtain ⟨pairs, trace, supported⟩ :=
    fixed_table_action_gives_one_nonterminal_trace table environment raw state
      next action .none noSubmission forced derived advanced nonterminal
  exact ⟨pairs, next, trace, supported, rfl, rfl, rfl⟩

/-- Absorbing the selected work nonce is the only duplex update associated
with that stage after its verifier query and checkpoint. -/
theorem work_nonce_absorb_run_gives_future_free_step
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (before after : EvalState) (stage : WorkStage) (nonce : NonceBytes)
    (remaining : List FutureFreeSlot)
    (atControl : state.current.control = .workAbsorb stage nonce remaining)
    (same : SameDigest state.current.core before)
    (run : absorbStep table before (workNoncePayload stage nonce) = some after)
    (remainingNonempty : remaining ≠ []) :
    ∃ pairs next,
      NonterminalRawDriverTrace environment raw state 1 pairs next ∧
      PathUsesFixedTable table pairs ∧
      next.current.control = .linear remaining ∧
      SameDigest next.current.core after ∧
      next.current.q16Candidates = state.current.q16Candidates := by
  let payload := workNoncePayload stage nonce
  rw [absorbStep] at run
  obtain ⟨queryPair, queryRun, result⟩ := Option.bind_eq_some_iff.mp run
  rcases queryPair with ⟨output, stepped⟩
  have steppedEq : stepped = after := by
    simpa only [pure, Option.some.injEq] using result
  subst stepped
  obtain ⟨lookup, _calls, digest⟩ := query_step_appends_one table before
    after (.absorb payload) output queryRun
  have outputEq : output = after.digest := by
    simpa only [RawQueryRole.nextDigest] using digest.symm
  subst output
  have normalized : tableLookup table
      (bytes before.digest ++ [domAbsorb, payload.label] ++ payload.data) =
        some after.digest := by
    simpa only [RawQueryRole.input] using lookup
  have derived : deriveReply table state.current.bindings state.current.core
      (.absorb payload) = some (.single after.digest) := by
    simp only [deriveReply, actionInputs, lookupSingleInput]
    change state.current.core.digest = before.digest at same
    rw [same, normalized]
    rfl
  let nextCore : RuntimeCore :=
    { state.current.core with digest := after.digest }
  have applied : applyActionWorkErased state.current.core (.absorb payload)
      (.single after.digest) = some nextCore := by rfl
  let nextSnapshot : FutureFreeSnapshot :=
    { state.current with control := .linear remaining, core := nextCore }
  let next := appendFutureFreeSnapshot state
    (.verifier (.absorb payload) (.single after.digest)) nextSnapshot
  have noSubmission : submitNextRawMessage raw state = none := by
    simp [submitNextRawMessage, atControl]
  have forced : state.current.control.nextVerifierAction? =
      some (.absorb payload) := by
    rw [atControl]
    rfl
  have advanced : advanceFutureFreeVerifier environment state
      (.single after.digest) = some next := by
    have updated : afterFutureFreeVerifierReply environment state.current
        (.single after.digest) nextCore = some nextSnapshot := by
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        atControl, linearOrDone, remainingNonempty, nextSnapshot]
    simpa [next] using
      advance_future_free_verifier_of_components environment state
        (.absorb payload) (.single after.digest) nextCore nextSnapshot forced
        applied updated
  have nonterminal : isDriverHalt next.current.control = false := by rfl
  obtain ⟨pairs, trace, supported⟩ :=
    fixed_table_action_gives_one_nonterminal_trace table environment raw state
      next (.absorb payload) (.single after.digest) noSubmission forced derived
      advanced nonterminal
  exact ⟨pairs, next, trace, supported, rfl, rfl, rfl⟩

/-- One work slot consists of exactly four verifier-machine microsteps: raw
nonce submission, the one verifier-visible selected query, its stage-specific
checkpoint, and the nonce absorb.  Exploratory probes occur only in the
evaluator evidence used to locate the selected query. -/
theorem linear_work_slot_run_gives_future_free_trace
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (before afterGrind afterAbsorb : EvalState) (stage : WorkStage)
    (choice : GrindingChoice stage) (remaining : List FutureFreeSlot)
    (atControl : state.current.control = .linear (.work stage :: remaining))
    (same : SameDigest state.current.core before)
    (selectedIsRaw : choice.selected = rawWorkNonceAt raw stage)
    (grindRun : runGrindingChoiceWorkErased table before stage choice =
      some afterGrind)
    (absorbRun : absorbStep table afterGrind
      (workNoncePayload stage choice.selected) = some afterAbsorb)
    (remainingNonempty : remaining ≠ []) :
    ∃ pairs final,
      NonterminalRawDriverTrace environment raw state 4 pairs final ∧
      PathUsesFixedTable table pairs ∧
      final.current.control = .linear remaining ∧
      SameDigest final.current.core afterAbsorb ∧
      final.current.q16Candidates = state.current.q16Candidates := by
  let nonce := rawWorkNonceAt raw stage
  let submittedSnapshot : FutureFreeSnapshot :=
    { state.current with control := .workCheck stage nonce remaining }
  let submitted := appendFutureFreeSnapshot state
    (.proverWorkNonce stage nonce) submittedSnapshot
  have rawSubmitted : submitNextRawMessage raw state = some submitted := by
    unfold submitNextRawMessage
    split <;> simp_all [submitFutureFreeWorkNonce, nonce, submitted,
      submittedSnapshot]
  have submittedNonterminal : isDriverHalt submitted.current.control = false := by
    rfl
  obtain ⟨submissionTrace, submissionSupported⟩ :=
    raw_submission_gives_one_nonterminal_trace table environment raw state
      submitted rawSubmitted submittedNonterminal
  have submittedControl : submitted.current.control =
      .workCheck stage choice.selected remaining := by
    change FutureFreeControl.workCheck stage nonce remaining =
      .workCheck stage choice.selected remaining
    rw [selectedIsRaw]
  have submittedSame : SameDigest submitted.current.core before := by
    change state.current.core.digest = before.digest
    exact same
  obtain ⟨workPairs, checked, workTrace, workSupported, checkedControl,
      _checkedCore, checkedSame, checkedCandidates⟩ :=
    selected_work_choice_run_gives_future_free_step table environment raw
      submitted before afterGrind stage choice remaining submittedControl
      submittedSame grindRun
  obtain ⟨checkpointPairs, checkpointed, checkpointTrace,
      checkpointSupported, checkpointControl, checkpointCore,
      checkpointCandidates⟩ :=
    work_checkpoint_gives_future_free_step table environment raw checked stage
      choice.selected remaining checkedControl
  have checkpointSame : SameDigest checkpointed.current.core afterGrind := by
    rw [checkpointCore]
    exact checkedSame
  obtain ⟨absorbPairs, final, absorbTrace, absorbSupported, finalControl,
      finalSame, finalCandidates⟩ :=
    work_nonce_absorb_run_gives_future_free_step table environment raw
      checkpointed afterGrind afterAbsorb stage choice.selected remaining
      checkpointControl checkpointSame absorbRun remainingNonempty
  have firstTwo := nonterminal_raw_driver_trace_append environment raw state
    submitted checked 1 1 [] workPairs submissionTrace workTrace
  have firstThree := nonterminal_raw_driver_trace_append environment raw state
    checked checkpointed 2 1 ([] ++ workPairs) checkpointPairs firstTwo
    checkpointTrace
  have allFour := nonterminal_raw_driver_trace_append environment raw state
    checkpointed final 3 1 (([] ++ workPairs) ++ checkpointPairs) absorbPairs
    firstThree absorbTrace
  refine ⟨(([] ++ workPairs) ++ checkpointPairs) ++ absorbPairs, final,
    by simpa using allFour, ?_, finalControl, finalSame, ?_⟩
  · exact path_uses_fixed_table_append table
      (([] ++ workPairs) ++ checkpointPairs) absorbPairs
      (path_uses_fixed_table_append table ([] ++ workPairs) checkpointPairs
        (path_uses_fixed_table_append table [] workPairs submissionSupported
          workSupported) checkpointSupported) absorbSupported
  · exact finalCandidates.trans
      (checkpointCandidates.trans checkedCandidates)

/-! ## A single induction for every non-q16 linear region -/

def fixedTapeGrindingChoice (messages : Messages) :
    (stage : WorkStage) → GrindingChoice stage
  | .batch => messages.batchGrinding
  | .fold => messages.foldGrinding
  | .final => messages.finalGrinding

def fixedLinearActionEvent? : VerifierAction → Option MachineEvent
  | .absorb payload => some (.absorb payload)
  | .checkpoint checkpoint => some (.check checkpoint)
  | _ => none

def linearSlotSupported : FutureFreeSlot → Bool
  | .fixed action => (fixedLinearActionEvent? action).isSome
  | .challenge _ | .payload _ | .work _ => true
  | .beginQ16 => false

def fixedTapeLinearSlotEvents (tape : DeployedFixedTape) :
    FutureFreeSlot → List MachineEvent
  | .fixed action => (fixedLinearActionEvent? action).toList
  | .challenge id => [challengeEvent tape.messages id]
  | .payload site =>
      [.absorb (rawPayloadAt (fixedTapeRawMessages tape) site)]
  | .work stage =>
      let choice := fixedTapeGrindingChoice tape.messages stage
      [.grind stage choice,
       .check (checkpointOfWorkStage stage),
       .absorb (workNoncePayload stage choice.selected)]
  | .beginQ16 => []

def fixedTapeLinearEvents (tape : DeployedFixedTape)
    (slots : List FutureFreeSlot) : List MachineEvent :=
  slots.flatMap (fixedTapeLinearSlotEvents tape)

def fixedTapeLinearFuel (tape : DeployedFixedTape) :
    FutureFreeSlot → Nat
  | .fixed _ => 1
  | .challenge id => (tape.messages.challengeUse id).blocksUsed
  | .payload _ => 2
  | .work _ => 4
  | .beginQ16 => 0

def fixedTapeLinearFuels (tape : DeployedFixedTape)
    (slots : List FutureFreeSlot) : Nat :=
  (slots.map (fixedTapeLinearFuel tape)).sum

theorem run_machine_events_work_erased_append_iff
    (table : FixedOracleTable) (first second : List MachineEvent)
    (state final : EvalState) :
    runMachineEventsWorkErased table (first ++ second) state = some final ↔
      ∃ middle,
        runMachineEventsWorkErased table first state = some middle ∧
        runMachineEventsWorkErased table second middle = some final := by
  induction first generalizing state with
  | nil => simp [runMachineEventsWorkErased]
  | cons event rest ih =>
      simp only [List.cons_append, runMachineEventsWorkErased]
      constructor
      · intro run
        obtain ⟨next, eventRun, tailRun⟩ := Option.bind_eq_some_iff.mp run
        obtain ⟨middle, restRun, secondRun⟩ :=
          (ih (state := next)).mp tailRun
        refine ⟨middle, ?_, secondRun⟩
        exact Option.bind_eq_some_iff.mpr ⟨next, eventRun, restRun⟩
      · rintro ⟨middle, firstRun, secondRun⟩
        obtain ⟨next, eventRun, restRun⟩ :=
          Option.bind_eq_some_iff.mp firstRun
        exact Option.bind_eq_some_iff.mpr
          ⟨next, eventRun, (ih (state := next)).mpr
            ⟨middle, restRun, secondRun⟩⟩

theorem fixed_tape_linear_events_cons
    (tape : DeployedFixedTape) (slot : FutureFreeSlot)
    (rest : List FutureFreeSlot) :
    fixedTapeLinearEvents tape (slot :: rest) =
      fixedTapeLinearSlotEvents tape slot ++ fixedTapeLinearEvents tape rest := by
  rfl

theorem fixed_tape_linear_fuels_cons
    (tape : DeployedFixedTape) (slot : FutureFreeSlot)
    (rest : List FutureFreeSlot) :
    fixedTapeLinearFuels tape (slot :: rest) =
      fixedTapeLinearFuel tape slot + fixedTapeLinearFuels tape rest := by
  simp [fixedTapeLinearFuels]

def EveryLinearSlotSupported : List FutureFreeSlot → Prop
  | [] => True
  | slot :: rest =>
      linearSlotSupported slot = true ∧ EveryLinearSlotSupported rest

theorem supported_fixed_action_classification
    (action : VerifierAction)
    (supported : linearSlotSupported (.fixed action) = true) :
    (∃ payload, action = .absorb payload) ∨
      (∃ checkpoint, action = .checkpoint checkpoint) := by
  cases action <;>
    simp [linearSlotSupported, fixedLinearActionEvent?] at supported ⊢

def EveryChallengeSecure (environment : FutureFreeEnvironment)
    (messages : Messages) : Prop :=
  ∀ id, ChallengeSecureMapAccepted environment id
    (messages.challengeValue id)

theorem work_slot_event_run_exposes
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (stage : WorkStage) (before after : EvalState)
    (run : runMachineEventsWorkErased table
      (fixedTapeLinearSlotEvents tape (.work stage)) before = some after) :
    ∃ afterGrind,
      runGrindingChoiceWorkErased table before stage
          (fixedTapeGrindingChoice tape.messages stage) = some afterGrind ∧
      absorbStep table afterGrind
          (workNoncePayload stage
            (fixedTapeGrindingChoice tape.messages stage).selected) =
        some after := by
  simp only [fixedTapeLinearSlotEvents, runMachineEventsWorkErased] at run
  obtain ⟨afterGrind, grindRun, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨afterCheck, checkRun, run⟩ := Option.bind_eq_some_iff.mp run
  have checkEq : afterCheck = afterGrind := by
    simpa [runMachineEventWorkErased] using (Option.some.inj checkRun).symm
  subst afterCheck
  obtain ⟨afterAbsorb, absorbRun, finalRun⟩ :=
    Option.bind_eq_some_iff.mp run
  have finalEq : afterAbsorb = after := by
    simpa [runMachineEventsWorkErased] using Option.some.inj finalRun
  subst afterAbsorb
  exact ⟨afterGrind, grindRun, absorbRun⟩

/-- Every supported non-q16 slot in a fixed tape is replayed by the dynamic
controller.  The processed prefix is arbitrary and the untouched `tail`
remains future-free; this is what lets the same theorem cover both sides of
the q16 forest. -/
theorem fixed_tape_linear_region_gives_future_free_trace
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace)
    (wellFormed : TraceWellFormed table exactDeterministicDecoders tape rawTrace)
    (state : FutureFreeVerifierState) (before after : EvalState)
    (slots tail : List FutureFreeSlot)
    (atControl : state.current.control = .linear (slots ++ tail))
    (same : SameDigest state.current.core before)
    (run : runMachineEventsWorkErased table (fixedTapeLinearEvents tape slots)
      before = some after)
    (allDecoded : StateSamplesDecodeAs tape.messages after)
    (secureAll : EveryChallengeSecure (fixedTapeFutureFreeEnvironment tape)
      tape.messages)
    (supported : EveryLinearSlotSupported slots)
    (tailNonempty : tail ≠ []) :
    ∃ steps pairs final,
      NonterminalRawDriverTrace (fixedTapeFutureFreeEnvironment tape)
        (fixedTapeRawMessages tape) state steps pairs final ∧
      PathUsesFixedTable table pairs ∧
      final.current.control = .linear tail ∧
      SameDigest final.current.core after ∧
      final.current.q16Candidates = state.current.q16Candidates ∧
      steps = fixedTapeLinearFuels tape slots := by
  induction slots generalizing state before with
  | nil =>
      have stateEq : before = after := by
        simpa [fixedTapeLinearEvents, runMachineEventsWorkErased] using
          Option.some.inj run
      subst after
      refine ⟨0, [], state, .stop state, path_uses_fixed_table_nil table,
        ?_, same, rfl, rfl⟩
      simpa using atControl
  | cons slot rest ih =>
      rw [fixed_tape_linear_events_cons] at run
      obtain ⟨middle, headRun, restRun⟩ :=
        (run_machine_events_work_erased_append_iff table
          (fixedTapeLinearSlotEvents tape slot)
          (fixedTapeLinearEvents tape rest) before after).mp run
      have restIncluded : SamplesIncluded middle after :=
        machine_events_work_erased_samples_included table
          (fixedTapeLinearEvents tape rest) middle after restRun
      have middleDecoded : StateSamplesDecodeAs tape.messages middle :=
        state_samples_decode_of_included tape.messages middle after restIncluded
          allDecoded
      have headSupported : linearSlotSupported slot = true := supported.1
      have restSupported : EveryLinearSlotSupported rest := supported.2
      have remainingNonempty : rest ++ tail ≠ [] := by
        intro empty
        cases rest with
        | nil => exact tailNonempty (by simpa using empty)
        | cons head rest => simp at empty
      have headControl : state.current.control =
          .linear (slot :: (rest ++ tail)) := by
        simpa only [List.cons_append] using atControl
      cases slot with
      | fixed action =>
          rcases supported_fixed_action_classification action headSupported with
            ⟨payload, rfl⟩ | ⟨checkpoint, rfl⟩
          ·
              have eventRun : runMachineEventWorkErased table before
                  (.absorb payload) = some middle := by
                simpa [fixedTapeLinearSlotEvents, fixedLinearActionEvent?,
                  runMachineEventsWorkErased] using headRun
              obtain ⟨nextCore, actionsRun, nextSame, _c1, _c2, _q16⟩ :=
                machine_event_actions_agree table state.current.bindings
                  state.current.core before middle (.absorb payload) same
                  eventRun
              have actionRun : runActionCore table state.current.bindings
                  state.current.core (.absorb payload) = some nextCore := by
                simpa [eventActions, runActionCores] using actionsRun
              obtain ⟨headPairs, next, headTrace, headTable, nextControl,
                  nextCoreEq, nextCandidates⟩ :=
                linear_fixed_action_run_gives_future_free_step table
                  (fixedTapeFutureFreeEnvironment tape)
                  (fixedTapeRawMessages tape) state (.absorb payload)
                  (rest ++ tail) state.current.bindings state.current.core
                  nextCore headControl rfl rfl actionRun remainingNonempty
              have nextSame' : SameDigest next.current.core middle := by
                rw [nextCoreEq]
                exact nextSame
              obtain ⟨tailSteps, tailPairs, final, tailTrace, tailTable,
                  finalControl, finalSame, finalCandidates, tailFuel⟩ :=
                ih next middle nextControl nextSame' restRun restSupported
              refine ⟨1 + tailSteps, headPairs ++ tailPairs, final,
                nonterminal_raw_driver_trace_append
                  (fixedTapeFutureFreeEnvironment tape)
                  (fixedTapeRawMessages tape) state next final 1 tailSteps
                  headPairs tailPairs headTrace tailTrace,
                path_uses_fixed_table_append table headPairs tailPairs headTable
                  tailTable, finalControl, finalSame, ?_, ?_⟩
              · exact finalCandidates.trans nextCandidates
              · simp [fixedTapeLinearFuels, fixedTapeLinearFuel, tailFuel]
          ·
              have eventRun : runMachineEventWorkErased table before
                  (.check checkpoint) = some middle := by
                simpa [fixedTapeLinearSlotEvents, fixedLinearActionEvent?,
                  runMachineEventsWorkErased] using headRun
              obtain ⟨nextCore, actionsRun, nextSame, _c1, _c2, _q16⟩ :=
                machine_event_actions_agree table state.current.bindings
                  state.current.core before middle (.check checkpoint) same
                  eventRun
              have actionRun : runActionCore table state.current.bindings
                  state.current.core (.checkpoint checkpoint) =
                    some nextCore := by
                simpa [eventActions, runActionCores] using actionsRun
              obtain ⟨headPairs, next, headTrace, headTable, nextControl,
                  nextCoreEq, nextCandidates⟩ :=
                linear_fixed_action_run_gives_future_free_step table
                  (fixedTapeFutureFreeEnvironment tape)
                  (fixedTapeRawMessages tape) state (.checkpoint checkpoint)
                  (rest ++ tail) state.current.bindings state.current.core
                  nextCore headControl rfl rfl actionRun remainingNonempty
              have nextSame' : SameDigest next.current.core middle := by
                rw [nextCoreEq]
                exact nextSame
              obtain ⟨tailSteps, tailPairs, final, tailTrace, tailTable,
                  finalControl, finalSame, finalCandidates, tailFuel⟩ :=
                ih next middle nextControl nextSame' restRun restSupported
              refine ⟨1 + tailSteps, headPairs ++ tailPairs, final,
                nonterminal_raw_driver_trace_append
                  (fixedTapeFutureFreeEnvironment tape)
                  (fixedTapeRawMessages tape) state next final 1 tailSteps
                  headPairs tailPairs headTrace tailTrace,
                path_uses_fixed_table_append table headPairs tailPairs headTable
                  tailTable, finalControl, finalSame, ?_, ?_⟩
              · exact finalCandidates.trans nextCandidates
              · simp [fixedTapeLinearFuels, fixedTapeLinearFuel, tailFuel]
      | challenge id =>
          have eventRun : runMachineEventWorkErased table before
              (challengeEvent tape.messages id) = some middle := by
            simpa [fixedTapeLinearSlotEvents, runMachineEventsWorkErased] using
              headRun
          obtain ⟨blocks, headPairs, next, blocksLength, headTrace,
              headTable, nextControl, nextSame, nextCandidates⟩ :=
            linear_challenge_event_run_gives_future_free_trace table
              (fixedTapeFutureFreeEnvironment tape) tape.messages
              (fixedTapeRawMessages tape) state before middle id
              (rest ++ tail) headControl same (by rfl) eventRun middleDecoded
              (secureAll id) remainingNonempty
          obtain ⟨tailSteps, tailPairs, final, tailTrace, tailTable,
              finalControl, finalSame, finalCandidates, tailFuel⟩ :=
            ih next middle nextControl nextSame restRun restSupported
          refine ⟨blocks.length + tailSteps, headPairs ++ tailPairs, final,
            nonterminal_raw_driver_trace_append
              (fixedTapeFutureFreeEnvironment tape)
              (fixedTapeRawMessages tape) state next final blocks.length
              tailSteps headPairs tailPairs headTrace tailTrace,
            path_uses_fixed_table_append table headPairs tailPairs headTable
              tailTable, finalControl, finalSame, ?_, ?_⟩
          · exact finalCandidates.trans nextCandidates
          · simp [fixedTapeLinearFuels, fixedTapeLinearFuel, blocksLength,
              tailFuel]
      | payload site =>
          have eventRun : absorbStep table before
              (rawPayloadAt (fixedTapeRawMessages tape) site) = some middle := by
            simpa [fixedTapeLinearSlotEvents, runMachineEventsWorkErased,
              runMachineEventWorkErased] using headRun
          obtain ⟨headPairs, next, headTrace, headTable, nextControl,
              nextSame, nextCandidates⟩ :=
            linear_payload_run_gives_future_free_trace table
              (fixedTapeFutureFreeEnvironment tape)
              (fixedTapeRawMessages tape) state before middle site
              (rest ++ tail) headControl same eventRun remainingNonempty
          obtain ⟨tailSteps, tailPairs, final, tailTrace, tailTable,
              finalControl, finalSame, finalCandidates, tailFuel⟩ :=
            ih next middle nextControl nextSame restRun restSupported
          refine ⟨2 + tailSteps, headPairs ++ tailPairs, final,
            nonterminal_raw_driver_trace_append
              (fixedTapeFutureFreeEnvironment tape)
              (fixedTapeRawMessages tape) state next final 2 tailSteps
              headPairs tailPairs headTrace tailTrace,
            path_uses_fixed_table_append table headPairs tailPairs headTable
              tailTable, finalControl, finalSame, ?_, ?_⟩
          · exact finalCandidates.trans nextCandidates
          · simp [fixedTapeLinearFuels, fixedTapeLinearFuel, tailFuel]
      | work stage =>
          obtain ⟨afterGrind, grindRun, absorbRun⟩ :=
            work_slot_event_run_exposes table tape stage before middle headRun
          let choice := fixedTapeGrindingChoice tape.messages stage
          have selectedIsRaw : choice.selected =
              rawWorkNonceAt (fixedTapeRawMessages tape) stage := by
            cases stage <;> rfl
          obtain ⟨headPairs, next, headTrace, headTable, nextControl,
              nextSame, nextCandidates⟩ :=
            linear_work_slot_run_gives_future_free_trace table
              (fixedTapeFutureFreeEnvironment tape)
              (fixedTapeRawMessages tape) state before afterGrind middle stage
              choice (rest ++ tail) headControl same selectedIsRaw grindRun
              absorbRun remainingNonempty
          obtain ⟨tailSteps, tailPairs, final, tailTrace, tailTable,
              finalControl, finalSame, finalCandidates, tailFuel⟩ :=
            ih next middle nextControl nextSame restRun restSupported
          refine ⟨4 + tailSteps, headPairs ++ tailPairs, final,
            nonterminal_raw_driver_trace_append
              (fixedTapeFutureFreeEnvironment tape)
              (fixedTapeRawMessages tape) state next final 4 tailSteps
              headPairs tailPairs headTrace tailTrace,
            path_uses_fixed_table_append table headPairs tailPairs headTable
              tailTable, finalControl, finalSame, ?_, ?_⟩
          · exact finalCandidates.trans nextCandidates
          · simp [fixedTapeLinearFuels, fixedTapeLinearFuel, tailFuel]
      | beginQ16 =>
          simp [linearSlotSupported] at headSupported

theorem well_formed_trace_gives_every_challenge_secure
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace)
    (wellFormed : TraceWellFormed table exactDeterministicDecoders tape
      rawTrace) :
    EveryChallengeSecure (fixedTapeFutureFreeEnvironment tape)
      tape.messages := by
  intro id
  cases id <;> simp [EveryChallengeSecure, ChallengeSecureMapAccepted,
    fixedTapeFutureFreeEnvironment]
  case circlePoint sample =>
    exact ⟨tape.circlePoints sample,
      wellFormed.secureCirclePointsDecode sample⟩

def afterQ16PreterminalSlots : List FutureFreeSlot :=
  [.fixed (.checkpoint .frontierCount),
   .fixed (.absorb .queryBatchDomain),
   .challenge .queryBatch,
   .fixed (.checkpoint .twoTreeAuthentication),
   .payload .queryBatchClaim] ++
  relationTailSlots ++
  [.fixed (.checkpoint .relationTerminal)]

theorem after_q16_slots_split_terminal :
    afterQ16Slots = afterQ16PreterminalSlots ++ [.fixed .terminal] := by
  rfl

theorem before_q16_slots_are_supported :
    EveryLinearSlotSupported beforeQ16Slots := by
  simp [EveryLinearSlotSupported, beforeQ16Slots, zeroCheckSlots,
    semanticSlots, oodSlots, linearSlotSupported, fixedLinearActionEvent?]

theorem after_q16_preterminal_slots_are_supported :
    EveryLinearSlotSupported afterQ16PreterminalSlots := by
  simp [EveryLinearSlotSupported, afterQ16PreterminalSlots,
    relationTailSlots, linearSlotSupported, fixedLinearActionEvent?]

theorem fixed_tape_before_q16_events_are_exact_prefix_after_c2
    (tape : DeployedFixedTape) :
    fixedTapeLinearEvents tape beforeQ16Slots =
      prefixAfterC2 tape.messages := by
  simp [fixedTapeLinearEvents, fixedTapeLinearSlotEvents,
    fixedLinearActionEvent?, beforeQ16Slots, zeroCheckSlots, semanticSlots,
    oodSlots, fixedTapeGrindingChoice, fixedTapeRawMessages, rawPayloadAt,
    rawOfMessages, checkpointOfWorkStage, workNoncePayload, prefixAfterC2,
    semanticEvents, oodEvents]

theorem fixed_tape_after_q16_events_are_exact_accepted_suffix
    (tape : DeployedFixedTape) :
    fixedTapeLinearEvents tape afterQ16PreterminalSlots =
      afterAcceptedQueryScan tape.messages := by
  simp [fixedTapeLinearEvents, fixedTapeLinearSlotEvents,
    fixedLinearActionEvent?, afterQ16PreterminalSlots, relationTailSlots,
    fixedTapeRawMessages, rawPayloadAt, rawOfMessages, afterAcceptedQueryScan,
    relationTailEvents]

/-! ## Exact q16 cloned-branch execution -/

theorem begin_q16_marks_one_live_base
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (remaining : List FutureFreeSlot)
    (atControl : state.current.control =
      .linear (.beginQ16 :: remaining)) :
    ∃ next,
      NonterminalRawDriverTrace environment raw state 1 [] next ∧
      PathUsesFixedTable table [] ∧
      next.current.control =
        .q16Absorb state.current.core.digest 0 remaining ∧
      next.current.q16Candidates = state.current.q16Candidates ∧
      next.current.core.digest = state.current.core.digest ∧
      next.current.core.q16Base = some state.current.core.digest := by
  let action := VerifierAction.markQ16Base
  let nextCore : RuntimeCore :=
    { state.current.core with q16Base := some state.current.core.digest }
  let nextSnapshot : FutureFreeSnapshot :=
    { state.current with
      control := .q16Absorb state.current.core.digest 0 remaining
      core := nextCore }
  let next := appendFutureFreeSnapshot state (.verifier action .none)
    nextSnapshot
  have noSubmission : submitNextRawMessage raw state = none := by
    simp [submitNextRawMessage, atControl]
  have forced : state.current.control.nextVerifierAction? = some action := by
    rw [atControl]
    rfl
  have derived : deriveReply table state.current.bindings state.current.core
      action = some .none := by rfl
  have applied : applyActionWorkErased state.current.core action .none =
      some nextCore := by rfl
  have updated : afterFutureFreeVerifierReply environment state.current .none
      nextCore = some nextSnapshot := by
    simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
      atControl, nextCore, nextSnapshot]
  have advanced : advanceFutureFreeVerifier environment state .none =
      some next := by
    simpa [next] using
      advance_future_free_verifier_of_components environment state action .none
        nextCore nextSnapshot forced applied updated
  have nonterminal : isDriverHalt next.current.control = false := by rfl
  have microstep : MachineQueryPath
      (rawFutureFreeMicrostep environment raw state) [] next := by
    have actionPath : MachineQueryPath
        (futureFreeReplyProgram state action) [] .none := by
      exact structural_future_free_reply_path state action rfl
    have runner : MachineQueryPath
        (runOneFutureFreeVerifierAction environment state) [] next := by
      unfold runOneFutureFreeVerifierAction
      rw [forced]
      apply machine_query_path_bind_join _ _ [] [] .none next actionPath
      rw [advanced]
      exact .pure next
    simpa [rawFutureFreeMicrostep, noSubmission] using runner
  have trace : NonterminalRawDriverTrace environment raw state 1 [] next := by
    simpa using NonterminalRawDriverTrace.next microstep nonterminal
      (NonterminalRawDriverTrace.stop next)
  exact ⟨next, trace, path_uses_fixed_table_nil table, rfl, rfl, rfl, rfl⟩

theorem q16_candidate_absorb_run_gives_future_free_step
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (before after : EvalState) (base : Digest256) (counter : Fin 64)
    (remaining : List FutureFreeSlot)
    (atControl : state.current.control = .q16Absorb base counter remaining)
    (saved : state.current.core.q16Base = some base)
    (same : SameDigest state.current.core before)
    (run : absorbStep table before (.queryCandidate counter) = some after) :
    ∃ pairs next,
      NonterminalRawDriverTrace environment raw state 1 pairs next ∧
      PathUsesFixedTable table pairs ∧
      next.current.control = .q16Sample base counter [] remaining ∧
      next.current.q16Candidates = state.current.q16Candidates ∧
      next.current.core =
        { state.current.core with digest := after.digest } ∧
      next.current.core.q16Base = some base ∧
      SameDigest next.current.core after := by
  rw [absorbStep] at run
  obtain ⟨queryPair, queryRun, result⟩ := Option.bind_eq_some_iff.mp run
  rcases queryPair with ⟨output, stepped⟩
  have steppedEq : stepped = after := by
    simpa only [pure, Option.some.injEq] using result
  subst stepped
  obtain ⟨lookup, _calls, digest⟩ := query_step_appends_one table before
    after (.absorb (.queryCandidate counter)) output queryRun
  have outputEq : output = after.digest := by
    simpa only [RawQueryRole.nextDigest] using digest.symm
  subst output
  have normalized : tableLookup table
      (bytes before.digest ++
        [domAbsorb, queryCandidateLabel, UInt8.ofNat counter.val]) =
      some after.digest := by
    simpa only [RawQueryRole.input, Payload.label, Payload.data,
      List.append_assoc, List.cons_append, List.nil_append] using lookup
  have derived : deriveReply table state.current.bindings state.current.core
      (.absorb (.queryCandidate counter)) = some (.single after.digest) := by
    simp only [deriveReply, actionInputs, lookupSingleInput]
    change state.current.core.digest = before.digest at same
    rw [same]
    change (do
      let found ← tableLookup table
        (bytes before.digest ++
          [domAbsorb, queryCandidateLabel, UInt8.ofNat counter.val])
      pure (VerifierReply.single found)) =
        some (VerifierReply.single after.digest)
    rw [normalized]
    rfl
  let nextCore : RuntimeCore :=
    { state.current.core with digest := after.digest }
  have applied : applyActionWorkErased state.current.core
      (.absorb (.queryCandidate counter)) (.single after.digest) =
        some nextCore := by rfl
  let nextSnapshot : FutureFreeSnapshot :=
    { state.current with
      control := .q16Sample base counter [] remaining
      core := nextCore }
  let next := appendFutureFreeSnapshot state
    (.verifier (.absorb (.queryCandidate counter)) (.single after.digest))
    nextSnapshot
  have noSubmission : submitNextRawMessage raw state = none := by
    simp [submitNextRawMessage, atControl]
  have forced : state.current.control.nextVerifierAction? =
      some (.absorb (.queryCandidate counter)) := by
    rw [atControl]
    rfl
  have advanced : advanceFutureFreeVerifier environment state
      (.single after.digest) = some next := by
    have updated : afterFutureFreeVerifierReply environment state.current
        (.single after.digest) nextCore = some nextSnapshot := by
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        atControl, nextSnapshot]
    simpa [next] using
      advance_future_free_verifier_of_components environment state
        (.absorb (.queryCandidate counter)) (.single after.digest) nextCore
        nextSnapshot forced applied updated
  have nonterminal : isDriverHalt next.current.control = false := by rfl
  obtain ⟨pairs, trace, supported⟩ :=
    fixed_table_action_gives_one_nonterminal_trace table environment raw state
      next (.absorb (.queryCandidate counter)) (.single after.digest)
      noSubmission forced derived advanced nonterminal
  refine ⟨pairs, next, trace, supported, rfl, rfl, rfl, ?_, rfl⟩
  change state.current.core.q16Base = some base
  exact saved

theorem process_future_free_candidate_block_preserves_core
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (base : Digest256) (counter : Fin 64) (outputs : List Digest256)
    (remaining : List FutureFreeSlot) (output : Digest256)
    (nextCore : RuntimeCore) :
    (processFutureFreeCandidateBlock environment snapshot base counter outputs
      remaining output nextCore).core = nextCore := by
  unfold processFutureFreeCandidateBlock
  cases decoded : environment.decoders.candidate counter
      (outputs ++ [output]) with
  | none =>
      simp only [decoded]
      split <;> rfl
  | some outcome =>
      cases outcome with
      | samplerAbort => simp only [decoded]
      | schedule schedule =>
          simp only [decoded]
          split <;> rfl

theorem undecoded_candidate_block_continues_sampling
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (base : Digest256) (counter : Fin 64) (outputs : List Digest256)
    (remaining : List FutureFreeSlot) (output : Digest256)
    (nextCore : RuntimeCore)
    (undecoded : environment.decoders.candidate counter
      (outputs ++ [output]) = none)
    (belowCap : (outputs ++ [output]).length < 8) :
    (processFutureFreeCandidateBlock environment snapshot base counter outputs
      remaining output nextCore).control =
        .q16Sample base counter (outputs ++ [output]) remaining := by
  simp only [processFutureFreeCandidateBlock, undecoded, belowCap, if_pos]

theorem q16_candidate_squeeze_run_gives_future_free_step
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (before after : EvalState) (base : Digest256) (counter : Fin 64)
    (outputs : List Digest256) (remaining : List FutureFreeSlot)
    (block : Nat) (output : Digest256)
    (atControl : state.current.control =
      .q16Sample base counter outputs remaining)
    (blockIndex : block = outputs.length)
    (saved : state.current.core.q16Base = some base)
    (same : SameDigest state.current.core before)
    (run : squeezeStep table before (.queryCandidate counter) block =
      some (output, after))
    (processedNonterminal : isDriverHalt
      (processFutureFreeCandidateBlock environment state.current base counter
        outputs remaining output
        { state.current.core with digest := after.digest }).control = false) :
    ∃ pairs next,
      NonterminalRawDriverTrace environment raw state 1 pairs next ∧
      PathUsesFixedTable table pairs ∧
      next.current.control =
        (processFutureFreeCandidateBlock environment state.current base counter
          outputs remaining output
          { state.current.core with digest := after.digest }).control ∧
      next.current.q16Candidates =
        (processFutureFreeCandidateBlock environment state.current base counter
          outputs remaining output
          { state.current.core with digest := after.digest }).q16Candidates ∧
      next.current.core =
        { state.current.core with digest := after.digest } ∧
      next.current.core.q16Base = some base ∧
      SameDigest next.current.core after := by
  have noSubmission : submitNextRawMessage raw state = none := by
    simp [submitNextRawMessage, atControl]
  have forced : state.current.control.nextVerifierAction? =
      some (.squeezePair (.queryCandidate counter) block) := by
    rw [atControl, blockIndex]
    rfl
  obtain ⟨derived, applied, _pairs, _replyPath, _supported⟩ :=
    evaluator_squeeze_derives_exact_future_free_reply table state before after
      (.queryCandidate counter) block output same run
  let nextCore : RuntimeCore :=
    { state.current.core with digest := after.digest }
  let processed := processFutureFreeCandidateBlock environment state.current
    base counter outputs remaining output nextCore
  let nextSnapshot : FutureFreeSnapshot :=
    { processed with bindings := state.current.bindings }
  let next := appendFutureFreeSnapshot state
    (.verifier (.squeezePair (.queryCandidate counter) block)
      (.squeeze output after.digest)) nextSnapshot
  have updated : afterFutureFreeVerifierReply environment state.current
      (.squeeze output after.digest) nextCore = some nextSnapshot := by
    simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
      atControl, processed, nextSnapshot]
  have advanced : advanceFutureFreeVerifier environment state
      (.squeeze output after.digest) = some next := by
    simpa [next] using
      advance_future_free_verifier_of_components environment state
        (.squeezePair (.queryCandidate counter) block)
        (.squeeze output after.digest) nextCore nextSnapshot forced applied
        updated
  have nextControl : next.current.control = processed.control := by rfl
  have nextCoreEq : next.current.core = nextCore := by
    change processed.core = nextCore
    exact process_future_free_candidate_block_preserves_core environment
      state.current base counter outputs remaining output nextCore
  have nonterminal : isDriverHalt next.current.control = false := by
    rw [nextControl]
    exact processedNonterminal
  obtain ⟨pairs, trace, supported⟩ :=
    fixed_table_action_gives_one_nonterminal_trace table environment raw state
      next (.squeezePair (.queryCandidate counter) block)
      (.squeeze output after.digest) noSubmission forced derived advanced
      nonterminal
  refine ⟨pairs, next, trace, supported, nextControl, rfl, nextCoreEq, ?_, ?_⟩
  · rw [nextCoreEq]
    change state.current.core.q16Base = some base
    exact saved
  · rw [nextCoreEq]
    rfl

def decodedCandidateControl (environment : FutureFreeEnvironment)
    (base : Digest256) (counter : Fin 64) (outcome : CandidateOutcome)
    (remaining : List FutureFreeSlot) : FutureFreeControl :=
  match outcome with
  | .samplerAbort =>
      .q16SamplerReject counter (.q16SamplerAbort counter)
  | .schedule schedule =>
      if environment.frontierNodes schedule ≤ 203 then
        .q16Selected base counter schedule remaining
      else
        .q16Restore base counter (nextQ16Counter? counter) remaining

theorem evaluator_candidate_chain_gives_future_free_trace
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (before after : EvalState) (base : Digest256) (counter : Fin 64)
    (already fresh : List Digest256) (remaining : List FutureFreeSlot)
    (first : Nat) (outcome : CandidateOutcome)
    (chain : EvaluatorSqueezeChain table (.queryCandidate counter) first
      before fresh after)
    (atControl : state.current.control =
      .q16Sample base counter already remaining)
    (firstIndex : first = already.length)
    (saved : state.current.core.q16Base = some base)
    (same : SameDigest state.current.core before)
    (sampled : ∃ schedule, outcome = .schedule schedule)
    (accepted : environment.decoders.candidate counter (already ++ fresh) =
      some outcome)
    (withinCap : (already ++ fresh).length ≤ 8)
    (freshNonempty : fresh ≠ []) :
    ∃ pairs final,
      NonterminalRawDriverTrace environment raw state fresh.length pairs final ∧
      PathUsesFixedTable table pairs ∧
      final.current.control =
        decodedCandidateControl environment base counter outcome remaining ∧
      final.current.q16Candidates = state.current.q16Candidates ++
        [{ counter := counter, outcome := outcome }] ∧
      final.current.core.q16Base = some base ∧
      SameDigest final.current.core after := by
  obtain ⟨schedule, outcomeEq⟩ := sampled
  subst outcome
  induction chain generalizing state already with
  | done first before =>
      exact False.elim (freshNonempty rfl)
  | @next first before middle after output outputs head tail ih =>
      have minimal := accepted_future_free_candidate_is_prefix_minimal
        environment counter (already ++ output :: outputs)
          (.schedule schedule) accepted
      cases outputs with
      | nil =>
          cases tail
          have decodedLast : environment.decoders.candidate counter
              (already ++ [output]) = some (.schedule schedule) := by
            simpa using accepted
          have processedNonterminal : isDriverHalt
              (processFutureFreeCandidateBlock environment state.current base
                counter already remaining output
                { state.current.core with digest := middle.digest }).control =
                false := by
            by_cases compact : environment.frontierNodes schedule ≤ 203
            · rw [compact_candidate_block_forces_selection environment
                state.current base counter already remaining output
                { state.current.core with digest := middle.digest } schedule
                decodedLast compact]
              rfl
            · have noncompact : 203 < environment.frontierNodes schedule := by
                omega
              rw [noncompact_candidate_block_forces_protocol_restore
                environment state.current base counter already remaining
                output { state.current.core with digest := middle.digest }
                schedule decodedLast noncompact]
              rfl
          obtain ⟨pairs, final, trace, supported, finalControl,
              finalCandidates, _finalCore, finalSaved, finalSame⟩ :=
            q16_candidate_squeeze_run_gives_future_free_step table environment
              raw state before middle base counter already remaining first
              output atControl firstIndex saved same head processedNonterminal
          refine ⟨pairs, final, by simpa using trace, supported, ?_, ?_,
            finalSaved, finalSame⟩
          · rw [finalControl]
            by_cases compact : environment.frontierNodes schedule ≤ 203
            · rw [compact_candidate_block_forces_selection environment
                state.current base counter already remaining output
                { state.current.core with digest := middle.digest } schedule
                decodedLast compact]
              simp [decodedCandidateControl, compact]
            · have noncompact : 203 < environment.frontierNodes schedule := by
                omega
              rw [noncompact_candidate_block_forces_protocol_restore
                environment state.current base counter already remaining output
                { state.current.core with digest := middle.digest } schedule
                decodedLast noncompact]
              simp [decodedCandidateControl, compact]
          · rw [finalCandidates]
            simp only [processFutureFreeCandidateBlock, decodedLast]
            split <;> rfl
      | cons nextOutput restOutputs =>
          let accumulated := already ++ [output]
          have totalEq : already ++ output :: nextOutput :: restOutputs =
              accumulated ++ nextOutput :: restOutputs := by
            simp [accumulated, List.append_assoc]
          have accumulatedShort : accumulated.length <
              (already ++ output :: nextOutput :: restOutputs).length := by
            simp [accumulated]
          have takeEq :
              (already ++ output :: nextOutput :: restOutputs).take
                  accumulated.length = accumulated := by
            rw [totalEq, List.take_append_of_le_length (Nat.le_refl _),
              List.take_length]
          have undecoded : environment.decoders.candidate counter accumulated =
              none := by
            rw [← takeEq]
            exact minimal accumulated.length accumulatedShort
          have accumulatedBelowCap : accumulated.length < 8 := by
            have totalLength :
                (already ++ output :: nextOutput :: restOutputs).length ≤ 8 := by
              simpa using withinCap
            omega
          have processContinues :
              (processFutureFreeCandidateBlock environment state.current base
                counter already remaining output
                { state.current.core with digest := middle.digest }).control =
              .q16Sample base counter accumulated remaining := by
            exact undecoded_candidate_block_continues_sampling environment
              state.current base counter already remaining output
              { state.current.core with digest := middle.digest } undecoded
              (by simpa [accumulated] using accumulatedBelowCap)
          have processedNonterminal : isDriverHalt
              (processFutureFreeCandidateBlock environment state.current base
                counter already remaining output
                { state.current.core with digest := middle.digest }).control =
                false := by
            rw [processContinues]
            rfl
          obtain ⟨headPairs, nextState, headTrace, headSupported,
              nextControl, nextCandidates, _nextCore, nextSaved, nextSame⟩ :=
            q16_candidate_squeeze_run_gives_future_free_step table environment
              raw state before middle base counter already remaining first
              output atControl firstIndex saved same head processedNonterminal
          have nextAtControl : nextState.current.control =
              .q16Sample base counter accumulated remaining := by
            rw [nextControl, processContinues]
          have nextFirstIndex : first + 1 = accumulated.length := by
            simp [accumulated, firstIndex]
          have tailWithinCap :
              (accumulated ++ nextOutput :: restOutputs).length ≤ 8 := by
            rw [← totalEq]
            exact withinCap
          have tailAccepted : environment.decoders.candidate counter
              (accumulated ++ nextOutput :: restOutputs) =
                some (.schedule schedule) := by
            rw [← totalEq]
            exact accepted
          obtain ⟨tailPairs, final, tailTrace, tailSupported, finalControl,
              finalCandidates, finalSaved, finalSame⟩ :=
            ih (state := nextState) (already := accumulated) nextAtControl
              nextFirstIndex nextSaved nextSame tailWithinCap
              (by simp) tailAccepted
          refine ⟨headPairs ++ tailPairs, final, ?_, ?_, ?_, ?_, finalSaved,
            finalSame⟩
          · have combined := nonterminal_raw_driver_trace_append environment raw
              state nextState final 1 (nextOutput :: restOutputs).length
              headPairs tailPairs headTrace tailTrace
            simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using combined
          · exact path_uses_fixed_table_append table headPairs tailPairs
              headSupported tailSupported
          · exact finalControl
          · have undecoded' :
                environment.decoders.candidate counter (already ++ [output]) =
                  none := by
              simpa [accumulated] using undecoded
            rw [finalCandidates, nextCandidates]
            simp only [processFutureFreeCandidateBlock, undecoded']
            split <;> rfl

theorem q16_candidate_run_gives_future_free_trace
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (before finalEval : EvalState) (base : Digest256)
    (spec : CandidateSpec) (remaining : List FutureFreeSlot)
    (atControl : state.current.control =
      .q16Absorb base spec.counter remaining)
    (saved : state.current.core.q16Base = some base)
    (same : SameDigest state.current.core before)
    (run : runCandidate table before spec = some finalEval)
    (sampled : ∃ schedule, spec.outcome = .schedule schedule)
    (decoderEq : environment.decoders = exactDeterministicDecoders)
    (decodedState : StateCandidatesDecodeAs finalEval) :
    ∃ steps pairs final,
      NonterminalRawDriverTrace environment raw state steps pairs final ∧
      PathUsesFixedTable table pairs ∧
      final.current.control = decodedCandidateControl environment base
        spec.counter spec.outcome remaining ∧
      final.current.q16Candidates = state.current.q16Candidates ++
        [{ counter := spec.counter, outcome := spec.outcome }] ∧
      final.current.core.q16Base = some base ∧
      SameDigest final.current.core finalEval ∧
      steps = 1 + spec.outcome.blocksUsed := by
  obtain ⟨afterCounter, blocks, afterBlocks, absorbRun, squeezeRun,
      finalEvalEq, blocksLength, recordMember⟩ :=
    run_candidate_exposes_exact_record table before finalEval spec run
  let record : CandidateRecord :=
    { counter := spec.counter
      outcome := spec.outcome
      baseDigest := before.digest
      endDigest := afterBlocks.digest
      blocks := blocks }
  have recordMember' : record ∈ finalEval.candidates := by
    simpa [record] using recordMember
  have acceptedExact : exactDeterministicDecoders.candidate spec.counter blocks =
      some spec.outcome := by
    simpa [record] using decodedState record recordMember'
  have accepted : environment.decoders.candidate spec.counter blocks =
      some spec.outcome := by
    rw [decoderEq]
    exact acceptedExact
  have withinCap : blocks.length ≤ 8 := by
    rw [blocksLength]
    exact candidate_outcome_blocks_le_eight spec.outcome
  have blocksNonempty : blocks ≠ [] := by
    intro empty
    have lengthZero : blocks.length = 0 := by simp [empty]
    obtain ⟨schedule, outcomeEq⟩ := sampled
    have positive : 2 ≤ spec.outcome.blocksUsed := by
      rw [outcomeEq]
      exact schedule.atLeastTwoBlocks
    rw [blocksLength] at lengthZero
    omega
  obtain ⟨absorbPairs, afterAbsorbState, absorbTrace, absorbTable,
      absorbControl, absorbCandidates, _absorbCore, absorbSaved, absorbSame⟩ :=
    q16_candidate_absorb_run_gives_future_free_step table environment raw state
      before afterCounter base spec.counter remaining atControl saved same
      absorbRun
  have chain : EvaluatorSqueezeChain table (.queryCandidate spec.counter) 0
      afterCounter blocks afterBlocks :=
    evaluator_squeeze_chain_of_run table (.queryCandidate spec.counter) 0
      spec.outcome.blocksUsed afterCounter afterBlocks blocks
      (by simpa [squeezeMany] using squeezeRun)
  obtain ⟨squeezePairs, final, squeezeTrace, squeezeTable, finalControl,
      finalCandidates, finalSaved, finalSame⟩ :=
    evaluator_candidate_chain_gives_future_free_trace table environment raw
      afterAbsorbState afterCounter afterBlocks base spec.counter [] blocks
      remaining 0 spec.outcome chain absorbControl rfl absorbSaved absorbSame
      sampled (by simpa using accepted) (by simpa using withinCap)
      blocksNonempty
  have combined := nonterminal_raw_driver_trace_append environment raw state
    afterAbsorbState final 1 blocks.length absorbPairs squeezePairs absorbTrace
    squeezeTrace
  refine ⟨1 + blocks.length, absorbPairs ++ squeezePairs, final, combined,
    path_uses_fixed_table_append table absorbPairs squeezePairs absorbTable
      squeezeTable, finalControl, ?_, finalSaved, ?_, ?_⟩
  · rw [finalCandidates, absorbCandidates]
  · have digestEq : afterBlocks.digest = finalEval.digest := by
      rw [finalEvalEq]
    exact finalSame.trans digestEq
  · rw [blocksLength]

theorem q16_restore_to_successor_gives_future_free_step
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (base : Digest256) (counter nextCounter : Fin 64)
    (remaining : List FutureFreeSlot)
    (atControl : state.current.control =
      .q16Restore base counter (some nextCounter) remaining)
    (saved : state.current.core.q16Base = some base) :
    ∃ next,
      NonterminalRawDriverTrace environment raw state 1 [] next ∧
      PathUsesFixedTable table [] ∧
      next.current.control = .q16Absorb base nextCounter remaining ∧
      next.current.q16Candidates = state.current.q16Candidates ∧
      next.current.core.digest = base ∧
      next.current.core.q16Base = some base := by
  let action := VerifierAction.q16Restore counter
  let nextCore : RuntimeCore :=
    { state.current.core with digest := base }
  let nextSnapshot : FutureFreeSnapshot :=
    { state.current with
      control := .q16Absorb base nextCounter remaining
      core := nextCore }
  let next := appendFutureFreeSnapshot state (.verifier action .none)
    nextSnapshot
  have noSubmission : submitNextRawMessage raw state = none := by
    simp [submitNextRawMessage, atControl]
  have forced : state.current.control.nextVerifierAction? = some action := by
    rw [atControl]
    rfl
  have derived : deriveReply table state.current.bindings state.current.core
      action = some .none := by rfl
  have applied : applyActionWorkErased state.current.core action .none =
      some nextCore := by
    simp [action, applyActionWorkErased, saved, nextCore]
  have updated : afterFutureFreeVerifierReply environment state.current .none
      nextCore = some nextSnapshot := by
    simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
      atControl, nextSnapshot]
  have advanced : advanceFutureFreeVerifier environment state .none =
      some next := by
    simpa [next] using
      advance_future_free_verifier_of_components environment state action .none
        nextCore nextSnapshot forced applied updated
  have nonterminal : isDriverHalt next.current.control = false := by rfl
  have actionPath : MachineQueryPath (futureFreeReplyProgram state action) []
      .none := structural_future_free_reply_path state action rfl
  have runner : MachineQueryPath
      (runOneFutureFreeVerifierAction environment state) [] next := by
    unfold runOneFutureFreeVerifierAction
    rw [forced]
    apply machine_query_path_bind_join _ _ [] [] .none next actionPath
    rw [advanced]
    exact .pure next
  have microstep : MachineQueryPath
      (rawFutureFreeMicrostep environment raw state) [] next := by
    simpa [rawFutureFreeMicrostep, noSubmission] using runner
  have trace : NonterminalRawDriverTrace environment raw state 1 [] next := by
    simpa using NonterminalRawDriverTrace.next microstep nonterminal
      (NonterminalRawDriverTrace.stop next)
  refine ⟨next, trace, path_uses_fixed_table_nil table, rfl, rfl, rfl, ?_⟩
  change state.current.core.q16Base = some base
  exact saved

theorem q16_selected_marker_gives_future_free_step
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (base : Digest256) (counter : Fin 64) (schedule : QuerySchedule)
    (remaining : List FutureFreeSlot)
    (atControl : state.current.control =
      .q16Selected base counter schedule remaining)
    (remainingNonempty : remaining ≠ []) :
    ∃ next,
      NonterminalRawDriverTrace environment raw state 1 [] next ∧
      PathUsesFixedTable table [] ∧
      next.current.control = .linear remaining ∧
      next.current.q16Candidates = state.current.q16Candidates ∧
      next.current.core = state.current.core := by
  let action := VerifierAction.q16Selected counter
  let nextSnapshot : FutureFreeSnapshot :=
    { state.current with control := .linear remaining }
  let next := appendFutureFreeSnapshot state (.verifier action .none)
    nextSnapshot
  have noSubmission : submitNextRawMessage raw state = none := by
    simp [submitNextRawMessage, atControl]
  have forced : state.current.control.nextVerifierAction? = some action := by
    rw [atControl]
    rfl
  have derived : deriveReply table state.current.bindings state.current.core
      action = some .none := by rfl
  have applied : applyActionWorkErased state.current.core action .none =
      some state.current.core := by rfl
  have updated : afterFutureFreeVerifierReply environment state.current .none
      state.current.core = some nextSnapshot := by
    simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
      atControl, linearOrDone, remainingNonempty, nextSnapshot]
  have advanced : advanceFutureFreeVerifier environment state .none =
      some next := by
    simpa [next] using
      advance_future_free_verifier_of_components environment state action .none
        state.current.core nextSnapshot forced applied updated
  have nonterminal : isDriverHalt next.current.control = false := by rfl
  have actionPath : MachineQueryPath (futureFreeReplyProgram state action) []
      .none := structural_future_free_reply_path state action rfl
  have runner : MachineQueryPath
      (runOneFutureFreeVerifierAction environment state) [] next := by
    unfold runOneFutureFreeVerifierAction
    rw [forced]
    apply machine_query_path_bind_join _ _ [] [] .none next actionPath
    rw [advanced]
    exact .pure next
  have microstep : MachineQueryPath
      (rawFutureFreeMicrostep environment raw state) [] next := by
    simpa [rawFutureFreeMicrostep, noSubmission] using runner
  have trace : NonterminalRawDriverTrace environment raw state 1 [] next := by
    simpa using NonterminalRawDriverTrace.next microstep nonterminal
      (NonterminalRawDriverTrace.stop next)
  exact ⟨next, trace, path_uses_fixed_table_nil table, rfl, rfl, rfl⟩

inductive ExactDiscardedQ16Plan (environment : FutureFreeEnvironment) :
    Fin 64 → List CandidateSpec → Fin 64 → Prop where
  | done (counter : Fin 64) :
      ExactDiscardedQ16Plan environment counter [] counter
  | step {counter next finalCounter : Fin 64}
      (schedule : QuerySchedule) (rest : List CandidateSpec)
      (noncompact : 203 < environment.frontierNodes schedule)
      (successor : nextQ16Counter? counter = some next)
      (tail : ExactDiscardedQ16Plan environment next rest finalCounter) :
      ExactDiscardedQ16Plan environment counter
        ({ counter := counter, outcome := .schedule schedule } :: rest)
        finalCounter

def earlierSpecsSlice {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) (start count : Nat)
    (withinSelected : start + count ≤ search.selectedCounter.val) :
    List CandidateSpec :=
  (List.finRange count).map fun offset =>
    let counter : Fin 64 :=
      ⟨start + offset.val, by
        have belowEnd : start + offset.val < start + count := by omega
        exact Nat.lt_trans (Nat.lt_of_lt_of_le belowEnd withinSelected)
          search.selectedCounter.isLt⟩
    { counter := counter, outcome := search.outcome counter }

theorem exact_discarded_q16_plan_for_slice
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) (start count : Nat)
    (withinSelected : start + count ≤ search.selectedCounter.val) :
    ExactDiscardedQ16Plan
      { frontierNodes := frontierNodes }
      ⟨start, by omega⟩
      (earlierSpecsSlice search start count withinSelected)
      ⟨start + count, by omega⟩ := by
  induction count generalizing start with
  | zero =>
      simpa [earlierSpecsSlice] using
        (ExactDiscardedQ16Plan.done
          (environment :=
            ({ frontierNodes := frontierNodes } : FutureFreeEnvironment))
          ⟨start, by omega⟩)
  | succ count ih =>
      let counter : Fin 64 := ⟨start, by omega⟩
      let next : Fin 64 := ⟨start + 1, by omega⟩
      have earlier : counter.val < search.selectedCounter.val := by
        dsimp [counter]
        omega
      obtain ⟨schedule, outcomeEq, noncompact⟩ :=
        search.everyEarlierSampledAndNoncompact counter earlier
      have tailWithin : (start + 1) + count ≤
          search.selectedCounter.val := by omega
      have tailPlan := ih (start := start + 1) tailWithin
      have successor : nextQ16Counter? counter = some next := by
        unfold nextQ16Counter?
        split
        · rfl
        · rename_i unavailable
          exfalso
          apply unavailable
          dsimp [counter]
          omega
      have stepPlan := ExactDiscardedQ16Plan.step schedule
        (earlierSpecsSlice search (start + 1) count tailWithin) noncompact
        successor tailPlan
      have outcomeSpec :
          ({ counter := counter, outcome := search.outcome counter } :
              CandidateSpec) =
            { counter := counter, outcome := .schedule schedule } := by
        rw [outcomeEq]
      rw [← outcomeSpec] at stepPlan
      simpa [earlierSpecsSlice, List.finRange_succ, Function.comp_def,
        counter, next, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        stepPlan

theorem exact_discarded_q16_plan_of_first_cap_search
    (tape : DeployedFixedTape) :
    ExactDiscardedQ16Plan (fixedTapeFutureFreeEnvironment tape) 0
      (q16TapeOfSearch tape.search).earlier tape.search.selectedCounter := by
  have slicePlan := exact_discarded_q16_plan_for_slice tape.search 0
    tape.search.selectedCounter.val (by omega)
  simpa [fixedTapeFutureFreeEnvironment, q16TapeOfSearch, earlierSpecs,
    earlierSpecsSlice, Function.comp_def] using slicePlan

def discardedQ16Fuel : List CandidateSpec → Nat
  | [] => 0
  | spec :: rest => 2 + spec.outcome.blocksUsed + discardedQ16Fuel rest

def decodedCandidatesOfSpecs (specs : List CandidateSpec) :
    List DecodedQ16Candidate :=
  specs.map fun spec =>
    { counter := spec.counter, outcome := spec.outcome }

theorem discarded_q16_plan_gives_future_free_trace
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (before finalEval : EvalState) (base : Digest256)
    (counter finalCounter : Fin 64) (specs : List CandidateSpec)
    (remaining : List FutureFreeSlot)
    (plan : ExactDiscardedQ16Plan environment counter specs finalCounter)
    (atControl : state.current.control = .q16Absorb base counter remaining)
    (saved : state.current.core.q16Base = some base)
    (same : SameDigest state.current.core before)
    (atBase : before.digest = base)
    (run : runDiscardedCandidates table base specs before = some finalEval)
    (decoderEq : environment.decoders = exactDeterministicDecoders)
    (decodedState : StateCandidatesDecodeAs finalEval) :
    ∃ steps pairs final,
      NonterminalRawDriverTrace environment raw state steps pairs final ∧
      PathUsesFixedTable table pairs ∧
      final.current.control = .q16Absorb base finalCounter remaining ∧
      final.current.q16Candidates = state.current.q16Candidates ++
        decodedCandidatesOfSpecs specs ∧
      final.current.core.q16Base = some base ∧
      SameDigest final.current.core finalEval ∧
      steps = discardedQ16Fuel specs := by
  induction plan generalizing state before with
  | done counter =>
      rw [runDiscardedCandidates] at run
      have equal : before = finalEval := Option.some.inj run
      subst finalEval
      exact ⟨0, [], state, .stop state, path_uses_fixed_table_nil table,
        atControl, by simp [decodedCandidatesOfSpecs], saved, same, rfl⟩
  | @step counter next finalCounter schedule rest noncompact successor
      tailPlan ih =>
      rw [runDiscardedCandidates] at run
      obtain ⟨branch, branchRun, restRun⟩ := Option.bind_eq_some_iff.mp run
      have restIncluded : CandidatesIncluded (restoreDigest base branch)
          finalEval :=
        run_discarded_candidates_preserves_prior_candidates table base rest
          (restoreDigest base branch) finalEval restRun
      have branchDecoded : StateCandidatesDecodeAs branch := by
        apply state_candidates_decode_of_included branch finalEval
        · intro record member
          exact restIncluded record (by
            change record ∈ branch.candidates
            exact member)
        · exact decodedState
      let spec : CandidateSpec :=
        { counter := counter, outcome := .schedule schedule }
      obtain ⟨candidateSteps, candidatePairs, afterCandidate,
          candidateTrace, candidateTable, candidateControl, _candidateLedger,
          candidateSaved, candidateSame, candidateFuel⟩ :=
        q16_candidate_run_gives_future_free_trace table environment raw state
          before branch base spec remaining atControl saved same branchRun
          ⟨schedule, rfl⟩ decoderEq branchDecoded
      have candidateControl' : afterCandidate.current.control =
          .q16Restore base counter (some next) remaining := by
        rw [candidateControl]
        simp [decodedCandidateControl, spec, noncompact, successor,
          Nat.not_le.mpr noncompact]
      obtain ⟨restored, restoreTrace, restoreTable, restoredControl,
          _restoredCandidates, restoredDigest, restoredSaved⟩ :=
        q16_restore_to_successor_gives_future_free_step table environment raw
          afterCandidate base counter next remaining candidateControl'
          candidateSaved
      have restoredSame : SameDigest restored.current.core
          (restoreDigest base branch) := by
        change restored.current.core.digest = base
        exact restoredDigest
      obtain ⟨tailSteps, tailPairs, final, tailTrace, tailTable,
          finalControl, finalCandidates, finalSaved, finalSame, tailFuel⟩ :=
        ih restored (restoreDigest base branch) restoredControl restoredSaved
          restoredSame rfl restRun
      have throughRestore := nonterminal_raw_driver_trace_append environment raw
        state afterCandidate restored candidateSteps 1 candidatePairs []
        candidateTrace restoreTrace
      have allTrace := nonterminal_raw_driver_trace_append environment raw state
        restored final (candidateSteps + 1) tailSteps
        (candidatePairs ++ []) tailPairs throughRestore tailTrace
      refine ⟨(candidateSteps + 1) + tailSteps,
        (candidatePairs ++ []) ++ tailPairs, final, allTrace,
        path_uses_fixed_table_append table (candidatePairs ++ []) tailPairs
          (path_uses_fixed_table_append table candidatePairs [] candidateTable
            restoreTable) tailTable,
        finalControl, ?_, finalSaved, finalSame, ?_⟩
      · rw [finalCandidates, _restoredCandidates, _candidateLedger]
        simp [decodedCandidatesOfSpecs, spec, List.append_assoc]
      · simp [discardedQ16Fuel, spec, candidateFuel, tailFuel]
        omega

/-- The semantic discarded-candidate run advances the exact first-compact
history by precisely the records named by the control-flow plan.  This is
independent of the future-free state ledger; the two equalities are composed
only at the accepted-run boundary. -/
theorem discarded_q16_plan_advances_prior_history
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (before finalEval : EvalState) (base : Digest256)
    (counter finalCounter : Fin 64) (specs : List CandidateSpec)
    (plan : ExactDiscardedQ16Plan environment counter specs finalCounter)
    (run : runDiscardedCandidates table base specs before = some finalEval)
    (decoderEq : environment.decoders = exactDeterministicDecoders)
    (decodedState : StateCandidatesDecodeAs finalEval)
    (records : List DecodedQ16Candidate)
    (prior : Q16PriorNoncompactHistory environment counter records) :
    Q16PriorNoncompactHistory environment finalCounter
      (records ++ decodedCandidatesOfSpecs specs) := by
  induction plan generalizing before records with
  | done counter =>
      simpa [decodedCandidatesOfSpecs] using prior
  | @step counter next finalCounter schedule rest noncompact successor
      tailPlan ih =>
      rw [runDiscardedCandidates] at run
      obtain ⟨branch, branchRun, restRun⟩ := Option.bind_eq_some_iff.mp run
      have restIncluded : CandidatesIncluded (restoreDigest base branch)
          finalEval :=
        run_discarded_candidates_preserves_prior_candidates table base rest
          (restoreDigest base branch) finalEval restRun
      have branchDecoded : StateCandidatesDecodeAs branch := by
        apply state_candidates_decode_of_included branch finalEval
        · intro record member
          exact restIncluded record (by
            change record ∈ branch.candidates
            exact member)
        · exact decodedState
      let spec : CandidateSpec :=
        { counter := counter, outcome := .schedule schedule }
      obtain ⟨_afterCounter, blocks, _afterBlocks, _absorbRun, _squeezeRun,
          _branchExact, _blocksLength, recordMember⟩ :=
        run_candidate_exposes_exact_record table before branch spec branchRun
      have exactDecode := branchDecoded _ recordMember
      have environmentDecode :
          environment.decoders.candidate counter blocks =
            some (.schedule schedule) := by
        rw [decoderEq]
        simpa [spec] using exactDecode
      have nextHistory : Q16PriorNoncompactHistory environment next
          (records ++ [decodedScheduleRecord counter schedule]) :=
        Q16PriorNoncompactHistory.step blocks schedule prior environmentDecode
          noncompact successor
      have tailHistory := ih (restoreDigest base branch) restRun
        (records ++ [decodedScheduleRecord counter schedule]) nextHistory
      simpa [decodedCandidatesOfSpecs, spec, decodedScheduleRecord,
        List.append_assoc] using tailHistory

theorem accepting_q16_run_gives_future_free_trace
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace)
    (state : FutureFreeVerifierState) (baseState afterQ16 : EvalState)
    (remaining : List FutureFreeSlot)
    (atControl : state.current.control =
      .linear (.beginQ16 :: remaining))
    (same : SameDigest state.current.core baseState)
    (q16Run : runQ16 table baseState (q16TapeOfSearch tape.search) =
      some afterQ16)
    (plan : ExactDiscardedQ16Plan (fixedTapeFutureFreeEnvironment tape) 0
      (q16TapeOfSearch tape.search).earlier tape.search.selectedCounter)
    (decodedState : StateCandidatesDecodeAs afterQ16)
    (remainingNonempty : remaining ≠ []) :
    ∃ steps pairs final,
      NonterminalRawDriverTrace (fixedTapeFutureFreeEnvironment tape)
        (fixedTapeRawMessages tape) state steps pairs final ∧
      PathUsesFixedTable table pairs ∧
      final.current.control = .linear remaining ∧
      final.current.q16Candidates = state.current.q16Candidates ++
        decodedCandidatesOfSpecs (q16TapeOfSearch tape.search).earlier ++
          [decodedScheduleRecord tape.search.selectedCounter
            tape.search.selectedSchedule] ∧
      SameDigest final.current.core afterQ16 ∧
      steps = 2 + discardedQ16Fuel
          (q16TapeOfSearch tape.search).earlier +
        (1 + (q16TapeOfSearch tape.search).selected.outcome.blocksUsed) := by
  rw [runQ16] at q16Run
  obtain ⟨beforeSelected, earlierRun, selectedRun⟩ :=
    Option.bind_eq_some_iff.mp q16Run
  obtain ⟨marked, markTrace, markTable, markControl, markCandidates,
      markDigest, markSaved⟩ :=
    begin_q16_marks_one_live_base table (fixedTapeFutureFreeEnvironment tape)
      (fixedTapeRawMessages tape) state remaining atControl
  have baseEq : state.current.core.digest = baseState.digest := same
  have markControl' : marked.current.control =
      .q16Absorb baseState.digest 0 remaining := by
    rw [markControl, baseEq]
  have markedSame : SameDigest marked.current.core baseState := by
    change marked.current.core.digest = baseState.digest
    exact markDigest.trans baseEq
  have markedSaved : marked.current.core.q16Base = some baseState.digest := by
    rw [markSaved, baseEq]
  have selectedIncluded : CandidatesIncluded beforeSelected afterQ16 :=
    run_candidate_preserves_prior_candidates table beforeSelected afterQ16
      (q16TapeOfSearch tape.search).selected selectedRun
  have earlierDecoded : StateCandidatesDecodeAs beforeSelected :=
    state_candidates_decode_of_included beforeSelected afterQ16
      selectedIncluded decodedState
  obtain ⟨discardedSteps, discardedPairs, beforeSelectedState,
      discardedTrace, discardedTable, selectedControl, discardedCandidates,
      selectedSaved, selectedSame, discardedFuelEq⟩ :=
    discarded_q16_plan_gives_future_free_trace table
      (fixedTapeFutureFreeEnvironment tape) (fixedTapeRawMessages tape) marked
      baseState beforeSelected baseState.digest 0 tape.search.selectedCounter
      (q16TapeOfSearch tape.search).earlier remaining plan markControl'
      markedSaved markedSame rfl earlierRun (by rfl) earlierDecoded
  obtain ⟨selectedSteps, selectedPairs, selectedState, selectedTrace,
      selectedTable, decodedControl, selectedLedger, selectedBaseSaved,
      selectedFinalSame, selectedFuelEq⟩ :=
    q16_candidate_run_gives_future_free_trace table
      (fixedTapeFutureFreeEnvironment tape) (fixedTapeRawMessages tape)
      beforeSelectedState beforeSelected afterQ16 baseState.digest
      (q16TapeOfSearch tape.search).selected remaining selectedControl
      selectedSaved selectedSame selectedRun
      ⟨tape.search.selectedSchedule, rfl⟩ (by rfl) decodedState
  have selectedControl' : selectedState.current.control =
      .q16Selected baseState.digest tape.search.selectedCounter
        tape.search.selectedSchedule remaining := by
    rw [decodedControl]
    simp [decodedCandidateControl, fixedTapeFutureFreeEnvironment,
      q16TapeOfSearch, tape.search.selectedCompact]
  obtain ⟨afterMarker, markerTrace, markerTable, finalControl,
      markerCandidates, markerCore⟩ :=
    q16_selected_marker_gives_future_free_step table
      (fixedTapeFutureFreeEnvironment tape) (fixedTapeRawMessages tape)
      selectedState baseState.digest tape.search.selectedCounter
      tape.search.selectedSchedule remaining selectedControl'
      remainingNonempty
  have markerSame : SameDigest afterMarker.current.core afterQ16 := by
    rw [markerCore]
    exact selectedFinalSame
  have throughDiscarded := nonterminal_raw_driver_trace_append
    (fixedTapeFutureFreeEnvironment tape) (fixedTapeRawMessages tape) state
    marked beforeSelectedState 1 discardedSteps [] discardedPairs markTrace
    discardedTrace
  have throughSelected := nonterminal_raw_driver_trace_append
    (fixedTapeFutureFreeEnvironment tape) (fixedTapeRawMessages tape) state
    beforeSelectedState selectedState (1 + discardedSteps) selectedSteps
    ([] ++ discardedPairs) selectedPairs throughDiscarded selectedTrace
  have allTrace := nonterminal_raw_driver_trace_append
    (fixedTapeFutureFreeEnvironment tape) (fixedTapeRawMessages tape) state
    selectedState afterMarker ((1 + discardedSteps) + selectedSteps) 1
    (([] ++ discardedPairs) ++ selectedPairs) [] throughSelected markerTrace
  refine ⟨((1 + discardedSteps) + selectedSteps) + 1,
    (([] ++ discardedPairs) ++ selectedPairs) ++ [], afterMarker, allTrace,
    path_uses_fixed_table_append table
      (([] ++ discardedPairs) ++ selectedPairs) []
      (path_uses_fixed_table_append table ([] ++ discardedPairs) selectedPairs
        (path_uses_fixed_table_append table [] discardedPairs markTable
          discardedTable) selectedTable) markerTable,
    finalControl, ?_, markerSame, ?_⟩
  · rw [markerCandidates, selectedLedger, discardedCandidates,
      markCandidates]
    rfl
  · rw [discardedFuelEq, selectedFuelEq]
    omega

/-- If the verifier reaches its unique q16 scan with an empty candidate
ledger, the accepted run returns the complete restoration-stable certificate:
all earlier records are exact noncompact successors and the final record is
the first compact selection. -/
theorem accepting_q16_run_gives_selected_ledger_certificate
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace)
    (state : FutureFreeVerifierState) (baseState afterQ16 : EvalState)
    (remaining : List FutureFreeSlot)
    (atControl : state.current.control =
      .linear (.beginQ16 :: remaining))
    (initialCandidates : state.current.q16Candidates = [])
    (same : SameDigest state.current.core baseState)
    (q16Run : runQ16 table baseState (q16TapeOfSearch tape.search) =
      some afterQ16)
    (plan : ExactDiscardedQ16Plan (fixedTapeFutureFreeEnvironment tape) 0
      (q16TapeOfSearch tape.search).earlier tape.search.selectedCounter)
    (decodedState : StateCandidatesDecodeAs afterQ16)
    (remainingNonempty : remaining ≠ []) :
    ∃ steps pairs final,
      ∃ certificate : SelectedQ16LedgerCertificate
          (fixedTapeFutureFreeEnvironment tape) final.current,
      certificate.selectedCounter = tape.search.selectedCounter ∧
      certificate.selectedSchedule = tape.search.selectedSchedule ∧
      NonterminalRawDriverTrace (fixedTapeFutureFreeEnvironment tape)
        (fixedTapeRawMessages tape) state steps pairs final ∧
      PathUsesFixedTable table pairs ∧
      final.current.control = .linear remaining ∧
      SameDigest final.current.core afterQ16 ∧
      steps = 2 + discardedQ16Fuel
          (q16TapeOfSearch tape.search).earlier +
        (1 + (q16TapeOfSearch tape.search).selected.outcome.blocksUsed) := by
  have q16RunParts := q16Run
  rw [runQ16] at q16RunParts
  obtain ⟨beforeSelected, earlierRun, selectedRun⟩ :=
    Option.bind_eq_some_iff.mp q16RunParts
  have selectedIncluded : CandidatesIncluded beforeSelected afterQ16 :=
    run_candidate_preserves_prior_candidates table beforeSelected afterQ16
      (q16TapeOfSearch tape.search).selected selectedRun
  have earlierDecoded : StateCandidatesDecodeAs beforeSelected :=
    state_candidates_decode_of_included beforeSelected afterQ16
      selectedIncluded decodedState
  have priorHistory : Q16PriorNoncompactHistory
      (fixedTapeFutureFreeEnvironment tape) tape.search.selectedCounter
      (decodedCandidatesOfSpecs (q16TapeOfSearch tape.search).earlier) := by
    simpa using
      (discarded_q16_plan_advances_prior_history table
        (fixedTapeFutureFreeEnvironment tape) baseState beforeSelected
        baseState.digest 0 tape.search.selectedCounter
        (q16TapeOfSearch tape.search).earlier plan earlierRun (by rfl)
        earlierDecoded []
        (Q16PriorNoncompactHistory.start
          (environment := fixedTapeFutureFreeEnvironment tape)))
  obtain ⟨steps, pairs, final, trace, supported, finalControl,
      ledgerExact, finalSame, fuelExact⟩ :=
    accepting_q16_run_gives_future_free_trace table tape rawTrace state
      baseState afterQ16 remaining atControl same q16Run plan decodedState
      remainingNonempty
  have ledgerExact' : final.current.q16Candidates =
      decodedCandidatesOfSpecs (q16TapeOfSearch tape.search).earlier ++
        [decodedScheduleRecord tape.search.selectedCounter
          tape.search.selectedSchedule] := by
    rw [ledgerExact, initialCandidates]
    simp
  let certificate : SelectedQ16LedgerCertificate
      (fixedTapeFutureFreeEnvironment tape) final.current :=
    { priorCandidates :=
        decodedCandidatesOfSpecs (q16TapeOfSearch tape.search).earlier
      selectedCounter := tape.search.selectedCounter
      selectedSchedule := tape.search.selectedSchedule
      priorHistory := priorHistory
      selectedCompact := by
        simpa [fixedTapeFutureFreeEnvironment] using
          tape.search.selectedCompact
      ledgerExact := ledgerExact' }
  exact ⟨steps, pairs, final, certificate, rfl, rfl, trace, supported,
    finalControl, finalSame, fuelExact⟩

theorem terminal_slot_gives_schedule_exhaustion
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (atControl : state.current.control = .linear [.fixed .terminal]) :
    ∃ final,
      MachineQueryPath (rawFutureFreeMicrostep environment raw state) [] final ∧
      PathUsesFixedTable table [] ∧
      FutureFreeScheduleExhausted final.current ∧
      final.current.core = state.current.core ∧
      final.current.q16Candidates = state.current.q16Candidates := by
  let action := VerifierAction.terminal
  let nextSnapshot : FutureFreeSnapshot :=
    { state.current with control := .done }
  let final := appendFutureFreeSnapshot state (.verifier action .none)
    nextSnapshot
  have noSubmission : submitNextRawMessage raw state = none := by
    simp [submitNextRawMessage, atControl]
  have forced : state.current.control.nextVerifierAction? = some action := by
    rw [atControl]
    rfl
  have applied : applyActionWorkErased state.current.core action .none =
      some state.current.core := by rfl
  have updated : afterFutureFreeVerifierReply environment state.current .none
      state.current.core = some nextSnapshot := by
    simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
      atControl, linearOrDone, nextSnapshot]
  have advanced : advanceFutureFreeVerifier environment state .none =
      some final := by
    simpa [final] using
      advance_future_free_verifier_of_components environment state action .none
        state.current.core nextSnapshot forced applied updated
  have actionPath : MachineQueryPath (futureFreeReplyProgram state action) []
      .none := structural_future_free_reply_path state action rfl
  have runner : MachineQueryPath
      (runOneFutureFreeVerifierAction environment state) [] final := by
    unfold runOneFutureFreeVerifierAction
    rw [forced]
    apply machine_query_path_bind_join _ _ [] [] .none final actionPath
    rw [advanced]
    exact .pure final
  have microstep : MachineQueryPath
      (rawFutureFreeMicrostep environment raw state) [] final := by
    simpa [rawFutureFreeMicrostep, noSubmission] using runner
  exact ⟨final, microstep, path_uses_fixed_table_nil table, rfl, rfl, rfl⟩

/-! ## One exact evaluator decomposition -/

/-- All evaluator states used by the complete operational comparison.  This
record is produced by reducing `refineWorkErased`; none of its fields asserts
verifier acceptance or extraction. -/
structure CompleteWorkErasedEvaluatorRun
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace) where
  beforeC1 : EvalState
  withC1Salt : EvalState
  afterC1 : EvalState
  afterLambda : EvalState
  afterPhaseChallenges : EvalState
  withC2Salt : EvalState
  afterC2 : EvalState
  prefixState : EvalState
  afterQ16 : EvalState
  finalState : EvalState
  c1Salt : Digest256
  c2Salt : Digest256
  beforeC1Run : runMachineEventsWorkErased table
      (prefixBeforeC1 tape.messages) initialEvalState = some beforeC1
  c1SaltRun : rootSaltStep table beforeC1 tape.messages.context c1TreeTag =
      some (c1Salt, withC1Salt)
  c1AbsorbRun : absorbStep table withC1Salt
      (.c1Root tape.messages.c1Root c1Salt) = some afterC1
  lambdaRun : runMachineEventWorkErased table afterC1
      (challengeEvent tape.messages .lambda) = some afterLambda
  chiRun : runMachineEventWorkErased table afterLambda
      (challengeEvent tape.messages .chi) = some afterPhaseChallenges
  c2SaltRun : rootSaltStep table afterPhaseChallenges tape.messages.context
      c2TreeTag = some (c2Salt, withC2Salt)
  c2AbsorbRun : absorbStep table withC2Salt
      (.c2Root tape.messages.c2.root c2Salt) = some afterC2
  beforeQ16Run : runMachineEventsWorkErased table
      (prefixAfterC2 tape.messages) afterC2 = some prefixState
  q16Run : runQ16 table prefixState (q16TapeOfSearch tape.search) =
      some afterQ16
  afterQ16Run : runMachineEventsWorkErased table
      (afterAcceptedQueryScan tape.messages) afterQ16 = some finalState
  rawTraceEq :
      { initialDigest := initialEvalState.digest
        q16BaseDigest := prefixState.digest
        selectedCounter := tape.search.selectedCounter
        finalDigest := finalState.digest
        circlePoints := tape.circlePoints
        calls := finalState.calls
        samples := finalState.samples
        candidates := finalState.candidates } = rawTrace

theorem refine_work_erased_exposes_complete_evaluator_run
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace)
    (run : refineWorkErased table tape = some rawTrace) :
    Nonempty (CompleteWorkErasedEvaluatorRun table tape rawTrace) := by
  rw [refineWorkErased] at run
  obtain ⟨prefixState, prefixRun, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨afterQ16, q16Run, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨finalState, afterQ16Run, rawRun⟩ :=
    Option.bind_eq_some_iff.mp run
  rw [runPrefixWorkErased] at prefixRun
  obtain ⟨beforeC1, beforeC1Run, prefixRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  obtain ⟨c1Pair, c1SaltRun, prefixRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  rcases c1Pair with ⟨c1Salt, withC1Salt⟩
  obtain ⟨afterC1, c1AbsorbRun, prefixRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  obtain ⟨afterPhaseChallenges, phaseRun, prefixRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  obtain ⟨c2Pair, c2SaltRun, prefixRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  rcases c2Pair with ⟨c2Salt, withC2Salt⟩
  obtain ⟨afterC2, c2AbsorbRun, beforeQ16Run⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  rw [runMachineEventsWorkErased] at phaseRun
  obtain ⟨afterLambda, lambdaRun, phaseRun⟩ :=
    Option.bind_eq_some_iff.mp phaseRun
  rw [runMachineEventsWorkErased] at phaseRun
  obtain ⟨afterChi, chiRun, phaseRun⟩ :=
    Option.bind_eq_some_iff.mp phaseRun
  have afterChiEq : afterChi = afterPhaseChallenges := by
    simpa [runMachineEventsWorkErased] using Option.some.inj phaseRun
  subst afterChi
  have rawTraceEq :
      { initialDigest := initialEvalState.digest
        q16BaseDigest := prefixState.digest
        selectedCounter := tape.search.selectedCounter
        finalDigest := finalState.digest
        circlePoints := tape.circlePoints
        calls := finalState.calls
        samples := finalState.samples
        candidates := finalState.candidates } = rawTrace :=
    Option.some.inj rawRun
  exact ⟨⟨beforeC1, withC1Salt, afterC1, afterLambda,
    afterPhaseChallenges, withC2Salt, afterC2, prefixState, afterQ16,
    finalState, c1Salt, c2Salt, beforeC1Run, c1SaltRun, c1AbsorbRun,
    lambdaRun, chiRun, c2SaltRun, c2AbsorbRun, beforeQ16Run, q16Run,
    afterQ16Run, rawTraceEq⟩⟩

theorem complete_evaluator_final_samples_decode
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace)
    (wellFormed : TraceWellFormed table exactDeterministicDecoders tape
      rawTrace)
    (run : CompleteWorkErasedEvaluatorRun table tape rawTrace) :
    StateSamplesDecodeAs tape.messages run.finalState := by
  intro record member
  apply wellFormed.challengesDecode record
  have samplesEq : run.finalState.samples = rawTrace.samples := by
    simpa using congrArg InteractiveRawTrace.samples run.rawTraceEq
  rw [← samplesEq]
  exact member

theorem complete_evaluator_final_candidates_decode
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace)
    (wellFormed : TraceWellFormed table exactDeterministicDecoders tape
      rawTrace)
    (run : CompleteWorkErasedEvaluatorRun table tape rawTrace) :
    StateCandidatesDecodeAs run.finalState := by
  intro record member
  apply wellFormed.candidatesDecode record
  have candidatesEq : run.finalState.candidates = rawTrace.candidates := by
    simpa using congrArg InteractiveRawTrace.candidates run.rawTraceEq
  rw [← candidatesEq]
  exact member

theorem samples_included_trans {first middle final : EvalState}
    (left : SamplesIncluded first middle)
    (right : SamplesIncluded middle final) :
    SamplesIncluded first final := by
  intro record member
  exact right record (left record member)

theorem candidates_included_trans {first middle final : EvalState}
    (left : CandidatesIncluded first middle)
    (right : CandidatesIncluded middle final) :
    CandidatesIncluded first final := by
  intro record member
  exact right record (left record member)

/-! ## Exact public-prefix length for the canonical construction -/

/-- The fixed-prefix replay has one driver microstep per verifier action.
This strengthens the earlier existential-step interface without changing its
callers. -/
theorem fixed_prefix_table_trace_gives_exact_step_count
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (bindings : FixedBindings)
    (core : RuntimeCore) (actions : List VerifierAction)
    (state : FutureFreeVerifierState)
    (trace : TableExecutionTrace table bindings core actions)
    (control : state.current.control =
      .adaptive (fixedPrefixBoundaryControl actions))
    (stateBindings : state.current.bindings = bindings)
    (stateCore : state.current.core = core) :
    ∃ pairs final,
      NonterminalRawDriverTrace environment raw state actions.length pairs final ∧
      PathUsesFixedTable table pairs ∧
      final.current.control = .adaptive .awaitingC1 ∧
      final.current.bindings = bindings ∧
      final.current.core = tableExecutionLastCore trace ∧
      final.current.q16Candidates = state.current.q16Candidates := by
  induction trace generalizing state with
  | done core =>
      refine ⟨[], state, .stop state, path_uses_fixed_table_nil table,
        ?_, stateBindings, ?_, rfl⟩
      · simpa using control
      · simpa [tableExecutionLastCore] using stateCore
  | @step core next action rest reply derived applied tail ih =>
      have controlHead : state.current.control =
          .adaptive (.fixedPrefix (action :: rest)) := by
        simpa using control
      have noSubmission : submitNextRawMessage raw state = none := by
        simp [submitNextRawMessage, controlHead]
      have forced : state.current.control.nextVerifierAction? = some action := by
        rw [controlHead]
        rfl
      have derivedState : deriveReply table state.current.bindings
          state.current.core action = some reply := by
        simpa [stateBindings, stateCore] using derived
      let nextSnapshot : FutureFreeSnapshot :=
        { state.current with
          control := .adaptive (fixedPrefixBoundaryControl rest)
          core := next }
      let nextState : FutureFreeVerifierState :=
        appendFutureFreeSnapshot state (.verifier action reply) nextSnapshot
      have advanced : advanceFutureFreeVerifier environment state reply =
          some nextState := by
        have appliedState : applyActionWorkErased state.current.core action reply =
            some next := by
          simpa [stateCore] using applied
        have updated : afterFutureFreeVerifierReply environment state.current
            reply next = some nextSnapshot := by
          cases rest <;>
            simp [afterFutureFreeVerifierReply,
              rawAfterFutureFreeVerifierReply, controlHead,
              OpenAdaptiveControl.afterVerifierReply,
              finishFixedPrefixControl, fixedPrefixBoundaryControl,
              nextSnapshot]
        simpa [nextState] using
          advance_future_free_verifier_of_components environment state action
            reply next nextSnapshot forced appliedState updated
      obtain ⟨headPairs, headPath, headSupported⟩ :=
        fixed_table_action_is_raw_future_free_microstep table environment raw
          state nextState action reply noSubmission forced derivedState advanced
      have nextControl : nextState.current.control =
          .adaptive (fixedPrefixBoundaryControl rest) := by
        rfl
      have nextBindings : nextState.current.bindings = bindings := by
        simpa [nextState, nextSnapshot, appendFutureFreeSnapshot,
          stateBindings]
      have nextCore : nextState.current.core = next := by rfl
      obtain ⟨tailPairs, final, tailTrace, tailSupported, finalControl,
          finalBindings, finalCore, finalCandidates⟩ :=
        ih nextState nextControl nextBindings nextCore
      have nextNonterminal : isDriverHalt nextState.current.control = false := by
        rw [nextControl]
        cases rest <;> rfl
      refine ⟨headPairs ++ tailPairs, final, ?_,
        path_uses_fixed_table_append table headPairs tailPairs headSupported
          tailSupported,
        finalControl, finalBindings, ?_, ?_⟩
      · simpa using
          (NonterminalRawDriverTrace.next headPath nextNonterminal tailTrace)
      · simpa [tableExecutionLastCore] using finalCore
      · rw [finalCandidates]
        rfl

/-- The literal deployed pre-C1 schedule contains exactly six actions. -/
theorem prefix_before_c1_run_gives_exact_six_step_trace
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (beforeC1 : EvalState)
    (run : runMachineEventsWorkErased table
      (prefixBeforeC1 tape.messages) initialEvalState = some beforeC1) :
    ∃ pairs final,
      NonterminalRawDriverTrace (fixedTapeFutureFreeEnvironment tape)
        (fixedTapeRawMessages tape)
        (initialFutureFreeVerifierState
          (FixedBindings.ofContext tape.messages.context))
        6 pairs final ∧
      PathUsesFixedTable table pairs ∧
      final.current.control = .adaptive .awaitingC1 ∧
      SameDigest final.current.core beforeC1 ∧
      final.current.core.c1Salt = none ∧
      final.current.core.c2Salt = none ∧
      final.current.core.q16Base = none ∧
      final.current.q16Candidates = [] := by
  let bindings := FixedBindings.ofContext tape.messages.context
  obtain ⟨beforeCore, actionRun, same, c1Salt, c2Salt, q16Base⟩ :=
    machine_events_actions_agree table bindings
      (prefixBeforeC1 tape.messages) initialCore initialEvalState beforeC1 rfl
      run
  obtain ⟨tableTrace, lastCore⟩ :=
    table_execution_trace_with_exact_last_of_run table bindings
      (eventsToActions (prefixBeforeC1 tape.messages)) initialCore beforeCore
      actionRun
  let initial := initialFutureFreeVerifierState bindings
  have initialControl : initial.current.control =
      .adaptive
        (fixedPrefixBoundaryControl
          (eventsToActions (prefixBeforeC1 tape.messages))) := by
    simp [initial, bindings, initialFutureFreeVerifierState,
      initialFutureFreeSnapshot, fixed_bindings_recover_context,
      fixedPrefixBoundaryControl, openFixedPrefixActions, prefixBeforeC1,
      eventsToActions, eventActions] <;> rfl
  obtain ⟨pairs, final, trace, supported, finalControl, _finalBindings,
      finalCore, finalCandidates⟩ :=
    fixed_prefix_table_trace_gives_exact_step_count table
      (fixedTapeFutureFreeEnvironment tape) (fixedTapeRawMessages tape)
      bindings initialCore (eventsToActions (prefixBeforeC1 tape.messages))
      initial tableTrace initialControl rfl rfl
  have exactTrace : NonterminalRawDriverTrace
      (fixedTapeFutureFreeEnvironment tape) (fixedTapeRawMessages tape)
      initial 6 pairs final := by
    simpa [prefixBeforeC1, eventsToActions, eventActions] using trace
  refine ⟨pairs, final, exactTrace, supported, finalControl, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [finalCore, lastCore]
    exact same
  · rw [finalCore, lastCore]
    exact c1Salt.trans rfl
  · rw [finalCore, lastCore]
    exact c2Salt.trans rfl
  · rw [finalCore, lastCore]
    exact q16Base.trans rfl
  · simpa [initial, initialFutureFreeVerifierState,
      initialFutureFreeSnapshot] using finalCandidates

/-! ## The final result type keeps acceptance outside the compiler bridge -/

structure CompleteCheckedFutureFreePath
    (table : FixedOracleTable) (tape : DeployedFixedTape) where
  fuel : Nat
  pairs : List (ShaInput × ShaOutput)
  final : FutureFreeVerifierState
  path : MachineQueryPath
    (initialRawFutureFreeProgram (fixedTapeFutureFreeEnvironment tape)
      (fixedTapeRawMessages tape) fuel) pairs final
  tableBacked : PathUsesFixedTable table pairs
  exhausted : FutureFreeScheduleExhausted final.current
  invariant : FutureFreeRunInvariant
    (FixedBindings.ofContext tape.messages.context) final
  externalObligations : List FutureFreeExternalAcceptanceObligation
  externalObligationsExact : externalObligations =
    futureFreeExternalAcceptanceObligations

/-- The unpadded construction returned by the checked refinement, together
with the exact protocol-local decomposition of its driver fuel.  This record
does not assert any semantic, Merkle, or terminal acceptance predicate. -/
structure CanonicalCheckedFutureFreeConstruction
    (table : FixedOracleTable) (tape : DeployedFixedTape) where
  complete : CompleteCheckedFutureFreePath table tape
  selectedQ16 : SelectedQ16LedgerCertificate
    (fixedTapeFutureFreeEnvironment tape) complete.final.current
  selectedQ16CounterExact :
    selectedQ16.selectedCounter = tape.search.selectedCounter
  selectedQ16ScheduleExact :
    selectedQ16.selectedSchedule = tape.search.selectedSchedule
  adaptiveSteps : Nat
  beforeQ16Steps : Nat
  q16Steps : Nat
  afterQ16Steps : Nat
  completeFuel : complete.fuel =
    ((((6 + adaptiveSteps) + beforeQ16Steps) + q16Steps) + afterQ16Steps) + 1
  adaptiveFuel : adaptiveSteps = 6 +
    (tape.messages.challengeUse .lambda).blocksUsed +
    (tape.messages.challengeUse .chi).blocksUsed
  beforeQ16Fuel : beforeQ16Steps =
    fixedTapeLinearFuels tape beforeQ16Slots
  q16Fuel : q16Steps = 2 +
    discardedQ16Fuel (q16TapeOfSearch tape.search).earlier +
    (1 + (q16TapeOfSearch tape.search).selected.outcome.blocksUsed)
  afterQ16Fuel : afterQ16Steps =
    fixedTapeLinearFuels tape afterQ16PreterminalSlots

/-- A successful work-erased checked refinement drives the complete
future-free verifier to schedule exhaustion.  This is the deterministic
compiler-refinement face: the five semantic/authentication obligations remain
data named by `externalObligations` and are not asserted here. -/
theorem checked_work_erased_refinement_constructs_canonical_future_free_path
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace)
    (run : checkedRefineWorkErased table exactDeterministicDecoders tape =
      some rawTrace) :
    Nonempty (CanonicalCheckedFutureFreeConstruction table tape) := by
  let environment := fixedTapeFutureFreeEnvironment tape
  let raw := fixedTapeRawMessages tape
  let bindings := FixedBindings.ofContext tape.messages.context
  have wellFormed : TraceWellFormed table exactDeterministicDecoders tape
      rawTrace :=
    checked_work_erased_refinement_is_well_formed table tape rawTrace run
  have erasedRun : refineWorkErased table tape = some rawTrace :=
    checked_refine_work_erased_forgets_check table exactDeterministicDecoders
      tape rawTrace run
  obtain ⟨evaluator⟩ :=
    refine_work_erased_exposes_complete_evaluator_run table tape rawTrace
      erasedRun

  have finalSamples : StateSamplesDecodeAs tape.messages
      evaluator.finalState :=
    complete_evaluator_final_samples_decode table tape rawTrace wellFormed
      evaluator
  have finalCandidates : StateCandidatesDecodeAs evaluator.finalState :=
    complete_evaluator_final_candidates_decode table tape rawTrace wellFormed
      evaluator
  have suffixSamples : SamplesIncluded evaluator.afterQ16
      evaluator.finalState :=
    machine_events_work_erased_samples_included table
      (afterAcceptedQueryScan tape.messages) evaluator.afterQ16
      evaluator.finalState evaluator.afterQ16Run
  have suffixCandidates : CandidatesIncluded evaluator.afterQ16
      evaluator.finalState :=
    machine_events_work_erased_candidates_included table
      (afterAcceptedQueryScan tape.messages) evaluator.afterQ16
      evaluator.finalState evaluator.afterQ16Run
  have q16Samples : SamplesIncluded evaluator.prefixState
      evaluator.afterQ16 :=
    run_q16_preserves_prior_samples table evaluator.prefixState
      evaluator.afterQ16 (q16TapeOfSearch tape.search) evaluator.q16Run
  have prefixSamples : SamplesIncluded evaluator.afterC2
      evaluator.prefixState :=
    machine_events_work_erased_samples_included table
      (prefixAfterC2 tape.messages) evaluator.afterC2 evaluator.prefixState
      evaluator.beforeQ16Run
  have c2AbsorbPreserved :=
    absorb_step_preserves_samples_and_candidates table evaluator.withC2Salt
      evaluator.afterC2
      (.c2Root tape.messages.c2.root evaluator.c2Salt)
      evaluator.c2AbsorbRun
  have c2SaltPreserved :=
    root_salt_step_preserves_samples_and_candidates table
      evaluator.afterPhaseChallenges evaluator.withC2Salt
      tape.messages.context c2TreeTag evaluator.c2Salt evaluator.c2SaltRun
  have phaseToC2 : SamplesIncluded evaluator.afterPhaseChallenges
      evaluator.afterC2 := by
    intro record member
    rw [c2AbsorbPreserved.1, c2SaltPreserved.1]
    exact member
  have prefixToFinal : SamplesIncluded evaluator.prefixState
      evaluator.finalState :=
    samples_included_trans q16Samples suffixSamples
  have phaseToFinal : SamplesIncluded evaluator.afterPhaseChallenges
      evaluator.finalState :=
    samples_included_trans phaseToC2
      (samples_included_trans prefixSamples prefixToFinal)
  have phaseDecoded : StateSamplesDecodeAs tape.messages
      evaluator.afterPhaseChallenges :=
    state_samples_decode_of_included tape.messages
      evaluator.afterPhaseChallenges evaluator.finalState phaseToFinal
      finalSamples
  have prefixDecoded : StateSamplesDecodeAs tape.messages
      evaluator.prefixState :=
    state_samples_decode_of_included tape.messages evaluator.prefixState
      evaluator.finalState prefixToFinal finalSamples
  have afterQ16Decoded : StateCandidatesDecodeAs evaluator.afterQ16 :=
    state_candidates_decode_of_included evaluator.afterQ16 evaluator.finalState
      suffixCandidates finalCandidates
  have secureAll : EveryChallengeSecure environment tape.messages := by
    simpa [environment] using
      well_formed_trace_gives_every_challenge_secure table tape rawTrace
        wellFormed

  obtain ⟨prefixPairs, c1State, prefixTrace, prefixTable,
      c1Control, c1Same, _c1SaltEmpty, _c2SaltEmpty, _q16BaseEmpty,
      c1CandidatesEmpty⟩ :=
    prefix_before_c1_run_gives_exact_six_step_trace table tape
      evaluator.beforeC1 evaluator.beforeC1Run
  have c1Fixed : FutureFreeBindingsFixed bindings c1State := by
    apply nonterminal_trace_preserves_fixed_bindings bindings environment raw
      (initialFutureFreeVerifierState bindings) c1State 6 prefixPairs
    · exact initial_future_free_bindings_are_fixed bindings
    · simpa [environment, raw, bindings] using prefixTrace

  obtain ⟨adaptiveSteps, adaptivePairs, afterC2State, adaptiveTrace,
      adaptiveTable, adaptiveControl, adaptiveSame, adaptiveCandidates,
      adaptiveFuel⟩ :=
    adaptive_c1_through_c2_run_gives_future_free_trace table tape c1State
      evaluator.beforeC1 evaluator.withC1Salt evaluator.afterC1
      evaluator.afterLambda evaluator.afterPhaseChallenges
      evaluator.withC2Salt evaluator.afterC2 evaluator.c1Salt evaluator.c2Salt
      c1Control c1Fixed c1Same evaluator.c1SaltRun evaluator.c1AbsorbRun
      evaluator.lambdaRun evaluator.chiRun phaseDecoded evaluator.c2SaltRun
      evaluator.c2AbsorbRun
  have beforeControl : afterC2State.current.control =
      .linear (beforeQ16Slots ++ (.beginQ16 :: afterQ16Slots)) := by
    simpa [fullFutureFreeSlots, List.append_assoc] using adaptiveControl
  have beforeRun : runMachineEventsWorkErased table
      (fixedTapeLinearEvents tape beforeQ16Slots) evaluator.afterC2 =
        some evaluator.prefixState := by
    rw [fixed_tape_before_q16_events_are_exact_prefix_after_c2]
    exact evaluator.beforeQ16Run
  obtain ⟨beforeSteps, beforePairs, q16State, beforeTrace, beforeTable,
      q16Control, q16Same, beforeCandidates, beforeFuel⟩ :=
    fixed_tape_linear_region_gives_future_free_trace table tape rawTrace
      wellFormed afterC2State evaluator.afterC2 evaluator.prefixState
      beforeQ16Slots (.beginQ16 :: afterQ16Slots) beforeControl adaptiveSame
      beforeRun prefixDecoded secureAll before_q16_slots_are_supported
      (by simp)

  have q16CandidatesEmpty : q16State.current.q16Candidates = [] :=
    beforeCandidates.trans (adaptiveCandidates.trans c1CandidatesEmpty)

  have q16Plan := exact_discarded_q16_plan_of_first_cap_search tape
  obtain ⟨q16Steps, q16Pairs, afterQ16State, q16Certificate,
      q16CounterExact, q16ScheduleExact, q16Trace, q16Table,
      afterQ16Control, q16SameFinal, q16Fuel⟩ :=
    accepting_q16_run_gives_selected_ledger_certificate table tape rawTrace
      q16State evaluator.prefixState evaluator.afterQ16 afterQ16Slots
      q16Control q16CandidatesEmpty q16Same evaluator.q16Run q16Plan
      afterQ16Decoded (by decide)
  have afterControl : afterQ16State.current.control =
      .linear (afterQ16PreterminalSlots ++ [.fixed .terminal]) := by
    rw [← after_q16_slots_split_terminal]
    exact afterQ16Control
  have afterRun : runMachineEventsWorkErased table
      (fixedTapeLinearEvents tape afterQ16PreterminalSlots)
      evaluator.afterQ16 = some evaluator.finalState := by
    rw [fixed_tape_after_q16_events_are_exact_accepted_suffix]
    exact evaluator.afterQ16Run
  obtain ⟨afterSteps, afterPairs, beforeTerminal, afterTrace, afterTable,
      terminalControl, terminalSame, afterCandidates, afterFuel⟩ :=
    fixed_tape_linear_region_gives_future_free_trace table tape rawTrace
      wellFormed afterQ16State evaluator.afterQ16 evaluator.finalState
      afterQ16PreterminalSlots [.fixed .terminal] afterControl q16SameFinal
      afterRun finalSamples secureAll
      after_q16_preterminal_slots_are_supported (by simp)
  obtain ⟨final, terminalPath, terminalTable, exhausted, _terminalCore,
      terminalCandidates⟩ :=
    terminal_slot_gives_schedule_exhaustion table environment raw beforeTerminal
      (by simpa [environment, raw] using terminalControl)
  let finalQ16Certificate : SelectedQ16LedgerCertificate environment
      final.current :=
    q16Certificate.transport
      (terminalCandidates.trans afterCandidates)

  have prefixAdaptive := nonterminal_raw_driver_trace_append environment raw
    (initialFutureFreeVerifierState bindings) c1State afterC2State 6
    adaptiveSteps prefixPairs adaptivePairs
    (by simpa [environment, raw, bindings] using prefixTrace)
    (by simpa [environment, raw] using adaptiveTrace)
  have throughBefore := nonterminal_raw_driver_trace_append environment raw
    (initialFutureFreeVerifierState bindings) afterC2State q16State
    (6 + adaptiveSteps) beforeSteps
    (prefixPairs ++ adaptivePairs) beforePairs prefixAdaptive
    (by simpa [environment, raw] using beforeTrace)
  have throughQ16 := nonterminal_raw_driver_trace_append environment raw
    (initialFutureFreeVerifierState bindings) q16State afterQ16State
    ((6 + adaptiveSteps) + beforeSteps) q16Steps
    ((prefixPairs ++ adaptivePairs) ++ beforePairs) q16Pairs throughBefore
    (by simpa [environment, raw] using q16Trace)
  have throughAfter := nonterminal_raw_driver_trace_append environment raw
    (initialFutureFreeVerifierState bindings) afterQ16State beforeTerminal
    (((6 + adaptiveSteps) + beforeSteps) + q16Steps) afterSteps
    (((prefixPairs ++ adaptivePairs) ++ beforePairs) ++ q16Pairs) afterPairs
    throughQ16 (by simpa [environment, raw] using afterTrace)
  let nonterminalSteps :=
    (((6 + adaptiveSteps) + beforeSteps) + q16Steps) + afterSteps
  let nonterminalPairs :=
    (((prefixPairs ++ adaptivePairs) ++ beforePairs) ++ q16Pairs) ++
      afterPairs
  have throughAfter' : NonterminalRawDriverTrace environment raw
      (initialFutureFreeVerifierState bindings) nonterminalSteps
      nonterminalPairs beforeTerminal := by
    simpa [nonterminalSteps, nonterminalPairs] using throughAfter
  have finalHalt : isDriverHalt final.current.control = true := by
    change final.current.control = .done at exhausted
    rw [exhausted]
    rfl
  have driven : MachineQueryPath
      (driveRawFutureFree environment raw (nonterminalSteps + 1)
        (initialFutureFreeVerifierState bindings))
      (nonterminalPairs ++ []) final :=
    nonterminal_trace_then_terminal_step_has_machine_path environment raw
      (initialFutureFreeVerifierState bindings) beforeTerminal final
      nonterminalSteps nonterminalPairs [] throughAfter'
      (by simpa [environment, raw] using terminalPath) finalHalt
  have fullPath : MachineQueryPath
      (initialRawFutureFreeProgram environment raw (nonterminalSteps + 1))
      nonterminalPairs final := by
    have bindingsRaw : bindings = FixedBindings.ofContext raw.context := by
      rfl
    rw [bindingsRaw] at driven
    simpa [initialRawFutureFreeProgram] using driven
  have allTable : PathUsesFixedTable table nonterminalPairs := by
    exact path_uses_fixed_table_append table
      (((prefixPairs ++ adaptivePairs) ++ beforePairs) ++ q16Pairs)
      afterPairs
      (path_uses_fixed_table_append table
        ((prefixPairs ++ adaptivePairs) ++ beforePairs) q16Pairs
        (path_uses_fixed_table_append table (prefixPairs ++ adaptivePairs)
          beforePairs
          (path_uses_fixed_table_append table prefixPairs adaptivePairs
            prefixTable adaptiveTable) beforeTable) q16Table) afterTable
  have invariant : FutureFreeRunInvariant bindings final := by
    simpa [environment, raw, bindings] using
      initial_raw_future_free_return_has_exact_run_invariant environment raw
        (nonterminalSteps + 1) nonterminalPairs final fullPath
  let complete : CompleteCheckedFutureFreePath table tape :=
    { fuel := nonterminalSteps + 1
      pairs := nonterminalPairs
      final := final
      path := by simpa [environment, raw] using fullPath
      tableBacked := allTable
      exhausted := exhausted
      invariant := by simpa [bindings] using invariant
      externalObligations := futureFreeExternalAcceptanceObligations
      externalObligationsExact := rfl }
  have completeFuel : complete.fuel =
      ((((6 + adaptiveSteps) + beforeSteps) + q16Steps) + afterSteps) + 1 := by
    rfl
  exact ⟨
    { complete := complete
      selectedQ16 := by
        simpa [environment] using finalQ16Certificate
      selectedQ16CounterExact := by
        simpa [environment, finalQ16Certificate,
          SelectedQ16LedgerCertificate.transport] using q16CounterExact
      selectedQ16ScheduleExact := by
        simpa [environment, finalQ16Certificate,
          SelectedQ16LedgerCertificate.transport] using q16ScheduleExact
      adaptiveSteps := adaptiveSteps
      beforeQ16Steps := beforeSteps
      q16Steps := q16Steps
      afterQ16Steps := afterSteps
      completeFuel := completeFuel
      adaptiveFuel := adaptiveFuel
      beforeQ16Fuel := beforeFuel
      q16Fuel := q16Fuel
      afterQ16Fuel := afterFuel }⟩

/-- Compatibility projection retaining the original public theorem surface. -/
theorem checked_work_erased_refinement_constructs_complete_future_free_path
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace)
    (run : checkedRefineWorkErased table exactDeterministicDecoders tape =
      some rawTrace) :
    Nonempty (CompleteCheckedFutureFreePath table tape) := by
  obtain ⟨construction⟩ :=
    checked_work_erased_refinement_constructs_canonical_future_free_path
      table tape rawTrace run
  exact ⟨construction.complete⟩

/-- A strict deployed checked refinement supplies exactly the selected-work
and exploratory-probe provenance needed by the preceding work-erased
operational theorem.  No work success probability is divided by grinding
effort; strict success is merely mapped monotonically to the erased verifier. -/
theorem strict_checked_refinement_constructs_complete_future_free_path
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace)
    (run : checkedRefine table exactDeterministicDecoders tape =
      some rawTrace) :
    Nonempty (CompleteCheckedFutureFreePath table tape) := by
  exact checked_work_erased_refinement_constructs_complete_future_free_path
    table tape rawTrace
      (checked_refinement_success_survives_work_erasure table
        exactDeterministicDecoders tape rawTrace run)

#print axioms refine_work_erased_exposes_complete_evaluator_run
#print axioms discarded_q16_plan_gives_future_free_trace
#print axioms discarded_q16_plan_advances_prior_history
#print axioms accepting_q16_run_gives_selected_ledger_certificate
#print axioms checked_work_erased_refinement_constructs_canonical_future_free_path
#print axioms checked_work_erased_refinement_constructs_complete_future_free_path
#print axioms strict_checked_refinement_constructs_complete_future_free_path

end

end AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
