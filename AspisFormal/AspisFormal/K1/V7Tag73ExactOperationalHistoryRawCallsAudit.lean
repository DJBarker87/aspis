import AspisFormal.K1.V7Tag73OperationalSemanticReplay

/-!
# Exact operational verifier-history/raw-call audit

The operational input already stores the alignment of the actual second-phase
verifier with the canonical checked path constructed from the strict fixed
replay.  This file exposes that equality directly and records the precise
remaining comparison with the larger deterministic-refinement call ledger.

The two ledgers are intentionally not identified here.  In particular,
`InteractiveRawTrace.calls` retains the pre-selected grinding probes performed
as adversary history, whereas `RawVerifierExecution.verifierHistory` starts
after that first phase and contains verifier records only.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactOperationalHistoryRawCallsAudit

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73FutureFreeCheckedRefinementBisimulation
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73OperationalSemanticReplay

noncomputable section

/-- The query/answer list of the canonical checked verifier path stored in the
actual operational root certificate. -/
def exactOperationalCanonicalPairs
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : List (ShaInput × ShaOutput) :=
  input.package.root.fixedRoot.base.canonical.construction.complete.pairs

/-- The actual operational verifier history is exactly the canonical checked
path.  This is a source equality already constructed by the root alignment,
not a caller-provided trace premise. -/
theorem exact_operational_verifier_history_eq_canonical_pairs
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    queryAnswerTrace
        input.package.root.fixedRoot.base.projected.execution.verifierHistory =
      exactOperationalCanonicalPairs input := by
  exact input.package.root.fixedRoot.base.actualPathAlignment.verifierHistoryExact

/-- The raw trace's call ledger is exactly the final evaluator call ledger.
This exposes the deterministic-refinement side without asserting that its
adversary-history probes are verifier calls. -/
theorem exact_operational_raw_calls_eq_final_evaluator_calls
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∃ evaluator : CompleteWorkErasedEvaluatorRun (exactOperationalTable input)
        (exactOperationalTape input) (exactOperationalRawTrace input),
      (exactOperationalRawTrace input).calls = evaluator.finalState.calls := by
  obtain ⟨evaluator⟩ :=
    exact_operational_input_constructs_complete_evaluator input
  refine ⟨evaluator, ?_⟩
  simpa using
    (congrArg InteractiveRawTrace.calls evaluator.rawTraceEq).symm

/-- Exact audit boundary: the requested all-raw-calls equality is equivalent
to identifying the canonical verifier path with the complete refinement call
ledger.  Existing operational source alignment discharges the left-hand
history-to-path comparison, but the latter ledger also contains first-phase
grinding probes. -/
theorem exact_operational_verifier_history_eq_raw_calls_iff
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    (queryAnswerTrace
          input.package.root.fixedRoot.base.projected.execution.verifierHistory =
        (exactOperationalRawTrace input).calls.map
          (fun call => (call.input, call.output))) ↔
      exactOperationalCanonicalPairs input =
        (exactOperationalRawTrace input).calls.map
          (fun call => (call.input, call.output)) := by
  rw [exact_operational_verifier_history_eq_canonical_pairs]

/-! ## The concrete grinding-ledger obstruction -/

/-- Every pre-selected grinding probe contributes one literal raw call. -/
theorem run_grinding_probes_calls_length
    (table : FixedOracleTable) (stage : WorkStage)
    (probes : List NonceBytes) (state next : EvalState)
    (run : runGrindingProbes table stage probes state = some next) :
    next.calls.length = state.calls.length + probes.length := by
  induction probes generalizing state with
  | nil =>
      rw [runGrindingProbes] at run
      cases Option.some.inj run
      simp
  | cons nonce rest ih =>
      rw [runGrindingProbes] at run
      obtain ⟨pair, probeRun, restRun⟩ := Option.bind_eq_some_iff.mp run
      rcases pair with ⟨output, afterProbe⟩
      have appended := query_step_appends_one table state afterProbe
        (.grind stage nonce) output probeRun
      rw [ih afterProbe restRun, appended.2.1]
      simp
      omega

/-- The complete work-erased grinding choice contains all pre-selected raw
probes and then the single selected verifier probe. -/
theorem run_grinding_choice_work_erased_calls_length
    (table : FixedOracleTable) (state next : EvalState)
    (stage : WorkStage) (choice : GrindingChoice stage)
    (run : runGrindingChoiceWorkErased table state stage choice = some next) :
    next.calls.length =
      state.calls.length + choice.probesBeforeSelected.length + 1 := by
  rw [runGrindingChoiceWorkErased] at run
  obtain ⟨queried, probesRun, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨selectedPair, selectedRun, result⟩ :=
    Option.bind_eq_some_iff.mp run
  rcases selectedPair with ⟨output, afterSelected⟩
  have afterSelectedExact : afterSelected = next := by
    simpa only [pure, Option.some.injEq] using result
  subst afterSelected
  have probesLength := run_grinding_probes_calls_length table stage
    choice.probesBeforeSelected state queried probesRun
  have selectedAppend := query_step_appends_one table queried next
    (.grind stage choice.selected) output selectedRun
  rw [selectedAppend.2.1, List.length_append, probesLength]
  simp

/-- At the action level the exact causal projection deletes precisely the
pre-selected grinding actions.  Thus the raw and verifier action fragments
coincide exactly when the adversary-history fragment is empty. -/
theorem grinding_actions_eq_future_free_visible_iff
    (stage : WorkStage) (choice : GrindingChoice stage) :
    grindingActions stage choice =
        futureFreeVisibleActions (grindingActions stage choice) ↔
      choice.probesBeforeSelected = [] := by
  rw [grinding_actions_project_to_one_selected_verifier_query]
  constructor
  · intro equal
    cases probesExact : choice.probesBeforeSelected with
    | nil => rfl
    | cons nonce rest =>
        have lengths := congrArg List.length equal
        simp [grindingActions, probesExact] at lengths
  · intro empty
    simp [grindingActions, empty]

#print axioms exact_operational_verifier_history_eq_canonical_pairs
#print axioms exact_operational_raw_calls_eq_final_evaluator_calls
#print axioms exact_operational_verifier_history_eq_raw_calls_iff
#print axioms run_grinding_probes_calls_length
#print axioms run_grinding_choice_work_erased_calls_length
#print axioms grinding_actions_eq_future_free_visible_iff

end

end AspisK1.V7Tag73ExactOperationalHistoryRawCallsAudit
