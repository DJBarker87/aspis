import AspisFormal.K1.V7FsAokExperiment

/-!
# Obstruction to history/input-only persistent role selection

An arbitrary `OracleMachine` continuation may decide, after seeing a fresh
oracle answer, whether the query belongs to the eventually retained verifier
path or to an erased grinding path.  Consequently, the pre-answer oracle
history and query input do not generically determine that eventual role.

This file gives a small executable counterexample.  Both runs start from the
same empty oracle, issue the same query, and use the same continuation.  They
differ only in the fresh answer supplied by the controller.  The continuation
returns different eventual dispositions.  Thus no function of only the
pre-answer history and input can classify both runs exactly.

The result is a semantic-model boundary, not a statement about the deployed
Tag-73 scheduler and not a probability claim.  A positive persistent-role
construction must use additional pre-answer scheduler structure that rules out
this answer-dependent choice; it cannot follow for arbitrary
`OracleMachine` continuations.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73PersistentRoleSelectionObstruction

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7FsAokExperiment

/-- The two dispositions relevant to the minimal counterexample.  These are
semantic labels for the witness, not new protocol states. -/
inductive EventualQueryDisposition where
  | selectedVerifierUse
  | erasedGrindingProbe
  deriving DecidableEq, Repr

/-- A concrete fresh answer used by the selected branch. -/
def selectedAnswer : ShaOutput := zeroBytes 32

/-- A concrete different fresh answer used by the erased branch. -/
def erasedAnswer : ShaOutput := fun index =>
  if index = (0 : Fin 32) then 1 else 0

theorem selected_answer_ne_erased_answer :
    selectedAnswer ≠ erasedAnswer := by
  intro equal
  have atZero := congrFun equal (0 : Fin 32)
  simp [selectedAnswer, erasedAnswer, zeroBytes] at atZero

/-- The eventual disposition chosen by the continuation after the answer is
known. -/
def dispositionAfterAnswer (answer : ShaOutput) :
    EventualQueryDisposition :=
  if answer = selectedAnswer then
    .selectedVerifierUse
  else
    .erasedGrindingProbe

@[simp] theorem disposition_after_selected_answer :
    dispositionAfterAnswer selectedAnswer =
      .selectedVerifierUse := by
  simp [dispositionAfterAnswer]

@[simp] theorem disposition_after_erased_answer :
    dispositionAfterAnswer erasedAnswer =
      .erasedGrindingProbe := by
  simp [dispositionAfterAnswer, selected_answer_ne_erased_answer.symm]

/-- One query whose continuation assigns its eventual role only after reading
the answer.  The query node itself is identical in both counterexample runs. -/
def answerDependentRoleMachine (input : ShaInput) :
    OracleMachine EventualQueryDisposition :=
  .query input fun answer => .pure (dispositionAfterAnswer answer)

/-- A deterministic controller that supplies one fixed fresh answer. -/
def constantAnswerController (answer : ShaOutput) : AdaptiveController :=
  fun _history _input => .answer answer

/-- Exact one-query budgets for the executable witness. -/
def oneFreshQueryLimits : OracleLimits where
  totalCalls := 1
  freshCalls := 1
  programmedPoints := 0

/-- The selected-answer execution returns the selected disposition. -/
theorem selected_answer_run_returns_selected (input : ShaInput) :
    (runMachine (constantAnswerController selectedAnswer)
      oneFreshQueryLimits .adversary 1 emptyOracle
      (answerDependentRoleMachine input)).halt =
        .returned .selectedVerifierUse := by
  simp [runMachine, answerDependentRoleMachine, queryOracle,
    constantAnswerController, oneFreshQueryLimits, emptyOracle, lookupEntry]

/-- The different-answer execution returns the erased disposition. -/
theorem erased_answer_run_returns_erased (input : ShaInput) :
    (runMachine (constantAnswerController erasedAnswer)
      oneFreshQueryLimits .adversary 1 emptyOracle
      (answerDependentRoleMachine input)).halt =
        .returned .erasedGrindingProbe := by
  simp [runMachine, answerDependentRoleMachine, queryOracle,
    constantAnswerController, oneFreshQueryLimits, emptyOracle, lookupEntry]

/-- A classifier restricted to the information available in the requirement:
the pre-answer raw history and the currently fixed query input. -/
abbrev HistoryInputRoleDecider :=
  List QueryRecord → ShaInput → EventualQueryDisposition

/-- Exact classification of the witness continuation for one possible answer.
The answer is deliberately absent from the decider's arguments. -/
def ClassifiesAnswerExactly (decider : HistoryInputRoleDecider)
    (history : List QueryRecord) (input : ShaInput) (answer : ShaOutput) :
    Prop :=
  decider history input = dispositionAfterAnswer answer

/-- No history/input-only pre-answer decider can exactly classify both
possible executions of the same query node. -/
theorem no_history_input_decider_classifies_both_answers
    (decider : HistoryInputRoleDecider)
    (history : List QueryRecord) (input : ShaInput) :
    ¬ (ClassifiesAnswerExactly decider history input selectedAnswer ∧
       ClassifiesAnswerExactly decider history input erasedAnswer) := by
  rintro ⟨selectedExact, erasedExact⟩
  simp only [ClassifiesAnswerExactly, disposition_after_selected_answer]
    at selectedExact
  simp only [ClassifiesAnswerExactly, disposition_after_erased_answer]
    at erasedExact
  have impossible : EventualQueryDisposition.selectedVerifierUse =
      EventualQueryDisposition.erasedGrindingProbe :=
    selectedExact.symm.trans erasedExact
  contradiction

/-- Combined operational form of the obstruction.  It records both exact
runs and the failure of every history/input-only classifier. -/
theorem same_preanswer_query_has_distinct_eventual_dispositions
    (decider : HistoryInputRoleDecider) (input : ShaInput) :
    (runMachine (constantAnswerController selectedAnswer)
      oneFreshQueryLimits .adversary 1 emptyOracle
      (answerDependentRoleMachine input)).halt =
        .returned .selectedVerifierUse ∧
    (runMachine (constantAnswerController erasedAnswer)
      oneFreshQueryLimits .adversary 1 emptyOracle
      (answerDependentRoleMachine input)).halt =
        .returned .erasedGrindingProbe ∧
    ¬ (ClassifiesAnswerExactly decider emptyOracle.history input selectedAnswer ∧
       ClassifiesAnswerExactly decider emptyOracle.history input erasedAnswer) := by
  exact ⟨selected_answer_run_returns_selected input,
    erased_answer_run_returns_erased input,
    no_history_input_decider_classifies_both_answers decider
      emptyOracle.history input⟩

#print axioms selected_answer_ne_erased_answer
#print axioms selected_answer_run_returns_selected
#print axioms erased_answer_run_returns_erased
#print axioms no_history_input_decider_classifies_both_answers
#print axioms same_preanswer_query_has_distinct_eventual_dispositions

end AspisK1.V7Tag73PersistentRoleSelectionObstruction
