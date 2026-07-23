import Tag67SixActualStepsCore
import AspisFormal.V5NonceWorkAuthentication

namespace AspisTag67SixActualSteps

open AspisTag67GeneratedSixSteps
open AspisV5NonceWorkAuthentication
open AspisFormal.V5ExactRuntimeWireRepair

/-- The six booleans computed by the actual grinding calls, in deployed
batch/fold0/fold1/fold2/fold3/final order. -/
structure SixComputedWorkChecks where
  batch : Bool
  fold0 : Bool
  fold1 : Bool
  fold2 : Bool
  fold3 : Bool
  finalQuery : Bool

def SixComputedWorkChecks.at (checks : SixComputedWorkChecks) : WorkKind → Bool
  | .batch => checks.batch
  | .fold ⟨0, _⟩ => checks.fold0
  | .fold ⟨1, _⟩ => checks.fold1
  | .fold ⟨2, _⟩ => checks.fold2
  | .fold ⟨3, _⟩ => checks.fold3
  | .finalQuery => checks.finalQuery

def maintainedProofStep (kind : WorkKind) (nonce : Nonce64) :
    Tag67ProofWorkStep where
  position := match kind with
    | .batch => 0
    | .fold round => round.val + 1
    | .finalQuery => 5
  bits := kind.difficulty
  label := kind.label
  foldRound := match kind with
    | .fold round => round.val
    | .batch | .finalQuery => 255
  nonce := nonce.val
  nextAction := match kind with
    | .batch => 0
    | .fold round => round.val + 1
    | .finalQuery => 5

def maintainedSixStepTrace (view : WorkWireView) : List Tag67ProofWorkStep :=
  [ maintainedProofStep .batch (view.nonces .batch),
    maintainedProofStep (.fold 0) (view.nonces (.fold 0)),
    maintainedProofStep (.fold 1) (view.nonces (.fold 1)),
    maintainedProofStep (.fold 2) (view.nonces (.fold 2)),
    maintainedProofStep (.fold 3) (view.nonces (.fold 3)),
    maintainedProofStep .finalQuery (view.nonces .finalQuery) ]

def runProofFacingSixSteps
    (checks : SixComputedWorkChecks) (view : WorkWireView) :
    Option (List Tag67ProofWorkStep) :=
  tag67ProofSixActualSteps
    checks.batch checks.fold0 checks.fold1 checks.fold2 checks.fold3
    checks.finalQuery
    (view.nonces .batch).val
    (view.nonces (.fold 0)).val
    (view.nonces (.fold 1)).val
    (view.nonces (.fold 2)).val
    (view.nonces (.fold 3)).val
    (view.nonces .finalQuery).val

theorem generated_batch_helper_check_precedes_absorb
    (ok : Bool) (nonce : Nat) :
    (ok = false → tag67ProofCheckAndAbsorbBatch ok nonce = none) ∧
      (ok = true → tag67ProofCheckAndAbsorbBatch ok nonce = some {
        position := 0, bits := 37, label := 28, foldRound := 255,
        nonce := nonce, nextAction := 0 }) := by
  cases ok <;> simp [tag67ProofCheckAndAbsorbBatch,
    tag67ProofRequireRealV5Work]

theorem generated_fold_helper_check_precedes_absorb
    (ok : Bool) (round nonce : Nat) (hround : round < 4) :
    (ok = false → tag67ProofCheckAndAbsorbFold ok round nonce = none) ∧
      (ok = true → ∃ step,
        tag67ProofCheckAndAbsorbFold ok round nonce = some step ∧
          step.position = round + 1 ∧ step.label = 20 ∧
          step.foldRound = round ∧ step.nonce = nonce ∧
          step.nextAction = round + 1 ∧
          step.bits = foldDifficulty ⟨round, hround⟩) := by
  interval_cases round <;>
    cases ok <;>
    simp [tag67ProofCheckAndAbsorbFold, tag67ProofRequireRealV5Work,
      foldDifficulty]

theorem generated_final_helper_check_precedes_absorb
    (ok : Bool) (nonce : Nat) :
    (ok = false → tag67ProofCheckAndAbsorbFinal ok nonce = none) ∧
      (ok = true → tag67ProofCheckAndAbsorbFinal ok nonce = some {
        position := 5, bits := 32, label := 5, foldRound := 255,
        nonce := nonce, nextAction := 5 }) := by
  cases ok <;> simp [tag67ProofCheckAndAbsorbFinal,
    tag67ProofRequireRealV5Work]

/-- A successful generated run is exactly the maintained six-position trace;
there is neither a seventh event nor a missing position. -/
theorem generated_six_steps_success_iff
    (checks : SixComputedWorkChecks) (view : WorkWireView) :
    runProofFacingSixSteps checks view = some (maintainedSixStepTrace view) ↔
      checks.batch = true ∧ checks.fold0 = true ∧
      checks.fold1 = true ∧ checks.fold2 = true ∧
      checks.fold3 = true ∧ checks.finalQuery = true := by
  cases checks with
  | mk batch fold0 fold1 fold2 fold3 finalQuery =>
      cases batch <;> cases fold0 <;> cases fold1 <;> cases fold2 <;>
        cases fold3 <;> cases finalQuery <;>
        simp [runProofFacingSixSteps, tag67ProofSixActualSteps,
          tag67ProofCheckAndAbsorbBatch, tag67ProofCheckAndAbsorbFold,
          tag67ProofCheckAndAbsorbFinal, tag67ProofRequireRealV5Work,
          maintainedSixStepTrace, maintainedProofStep, WorkKind.difficulty,
          WorkKind.label, foldDifficulty]

/-- Each failing check short-circuits before emitting that position's absorb
event.  Earlier successful positions do not permit a later failed position to
appear in the returned trace. -/
theorem generated_failure_returns_before_absorption
    (checks : SixComputedWorkChecks) (view : WorkWireView) :
    (checks.batch = false → runProofFacingSixSteps checks view = none) ∧
    (checks.batch = true → checks.fold0 = false →
      runProofFacingSixSteps checks view = none) ∧
    (checks.batch = true → checks.fold0 = true → checks.fold1 = false →
      runProofFacingSixSteps checks view = none) ∧
    (checks.batch = true → checks.fold0 = true → checks.fold1 = true →
      checks.fold2 = false → runProofFacingSixSteps checks view = none) ∧
    (checks.batch = true → checks.fold0 = true → checks.fold1 = true →
      checks.fold2 = true → checks.fold3 = false →
      runProofFacingSixSteps checks view = none) ∧
    (checks.batch = true → checks.fold0 = true → checks.fold1 = true →
      checks.fold2 = true → checks.fold3 = true →
      checks.finalQuery = false → runProofFacingSixSteps checks view = none) := by
  cases checks with
  | mk batch fold0 fold1 fold2 fold3 finalQuery =>
      cases batch <;> cases fold0 <;> cases fold1 <;> cases fold2 <;>
        cases fold3 <;> cases finalQuery <;>
        simp [runProofFacingSixSteps, tag67ProofSixActualSteps,
          tag67ProofCheckAndAbsorbBatch, tag67ProofCheckAndAbsorbFold,
          tag67ProofCheckAndAbsorbFinal, tag67ProofRequireRealV5Work]

/-- Exact deployed control-flow metadata, including the next operation after
each successful absorb.  The payload itself is fixed by `workAbsorbPayload`:
fold events use `round :: nonceLEBytes`; batch/final use `nonceLEBytes`. -/
theorem maintained_trace_has_exact_six_positions
    (view : WorkWireView) :
    (maintainedSixStepTrace view).length = 6 ∧
      (maintainedSixStepTrace view).map (·.position) = [0, 1, 2, 3, 4, 5] ∧
      (maintainedSixStepTrace view).map (·.bits) = [37, 34, 33, 30, 25, 32] ∧
      (maintainedSixStepTrace view).map (·.label) = [28, 20, 20, 20, 20, 5] ∧
      (maintainedSixStepTrace view).map (·.foldRound) = [255, 0, 1, 2, 3, 255] ∧
      (maintainedSixStepTrace view).map (·.nextAction) = [0, 1, 2, 3, 4, 5] ∧
      (maintainedSixStepTrace view).map (·.nonce) =
        [(view.nonces .batch).val,
         (view.nonces (.fold 0)).val,
         (view.nonces (.fold 1)).val,
         (view.nonces (.fold 2)).val,
         (view.nonces (.fold 3)).val,
         (view.nonces .finalQuery).val] := by
  simp [maintainedSixStepTrace, maintainedProofStep, WorkKind.difficulty,
    WorkKind.label, foldDifficulty]

theorem maintained_trace_payloads_are_exact
    (view : WorkWireView) :
    workAbsorbPayload .batch (view.nonces .batch) =
        List.ofFn (nonceLEBytes (view.nonces .batch)) ∧
      (∀ round : Fin 4,
        workAbsorbPayload (.fold round) (view.nonces (.fold round)) =
          (⟨round.val, by have := round.isLt; omega⟩ : Byte) ::
            List.ofFn (nonceLEBytes (view.nonces (.fold round)))) ∧
      workAbsorbPayload .finalQuery (view.nonces .finalQuery) =
        List.ofFn (nonceLEBytes (view.nonces .finalQuery)) := by
  constructor
  · rfl
  constructor
  · intro round
    rfl
  · rfl

/-- Canonical actual-state view: successful helpers produce exactly the
post-absorb state and only then execute gamma/alpha/selector-q18. -/
def positionedInputsFromActualOperations {State Challenge : Type*}
    (functions : ExecutableWorkFunctions State Challenge)
    (stateBefore : WorkKind → State) (nonce : WorkKind → Nonce64) :
    PositionedWorkInputs State Challenge where
  stateBefore := stateBefore
  nonce := nonce
  stateAfter := fun kind =>
    functions.absorb (stateBefore kind) kind.label
      (workAbsorbPayload kind (nonce kind))
  nextResult := fun kind =>
    functions.executeNext
      (functions.absorb (stateBefore kind) kind.label
        (workAbsorbPayload kind (nonce kind))) kind.nextAction

structure ActualPositionedStateStep (State Challenge : Type*) where
  kind : WorkKind
  stateBefore : State
  stateAfter : State
  nextResult : Challenge

def actualPositionedStateStep {State Challenge : Type*}
    (functions : ExecutableWorkFunctions State Challenge)
    (stateBefore : WorkKind → State) (view : WorkWireView)
    (kind : WorkKind) : ActualPositionedStateStep State Challenge :=
  let stateAfter := functions.absorb (stateBefore kind) kind.label
    (workAbsorbPayload kind (view.nonces kind))
  {
    kind
    stateBefore := stateBefore kind
    stateAfter
    nextResult := functions.executeNext stateAfter kind.nextAction
  }

def actualSixPositionedStateTrace {State Challenge : Type*}
    (functions : ExecutableWorkFunctions State Challenge)
    (stateBefore : WorkKind → State) (view : WorkWireView) :
    List (ActualPositionedStateStep State Challenge) :=
  [ actualPositionedStateStep functions stateBefore view .batch,
    actualPositionedStateStep functions stateBefore view (.fold 0),
    actualPositionedStateStep functions stateBefore view (.fold 1),
    actualPositionedStateStep functions stateBefore view (.fold 2),
    actualPositionedStateStep functions stateBefore view (.fold 3),
    actualPositionedStateStep functions stateBefore view .finalQuery ]

/-- This is the exact boolean boundary permitted by the HashFn Arrow blocker:
each already-computed boolean is identified with its one positioned grinding
predicate.  It is deliberately not a generic hash-faithfulness premise. -/
def ComputedChecksAreActualPredicates {State Challenge : Type*}
    (checks : SixComputedWorkChecks)
    (functions : ExecutableWorkFunctions State Challenge)
    (stateBefore : WorkKind → State) (view : WorkWireView) : Prop :=
  ∀ kind, checks.at kind = true ↔
    functions.grindingOK (stateBefore kind) kind.difficulty (view.nonces kind)

/-- Strong control-flow correspondence: after the six computed predicate
results are supplied, the source-shaped `?` chain succeeds exactly when the
maintained executable semantics performs all six exact check/absorb/next
steps.  No arbitrary acceptance predicate and no hash-faithfulness premise
remain here. -/
theorem proofFacingSuccess_iff_exactSixActualSteps
    {State Challenge : Type*}
    (checks : SixComputedWorkChecks)
    (functions : ExecutableWorkFunctions State Challenge)
    (stateBefore : WorkKind → State) (view : WorkWireView)
    (hchecks : ComputedChecksAreActualPredicates checks functions stateBefore view) :
    runProofFacingSixSteps checks view = some (maintainedSixStepTrace view) ↔
      ExecutableWorkAcceptance functions
        (positionedInputsFromActualOperations functions stateBefore view.nonces) := by
  rw [generated_six_steps_success_iff]
  constructor
  · rintro ⟨hbatch, hfold0, hfold1, hfold2, hfold3, hfinal⟩
    constructor
    intro kind
    constructor
    · cases kind with
      | batch => exact (hchecks .batch).mp hbatch
      | fold round =>
          fin_cases round
          · exact (hchecks (.fold 0)).mp hfold0
          · exact (hchecks (.fold 1)).mp hfold1
          · exact (hchecks (.fold 2)).mp hfold2
          · exact (hchecks (.fold 3)).mp hfold3
      | finalQuery => exact (hchecks .finalQuery).mp hfinal
    · exact ⟨rfl, rfl⟩
  · intro accepted
    have htrue (kind : WorkKind) : checks.at kind = true :=
      (hchecks kind).mpr (accepted.everyWorkOK kind).1
    exact ⟨htrue .batch, htrue (.fold 0), htrue (.fold 1),
      htrue (.fold 2), htrue (.fold 3), htrue .finalQuery⟩

/-- Strongest six-state trace theorem.  Besides acceptance, it exposes all six
actual before/after pairs and next results in deployed order.  Every `after`
is the exact fixed-label/fixed-payload absorb result, and every `nextResult`
uses that post-absorb state for gamma, alpha0--alpha3, or selector/q18. -/
theorem proofFacingSuccess_iff_exactSixPositionedStateTrace
    {State Challenge : Type*}
    (checks : SixComputedWorkChecks)
    (functions : ExecutableWorkFunctions State Challenge)
    (stateBefore : WorkKind → State) (view : WorkWireView)
    (hchecks : ComputedChecksAreActualPredicates checks functions stateBefore view) :
    runProofFacingSixSteps checks view = some (maintainedSixStepTrace view) ↔
      ExecutableWorkAcceptance functions
          (positionedInputsFromActualOperations functions stateBefore view.nonces) ∧
        (actualSixPositionedStateTrace functions stateBefore view).length = 6 ∧
        (actualSixPositionedStateTrace functions stateBefore view).map (·.kind) =
          [.batch, .fold 0, .fold 1, .fold 2, .fold 3, .finalQuery] ∧
        (actualSixPositionedStateTrace functions stateBefore view).map
          (fun step => (step.stateBefore, step.stateAfter, step.nextResult)) =
          [ (stateBefore .batch,
              functions.absorb (stateBefore .batch) 28
                (workAbsorbPayload .batch (view.nonces .batch)),
              functions.executeNext
                (functions.absorb (stateBefore .batch) 28
                  (workAbsorbPayload .batch (view.nonces .batch))) .sampleGamma),
            (stateBefore (.fold 0),
              functions.absorb (stateBefore (.fold 0)) 20
                (workAbsorbPayload (.fold 0) (view.nonces (.fold 0))),
              functions.executeNext
                (functions.absorb (stateBefore (.fold 0)) 20
                  (workAbsorbPayload (.fold 0) (view.nonces (.fold 0))))
                (.sampleFoldAlpha 0)),
            (stateBefore (.fold 1),
              functions.absorb (stateBefore (.fold 1)) 20
                (workAbsorbPayload (.fold 1) (view.nonces (.fold 1))),
              functions.executeNext
                (functions.absorb (stateBefore (.fold 1)) 20
                  (workAbsorbPayload (.fold 1) (view.nonces (.fold 1))))
                (.sampleFoldAlpha 1)),
            (stateBefore (.fold 2),
              functions.absorb (stateBefore (.fold 2)) 20
                (workAbsorbPayload (.fold 2) (view.nonces (.fold 2))),
              functions.executeNext
                (functions.absorb (stateBefore (.fold 2)) 20
                  (workAbsorbPayload (.fold 2) (view.nonces (.fold 2))))
                (.sampleFoldAlpha 2)),
            (stateBefore (.fold 3),
              functions.absorb (stateBefore (.fold 3)) 20
                (workAbsorbPayload (.fold 3) (view.nonces (.fold 3))),
              functions.executeNext
                (functions.absorb (stateBefore (.fold 3)) 20
                  (workAbsorbPayload (.fold 3) (view.nonces (.fold 3))))
                (.sampleFoldAlpha 3)),
            (stateBefore .finalQuery,
              functions.absorb (stateBefore .finalQuery) 5
                (workAbsorbPayload .finalQuery (view.nonces .finalQuery)),
              functions.executeNext
                (functions.absorb (stateBefore .finalQuery) 5
                  (workAbsorbPayload .finalQuery (view.nonces .finalQuery)))
                .absorbSelectorThenSampleQ18) ] := by
  rw [proofFacingSuccess_iff_exactSixActualSteps checks functions stateBefore view hchecks]
  simp [actualSixPositionedStateTrace, actualPositionedStateStep,
    WorkKind.label, WorkKind.nextAction]

#print axioms generated_batch_helper_check_precedes_absorb
#print axioms generated_fold_helper_check_precedes_absorb
#print axioms generated_final_helper_check_precedes_absorb
#print axioms generated_six_steps_success_iff
#print axioms generated_failure_returns_before_absorption
#print axioms maintained_trace_has_exact_six_positions
#print axioms maintained_trace_payloads_are_exact
#print axioms proofFacingSuccess_iff_exactSixActualSteps
#print axioms proofFacingSuccess_iff_exactSixPositionedStateTrace

end AspisTag67SixActualSteps
