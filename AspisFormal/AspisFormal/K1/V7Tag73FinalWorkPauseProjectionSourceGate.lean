import AspisFormal.K1.V7Tag73SchedulerNativeTargetPause

/-!
# Source gate for pre-final projection stability

The scheduler-native pause retains the exact pending oracle continuation, but
that continuation is intentionally an arbitrary function of the fresh answer.
Consequently the scheduler interface alone cannot establish that data returned
after the pause was already fixed before the selected final-work answer.

This module records both sides of that source boundary:

* an explicit answer-sensitive continuation counterexample; and
* the narrow, result-generic stability certificate that a concrete translated
  source wrapper may inhabit once it exposes a pre-final projection.

The certificate mentions neither Tag-73 acceptance nor K1 extraction.  It is a
control-flow/source property of one paused continuation.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73FinalWorkPauseProjectionSourceGate

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativeTargetPause

noncomputable section

universe u v

/-! ## The abstraction obstruction -/

def zeroSourceGateDigest : Digest256 := fun _index => 0

def firstByteOneSourceGateDigest : Digest256 := fun index =>
  if index.val = 0 then 1 else 0

theorem zero_source_gate_digest_ne_first_byte_one :
    zeroSourceGateDigest ≠ firstByteOneSourceGateDigest := by
  intro equal
  have atFirst := congrFun equal (⟨0, by omega⟩ : Fin 32)
  change (0 : UInt8) = 1 at atFirst
  exact (by decide : (0 : UInt8) ≠ 1) atFirst

/-- The pending program stored by a scheduler pause may retain its answer in
the returned value.  This is permitted by the generic `OracleMachine` type. -/
def answerSensitiveSourceContinuation (answer : ShaOutput) :
    OracleMachine Digest256 :=
  .pure answer

@[simp] theorem answer_sensitive_source_continuation_returns_input
    (answer : ShaOutput) :
    answerSensitiveSourceContinuation answer = .pure answer := by
  rfl

/-- There can be no theorem saying that an arbitrary scheduler continuation
has an answer-independent returned projection.  Production/source structure
must supply that fact for the particular continuation being replayed. -/
theorem arbitrary_oracle_continuation_does_not_freeze_returned_value :
    ¬ (∀ (nextProgram : ShaOutput → OracleMachine Digest256)
        (left right : ShaOutput),
      nextProgram left = nextProgram right) := by
  intro universal
  have equalPrograms := universal answerSensitiveSourceContinuation
    zeroSourceGateDigest firstByteOneSourceGateDigest
  have equalDigests :
      zeroSourceGateDigest = firstByteOneSourceGateDigest := by
    simpa only [answerSensitiveSourceContinuation,
      OracleMachine.pure.injEq] using equalPrograms
  exact zero_source_gate_digest_ne_first_byte_one equalDigests

/-! ## Narrow source certificate -/

/-- A source-level certificate that a projection of every successful return
from one frozen fresh-request continuation was already fixed at the pause.

`eligible` lets the caller restrict the statement to accepted final-work
answers.  Subsequent answer suffixes remain arbitrary: once the source says
the projection was fixed at the pause, later query answers cannot change it.
-/
structure ReturnedProjectionFrozenAtFreshPause
    {globalOracleCalls : Nat} {Result : Type u} {target : ShaInput}
    (transitionFuel : Nat)
    (pause : SchedulerNativeFreshPause globalOracleCalls Result target)
    (eligible : Digest256 → Prop) (Projection : Type v)
    (project : Result → Projection) where
  snapshot : Projection
  returned_eq_snapshot :
    ∀ (answer : Digest256) (remainingAnswers : List Digest256)
      (result : Result),
      eligible answer →
      (pause.resumeRunWith transitionFuel answer remainingAnswers).terminal =
        .returned result →
      project result = snapshot

/-- Two successful eligible resumptions of a source-certified pause have the
same pre-final projection, even when their later oracle suffixes differ. -/
theorem returned_projection_eq_of_frozen_at_fresh_pause
    {globalOracleCalls : Nat} {Result : Type u} {target : ShaInput}
    {transitionFuel : Nat}
    {pause : SchedulerNativeFreshPause globalOracleCalls Result target}
    {eligible : Digest256 → Prop} {Projection : Type v}
    {project : Result → Projection}
    (frozen : ReturnedProjectionFrozenAtFreshPause transitionFuel pause
      eligible Projection project)
    {leftAnswer rightAnswer : Digest256}
    {leftRemaining rightRemaining : List Digest256}
    {leftResult rightResult : Result}
    (leftEligible : eligible leftAnswer)
    (rightEligible : eligible rightAnswer)
    (leftReturned :
      (pause.resumeRunWith transitionFuel leftAnswer leftRemaining).terminal =
        .returned leftResult)
    (rightReturned :
      (pause.resumeRunWith transitionFuel rightAnswer rightRemaining).terminal =
        .returned rightResult) :
    project leftResult = project rightResult := by
  rw [frozen.returned_eq_snapshot leftAnswer leftRemaining leftResult
      leftEligible leftReturned,
    frozen.returned_eq_snapshot rightAnswer rightRemaining rightResult
      rightEligible rightReturned]

end

end AspisK1.V7Tag73FinalWorkPauseProjectionSourceGate
