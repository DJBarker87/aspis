import AspisFormal.K1.V7Tag73RawFutureFreeDriver
import AspisFormal.K1.V7Tag73ReturnedPlanSemantics
import AspisFormal.K1.V7Tag73CheckedRefinementFutureFreePath

/-!
# Fuel monotonicity after a Tag-73 driver halt

The concrete machine fixes one global driver-fuel cap before seeing the
proof, whereas an exact accepted transcript path naturally computes only the
number of microsteps it actually needs.  This leaf proves the required
alignment fact from the operational interpreter: once a path reaches a
terminal/rejecting control, adding unused driver fuel preserves the exact
ordered oracle path and final verifier state.

No runtime bound, acceptance predicate, restoration function or extraction
claim is assumed.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73RawDriverFuelMonotonicity

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ResumeDerivedReplayNode
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73ReturnedPlanSemantics
open AspisK1.V7Tag73CheckedRefinementFutureFreePath

noncomputable section

/-- Exact classification of the three controls at which the concrete driver
halts.  In particular, no pending prover or verifier action is hidden behind
the Boolean guard. -/
theorem is_driver_halt_iff (control : FutureFreeControl) :
    isDriverHalt control = true ↔
      control = .done ∨
      (∃ reason, control = .rejected reason) ∨
      control = .adaptive .rejected := by
  cases control with
  | adaptive adaptive =>
      cases adaptive <;> simp [isDriverHalt]
  | linear remaining => simp [isDriverHalt]
  | absorbPayload payload remaining => simp [isDriverHalt]
  | workCheck stage nonce remaining => simp [isDriverHalt]
  | workCheckpoint stage nonce remaining => simp [isDriverHalt]
  | workAbsorb stage nonce remaining => simp [isDriverHalt]
  | sampleChallenge id outputs remaining => simp [isDriverHalt]
  | q16Absorb base counter remaining => simp [isDriverHalt]
  | q16Sample base counter outputs remaining => simp [isDriverHalt]
  | q16Restore base counter nextCounter remaining => simp [isDriverHalt]
  | q16Selected base counter schedule remaining => simp [isDriverHalt]
  | q16SamplerReject counter reason => simp [isDriverHalt]
  | q16AllNoncompactReject => simp [isDriverHalt]
  | rejected reason => simp [isDriverHalt]
  | done => simp [isDriverHalt]

/-- At a control already classified as a driver halt, neither a raw prover
submission nor a verifier action is available, so one microstep stutters. -/
theorem raw_future_free_microstep_at_halt
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (state : FutureFreeVerifierState)
    (halted : isDriverHalt state.current.control = true) :
    rawFutureFreeMicrostep environment raw state = .pure state := by
  have submissionNone : submitNextRawMessage raw state = none := by
    rcases (is_driver_halt_iff state.current.control).mp halted with
      done | ⟨reason, rejected⟩ | adaptiveRejected
    · simp [submitNextRawMessage, done]
    · simp [submitNextRawMessage, rejected]
    · simp [submitNextRawMessage, adaptiveRejected]
  have actionNone : state.current.control.nextVerifierAction? = none := by
    rcases (is_driver_halt_iff state.current.control).mp halted with
      done | ⟨reason, rejected⟩ | adaptiveRejected
    · simp [done, FutureFreeControl.nextVerifierAction?]
    · simp [rejected, FutureFreeControl.nextVerifierAction?]
    · simp [adaptiveRejected, FutureFreeControl.nextVerifierAction?,
        OpenAdaptiveControl.nextVerifierAction?]
  unfold rawFutureFreeMicrostep
  rw [submissionNone]
  unfold runOneFutureFreeVerifierAction
  rw [actionNone]

/-- Starting from an already halted state, every fuel allowance returns that
state without issuing an oracle query. -/
theorem drive_raw_future_free_at_halt
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (state : FutureFreeVerifierState)
    (halted : isDriverHalt state.current.control = true) :
    ∀ fuel, MachineQueryPath
      (driveRawFutureFree environment raw fuel state) [] state := by
  intro fuel
  cases fuel with
  | zero => exact .pure state
  | succ fuel =>
      rw [driveRawFutureFree,
        raw_future_free_microstep_at_halt environment raw state halted]
      simpa [bindOracleMachine, halted] using MachineQueryPath.pure state

/-- Once an operational path has halted, unused extra fuel is observationally
irrelevant: the path's query/answer list and returned state are literal
equalities, not merely extension or simulation relations. -/
theorem drive_raw_future_free_path_extend_fuel
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages) :
    ∀ fuel extra state pairs result,
      MachineQueryPath (driveRawFutureFree environment raw fuel state)
          pairs result →
      isDriverHalt result.current.control = true →
      MachineQueryPath
        (driveRawFutureFree environment raw (fuel + extra) state)
        pairs result := by
  intro fuel
  induction fuel with
  | zero =>
      intro extra state pairs result path halted
      cases path
      simpa only [Nat.zero_add] using
        drive_raw_future_free_at_halt environment raw state halted extra
  | succ fuel ih =>
      intro extra state pairs result path halted
      simp only [driveRawFutureFree] at path
      obtain ⟨next, headPairs, tailPairs, headPath, tailPath, pairsExact⟩ :=
        machine_query_path_bind_split
          (rawFutureFreeMicrostep environment raw state)
          (fun next =>
            if isDriverHalt next.current.control then .pure next
            else driveRawFutureFree environment raw fuel next)
          pairs result path
      rw [show Nat.succ fuel + extra = Nat.succ (fuel + extra) by omega,
        driveRawFutureFree]
      rw [pairsExact]
      by_cases nextHalted : isDriverHalt next.current.control = true
      · have tail : MachineQueryPath
            (if isDriverHalt next.current.control = true then .pure next
              else driveRawFutureFree environment raw (fuel + extra) next)
            tailPairs result := by
          simpa [nextHalted] using tailPath
        exact machine_query_path_bind_join
          (rawFutureFreeMicrostep environment raw state)
          (fun next =>
            if isDriverHalt next.current.control = true then .pure next
            else driveRawFutureFree environment raw (fuel + extra) next)
          headPairs tailPairs next result headPath tail
      · simp [nextHalted] at tailPath
        have extendedTail := ih extra next tailPairs result tailPath halted
        have tail : MachineQueryPath
            (if isDriverHalt next.current.control = true then .pure next
              else driveRawFutureFree environment raw (fuel + extra) next)
            tailPairs result := by
          simpa [nextHalted] using extendedTail
        exact machine_query_path_bind_join
          (rawFutureFreeMicrostep environment raw state)
          (fun next =>
            if isDriverHalt next.current.control = true then .pure next
            else driveRawFutureFree environment raw (fuel + extra) next)
          headPairs tailPairs next result headPath tail

/-- Initial-state specialization used by the checked-path/runtime bridge. -/
theorem initial_raw_future_free_path_extend_fuel
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (fuel extra : Nat) (pairs : List (ShaInput × ShaOutput))
    (result : FutureFreeVerifierState)
    (path : MachineQueryPath
      (initialRawFutureFreeProgram environment raw fuel) pairs result)
    (halted : isDriverHalt result.current.control = true) :
    MachineQueryPath
      (initialRawFutureFreeProgram environment raw (fuel + extra))
      pairs result := by
  exact drive_raw_future_free_path_extend_fuel environment raw fuel extra
    (initialFutureFreeVerifierState (FixedBindings.ofContext raw.context))
    pairs result path halted

#print axioms raw_future_free_microstep_at_halt
#print axioms is_driver_halt_iff
#print axioms drive_raw_future_free_at_halt
#print axioms drive_raw_future_free_path_extend_fuel
#print axioms initial_raw_future_free_path_extend_fuel

end

end AspisK1.V7Tag73RawDriverFuelMonotonicity
