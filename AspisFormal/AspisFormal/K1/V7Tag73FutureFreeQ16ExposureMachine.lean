import AspisFormal.K1.V7Tag73Q16ControlInvariant
import AspisFormal.K1.V7Tag73CausalSlotMachineRouter

/-!
# Causal q16 labels for the literal future-free verifier

The future-free verifier exposes every squeeze as two sequential SHA queries.
Only the first query of a `q16Sample` consumes a candidate digest block; the
advance query and every other verifier query are residual coordinates.

This file gives an executable, answer-by-answer monitor for the production
`driveRawFutureFree` state machine.  Its current label is computed before the
next digest is supplied.  Zero-query prover and structural transitions are
normalized using only the remaining driver fuel and the current verifier
state.  Therefore the label may depend on earlier answers through that state,
but never on the answer it labels.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73FutureFreeQ16ExposureMachine

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73Q16ControlInvariant
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalSlotMachineRouter

noncomputable section

/-- The q16 coordinate named by the live verifier control, when the literal
block counter is within the deployed eight-block cap. -/
def currentQ16DigestSlot? (state : FutureFreeVerifierState) :
    Option Q16DigestSlot :=
  match state.current.control with
  | .q16Sample _base counter outputs _remaining =>
      if bounded : outputs.length < 8 then
        some (counter, ⟨outputs.length, bounded⟩)
      else
        none
  | _ => none

theorem current_q16_digest_slot_eq_bounded_snapshot
    (state : FutureFreeVerifierState)
    (base : Digest256) (counter : Fin 64) (outputs : List Digest256)
    (remaining : List FutureFreeSlot)
    (controlExact : state.current.control =
      .q16Sample base counter outputs remaining)
    (bounded : Q16SnapshotSlotBound state.current) :
    currentQ16DigestSlot? state =
      some (q16DigestSlotOfBoundedSnapshot state.current base counter outputs
        remaining controlExact bounded) := by
  have lengthBound : outputs.length < 8 := by
    rw [Q16SnapshotSlotBound, controlExact] at bounded
    exact bounded
  simp [currentQ16DigestSlot?, controlExact, lengthBound,
    q16DigestSlotOfBoundedSnapshot]

/-- Monitor state between individual full-256 oracle answers.  `drive` is a
literal production driver invocation.  `squeezeAdvance` is the second half of
one already exposed squeeze.  `stopped` retains the exact terminal program so
the program-erasure theorem does not conflate return and abort. -/
inductive FutureFreeQ16ExposureCursor where
  | drive (fuel : Nat) (state : FutureFreeVerifierState)
  | squeezeAdvance (fuel : Nat) (state : FutureFreeVerifierState)
      (output : Digest256)
  | stopped (program : OracleMachine FutureFreeVerifierState)

/-- Complete the current verifier microstep and resume the production driver
with its literal remaining fuel. -/
def continueAfterVerifierReply
    (environment : FutureFreeEnvironment) (fuel : Nat)
    (state : FutureFreeVerifierState) (reply : VerifierReply) :
    FutureFreeQ16ExposureCursor :=
  match advanceFutureFreeVerifier environment state reply with
  | none => .stopped (.abort .controllerRefused)
  | some next =>
      if isDriverHalt next.current.control then
        .stopped (.pure next)
      else
        .drive fuel next

/-- The literal production continuation after one complete verifier reply. -/
def continueAfterVerifierReplyProgram
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (fuel : Nat) (state : FutureFreeVerifierState) (reply : VerifierReply) :
    OracleMachine FutureFreeVerifierState :=
  match advanceFutureFreeVerifier environment state reply with
  | none => .abort .controllerRefused
  | some next =>
      if isDriverHalt next.current.control then
        .pure next
      else
        driveRawFutureFree environment raw fuel next

/-- Forget the monitor and recover the exact oracle program at its current
position. -/
def FutureFreeQ16ExposureCursor.program
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages) :
    FutureFreeQ16ExposureCursor → OracleMachine FutureFreeVerifierState
  | .drive fuel state => driveRawFutureFree environment raw fuel state
  | .squeezeAdvance fuel state output =>
      .query (bytes state.current.core.digest ++ [domAdvance]) fun advance =>
        continueAfterVerifierReplyProgram environment raw fuel state
          (.squeeze output advance)
  | .stopped program => program

@[simp] theorem continue_after_verifier_reply_program_exact
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (fuel : Nat) (state : FutureFreeVerifierState) (reply : VerifierReply) :
    (continueAfterVerifierReply environment fuel state reply).program
        environment raw =
      continueAfterVerifierReplyProgram environment raw fuel state reply := by
  cases advanced : advanceFutureFreeVerifier environment state reply with
  | none =>
      simp [continueAfterVerifierReply, continueAfterVerifierReplyProgram,
        FutureFreeQ16ExposureCursor.program, advanced]
  | some next =>
      by_cases terminal : isDriverHalt next.current.control
      · simp [continueAfterVerifierReply, continueAfterVerifierReplyProgram,
          FutureFreeQ16ExposureCursor.program, advanced, terminal]
      · simp [continueAfterVerifierReply, continueAfterVerifierReplyProgram,
          FutureFreeQ16ExposureCursor.program, advanced, terminal]

@[simp] theorem bind_advanced_verifier_reply_program_exact
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (fuel : Nat) (state : FutureFreeVerifierState) (reply : VerifierReply) :
    bindOracleMachine
        (match advanceFutureFreeVerifier environment state reply with
        | some next => .pure next
        | none => .abort .controllerRefused)
        (fun next =>
          if isDriverHalt next.current.control then
            .pure next
          else
            driveRawFutureFree environment raw fuel next) =
      continueAfterVerifierReplyProgram environment raw fuel state reply := by
  cases advanced : advanceFutureFreeVerifier environment state reply with
  | none =>
      simp [advanced, bindOracleMachine, continueAfterVerifierReplyProgram]
  | some next =>
      by_cases terminal : isDriverHalt next.current.control
      · simp [advanced, terminal, bindOracleMachine,
          continueAfterVerifierReplyProgram]
      · simp [advanced, terminal, bindOracleMachine,
          continueAfterVerifierReplyProgram]

/-- Same equation with the proof-named conditional used literally by
`driveRawFutureFree`. -/
@[simp] theorem bind_advanced_verifier_reply_program_exact_dependent
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (fuel : Nat) (state : FutureFreeVerifierState) (reply : VerifierReply) :
    bindOracleMachine
        (match advanceFutureFreeVerifier environment state reply with
        | some next => .pure next
        | none => .abort .controllerRefused)
        (fun next =>
          if terminal : isDriverHalt next.current.control then
            .pure next
          else
            driveRawFutureFree environment raw fuel next) =
      continueAfterVerifierReplyProgram environment raw fuel state reply := by
  cases advanced : advanceFutureFreeVerifier environment state reply with
  | none =>
      simp [advanced, bindOracleMachine, continueAfterVerifierReplyProgram]
  | some next =>
      by_cases terminal : isDriverHalt next.current.control
      · simp [advanced, terminal, bindOracleMachine,
          continueAfterVerifierReplyProgram]
      · simp [advanced, terminal, bindOracleMachine,
          continueAfterVerifierReplyProgram]

@[simp] theorem squeeze_advance_cursor_program_exact
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (fuel : Nat) (state : FutureFreeVerifierState) (output : Digest256) :
    (FutureFreeQ16ExposureCursor.squeezeAdvance fuel state output).program
        environment raw =
      .query (bytes state.current.core.digest ++ [domAdvance]) fun advance =>
        continueAfterVerifierReplyProgram environment raw fuel state
          (.squeeze output advance) := by
  rfl

/-- One normalized pre-answer request.  The optional q16 slot is fixed before
the query answer is supplied. -/
inductive FutureFreeQ16ExposureRequest where
  | halted (program : OracleMachine FutureFreeVerifierState)
  | query (slot : Option Q16DigestSlot) (input : ShaInput)
      (next : Digest256 → FutureFreeQ16ExposureCursor)

def FutureFreeQ16ExposureRequest.program
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages) :
    FutureFreeQ16ExposureRequest → OracleMachine FutureFreeVerifierState
  | .halted program => program
  | .query _slot input next =>
      .query input fun answer => (next answer).program environment raw

/-- A structural verifier reply may normalize through further zero-query
steps.  If that recursive normalization erases to the production driver,
then the whole structural step does too. -/
theorem normalized_structural_reply_program_exact
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (fuel : Nat) (state : FutureFreeVerifierState) (reply : VerifierReply)
    (resume : FutureFreeVerifierState → FutureFreeQ16ExposureRequest)
    (resumeExact : ∀ next,
      (resume next).program environment raw =
        driveRawFutureFree environment raw fuel next) :
    (match advanceFutureFreeVerifier environment state reply with
      | none =>
          FutureFreeQ16ExposureRequest.halted
            (.abort .controllerRefused)
      | some next =>
          if isDriverHalt next.current.control then
            FutureFreeQ16ExposureRequest.halted (.pure next)
          else
            resume next).program environment raw =
      bindOracleMachine
        (match advanceFutureFreeVerifier environment state reply with
        | some next => .pure next
        | none => .abort .controllerRefused)
        (fun next =>
          if terminal : isDriverHalt next.current.control then
            .pure next
          else
            driveRawFutureFree environment raw fuel next) := by
  cases advanced : advanceFutureFreeVerifier environment state reply with
  | none =>
      simp [advanced, bindOracleMachine, FutureFreeQ16ExposureRequest.program]
  | some next =>
      by_cases terminal : isDriverHalt next.current.control
      · simp [advanced, terminal, bindOracleMachine,
          FutureFreeQ16ExposureRequest.program]
      · simpa [advanced, terminal, bindOracleMachine] using resumeExact next

/-- Normalize zero-query production transitions until the next actual SHA
exposure.  Recursion consumes one driver unit and cannot inspect the next
answer. -/
def seekDriveQ16Exposure
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages) :
    (fuel : Nat) → FutureFreeVerifierState → FutureFreeQ16ExposureRequest
  | 0, state => .halted (.pure state)
  | fuel + 1, state =>
      match submitNextRawMessage raw state with
      | some next =>
          if isDriverHalt next.current.control then
            .halted (.pure next)
          else
            seekDriveQ16Exposure environment raw fuel next
      | none =>
          match state.current.control.nextVerifierAction? with
          | none =>
              if isDriverHalt state.current.control then
                .halted (.pure state)
              else
                seekDriveQ16Exposure environment raw fuel state
          | some action =>
              match structuralFutureFreeReply action with
              | some reply =>
                  match advanceFutureFreeVerifier environment state reply with
                  | none => .halted (.abort .controllerRefused)
                  | some next =>
                      if isDriverHalt next.current.control then
                        .halted (.pure next)
                      else
                        seekDriveQ16Exposure environment raw fuel next
              | none =>
                  match action with
                  | .squeezePair _owner _block =>
                      .query (currentQ16DigestSlot? state)
                        (bytes state.current.core.digest ++ [domSqueeze])
                        (fun output => .squeezeAdvance fuel state output)
                  | _ =>
                      match actionInputs state.current.bindings
                          state.current.core action with
                      | [input] =>
                          .query none input fun output =>
                            continueAfterVerifierReply environment fuel state
                              (.single output)
                      | _ => .halted (.abort .controllerRefused)
termination_by fuel _ => fuel

/-- Normalize either phase of the monitor. -/
def seekFutureFreeQ16Exposure
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages) :
    FutureFreeQ16ExposureCursor → FutureFreeQ16ExposureRequest
  | .drive fuel state => seekDriveQ16Exposure environment raw fuel state
  | .squeezeAdvance fuel state output =>
      .query none (bytes state.current.core.digest ++ [domAdvance]) fun advance =>
        continueAfterVerifierReply environment fuel state
          (.squeeze output advance)
  | .stopped program => .halted program

/-- Normalization is only a view: erasing its label and continuation recovers
the literal production driver program. -/
theorem seek_drive_q16_exposure_program_exact
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages) :
    ∀ fuel state,
      (seekDriveQ16Exposure environment raw fuel state).program environment
          raw =
        driveRawFutureFree environment raw fuel state := by
  intro fuel
  induction fuel with
  | zero =>
      intro state
      simp [seekDriveQ16Exposure, FutureFreeQ16ExposureRequest.program,
        driveRawFutureFree]
  | succ fuel ih =>
      intro state
      simp only [seekDriveQ16Exposure, driveRawFutureFree]
      unfold rawFutureFreeMicrostep
      cases submitted : submitNextRawMessage raw state with
      | some next =>
          by_cases terminal : isDriverHalt next.current.control
          · simp [submitted, terminal, bindOracleMachine,
              FutureFreeQ16ExposureRequest.program]
          · simpa [submitted, terminal, bindOracleMachine] using ih next
      | none =>
          simp only [submitted]
          unfold runOneFutureFreeVerifierAction
          cases actionFound : state.current.control.nextVerifierAction? with
          | none =>
              by_cases terminal : isDriverHalt state.current.control
              · simp [actionFound, terminal, bindOracleMachine,
                  FutureFreeQ16ExposureRequest.program]
              · simpa [actionFound, terminal, bindOracleMachine] using
                  ih state
          | some action =>
              simp only [actionFound]
              cases action with
              | absorb payload =>
                  simp only [structuralFutureFreeReply,
                    futureFreeReplyProgram, actionInputs,
                    FutureFreeQ16ExposureRequest.program,
                    bindOracleMachine]
                  congr 1
                  funext output
                  rw [continue_after_verifier_reply_program_exact]
                  exact
                    (bind_advanced_verifier_reply_program_exact environment raw
                      fuel state (.single output)).symm
              | requestRootSalt tree =>
                  simp only [structuralFutureFreeReply,
                    futureFreeReplyProgram, actionInputs,
                    FutureFreeQ16ExposureRequest.program,
                    bindOracleMachine]
                  congr 1
                  funext output
                  rw [continue_after_verifier_reply_program_exact]
                  exact
                    (bind_advanced_verifier_reply_program_exact environment raw
                      fuel state (.single output)).symm
              | absorbC1 root =>
                  cases saltExact : state.current.core.c1Salt with
                  | none =>
                      simp [structuralFutureFreeReply,
                        futureFreeReplyProgram, actionInputs, saltExact,
                        FutureFreeQ16ExposureRequest.program,
                        bindOracleMachine]
                  | some salt =>
                      simp only [structuralFutureFreeReply,
                        futureFreeReplyProgram, actionInputs, saltExact,
                        FutureFreeQ16ExposureRequest.program,
                        bindOracleMachine]
                      congr 1
                      funext output
                      rw [continue_after_verifier_reply_program_exact]
                      exact
                        (bind_advanced_verifier_reply_program_exact environment
                          raw fuel state (.single output)).symm
              | absorbC2 lambda chi commitment =>
                  cases saltExact : state.current.core.c2Salt with
                  | none =>
                      simp [structuralFutureFreeReply,
                        futureFreeReplyProgram, actionInputs, saltExact,
                        FutureFreeQ16ExposureRequest.program,
                        bindOracleMachine]
                  | some salt =>
                      simp only [structuralFutureFreeReply,
                        futureFreeReplyProgram, actionInputs, saltExact,
                        FutureFreeQ16ExposureRequest.program,
                        bindOracleMachine]
                      congr 1
                      funext output
                      rw [continue_after_verifier_reply_program_exact]
                      exact
                        (bind_advanced_verifier_reply_program_exact environment
                          raw fuel state (.single output)).symm
              | squeezePair owner block =>
                  simp only [structuralFutureFreeReply,
                    futureFreeReplyProgram, actionInputs,
                    FutureFreeQ16ExposureRequest.program,
                    bindOracleMachine,
                    squeeze_advance_cursor_program_exact]
                  congr 1
                  funext output
                  congr 1
                  funext advance
                  exact
                    (bind_advanced_verifier_reply_program_exact environment raw
                      fuel state (.squeeze output advance)).symm
              | workProbe stage nonce kind =>
                  simp only [structuralFutureFreeReply,
                    futureFreeReplyProgram, actionInputs,
                    FutureFreeQ16ExposureRequest.program,
                    bindOracleMachine]
                  congr 1
                  funext output
                  rw [continue_after_verifier_reply_program_exact]
                  exact
                    (bind_advanced_verifier_reply_program_exact environment raw
                      fuel state (.single output)).symm
              | checkpoint checkpoint =>
                  simp only [structuralFutureFreeReply,
                    futureFreeReplyProgram, bindOracleMachine]
                  cases advanced : advanceFutureFreeVerifier environment state
                      .none with
                  | none =>
                      simp [advanced, bindOracleMachine,
                        FutureFreeQ16ExposureRequest.program]
                  | some next =>
                      by_cases terminal : isDriverHalt next.current.control
                      · simp [advanced, terminal, bindOracleMachine,
                          FutureFreeQ16ExposureRequest.program]
                      · simpa [advanced, terminal, bindOracleMachine] using
                          ih next
              | markQ16Base =>
                  simp only [structuralFutureFreeReply,
                    futureFreeReplyProgram, bindOracleMachine]
                  cases advanced : advanceFutureFreeVerifier environment state
                      .none with
                  | none =>
                      simp [advanced, bindOracleMachine,
                        FutureFreeQ16ExposureRequest.program]
                  | some next =>
                      by_cases terminal : isDriverHalt next.current.control
                      · simp [advanced, terminal, bindOracleMachine,
                          FutureFreeQ16ExposureRequest.program]
                      · simpa [advanced, terminal, bindOracleMachine] using
                          ih next
              | q16CandidateAbsorb counter outcome selected =>
                  simp only [structuralFutureFreeReply,
                    futureFreeReplyProgram, actionInputs,
                    FutureFreeQ16ExposureRequest.program,
                    bindOracleMachine]
                  congr 1
                  funext output
                  rw [continue_after_verifier_reply_program_exact]
                  exact
                    (bind_advanced_verifier_reply_program_exact environment raw
                      fuel state (.single output)).symm
              | q16Restore counter =>
                  simp only [structuralFutureFreeReply,
                    futureFreeReplyProgram, bindOracleMachine]
                  cases advanced : advanceFutureFreeVerifier environment state
                      .none with
                  | none =>
                      simp [advanced, bindOracleMachine,
                        FutureFreeQ16ExposureRequest.program]
                  | some next =>
                      by_cases terminal : isDriverHalt next.current.control
                      · simp [advanced, terminal, bindOracleMachine,
                          FutureFreeQ16ExposureRequest.program]
                      · simpa [advanced, terminal, bindOracleMachine] using
                          ih next
              | q16Selected counter =>
                  simp only [structuralFutureFreeReply,
                    futureFreeReplyProgram, bindOracleMachine]
                  cases advanced : advanceFutureFreeVerifier environment state
                      .none with
                  | none =>
                      simp [advanced, bindOracleMachine,
                        FutureFreeQ16ExposureRequest.program]
                  | some next =>
                      by_cases terminal : isDriverHalt next.current.control
                      · simp [advanced, terminal, bindOracleMachine,
                          FutureFreeQ16ExposureRequest.program]
                      · simpa [advanced, terminal, bindOracleMachine] using
                          ih next
              | q16SamplerAbortReject counter =>
                  simp only [structuralFutureFreeReply,
                    futureFreeReplyProgram, bindOracleMachine]
                  cases advanced : advanceFutureFreeVerifier environment state
                      .none with
                  | none =>
                      simp [advanced, bindOracleMachine,
                        FutureFreeQ16ExposureRequest.program]
                  | some next =>
                      by_cases terminal : isDriverHalt next.current.control
                      · simp [advanced, terminal, bindOracleMachine,
                          FutureFreeQ16ExposureRequest.program]
                      · simpa [advanced, terminal, bindOracleMachine] using
                          ih next
              | q16AllNoncompactReject =>
                  simp only [structuralFutureFreeReply,
                    futureFreeReplyProgram, bindOracleMachine]
                  cases advanced : advanceFutureFreeVerifier environment state
                      .none with
                  | none =>
                      simp [advanced, bindOracleMachine,
                        FutureFreeQ16ExposureRequest.program]
                  | some next =>
                      by_cases terminal : isDriverHalt next.current.control
                      · simp [advanced, terminal, bindOracleMachine,
                          FutureFreeQ16ExposureRequest.program]
                      · simpa [advanced, terminal, bindOracleMachine] using
                          ih next
              | terminal =>
                  simp only [structuralFutureFreeReply,
                    futureFreeReplyProgram, bindOracleMachine]
                  cases advanced : advanceFutureFreeVerifier environment state
                      .none with
                  | none =>
                      simp [advanced, bindOracleMachine,
                        FutureFreeQ16ExposureRequest.program]
                  | some next =>
                      by_cases terminal : isDriverHalt next.current.control
                      · simp [advanced, terminal, bindOracleMachine,
                          FutureFreeQ16ExposureRequest.program]
                      · simpa [advanced, terminal, bindOracleMachine] using
                          ih next

/-- The same erasure theorem holds at either monitor phase. -/
theorem seek_future_free_q16_exposure_program_exact
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (cursor : FutureFreeQ16ExposureCursor) :
    (seekFutureFreeQ16Exposure environment raw cursor).program environment raw =
      cursor.program environment raw := by
  cases cursor with
  | drive fuel state =>
      exact seek_drive_q16_exposure_program_exact environment raw fuel state
  | squeezeAdvance fuel state output =>
      simp only [seekFutureFreeQ16Exposure,
        FutureFreeQ16ExposureRequest.program,
        FutureFreeQ16ExposureCursor.program]
      apply congrArg (fun continuation =>
        OracleMachine.query
          (bytes state.current.core.digest ++ [domAdvance]) continuation)
      funext advance
      exact continue_after_verifier_reply_program_exact environment raw fuel
        state (.squeeze output advance)
  | stopped program => rfl

/-- The current causal label. -/
def futureFreeQ16PreferredSlot
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (cursor : FutureFreeQ16ExposureCursor) : Option Q16DigestSlot :=
  match seekFutureFreeQ16Exposure environment raw cursor with
  | .halted _ => none
  | .query slot _ _ => slot

/-- Advance by the supplied answer only after its destination has been
selected. -/
def futureFreeQ16AfterAnswer
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (cursor : FutureFreeQ16ExposureCursor) (answer : Digest256) :
    FutureFreeQ16ExposureCursor :=
  match seekFutureFreeQ16Exposure environment raw cursor with
  | .halted program => .stopped program
  | .query _slot _input next => next answer

/-- The exact future-free verifier is therefore a pre-answer slot machine. -/
def futureFreeQ16SlotMachine
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages) :
    PreAnswerSlotMachine Digest256 Q16DigestSlot
      FutureFreeQ16ExposureCursor where
  preferredSlot := futureFreeQ16PreferredSlot environment raw
  afterAnswer := futureFreeQ16AfterAnswer environment raw

@[simp] theorem squeeze_advance_has_no_q16_label
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (fuel : Nat) (state : FutureFreeVerifierState) (output : Digest256) :
    futureFreeQ16PreferredSlot environment raw
      (.squeezeAdvance fuel state output) = none := by
  rfl

/-- At an exposed bounded q16 sample the pre-answer label is the literal
candidate and already-consumed block count. -/
theorem exposed_q16_sample_has_exact_pre_answer_slot
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (cursor : FutureFreeQ16ExposureCursor)
    (fuel : Nat) (state : FutureFreeVerifierState)
    (base : Digest256) (counter : Fin 64) (outputs : List Digest256)
    (remaining : List FutureFreeSlot)
    (exposed : seekFutureFreeQ16Exposure environment raw cursor =
      .query (currentQ16DigestSlot? state)
        (bytes state.current.core.digest ++ [domSqueeze])
        (fun output => .squeezeAdvance fuel state output))
    (controlExact : state.current.control =
      .q16Sample base counter outputs remaining)
    (bounded : Q16SnapshotSlotBound state.current) :
    futureFreeQ16PreferredSlot environment raw cursor =
      some (q16DigestSlotOfBoundedSnapshot state.current base counter outputs
        remaining controlExact bounded) := by
  rw [futureFreeQ16PreferredSlot, exposed]
  exact current_q16_digest_slot_eq_bounded_snapshot state base counter outputs
    remaining controlExact bounded

#print axioms current_q16_digest_slot_eq_bounded_snapshot
#print axioms seek_drive_q16_exposure_program_exact
#print axioms seek_future_free_q16_exposure_program_exact
#print axioms squeeze_advance_has_no_q16_label
#print axioms exposed_q16_sample_has_exact_pre_answer_slot

end

end AspisK1.V7Tag73FutureFreeQ16ExposureMachine
