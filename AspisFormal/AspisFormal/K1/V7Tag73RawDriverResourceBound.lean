import AspisFormal.K1.V7Tag73RawVerifierExecution

/-!
# Query bound for the raw future-free Tag-73 driver

Every driver microstep is either a zero-query prover submission, a structural
verifier marker, a one-query absorb/root/work action, or one atomic two-query
squeeze.  Consequently a fuel-`n` driver path makes at most `2*n` SHA calls.
This is a deterministic runtime bound, not a probability or acceptance
statement.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73RawDriverResourceBound

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73ReturnedPlanSemantics
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73RawVerifierExecution

/-! ## At most two calls in one forced action -/

private theorem single_input_or_abort_path_length_le_one
    (inputs : List ShaInput) (pairs : List (ShaInput × ShaOutput))
    (reply : VerifierReply)
    (path : MachineQueryPath
      (match inputs with
      | [input] => .query input fun output => .pure (.single output)
      | _ => .abort .controllerRefused) pairs reply) :
    pairs.length ≤ 1 := by
  cases inputs with
  | nil => cases path
  | cons input rest =>
      cases rest with
      | nil =>
          cases path with
          | query _ _ output tailPairs _ tail =>
              cases tail
              simp
      | cons second more => cases path

theorem future_free_reply_program_path_length_le_two
    (state : FutureFreeVerifierState) (action : VerifierAction)
    (pairs : List (ShaInput × ShaOutput)) (reply : VerifierReply)
    (path : MachineQueryPath (futureFreeReplyProgram state action)
      pairs reply) :
    pairs.length ≤ 2 := by
  unfold futureFreeReplyProgram at path
  cases structural : structuralFutureFreeReply action with
  | some structuralReply =>
      rw [structural] at path
      cases path
      simp
  | none =>
      rw [structural] at path
      cases action with
      | absorb payload =>
          exact (single_input_or_abort_path_length_le_one
            (actionInputs state.current.bindings state.current.core
              (.absorb payload)) pairs reply path).trans (by omega)
      | requestRootSalt tree =>
          exact (single_input_or_abort_path_length_le_one
            (actionInputs state.current.bindings state.current.core
              (.requestRootSalt tree)) pairs reply path).trans (by omega)
      | absorbC1 root =>
          exact (single_input_or_abort_path_length_le_one
            (actionInputs state.current.bindings state.current.core
              (.absorbC1 root)) pairs reply path).trans (by omega)
      | absorbC2 lambda chi commitment =>
          exact (single_input_or_abort_path_length_le_one
            (actionInputs state.current.bindings state.current.core
              (.absorbC2 lambda chi commitment)) pairs reply path).trans
                (by omega)
      | squeezePair owner block =>
          cases path with
          | query _ _ output tailPairs _ tail =>
              cases tail with
              | query _ _ advance rest _ finish =>
                  cases finish
                  simp
      | workProbe stage nonce kind =>
          exact (single_input_or_abort_path_length_le_one
            (actionInputs state.current.bindings state.current.core
              (.workProbe stage nonce kind)) pairs reply path).trans (by omega)
      | checkpoint checkpoint => simp [structuralFutureFreeReply] at structural
      | markQ16Base => simp [structuralFutureFreeReply] at structural
      | q16CandidateAbsorb counter outcome selected =>
          exact (single_input_or_abort_path_length_le_one
            (actionInputs state.current.bindings state.current.core
              (.q16CandidateAbsorb counter outcome selected)) pairs reply path).trans
                (by omega)
      | q16Restore counter => simp [structuralFutureFreeReply] at structural
      | q16Selected counter => simp [structuralFutureFreeReply] at structural
      | q16SamplerAbortReject counter =>
          simp [structuralFutureFreeReply] at structural
      | q16AllNoncompactReject =>
          simp [structuralFutureFreeReply] at structural
      | terminal => simp [structuralFutureFreeReply] at structural

theorem run_one_future_free_verifier_action_path_length_le_two
    (environment : FutureFreeEnvironment)
    (state result : FutureFreeVerifierState)
    (pairs : List (ShaInput × ShaOutput))
    (path : MachineQueryPath
      (runOneFutureFreeVerifierAction environment state) pairs result) :
    pairs.length ≤ 2 := by
  unfold runOneFutureFreeVerifierAction at path
  split at path
  next noAction =>
    cases path
    simp
  next action forced =>
    obtain ⟨reply, headPairs, tailPairs, replyPath, tailPath, pairsExact⟩ :=
      machine_query_path_bind_split
        (futureFreeReplyProgram state action)
        (fun reply =>
          match advanceFutureFreeVerifier environment state reply with
          | some next => .pure next
          | none => .abort .controllerRefused)
        pairs result path
    cases advanced : advanceFutureFreeVerifier environment state reply with
    | none =>
        simp [advanced] at tailPath
        cases tailPath
    | some next =>
        simp [advanced] at tailPath
        cases tailPath
        simp only [List.append_nil] at pairsExact
        subst pairs
        exact future_free_reply_program_path_length_le_two state action
          headPairs reply replyPath

theorem raw_future_free_microstep_path_length_le_two
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (state result : FutureFreeVerifierState)
    (pairs : List (ShaInput × ShaOutput))
    (path : MachineQueryPath
      (rawFutureFreeMicrostep environment raw state) pairs result) :
    pairs.length ≤ 2 := by
  unfold rawFutureFreeMicrostep at path
  split at path
  next next submitted =>
    cases path
    simp
  next noSubmission =>
    exact run_one_future_free_verifier_action_path_length_le_two environment
      state result pairs path

/-! ## Global fuel bound -/

theorem drive_raw_future_free_path_length_le_two_mul_fuel
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages) :
    ∀ fuel state pairs result,
      MachineQueryPath (driveRawFutureFree environment raw fuel state)
        pairs result →
      pairs.length ≤ 2 * fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro state pairs result path
      cases path
      simp
  | succ fuel ih =>
      intro state pairs result path
      simp only [driveRawFutureFree] at path
      obtain ⟨next, headPairs, tailPairs, headPath, tailPath, pairsExact⟩ :=
        machine_query_path_bind_split
          (rawFutureFreeMicrostep environment raw state)
          (fun next =>
            if isDriverHalt next.current.control then .pure next
            else driveRawFutureFree environment raw fuel next)
          pairs result path
      have headBound := raw_future_free_microstep_path_length_le_two
        environment raw state next headPairs headPath
      rw [pairsExact, List.length_append]
      by_cases terminal : isDriverHalt next.current.control
      · simp [terminal] at tailPath
        cases tailPath
        simp only [List.length_nil, Nat.add_zero, Nat.mul_add,
          Nat.mul_one]
        omega
      · simp [terminal] at tailPath
        have tailBound := ih next tailPairs result tailPath
        simp only [Nat.mul_add, Nat.mul_one]
        omega

theorem initial_raw_future_free_path_length_le_two_mul_fuel
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (fuel : Nat) (pairs : List (ShaInput × ShaOutput))
    (result : FutureFreeVerifierState)
    (path : MachineQueryPath
      (initialRawFutureFreeProgram environment raw fuel) pairs result) :
    pairs.length ≤ 2 * fuel := by
  exact drive_raw_future_free_path_length_le_two_mul_fuel environment raw fuel
    (initialFutureFreeVerifierState (FixedBindings.ofContext raw.context))
    pairs result path

/-- The actual returned two-phase execution inherits the exact driver-fuel
query ceiling. -/
theorem raw_verifier_execution_query_path_length_le_two_mul_driver_fuel
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : RawVerifierExecution source) :
    execution.verifierHistory.length ≤ 2 * execution.driverFuel := by
  obtain ⟨pairs, path, history, _actors, _answers⟩ :=
    raw_verifier_execution_has_exact_query_path execution
  have bound := initial_raw_future_free_path_length_le_two_mul_fuel
    execution.environment execution.adversaryValue.rawMessages
    execution.driverFuel pairs execution.finalState path
  have lengthEquality : execution.verifierHistory.length = pairs.length := by
    simpa [queryAnswerTrace] using congrArg List.length history
  exact lengthEquality.trans_le bound

#print axioms future_free_reply_program_path_length_le_two
#print axioms run_one_future_free_verifier_action_path_length_le_two
#print axioms raw_future_free_microstep_path_length_le_two
#print axioms drive_raw_future_free_path_length_le_two_mul_fuel
#print axioms initial_raw_future_free_path_length_le_two_mul_fuel
#print axioms raw_verifier_execution_query_path_length_le_two_mul_driver_fuel

end AspisK1.V7Tag73RawDriverResourceBound
