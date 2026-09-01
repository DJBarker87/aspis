import AspisFormal.K1.V7Tag73CheckedRefinementFutureFreePath

/-!
# Append-only decoded-challenge ledger

The executable future-free verifier never removes a decoded challenge record.
Ordinary and adaptive samplers append one record on success; every other
prover or verifier transition preserves the ledger.  This file exposes that
small operational fact independently of the higher K1.3 extraction argument.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73DecodedChallengeLedgerMonotonicity

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73CheckedRefinementFutureFreePath
open AspisK1.V7FsAokExperiment

/-- Every decoded record in the first live snapshot remains in the second. -/
def DecodedChallengeLedgerIncluded
    (before after : FutureFreeVerifierState) : Prop :=
  ∀ record, record ∈ before.current.decodedChallenges →
    record ∈ after.current.decodedChallenges

theorem decoded_challenge_ledger_included_refl
    (state : FutureFreeVerifierState) :
    DecodedChallengeLedgerIncluded state state := by
  intro record member
  exact member

theorem decoded_challenge_ledger_included_trans
    {first middle final : FutureFreeVerifierState}
    (firstMiddle : DecodedChallengeLedgerIncluded first middle)
    (middleFinal : DecodedChallengeLedgerIncluded middle final) :
    DecodedChallengeLedgerIncluded first final := by
  intro record member
  exact middleFinal record (firstMiddle record member)

/-- Raw prover submissions only fill prover-owned fields and preserve the
decoded verifier ledger byte for byte. -/
theorem successful_raw_submission_preserves_decoded_challenges
    (raw : RawTag73ProverMessages)
    (state next : FutureFreeVerifierState)
    (submitted : submitNextRawMessage raw state = some next) :
    next.current.decodedChallenges = state.current.decodedChallenges := by
  unfold submitNextRawMessage at submitted
  split at submitted <;>
    simp_all [submitFutureFreeC1, submitFutureFreeC2,
      submitFutureFreePayload, submitFutureFreeWorkNonce,
      appendFutureFreeSnapshot]
  all_goals subst next <;> rfl

/-- A successful raw control update either preserves the challenge ledger or
appends a freshly decoded record. -/
theorem raw_after_reply_preserves_decoded_challenge_membership
    (environment : FutureFreeEnvironment)
    (snapshot next : FutureFreeSnapshot) (reply : VerifierReply)
    (nextCore : RuntimeCore)
    (run : rawAfterFutureFreeVerifierReply environment snapshot reply
      nextCore = some next) :
    ∀ record, record ∈ snapshot.decodedChallenges →
      record ∈ next.decodedChallenges := by
  intro record member
  unfold rawAfterFutureFreeVerifierReply at run
  split at run <;>
    simp_all [processFutureFreeChallengeBlock,
      completeFutureFreeChallenge, processFutureFreeCandidateBlock,
      List.mem_append]
  case h_1 =>
    obtain ⟨nextAdaptive, _adaptiveRun, nextExact⟩ :=
      Option.bind_eq_some_iff.mp run
    have nextEq := Option.some.inj nextExact
    subst next
    split <;> simp_all [List.mem_append] <;>
      split <;> simp_all [List.mem_append]
  all_goals subst next <;>
    try simp_all [processFutureFreeChallengeBlock,
      completeFutureFreeChallenge, processFutureFreeCandidateBlock,
      List.mem_append]
  all_goals split <;> try simp_all [List.mem_append]
  all_goals split <;> try simp_all [List.mem_append]
  all_goals split <;> try simp_all [List.mem_append]

/-- Reinstalling the fixed binding cannot affect the decoded ledger. -/
theorem after_reply_preserves_decoded_challenge_membership
    (environment : FutureFreeEnvironment)
    (snapshot next : FutureFreeSnapshot) (reply : VerifierReply)
    (nextCore : RuntimeCore)
    (run : afterFutureFreeVerifierReply environment snapshot reply nextCore =
      some next) :
    ∀ record, record ∈ snapshot.decodedChallenges →
      record ∈ next.decodedChallenges := by
  intro record member
  unfold afterFutureFreeVerifierReply at run
  cases raw : rawAfterFutureFreeVerifierReply environment snapshot reply
      nextCore with
  | none => simp [raw] at run
  | some candidate =>
      rw [raw] at run
      have nextExact : { candidate with bindings := snapshot.bindings } = next :=
        Option.some.inj run
      rw [← nextExact]
      exact raw_after_reply_preserves_decoded_challenge_membership environment
        snapshot candidate reply nextCore raw record member

theorem advance_future_free_verifier_preserves_decoded_challenge_membership
    (environment : FutureFreeEnvironment)
    (state next : FutureFreeVerifierState) (reply : VerifierReply)
    (run : advanceFutureFreeVerifier environment state reply = some next) :
    DecodedChallengeLedgerIncluded state next := by
  rw [advanceFutureFreeVerifier] at run
  obtain ⟨action, _actionExact, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨nextCore, _coreExact, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨nextSnapshot, snapshotExact, finalExact⟩ :=
    Option.bind_eq_some_iff.mp run
  have nextExact := Option.some.inj finalExact
  subst next
  intro record member
  simpa [appendFutureFreeSnapshot] using
    (after_reply_preserves_decoded_challenge_membership environment
      state.current nextSnapshot reply nextCore snapshotExact record member)

theorem future_free_operational_step_preserves_decoded_challenge_membership
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (state next : FutureFreeVerifierState)
    (pairs : List (ShaInput × ShaOutput))
    (step : FutureFreeOperationalStep environment raw state pairs next) :
    DecodedChallengeLedgerIncluded state next := by
  cases step with
  | prover submitted event snapshot appendExact =>
      intro record member
      rw [successful_raw_submission_preserves_decoded_challenges raw state next
        submitted]
      exact member
  | verifier forced replyPath advanced =>
      exact advance_future_free_verifier_preserves_decoded_challenge_membership
        environment state next _ advanced
  | stutter noSubmission noAction =>
      exact decoded_challenge_ledger_included_refl state

theorem future_free_operational_trace_preserves_decoded_challenge_membership
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (state final : FutureFreeVerifierState)
    (pairs : List (ShaInput × ShaOutput))
    (trace : FutureFreeOperationalTrace environment raw state pairs final) :
    DecodedChallengeLedgerIncluded state final := by
  induction trace with
  | stop current => exact decoded_challenge_ledger_included_refl current
  | next step rest inductionHypothesis =>
      exact decoded_challenge_ledger_included_trans
        (future_free_operational_step_preserves_decoded_challenge_membership
          environment raw _ _ _ step)
        inductionHypothesis

theorem nonterminal_raw_driver_trace_preserves_decoded_challenge_membership
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (state final : FutureFreeVerifierState) (steps : Nat)
    (pairs : List (ShaInput × ShaOutput))
    (trace : NonterminalRawDriverTrace environment raw state steps pairs final) :
    DecodedChallengeLedgerIncluded state final := by
  induction trace with
  | stop current => exact decoded_challenge_ledger_included_refl current
  | @next state middle final head tail steps headPath middleNonterminal rest ih =>
      exact decoded_challenge_ledger_included_trans
        (future_free_operational_step_preserves_decoded_challenge_membership
          environment raw state middle head
          (raw_future_free_microstep_path_is_operational environment raw state
            middle head headPath))
        ih

theorem raw_future_free_microstep_path_preserves_decoded_challenge_membership
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (state next : FutureFreeVerifierState)
    (pairs : List (ShaInput × ShaOutput))
    (path : MachineQueryPath (rawFutureFreeMicrostep environment raw state)
      pairs next) :
    DecodedChallengeLedgerIncluded state next :=
  future_free_operational_step_preserves_decoded_challenge_membership
    environment raw state next pairs
      (raw_future_free_microstep_path_is_operational environment raw state next
        pairs path)

#print axioms
  nonterminal_raw_driver_trace_preserves_decoded_challenge_membership
#print axioms
  raw_future_free_microstep_path_preserves_decoded_challenge_membership

end AspisK1.V7Tag73DecodedChallengeLedgerMonotonicity
