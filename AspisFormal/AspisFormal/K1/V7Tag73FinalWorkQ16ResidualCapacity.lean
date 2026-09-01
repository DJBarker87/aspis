import AspisFormal.K1.V7Tag73CausalQ16FinalWorkProbability

/-!
# Exact residual capacity after routing final work and q16 outputs

The joint causal router removes one accepted final-work digest and all 512
potential q16 output blocks from the fixed full-256 compiler tape.  This file
checks that the remaining tape has exactly the reserve required by every
other root, replay, and fork coordinate.

This is accounting only.  The source-continuation proof must still classify
the literal trace coordinates and show that the joint controller assigns the
named slots at their causal first exposures.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73FinalWorkQ16ResidualCapacity

open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ResourceLazyOracle
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Full-width verifier calls left after removing the one routed final-work
digest and every actually consumed q16 output half. -/
def tag73Full256ResidualAfterFinalWorkQ16Calls
    (messages : Messages)
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) : Nat :=
  publicRootSaltOracleCalls +
  acceptedLinearAbsorbOracleCalls +
  2 * challengeBlocksUsed messages +
  (selectedWorkVerifierOracleCalls - 1) +
  q16ResidualOracleCalls search

/-- The deployed full-width verifier count partitions into residual calls,
one final-work digest, and the actually used q16 output coordinates. -/
theorem full256_verifier_calls_split_residual_final_work_and_q16
    (messages : Messages)
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) :
    tag73Full256VerifierOracleCalls messages search =
      tag73Full256ResidualAfterFinalWorkQ16Calls messages search + 1 +
        q16NamedDigestOracleCalls search := by
  rw [tag73Full256VerifierOracleCalls,
    tag73Full256ResidualAfterFinalWorkQ16Calls,
    q16_branch_calls_split_named_and_residual]
  unfold selectedWorkVerifierOracleCalls
  omega

/-- Removing the routed final-work digest lowers the previous 999-call
non-q16 reserve by exactly one. -/
theorem tag73_full256_residual_after_final_work_q16_calls_le_998
    (messages : Messages)
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) :
    tag73Full256ResidualAfterFinalWorkQ16Calls messages search ≤ 998 := by
  have challengeCap := challenge_blocks_used_le_192 messages
  have q16ResidualCap := q16_residual_oracle_calls_le_576 search
  unfold tag73Full256ResidualAfterFinalWorkQ16Calls
    publicRootSaltOracleCalls acceptedLinearAbsorbOracleCalls
    selectedWorkVerifierOracleCalls
  omega

/-- Exact size of the residual component in the 513-slot joint router. -/
theorem exact_compiler_final_work_q16_residual_length_expanded
    (parameters : ExactCompilerResourceParameters) :
    (exactCompilerTargetCaps parameters).length - 513 =
      parameters.q1ShaCallCap + 998 +
        parameters.forkRequestCap *
          (parameters.q1ShaCallCap + 1511) +
        2 * parameters.forkRequestCap := by
  rw [exact_compiler_target_caps_length]
  unfold unifiedFull256ExposureCap full256MachineFreshCap sameTapeStartCap
    deployedFull256VerifierCallCap
  omega

/-- All non-routed coordinates of an accepted execution fit in the exact
joint-router residual.  No padding coordinate needs to steal a still-live
final-work or q16 slot merely because the residual dimension was undersized.
-/
theorem exact_compiler_final_work_q16_residual_covers_execution
    (parameters : ExactCompilerResourceParameters)
    (messages : Messages)
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) :
    parameters.q1ShaCallCap +
        tag73Full256ResidualAfterFinalWorkQ16Calls messages search +
        parameters.forkRequestCap *
          (parameters.q1ShaCallCap + 1511) +
        2 * parameters.forkRequestCap ≤
      (exactCompilerTargetCaps parameters).length - 513 := by
  rw [exact_compiler_final_work_q16_residual_length_expanded]
  have reserve :=
    tag73_full256_residual_after_final_work_q16_calls_le_998 messages search
  omega

#print axioms full256_verifier_calls_split_residual_final_work_and_q16
#print axioms tag73_full256_residual_after_final_work_q16_calls_le_998
#print axioms exact_compiler_final_work_q16_residual_length_expanded
#print axioms exact_compiler_final_work_q16_residual_covers_execution

end

end AspisK1.V7Tag73FinalWorkQ16ResidualCapacity
