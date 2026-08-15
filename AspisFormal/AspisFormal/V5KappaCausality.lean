import AspisFormal.V5FourClaimBatchUnion
import AspisFormal.V5TranscriptConnection

/-!
# The batching challenge is sampled after its inputs

The four-claim collision bound requires the candidate discrepancies to be
fixed before `kappa` is sampled.  This file proves the corresponding exact
ordering fact for the maintained V5 transcript schedule.  It does not by
itself prove that production Rust constructs the same candidate records; that
source connection remains separate.
-/

namespace AspisV5KappaCausality

open AspisV5TranscriptConnection

/-- Transcript operations that fix the roots, public statement, point claims,
terminal claims, gamma weights, and inactive claim used to construct the
four pre-kappa discrepancies. -/
def kappaPrerequisiteSteps : List ScheduleStep :=
  [.absorb .statement,
    .absorb (.circleRoot 0),
    .absorb .c2Root,
    .absorb .relationPoints,
    .absorb .statementEvaluations,
    .absorb .terminalClaims,
    .verifyWork .batch,
    .absorb .batchNonce,
    .squeeze .gamma,
    .absorb .inactiveClaim]

/-- `kappa` is the final operation of the prefix driver. -/
theorem kappa_is_last_prefix_operation :
    prefixSchedule.getLast? = some (.squeeze .kappa) := by
  decide

/-- The prefix driver samples `kappa` exactly once. -/
theorem kappa_occurs_exactly_once_in_prefix :
    prefixSchedule.count (.squeeze .kappa) = 1 := by
  decide

/-- Every byte/challenge input needed for the four individual claim
discrepancies occurs strictly before the unique `kappa` squeeze. -/
theorem every_batch_input_precedes_kappa :
    ∀ step ∈ kappaPrerequisiteSteps,
      prefixSchedule.idxOf step < prefixSchedule.idxOf (.squeeze .kappa) := by
  decide

/-! ## Audit -/

#print axioms kappa_is_last_prefix_operation
#print axioms kappa_occurs_exactly_once_in_prefix
#print axioms every_batch_input_precedes_kappa

end AspisV5KappaCausality
