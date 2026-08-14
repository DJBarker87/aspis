import AspisFormal.V5AcceptedExecutionReleasedFinalAccounting
import AspisFormal.V5RawFinalSecurityAccounting

/-!
# Raw accounting for the released accepted-execution reduction

The released accepted-execution theorem already places every false accepted
execution in the common 24-branch failure ledger.  This file composes that
deterministic result with the raw, non-work-normalized arithmetic.

The conclusion is deliberately conditional.  `AssumedRawFinalSecurityBounds`
must still connect the actual experiment to each ideal event and assign bounds
to every Rust, hash, extraction, credential, and Solana-runtime failure.  In a
multi-attempt attack, the caller must additionally account for the number and
timing of attempts; this theorem does not silently treat one-proof probability
as an all-time attacker bound.
-/

namespace AspisV5AcceptedExecutionReleasedRawAccounting

open MeasureTheory
open AspisCircleGroupOrder
open AspisV5AcceptedExecutionReleasedFinalAccounting
open AspisV5FinalSecurityAccounting
open AspisV5RawFinalSecurityAccounting
open AspisV5FriConcreteEncoderCommutation

/-- Exact raw subtotal, before replacing it by the coarser power-of-two
endpoint. -/
theorem released_attack_probability_le_raw_core_plus_external
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    [MeasurableSpace Coins]
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    (events : FinalSecurityEvents Coins)
    (failure : ReleasedAcceptedExecutionFailurePredicates Coins K)
    (attack : Set Coins)
    (attackReduces : attack ⊆ {coins | failure.Occurs coins})
    (coverage : ReleasedAcceptedExecutionFailureCoverage events failure)
    (budget : ExternalSecurityBudget)
    (assumed : AssumedRawFinalSecurityBounds measure events budget) :
    measure.real attack ≤ rawCoreSubtotal + budget.total := by
  have covered : attack ⊆ totalFinalFailure events :=
    Set.Subset.trans attackReduces
      (released_accepted_execution_failure_subset_total events failure
        coverage)
  exact raw_attack_probability_le_core_plus_external measure events attack
    covered budget assumed

/-- Conservative 75-bit raw ideal-core endpoint, with every external term
still shown as an explicit summand. -/
theorem released_attack_probability_le_two_pow_neg_75_plus_external
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    [MeasurableSpace Coins]
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    (events : FinalSecurityEvents Coins)
    (failure : ReleasedAcceptedExecutionFailurePredicates Coins K)
    (attack : Set Coins)
    (attackReduces : attack ⊆ {coins | failure.Occurs coins})
    (coverage : ReleasedAcceptedExecutionFailureCoverage events failure)
    (budget : ExternalSecurityBudget)
    (assumed : AssumedRawFinalSecurityBounds measure events budget) :
    measure.real attack ≤ (1 : Real) / 2 ^ 75 + budget.total := by
  have covered : attack ⊆ totalFinalFailure events :=
    Set.Subset.trans attackReduces
      (released_accepted_execution_failure_subset_total events failure
        coverage)
  exact raw_attack_probability_le_two_pow_neg_75_plus_external measure events
    attack covered budget assumed

#print axioms released_attack_probability_le_raw_core_plus_external
#print axioms released_attack_probability_le_two_pow_neg_75_plus_external

end AspisV5AcceptedExecutionReleasedRawAccounting
