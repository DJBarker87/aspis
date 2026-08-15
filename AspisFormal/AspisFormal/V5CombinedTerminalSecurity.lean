import AspisFormal.V5AdaptiveSumcheckChallengeBound
import AspisFormal.V5SequentialTerminalChallengeBound
import AspisFormal.SoundnessLedger

/-!
# Combined ideal bound for the V5 terminal argument

Two independent pieces of finite-field accounting now cover the terminal
argument for one trace fixed before its challenges:

* `35 / |K|` for theta, the ten-coordinate equality point, and mu; and
* `270 / |K|` for the ten adaptive degree-27 sumcheck rounds.

This file combines them without merging their causality requirements. The
result is `305 / |K|`. For the released four-limb M31 extension cardinality,
that is at most `2^-115`.

The production theorem remains conditional on one explicit probability
comparison. That comparison is where SHA-256 random-oracle behavior, field
sampling, source correspondence, and commitment-before-challenge facts must
be established; it is not inferred from the finite-field arithmetic.
-/

namespace AspisV5CombinedTerminalSecurity

open AspisFormal.ArithmetizationCore
open AspisV5AdaptiveSumcheckChallengeBound
open AspisV5FriFixedFamilyExperiment
open AspisV5SequentialTerminalChallengeBound

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Algebra F K]

/-- Sum of the two exact ideal experiments; the definitions keep their
different challenge schedules visible. -/
noncomputable def combinedIdealTerminalFailureProbability
    (terminal : FixedTerminalAlgebraPlan K)
    (sumcheck : AdaptiveDegree27MessagePlan K) : Rat :=
  terminalAlgebraFailureProbability terminal +
    adaptiveTenRoundRepairProbability sumcheck

/-- Complete ideal terminal arithmetic for one prefix-fixed trace. -/
theorem combinedIdealTerminalFailureProbability_le
    (terminal : FixedTerminalAlgebraPlan K)
    (sumcheck : AdaptiveDegree27MessagePlan K) :
    combinedIdealTerminalFailureProbability terminal sumcheck ≤
      (305 : Rat) / Fintype.card K := by
  calc
    combinedIdealTerminalFailureProbability terminal sumcheck ≤
        (35 : Rat) / Fintype.card K +
          (270 : Rat) / Fintype.card K :=
      add_le_add (terminalAlgebraFailureProbability_le terminal)
        (adaptiveTenRoundRepairProbability_le sumcheck)
    _ = (305 : Rat) / Fintype.card K := by ring

/-- At the released QM31 cardinality, the full ideal terminal subtotal is at
most `2^-115`. This is not a deployed theft-resistance bound. -/
theorem qm31_combined_ideal_terminal_le_two_pow_neg_115 :
    (305 : Real) / AspisSoundnessLedger.FIELD ≤
      (1 : Real) / 2 ^ 115 := by
  unfold AspisSoundnessLedger.FIELD
  norm_num

/-- Exact production boundary for transferring a concrete finite event to
the two ideal experiments. -/
structure ProductionCombinedTerminalConnection
    (Coins : Type*) [Fintype Coins] [DecidableEq Coins] [Nonempty Coins]
    (productionFailure : Finset Coins)
    (terminal : FixedTerminalAlgebraPlan K)
    (sumcheck : AdaptiveDegree27MessagePlan K)
    (hashSamplingAndSourceGap : Rat) : Prop where
  gapNonnegative : 0 ≤ hashSamplingAndSourceGap
  production_le_ideal_plus_gap :
    finiteUniformEventProbability productionFailure ≤
      combinedIdealTerminalFailureProbability terminal sumcheck +
        hashSamplingAndSourceGap

/-- A production event inherits `305 / |K|` only after the explicit
source/random-oracle reduction above is supplied. -/
theorem productionCombinedTerminalFailureProbability_le
    {Coins : Type*} [Fintype Coins] [DecidableEq Coins] [Nonempty Coins]
    (productionFailure : Finset Coins)
    (terminal : FixedTerminalAlgebraPlan K)
    (sumcheck : AdaptiveDegree27MessagePlan K)
    (hashSamplingAndSourceGap : Rat)
    (connection : ProductionCombinedTerminalConnection Coins
      productionFailure terminal sumcheck hashSamplingAndSourceGap) :
    finiteUniformEventProbability productionFailure ≤
      (305 : Rat) / Fintype.card K + hashSamplingAndSourceGap := by
  exact connection.production_le_ideal_plus_gap.trans
    (add_le_add
      (combinedIdealTerminalFailureProbability_le terminal sumcheck)
      le_rfl)

#print axioms combinedIdealTerminalFailureProbability_le
#print axioms qm31_combined_ideal_terminal_le_two_pow_neg_115
#print axioms productionCombinedTerminalFailureProbability_le

end AspisV5CombinedTerminalSecurity
