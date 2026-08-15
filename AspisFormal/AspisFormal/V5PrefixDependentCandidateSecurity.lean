import AspisFormal.V5CandidateTerminalSecurity

/-!
# Terminal security for a candidate list chosen from a transcript prefix

The released decoder's candidate list need not be one globally fixed type.
It may depend on data fixed before the terminal challenges.  This file proves
the corresponding conditional averaging step: if every prefix produces at
most 240 candidates, and each candidate has the checked `305 / |K|` terminal
bound, then averaging over all prefixes still costs at most
`73200 / |K|`.

The number of possible prefixes does not multiply the bound.  Prefixes are
averaged, while candidates within each prefix are union-bounded.

This is an ideal finite-field theorem.  Applying it to production still needs
an explicit comparison showing that the decoder list and algebra plans are
fixed by the prefix and that later Fiat--Shamir answers have the required
conditional distribution.
-/

namespace AspisV5PrefixDependentCandidateSecurity

open scoped BigOperators
open AspisFormal.ArithmetizationCore
open AspisV5AdaptiveSumcheckChallengeBound
open AspisV5CandidateTerminalSecurity
open AspisV5CombinedTerminalSecurity
open AspisV5FriFixedFamilyExperiment
open AspisV5SequentialTerminalChallengeBound

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Algebra F K]

/-- For each prefix, sum the checked one-candidate terminal probabilities;
then average those subtotals over prefixes. -/
noncomputable def prefixAveragedCandidateTerminalSubtotal
    (Prefix : Type*) [Fintype Prefix] [Nonempty Prefix]
    (CandidateAt : Prefix → Type*)
    [candidateFintype : ∀ p : Prefix, Fintype (CandidateAt p)]
    (terminal : ∀ p, CandidateAt p → FixedTerminalAlgebraPlan K)
    (sumcheck : ∀ p,
      CandidateAt p → AdaptiveDegree27MessagePlan K) : Rat :=
  (∑ p,
      candidateCombinedIdealTerminalSubtotal (CandidateAt p)
        (terminal p) (sumcheck p)) /
    Fintype.card Prefix

/-- A prefix-dependent list cap is enough: averaging over prefixes preserves
the same cap-240 terminal subtotal as a single fixed list. -/
theorem prefixAveragedCandidateTerminalSubtotal_le_240
    (Prefix : Type*) [Fintype Prefix] [Nonempty Prefix]
    (CandidateAt : Prefix → Type*)
    [candidateFintype : ∀ p : Prefix, Fintype (CandidateAt p)]
    (terminal : ∀ p, CandidateAt p → FixedTerminalAlgebraPlan K)
    (sumcheck : ∀ p,
      CandidateAt p → AdaptiveDegree27MessagePlan K)
    (candidateCap : ∀ p, Fintype.card (CandidateAt p) ≤ 240) :
    prefixAveragedCandidateTerminalSubtotal Prefix CandidateAt terminal
        sumcheck ≤
      (73200 : Rat) / Fintype.card K := by
  unfold prefixAveragedCandidateTerminalSubtotal
  exact finiteSubsetAverage_le (Finset.univ : Finset Prefix)
    (fun p ↦
      candidateCombinedIdealTerminalSubtotal (CandidateAt p)
        (terminal p) (sumcheck p))
    ((73200 : Rat) / Fintype.card K) (by positivity)
    (fun p _ ↦
      candidateCombinedIdealTerminalSubtotal_le_240 (CandidateAt p)
        (terminal p) (sumcheck p) (candidateCap p))

/-- The exact remaining production comparison for a list chosen from a
prefix.  The comparison is stated separately so source equality, commitment
timing, SHA-256 behavior, and conditional field sampling cannot be mistaken
for consequences of the finite-field count. -/
structure PrefixDependentProductionTerminalConnection
    (Coins Prefix : Type*)
    [Fintype Coins] [DecidableEq Coins] [Nonempty Coins]
    [Fintype Prefix] [Nonempty Prefix]
    (CandidateAt : Prefix → Type*)
    [candidateFintype : ∀ p : Prefix, Fintype (CandidateAt p)]
    (productionFailure : Finset Coins)
    (terminal : ∀ p, CandidateAt p → FixedTerminalAlgebraPlan K)
    (sumcheck : ∀ p,
      CandidateAt p → AdaptiveDegree27MessagePlan K)
    (sourceHashAndConditionalSamplingGap : Rat) : Prop where
  gapNonnegative : 0 ≤ sourceHashAndConditionalSamplingGap
  production_le_prefix_average_plus_gap :
    finiteUniformEventProbability productionFailure ≤
      prefixAveragedCandidateTerminalSubtotal Prefix CandidateAt terminal
          sumcheck +
        sourceHashAndConditionalSamplingGap

/-- Production inherits the cap-240 bound once the precise prefix/source/hash
comparison above is supplied. -/
theorem productionPrefixDependentTerminalFailureProbability_le
    {Coins Prefix : Type*}
    [Fintype Coins] [DecidableEq Coins] [Nonempty Coins]
    [Fintype Prefix] [Nonempty Prefix]
    (CandidateAt : Prefix → Type*)
    [candidateFintype : ∀ p : Prefix, Fintype (CandidateAt p)]
    (productionFailure : Finset Coins)
    (terminal : ∀ p, CandidateAt p → FixedTerminalAlgebraPlan K)
    (sumcheck : ∀ p,
      CandidateAt p → AdaptiveDegree27MessagePlan K)
    (sourceHashAndConditionalSamplingGap : Rat)
    (candidateCap : ∀ p, Fintype.card (CandidateAt p) ≤ 240)
    (connection : PrefixDependentProductionTerminalConnection
      (K := K) Coins Prefix CandidateAt productionFailure terminal sumcheck
      sourceHashAndConditionalSamplingGap) :
    finiteUniformEventProbability productionFailure ≤
      (73200 : Rat) / Fintype.card K +
        sourceHashAndConditionalSamplingGap := by
  exact connection.production_le_prefix_average_plus_gap.trans
    (add_le_add
      (prefixAveragedCandidateTerminalSubtotal_le_240 Prefix CandidateAt
        terminal sumcheck candidateCap)
      le_rfl)

#print axioms prefixAveragedCandidateTerminalSubtotal_le_240
#print axioms productionPrefixDependentTerminalFailureProbability_le

end AspisV5PrefixDependentCandidateSecurity
