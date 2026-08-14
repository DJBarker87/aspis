import AspisFormal.V5FriGlobalCausalStrategy

/-!
# The fixed-family adaptive FRI experiment

The adaptive FRI count is valid only after one base schedule and one causal
transcript family have been fixed.  The backwards strategy must then also be
fixed before the four challenges are sampled.  This file packages exactly
that experiment using `constructedAdaptiveStrategies base family`.

There is no existential quantifier over a transcript family or a strategy in
the event below.  In particular, a different family or strategy cannot be
chosen for each sampled challenge tuple.

The final section names the separate production/Fiat--Shamir boundary.  The
existing `FamilyMatchesFriTranscript` proposition is a statement about the
one actual challenge tuple: it does not show that all counterfactual
transcripts come from one causal family fixed before challenge sampling.
-/

namespace AspisV5FriFixedFamilyExperiment

open AspisCircleGroupOrder
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriAdaptiveUnmatched
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriGlobalCausalStrategy
open AspisV5FriPublishedOutputEncoderDecoding
open AspisV5FriReleasedAdaptiveExtraction
open AspisV5FriReleasedLineGeometry

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K] [NeZero (2 : K)]

/-! ## One fixed mathematical experiment -/

/-- The four suffix-conditioned bad fibres for one fixed schedule, one fixed
causal transcript family, and the strategy constructed from that family. -/
noncomputable def fixedFamilyBadSets
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)) :
    SuffixConditionedBadSets K releasedChallengeCap :=
  adaptiveBadSets base family hfinal htables hpublished
    (constructedAdaptiveStrategies base family)

/-- The finite event on the full four-challenge space. -/
noncomputable def fixedFamilyBadChallengeTuples
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)) :
    Finset (FourChallenges K) :=
  allBadChallengeTuples
    (fixedFamilyBadSets base family hfinal htables hpublished)

/-- Pointwise form of the same fixed event. -/
def FixedFamilyBadChallengeOccurs
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (z0 z1 z2 z3 : K) : Prop :=
  (fixedFamilyBadSets base family hfinal htables hpublished).Occurs
    z0 z1 z2 z3

@[simp] theorem mem_fixedFamilyBadChallengeTuples_iff
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (z0 z1 z2 z3 : K) :
    (((z0, z1), z2), z3) ∈
        fixedFamilyBadChallengeTuples base family hfinal htables hpublished ↔
      FixedFamilyBadChallengeOccurs base family hfinal htables hpublished
        z0 z1 z2 z3 := by
  simp [fixedFamilyBadChallengeTuples, FixedFamilyBadChallengeOccurs]

/-- The exact four-fibre union bound for the one fixed family and its one
constructed strategy. -/
theorem fixedFamilyBadChallengeTuples_card_le
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)) :
    (fixedFamilyBadChallengeTuples base family hfinal htables hpublished).card ≤
      Fintype.card K ^ 3 *
        (releasedChallengeCap 0 + releasedChallengeCap 1 +
          releasedChallengeCap 2 + releasedChallengeCap 3) := by
  simpa only [fixedFamilyBadChallengeTuples, fixedFamilyBadSets] using
    constructed_adaptiveBadChallengeTuples_card_le
      base family hfinal htables hpublished

/-- Exact mass of the fixed event under four independent uniform field
challenges. -/
noncomputable def fixedFamilyUniformBadProbability
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)) : Rat :=
  uniformBadChallengeProbability
    (fixedFamilyBadSets base family hfinal htables hpublished)

theorem fixedFamilyUniformBadProbability_eq_card_ratio
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)) :
    fixedFamilyUniformBadProbability base family hfinal htables hpublished =
      (fixedFamilyBadChallengeTuples base family hfinal htables hpublished).card /
        Fintype.card K ^ 4 := by
  rfl

/-- Uniform probability bound for the fixed family and the single strategy
constructed from it. -/
theorem fixedFamilyUniformBadProbability_le
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)) :
    fixedFamilyUniformBadProbability base family hfinal htables hpublished ≤
      (releasedChallengeCap 0 + releasedChallengeCap 1 +
        releasedChallengeCap 2 + releasedChallengeCap 3 : Rat) /
          Fintype.card K := by
  simpa only [fixedFamilyUniformBadProbability, fixedFamilyBadSets] using
    adaptiveBadChallengeProbability_le base family hfinal htables hpublished
      (constructedAdaptiveStrategies base family)

/-- Existential quantification over proofs of the three fixed mathematical
facts does not enlarge the event.  This lemma is useful because the general
accepted-execution theorem exposes those facts as witnesses while retaining
the same fixed family and constructed strategy. -/
theorem exists_proof_witnesses_iff_fixedFamilyBadChallengeOccurs
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (z0 z1 z2 z3 : K) :
    (∃ (hfinal' : FinalXMatchesReleasedDomain base)
        (htables' : InverseTablesMatch base releasedEvaluationPoints)
        (hpublished' : PublishedOrdinaryPolynomialCurveDecoding (K := K)),
      (adaptiveBadSets base family hfinal' htables' hpublished'
        (constructedAdaptiveStrategies base family)).Occurs z0 z1 z2 z3) ↔
      FixedFamilyBadChallengeOccurs base family hfinal htables hpublished
        z0 z1 z2 z3 := by
  constructor
  · rintro ⟨hfinal', htables', hpublished', hbad⟩
    have hfinalEq : hfinal' = hfinal := Subsingleton.elim _ _
    have htablesEq : htables' = htables := Subsingleton.elim _ _
    have hpublishedEq : hpublished' = hpublished := Subsingleton.elim _ _
    subst hfinal'
    subst htables'
    subst hpublished'
    exact hbad
  · intro hbad
    exact ⟨hfinal, htables, hpublished, hbad⟩

/-! ## Explicit production and Fiat--Shamir boundary -/

/-- Interpret a nested four-challenge tuple as the complete transcript from
the fixed causal family. -/
def fullTranscriptForTuple (family : CausalTranscriptFamily K)
    (challenges : FourChallenges K) : IdealTranscript K :=
  fullTranscript family challenges.1.1.1 challenges.1.1.2
    challenges.1.2 challenges.2

/-- A counterfactual transcript projection agrees with one fixed causal
family on every challenge tuple, not merely on the tuple observed in one
accepted execution. -/
def CounterfactualTranscriptsMatchFixedFamily
    (family : CausalTranscriptFamily K)
    (counterfactualTranscript : FourChallenges K -> IdealTranscript K) : Prop :=
  ∀ challenges,
    counterfactualTranscript challenges = fullTranscriptForTuple family challenges

/-- Uniform probability of an event in a finite experiment. -/
noncomputable def finiteUniformEventProbability
    {Coins : Type*} [Fintype Coins] (event : Finset Coins) : Rat :=
  event.card / Fintype.card Coins

theorem finiteUniformEventProbability_mono
    {Coins : Type*} [Fintype Coins] [DecidableEq Coins] [Nonempty Coins]
    {left right : Finset Coins} (hsubset : left ⊆ right) :
    finiteUniformEventProbability left ≤ finiteUniformEventProbability right := by
  unfold finiteUniformEventProbability
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Finset.card_le_card hsubset
  · positivity

/-- The boundary still required to use the ideal fixed-family count for a
production Fiat--Shamir execution.

`Coins` represents the random coins of the production security experiment.
The fields separately require:

1. every projected counterfactual transcript to follow one fixed causal
   family;
2. each projected production transcript to equal the corresponding member of
   that counterfactual family at its sampled challenge tuple;
3. every production failure under study to map to that family's fixed bad
   challenge event; and
4. the hash-derived challenge distribution's pullback of that event to have
   no more mass than four independent uniform field challenges.

None of these fields is supplied by the pointwise
`FamilyMatchesFriTranscript` proposition. -/
structure ProductionFiatShamirFixedFamilyConnection
    (Coins : Type*) [Fintype Coins] [DecidableEq Coins] [Nonempty Coins]
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (counterfactualTranscript : FourChallenges K -> IdealTranscript K)
    (projectedProductionTranscript : Coins -> IdealTranscript K)
    (productionChallengeTuple : Coins -> FourChallenges K)
    (productionFailure : Finset Coins) : Prop where
  counterfactualFamily :
    CounterfactualTranscriptsMatchFixedFamily family counterfactualTranscript
  productionTranscriptAtSampledTuple :
    ∀ coins, projectedProductionTranscript coins =
      counterfactualTranscript (productionChallengeTuple coins)
  productionFailureMapsToFixedEvent :
    productionFailure ⊆ Finset.univ.filter (fun coins =>
      productionChallengeTuple coins ∈
        fixedFamilyBadChallengeTuples base family hfinal htables hpublished)
  fiatShamirPullbackLeUniform :
    finiteUniformEventProbability
        (Finset.univ.filter (fun coins =>
          productionChallengeTuple coins ∈
            fixedFamilyBadChallengeTuples base family hfinal htables hpublished)) ≤
      fixedFamilyUniformBadProbability base family hfinal htables hpublished

/-- Once the named production/Fiat--Shamir connection is supplied, the
production failure event inherits the proved fixed-family uniform bound. -/
theorem productionFailureProbability_le_fixedFamilyBound
    {Coins : Type*} [Fintype Coins] [DecidableEq Coins] [Nonempty Coins]
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (counterfactualTranscript : FourChallenges K -> IdealTranscript K)
    (projectedProductionTranscript : Coins -> IdealTranscript K)
    (productionChallengeTuple : Coins -> FourChallenges K)
    (productionFailure : Finset Coins)
    (connection : ProductionFiatShamirFixedFamilyConnection Coins base family
      hfinal htables hpublished counterfactualTranscript
      projectedProductionTranscript productionChallengeTuple
      productionFailure) :
    finiteUniformEventProbability productionFailure ≤
      (releasedChallengeCap 0 + releasedChallengeCap 1 +
        releasedChallengeCap 2 + releasedChallengeCap 3 : Rat) /
          Fintype.card K := by
  exact (finiteUniformEventProbability_mono
      connection.productionFailureMapsToFixedEvent).trans
    (connection.fiatShamirPullbackLeUniform.trans
      (fixedFamilyUniformBadProbability_le base family hfinal htables
        hpublished))

#print axioms fixedFamilyBadChallengeTuples_card_le
#print axioms fixedFamilyUniformBadProbability_le
#print axioms exists_proof_witnesses_iff_fixedFamilyBadChallengeOccurs
#print axioms finiteUniformEventProbability_mono
#print axioms productionFailureProbability_le_fixedFamilyBound

end AspisV5FriFixedFamilyExperiment
