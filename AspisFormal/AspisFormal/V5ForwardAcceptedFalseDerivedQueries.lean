import AspisFormal.V5AcceptedExecutionDerivedQueries
import AspisFormal.V5BoundedQuerySamplerUniformity
import AspisFormal.V5ForwardAcceptedFalseRawAccounting

/-!
# Derived queries in the forward accepted-false experiment

The newest forward/raw accepted-false experiment previously stored an
arbitrary ordered injection `Fin 18 ↪ Fin 131072` at every sample.  This file
replaces that free input with the exact successful output of
`derive18Queries` on the transcript's squeezed blocks.

The finite query bound is then obtained from the proved bounded-sampler
experiment.  The only probabilistic bridge left here says that, conditional
on the transcript prefix which fixes the bad fibre set, the SHA/Fiat--Shamir
query output has at most the corresponding ideal bounded-sampler mass.  This
is a direct conditional law.  It is not an independence assumption.
-/

namespace AspisV5ForwardAcceptedFalseDerivedQueries

open MeasureTheory
open AspisCircleGroupOrder
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisV5AcceptedExecutionDerivedQueries
open AspisV5AcceptedSpendRelation
open AspisV5BoundedQuerySamplerUniformity
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ForwardAcceptedFalseRawAccounting
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriRelationCandidateBridge
open AspisV5FourClaimBatchUnion
open AspisV5RawFinalSecurityAccounting
open AspisV5RelationSumcheckSoundness
open AspisV5Tag67AcceptedFalseInclusion
open AspisV5Tag67CandidateTraceExtraction
open AspisV5Tag67FalseAcceptanceDecomposition
open AspisV5Tag67ModeledRelationAcceptanceBridge
open AspisV5TranscriptConnection
open AspisV5WithoutReplacementQuerySoundness

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K] [NeZero (2 : K)]

/-! ## Exact transcript-derived experiment data -/

/-- The forward accepted-false experiment with no caller-chosen query
schedule.  Successful `derive18Queries` output determines the ordered
injection used by the ideal FRI verifier. -/
structure ReleasedDerivedQueryExperimentData
    (Coins K : Type*) [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (rc : RoundConstants)
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest) where
  base : ReleasedIdealAcceptedFalseExperimentData Coins K rc deployedOwner
    deployedNote deployedNullifier deployedNode
  queryBlocks : Coins → List (FixedBytes 32)
  decodedQueries : Coins → List Nat
  queryDecode : ∀ coins,
    derive18Queries (queryBlocks coins) = some (decodedQueries coins)
  queriesAreDecoded : ∀ coins, base.queries coins =
    decodedQuerySchedule (queryBlocks coins) (decodedQueries coins)
      (queryDecode coins)

/-- Forget only the derivation witness.  The old experiment's `queries` field
is definitionally the injection built from the exact decoder output. -/
def ReleasedDerivedQueryExperimentData.toBase
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (data : ReleasedDerivedQueryExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode) :
    ReleasedIdealAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode :=
  data.base

theorem ReleasedDerivedQueryExperimentData.query_values_are_exact
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (data : ReleasedDerivedQueryExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode)
    (coins : Coins) :
    List.ofFn (fun index => ((data.toBase.queries coins) index).val) =
      data.decodedQueries coins := by
  change List.ofFn (fun index => ((data.base.queries coins) index).val) =
    data.decodedQueries coins
  rw [data.queriesAreDecoded coins]
  exact decodedQuerySchedule_values (data.queryBlocks coins)
    (data.decodedQueries coins) (data.queryDecode coins)

/-! ## Prefix-conditioned query law -/

/-- A finite prefix identifies the bad fibre set before the query squeeze.
The deterministic field says every concrete query-phase failure lands in that
set.  Its size bound is mathematical and does not assert anything about the
distribution of SHA output. -/
structure DerivedQueryPrefixProjection
    (Prefix Coins K : Type*) [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (data : ReleasedDerivedQueryExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode) where
  prefixOf : Coins → Prefix
  badAt : Prefix → Finset (Fin 131072)
  badAt_card : ∀ prefixValue, (badAt prefixValue).card ≤ 6082
  queryFailure_implies_bad : ∀ coins,
    QueryPhaseFailure (data.toBase.fri.scheduleAtCoin coins)
      (data.toBase.fri.transcriptAt coins) (data.toBase.queries coins) →
    AllQueriesIn (badAt (prefixOf coins)) (data.toBase.queries coins)

def DerivedQueryPrefixProjection.badQueryEvent
    {Prefix Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {data : ReleasedDerivedQueryExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    (projection : DerivedQueryPrefixProjection Prefix Coins K data) : Set Coins :=
  {coins | AllQueriesIn (projection.badAt (projection.prefixOf coins))
    (data.toBase.queries coins)}

theorem queryMiss_subset_badQueryEvent
    {Prefix Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {data : ReleasedDerivedQueryExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    (projection : DerivedQueryPrefixProjection Prefix Coins K data) :
    data.toBase.queryMiss ⊆ projection.badQueryEvent := by
  intro coins hfailure
  exact projection.queryFailure_implies_bad coins hfailure

/-- The sole query-distribution premise.  For each prefix-fixed bad set it
compares the actual SHA/Fiat--Shamir event with the exact ideal bounded sampler
conditioned on returning eighteen distinct queries.  It does not factor a
joint event or assert independence from the prefix. -/
structure ConditionalDerivedQuerySamplerLaw
    (Prefix Coins K : Type*) [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    [MeasurableSpace Coins]
    [MeasurableSpace Prefix] [MeasurableSingletonClass Prefix]
    [Fintype Prefix] [DecidableEq Prefix]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (measure : Measure Coins)
    {data : ReleasedDerivedQueryExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    (projection : DerivedQueryPrefixProjection Prefix Coins K data) : Prop where
  measurablePrefix : Measurable projection.prefixOf
  conditionalBoundedSampler :
    measure.real projection.badQueryEvent ≤
      ∑ prefixValue : Prefix,
        measure.real {coins | projection.prefixOf coins = prefixValue} *
          conditionedAllQueriesInProbability (q := 18) (maxDraws := 64)
            (projection.badAt prefixValue)

theorem prefix_fibre_real_mass_eq_one
    {Prefix Coins : Type*}
    [MeasurableSpace Coins]
    [MeasurableSpace Prefix] [MeasurableSingletonClass Prefix]
    [Fintype Prefix] [DecidableEq Prefix]
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    (prefixOf : Coins → Prefix) (hprefix : Measurable prefixOf) :
    (∑ prefixValue : Prefix,
      measure.real {coins | prefixOf coins = prefixValue}) = 1 := by
  let fibre : Prefix → Set Coins :=
    fun prefixValue => {coins | prefixOf coins = prefixValue}
  have hdisjoint :
      ((Finset.univ : Finset Prefix) : Set Prefix).PairwiseDisjoint fibre := by
    intro left _hleft right _hright hne
    change Disjoint (fibre left) (fibre right)
    rw [Set.disjoint_left]
    intro coins hleft hright
    exact hne (hleft.symm.trans hright)
  have hmeasurable : ∀ prefixValue ∈ (Finset.univ : Finset Prefix),
      MeasurableSet (fibre prefixValue) := by
    intro prefixValue _hvalue
    exact (MeasurableSet.singleton prefixValue).preimage hprefix
  have hunion :
      (⋃ prefixValue ∈ (Finset.univ : Finset Prefix), fibre prefixValue) =
        Set.univ := by
    ext coins
    simp [fibre]
  have hmeasure := measure_biUnion_finset (μ := measure) hdisjoint hmeasurable
  rw [hunion, measure_univ] at hmeasure
  have hreal := congrArg ENNReal.toReal hmeasure
  rw [ENNReal.toReal_one, ENNReal.toReal_sum] at hreal
  · simpa [Measure.real, fibre] using hreal.symm
  · intro prefixValue _hvalue
    exact measure_ne_top measure (fibre prefixValue)

/-- The exact decoder, prefix projection, finite bounded-sampler theorem, and
the one conditional SHA/Fiat--Shamir law imply the raw q18 term. -/
theorem derived_query_miss_probability_le_raw_bound
    {Prefix Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    [MeasurableSpace Coins]
    [MeasurableSpace Prefix] [MeasurableSingletonClass Prefix]
    [Fintype Prefix] [DecidableEq Prefix]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    {data : ReleasedDerivedQueryExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    (projection : DerivedQueryPrefixProjection Prefix Coins K data)
    (law : ConditionalDerivedQuerySamplerLaw Prefix Coins K measure projection) :
    measure.real data.toBase.queryMiss ≤ rawQ18IdealMissBound := by
  have hsubset :
      measure.real data.toBase.queryMiss ≤ measure.real projection.badQueryEvent :=
    MeasureTheory.measureReal_mono (queryMiss_subset_badQueryEvent projection)
  have hterm : ∀ prefixValue : Prefix,
      conditionedAllQueriesInProbability (q := 18) (maxDraws := 64)
          (projection.badAt prefixValue) ≤ rawQ18IdealMissBound := by
    intro prefixValue
    rw [conditionedAllQueriesInProbability_eq_ideal
      (projection.badAt prefixValue) (by norm_num) (by norm_num)]
    exact ideal_q18_miss_le_raw_bound (projection.badAt prefixValue)
      (projection.badAt_card prefixValue)
  have hweighted :
      (∑ prefixValue : Prefix,
        measure.real {coins | projection.prefixOf coins = prefixValue} *
          conditionedAllQueriesInProbability (q := 18) (maxDraws := 64)
            (projection.badAt prefixValue)) ≤
        rawQ18IdealMissBound := by
    calc
      (∑ prefixValue : Prefix,
          measure.real {coins | projection.prefixOf coins = prefixValue} *
            conditionedAllQueriesInProbability (q := 18) (maxDraws := 64)
              (projection.badAt prefixValue)) ≤
          ∑ prefixValue : Prefix,
            measure.real {coins | projection.prefixOf coins = prefixValue} *
              rawQ18IdealMissBound := by
        apply Finset.sum_le_sum
        intro prefixValue _hvalue
        exact mul_le_mul_of_nonneg_left (hterm prefixValue)
          MeasureTheory.measureReal_nonneg
      _ = (∑ prefixValue : Prefix,
            measure.real {coins | projection.prefixOf coins = prefixValue}) *
          rawQ18IdealMissBound := by
        rw [Finset.sum_mul]
      _ = rawQ18IdealMissBound := by
        rw [prefix_fibre_real_mass_eq_one measure projection.prefixOf
          law.measurablePrefix]
        ring
  exact hsubset.trans (law.conditionalBoundedSampler.trans hweighted)

/-! ## Rebuilding the newest raw connection without a free q18 premise -/

/-- The remaining six distributional connections.  Unlike
`ReleasedIdealAcceptedFalseRawConnections`, there is no query-miss field: it
is derived above from the exact query decoder and the conditional sampler
law. -/
structure ReleasedDerivedQueryRawConnections
    (Prefix Coins K : Type*) [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    [MeasurableSpace Coins]
    [MeasurableSpace Prefix] [MeasurableSingletonClass Prefix]
    [Fintype Prefix] [DecidableEq Prefix]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (measure : Measure Coins)
    (data : ReleasedDerivedQueryExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode) where
  projection : DerivedQueryPrefixProjection Prefix Coins K data
  querySampler : ConditionalDerivedQuerySamplerLaw Prefix Coins K measure
    projection
  friRound0 : measure.real data.toBase.toEvents.fri.round0Event ≤
    rawFriFibreBound 0
  friRound1 : measure.real data.toBase.toEvents.fri.round1Event ≤
    rawFriFibreBound 1
  friRound2 : measure.real data.toBase.toEvents.fri.round2Event ≤
    rawFriFibreBound 2
  friRound3 : measure.real data.toBase.toEvents.fri.round3Event ≤
    rawFriFibreBound 3
  relationRepair : measure.real data.toBase.toEvents.relationRepair ≤
    rawRelationRepairBound
  fourClaimBatchCollision :
    measure.real data.toBase.toEvents.fourClaimBatchCollision ≤
      AspisV5FourClaimBatchUnion.rawFourClaimBatchCollisionBound

theorem ReleasedDerivedQueryRawConnections.toRawConnections
    {Prefix Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    [MeasurableSpace Coins]
    [MeasurableSpace Prefix] [MeasurableSingletonClass Prefix]
    [Fintype Prefix] [DecidableEq Prefix]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    {data : ReleasedDerivedQueryExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    (connections : ReleasedDerivedQueryRawConnections Prefix Coins K measure
      data) :
    ReleasedIdealAcceptedFalseRawConnections measure data.toBase.toEvents where
  queryMiss := derived_query_miss_probability_le_raw_bound measure
    connections.projection connections.querySampler
  friRound0 := connections.friRound0
  friRound1 := connections.friRound1
  friRound2 := connections.friRound2
  friRound3 := connections.friRound3
  relationRepair := connections.relationRepair
  fourClaimBatchCollision := connections.fourClaimBatchCollision

set_option maxRecDepth 1000000 in
/-- Concrete ideal accounting for the transcript-derived query schedule.  In
particular, the endpoint no longer accepts either an arbitrary query schedule
or a separate q18 query-miss probability premise. -/
theorem released_derived_query_ideal_accepted_false_probability_le_raw_core_plus_explicit
    {Prefix Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    [MeasurableSpace Coins]
    [MeasurableSpace Prefix] [MeasurableSingletonClass Prefix]
    [Fintype Prefix] [DecidableEq Prefix]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    (data : ReleasedDerivedQueryExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode)
    (connections : ReleasedDerivedQueryRawConnections Prefix Coins K measure
      data) :
    measure.real data.toBase.acceptedFalse ≤
      (rawCoreSubtotal + rawFourClaimBatchCollisionBound) +
        measure.real data.toBase.relationOrExtractionFailure +
        measure.real data.toBase.statementBindingFailure := by
  exact
    released_concrete_ideal_accepted_false_probability_le_raw_core_plus_explicit
      measure data.toBase (connections.toRawConnections measure)

set_option maxRecDepth 1000000 in
/-- Production accounting for the transcript-derived query schedule.  The
remaining Rust/transcript/hash reduction is still explicit; this theorem does
not model SHA output as independent of the preceding transcript. -/
theorem released_derived_query_production_false_spend_probability_le_raw_core_plus_explicit
    {Prefix Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    [MeasurableSpace Coins]
    [MeasurableSpace Prefix] [MeasurableSingletonClass Prefix]
    [Fintype Prefix] [DecidableEq Prefix]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    (data : ReleasedDerivedQueryExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode)
    (connections : ReleasedDerivedQueryRawConnections Prefix Coins K measure
      data)
    (production : ReleasedProductionFalseSpendConnection data.toBase.toEvents) :
    measure.real production.productionFalseSpend ≤
      (rawCoreSubtotal + rawFourClaimBatchCollisionBound) +
        measure.real data.toBase.relationOrExtractionFailure +
        measure.real data.toBase.statementBindingFailure +
        measure.real (AspisV5CryptographicAssumptions.totalFailure
          production.transcriptAndHashFailures) := by
  exact
    released_concrete_production_false_spend_probability_le_raw_core_plus_explicit
      measure data.toBase (connections.toRawConnections measure) production

set_option maxRecDepth 1000000 in
/-- The corresponding one-proof numerical endpoint.  `2^-75` bounds the
ideal algebraic core; the displayed implementation/hash and mathematical
bridge events remain outside that number. -/
theorem released_derived_query_production_false_spend_probability_le_two_pow_neg_75_plus_explicit
    {Prefix Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    [MeasurableSpace Coins]
    [MeasurableSpace Prefix] [MeasurableSingletonClass Prefix]
    [Fintype Prefix] [DecidableEq Prefix]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    (data : ReleasedDerivedQueryExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode)
    (connections : ReleasedDerivedQueryRawConnections Prefix Coins K measure
      data)
    (production : ReleasedProductionFalseSpendConnection data.toBase.toEvents) :
    measure.real production.productionFalseSpend ≤
      (1 : Real) / 2 ^ 75 +
        measure.real data.toBase.relationOrExtractionFailure +
        measure.real data.toBase.statementBindingFailure +
        measure.real (AspisV5CryptographicAssumptions.totalFailure
          production.transcriptAndHashFailures) := by
  exact
    released_concrete_production_false_spend_probability_le_two_pow_neg_75_plus_explicit
      measure data.toBase (connections.toRawConnections measure) production

#print axioms ReleasedDerivedQueryExperimentData.query_values_are_exact
#print axioms prefix_fibre_real_mass_eq_one
#print axioms derived_query_miss_probability_le_raw_bound
#print axioms ReleasedDerivedQueryRawConnections.toRawConnections
#print axioms released_derived_query_ideal_accepted_false_probability_le_raw_core_plus_explicit
#print axioms released_derived_query_production_false_spend_probability_le_raw_core_plus_explicit
#print axioms released_derived_query_production_false_spend_probability_le_two_pow_neg_75_plus_explicit

end AspisV5ForwardAcceptedFalseDerivedQueries
