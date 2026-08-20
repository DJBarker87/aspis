import AspisFormal.V5AcceptedExecutionReleasedSecurity

/-!
# Deriving the released query schedule from transcript output

The accepted-execution theorem is stated for an ordered injection
`Fin 18 ↪ Fin 131072`.  The production transcript sampler returns a list of
natural numbers.  This file removes the need to supply the injection as a
separate premise: a successful exact 18-query decode proves the list has
length 18, has no duplicates, and is in range, so it determines the ordered
injection and its 18-element image.

This is a deterministic conversion.  It does not identify a Rust transcript
driver with the Lean driver.  That source equality remains the separately
named transcript-projection boundary.
-/

namespace AspisV5AcceptedExecutionDerivedQueries

open AspisCircleGroupOrder
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisV5AcceptedExecutionReleasedSchedule
open AspisV5AcceptedExecutionReleasedSecurity
open AspisV5AcceptedExecutionSecurityBridge
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriCompatibleCandidateChain
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriGlobalCausalStrategy
open AspisV5FriPublishedOutputEncoderDecoding
open AspisV5FriRelationCandidateBridge
open AspisV5FriReleasedAdaptiveExtraction
open AspisV5FriReleasedLineGeometry
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleConsumedValueBridge
open AspisV5MerkleRustBridge
open AspisV5NonceWorkAuthentication
open AspisV5RelationStressSourceBridge
open AspisV5Tag67AcceptedFalseInclusion
open AspisV5Tag67CandidateTraceExtraction
open AspisV5Tag67FalseAcceptanceDecomposition
open AspisV5Tag67ModeledRelationAcceptanceBridge
open AspisV5Tag67RelationListInclusion
open AspisV5TranscriptConnection
open AspisV5WithoutReplacementQuerySoundness

/-- A length-18 duplicate-free in-range list determines the ordered released
query schedule. -/
def queryScheduleOfExactList
    (queries : List Nat)
    (hlength : queries.length = 18)
    (hnodup : queries.Nodup)
    (hbound : ∀ query ∈ queries, query < 2 ^ 17) :
    QuerySchedule 18 131072 where
  toFun index :=
    ⟨queries.get (Fin.cast hlength.symm index), by
      have hmember :
          queries.get (Fin.cast hlength.symm index) ∈ queries :=
        List.get_mem queries (Fin.cast hlength.symm index)
      have := hbound _ hmember
      norm_num at this ⊢
      exact this⟩
  inj' := by
    intro left right heq
    have hvalues :
        queries.get (Fin.cast hlength.symm left) =
          queries.get (Fin.cast hlength.symm right) :=
      congrArg Fin.val heq
    have hindices :
        Fin.cast hlength.symm left = Fin.cast hlength.symm right :=
      hnodup.injective_get hvalues
    exact Fin.cast_injective hlength.symm hindices

theorem queryScheduleOfExactList_values
    (queries : List Nat)
    (hlength : queries.length = 18)
    (hnodup : queries.Nodup)
    (hbound : ∀ query ∈ queries, query < 2 ^ 17) :
    List.ofFn (fun index =>
      ((queryScheduleOfExactList queries hlength hnodup hbound) index).val) =
        queries := by
  change List.ofFn (fun index : Fin 18 =>
      queries.get (Fin.cast hlength.symm index)) = queries
  rw [← List.ofFn_congr hlength queries.get]
  exact List.ofFn_get queries

/-- The ordered schedule forced by a successful production-shaped query
decode.  Its three well-formedness proofs come from
`derive18Queries_success_is_exact`; callers do not supply them. -/
def decodedQuerySchedule
    (blocks : List (FixedBytes 32))
    (queries : List Nat)
    (hdecode : derive18Queries blocks = some queries) :
    QuerySchedule 18 131072 :=
  let exact := derive18Queries_success_is_exact blocks queries hdecode
  queryScheduleOfExactList queries exact.1 exact.2.1 exact.2.2

def decodedQuerySet
    (blocks : List (FixedBytes 32))
    (queries : List Nat)
    (hdecode : derive18Queries blocks = some queries) : Finset V5Query :=
  Finset.univ.image (decodedQuerySchedule blocks queries hdecode)

theorem decodedQuerySchedule_values
    (blocks : List (FixedBytes 32))
    (queries : List Nat)
    (hdecode : derive18Queries blocks = some queries) :
    List.ofFn (fun index =>
      ((decodedQuerySchedule blocks queries hdecode) index).val) = queries := by
  unfold decodedQuerySchedule
  exact queryScheduleOfExactList_values queries
    (derive18Queries_success_is_exact blocks queries hdecode).1
    (derive18Queries_success_is_exact blocks queries hdecode).2.1
    (derive18Queries_success_is_exact blocks queries hdecode).2.2

theorem decoded_query_positions_projection
    {FieldValue PointValue : Type*}
    (blocks : List (FixedBytes 32))
    (derived : V5DerivedValues FieldValue PointValue)
    (hdecode : derive18Queries blocks = some derived.queries) :
    derived.queries = List.ofFn (fun index =>
      ((decodedQuerySchedule blocks derived.queries hdecode) index).val) := by
  exact (decodedQuerySchedule_values blocks derived.queries hdecode).symm

theorem decodedQuerySet_card
    (blocks : List (FixedBytes 32))
    (queries : List Nat)
    (hdecode : derive18Queries blocks = some queries) :
    (decodedQuerySet blocks queries hdecode).card = 18 := by
  unfold decodedQuerySet
  rw [Finset.card_image_of_injective _
    (decodedQuerySchedule blocks queries hdecode).injective]
  simp

theorem mem_decodedQuerySet_iff
    (blocks : List (FixedBytes 32))
    (queries : List Nat)
    (hdecode : derive18Queries blocks = some queries)
    (query : V5Query) :
    query ∈ decodedQuerySet blocks queries hdecode ↔ query.val ∈ queries := by
  constructor
  · intro hmember
    rcases Finset.mem_image.mp hmember with ⟨index, _, hquery⟩
    rw [← decodedQuerySchedule_values blocks queries hdecode]
    simp only [List.mem_ofFn]
    exact ⟨index, congrArg Fin.val hquery⟩
  · intro hmember
    rw [← decodedQuerySchedule_values blocks queries hdecode] at hmember
    simp only [List.mem_ofFn] at hmember
    rcases hmember with ⟨index, hquery⟩
    exact Finset.mem_image.mpr
      ⟨index, Finset.mem_univ index, Fin.ext hquery⟩

theorem decoded_queries_are_exact
    (blocks : List (FixedBytes 32))
    (queries : List Nat)
    (hdecode : derive18Queries blocks = some queries) :
    List.ofFn (fun index =>
        ((decodedQuerySchedule blocks queries hdecode) index).val) = queries ∧
      (decodedQuerySet blocks queries hdecode).card = 18 ∧
      (∀ query : V5Query,
        query ∈ decodedQuerySet blocks queries hdecode ↔
          query.val ∈ queries) ∧
      queries.Nodup ∧
      (∀ query ∈ queries, query < 131072) := by
  have hexact := derive18Queries_success_is_exact blocks queries hdecode
  exact ⟨decodedQuerySchedule_values blocks queries hdecode,
    decodedQuerySet_card blocks queries hdecode,
    mem_decodedQuerySet_iff blocks queries hdecode,
    hexact.2.1, by simpa using hexact.2.2⟩

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K] [NeZero (2 : K)]

/-- The released accepted-execution reduction with its query schedule derived
from the exact transcript sampler output.  In particular, there is no free
query schedule, distinctness premise, range premise, or cardinality premise.

The production query set is still projected from the Rust opening verifier.
Its equality to the image of this derived schedule is checked by
`TranscriptExecutionProjection.querySetExact`; if that source connection is
absent, the theorem reports the named transcript-projection failure event. -/
theorem accepted_false_source_execution_event_with_derived_queries
    {RustInput MerkleDigest PointValue State : Type*}
    (rc : RoundConstants)
    {deployedOwner : AspisFormal.ArithmetizationCore.Digest ->
      AspisFormal.ArithmetizationCore.Digest}
    {deployedNote : AspisFormal.ArithmetizationCore.Digest ->
      AspisFormal.ArithmetizationCore.F ->
      AspisFormal.ArithmetizationCore.F ->
      AspisFormal.ArithmetizationCore.Digest ->
      AspisFormal.ArithmetizationCore.Digest}
    {deployedNullifier : AspisFormal.ArithmetizationCore.Digest ->
      AspisFormal.ArithmetizationCore.Digest ->
      AspisFormal.ArithmetizationCore.Digest}
    {deployedNode : AspisFormal.ArithmetizationCore.Digest ->
      AspisFormal.ArithmetizationCore.Digest ->
      AspisFormal.ArithmetizationCore.Digest}
    (hashing : MerkleHashing MerkleDigest)
    (rustAcceptsOpening : RustInput -> Prop)
    (rootsOf : RustInput -> V5PrivateRoots MerkleDigest)
    (querySetOf : RustInput -> Finset V5Query)
    (rustInput : RustInput)
    (base : FixedSchedule (ZMod P) K)
    (hproduction : ProductionUsesReleasedFriTables base)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (causalFamily : CausalTranscriptFamily K)
    (input : SourceRelationInput K)
    (relationFamily : CoherentCandidateFamily K
      (AcceptedCandidate base causalFamily input))
    (records : CandidateRecords (AcceptedCandidate base causalFamily input) K)
    (statement : V5PublicStatement)
    (decoder : OpeningFibreDecoder K)
    (expectedC2 : V5Query -> Fin 4 -> K)
    (transcriptInput : V5TranscriptInputs)
    (derived : V5DerivedValues K PointValue)
    (driverResult : V5TranscriptDriverResult K PointValue)
    (queryBlocks : List (FixedBytes 32))
    (hdecode : derive18Queries queryBlocks = some derived.queries)
    (workFunctions : ExecutableWorkFunctions State
      (SqueezeResult K PointValue))
    (workInputs : PositionedWorkInputs State (SqueezeResult K PointValue))
    (hsource : ∃ output, runSourceRelationVerifier input = some output)
    (hrustOpening : rustAcceptsOpening rustInput)
    (noWitness : ¬ StatementHasSpendWitness statement deployedOwner
      deployedNote deployedNullifier deployedNode) :
    let queries := decodedQuerySchedule queryBlocks derived.queries hdecode
    ReleasedAcceptedExecutionSecurityEvent
    (¬ SourceRelationInputMatchesFamily input relationFamily)
    (¬ FamilyMatchesFriTranscript
      (concreteCodeEncoders base releasedEvaluationPoints)
      (acceptedTranscript causalFamily input) relationFamily input.challenges)
    (¬ TranscriptExecutionProjection input transcriptInput derived
      driverResult (querySetOf rustInput) queries)
    (¬ WorkExecutionProjection transcriptInput derived workInputs)
    (¬ ∃ reference : AcceptedV5Forest hashing (rootsOf rustInput)
        (querySetOf rustInput),
      ForestProjectsToTranscript decoder hashing reference
        (acceptedTranscript causalFamily input) expectedC2)
    (¬ RustAcceptedOpeningYieldsForest hashing rustAcceptsOpening rootsOf
      querySetOf)
    (HashCollision hashing)
    (¬ ExecutableWorkAcceptance workFunctions workInputs)
    (∃ forest : AcceptedV5Forest hashing (rootsOf rustInput)
        (querySetOf rustInput),
      ¬ ForestFriChecks decoder hashing forest (acceptedSchedule base input)
        (acceptedTranscript causalFamily input) queries)
    (QueryPhaseFailure (acceptedSchedule base input)
      (acceptedTranscript causalFamily input) queries)
    (∃ (hfinal : FinalXMatchesReleasedDomain base)
        (htables : InverseTablesMatch base releasedEvaluationPoints)
        (hdecoding : PublishedOrdinaryPolynomialCurveDecoding (K := K)),
      (adaptiveBadSets base causalFamily hfinal htables hdecoding
        (constructedAdaptiveStrategies base causalFamily)).Occurs
        input.round0.alpha input.round1.alpha input.round2.alpha
          input.round3.alpha)
    (∃ candidate : AcceptedCandidate base causalFamily input,
      CandidateEarlierFailure rc (relationFamily.execution candidate)
        input.challenges statement (records candidate))
    (Fintype.card (AcceptedCandidate base causalFamily input) ≤ 240 ∧
      input.challenges ∈ boundedCandidateRepairEvent
        (fun candidate => (relationFamily.execution candidate).adaptiveData))
    (¬ Poseidon2Faithful rc deployedOwner deployedNote deployedNullifier
      deployedNode) := by
  let queries := decodedQuerySchedule queryBlocks derived.queries hdecode
  exact accepted_false_source_execution_event_with_released_tables rc hashing
    rustAcceptsOpening rootsOf querySetOf rustInput base hproduction hpublished
    causalFamily input relationFamily records statement queries decoder
    expectedC2 transcriptInput derived driverResult workFunctions workInputs
    hsource hrustOpening noWitness

/-- The query-derived endpoint specialized to the exact production
opening-and-FRI observation.  Successful observation now supplies the
authenticated forest, so the Rust-opening correspondence branch is `False`.
The derived schedule is still obtained from the exact 18-query transcript
decode, leaving neither a free query schedule nor a separate opening-forest
assumption in this maintained endpoint. -/
theorem accepted_false_source_observation_event_with_derived_queries
    {PointValue State : Type*}
    (rc : RoundConstants)
    {deployedOwner : AspisFormal.ArithmetizationCore.Digest ->
      AspisFormal.ArithmetizationCore.Digest}
    {deployedNote : AspisFormal.ArithmetizationCore.Digest ->
      AspisFormal.ArithmetizationCore.F ->
      AspisFormal.ArithmetizationCore.F ->
      AspisFormal.ArithmetizationCore.Digest ->
      AspisFormal.ArithmetizationCore.Digest}
    {deployedNullifier : AspisFormal.ArithmetizationCore.Digest ->
      AspisFormal.ArithmetizationCore.Digest ->
      AspisFormal.ArithmetizationCore.Digest}
    {deployedNode : AspisFormal.ArithmetizationCore.Digest ->
      AspisFormal.ArithmetizationCore.Digest ->
      AspisFormal.ArithmetizationCore.Digest}
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte ->
      AspisV5MerkleRustBridge.Digest32)
    (rustObservation : V5ProductionCall ->
      Option OpeningAndFriObservation)
    (rustCall : V5ProductionCall)
    (observation : OpeningAndFriObservation)
    (hconsumer : ExactRustV5OpeningAndFriConsumerEquality sha256
      rustObservation)
    (hobservation : rustObservation rustCall = some observation)
    (base : FixedSchedule (ZMod P) K)
    (hproduction : ProductionUsesReleasedFriTables base)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (causalFamily : CausalTranscriptFamily K)
    (input : SourceRelationInput K)
    (relationFamily : CoherentCandidateFamily K
      (AcceptedCandidate base causalFamily input))
    (records : CandidateRecords (AcceptedCandidate base causalFamily input) K)
    (statement : V5PublicStatement)
    (decoder : OpeningFibreDecoder K)
    (expectedC2 : V5Query -> Fin 4 -> K)
    (transcriptInput : V5TranscriptInputs)
    (derived : V5DerivedValues K PointValue)
    (driverResult : V5TranscriptDriverResult K PointValue)
    (queryBlocks : List (FixedBytes 32))
    (hdecode : derive18Queries queryBlocks = some derived.queries)
    (workFunctions : ExecutableWorkFunctions State
      (SqueezeResult K PointValue))
    (workInputs : PositionedWorkInputs State (SqueezeResult K PointValue))
    (hsource : ∃ output, runSourceRelationVerifier input = some output)
    (noWitness : ¬ StatementHasSpendWitness statement deployedOwner
      deployedNote deployedNullifier deployedNode) :
    let queries := decodedQuerySchedule queryBlocks derived.queries hdecode
    ReleasedAcceptedExecutionSecurityEvent
    (¬ SourceRelationInputMatchesFamily input relationFamily)
    (¬ FamilyMatchesFriTranscript
      (concreteCodeEncoders base releasedEvaluationPoints)
      (acceptedTranscript causalFamily input) relationFamily input.challenges)
    (¬ TranscriptExecutionProjection input transcriptInput derived
      driverResult rustCall.queries queries)
    (¬ WorkExecutionProjection transcriptInput derived workInputs)
    (¬ ∃ reference : AcceptedV5Forest (sha256MerkleHashing sha256)
        rustCall.roots rustCall.queries,
      ForestProjectsToTranscript decoder (sha256MerkleHashing sha256)
        reference (acceptedTranscript causalFamily input) expectedC2)
    False
    (HashCollision (sha256MerkleHashing sha256))
    (¬ ExecutableWorkAcceptance workFunctions workInputs)
    (∃ forest : AcceptedV5Forest (sha256MerkleHashing sha256)
        rustCall.roots rustCall.queries,
      ¬ ForestFriChecks decoder (sha256MerkleHashing sha256) forest
        (acceptedSchedule base input)
        (acceptedTranscript causalFamily input) queries)
    (QueryPhaseFailure (acceptedSchedule base input)
      (acceptedTranscript causalFamily input) queries)
    (∃ (hfinal : FinalXMatchesReleasedDomain base)
        (htables : InverseTablesMatch base releasedEvaluationPoints)
        (hdecoding : PublishedOrdinaryPolynomialCurveDecoding (K := K)),
      (adaptiveBadSets base causalFamily hfinal htables hdecoding
        (constructedAdaptiveStrategies base causalFamily)).Occurs
        input.round0.alpha input.round1.alpha input.round2.alpha
          input.round3.alpha)
    (∃ candidate : AcceptedCandidate base causalFamily input,
      CandidateEarlierFailure rc (relationFamily.execution candidate)
        input.challenges statement (records candidate))
    (Fintype.card (AcceptedCandidate base causalFamily input) ≤ 240 ∧
      input.challenges ∈ boundedCandidateRepairEvent
        (fun candidate => (relationFamily.execution candidate).adaptiveData))
    (¬ Poseidon2Faithful rc deployedOwner deployedNote deployedNullifier
      deployedNode) := by
  let queries := decodedQuerySchedule queryBlocks derived.queries hdecode
  exact accepted_false_source_observation_event_with_released_tables rc sha256
    rustObservation rustCall observation hconsumer hobservation base
    hproduction hpublished causalFamily input relationFamily records statement
    queries decoder expectedC2 transcriptInput derived driverResult
    workFunctions workInputs hsource noWitness

#print axioms queryScheduleOfExactList_values
#print axioms decodedQuerySchedule_values
#print axioms decoded_query_positions_projection
#print axioms decodedQuerySet_card
#print axioms mem_decodedQuerySet_iff
#print axioms decoded_queries_are_exact
#print axioms accepted_false_source_execution_event_with_derived_queries
#print axioms accepted_false_source_observation_event_with_derived_queries

end AspisV5AcceptedExecutionDerivedQueries
