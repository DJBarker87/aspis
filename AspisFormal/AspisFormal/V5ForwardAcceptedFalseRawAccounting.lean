import AspisFormal.V5FriForwardCompatibleChain
import AspisFormal.V5FourClaimBatchUnion
import AspisFormal.V5RawFinalSecurityAccounting

/-!
# Raw accounting for the prefix-timed accepted-false theorem

`V5FriForwardCompatibleChain` proves the deterministic four-way inclusion for
an ideal accepted false spend:

1. the eighteen-query miss;
2. one of four prefix-timed FRI compatibility events;
3. an earlier relation, extraction, or statement-binding failure; or
4. the cap-240 relation-repair event.

This file connects those exact FRI sets to the existing raw one-proof
accounting.  The one-proof ideal core is at most `2^-75`; relation/extraction,
statement binding, and production transcript/hash failures remain visible as
separate probability terms.

It also supplies the full adaptive-attempt analogue.  The adversary may choose
a new causal transcript family from the complete prior-attempt history, but
not from the fresh four-challenge tuple of the current attempt.  Thus `T`
completed fresh attempts cost `T` times the raw FRI bound.  Connecting a real
Rust/SHA-256 execution to that experiment remains an explicit premise.
-/

namespace AspisV5ForwardAcceptedFalseRawAccounting

open MeasureTheory
open AspisCircleGroupOrder
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5CryptographicAssumptions
open AspisV5FiatShamirAdaptiveQueryBudget
open AspisV5FinalSecurityAccounting
open AspisV5FriAdaptiveUnmatched
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriFixedFamilyExperiment
open AspisV5FriForwardCompatibleChain
open AspisV5FourClaimBatchUnion
open AspisV5FriPublishedOutputEncoderDecoding
open AspisV5FriReleasedAdaptiveExtraction
open AspisV5FriReleasedLineGeometry
open AspisV5FriRelationCandidateBridge
open AspisV5FriRoundByRoundSoundness
open AspisV5RawFinalSecurityAccounting
open AspisV5RelationSumcheckSoundness
open AspisV5Tag67AcceptedFalseInclusion
open AspisV5Tag67CandidateTraceExtraction
open AspisV5Tag67FalseAcceptanceDecomposition
open AspisV5Tag67ModeledRelationAcceptanceBridge
open AspisV5Tag67RelationListInclusion
open AspisV5WithoutReplacementQuerySoundness

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K] [NeZero (2 : K)]

/-! ## The exact compatibility event inside a larger experiment -/

structure CompatibilityFriExperiment (Coins K : Type*)
    [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] where
  base : FixedSchedule (ZMod P) K
  family : CausalTranscriptFamily K
  finalDomain : FinalXMatchesReleasedDomain base
  inverseTables : InverseTablesMatch base releasedEvaluationPoints
  publishedDecoding : PublishedOrdinaryPolynomialCurveDecoding (K := K)
  round0Challenge : Coins → K
  round1Challenge : Coins → K
  round2Challenge : Coins → K
  round3Challenge : Coins → K

noncomputable def CompatibilityFriExperiment.badSets
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (experiment : CompatibilityFriExperiment Coins K) :=
  releasedCompatibilityBadSets experiment.base experiment.family
    experiment.finalDomain experiment.inverseTables
    experiment.publishedDecoding

def CompatibilityFriExperiment.round0Event
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (experiment : CompatibilityFriExperiment Coins K) : Set Coins :=
  {coins | experiment.round0Challenge coins ∈ experiment.badSets.round0}

def CompatibilityFriExperiment.round1Event
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (experiment : CompatibilityFriExperiment Coins K) : Set Coins :=
  {coins | experiment.round1Challenge coins ∈
    experiment.badSets.round1 (experiment.round0Challenge coins)}

def CompatibilityFriExperiment.round2Event
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (experiment : CompatibilityFriExperiment Coins K) : Set Coins :=
  {coins | experiment.round2Challenge coins ∈
    experiment.badSets.round2 (experiment.round0Challenge coins)
      (experiment.round1Challenge coins)}

def CompatibilityFriExperiment.round3Event
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (experiment : CompatibilityFriExperiment Coins K) : Set Coins :=
  {coins | experiment.round3Challenge coins ∈
    experiment.badSets.round3 (experiment.round0Challenge coins)
      (experiment.round1Challenge coins) (experiment.round2Challenge coins)}

def CompatibilityFriExperiment.event
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (experiment : CompatibilityFriExperiment Coins K) : Set Coins :=
  {coins | experiment.badSets.Occurs
    (experiment.round0Challenge coins)
    (experiment.round1Challenge coins)
    (experiment.round2Challenge coins)
    (experiment.round3Challenge coins)}

theorem CompatibilityFriExperiment.event_eq_round_union
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (experiment : CompatibilityFriExperiment Coins K) :
    experiment.event = experiment.round0Event ∪
      (experiment.round1Event ∪
        (experiment.round2Event ∪ experiment.round3Event)) := by
  ext coins
  simp only [CompatibilityFriExperiment.event,
    CompatibilityFriExperiment.round0Event,
    CompatibilityFriExperiment.round1Event,
    CompatibilityFriExperiment.round2Event,
    CompatibilityFriExperiment.round3Event, Set.mem_setOf_eq, Set.mem_union,
    PrefixConditionedBadSets.Occurs]

def CompatibilityFriExperiment.scheduleAtCoin
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (experiment : CompatibilityFriExperiment Coins K) (coins : Coins) :
    FixedSchedule (ZMod P) K :=
  scheduleAt experiment.base
    (experiment.round0Challenge coins) (experiment.round1Challenge coins)
    (experiment.round2Challenge coins) (experiment.round3Challenge coins)

def CompatibilityFriExperiment.transcriptAt
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (experiment : CompatibilityFriExperiment Coins K) (coins : Coins) :
    IdealTranscript K :=
  fullTranscript experiment.family
    (experiment.round0Challenge coins) (experiment.round1Challenge coins)
    (experiment.round2Challenge coins) (experiment.round3Challenge coins)

abbrev CompatibilityFriExperiment.CandidateAt
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (experiment : CompatibilityFriExperiment Coins K) (coins : Coins) :=
  {candidate // candidate ∈ initialCandidateList
    (concreteCodeEncoders experiment.base releasedEvaluationPoints)
    (experiment.transcriptAt coins)}

/-! ## The smallest honest ideal-event connection -/

/-- Events for one ideal accepted-false experiment.  The two unbounded ideal
terms are separated so that a statement-decoding/binding gap is not hidden
inside a generic relation budget. -/
structure ReleasedIdealAcceptedFalseEvents (Coins K : Type*)
    [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] where
  fri : CompatibilityFriExperiment Coins K
  acceptedFalse : Set Coins
  queryMiss : Set Coins
  fourClaimBatchCollision : Set Coins
  relationOrExtractionFailure : Set Coins
  statementBindingFailure : Set Coins
  relationRepair : Set Coins

/-! ## Concrete per-coin data and proved event coverage -/

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1000000 in
/-- All mathematical data consumed by the four-way inclusion at one coin
outcome.  Only the successful modeled relation check, ideal FRI acceptance,
and false-statement condition define the `acceptedFalse` event below; they are
not required to hold for every coin. -/
structure ReleasedIdealAcceptedFalseExperimentData
    (Coins K : Type*) [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (rc : RoundConstants)
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest) where
  fri : CompatibilityFriExperiment Coins K
  poseidon : Poseidon2Faithful rc deployedOwner deployedNote
    deployedNullifier deployedNode
  queries : Coins → QuerySchedule 18 131072
  relationFamily : (coins : Coins) →
    CoherentCandidateFamily K (fri.CandidateAt coins)
  records : (coins : Coins) → CandidateRecords (fri.CandidateAt coins) K
  statement : Coins → V5PublicStatement
  challenges : Coins → TwelveRelationChallenges K
  scheduleMatches : ∀ coins, ScheduleMatchesRelationChallenges
    (fri.scheduleAtCoin coins) (challenges coins)
  familyMatches : ∀ coins, FamilyMatchesFriTranscript
    (concreteCodeEncoders fri.base releasedEvaluationPoints)
    (fri.transcriptAt coins) (relationFamily coins) (challenges coins)

/-- The four still-unbounded earlier candidate failures other than the
separately bounded batching collision and public-statement binding. -/
def CandidateRelationOrExtractionFailure
    (rc : RoundConstants)
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (statement : V5PublicStatement)
    (record : CandidateSemanticRecord K) : Prop :=
  FourClaimBatchEquationFailure execution challenges record ∨
    CombinedLaneBindingFailure execution record ∨
    ArithmeticResidualFailure execution challenges statement record ∨
    HashMerkleResidualFailure rc execution challenges statement record

theorem candidateEarlierFailure_iff_batch_or_relationOrExtraction_or_statement
    (rc : RoundConstants)
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (statement : V5PublicStatement)
    (record : CandidateSemanticRecord K) :
    CandidateEarlierFailure rc execution challenges statement record ↔
      FourClaimBatchCollision record ∨
        CandidateRelationOrExtractionFailure rc execution challenges statement
            record ∨
          PublicStatementBindingFailure execution challenges statement record := by
  simp only [CandidateEarlierFailure, CandidateRelationOrExtractionFailure]
  aesop

def ReleasedIdealAcceptedFalseExperimentData.acceptedFalse
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (data : ReleasedIdealAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode) : Set Coins :=
  {coins |
    (∃ output, runModeledRelationVerifier (data.relationFamily coins)
      (data.challenges coins) = some output) ∧
    IdealAccepts (data.fri.scheduleAtCoin coins)
      (data.fri.transcriptAt coins) (data.queries coins) ∧
    ¬ StatementHasSpendWitness (data.statement coins) deployedOwner
      deployedNote deployedNullifier deployedNode}

def ReleasedIdealAcceptedFalseExperimentData.queryMiss
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (data : ReleasedIdealAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode) : Set Coins :=
  {coins | QueryPhaseFailure (data.fri.scheduleAtCoin coins)
    (data.fri.transcriptAt coins) (data.queries coins)}

def ReleasedIdealAcceptedFalseExperimentData.fourClaimBatchCollision
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (data : ReleasedIdealAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode) : Set Coins :=
  {coins | ∃ candidate,
    FourClaimBatchCollision (data.records coins candidate)}

def ReleasedIdealAcceptedFalseExperimentData.relationOrExtractionFailure
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (data : ReleasedIdealAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode) : Set Coins :=
  {coins | ∃ candidate,
    CandidateRelationOrExtractionFailure rc
      ((data.relationFamily coins).execution candidate)
      (data.challenges coins) (data.statement coins)
      (data.records coins candidate)}

def ReleasedIdealAcceptedFalseExperimentData.statementBindingFailure
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (data : ReleasedIdealAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode) : Set Coins :=
  {coins | ∃ candidate,
    PublicStatementBindingFailure
      ((data.relationFamily coins).execution candidate)
      (data.challenges coins) (data.statement coins)
      (data.records coins candidate)}

def ReleasedIdealAcceptedFalseExperimentData.relationRepair
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (data : ReleasedIdealAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode) : Set Coins :=
  {coins |
    Fintype.card (data.fri.CandidateAt coins) ≤ 240 ∧
      data.challenges coins ∈ boundedCandidateRepairEvent
        (fun candidate =>
          ((data.relationFamily coins).execution candidate).adaptiveData)}

def ReleasedIdealAcceptedFalseExperimentData.toEvents
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (data : ReleasedIdealAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode) :
    ReleasedIdealAcceptedFalseEvents Coins K where
  fri := data.fri
  acceptedFalse := data.acceptedFalse
  queryMiss := data.queryMiss
  fourClaimBatchCollision := data.fourClaimBatchCollision
  relationOrExtractionFailure := data.relationOrExtractionFailure
  statementBindingFailure := data.statementBindingFailure
  relationRepair := data.relationRepair

/-- Exact pointwise bridge from the conclusion of
`released_ideal_accepted_false_prefix_inclusion` to experiment events.

To construct this field, apply that theorem at `coins`; map its concrete query
and repair branches to the corresponding sets, its exact compatibility event
to `events.fri.event`, and split `CandidateEarlierFailure` between the named
relation/extraction and statement-binding sets. -/
structure ReleasedIdealAcceptedFalseCoverage
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (events : ReleasedIdealAcceptedFalseEvents Coins K) : Prop where
  pointwise : ∀ coins, coins ∈ events.acceptedFalse →
    coins ∈ events.queryMiss ∨
    coins ∈ events.fri.event ∨
    coins ∈ events.fourClaimBatchCollision ∨
    coins ∈ events.relationOrExtractionFailure ∨
    coins ∈ events.statementBindingFailure ∨
    coins ∈ events.relationRepair

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1000000 in
/-- The concrete experiment obtains its event coverage by applying the proved
prefix-timed accepted-false inclusion independently at each coin outcome. -/
theorem ReleasedIdealAcceptedFalseExperimentData.toEvents_coverage
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (data : ReleasedIdealAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode) :
    ReleasedIdealAcceptedFalseCoverage data.toEvents := by
  constructor
  intro coins haccepted
  rcases haccepted with ⟨hmodeled, hfri, hnoWitness⟩
  have inclusion := released_ideal_accepted_false_prefix_inclusion
    rc data.poseidon data.fri.base data.fri.family (data.queries coins)
    data.fri.finalDomain data.fri.inverseTables data.fri.publishedDecoding
    (data.fri.round0Challenge coins) (data.fri.round1Challenge coins)
    (data.fri.round2Challenge coins) (data.fri.round3Challenge coins)
    (data.relationFamily coins) (data.records coins) (data.statement coins)
    (data.challenges coins) (data.scheduleMatches coins)
    (data.familyMatches coins) hmodeled hfri hnoWitness
  rcases inclusion with hquery | hcompatibility | hearlier | hrepair
  · exact Or.inl hquery
  · exact Or.inr (Or.inl hcompatibility)
  · rcases hearlier with ⟨candidate, hfailure⟩
    rcases
      (candidateEarlierFailure_iff_batch_or_relationOrExtraction_or_statement
      rc ((data.relationFamily coins).execution candidate)
      (data.challenges coins) (data.statement coins)
      (data.records coins candidate)).mp hfailure with
      hbatch | hrelation | hstatement
    · exact Or.inr (Or.inr (Or.inl ⟨candidate, hbatch⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨candidate, hrelation⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨candidate, hstatement⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hrepair))))

/-- These seven inequalities are precisely the distributional connections
needed for the checked raw core and batching terms.  In particular, the FRI
fields assert that the four projected challenges have the required fresh
uniform law; cardinality alone does not prove that about arbitrary `Coins`. -/
structure ReleasedIdealAcceptedFalseRawConnections
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    [MeasurableSpace Coins]
    (measure : Measure Coins)
    (events : ReleasedIdealAcceptedFalseEvents Coins K) : Prop where
  queryMiss : measure.real events.queryMiss ≤ rawQ18IdealMissBound
  friRound0 : measure.real events.fri.round0Event ≤ rawFriFibreBound 0
  friRound1 : measure.real events.fri.round1Event ≤ rawFriFibreBound 1
  friRound2 : measure.real events.fri.round2Event ≤ rawFriFibreBound 2
  friRound3 : measure.real events.fri.round3Event ≤ rawFriFibreBound 3
  relationRepair : measure.real events.relationRepair ≤ rawRelationRepairBound
  /-- This follows from `recordBatchCollisionSet_card_le_720` when candidate
  discrepancies are fixed before a uniform `kappa` is sampled. -/
  fourClaimBatchCollision :
    measure.real events.fourClaimBatchCollision ≤
      rawFourClaimBatchCollisionBound

/-! ## Reuse of the raw core ledger -/

def emptySecurityFailureEvents (Coins : Type*) : SecurityFailureEvents Coins where
  event := fun _kind => ∅

def emptyRuntimeFailurePredicates (Coins : Type*) :
    AspisV5TheftStateTransitionReduction.RuntimeFailurePredicates Coins where
  rustStateModelMismatch := fun _ => False
  systemProgramOrPdaMismatch := fun _ => False
  writableAccountLockFailure := fun _ => False
  rejectedTransactionRollbackFailure := fun _ => False
  committedMarkerPersistenceFailure := fun _ => False
  finalizedStateObservationFailure := fun _ => False
  closeOrRefundModelMismatch := fun _ => False

def ReleasedIdealAcceptedFalseEvents.coreLedger
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (events : ReleasedIdealAcceptedFalseEvents Coins K) :
    FinalSecurityEvents Coins where
  queryAndFinalWorkMiss := events.queryMiss
  friRound0 := events.fri.round0Event
  friRound1 := events.fri.round1Event
  friRound2 := events.fri.round2Event
  friRound3 := events.fri.round3Event
  relationRepair := events.relationRepair
  transcriptAndPrimitives := emptySecurityFailureEvents Coins
  acceptedRunRelationBridge := ∅
  proofMerkleOpeningBridge := ∅
  victimCredentialRecovery := ∅
  runtime := emptyRuntimeFailurePredicates Coins

theorem ReleasedIdealAcceptedFalseRawConnections.toCoreBounds
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    [MeasurableSpace Coins]
    (measure : Measure Coins)
    (events : ReleasedIdealAcceptedFalseEvents Coins K)
    (connections : ReleasedIdealAcceptedFalseRawConnections measure events) :
    AssumedRawOneProofCoreBounds measure events.coreLedger where
  queryMiss := connections.queryMiss
  friRound0 := connections.friRound0
  friRound1 := connections.friRound1
  friRound2 := connections.friRound2
  friRound3 := connections.friRound3
  relationRepair := connections.relationRepair

@[simp] theorem ReleasedIdealAcceptedFalseEvents.mem_coreFailure_iff
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (events : ReleasedIdealAcceptedFalseEvents Coins K) (coins : Coins) :
    coins ∈ rawOneProofCoreFailure events.coreLedger ↔
      coins ∈ events.queryMiss ∨
      coins ∈ events.fri.round0Event ∨
      coins ∈ events.fri.round1Event ∨
      coins ∈ events.fri.round2Event ∨
      coins ∈ events.fri.round3Event ∨
      coins ∈ events.relationRepair := by
  simp [rawOneProofCoreFailure, rawOneProofCoreEvents,
    ReleasedIdealAcceptedFalseEvents.coreLedger]

theorem released_ideal_accepted_false_subset_core_plus_explicit
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (events : ReleasedIdealAcceptedFalseEvents Coins K)
    (coverage : ReleasedIdealAcceptedFalseCoverage events) :
    events.acceptedFalse ⊆
      ((rawOneProofCoreFailure events.coreLedger ∪
        events.fourClaimBatchCollision) ∪
        events.relationOrExtractionFailure) ∪
        events.statementBindingFailure := by
  intro coins haccepted
  rcases coverage.pointwise coins haccepted with
    hquery | hfri | hbatch | hrelation | hstatement | hrepair
  · apply Or.inl
    apply Or.inl
    apply Or.inl
    exact (events.mem_coreFailure_iff coins).mpr (Or.inl hquery)
  · have hfri' :
        events.fri.round0Challenge coins ∈ events.fri.badSets.round0 ∨
        events.fri.round1Challenge coins ∈
            events.fri.badSets.round1 (events.fri.round0Challenge coins) ∨
        events.fri.round2Challenge coins ∈
            events.fri.badSets.round2 (events.fri.round0Challenge coins)
              (events.fri.round1Challenge coins) ∨
        events.fri.round3Challenge coins ∈
            events.fri.badSets.round3 (events.fri.round0Challenge coins)
              (events.fri.round1Challenge coins)
              (events.fri.round2Challenge coins) := by
      simpa only [CompatibilityFriExperiment.event, Set.mem_setOf_eq,
        PrefixConditionedBadSets.Occurs] using hfri
    rcases hfri' with h0 | h1 | h2 | h3
    · have hcore := (events.mem_coreFailure_iff coins).mpr
        (Or.inr (Or.inl h0))
      exact Or.inl (Or.inl (Or.inl hcore))
    · have hcore := (events.mem_coreFailure_iff coins).mpr
        (Or.inr (Or.inr (Or.inl h1)))
      exact Or.inl (Or.inl (Or.inl hcore))
    · have hcore := (events.mem_coreFailure_iff coins).mpr
        (Or.inr (Or.inr (Or.inr (Or.inl h2))))
      exact Or.inl (Or.inl (Or.inl hcore))
    · have hcore := (events.mem_coreFailure_iff coins).mpr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h3)))))
      exact Or.inl (Or.inl (Or.inl hcore))
  · exact Or.inl (Or.inl (Or.inr hbatch))
  · exact Or.inl (Or.inr hrelation)
  · exact Or.inr hstatement
  · exact Or.inl (Or.inl (Or.inl
      ((events.mem_coreFailure_iff coins).mpr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hrepair))))))))

/-! ## Explicit ideal one-proof probability -/

theorem released_ideal_accepted_false_probability_le_raw_core_plus_explicit
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    [MeasurableSpace Coins]
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    (events : ReleasedIdealAcceptedFalseEvents Coins K)
    (coverage : ReleasedIdealAcceptedFalseCoverage events)
    (connections : ReleasedIdealAcceptedFalseRawConnections measure events) :
    measure.real events.acceptedFalse ≤
      (rawCoreSubtotal + rawFourClaimBatchCollisionBound) +
        measure.real events.relationOrExtractionFailure +
        measure.real events.statementBindingFailure := by
  have hsubset := released_ideal_accepted_false_subset_core_plus_explicit
    events coverage
  have hcore := raw_one_proof_core_probability_le_subtotal measure
    events.coreLedger (connections.toCoreBounds measure events)
  calc
    measure.real events.acceptedFalse ≤
        measure.real (((rawOneProofCoreFailure events.coreLedger ∪
          events.fourClaimBatchCollision) ∪
          events.relationOrExtractionFailure) ∪
          events.statementBindingFailure) :=
      MeasureTheory.measureReal_mono hsubset
    _ ≤ measure.real
          ((rawOneProofCoreFailure events.coreLedger ∪
            events.fourClaimBatchCollision) ∪
            events.relationOrExtractionFailure) +
        measure.real events.statementBindingFailure :=
      MeasureTheory.measureReal_union_le _ _
    _ ≤ (measure.real
          (rawOneProofCoreFailure events.coreLedger ∪
            events.fourClaimBatchCollision) +
          measure.real events.relationOrExtractionFailure) +
        measure.real events.statementBindingFailure := by
      gcongr
      exact MeasureTheory.measureReal_union_le _ _
    _ ≤ ((measure.real (rawOneProofCoreFailure events.coreLedger) +
          measure.real events.fourClaimBatchCollision) +
          measure.real events.relationOrExtractionFailure) +
        measure.real events.statementBindingFailure := by
      gcongr
      exact MeasureTheory.measureReal_union_le _ _
    _ ≤ (rawCoreSubtotal + rawFourClaimBatchCollisionBound) +
          measure.real events.relationOrExtractionFailure +
        measure.real events.statementBindingFailure := by
      gcongr
      exact connections.fourClaimBatchCollision

/-- The `2^-75` number is a one-proof ideal-core bound.  The two displayed
terms are not assigned numbers by this theorem. -/
theorem released_ideal_accepted_false_probability_le_two_pow_neg_75_plus_explicit
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    [MeasurableSpace Coins]
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    (events : ReleasedIdealAcceptedFalseEvents Coins K)
    (coverage : ReleasedIdealAcceptedFalseCoverage events)
    (connections : ReleasedIdealAcceptedFalseRawConnections measure events) :
    measure.real events.acceptedFalse ≤
      (1 : Real) / 2 ^ 75 +
        measure.real events.relationOrExtractionFailure +
        measure.real events.statementBindingFailure := by
  exact (released_ideal_accepted_false_probability_le_raw_core_plus_explicit
    measure events coverage connections).trans (by
      gcongr
      exact raw_core_plus_four_claim_batch_le_two_pow_neg_75)

set_option maxRecDepth 1000000 in
/-- Concrete ideal one-proof accounting.  Unlike the generic theorem above,
the accepted-false inclusion is discharged by the deterministic theorem and
is not a premise supplied by the caller. -/
theorem released_concrete_ideal_accepted_false_probability_le_raw_core_plus_explicit
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Coins]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    (data : ReleasedIdealAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode)
    (connections : ReleasedIdealAcceptedFalseRawConnections measure
      data.toEvents) :
    measure.real data.acceptedFalse ≤
      (rawCoreSubtotal + rawFourClaimBatchCollisionBound) +
        measure.real data.relationOrExtractionFailure +
        measure.real data.statementBindingFailure := by
  exact released_ideal_accepted_false_probability_le_raw_core_plus_explicit
    measure data.toEvents data.toEvents_coverage connections

set_option maxRecDepth 1000000 in
/-- The numerical core is at most `2^-75` for one ideal proof.  The displayed
relation/extraction and statement-binding terms remain explicit. -/
theorem released_concrete_ideal_accepted_false_probability_le_two_pow_neg_75_plus_explicit
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Coins]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    (data : ReleasedIdealAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode)
    (connections : ReleasedIdealAcceptedFalseRawConnections measure
      data.toEvents) :
    measure.real data.acceptedFalse ≤
      (1 : Real) / 2 ^ 75 +
        measure.real data.relationOrExtractionFailure +
        measure.real data.statementBindingFailure := by
  exact
    released_ideal_accepted_false_probability_le_two_pow_neg_75_plus_explicit
      measure data.toEvents data.toEvents_coverage connections

/-! ## Production transfer keeps transcript/hash failure explicit -/

structure ReleasedProductionFalseSpendConnection
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (events : ReleasedIdealAcceptedFalseEvents Coins K) where
  productionFalseSpend : Set Coins
  transcriptAndHashFailures : SecurityFailureEvents Coins
  production_subset_ideal_or_hash :
    productionFalseSpend ⊆ events.acceptedFalse ∪
      AspisV5CryptographicAssumptions.totalFailure transcriptAndHashFailures

theorem released_production_false_spend_probability_le_raw_core_plus_explicit
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    [MeasurableSpace Coins]
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    (events : ReleasedIdealAcceptedFalseEvents Coins K)
    (coverage : ReleasedIdealAcceptedFalseCoverage events)
    (connections : ReleasedIdealAcceptedFalseRawConnections measure events)
    (production : ReleasedProductionFalseSpendConnection events) :
    measure.real production.productionFalseSpend ≤
      (rawCoreSubtotal + rawFourClaimBatchCollisionBound) +
        measure.real events.relationOrExtractionFailure +
        measure.real events.statementBindingFailure +
        measure.real (AspisV5CryptographicAssumptions.totalFailure
          production.transcriptAndHashFailures) := by
  calc
    measure.real production.productionFalseSpend ≤
        measure.real (events.acceptedFalse ∪
          AspisV5CryptographicAssumptions.totalFailure
            production.transcriptAndHashFailures) :=
      MeasureTheory.measureReal_mono production.production_subset_ideal_or_hash
    _ ≤ measure.real events.acceptedFalse +
          measure.real (AspisV5CryptographicAssumptions.totalFailure
            production.transcriptAndHashFailures) :=
      MeasureTheory.measureReal_union_le _ _
    _ ≤ (rawCoreSubtotal + rawFourClaimBatchCollisionBound) +
          measure.real events.relationOrExtractionFailure +
          measure.real events.statementBindingFailure +
          measure.real (AspisV5CryptographicAssumptions.totalFailure
            production.transcriptAndHashFailures) := by
      gcongr
      exact released_ideal_accepted_false_probability_le_raw_core_plus_explicit
        measure events coverage connections

theorem released_production_false_spend_probability_le_two_pow_neg_75_plus_explicit
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    [MeasurableSpace Coins]
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    (events : ReleasedIdealAcceptedFalseEvents Coins K)
    (coverage : ReleasedIdealAcceptedFalseCoverage events)
    (connections : ReleasedIdealAcceptedFalseRawConnections measure events)
    (production : ReleasedProductionFalseSpendConnection events) :
    measure.real production.productionFalseSpend ≤
      (1 : Real) / 2 ^ 75 +
        measure.real events.relationOrExtractionFailure +
        measure.real events.statementBindingFailure +
        measure.real (AspisV5CryptographicAssumptions.totalFailure
          production.transcriptAndHashFailures) := by
  exact (released_production_false_spend_probability_le_raw_core_plus_explicit
    measure events coverage connections production).trans (by
      gcongr
      exact raw_core_plus_four_claim_batch_le_two_pow_neg_75)

set_option maxRecDepth 1000000 in
/-- Concrete production accounting with the deterministic ideal inclusion
already discharged.  The Rust/transcript/hash reduction remains visible in
`production`, rather than being folded into the `2^-75` ideal-core number. -/
theorem released_concrete_production_false_spend_probability_le_raw_core_plus_explicit
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Coins]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    (data : ReleasedIdealAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode)
    (connections : ReleasedIdealAcceptedFalseRawConnections measure
      data.toEvents)
    (production : ReleasedProductionFalseSpendConnection data.toEvents) :
    measure.real production.productionFalseSpend ≤
      (rawCoreSubtotal + rawFourClaimBatchCollisionBound) +
        measure.real data.relationOrExtractionFailure +
        measure.real data.statementBindingFailure +
        measure.real (AspisV5CryptographicAssumptions.totalFailure
          production.transcriptAndHashFailures) := by
  exact released_production_false_spend_probability_le_raw_core_plus_explicit
    measure data.toEvents data.toEvents_coverage connections production

set_option maxRecDepth 1000000 in
/-- One-proof production corollary.  This is deliberately not an all-time or
multi-attempt theft bound: the two mathematical bridge terms and the
transcript/hash term are still explicit, and repeated attempts are accounted
for separately below. -/
theorem released_concrete_production_false_spend_probability_le_two_pow_neg_75_plus_explicit
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Coins]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    (data : ReleasedIdealAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode)
    (connections : ReleasedIdealAcceptedFalseRawConnections measure
      data.toEvents)
    (production : ReleasedProductionFalseSpendConnection data.toEvents) :
    measure.real production.productionFalseSpend ≤
      (1 : Real) / 2 ^ 75 +
        measure.real data.relationOrExtractionFailure +
        measure.real data.statementBindingFailure +
        measure.real (AspisV5CryptographicAssumptions.totalFailure
          production.transcriptAndHashFailures) := by
  exact
    released_production_false_spend_probability_le_two_pow_neg_75_plus_explicit
      measure data.toEvents data.toEvents_coverage connections production

/-! ## Adaptive attempt/query-budget accounting -/

/-- The next causal transcript family is selected from prior completed
four-challenge tuples only.  The current fresh tuple is unavailable. -/
structure CompatibilityAdaptiveFriAttemptPlan (K : Type*) where
  familyAt : List (AspisV5FriAdaptiveUnmatched.FourChallenges K) →
    CausalTranscriptFamily K

noncomputable def CompatibilityAdaptiveFriAttemptPlan.toFreshOraclePlan
    (plan : CompatibilityAdaptiveFriAttemptPlan K)
    (base : FixedSchedule (ZMod P) K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)) :
    AdaptiveFreshOraclePlan
      (AspisV5FriAdaptiveUnmatched.FourChallenges K) where
  badAt history := prefixBadChallengeTuples
    (releasedCompatibilityBadSets base (plan.familyAt history) hfinal htables
      hpublished)

theorem compatibilityAdaptiveFriPlan_everyFreshBadSetBounded
    (plan : CompatibilityAdaptiveFriAttemptPlan K)
    (base : FixedSchedule (ZMod P) K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)) :
    EveryFreshBadSetBounded
      (plan.toFreshOraclePlan base hfinal htables hpublished)
      (releasedFriRawPerAttemptBound (K := K)) := by
  intro history
  have h := releasedCompatibilityBadProbability_le base
    (plan.familyAt history) hfinal htables hpublished
  change
    ((prefixBadChallengeTuples
      (releasedCompatibilityBadSets base (plan.familyAt history) hfinal htables
        hpublished)).card : Rat) /
        Fintype.card (AspisV5FriAdaptiveUnmatched.FourChallenges K) ≤
      releasedFriRawPerAttemptBound (K := K)
  rw [show Fintype.card
      (AspisV5FriAdaptiveUnmatched.FourChallenges K) = Fintype.card K ^ 4 by
    simp [AspisV5FriAdaptiveUnmatched.FourChallenges, pow_succ]]
  exact h

/-- This is an adaptive attacker bound, unlike the one-proof `2^-75`
corollary above.  `attempts` is the number of completed fresh ideal attempts. -/
theorem adaptiveCompatibilityReleasedFriFailureProbability_le_attempts_mul
    (plan : CompatibilityAdaptiveFriAttemptPlan K)
    (base : FixedSchedule (ZMod P) K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (attempts : Nat) :
    adaptiveFailureProbabilityFromStart
        (plan.toFreshOraclePlan base hfinal htables hpublished) attempts ≤
      (attempts : Rat) * releasedFriRawPerAttemptBound (K := K) := by
  exact adaptiveFailureProbabilityFromStart_le_attempts_mul _ _
    releasedFriRawPerAttemptBound_nonnegative
    (compatibilityAdaptiveFriPlan_everyFreshBadSetBounded plan base hfinal
      htables hpublished) attempts

theorem adaptiveCompatibilityReleasedFriFailureProbability_le_queryBudget_mul
    (plan : CompatibilityAdaptiveFriAttemptPlan K)
    (base : FixedSchedule (ZMod P) K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (attempts freshQueryBudget : Nat)
    (hattempts : attempts ≤ freshQueryBudget) :
    adaptiveFailureProbabilityFromStart
        (plan.toFreshOraclePlan base hfinal htables hpublished) attempts ≤
      (freshQueryBudget : Rat) * releasedFriRawPerAttemptBound (K := K) := by
  exact adaptiveFailureProbabilityFromStart_le_queryBudget_mul _ _
    releasedFriRawPerAttemptBound_nonnegative
    (compatibilityAdaptiveFriPlan_everyFreshBadSetBounded plan base hfinal
      htables hpublished) attempts freshQueryBudget hattempts

/-- Exact remaining production reduction for the adaptive compatibility
event.  It must map Rust/SHA-256 executions to completed fresh attempts and
account for repeated queries, rejection sampling, interleaving, and any
random-oracle/implementation gap. -/
theorem productionCompatibilityReleasedFriFailureProbability_le_queryBudget_mul_add_gap
    {Coins : Type*}
    [Fintype Coins] [DecidableEq Coins] [Nonempty Coins]
    (productionFailure : Finset Coins)
    (plan : CompatibilityAdaptiveFriAttemptPlan K)
    (base : FixedSchedule (ZMod P) K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (completedAttempts freshQueryBudget : Nat)
    (hashAndSamplingGap : Rat)
    (connection : ProductionAdaptiveFreshOracleConnection Coins
      (AspisV5FriAdaptiveUnmatched.FourChallenges K) productionFailure
      (plan.toFreshOraclePlan base hfinal htables hpublished)
      completedAttempts freshQueryBudget hashAndSamplingGap) :
    finiteUniformEventProbability productionFailure ≤
      (freshQueryBudget : Rat) * releasedFriRawPerAttemptBound (K := K) +
        hashAndSamplingGap := by
  exact productionFailureProbability_le_queryBudget_mul_add_gap
    productionFailure
    (plan.toFreshOraclePlan base hfinal htables hpublished)
    completedAttempts freshQueryBudget
    (releasedFriRawPerAttemptBound (K := K)) hashAndSamplingGap
    releasedFriRawPerAttemptBound_nonnegative
    (compatibilityAdaptiveFriPlan_everyFreshBadSetBounded plan base hfinal
      htables hpublished)
    connection

/-! ## Audit -/

#print axioms CompatibilityFriExperiment.event_eq_round_union
#print axioms ReleasedIdealAcceptedFalseExperimentData.toEvents_coverage
#print axioms released_ideal_accepted_false_subset_core_plus_explicit
#print axioms released_ideal_accepted_false_probability_le_raw_core_plus_explicit
#print axioms
  released_ideal_accepted_false_probability_le_two_pow_neg_75_plus_explicit
#print axioms
  released_concrete_ideal_accepted_false_probability_le_raw_core_plus_explicit
#print axioms
  released_concrete_ideal_accepted_false_probability_le_two_pow_neg_75_plus_explicit
#print axioms
  released_production_false_spend_probability_le_raw_core_plus_explicit
#print axioms
  released_production_false_spend_probability_le_two_pow_neg_75_plus_explicit
#print axioms
  released_concrete_production_false_spend_probability_le_raw_core_plus_explicit
#print axioms
  released_concrete_production_false_spend_probability_le_two_pow_neg_75_plus_explicit
#print axioms compatibilityAdaptiveFriPlan_everyFreshBadSetBounded
#print axioms adaptiveCompatibilityReleasedFriFailureProbability_le_attempts_mul
#print axioms
  adaptiveCompatibilityReleasedFriFailureProbability_le_queryBudget_mul
#print axioms
  productionCompatibilityReleasedFriFailureProbability_le_queryBudget_mul_add_gap

end AspisV5ForwardAcceptedFalseRawAccounting
