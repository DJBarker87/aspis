import AspisFormal.V5RelationStressSourceBridge
import AspisFormal.V5MerkleAuthenticationBinding
import AspisFormal.V5TranscriptConnection
import AspisFormal.V5FriReleasedAdaptiveExtraction
import AspisFormal.V5FriGlobalCausalStrategy
import AspisFormal.V5Tag67AcceptedFalseInclusion

/-!
# One accepted V5 execution: deterministic security reduction

This file joins the maintained source-shaped relation loop, transcript
schedule, authenticated private openings, released FRI extraction, and spend
relation.  It does not turn an unfinished implementation correspondence into
an assumption named after the desired conclusion.  Instead, the final theorem
returns every still-open boundary as a direct equality failure or as one of
the already defined mathematical failure events.

In particular, backwards FRI extraction uses one response strategy fixed over
the whole four-challenge space.  `V5FriGlobalCausalStrategy` constructs that
strategy in Lean from the causal transcript family; it is no longer an
implementation-facing assumption.
-/

namespace AspisV5AcceptedExecutionSecurityBridge

open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriCompatibleCandidateChain
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriGlobalCausalStrategy
open AspisV5FriPublishedOutputEncoderDecoding
open AspisV5FriRelationCandidateBridge
open AspisV5FriReleasedAdaptiveExtraction
open AspisV5FriReleasedLineGeometry
open AspisV5MerkleAuthenticationBinding
open AspisV5NonceWorkAuthentication
open AspisV5RelationStressSourceBridge
open AspisV5Tag67AcceptedFalseInclusion
open AspisV5Tag67CandidateTraceExtraction
open AspisV5Tag67FalseAcceptanceDecomposition
open AspisV5Tag67ModeledRelationAcceptanceBridge
open AspisV5Tag67RelationListInclusion
open AspisV5TranscriptConnection
open AspisV5WithoutReplacementQuerySoundness

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [NeZero (2 : K)]

/-! ## The exact data selected by one accepted execution -/

/-- The four fold challenges in the scalar relation input determine the one
FRI schedule used for this execution. -/
def acceptedSchedule
    (base : FixedSchedule (ZMod AspisCircleGroupOrder.P) K)
    (input : SourceRelationInput K) :
    FixedSchedule (ZMod AspisCircleGroupOrder.P) K :=
  scheduleAt base input.round0.alpha input.round1.alpha
    input.round2.alpha input.round3.alpha

/-- The causally committed words evaluated at the four challenges consumed by
this execution. -/
def acceptedTranscript (family : CausalTranscriptFamily K)
    (input : SourceRelationInput K) : IdealTranscript K :=
  fullTranscript family input.round0.alpha input.round1.alpha
    input.round2.alpha input.round3.alpha

/-- The one initial decoder list.  Later rounds never introduce independent
candidate choices. -/
abbrev AcceptedCandidate
    (base : FixedSchedule (ZMod AspisCircleGroupOrder.P) K)
    (causalFamily : CausalTranscriptFamily K)
    (input : SourceRelationInput K) :=
  { candidate // candidate ∈ initialCandidateList
      (concreteCodeEncoders base releasedEvaluationPoints)
      (acceptedTranscript causalFamily input) }

/-! ## Authenticated opened values and exact query arithmetic -/

/-- Decoding of one opened private-tree record into the four field elements
used at its queried FRI fibre.  The production proof still has to instantiate
this function with its exact little-endian field decoder. -/
structure OpeningFibreDecoder (K : Type*) where
  decode : V5PrivateSection -> List AspisV5MerkleAuthenticationBinding.Byte ->
    Fin 4 -> K

/-- Four values decoded from one accepted leaf. -/
def decodedFibre {Digest : Type*}
    (decoder : OpeningFibreDecoder K)
    (hashing : MerkleHashing Digest)
    {roots : V5PrivateRoots Digest} {querySet : Finset V5Query}
    (forest : AcceptedV5Forest hashing roots querySet)
    (tree : V5PrivateSection) (query : V5Query) (hq : query ∈ querySet) :
    Fin 4 -> K :=
  decoder.decode tree
    (openedValue (forest.opening tree query hq))

/-- Concrete byte-to-field projection from an authenticated forest to the
four maintained FRI words.  C2 is included explicitly even though it is used
by the semantic trace rather than by the four FRI fold equations. -/
structure ForestProjectsToTranscript {Digest : Type*}
    (decoder : OpeningFibreDecoder K)
    (hashing : MerkleHashing Digest)
    {roots : V5PrivateRoots Digest} {querySet : Finset V5Query}
    (forest : AcceptedV5Forest hashing roots querySet)
    (transcript : IdealTranscript K)
    (expectedC2 : V5Query -> Fin 4 -> K) : Prop where
  circle : ∀ query hq slot,
    decodedFibre decoder hashing forest .c1 query hq slot =
      transcript.layer0 (childIndex query slot)
  c2 : ∀ query hq slot,
    decodedFibre decoder hashing forest .c2 query hq slot =
      expectedC2 query slot
  line1 : ∀ query hq slot,
    decodedFibre decoder hashing forest .line1 query hq slot =
      transcript.layer1 (childIndex (queryParent1 query) slot)
  line2 : ∀ query hq slot,
    decodedFibre decoder hashing forest .line2 query hq slot =
      transcript.layer2 (childIndex (queryParent2 query) slot)
  line3 : ∀ query hq slot,
    decodedFibre decoder hashing forest .line3 query hq slot =
      transcript.layer3 (childIndex (queryParent3 query) slot)

/-- Outside a concrete Merkle hash collision, any second accepted forest under
the same roots and indices has the same decoded values and therefore the same
word projection. -/
theorem forestProjectsToTranscript_of_collisionFree
    {Digest : Type*}
    (decoder : OpeningFibreDecoder K)
    (hashing : MerkleHashing Digest)
    {roots : V5PrivateRoots Digest} {querySet : Finset V5Query}
    (reference accepted : AcceptedV5Forest hashing roots querySet)
    (transcript : IdealTranscript K)
    (expectedC2 : V5Query -> Fin 4 -> K)
    (hreference : ForestProjectsToTranscript decoder hashing reference
      transcript expectedC2)
    (hfree : CollisionFree hashing) :
    ForestProjectsToTranscript decoder hashing accepted transcript
      expectedC2 := by
  constructor
  · intro query hq slot
    calc
      decodedFibre decoder hashing accepted .c1 query hq slot =
          decodedFibre decoder hashing reference .c1 query hq slot := by
        unfold decodedFibre
        rw [acceptedV5Forest_values_unique hashing hfree accepted reference
          .c1 query hq]
      _ = transcript.layer0 (childIndex query slot) :=
        hreference.circle query hq slot
  · intro query hq slot
    calc
      decodedFibre decoder hashing accepted .c2 query hq slot =
          decodedFibre decoder hashing reference .c2 query hq slot := by
        unfold decodedFibre
        rw [acceptedV5Forest_values_unique hashing hfree accepted reference
          .c2 query hq]
      _ = expectedC2 query slot := hreference.c2 query hq slot
  · intro query hq slot
    calc
      decodedFibre decoder hashing accepted .line1 query hq slot =
          decodedFibre decoder hashing reference .line1 query hq slot := by
        unfold decodedFibre
        rw [acceptedV5Forest_values_unique hashing hfree accepted reference
          .line1 query hq]
      _ = transcript.layer1 (childIndex (queryParent1 query) slot) :=
        hreference.line1 query hq slot
  · intro query hq slot
    calc
      decodedFibre decoder hashing accepted .line2 query hq slot =
          decodedFibre decoder hashing reference .line2 query hq slot := by
        unfold decodedFibre
        rw [acceptedV5Forest_values_unique hashing hfree accepted reference
          .line2 query hq]
      _ = transcript.layer2 (childIndex (queryParent2 query) slot) :=
        hreference.line2 query hq slot
  · intro query hq slot
    calc
      decodedFibre decoder hashing accepted .line3 query hq slot =
          decodedFibre decoder hashing reference .line3 query hq slot := by
        unfold decodedFibre
        rw [acceptedV5Forest_values_unique hashing hfree accepted reference
          .line3 query hq]
      _ = transcript.layer3 (childIndex (queryParent3 query) slot) :=
        hreference.line3 query hq slot

/-- The exact four arithmetic comparisons made at each of the eighteen
opened query paths, stated on the decoded authenticated values rather than as
an assumed `IdealAccepts` conclusion. -/
structure ForestFriChecks {Digest : Type*}
    (decoder : OpeningFibreDecoder K)
    (hashing : MerkleHashing Digest)
    {roots : V5PrivateRoots Digest} {querySet : Finset V5Query}
    (forest : AcceptedV5Forest hashing roots querySet)
    (schedule : FixedSchedule (ZMod AspisCircleGroupOrder.P) K)
    (transcript : IdealTranscript K)
    (queries : QuerySchedule 18 131072) : Prop where
  queryMember : ∀ i, queries i ∈ querySet
  circle : ∀ i,
    circleFoldValue (schedule.alpha 0)
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.circleInv2x (queries i)))
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.circleInv2y (queries i)))
        (decodedFibre decoder hashing forest .c1 (queries i) (queryMember i)) =
      decodedFibre decoder hashing forest .line1 (queries i) (queryMember i)
        (@slotIndex 32768 (queries i))
  line1 : ∀ i,
    lineFoldValue (schedule.alpha 1)
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.line1Inverse (queryParent1 (queries i)) 0))
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.line1Inverse (queryParent1 (queries i)) 1))
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.line1Inverse (queryParent1 (queries i)) 2))
        (decodedFibre decoder hashing forest .line1 (queries i) (queryMember i)) =
      decodedFibre decoder hashing forest .line2 (queries i) (queryMember i)
        (@slotIndex 8192 (queryParent1 (queries i)))
  line2 : ∀ i,
    lineFoldValue (schedule.alpha 2)
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.line2Inverse (queryParent2 (queries i)) 0))
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.line2Inverse (queryParent2 (queries i)) 1))
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.line2Inverse (queryParent2 (queries i)) 2))
        (decodedFibre decoder hashing forest .line2 (queries i) (queryMember i)) =
      decodedFibre decoder hashing forest .line3 (queries i) (queryMember i)
        (@slotIndex 2048 (queryParent2 (queries i)))
  line3 : ∀ i,
    lineFoldValue (schedule.alpha 3)
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.line3Inverse (queryParent3 (queries i)) 0))
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.line3Inverse (queryParent3 (queries i)) 1))
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.line3Inverse (queryParent3 (queries i)) 2))
        (decodedFibre decoder hashing forest .line3 (queries i) (queryMember i)) =
      finalTensorValue
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.finalX (queryParent3 (queries i))))
        transcript.publishedFinal

/-- The source-level arithmetic comparisons plus the exact authenticated
byte projection imply the existing ideal FRI acceptance predicate. -/
theorem idealAccepts_of_forestFriChecks
    {Digest : Type*}
    (decoder : OpeningFibreDecoder K)
    (hashing : MerkleHashing Digest)
    {roots : V5PrivateRoots Digest} {querySet : Finset V5Query}
    (forest : AcceptedV5Forest hashing roots querySet)
    (schedule : FixedSchedule (ZMod AspisCircleGroupOrder.P) K)
    (transcript : IdealTranscript K)
    (expectedC2 : V5Query -> Fin 4 -> K)
    (queries : QuerySchedule 18 131072)
    (hprojection : ForestProjectsToTranscript decoder hashing forest
      transcript expectedC2)
    (hchecks : ForestFriChecks decoder hashing forest schedule transcript
      queries) :
    IdealAccepts schedule transcript queries := by
  intro i
  unfold QueryConsistent
  constructor
  · rw [circleFoldLayer_apply]
    calc
      circleFoldValue (schedule.alpha 0)
          (algebraMap (ZMod AspisCircleGroupOrder.P) K
            (schedule.circleInv2x (queries i)))
          (algebraMap (ZMod AspisCircleGroupOrder.P) K
            (schedule.circleInv2y (queries i)))
          (fun slot => transcript.layer0 (childIndex (queries i) slot)) =
          circleFoldValue (schedule.alpha 0)
            (algebraMap (ZMod AspisCircleGroupOrder.P) K
              (schedule.circleInv2x (queries i)))
            (algebraMap (ZMod AspisCircleGroupOrder.P) K
              (schedule.circleInv2y (queries i)))
            (decodedFibre decoder hashing forest .c1 (queries i)
              (hchecks.queryMember i)) := by
        congr 1
        funext slot
        exact (hprojection.circle (queries i) (hchecks.queryMember i) slot).symm
      _ = decodedFibre decoder hashing forest .line1 (queries i)
            (hchecks.queryMember i) (@slotIndex 32768 (queries i)) :=
        hchecks.circle i
      _ = transcript.layer1
            (childIndex (queryParent1 (queries i))
              (@slotIndex 32768 (queries i))) :=
        hprojection.line1 (queries i) (hchecks.queryMember i) _
      _ = transcript.layer1 (queries i) := by
        rw [childIndex_queryParent1_slotIndex]
  constructor
  · rw [lineFoldLayer_apply]
    calc
      lineFoldValue (schedule.alpha 1)
          (algebraMap (ZMod AspisCircleGroupOrder.P) K
            (schedule.line1Inverse (queryParent1 (queries i)) 0))
          (algebraMap (ZMod AspisCircleGroupOrder.P) K
            (schedule.line1Inverse (queryParent1 (queries i)) 1))
          (algebraMap (ZMod AspisCircleGroupOrder.P) K
            (schedule.line1Inverse (queryParent1 (queries i)) 2))
          (fun slot => transcript.layer1
            (childIndex (queryParent1 (queries i)) slot)) =
          lineFoldValue (schedule.alpha 1)
            (algebraMap (ZMod AspisCircleGroupOrder.P) K
              (schedule.line1Inverse (queryParent1 (queries i)) 0))
            (algebraMap (ZMod AspisCircleGroupOrder.P) K
              (schedule.line1Inverse (queryParent1 (queries i)) 1))
            (algebraMap (ZMod AspisCircleGroupOrder.P) K
              (schedule.line1Inverse (queryParent1 (queries i)) 2))
            (decodedFibre decoder hashing forest .line1 (queries i)
              (hchecks.queryMember i)) := by
        congr 1
        funext slot
        exact (hprojection.line1 (queries i) (hchecks.queryMember i) slot).symm
      _ = decodedFibre decoder hashing forest .line2 (queries i)
            (hchecks.queryMember i)
            (@slotIndex 8192 (queryParent1 (queries i))) :=
        hchecks.line1 i
      _ = transcript.layer2
            (childIndex (queryParent2 (queries i))
              (@slotIndex 8192 (queryParent1 (queries i)))) :=
        hprojection.line2 (queries i) (hchecks.queryMember i) _
      _ = transcript.layer2 (queryParent1 (queries i)) := by
        rw [childIndex_queryParent2_slotIndex]
  constructor
  · rw [lineFoldLayer_apply]
    calc
      lineFoldValue (schedule.alpha 2)
          (algebraMap (ZMod AspisCircleGroupOrder.P) K
            (schedule.line2Inverse (queryParent2 (queries i)) 0))
          (algebraMap (ZMod AspisCircleGroupOrder.P) K
            (schedule.line2Inverse (queryParent2 (queries i)) 1))
          (algebraMap (ZMod AspisCircleGroupOrder.P) K
            (schedule.line2Inverse (queryParent2 (queries i)) 2))
          (fun slot => transcript.layer2
            (childIndex (queryParent2 (queries i)) slot)) =
          lineFoldValue (schedule.alpha 2)
            (algebraMap (ZMod AspisCircleGroupOrder.P) K
              (schedule.line2Inverse (queryParent2 (queries i)) 0))
            (algebraMap (ZMod AspisCircleGroupOrder.P) K
              (schedule.line2Inverse (queryParent2 (queries i)) 1))
            (algebraMap (ZMod AspisCircleGroupOrder.P) K
              (schedule.line2Inverse (queryParent2 (queries i)) 2))
            (decodedFibre decoder hashing forest .line2 (queries i)
              (hchecks.queryMember i)) := by
        congr 1
        funext slot
        exact (hprojection.line2 (queries i) (hchecks.queryMember i) slot).symm
      _ = decodedFibre decoder hashing forest .line3 (queries i)
            (hchecks.queryMember i)
            (@slotIndex 2048 (queryParent2 (queries i))) :=
        hchecks.line2 i
      _ = transcript.layer3
            (childIndex (queryParent3 (queries i))
              (@slotIndex 2048 (queryParent2 (queries i)))) :=
        hprojection.line3 (queries i) (hchecks.queryMember i) _
      _ = transcript.layer3 (queryParent2 (queries i)) := by
        rw [childIndex_queryParent3_slotIndex]
  · rw [lineFoldLayer_apply]
    calc
      lineFoldValue (schedule.alpha 3)
          (algebraMap (ZMod AspisCircleGroupOrder.P) K
            (schedule.line3Inverse (queryParent3 (queries i)) 0))
          (algebraMap (ZMod AspisCircleGroupOrder.P) K
            (schedule.line3Inverse (queryParent3 (queries i)) 1))
          (algebraMap (ZMod AspisCircleGroupOrder.P) K
            (schedule.line3Inverse (queryParent3 (queries i)) 2))
          (fun slot => transcript.layer3
            (childIndex (queryParent3 (queries i)) slot)) =
          lineFoldValue (schedule.alpha 3)
            (algebraMap (ZMod AspisCircleGroupOrder.P) K
              (schedule.line3Inverse (queryParent3 (queries i)) 0))
            (algebraMap (ZMod AspisCircleGroupOrder.P) K
              (schedule.line3Inverse (queryParent3 (queries i)) 1))
            (algebraMap (ZMod AspisCircleGroupOrder.P) K
              (schedule.line3Inverse (queryParent3 (queries i)) 2))
            (decodedFibre decoder hashing forest .line3 (queries i)
              (hchecks.queryMember i)) := by
        congr 1
        funext slot
        exact (hprojection.line3 (queries i) (hchecks.queryMember i) slot).symm
      _ = finalTensorValue
            (algebraMap (ZMod AspisCircleGroupOrder.P) K
              (schedule.finalX (queryParent3 (queries i))))
            transcript.publishedFinal := hchecks.line3 i

/-! ## Exact transcript and positioned-work projection -/

/-- Equalities connecting this scalar relation input, this Rust transcript
driver result, and this query set.  Each field names a value actually consumed
by the source-shaped verifier. -/
structure TranscriptExecutionProjection {PointValue : Type*}
    (input : SourceRelationInput K)
    (transcriptInput : V5TranscriptInputs)
    (derived : V5DerivedValues K PointValue)
    (driverResult : V5TranscriptDriverResult K PointValue)
    (querySet : Finset V5Query)
    (queries : QuerySchedule 18 131072) : Prop where
  driver : driverResult = sourceShapedTranscriptDriver transcriptInput derived
  firstMix : ∀ round : Fin 4,
    (![input.round0.firstMix, input.round1.firstMix,
        input.round2.firstMix, input.round3.firstMix] round) =
      derived.oodMix round 0
  secondMix : ∀ round : Fin 4,
    (![input.round0.secondMix, input.round1.secondMix,
        input.round2.secondMix, input.round3.secondMix] round) =
      derived.oodMix round 1
  foldChallenge : ∀ round : Fin 4,
    (![input.round0.alpha, input.round1.alpha,
        input.round2.alpha, input.round3.alpha] round) =
      derived.foldChallenge round
  queryPositions : derived.queries = List.ofFn (fun i => (queries i).val)
  querySetExact : querySet = Finset.univ.image queries

/-- Exact placement of the six nonce fields and the values sampled after each
successful work check. -/
structure WorkExecutionProjection {PointValue State : Type*}
    (input : V5TranscriptInputs)
    (derived : V5DerivedValues K PointValue)
    (workInputs : PositionedWorkInputs State (SqueezeResult K PointValue)) : Prop where
  nonce : input.nonce = workInputs.nonce
  batchNext : workInputs.nextResult .batch = .field derived.gamma
  foldNext : ∀ round,
    workInputs.nextResult (.fold round) = .field (derived.foldChallenge round)
  finalNext : workInputs.nextResult .finalQuery = .queries derived.queries

theorem scheduledQuery_mem_of_projection
    {PointValue : Type*}
    (input : SourceRelationInput K)
    (transcriptInput : V5TranscriptInputs)
    (derived : V5DerivedValues K PointValue)
    (driverResult : V5TranscriptDriverResult K PointValue)
    (querySet : Finset V5Query)
    (queries : QuerySchedule 18 131072)
    (projection : TranscriptExecutionProjection input transcriptInput derived
      driverResult querySet queries) :
    ∀ i, queries i ∈ querySet := by
  intro i
  rw [projection.querySetExact]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-! ## Final deterministic inclusion -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

/-- The result of the deterministic reduction.  Every constructor carries
the underlying event itself; this is a tagged disjunction, not an assumption
that acceptance already implies the desired repair event. -/
inductive AcceptedExecutionSecurityEvent
    (sourceRelationProjectionFailure : Prop)
    (familyProjectionFailure : Prop)
    (transcriptProjectionFailure : Prop)
    (workProjectionFailure : Prop)
    (releasedFinalDomainFailure : Prop)
    (releasedInverseTableFailure : Prop)
    (referenceForestFailure : Prop)
    (globalCausalSelectionFailure : Prop)
    (rustOpeningCorrespondenceFailure : Prop)
    (hashCollision : Prop)
    (workFailure : Prop)
    (friArithmeticFailure : Prop)
    (queryMiss : Prop)
    (countedFriFibre : Prop)
    (candidateTraceFailure : Prop)
    (relationRepair : Prop)
    (poseidonFailure : Prop)
    (publishedDecodingFailure : Prop) : Prop where
  | sourceRelationProjection (failure : sourceRelationProjectionFailure)
  | familyProjection (failure : familyProjectionFailure)
  | transcriptProjection (failure : transcriptProjectionFailure)
  | workProjection (failure : workProjectionFailure)
  | releasedFinalDomain (failure : releasedFinalDomainFailure)
  | releasedInverseTable (failure : releasedInverseTableFailure)
  | referenceForest (failure : referenceForestFailure)
  | globalCausalSelection (failure : globalCausalSelectionFailure)
  | rustOpeningCorrespondence (failure : rustOpeningCorrespondenceFailure)
  | merkleHashCollision (failure : hashCollision)
  | workCheck (failure : workFailure)
  | friArithmetic (failure : friArithmeticFailure)
  | queryPhase (failure : queryMiss)
  | friFibre (failure : countedFriFibre)
  | candidateTrace (failure : candidateTraceFailure)
  | relationRepairEvent (failure : relationRepair)
  | poseidon (failure : poseidonFailure)
  | publishedDecoding (failure : publishedDecodingFailure)

/-- A successful source-shaped false execution reaches one directly stated
remaining event.  The conclusion deliberately retains the exact missing
source projections, authenticated opening correspondence,
transcript/work/query checks, counted FRI fibre, candidate trace failures,
relation repair event, and primitive premises.  The old global-strategy slot
is `False`: the strategy is now constructed in Lean.
-/
theorem accepted_false_source_execution_event
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
    (base : FixedSchedule (ZMod AspisCircleGroupOrder.P) K)
    (causalFamily : CausalTranscriptFamily K)
    (input : SourceRelationInput K)
    (relationFamily : CoherentCandidateFamily K
      (AcceptedCandidate base causalFamily input))
    (records : CandidateRecords (AcceptedCandidate base causalFamily input) K)
    (statement : V5PublicStatement)
    (queries : QuerySchedule 18 131072)
    (decoder : OpeningFibreDecoder K)
    (expectedC2 : V5Query -> Fin 4 -> K)
    (transcriptInput : V5TranscriptInputs)
    (derived : V5DerivedValues K PointValue)
    (driverResult : V5TranscriptDriverResult K PointValue)
    (workFunctions : ExecutableWorkFunctions State
      (SqueezeResult K PointValue))
    (workInputs : PositionedWorkInputs State (SqueezeResult K PointValue))
    (hsource : ∃ output, runSourceRelationVerifier input = some output)
    (hrustOpening : rustAcceptsOpening rustInput)
    (noWitness : ¬ StatementHasSpendWitness statement deployedOwner
      deployedNote deployedNullifier deployedNode) :
    AcceptedExecutionSecurityEvent
    (¬ SourceRelationInputMatchesFamily input relationFamily)
    (¬ FamilyMatchesFriTranscript
      (concreteCodeEncoders base releasedEvaluationPoints)
      (acceptedTranscript causalFamily input) relationFamily input.challenges)
    (¬ TranscriptExecutionProjection input transcriptInput derived driverResult
      (querySetOf rustInput) queries)
    (¬ WorkExecutionProjection transcriptInput derived workInputs)
    (¬ FinalXMatchesReleasedDomain base)
    (¬ InverseTablesMatch base releasedEvaluationPoints)
    (¬ ∃ reference : AcceptedV5Forest hashing (rootsOf rustInput)
        (querySetOf rustInput),
      ForestProjectsToTranscript decoder hashing reference
        (acceptedTranscript causalFamily input) expectedC2)
    False
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
        (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)),
      (adaptiveBadSets base causalFamily hfinal htables hpublished
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
      deployedNode)
    (¬ PublishedOrdinaryPolynomialCurveDecoding (K := K)) := by
  classical
  by_cases hrelationProjection :
      SourceRelationInputMatchesFamily input relationFamily
  case neg => exact .sourceRelationProjection hrelationProjection
  by_cases hfamily : FamilyMatchesFriTranscript
      (concreteCodeEncoders base releasedEvaluationPoints)
      (acceptedTranscript causalFamily input) relationFamily input.challenges
  case neg => exact .familyProjection hfamily
  by_cases htranscript : TranscriptExecutionProjection input transcriptInput
      derived driverResult (querySetOf rustInput) queries
  case neg => exact .transcriptProjection htranscript
  by_cases hworkProjection :
      WorkExecutionProjection transcriptInput derived workInputs
  case neg => exact .workProjection hworkProjection
  by_cases hfinal : FinalXMatchesReleasedDomain base
  case neg => exact .releasedFinalDomain hfinal
  by_cases htables : InverseTablesMatch base releasedEvaluationPoints
  case neg => exact .releasedInverseTable htables
  by_cases hreferenceExists :
      ∃ reference : AcceptedV5Forest hashing (rootsOf rustInput)
          (querySetOf rustInput),
        ForestProjectsToTranscript decoder hashing reference
          (acceptedTranscript causalFamily input) expectedC2
  case neg => exact .referenceForest hreferenceExists
  rcases hreferenceExists with ⟨reference, hreference⟩
  by_cases hrustCorrespondence :
      RustAcceptedOpeningYieldsForest hashing rustAcceptsOpening rootsOf
        querySetOf
  case neg => exact .rustOpeningCorrespondence hrustCorrespondence
  obtain ⟨acceptedForest⟩ := hrustCorrespondence rustInput hrustOpening
  by_cases hcollision : HashCollision hashing
  case pos => exact .merkleHashCollision hcollision
  have hforestProjection :
      ForestProjectsToTranscript decoder hashing acceptedForest
        (acceptedTranscript causalFamily input) expectedC2 :=
    forestProjectsToTranscript_of_collisionFree decoder hashing reference
      acceptedForest (acceptedTranscript causalFamily input) expectedC2
      hreference hcollision
  by_cases hwork : ExecutableWorkAcceptance workFunctions workInputs
  case neg => exact .workCheck hwork
  by_cases hfriChecks :
      ForestFriChecks decoder hashing acceptedForest
        (acceptedSchedule base input) (acceptedTranscript causalFamily input)
        queries
  case neg => exact .friArithmetic ⟨acceptedForest, hfriChecks⟩
  have hideal : IdealAccepts (acceptedSchedule base input)
      (acceptedTranscript causalFamily input) queries :=
    idealAccepts_of_forestFriChecks decoder hashing acceptedForest
      (acceptedSchedule base input) (acceptedTranscript causalFamily input)
      expectedC2 queries hforestProjection hfriChecks
  by_cases hposeidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode
  case neg => exact .poseidon hposeidon
  by_cases hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)
  case neg => exact .publishedDecoding hpublished
  have htwo : (2 : K) ≠ 0 := NeZero.ne _
  have hfour : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero htwo htwo
  have hmodeled : ∃ output,
      runModeledRelationVerifier relationFamily input.challenges = some output :=
    source_success_implies_modeled_relation_success input relationFamily
      hrelationProjection hsource
  have hallAccepts :
      AllCandidateRelationChecksAccept relationFamily input.challenges :=
    modeled_success_implies_all_candidate_relation_checks_accept
      relationFamily input.challenges hmodeled
  have hextracted := accepted_ideal_fri_extracts_with_constructed_strategy
    base causalFamily queries hfinal htables hpublished
    input.round0.alpha input.round1.alpha input.round2.alpha
    input.round3.alpha (by
      simpa only [acceptedSchedule, acceptedTranscript] using hideal)
  rcases hextracted with hquery | hbad | hextracted
  · have hquery' : QueryPhaseFailure (acceptedSchedule base input)
        (acceptedTranscript causalFamily input) queries := by
      simpa only [acceptedSchedule, acceptedTranscript] using hquery
    exact .queryPhase hquery'
  · have hcounted :
        ∃ (hfinal' : FinalXMatchesReleasedDomain base)
            (htables' : InverseTablesMatch base releasedEvaluationPoints)
            (hpublished' : PublishedOrdinaryPolynomialCurveDecoding (K := K)),
          (adaptiveBadSets base causalFamily hfinal' htables' hpublished'
            (constructedAdaptiveStrategies base causalFamily)).Occurs
              input.round0.alpha input.round1.alpha
              input.round2.alpha input.round3.alpha :=
      ⟨hfinal, htables, hpublished, hbad⟩
    exact .friFibre hcounted
  · rcases hextracted with ⟨c0, hc0Before, hcardBefore, hfold⟩
    let encoders := concreteCodeEncoders base releasedEvaluationPoints
    have hlistEq :
        initialCandidateList encoders (transcriptBeforeRound0 causalFamily) =
          initialCandidateList encoders
            (acceptedTranscript causalFamily input) :=
      initialCandidateList_eq_of_layer0_eq encoders
        (transcriptBeforeRound0 causalFamily)
        (acceptedTranscript causalFamily input) (by rfl)
    have hc0Full : c0 ∈ initialCandidateList encoders
        (acceptedTranscript causalFamily input) := by
      rw [← hlistEq]
      exact hc0Before
    let candidate : AcceptedCandidate base causalFamily input := ⟨c0, hc0Full⟩
    have hcardFull :
        (initialCandidateList encoders
          (acceptedTranscript causalFamily input)).card ≤ 240 := by
      rw [← hlistEq]
      exact hcardBefore
    have hcandidateCard :
        Fintype.card (AcceptedCandidate base causalFamily input) ≤ 240 := by
      simpa only [AcceptedCandidate, encoders, Fintype.card_coe] using hcardFull
    have halpha : ScheduleMatchesRelationChallenges
        (acceptedSchedule base input) input.challenges := by
      simp only [ScheduleMatchesRelationChallenges, acceptedSchedule,
        scheduleAt, SourceRelationInput.challenges,
        SourceRelationRound.challenges, round0Block, round1Block,
        round2Block, round3Block]
      exact ⟨rfl, rfl, rfl, rfl⟩
    have hfinalMap :
        finalCoefficientMap (acceptedSchedule base input) candidate.1 =
          (acceptedTranscript causalFamily input).publishedFinal := by
      change
        coefficientFoldLayer 4 input.round3.alpha
            (coefficientFoldLayer 16 input.round2.alpha
              (coefficientFoldLayer 64 input.round1.alpha
                (coefficientFoldLayer 256 input.round0.alpha c0))) =
          causalFamily.final input.round0.alpha input.round1.alpha
            input.round2.alpha input.round3.alpha
      exact hfold
    have hmatches :
        (relationFamily.execution candidate).FinalMatches input.challenges :=
      finalMatches_of_extracted_candidate (acceptedSchedule base input)
        encoders (acceptedTranscript causalFamily input) relationFamily
        input.challenges halpha hfamily candidate hfinalMap
    by_cases hearlier : ∃ candidate : AcceptedCandidate base causalFamily input,
        CandidateEarlierFailure rc (relationFamily.execution candidate)
          input.challenges statement (records candidate)
    · exact .candidateTrace hearlier
    · have hallFalse : AllCandidatesFalse relationFamily input.challenges :=
        false_statement_outside_all_candidate_failures rc hposeidon
          relationFamily records input.challenges statement noWitness (by
            intro candidate hfailure
            exact hearlier ⟨candidate, hfailure⟩)
      have hrepair : input.challenges ∈ boundedCandidateRepairEvent
          (fun candidate =>
            (relationFamily.execution candidate).adaptiveData) :=
        matching_false_candidate_mem_boundedCandidateRepairEvent
          (fun candidate => relationFamily.execution candidate)
          input.challenges hfour hallAccepts hallFalse ⟨candidate, hmatches⟩
      exact .relationRepairEvent ⟨hcandidateCard, hrepair⟩

#print axioms forestProjectsToTranscript_of_collisionFree
#print axioms idealAccepts_of_forestFriChecks
#print axioms accepted_false_source_execution_event

end AspisV5AcceptedExecutionSecurityBridge
