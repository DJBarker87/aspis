import AspisFormal.V5FriFixedFamilyExperiment
import AspisFormal.V5MerkleTranscriptProjection
import AspisFormal.V5TranscriptSourceAdapter

/-!
# Deterministic production-to-Fiat--Shamir bridge

The released FRI probability theorem is stated for one causal family of
committed words.  The authenticated-root development already constructs that
family.  This file removes two avoidable inputs from the production boundary:

* the counterfactual transcript family is the transcript selected by the five
  challenge-timed Merkle roots; and
* the production transcript at a sampled challenge tuple is that same
  root-selected transcript by definition.

For the corresponding counted FRI event, the only remaining Fiat--Shamir
premise is the explicit SHA-256/random-oracle pullback bound.  This file does
not assert that SHA-256 is a random oracle and does not assign that premise a
numerical value.

The final section also connects the maintained source-shaped transcript
driver to the root and fold-challenge objects used here.  Identifying that
pure driver with every accepted execution of the unchanged Rust verifier is a
separate source-extraction task; it is not renamed or assumed below.
-/

namespace AspisV5ProductionFiatShamirBridge

open AspisV5AcceptedExecutionSecurityBridge
open AspisV5FriAdaptiveUnmatched
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriFixedFamilyExperiment
open AspisV5FriPublishedOutputEncoderDecoding
open AspisV5FriReleasedAdaptiveExtraction
open AspisV5FriReleasedLineGeometry
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5MerkleTranscriptProjection
open AspisV5TranscriptConnection
open AspisV5TranscriptSourceAdapter

/-! ## Exact roots and challenges carried by the source-shaped driver -/

/-- The five private-opening roots read from the same fixed body which feeds
the maintained transcript driver.  Layer zero is C1; layers one through three
are the later FRI roots. -/
def transcriptPrivateRoots (input : V5TranscriptInputs) :
    V5PrivateRoots AspisV5MerkleRustBridge.Digest32 where
  c1 := input.circleRoot 0
  c2 := input.c2Root
  line1 := input.circleRoot 1
  line2 := input.circleRoot 2
  line3 := input.circleRoot 3

/-- Regard the fixed roots of one accepted body as a causal root family.  This
is the exact family used when a deterministic accepted body is replayed at
counterfactual fold challenges.  The SHA/random-oracle reduction remains
responsible for relating that replay experiment to an adaptive prover. -/
def fixedBodyCausalRoots {K : Type*}
    (input : V5TranscriptInputs) (publishedFinal : Fin 4 -> K) :
    CausalMerkleRoots K AspisV5MerkleRustBridge.Digest32 where
  c1 := input.circleRoot 0
  c2 := input.c2Root
  line1 := fun _ => input.circleRoot 1
  line2 := fun _ _ => input.circleRoot 2
  line3 := fun _ _ _ => input.circleRoot 3
  final := fun _ _ _ _ => publishedFinal

@[simp] theorem fixedBodyCausalRoots_at
    {K : Type*} (input : V5TranscriptInputs)
    (publishedFinal : Fin 4 -> K) (z0 z1 z2 : K) :
    (fixedBodyCausalRoots input publishedFinal).at z0 z1 z2 =
      transcriptPrivateRoots input := by
  rfl

/-- The nested four-tuple returned by the four named fold-challenge squeezes. -/
def foldChallengeTuple {K PointValue : Type*}
    (derived : V5DerivedValues K PointValue) : FourChallenges K :=
  (((derived.foldChallenge 0, derived.foldChallenge 1),
      derived.foldChallenge 2), derived.foldChallenge 3)

def consumedFoldChallengeTuple {K PointValue : Type*}
    (driver : V5TranscriptDriverResult K PointValue) : FourChallenges K :=
  (((driver.consumed.foldChallenges 0,
      driver.consumed.foldChallenges 1),
    driver.consumed.foldChallenges 2),
    driver.consumed.foldChallenges 3)

/-- The source-shaped driver forwards exactly the four squeeze results from
which `foldChallengeTuple` is built. -/
theorem source_driver_consumes_fold_challenge_tuple
    {K PointValue : Type*} (input : V5TranscriptInputs)
    (derived : V5DerivedValues K PointValue) :
    consumedFoldChallengeTuple (sourceAdapterDriver input derived) =
      foldChallengeTuple derived := by
  rfl

/-! ## Root-defined counterfactual transcript -/

/-- The complete ideal transcript selected by one challenge tuple and one
causal family of roots. -/
noncomputable def rootCounterfactualTranscript
    {K Digest : Type*}
    (decoder : ProductionOpeningDecoder K)
    (hashing : MerkleHashing Digest)
    (roots : CausalMerkleRoots K Digest)
    (challenges : FourChallenges K) : IdealTranscript K :=
  committedTranscript decoder hashing
    (roots.at challenges.1.1.1 challenges.1.1.2 challenges.1.2)
    (roots.final challenges.1.1.1 challenges.1.1.2 challenges.1.2
      challenges.2)

/-- The root-defined counterfactual transcript is exactly the complete
transcript of the causal family constructed from those roots, for every
challenge tuple.  No production equality premise occurs here. -/
theorem rootCounterfactualTranscript_matches_committedCausalFamily
    {K Digest : Type*}
    (decoder : ProductionOpeningDecoder K)
    (hashing : MerkleHashing Digest)
    (roots : CausalMerkleRoots K Digest) :
    CounterfactualTranscriptsMatchFixedFamily
      (committedCausalFamily decoder hashing roots)
      (rootCounterfactualTranscript decoder hashing roots) := by
  intro challenges
  rcases challenges with ⟨⟨⟨z0, z1⟩, z2⟩, z3⟩
  exact fullTranscript_committedCausalFamily decoder hashing roots z0 z1 z2 z3
    |>.symm

/-- At the four challenges forwarded by the source-shaped driver, the fixed
body's root family selects exactly the five roots and final polynomial decoded
from that body. -/
theorem source_driver_selects_fixed_body_transcript
    {K PointValue : Type*}
    (decoder : ProductionOpeningDecoder K)
    (hashing : MerkleHashing AspisV5MerkleRustBridge.Digest32)
    (input : V5TranscriptInputs)
    (derived : V5DerivedValues K PointValue)
    (publishedFinal : Fin 4 -> K) :
    rootCounterfactualTranscript decoder hashing
        (fixedBodyCausalRoots input publishedFinal)
        (foldChallengeTuple derived) =
      committedTranscript decoder hashing (transcriptPrivateRoots input)
        publishedFinal := by
  rfl

/-- The Merkle forest accepted under the fixed body's five roots projects to
the same transcript selected by the source driver's four fold challenges.
The only cryptographic premise is ordinary Merkle collision freedom. -/
theorem accepted_forest_projects_to_source_driver_transcript
    {K PointValue : Type*}
    (decoder : ProductionOpeningDecoder K)
    (hashing : MerkleHashing AspisV5MerkleRustBridge.Digest32)
    (hfree : CollisionFree hashing)
    (input : V5TranscriptInputs)
    (derived : V5DerivedValues K PointValue)
    (publishedFinal : Fin 4 -> K)
    {querySet : Finset V5Query}
    (forest : AcceptedV5Forest hashing (transcriptPrivateRoots input)
      querySet) :
    ForestProjectsToTranscript decoder hashing forest
      (rootCounterfactualTranscript decoder hashing
        (fixedBodyCausalRoots input publishedFinal)
        (foldChallengeTuple derived))
      (committedC2 decoder hashing (transcriptPrivateRoots input)) := by
  rw [source_driver_selects_fixed_body_transcript decoder hashing input
    derived publishedFinal]
  exact forest_projects_to_committedTranscript decoder hashing hfree forest
    publishedFinal

/-- Project the production transcript at its sampled challenge tuple.  Once
the root family has been fixed, this is not another independently supplied
counterfactual object. -/
noncomputable def sampledRootTranscript
    {Coins K Digest : Type*}
    (decoder : ProductionOpeningDecoder K)
    (hashing : MerkleHashing Digest)
    (roots : CausalMerkleRoots K Digest)
    (challengeTuple : Coins -> FourChallenges K) (coins : Coins) :
    IdealTranscript K :=
  rootCounterfactualTranscript decoder hashing roots (challengeTuple coins)

theorem sampledRootTranscript_eq_counterfactual_at_tuple
    {Coins K Digest : Type*}
    (decoder : ProductionOpeningDecoder K)
    (hashing : MerkleHashing Digest)
    (roots : CausalMerkleRoots K Digest)
    (challengeTuple : Coins -> FourChallenges K) (coins : Coins) :
    sampledRootTranscript decoder hashing roots challengeTuple coins =
      rootCounterfactualTranscript decoder hashing roots
        (challengeTuple coins) := by
  rfl

/-! ## The exact remaining SHA/random-oracle premise -/

section FiniteExperiment

variable {Coins K Digest : Type*}
  [Fintype Coins] [DecidableEq Coins] [Nonempty Coins]
  [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [NeZero (2 : K)]

/-- The production FRI event whose sampled challenge tuple lands in the
proved bad set for the root-constructed causal family. -/
noncomputable def rootDefinedFriFailure
    (base : FixedSchedule (ZMod AspisCircleGroupOrder.P) K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (decoder : ProductionOpeningDecoder K)
    (hashing : MerkleHashing Digest)
    (roots : CausalMerkleRoots K Digest)
    (challengeTuple : Coins -> FourChallenges K) : Finset Coins :=
  Finset.univ.filter fun coins =>
    challengeTuple coins ∈ fixedFamilyBadChallengeTuples base
      (committedCausalFamily decoder hashing roots) hfinal htables hpublished

/-- The one cryptographic comparison which deterministic source execution
cannot prove: SHA-derived challenges pull the root-defined FRI bad event back
with no more mass than independent uniform field challenges. -/
def SHA256RandomOraclePullbackBound
    (base : FixedSchedule (ZMod AspisCircleGroupOrder.P) K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (decoder : ProductionOpeningDecoder K)
    (hashing : MerkleHashing Digest)
    (roots : CausalMerkleRoots K Digest)
    (challengeTuple : Coins -> FourChallenges K) : Prop :=
  finiteUniformEventProbability
      (rootDefinedFriFailure base hfinal htables hpublished decoder hashing
        roots challengeTuple) <=
    fixedFamilyUniformBadProbability base
      (committedCausalFamily decoder hashing roots) hfinal htables hpublished

/-- Construct the complete fixed-family connection for the root-defined FRI
event.  The causal family, all counterfactual transcripts, the sampled
production transcript, and the failure-event inclusion are discharged by
definitions and theorems.  Only the explicit SHA/random-oracle probability
comparison is supplied. -/
theorem rootDefined_productionFiatShamir_connection
    (base : FixedSchedule (ZMod AspisCircleGroupOrder.P) K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (decoder : ProductionOpeningDecoder K)
    (hashing : MerkleHashing Digest)
    (roots : CausalMerkleRoots K Digest)
    (challengeTuple : Coins -> FourChallenges K)
    (hpullback : SHA256RandomOraclePullbackBound base hfinal htables
      hpublished decoder hashing roots challengeTuple) :
    ProductionFiatShamirFixedFamilyConnection Coins base
      (committedCausalFamily decoder hashing roots) hfinal htables hpublished
      (rootCounterfactualTranscript decoder hashing roots)
      (sampledRootTranscript decoder hashing roots challengeTuple)
      challengeTuple
      (rootDefinedFriFailure base hfinal htables hpublished decoder hashing
        roots challengeTuple) where
  counterfactualFamily :=
    rootCounterfactualTranscript_matches_committedCausalFamily decoder hashing
      roots
  productionTranscriptAtSampledTuple := by
    intro coins
    rfl
  productionFailureMapsToFixedEvent := by
    intro coins hcoins
    simpa [rootDefinedFriFailure] using hcoins
  fiatShamirPullbackLeUniform := hpullback

/-- The root-defined production FRI event inherits the proved four-round
bound with no source/model or causal-family premise. -/
theorem rootDefinedFriFailure_probability_le
    (base : FixedSchedule (ZMod AspisCircleGroupOrder.P) K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (decoder : ProductionOpeningDecoder K)
    (hashing : MerkleHashing Digest)
    (roots : CausalMerkleRoots K Digest)
    (challengeTuple : Coins -> FourChallenges K)
    (hpullback : SHA256RandomOraclePullbackBound base hfinal htables
      hpublished decoder hashing roots challengeTuple) :
    finiteUniformEventProbability
        (rootDefinedFriFailure base hfinal htables hpublished decoder hashing
          roots challengeTuple) <=
      (releasedChallengeCap 0 + releasedChallengeCap 1 +
        releasedChallengeCap 2 + releasedChallengeCap 3 : Rat) /
          Fintype.card K := by
  exact productionFailureProbability_le_fixedFamilyBound base
    (committedCausalFamily decoder hashing roots) hfinal htables hpublished
    (rootCounterfactualTranscript decoder hashing roots)
    (sampledRootTranscript decoder hashing roots challengeTuple)
    challengeTuple
    (rootDefinedFriFailure base hfinal htables hpublished decoder hashing
      roots challengeTuple)
    (rootDefined_productionFiatShamir_connection base hfinal htables
      hpublished decoder hashing roots challengeTuple hpullback)

end FiniteExperiment

#print axioms fixedBodyCausalRoots_at
#print axioms source_driver_consumes_fold_challenge_tuple
#print axioms rootCounterfactualTranscript_matches_committedCausalFamily
#print axioms source_driver_selects_fixed_body_transcript
#print axioms accepted_forest_projects_to_source_driver_transcript
#print axioms sampledRootTranscript_eq_counterfactual_at_tuple
#print axioms rootDefined_productionFiatShamir_connection
#print axioms rootDefinedFriFailure_probability_le

end AspisV5ProductionFiatShamirBridge
