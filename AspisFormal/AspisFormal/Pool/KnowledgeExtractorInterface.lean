import Mathlib

/-!
# Knowledge-extractor interfaces for Pool V1

This file replaces the shape "accepted execution record -> witness" by typed
interfaces matching the extractor theorems that are actually available in the
classical random-oracle literature.

The principal distinction is operational.  The BCS proof-of-knowledge
extractor is a probabilistic black-box extractor that may restart the malicious
prover with the same random tape and answer its random-oracle queries
differently.  It is not, as a theorem, a deterministic function of one public
proof or one recorded query log.  Round-by-round knowledge also requires an
algorithmic extractor at each escape boundary.  Merely proving that a nearby
codeword exists is not such an algorithm.

Nothing below asserts that V7 satisfies one of these interfaces.  The final
obligation structure deliberately has no constructor in this file.  It is a
typed checklist for the missing protocol-specific reductions.
-/

set_option autoImplicit false

namespace AspisPool.KnowledgeExtractorInterface

/-! ## Extractor access and statement timing -/

/-- Operational access used by a knowledge extractor.  These modes are not
interchangeable assumptions. -/
inductive ExtractorAccess where
  /-- One completed run and its random-oracle query log, with no restart. -/
  | oneRecordedRun
  /-- Classical black-box access with same-random-tape restart/state restoration. -/
  | classicalBlackBoxRestart
  /-- Quantum black-box access, as in compressed-oracle/QROM extraction. -/
  | quantumBlackBox
  /-- An extractor relying on algebraic representations in an algebraic model. -/
  | algebraicModel
  deriving DecidableEq, Repr

/-- When the adversarial statement is selected relative to oracle and
simulation access. -/
inductive StatementTiming where
  | fixedBeforeOracleAccess
  | chosenByAdversaryDuringOracleAccess
  | chosenAfterSimulatedProofs
  deriving DecidableEq, Repr

/-! ## Exact classical error expressions appearing in the sources -/

/-- BCS 2016, Theorem 7.1: preservation of a *restricted
state-restoration* proof of knowledge through the ordinary binary-Merkle BCS
compiler.  `oracleQueries` is the malicious prover's random-oracle query bound
and `oracleBits` is the full random-oracle output length. -/
noncomputable def bcs16KnowledgeError
    (stateRestorationError : Real) (oracleQueries oracleBits : Nat) : Real :=
  stateRestorationError +
    3 * (((oracleQueries : Real) ^ 2 + 1) / (2 : Real) ^ oracleBits)

/-- Block et al. 2023, Theorem 3.15, classical form: a round-by-round
knowledge error is charged once per adversarial random-oracle query, followed
by the BCS Merkle/random-oracle term. -/
noncomputable def classicalRbrKnowledgeError
    (roundByRoundError : Real) (oracleQueries oracleBits : Nat) : Real :=
  (oracleQueries : Real) * roundByRoundError +
    3 * (((oracleQueries : Real) ^ 2 + 1) / (2 : Real) ^ oracleBits)

/-- The formula stated by S-two Theorem 22.  S-two explicitly postpones its
formal treatment and its Remark 23 only sketches the mixed-domain Merkle
adaptation, so this definition records the claimed arithmetic rather than an
Aspis applicability theorem. -/
noncomputable def sTwoClaimedKnowledgeError
    (maximumRoundError : Real) (oracleQueries publicCoinRounds oracleBits : Nat) : Real :=
  ((oracleQueries + publicCoinRounds : Nat) : Real) * maximumRoundError +
    3 * (((oracleQueries : Real) ^ 2 + 1) / (2 : Real) ^ oracleBits)

/-! ## Algorithmic round-by-round knowledge -/

/-- A typed form of round-by-round knowledge.  The extractor consumes the
statement, partial transcript, and current prover message.  When the chance of
escaping the doomed set exceeds the knowledge error, it must *compute* a valid
witness.  `escapeProbability` abstracts the round-specific public-coin
distribution; V7 must instantiate it for each of its heterogeneous challenges. -/
structure RoundByRoundKnowledge
    (Statement Transcript ProverMessage Witness : Type*) where
  relation : Statement -> Witness -> Prop
  initialTranscript : Statement -> Transcript
  acceptsComplete : Statement -> Transcript -> Prop
  doomed : Statement -> Transcript -> Prop
  escapeProbability : Statement -> Transcript -> ProverMessage -> Real
  knowledgeError : Real
  extract : Statement -> Transcript -> ProverMessage -> Witness
  polynomialTime : Prop
  errorInUnitInterval : knowledgeError ∈ Set.Icc (0 : Real) 1
  initialDoomed : forall x, doomed x (initialTranscript x)
  doomedCompleteRejects : forall x transcript,
    doomed x transcript -> acceptsComplete x transcript -> False
  extractsAboveThreshold : forall x transcript message,
    doomed x transcript ->
    knowledgeError < escapeProbability x transcript message ->
    relation x (extract x transcript message)

/-- An actual list-decoding algorithm, rather than an existential proximity
predicate.  Completeness requires every close codeword to occur in the finite
output list; soundness rules out spurious entries. -/
structure AlgorithmicListDecoder (ReceivedWord Message : Type*) where
  close : ReceivedWord -> Message -> Prop
  decode : ReceivedWord -> List Message
  listSizeCap : Nat
  complete : forall received message, close received message -> message ∈ decode received
  sound : forall received message, message ∈ decode received -> close received message
  outputBound : forall received, (decode received).length ≤ listSizeCap
  deterministicPolynomialTime : Prop

/-! ## What the classical BCS theorem supplies -/

/-- A probabilistic black-box extractor.  The output is not required to be a
valid witness for every choice of extractor coins; validity is accounted for by
`validExtractionProbability` in the knowledge guarantee. -/
structure BlackBoxExtractor
    (Statement Witness Adversary ExtractorCoins : Type*) where
  run : Adversary -> Statement -> ExtractorCoins -> Witness
  access : ExtractorAccess
  expectedPolynomialTime : Prop

/-- Fixed-statement classical-ROM argument-of-knowledge guarantee in the shape
of BCS 2016 Theorem 7.1.  The theorem quantifies over a malicious prover and
relates its acceptance probability to the probability that the black-box
extractor returns a valid witness.  It does not give pointwise extraction from
each accepting execution. -/
structure FixedStatementClassicalBCSKnowledge
    (Statement Witness Adversary ExtractorCoins : Type*) where
  relation : Statement -> Witness -> Prop
  extractor : BlackBoxExtractor Statement Witness Adversary ExtractorCoins
  oracleQueries : Nat
  oracleBits : Nat
  restrictedStateRestorationError : Real
  acceptanceProbability : Statement -> Adversary -> Real
  validExtractionProbability : Statement -> Adversary -> Real
  probabilitiesInUnitInterval : forall x adversary,
    acceptanceProbability x adversary ∈ Set.Icc (0 : Real) 1 /\
      validExtractionProbability x adversary ∈ Set.Icc (0 : Real) 1
  restartAccess : extractor.access = .classicalBlackBoxRestart
  extractionBound : forall x adversary,
    acceptanceProbability x adversary ≤
      validExtractionProbability x adversary +
        bcs16KnowledgeError restrictedStateRestorationError oracleQueries oracleBits

theorem bcsExtractor_is_not_typed_as_one_recorded_run
    {Statement Witness Adversary ExtractorCoins : Type*}
    (guarantee : FixedStatementClassicalBCSKnowledge
      Statement Witness Adversary ExtractorCoins) :
    guarantee.extractor.access ≠ .oneRecordedRun := by
  rw [guarantee.restartAccess]
  decide

/-! ## Straight-line Merkle query-graph boundary -/

/-- Failures emitted by a future V7-specific query-graph extractor.  They must
be bounded for the 208-bit truncated, domain-separated two-tree construction;
the generic 104-bit birthday shorthand is not itself this extraction bound. -/
inductive MerkleExtractionFailure where
  | missingRootQuery
  | missingPreimageQuery
  | guessedDigest
  | forwardReference
  | truncatedDigestCollision
  | malformedTypedPreimage
  | pairedSaltMismatch
  deriving DecidableEq, Repr

inductive MerkleExtractionResult (ReceivedWord : Type*) where
  | word (received : ReceivedWord)
  | failure (reason : MerkleExtractionFailure)

/-- A one-log Merkle extractor is a separate, protocol-specific object.  If it
is constructed, it can justify a straight-line *commitment-word* extraction
step; it does not by itself replace the black-box BCS witness extractor. -/
structure MerkleQueryGraphExtractor
    (Root QueryLog ReceivedWord : Type*) where
  extract : Root -> QueryLog -> MerkleExtractionResult ReceivedWord
  matchesRoot : Root -> ReceivedWord -> Prop
  acceptedRoot : Root -> QueryLog -> Prop
  failureProbability : Nat -> Real
  resultSound : forall root log,
    acceptedRoot root log ->
      (exists word, extract root log = .word word /\ matchesRoot root word) \/
      (exists reason, extract root log = .failure reason)
  concreteFailureBound : Prop

/-! ## Extraction after simulated/observed proofs -/

/-- A game-level simulation-extractability boundary.  It follows the shape of
the programmable-ROM definition: the adversary may see simulated proofs, the
forgery must be fresh, and extraction is probabilistic with an explicit loss.
The 2023 generic upgrade additionally needs a canonical simulator and a
weak-unique-response premise; those are explicit fields rather than inferred
from ordinary zero knowledge. -/
structure ObservedProofSimulationExtractability
    (Statement Proof Witness Adversary ExtractorCoins : Type*) where
  relation : Statement -> Witness -> Prop
  accepts : Statement -> Proof -> Prop
  freshAfterSimulation : Adversary -> Statement -> Proof -> Prop
  extract : Adversary -> ExtractorCoins -> Statement -> Proof -> Witness
  randomOracleQueries : Nat
  simulationQueries : Nat
  freshAcceptanceProbability : Adversary -> Real
  validExtractionProbability : Adversary -> Real
  knowledgeError : Real
  polynomialLoss : Real
  errorNonnegative : 0 ≤ knowledgeError
  lossPositive : 0 < polynomialLoss
  canonicalProgrammableRoSimulator : Prop
  fiatShamirExtractability : Prop
  weakUniqueResponse : Prop
  statementTiming : StatementTiming
  timingAfterSimulatedProofs : statementTiming = .chosenAfterSimulatedProofs
  extractorAccess : ExtractorAccess
  blackBoxRestartAccess : extractorAccess = .classicalBlackBoxRestart
  extractionBound : forall adversary,
    (freshAcceptanceProbability adversary - knowledgeError) / polynomialLoss ≤
      validExtractionProbability adversary

/-! ## Exact V7 applicability obligations -/

/-- Protocol-specific work still required before the deployed Tag-73 verifier
has an end-to-end argument-of-knowledge theorem.  Each field is intentionally a
`Prop`: this file neither postulates nor proves any of them. -/
structure V7KnowledgeExtractionObligations where
  exactInteractiveTranscriptAndRoundMap : Prop
  roundByRoundKnowledgeForSpendRelation : Prop
  challengeDependentC2CommitmentCovered : Prop
  conditionedFirstCap203QueryScheduleCovered : Prop
  allThreeGrindingStagesCovered : Prop
  adaptiveStatementSelectionCovered : Prop
  merkle208TwoTreeQueryGraphExtractor : Prop
  merkle208ConcreteFailureProbability : Prop
  algorithmicInitialWidth29Decoder : Prop
  algorithmicOneFoldDecoder : Prop
  singleConsistentCandidateChain : Prop
  acceptedTraceToSpendWitness : Prop
  deployedRustTranscriptCorrespondence : Prop
  extractionErrorIsRawNotWorkNormalized : Prop

/-- Additional obligations for the fixed-victim game after prior public or
simulated proofs. -/
structure V7ObservedProofObligations extends V7KnowledgeExtractionObligations where
  canonicalProgrammableRoSimulator : Prop
  simulatedProofProgrammingIsExact : Prop
  weakUniqueResponseForExactV7 : Prop
  freshnessBindsStatementAttemptAndProofAccount : Prop
  adaptiveSimulationExtractionError : Prop

end AspisPool.KnowledgeExtractorInterface
