import AspisFormal.K1.V7Tag73ExactFixedQ16JointEventHandoff
import AspisFormal.K1.V7Tag73ExactFixedFullRunFactorization
import AspisFormal.K1.V7Tag73IndexedAlignedRecordReplay
import AspisFormal.Pool.V7MerklePartialPathExtractor

/-!
# Merkle word source fixed before Tag-73 q16

For q16 soundness the received word must be a function of data committed
before the q16 schedule is sampled.  The completed-prover oracle is too late:
it can contain authentication calls selected by q16 itself.

This module instead derives a total 208-bit oracle view and canonical word
from the literal unified-exposure prefix before the selected final-work/q16
anchor.  Equality of that prefix and the committed roots is definitionally
sufficient for equality of the q16 word.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73K13PreQ16MerkleWordSource

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.V7MerklePartialPathExtractor
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleQueryGrammar

noncomputable section

/-- First answer for an input in one chronological exposure prefix. -/
def exposurePrefixLookup : List UnifiedExposureRecord → ShaInput →
    Option Digest256
  | [], _ => none
  | record :: rest, input =>
      if causalInput? record = some input then
        some record.answer
      else
        exposurePrefixLookup rest input

/-- Exact typed query log carried by a chronological exposure prefix. -/
def exposurePrefixRawQueries (records : List UnifiedExposureRecord) :
    OrderedRawQueryLog :=
  (records.filterMap causalInput?).map runtimeInputToRawHashInput

/-- Total 208-bit view determined only by the chronological prefix. -/
def exposurePrefixTruncate (records : List UnifiedExposureRecord) :
    RawHashInput → AspisPool.V7MerkleQueryGrammar.Digest208 :=
  fun rawInput =>
    match exposurePrefixLookup records (rawHashInputToRuntimeInput rawInput) with
    | some digest => runtimeDigest256PrefixToMerkleDigest digest
    | none => zeroMerkleDigest

/-- Canonical received word determined before q16.  Unresolved coordinates
use the same fixed defaults as the K1.2 partial-path extractor. -/
def preQ16PrefixWords (records : List UnifiedExposureRecord) (roots : Roots) :
    ExtractedWords :=
  extractPrefixFixedWords (exposurePrefixTruncate records)
    (exposurePrefixRawQueries records) roots

/-- The selected trial index cuts the exact root record list immediately
before the routed final-work/q16 coordinate. -/
def exactTrialPreQ16Words
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (trial : ExactCompilerExposureTrial parameters) : ExtractedWords :=
  preQ16PrefixWords
    (exactFixedRootRecords input.package.root |>.take trial.val)
    (exactK12Roots input)

/-- Pure source congruence: no hash assumption, probability premise, or
post-q16 execution state occurs. -/
theorem preQ16PrefixWords_congr
    {leftRecords rightRecords : List UnifiedExposureRecord}
    {leftRoots rightRoots : Roots}
    (recordsExact : leftRecords = rightRecords)
    (rootsExact : leftRoots = rightRoots) :
    preQ16PrefixWords leftRecords leftRoots =
      preQ16PrefixWords rightRecords rightRoots := by
  subst rightRecords
  subst rightRoots
  rfl

/-- A literal selected-anchor decomposition identifies the trial prefix with
the preceding record list. -/
theorem exactTrialPreQ16Words_eq_of_anchor
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (trial : ExactCompilerExposureTrial parameters)
    (prior later : List UnifiedExposureRecord)
    (selected : UnifiedExposureRecord)
    (rootExact : exactFixedRootRecords input.package.root =
      prior ++ selected :: later)
    (trialExact : trial.val = prior.length) :
    exactTrialPreQ16Words input trial =
      preQ16PrefixWords prior (exactK12Roots input) := by
  unfold exactTrialPreQ16Words
  rw [rootExact, trialExact]
  simp

/-- Two selected anchors with the same literal prior and roots therefore
have one pre-q16 word, independently of every routed q16 answer. -/
theorem exactTrialPreQ16Words_eq_of_common_anchor_prior
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {leftSample rightSample : ExactCompilerSample HiddenTape parameters}
    (left : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance leftSample)
    (right : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance rightSample)
    (trial : ExactCompilerExposureTrial parameters)
    (leftPrior leftLater rightPrior rightLater : List UnifiedExposureRecord)
    (leftSelected rightSelected : UnifiedExposureRecord)
    (leftRootExact : exactFixedRootRecords left.package.root =
      leftPrior ++ leftSelected :: leftLater)
    (rightRootExact : exactFixedRootRecords right.package.root =
      rightPrior ++ rightSelected :: rightLater)
    (leftTrialExact : trial.val = leftPrior.length)
    (rightTrialExact : trial.val = rightPrior.length)
    (priorExact : leftPrior = rightPrior)
    (rootsExact : exactK12Roots left = exactK12Roots right) :
    exactTrialPreQ16Words left trial = exactTrialPreQ16Words right trial := by
  rw [exactTrialPreQ16Words_eq_of_anchor left trial leftPrior leftLater
      leftSelected leftRootExact leftTrialExact,
    exactTrialPreQ16Words_eq_of_anchor right trial rightPrior rightLater
      rightSelected rightRootExact rightTrialExact]
  exact preQ16PrefixWords_congr priorExact rootsExact

#print axioms preQ16PrefixWords_congr
#print axioms exactTrialPreQ16Words_eq_of_anchor
#print axioms exactTrialPreQ16Words_eq_of_common_anchor_prior

end

end AspisK1.V7Tag73K13PreQ16MerkleWordSource
