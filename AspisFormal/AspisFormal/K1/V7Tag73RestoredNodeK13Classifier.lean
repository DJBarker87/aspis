import AspisFormal.K1.V7Tag73ParsedK13K14Classifier
import AspisFormal.K1.V7Tag73ConcreteRestorationClient

/-!
# Restoration-node K1.2/K1.3 classifier for Tag-73

The fixed-run classifier reads the returned root execution.  K1.6 also stores
every successful same-tape restoration execution as a
`ConcreteRestorationNode`.  This module projects the exact same K1.2 inputs
from one such node and feeds successful extraction into the already frozen
parser-data K1.3 classifier.

No acceptance or probability premise is hidden here.  The classifier returns
either a proof-relevant K1.2/K1.3 certificate or the exact authentication,
typed extraction, or K1.3 failure that occurred.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73RestoredNodeK13Classifier

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ActualNodeCausalProvenance
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73Q16ControlInvariant
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleQueryExtractor
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

abbrev RestoredK13Node (Statement Payload : Type*) :=
  ConcreteRestorationNode Statement Tag73K12ParsedProof Payload

def restoredNodeK12Proof
    {Statement Payload : Type*}
    (node : RestoredK13Node Statement Payload) : Tag73K12ParsedProof :=
  node.adversaryValue.1.publicProof.proof.rawProof

def restoredNodeK12Roots
    {Statement Payload : Type*}
    (node : RestoredK13Node Statement Payload) : Roots :=
  { c1 := runtimeDigest208ToMerkleDigest node.adversaryValue.rawMessages.c1Root
    c2 := runtimeDigest208ToMerkleDigest node.adversaryValue.rawMessages.c2Root }

def restoredNodeK12Openings
    {Statement Payload : Type*}
    (node : RestoredK13Node Statement Payload) : TwoTreeOpeningProof :=
  (restoredNodeK12Proof node).openings

def restoredNodeK12OrderedQueries
    {Statement Payload : Type*}
    (node : RestoredK13Node Statement Payload) : OrderedRawQueryLog :=
  node.verifierFinalOracle.history.map
    (fun record => runtimeInputToRawHashInput record.input)

/-- The node-local 208-bit view of the immutable shared random-oracle table.
As in the fixed-root classifier, an absent input is totalized to zero and can
only lead to a typed extraction failure, never silent success. -/
def restoredNodeK12Truncate
    {Statement Payload : Type*}
    (node : RestoredK13Node Statement Payload) : RawHashInput →
      AspisPool.V7MerkleQueryGrammar.Digest208 :=
  fun rawInput =>
    match lookupEntry node.verifierFinalOracle
        (rawHashInputToRuntimeInput rawInput) with
    | some entry => runtimeDigest256PrefixToMerkleDigest entry.output
    | none => zeroMerkleDigest

structure RestoredNodeK12Certificate
    {Statement Payload : Type*}
    (node : RestoredK13Node Statement Payload) where
  words : ExtractedWords
  openingsAccepted : accepted_two_tree_openings (restoredNodeK12Truncate node)
    (restoredNodeK12Roots node) (restoredNodeK12Openings node)
  extracted : extractV7Words (restoredNodeK12Truncate node)
    (restoredNodeK12Roots node) (restoredNodeK12Openings node)
    (restoredNodeK12OrderedQueries node) = .words words
  rootsAndOpenings : wordsMatchRootsAndAllAcceptedOpenings
    (restoredNodeK12Truncate node) words (restoredNodeK12Roots node)
    (restoredNodeK12Openings node)
  causalProvenance : SuccessfulCausalProvenance
    (restoredNodeK12Truncate node) (restoredNodeK12Roots node)
    (restoredNodeK12Openings node) (restoredNodeK12OrderedQueries node) words

inductive RestoredNodeK12Error
    {Statement Payload : Type*}
    (node : RestoredK13Node Statement Payload) : Type
  | openingAuthenticationRejected
      (rejected : ¬ accepted_two_tree_openings (restoredNodeK12Truncate node)
        (restoredNodeK12Roots node) (restoredNodeK12Openings node))
  | extractionFailure (reason : Failure)
      (failed : extractV7Words (restoredNodeK12Truncate node)
        (restoredNodeK12Roots node) (restoredNodeK12Openings node)
        (restoredNodeK12OrderedQueries node) = .failure reason)

noncomputable def classifyRestoredNodeK12
    {Statement Payload : Type*}
    (node : RestoredK13Node Statement Payload) :
    RestoredNodeK12Certificate node ⊕ RestoredNodeK12Error node := by
  classical
  by_cases accepted : accepted_two_tree_openings (restoredNodeK12Truncate node)
      (restoredNodeK12Roots node) (restoredNodeK12Openings node)
  · cases extractionEquation : extractV7Words (restoredNodeK12Truncate node)
        (restoredNodeK12Roots node) (restoredNodeK12Openings node)
        (restoredNodeK12OrderedQueries node) with
    | words words =>
        exact .inl
          { words := words
            openingsAccepted := accepted
            extracted := extractionEquation
            rootsAndOpenings :=
              extractV7Words_success_yields_roots_and_openings_match
                (restoredNodeK12Truncate node) (restoredNodeK12Roots node)
                (restoredNodeK12Openings node)
                (restoredNodeK12OrderedQueries node) words extractionEquation
            causalProvenance :=
              extractV7Words_success_yields_causal_provenance
                (restoredNodeK12Truncate node) (restoredNodeK12Roots node)
                (restoredNodeK12Openings node)
                (restoredNodeK12OrderedQueries node) words extractionEquation }
    | failure reason =>
        exact .inr (.extractionFailure reason extractionEquation)
  · exact .inr (.openingAuthenticationRejected accepted)

structure RestoredNodeK13Certificate
    {Statement Payload : Type*}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (node : RestoredK13Node Statement Payload) where
  k12 : RestoredNodeK12Certificate node
  k13 : ParsedK13Certificate decoder k12.words (restoredNodeK12Proof node)

inductive RestoredNodeK13Error
    {Statement Payload : Type*}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (node : RestoredK13Node Statement Payload) : Type
  | k12 (error : RestoredNodeK12Error node)
  | k13 (words : ExtractedWords)
      (error : ParsedK13Error decoder words (restoredNodeK12Proof node))

/-- Exact restoration-aware K1.3 classifier.  It consumes only one stored
runtime node and the frozen decoder instantiation. -/
noncomputable def classifyRestoredNodeK13
    {Statement Payload : Type*}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (node : RestoredK13Node Statement Payload) :
    RestoredNodeK13Certificate decoder node ⊕
      RestoredNodeK13Error decoder node :=
  match classifyRestoredNodeK12 node with
  | .inr error => .inr (.k12 error)
  | .inl k12 =>
      match classifyParsedK13 decoder k12.words (restoredNodeK12Proof node) with
      | .inl k13 => .inl ⟨k12, k13⟩
      | .inr error => .inr (.k13 k12.words error)

theorem restoredNodeK13_error_is_exact_stage_failure
    {Statement Payload : Type*}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {node : RestoredK13Node Statement Payload}
    (error : RestoredNodeK13Error decoder node) :
    Nonempty (RestoredNodeK12Error node) ∨
      ∃ words : ExtractedWords,
        Nonempty (ParsedK13Error decoder words (restoredNodeK12Proof node)) := by
  cases error with
  | k12 error => exact .inl ⟨error⟩
  | k13 words error => exact .inr ⟨words, ⟨error⟩⟩

/-! ## Literal K1.6 accumulator handoff -/

def exactRestorationAccumulator
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ConcreteRestorationAccumulator Statement Tag73K12ParsedProof Payload :=
  input.package.root.full.clientRun.accumulator

/-- A node selected from the literal completed K1.6 accumulator carries both
operational invariants proved by the exact state map and the total exact
K1.2/K1.3 classification above. -/
structure ExactStoredNodeK13Classification
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (node : RestoredK13Node Statement Payload) : Type where
  member : node ∈ (exactRestorationAccumulator input).nodes
  historyClosed : FutureFreeHistoryClosed node.verifierFinalState
  q16SlotInvariant : FutureFreeQ16SlotInvariant node.verifierFinalState
  classified : RestoredNodeK13Certificate decoder node ⊕
    RestoredNodeK13Error decoder node

noncomputable def exact_operational_stored_node_has_k13_classification
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (node : RestoredK13Node Statement Payload)
    (member : node ∈ (exactRestorationAccumulator input).nodes) :
    ExactStoredNodeK13Classification decoder input node :=
  { member := member
    historyClosed := input.stateMap.everyNodeHistoryClosed node member
    q16SlotInvariant := input.stateMap.everyNodeQ16SlotInvariant node member
    classified := classifyRestoredNodeK13 decoder node }

#print axioms restoredNodeK13_error_is_exact_stage_failure
#print axioms exact_operational_stored_node_has_k13_classification

end

end AspisK1.V7Tag73RestoredNodeK13Classifier
