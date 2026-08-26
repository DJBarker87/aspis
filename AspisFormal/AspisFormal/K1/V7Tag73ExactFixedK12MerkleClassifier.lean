import AspisFormal.K1.V7Tag73ExactFixedOperationalStateMap
import AspisFormal.Pool.V7MerkleQueryExtractor
import AspisFormal.Pool.V7CoherentTraceExtraction

/-!
# Exact fixed-run K1.2 Merkle classifier for Tag-73

This module connects the literal fixed Tag-73 scheduler object used by K1.6
to the executable two-tree K1.2 query-graph extractor.  The connection is
data-only:

* the two roots come from the prover messages in the actual returned proof;
* the sixteen paired openings come from the concrete parsed-proof type below;
* the ordered raw query log is the actual shared-oracle history at the end of
  the root verifier run; and
* the 208-bit hash view is the first 26 bytes of the first-hit 256-bit oracle
  table answer, with an unqueried input totalized to zero.

The classifier never assumes authentication or extraction success.  It
returns either a proof-relevant complete-word certificate or one of two exact
failure forms: the supplied openings do not authenticate, or the accepted
query graph produces one of K1.2's seven typed extraction failures.  The
separate source bridge must prove that deployed acceptance excludes the first
form; the separate 208-bit ROM argument must bound the second.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactFixedK12MerkleClassifier

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleQueryExtractor

noncomputable section

/-! ## Concrete post-parser proof material -/

/-- The extraction-relevant canonical Tag-73 parsed proof.  Roots remain
single-sourced from the transcript messages and oracle answers remain
single-sourced from the scheduler state.  The downstream fields are plain
parsed data, not acceptance or extraction propositions. -/
structure Tag73K12ParsedProof where
  openings : TwoTreeOpeningProof
  gamma : AspisV5ComponentCQM31TowerExact.QM31Exact
  disclosedFinal :
    AspisPool.AlgorithmicCircleDecoderV7.FinalMessage
      AspisV5ComponentCQM31TowerExact.QM31Exact
  schedule : AspisPool.V7CoherentTraceExtraction.ExactSchedule
  queries : AspisV5WithoutReplacementQuerySoundness.QuerySchedule 16 262144

/-! ## Exact runtime-byte conversion -/

/-- Choice-free equivalence between the runtime transcript byte and the
mathematical byte used by the K1.2 grammar. -/
def runtimeByteEquivMerkleByte : UInt8 ≃ AspisPool.V7MerkleQueryGrammar.Byte :=
  ({ toFun := UInt8.toFin
     invFun := UInt8.ofFin
     left_inv := UInt8.ofFin_toFin
     right_inv := UInt8.toFin_ofFin } : UInt8 ≃ Fin UInt8.size).trans
    (finCongr (by decide : UInt8.size = 256))

def runtimeInputToRawHashInput (input : ByteString) : RawHashInput :=
  input.map runtimeByteEquivMerkleByte

def rawHashInputToRuntimeInput (input : RawHashInput) : ByteString :=
  input.map runtimeByteEquivMerkleByte.symm

@[simp] theorem runtimeInputToRawHashInput_roundtrip
    (input : RawHashInput) :
    runtimeInputToRawHashInput (rawHashInputToRuntimeInput input) = input := by
  simp [runtimeInputToRawHashInput, rawHashInputToRuntimeInput]

@[simp] theorem rawHashInputToRuntimeInput_roundtrip
    (input : ByteString) :
    rawHashInputToRuntimeInput (runtimeInputToRawHashInput input) = input := by
  simp [runtimeInputToRawHashInput, rawHashInputToRuntimeInput]

def runtimeDigest208ToMerkleDigest
    (digest : AspisK1.V7Tag73TranscriptSchedule.Digest208) :
    AspisPool.V7MerkleQueryGrammar.Digest208 :=
  fun index => runtimeByteEquivMerkleByte (digest index)

def runtimeDigest256PrefixToMerkleDigest (digest : Digest256) :
    AspisPool.V7MerkleQueryGrammar.Digest208 :=
  fun index => runtimeByteEquivMerkleByte
    (digest ⟨index.val, by omega⟩)

def zeroMerkleDigest : AspisPool.V7MerkleQueryGrammar.Digest208 :=
  fun _ => 0

/-! ## Literal scheduler projections -/

abbrev ExactK12OperationalInput
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (sample : ExactCompilerSample HiddenTape parameters) :=
  ExactFixedOperationalStateRestorationInput transitionFuel configuration
    projection fixedInstance sample

def exactK12Runtime
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :=
  input.package.root.fixedRoot.base.runtime

def exactK12Roots
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Roots :=
  { c1 := runtimeDigest208ToMerkleDigest
      (exactK12Runtime input).adversaryValue.rawMessages.c1Root
    c2 := runtimeDigest208ToMerkleDigest
      (exactK12Runtime input).adversaryValue.rawMessages.c2Root }

def exactK12Openings
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : TwoTreeOpeningProof :=
  (exactK12Runtime input).adversaryValue.1.publicProof.proof.rawProof.openings

def exactK12OrderedQueries
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : OrderedRawQueryLog :=
  (exactK12Runtime input).verifierFinalOracle.history.map
    (fun record => runtimeInputToRawHashInput record.input)

/-- The total 208-bit view of the actual first-hit scheduler table.  Returning
zero for an absent raw input cannot create extractor success silently: an
accepted root/path not present in the log is classified by the extractor as a
missing-query or guessed-digest failure (or a prefix collision). -/
def exactK12Truncate
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : RawHashInput →
        AspisPool.V7MerkleQueryGrammar.Digest208 :=
  fun rawInput =>
    match lookupEntry (exactK12Runtime input).verifierFinalOracle
        (rawHashInputToRuntimeInput rawInput) with
    | some entry => runtimeDigest256PrefixToMerkleDigest entry.output
    | none => zeroMerkleDigest

@[simp] theorem exactK12Roots_c1_is_returned_root
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
    (exactK12Roots input).c1 = runtimeDigest208ToMerkleDigest
      (exactK12Runtime input).adversaryValue.rawMessages.c1Root := by
  rfl

@[simp] theorem exactK12Roots_c2_is_returned_root
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
    (exactK12Roots input).c2 = runtimeDigest208ToMerkleDigest
      (exactK12Runtime input).adversaryValue.rawMessages.c2Root := by
  rfl

theorem exactK12OrderedQueries_is_literal_shared_history
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
    exactK12OrderedQueries input =
      (exactK12Runtime input).verifierFinalOracle.history.map
        (fun record => runtimeInputToRawHashInput record.input) := by
  rfl

/-! ## Proof-relevant classifier -/

structure ExactK12Certificate
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) where
  words : ExtractedWords
  openingsAccepted : accepted_two_tree_openings (exactK12Truncate input)
    (exactK12Roots input) (exactK12Openings input)
  extracted : extractV7Words (exactK12Truncate input) (exactK12Roots input)
    (exactK12Openings input) (exactK12OrderedQueries input) = .words words
  rootsAndOpenings : wordsMatchRootsAndAllAcceptedOpenings
    (exactK12Truncate input) words (exactK12Roots input)
      (exactK12Openings input)
  causalProvenance : SuccessfulCausalProvenance
    (exactK12Truncate input) (exactK12Roots input) (exactK12Openings input)
      (exactK12OrderedQueries input) words

inductive ExactK12Error
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Type
  | openingAuthenticationRejected
      (rejected : ¬ accepted_two_tree_openings (exactK12Truncate input)
        (exactK12Roots input) (exactK12Openings input))
  | extractionFailure (reason : Failure)
      (failed : extractV7Words (exactK12Truncate input) (exactK12Roots input)
        (exactK12Openings input) (exactK12OrderedQueries input) =
          .failure reason)

/-- Executable K1.2 classifier on the literal scheduler data. -/
noncomputable def classifyExactK12
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
    ExactK12Certificate input ⊕ ExactK12Error input := by
  classical
  by_cases accepted : accepted_two_tree_openings (exactK12Truncate input)
      (exactK12Roots input) (exactK12Openings input)
  · cases extractionEquation : extractV7Words (exactK12Truncate input)
        (exactK12Roots input) (exactK12Openings input)
        (exactK12OrderedQueries input) with
    | words words =>
        exact .inl
          { words := words
            openingsAccepted := accepted
            extracted := extractionEquation
            rootsAndOpenings :=
              extractV7Words_success_yields_roots_and_openings_match
                (exactK12Truncate input) (exactK12Roots input)
                (exactK12Openings input) (exactK12OrderedQueries input) words
                extractionEquation
            causalProvenance :=
              extractV7Words_success_yields_causal_provenance
                (exactK12Truncate input) (exactK12Roots input)
                (exactK12Openings input) (exactK12OrderedQueries input) words
                extractionEquation }
    | failure reason =>
        exact .inr (.extractionFailure reason extractionEquation)
  · exact .inr (.openingAuthenticationRejected accepted)

theorem exactK12_error_is_authentication_or_typed_extraction_failure
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    (error : ExactK12Error input) :
    (¬ accepted_two_tree_openings (exactK12Truncate input)
        (exactK12Roots input) (exactK12Openings input)) ∨
      V7MerkleExtractionFailure (exactK12Truncate input)
        (exactK12Roots input) (exactK12Openings input)
          (exactK12OrderedQueries input) := by
  cases error with
  | openingAuthenticationRejected rejected => exact Or.inl rejected
  | extractionFailure reason failed => exact Or.inr ⟨reason, failed⟩

#print axioms runtimeInputToRawHashInput_roundtrip
#print axioms rawHashInputToRuntimeInput_roundtrip
#print axioms exactK12OrderedQueries_is_literal_shared_history
#print axioms exactK12_error_is_authentication_or_typed_extraction_failure

end

end AspisK1.V7Tag73ExactFixedK12MerkleClassifier
