import AspisFormal.K1.V7Tag73ExactFixedK12CoveredClassifier
import AspisFormal.Pool.V7CoherentTraceExtraction

/-!
# Exact fixed-run K1.3 and K1.4 classifiers for Tag-73

This leaf continues from the literal scheduler K1.2 certificate.  It reads
`gamma`, `final256`, the four-fold schedule, and the q16 schedule from the
same parsed proof value that supplied the two Merkle openings.  It then runs
the one fixed algorithmic decoder and returns either:

* the exact initial/final decoder lists and all deterministic one-fold
  acceptance obligations needed by candidate extraction; or
* one of the already named query, fold, list-cap, or ideal-acceptance errors.

K1.4 consumes that exact certificate and constructs one coherent semantic
trace, except for the single published width-29 matching-decomposition event.
No acceptance proposition is stored in the parsed proof and no witness is
supplied to either classifier.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFixedK13K14Classifier

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CandidateChainExtraction
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact
open AspisV6OneFoldCandidateExtraction
open AspisV5WithoutReplacementQuerySoundness

noncomputable section

def exactK13ParsedProof
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Tag73K12ParsedProof :=
  (exactK12Runtime input).adversaryValue.1.publicProof.proof.rawProof

def exactK13Transcript
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactK12Certificate input) : IdealTranscript QM31Exact :=
  extractedIdealTranscript k12.words (exactK13ParsedProof input).gamma
    (exactK13ParsedProof input).disclosedFinal

def exactK13Encoders (decoder : ExactDecoderInstantiation QM31Exact) :
    CodeEncoders QM31Exact :=
  decoderCodeEncoders decoder

structure ExactK13Certificate
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
    (k12 : ExactK12Certificate input) where
  lists : DecodedCandidateLists QM31Exact
  listsExact : lists = decoder.decodeBoth (exactK13Transcript input k12).initial
    (foldedReceived (exactK13ParsedProof input).schedule
      (exactK13Transcript input k12))
  accepts : IdealAccepts (exactK13ParsedProof input).schedule
    (exactK13Encoders decoder) (exactK13Transcript input k12)
    (exactK13ParsedProof input).queries
  noQueryFailure : ¬ QueryPhaseFailure
    (exactK13ParsedProof input).schedule (exactK13Encoders decoder)
    (exactK13Transcript input k12) (exactK13ParsedProof input).queries
  noFoldFailure : ¬ OneFoldReductionFailure
    (exactK13ParsedProof input).schedule (exactK13Encoders decoder)
    (exactK13Transcript input k12)
  noListCapFailure : ¬ InitialListCapFailure (exactK13Encoders decoder)
    (exactK13Transcript input k12)

inductive ExactK13Error
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
    (k12 : ExactK12Certificate input) : Type
  | idealRejected :
      ¬ IdealAccepts (exactK13ParsedProof input).schedule
        (exactK13Encoders decoder) (exactK13Transcript input k12)
        (exactK13ParsedProof input).queries →
      ExactK13Error decoder input k12
  | queryPhaseFailure :
      QueryPhaseFailure (exactK13ParsedProof input).schedule
        (exactK13Encoders decoder) (exactK13Transcript input k12)
        (exactK13ParsedProof input).queries →
      ExactK13Error decoder input k12
  | oneFoldReductionFailure :
      OneFoldReductionFailure (exactK13ParsedProof input).schedule
        (exactK13Encoders decoder) (exactK13Transcript input k12) →
      ExactK13Error decoder input k12
  | initialListCapFailure :
      InitialListCapFailure (exactK13Encoders decoder)
        (exactK13Transcript input k12) →
      ExactK13Error decoder input k12

noncomputable def classifyExactK13
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
    (k12 : ExactK12Certificate input) :
    ExactK13Certificate decoder input k12 ⊕ ExactK13Error decoder input k12 := by
  classical
  by_cases accepts : IdealAccepts (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder) (exactK13Transcript input k12)
      (exactK13ParsedProof input).queries
  · by_cases queryFailure : QueryPhaseFailure
        (exactK13ParsedProof input).schedule (exactK13Encoders decoder)
        (exactK13Transcript input k12) (exactK13ParsedProof input).queries
    · exact .inr (.queryPhaseFailure queryFailure)
    · by_cases foldFailure : OneFoldReductionFailure
          (exactK13ParsedProof input).schedule (exactK13Encoders decoder)
          (exactK13Transcript input k12)
      · exact .inr (.oneFoldReductionFailure foldFailure)
      · by_cases listFailure : InitialListCapFailure
            (exactK13Encoders decoder) (exactK13Transcript input k12)
        · exact .inr (.initialListCapFailure listFailure)
        · exact .inl
            { lists := decoder.decodeBoth (exactK13Transcript input k12).initial
                (foldedReceived (exactK13ParsedProof input).schedule
                  (exactK13Transcript input k12))
              listsExact := rfl
              accepts := accepts
              noQueryFailure := queryFailure
              noFoldFailure := foldFailure
              noListCapFailure := listFailure }
  · exact .inr (.idealRejected accepts)

structure ExactK14Certificate
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : InitialProjectionBinding decoder)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactK12Certificate input) where
  extraction : CoherentTraceExtraction decoder binding k12.words
    (exactK13ParsedProof input).gamma
    (exactK13ParsedProof input).disclosedFinal
    (exactK13ParsedProof input).schedule

inductive ExactK14Error
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
    (k12 : ExactK12Certificate input) : Type
  | width29 : Width29DecompositionFailure decoder k12.words
      (exactK13ParsedProof input).gamma
      (exactK13ParsedProof input).disclosedFinal
      (exactK13ParsedProof input).schedule →
    ExactK14Error decoder input k12

noncomputable def classifyExactK14
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : InitialProjectionBinding decoder)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactK12Certificate input)
    (k13 : ExactK13Certificate decoder input k12) :
    ExactK14Certificate decoder binding input k12 ⊕
      ExactK14Error decoder input k12 := by
  classical
  have result := accepted_onefold_extracts_coherent_trace_or_width29_failure
    decoder binding k12.words (exactK13ParsedProof input).gamma
    (exactK13ParsedProof input).disclosedFinal
    (exactK13ParsedProof input).schedule (exactK13ParsedProof input).queries
    k13.accepts k13.noQueryFailure k13.noFoldFailure
    k13.noListCapFailure
  by_cases extracted : ∃ extraction : CoherentTraceExtraction decoder binding
      k12.words (exactK13ParsedProof input).gamma
      (exactK13ParsedProof input).disclosedFinal
      (exactK13ParsedProof input).schedule, True
  · have inhabited : Nonempty (CoherentTraceExtraction decoder binding
        k12.words (exactK13ParsedProof input).gamma
        (exactK13ParsedProof input).disclosedFinal
        (exactK13ParsedProof input).schedule) := by
      exact extracted.elim fun extraction _ => ⟨extraction⟩
    exact .inl ⟨Classical.choice inhabited⟩
  · exact .inr (.width29 (result.resolve_left extracted))

/-- Executable deterministic cover from an exact K1.2 scheduler certificate
through one coherent K1.4 trace.  Every right branch is one named K1.3/K1.4
failure; there is no aggregate or caller-selected error event. -/
noncomputable def classifyExactK13K14
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : InitialProjectionBinding decoder)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactK12Certificate input) :
    ExactK14Certificate decoder binding input k12 ⊕
      (ExactK13Error decoder input k12 ⊕ ExactK14Error decoder input k12) :=
  match classifyExactK13 decoder input k12 with
  | .inr error => .inr (.inl error)
  | .inl k13 =>
      match classifyExactK14 decoder binding input k12 k13 with
      | .inl k14 => .inl k14
      | .inr error => .inr (.inr error)

#print axioms classifyExactK13
#print axioms classifyExactK14
#print axioms classifyExactK13K14

end

end AspisK1.V7Tag73ExactFixedK13K14Classifier
