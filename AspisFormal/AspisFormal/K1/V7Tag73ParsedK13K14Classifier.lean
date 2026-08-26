import AspisFormal.K1.V7Tag73ExactFixedK13K14Classifier

/-!
# Parsed-data K1.3 and K1.4 classifiers for Tag-73

The fixed-run classifier originally read its transcript fields through an
`ExactK12OperationalInput`.  A restoration child and the terminal
accumulator instead expose the same canonical `Tag73K12ParsedProof` directly.
This module factors the mathematical classifier through that parser data and
the already authenticated K1.2 words.  It introduces no acceptance premise:
every classifier still returns either its certificate or the corresponding
typed K1.3/K1.4 failure.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ParsedK13K14Classifier

open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CandidateChainExtraction
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact
open AspisV5WithoutReplacementQuerySoundness
open AspisV6OneFoldCandidateExtraction

noncomputable section

def parsedK13Transcript
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (proof : Tag73K12ParsedProof) : IdealTranscript QM31Exact :=
  extractedIdealTranscript words proof.gamma proof.disclosedFinal

structure ParsedK13Certificate
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (proof : Tag73K12ParsedProof) where
  lists : DecodedCandidateLists QM31Exact
  listsExact : lists = decoder.decodeBoth (parsedK13Transcript words proof).initial
    (foldedReceived proof.schedule (parsedK13Transcript words proof))
  accepts : IdealAccepts proof.schedule (decoderCodeEncoders decoder)
    (parsedK13Transcript words proof) proof.queries
  noQueryFailure : ¬ QueryPhaseFailure proof.schedule
    (decoderCodeEncoders decoder) (parsedK13Transcript words proof) proof.queries
  noFoldFailure : ¬ OneFoldReductionFailure proof.schedule
    (decoderCodeEncoders decoder) (parsedK13Transcript words proof)
  noListCapFailure : ¬ InitialListCapFailure (decoderCodeEncoders decoder)
    (parsedK13Transcript words proof)

inductive ParsedK13Error
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (proof : Tag73K12ParsedProof) : Type
  | idealRejected :
      ¬ IdealAccepts proof.schedule (decoderCodeEncoders decoder)
        (parsedK13Transcript words proof) proof.queries →
      ParsedK13Error decoder words proof
  | queryPhaseFailure :
      QueryPhaseFailure proof.schedule (decoderCodeEncoders decoder)
        (parsedK13Transcript words proof) proof.queries →
      ParsedK13Error decoder words proof
  | oneFoldReductionFailure :
      OneFoldReductionFailure proof.schedule (decoderCodeEncoders decoder)
        (parsedK13Transcript words proof) →
      ParsedK13Error decoder words proof
  | initialListCapFailure :
      InitialListCapFailure (decoderCodeEncoders decoder)
        (parsedK13Transcript words proof) →
      ParsedK13Error decoder words proof

noncomputable def classifyParsedK13
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (proof : Tag73K12ParsedProof) :
    ParsedK13Certificate decoder words proof ⊕
      ParsedK13Error decoder words proof := by
  classical
  by_cases accepts : IdealAccepts proof.schedule (decoderCodeEncoders decoder)
      (parsedK13Transcript words proof) proof.queries
  · by_cases queryFailure : QueryPhaseFailure proof.schedule
        (decoderCodeEncoders decoder) (parsedK13Transcript words proof)
        proof.queries
    · exact .inr (.queryPhaseFailure queryFailure)
    · by_cases foldFailure : OneFoldReductionFailure proof.schedule
          (decoderCodeEncoders decoder) (parsedK13Transcript words proof)
      · exact .inr (.oneFoldReductionFailure foldFailure)
      · by_cases listFailure : InitialListCapFailure
            (decoderCodeEncoders decoder) (parsedK13Transcript words proof)
        · exact .inr (.initialListCapFailure listFailure)
        · exact .inl
            { lists := decoder.decodeBoth (parsedK13Transcript words proof).initial
                (foldedReceived proof.schedule
                  (parsedK13Transcript words proof))
              listsExact := rfl
              accepts := accepts
              noQueryFailure := queryFailure
              noFoldFailure := foldFailure
              noListCapFailure := listFailure }
  · exact .inr (.idealRejected accepts)

structure ParsedK14Certificate
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : InitialProjectionBinding decoder)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (proof : Tag73K12ParsedProof) where
  extraction : CoherentTraceExtraction decoder binding words proof.gamma
    proof.disclosedFinal proof.schedule

inductive ParsedK14Error
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (proof : Tag73K12ParsedProof) : Type
  | width29 : Width29DecompositionFailure decoder words proof.gamma
      proof.disclosedFinal proof.schedule →
    ParsedK14Error decoder words proof

noncomputable def classifyParsedK14
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : InitialProjectionBinding decoder)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (proof : Tag73K12ParsedProof)
    (k13 : ParsedK13Certificate decoder words proof) :
    ParsedK14Certificate decoder binding words proof ⊕
      ParsedK14Error decoder words proof := by
  classical
  have result := accepted_onefold_extracts_coherent_trace_or_width29_failure
    decoder binding words proof.gamma proof.disclosedFinal proof.schedule
    proof.queries k13.accepts k13.noQueryFailure k13.noFoldFailure
    k13.noListCapFailure
  by_cases extracted : ∃ extraction : CoherentTraceExtraction decoder binding
      words proof.gamma proof.disclosedFinal proof.schedule, True
  · have inhabited : Nonempty (CoherentTraceExtraction decoder binding words
        proof.gamma proof.disclosedFinal proof.schedule) :=
      extracted.elim fun extraction _ => ⟨extraction⟩
    exact .inl ⟨Classical.choice inhabited⟩
  · exact .inr (.width29 (result.resolve_left extracted))

noncomputable def classifyParsedK13K14
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : InitialProjectionBinding decoder)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (proof : Tag73K12ParsedProof) :
    ParsedK14Certificate decoder binding words proof ⊕
      (ParsedK13Error decoder words proof ⊕
        ParsedK14Error decoder words proof) :=
  match classifyParsedK13 decoder words proof with
  | .inr error => .inr (.inl error)
  | .inl k13 =>
      match classifyParsedK14 decoder binding words proof k13 with
      | .inl k14 => .inl k14
      | .inr error => .inr (.inr error)

/-- The old exact fixed-run certificate is definitionally an instance of the
new parser-data certificate. -/
def parsedK13CertificateOfExact
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : AspisK1.V7Tag73ExactCompilerResources.ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : AspisK1.V7Tag73ExactPlainRomRun.ExactPlainRomConfiguration
      HiddenTape TapeIdentity Observation Statement Tag73K12ParsedProof Payload
      Result parameters}
    {projection : AspisK1.V7Tag73ExactSourceAcceptanceModel.AcceptedTapeProjection
      Statement Tag73K12ParsedProof Payload}
    {fixedInstance : AspisK1.V7FsAokExperiment.PublicInstance Statement}
    {sample : AspisK1.V7Tag73ExactCompilerResources.ExactCompilerSample
      HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {k12 : ExactPrefixK12Certificate input}
    (k13 : ExactK13Certificate decoder input k12) :
    ParsedK13Certificate decoder k12.words (exactK13ParsedProof input) :=
  { lists := k13.lists
    listsExact := k13.listsExact
    accepts := k13.accepts
    noQueryFailure := k13.noQueryFailure
    noFoldFailure := k13.noFoldFailure
    noListCapFailure := k13.noListCapFailure }

def parsedK14CertificateOfExact
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : AspisK1.V7Tag73ExactCompilerResources.ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : AspisK1.V7Tag73ExactPlainRomRun.ExactPlainRomConfiguration
      HiddenTape TapeIdentity Observation Statement Tag73K12ParsedProof Payload
      Result parameters}
    {projection : AspisK1.V7Tag73ExactSourceAcceptanceModel.AcceptedTapeProjection
      Statement Tag73K12ParsedProof Payload}
    {fixedInstance : AspisK1.V7FsAokExperiment.PublicInstance Statement}
    {sample : AspisK1.V7Tag73ExactCompilerResources.ExactCompilerSample
      HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {k12 : ExactPrefixK12Certificate input}
    (k14 : ExactK14Certificate decoder binding input k12) :
    ParsedK14Certificate decoder binding k12.words (exactK13ParsedProof input) :=
  ⟨k14.extraction⟩

end

#print axioms classifyParsedK13
#print axioms classifyParsedK14
#print axioms classifyParsedK13K14
#print axioms parsedK13CertificateOfExact
#print axioms parsedK14CertificateOfExact

end AspisK1.V7Tag73ParsedK13K14Classifier
