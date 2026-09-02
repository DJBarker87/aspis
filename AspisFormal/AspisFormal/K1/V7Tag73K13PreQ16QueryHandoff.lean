import AspisFormal.K1.V7Tag73K13PreQ16ViewAgreement
import AspisFormal.K1.V7Tag73ParsedK13K14Classifier
import AspisFormal.K1.V7Tag73ExactFixedK13K14FailureReduction

/-!
# Pre-q16-local K1.3 query handoff

The q16 probability argument must use a received word fixed before the selected
q16 coordinate.  It is not necessary (and in the adversary-first execution is
not sound) to identify that word with the complete prover-final received word.

This leaf proves the smaller fact actually consumed by the query test: two
received words which project the same authenticated opening give identical
values on the four-symbol fibre read by the circle fold.  Consequently an
accepted selected query for the legacy K1.3 word is accepted for the pre-q16
word as well.  The latter therefore supplies the q16-independent bad set.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73K13PreQ16QueryHandoff

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedK13K14FailureReduction
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13PreQ16MerkleWordSource
open AspisK1.V7Tag73K13PreQ16ViewAgreement
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7ExtractedLaneWords
open AspisPool.V7MerkleFirstUnresolvedBinding
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7Width29ComponentExtraction
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCQM31TowerExact
open AspisV6OneFoldCandidateExtraction
open AspisV6Width29CorrelatedAgreement

noncomputable section

/-- Projection of the same paired opening makes all twenty-nine decoded lanes
equal on each of the four symbols read by its circle fibre. -/
theorem projected_opening_lane_value_eq
    (left right : ExtractedWords) (opening : PairedOpening)
    (leftProjection : openingIsProjection left opening)
    (rightProjection : openingIsProjection right opening)
    (slot : Fin 4) (lane : Fin 29) :
    extractedWidth29InitialWords left lane
        (childIndex opening.position slot) =
      extractedWidth29InitialWords right lane
        (childIndex opening.position slot) := by
  have c1Left : extractedC1Leaf left opening.position =
      ⟨opening.c1Value, opening.sharedSalt⟩ :=
    extractedC1Leaf_of_projection left opening.position _ leftProjection.1
  have c1Right : extractedC1Leaf right opening.position =
      ⟨opening.c1Value, opening.sharedSalt⟩ :=
    extractedC1Leaf_of_projection right opening.position _ rightProjection.1
  have c2Left : extractedC2Leaf left opening.position =
      ⟨opening.c2Value, opening.sharedSalt⟩ :=
    extractedC2Leaf_of_projection left opening.position _ leftProjection.2
  have c2Right : extractedC2Leaf right opening.position =
      ⟨opening.c2Value, opening.sharedSalt⟩ :=
    extractedC2Leaf_of_projection right opening.position _ rightProjection.2
  have childExact : childIndex opening.position slot =
      initialIndex opening.position slot := Fin.ext rfl
  rcases width29_lane_partition lane with ⟨column, rfl⟩ | ⟨helper, rfl⟩
  · rw [extractedWidth29_c1_lane, extractedWidth29_c1_lane, childExact]
    simp only [c1Received, fibreIndex_initialIndex, fibreSlot_initialIndex,
      c1Left, c1Right]
  · rw [extractedWidth29_c2_lane, extractedWidth29_c2_lane, childExact]
    simp only [c2Received, fibreIndex_initialIndex, fibreSlot_initialIndex,
      c2Left, c2Right]

/-- The gamma-batched initial words agree on the complete four-symbol fibre
authenticated by one paired opening. -/
theorem projected_opening_batched_fibre_eq
    (left right : ExtractedWords) (opening : PairedOpening)
    (leftProjection : openingIsProjection left opening)
    (rightProjection : openingIsProjection right opening)
    (gamma : QM31Exact) (slot : Fin 4) :
    (extractedIdealTranscript left gamma (fun _ => 0)).initial
        (childIndex opening.position slot) =
      (extractedIdealTranscript right gamma (fun _ => 0)).initial
        (childIndex opening.position slot) := by
  simp only [extractedIdealTranscript, batchInitialWords]
  apply congrArg (fun values => width29Batch values gamma)
  funext lane
  exact projected_opening_lane_value_eq left right opening leftProjection
    rightProjection slot lane

/-- Query consistency is local to the authenticated four-symbol fibre and the
shared disclosed final vector. -/
theorem query_consistent_of_shared_projected_opening
    (schedule : OneFoldSchedule M31Exact QM31Exact)
    (encoders : CodeEncoders QM31Exact)
    (left right : ExtractedWords) (opening : PairedOpening)
    (leftProjection : openingIsProjection left opening)
    (rightProjection : openingIsProjection right opening)
    (gamma : QM31Exact) (disclosedFinal : FinalMessage QM31Exact)
    (query : Fin 262144)
    (positionExact : query.val = opening.position.val)
    (consistent : QueryConsistent schedule encoders
      (extractedIdealTranscript left gamma disclosedFinal)
      query) :
    QueryConsistent schedule encoders
      (extractedIdealTranscript right gamma disclosedFinal)
      query := by
  unfold QueryConsistent at consistent ⊢
  rw [circleFoldLayer_apply] at consistent ⊢
  have fibreExact :
      (fun slot => (extractedIdealTranscript right gamma disclosedFinal).initial
        (childIndex query slot)) =
      (fun slot => (extractedIdealTranscript left gamma disclosedFinal).initial
        (childIndex query slot)) := by
    funext slot
    have childExact : childIndex query slot =
        childIndex opening.position slot := by
      apply Fin.ext
      simp only [childIndex_val]
      omega
    rw [childExact]
    exact (projected_opening_batched_fibre_eq left right opening leftProjection
      rightProjection gamma slot).symm
  exact (congrArg
    (circleFoldValue schedule.alpha
      (algebraMap M31Exact QM31Exact (schedule.circleInv2x query))
      (algebraMap M31Exact QM31Exact (schedule.circleInv2y query)))
    fibreExact).trans consistent

/-- Exact data equality the production verifier must expose between each
authenticated opening and the q16 position at the same ordinal.  It is kept
separate from the hash/circle assumptions and is intended to be discharged by
the Rust/Aeneas accepted-caller bridge. -/
def ExactOpeningPositionsSourceBinding
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Prop :=
  ∀ ordinal : Fin 16,
    (exactK12Openings input ordinal).position.val =
      ((exactOperationalTape input).search.selectedSchedule.positions ordinal).val

/-- Outside the two already counted Merkle events, literal acceptance on the
legacy extracted word transfers pointwise to the completion fixed immediately
before q16.  This is deliberately only an `IdealAccepts` theorem: the global
consistency-set cardinality is reclassified on the pre-q16 completion rather
than unsoundly copied from the later word. -/
theorem exact_ideal_accepts_transfers_to_preQ16_completion
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input)
    (decoded : Fin 641 → QM31Exact)
    (source : ExactParsedProofSourceBinding input decoded)
    (positions : ExactOpeningPositionsSourceBinding input)
    (prior later : List UnifiedExposureRecord) (pivot : UnifiedExposureRecord)
    (rootExact : exactFixedRootRecords input.package.root =
      prior ++ pivot :: later)
    (noLate : ¬ PrefixResolutionLateTargetHit (exactK12Truncate input)
      (exposurePrefixRawQueries prior) (exactK12OrderedQueries input)
      (exactK12Roots input) (exactK12Openings input))
    (noCollision : ¬ RawLogTruncatedDigestCollision (exactK12Truncate input)
      (exactK12OrderedQueries input))
    (accepts : IdealAccepts (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder) (exactK13Transcript input k12)
      (exactK13ParsedProof input).queries) :
    IdealAccepts (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder)
      (extractedIdealTranscript
        (preQ16PrefixWords prior (exactK12Roots input))
        (exactK13ParsedProof input).gamma
        (exactK13ParsedProof input).disclosedFinal)
      (exactK13ParsedProof input).queries := by
  have preQ16Projections : disclosuresAreProjections
      (preQ16PrefixWords prior (exactK12Roots input))
      (exactK12Openings input) := by
    rcases exact_accepted_openings_yield_preQ16_projections_or_counted_failure
        input prior later pivot rootExact k12.openingsAccepted
          k12.suppliedCovered with projections | late | collision
    · exact projections
    · exact False.elim (noLate late)
    · exact False.elim (noCollision collision)
  intro ordinal
  let opening := exactK12Openings input ordinal
  have oldProjection : openingIsProjection k12.words opening :=
    k12.projections ordinal
  have newProjection : openingIsProjection
      (preQ16PrefixWords prior (exactK12Roots input)) opening :=
    preQ16Projections ordinal
  have positionExact : ((exactK13ParsedProof input).queries ordinal).val =
      opening.position.val := by
    rw [source.selectedQueriesExact]
    exact (positions ordinal).symm
  exact query_consistent_of_shared_projected_opening
    (exactK13ParsedProof input).schedule (exactK13Encoders decoder)
    k12.words (preQ16PrefixWords prior (exactK12Roots input)) opening
    oldProjection newProjection (exactK13ParsedProof input).gamma
    (exactK13ParsedProof input).disclosedFinal
    ((exactK13ParsedProof input).queries ordinal) positionExact (accepts ordinal)

/-- Re-run the deterministic K1.3 classifier on a genuinely pre-q16 word.
Once ideal acceptance has been transferred, the only error branches are the
small query set and the named one-fold reduction event. -/
theorem classify_preQ16_k13_of_accepts
    (decoder : ExactDecoderInstantiation QM31Exact)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (words : ExtractedWords) (proof : Tag73K12ParsedProof)
    (accepts : IdealAccepts proof.schedule (decoderCodeEncoders decoder)
      (parsedK13Transcript words proof) proof.queries) :
    Nonempty (ParsedK13Certificate decoder words proof) ∨
      QueryPhaseFailure proof.schedule (decoderCodeEncoders decoder)
          (parsedK13Transcript words proof) proof.queries ∨
      OneFoldReductionFailure proof.schedule (decoderCodeEncoders decoder)
          (parsedK13Transcript words proof) := by
  rcases classifyParsedK13 decoder words proof with certificate | error
  · exact Or.inl ⟨certificate⟩
  · right
    cases error with
    | idealRejected rejected => exact False.elim (rejected accepts)
    | queryPhaseFailure failure => exact Or.inl failure
    | oneFoldReductionFailure failure => exact Or.inr failure
    | initialListCapFailure failure =>
        have overlap := exact_k13_initial_encoder_overlap_cap decoder
          initialEncoderExact
        exact False.elim
          ((initial_list_cap_failure_impossible_of_overlap
            (decoderCodeEncoders decoder) (parsedK13Transcript words proof)
            overlap) failure)

/-- Complete deterministic correction of the old q16-dependent classifier.
An accepted run either classifies against the pre-q16 completion, or enters
one of the two explicit Merkle failure events already exposed by K1.2. -/
theorem exact_preQ16_k13_classification_or_counted_merkle_failure
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input)
    (decoded : Fin 641 → QM31Exact)
    (source : ExactParsedProofSourceBinding input decoded)
    (positions : ExactOpeningPositionsSourceBinding input)
    (prior later : List UnifiedExposureRecord) (pivot : UnifiedExposureRecord)
    (rootExact : exactFixedRootRecords input.package.root =
      prior ++ pivot :: later)
    (accepts : IdealAccepts (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder) (exactK13Transcript input k12)
      (exactK13ParsedProof input).queries) :
    (Nonempty (ParsedK13Certificate decoder
        (preQ16PrefixWords prior (exactK12Roots input))
        (exactK13ParsedProof input)) ∨
      QueryPhaseFailure (exactK13ParsedProof input).schedule
          (exactK13Encoders decoder)
          (parsedK13Transcript
            (preQ16PrefixWords prior (exactK12Roots input))
            (exactK13ParsedProof input))
          (exactK13ParsedProof input).queries ∨
      OneFoldReductionFailure (exactK13ParsedProof input).schedule
          (exactK13Encoders decoder)
          (parsedK13Transcript
            (preQ16PrefixWords prior (exactK12Roots input))
            (exactK13ParsedProof input))) ∨
      PrefixResolutionLateTargetHit (exactK12Truncate input)
        (exposurePrefixRawQueries prior) (exactK12OrderedQueries input)
        (exactK12Roots input) (exactK12Openings input) ∨
      RawLogTruncatedDigestCollision (exactK12Truncate input)
        (exactK12OrderedQueries input) := by
  by_cases late : PrefixResolutionLateTargetHit (exactK12Truncate input)
      (exposurePrefixRawQueries prior) (exactK12OrderedQueries input)
      (exactK12Roots input) (exactK12Openings input)
  · exact Or.inr (Or.inl late)
  · by_cases collision : RawLogTruncatedDigestCollision
        (exactK12Truncate input) (exactK12OrderedQueries input)
    · exact Or.inr (Or.inr collision)
    · left
      apply classify_preQ16_k13_of_accepts decoder initialEncoderExact
      exact exact_ideal_accepts_transfers_to_preQ16_completion input k12 decoded
        source positions prior later pivot rootExact late collision accepts

#print axioms projected_opening_lane_value_eq
#print axioms projected_opening_batched_fibre_eq
#print axioms query_consistent_of_shared_projected_opening
#print axioms exact_ideal_accepts_transfers_to_preQ16_completion
#print axioms classify_preQ16_k13_of_accepts
#print axioms exact_preQ16_k13_classification_or_counted_merkle_failure

end

end AspisK1.V7Tag73K13PreQ16QueryHandoff
