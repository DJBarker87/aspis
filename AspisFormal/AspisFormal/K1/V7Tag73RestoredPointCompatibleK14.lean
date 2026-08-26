import AspisFormal.K1.V7Tag73ExactFixedK13K14FailureReduction
import AspisFormal.Pool.V7CorrelatedPointClaimExtraction
import AspisFormal.Pool.V7FixedWidth29TupleList
import AspisFormal.Pool.V7PointClaimBatchBinding

/-!
# Restoration-wide point-compatible K1.4 extraction

This is the causal replacement for treating the locally selected component
tuple as fixed before `gamma`.  The restored response strategy is filtered by
the three exact point-functional equations.  Above the existing published
width-29 cap, correlated decoding returns one fixed tuple, one jointly-close
restored response, and all 87 point claims exactly.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace AspisK1.V7Tag73RestoredPointCompatibleK14

open AspisK1.V7Tag73ExactFixedK13K14FailureReduction
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CandidateChainExtraction
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7CombinedCandidateExact
open AspisPool.V7CorrelatedPointClaimExtraction
open AspisPool.V7ExtractedLaneWords
open AspisPool.V7FixedWidth29TupleList
open AspisPool.V7PointClaimBatchBinding
open AspisPool.V7Width29ComponentExtraction
open AspisV5ComponentADeployedTerminalApplicability
open AspisV5ComponentCQM31TowerExact
open AspisV6OneFoldCandidateExtraction
open AspisV6PublishedTheoremInterfaces
open AspisV6TranscriptRelationGrammar
open AspisV6Width29ConstrainedFunctionalExtraction
open AspisV6Width29CorrelatedAgreement

noncomputable section

/-- Exact constrained gamma set for one restoration-wide response strategy. -/
noncomputable def restoredPointConstrainedGammaSet
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (point : Fin 10 → QM31Exact)
    (claims : Fin 3 → Fin 29 → QM31Exact)
    (response : QM31Exact → InitialMessage QM31Exact) : Finset QM31Exact :=
  width29GoodChallenges exactInitialEncoder
    AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
    (extractedWidth29InitialWords words)
    (constrainedWidth29Strategy (pointFunctional point) claims
      (restoredWidth29Strategy decoder
        (extractedWidth29InitialWords words) response))

/-- One fixed point-compatible tuple plus a concrete jointly-close restored
response. -/
def HasRestoredPointCompatibleK14
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (point : Fin 10 → QM31Exact)
    (claims : Fin 3 → Fin 29 → QM31Exact)
    (response : QM31Exact → InitialMessage QM31Exact) : Prop :=
  ∃ (components : Width29InitialMessages QM31Exact) (gamma : QM31Exact),
    gamma ∈ restoredPointConstrainedGammaSet decoder words point claims
      response ∧
    Width29ValidResponse exactInitialEncoder
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
      (extractedWidth29InitialWords words)
      (restoredWidth29Strategy decoder
        (extractedWidth29InitialWords words) response) gamma ∧
    Width29CandidateOnCurve exactInitialEncoder
      (restoredWidth29Strategy decoder
        (extractedWidth29InitialWords words) response) components gamma ∧
    (restoredWidth29Strategy decoder
      (extractedWidth29InitialWords words) response).support gamma ⊆
      width29JointAgreementSet exactInitialEncoder
        (extractedWidth29InitialWords words) components ∧
    ∀ row, claims row = fun lane =>
      multilinearEvalValue
        (AspisV6AcceptedPathObligations.statementPoint point row)
        (components lane)

/-- The whole strengthened failure event occupies at most the existing
published K1.4 cap.  The 87 functional equations do not add a decoder-list
factor or a separate post-selected 84-root term. -/
theorem no_restored_point_compatible_k14_card_le
    (decoder : ExactDecoderInstantiation QM31Exact)
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (point : Fin 10 → QM31Exact)
    (claims : Fin 3 → Fin 29 → QM31Exact)
    (response : QM31Exact → InitialMessage QM31Exact)
    (failure : ¬ HasRestoredPointCompatibleK14 decoder words point claims
      response) :
    (restoredPointConstrainedGammaSet decoder words point claims response).card
      ≤ initialBatchChallengeCap := by
  by_contra exceeds
  have many : initialBatchChallengeCap <
      (restoredPointConstrainedGammaSet decoder words point claims response).card :=
    Nat.lt_of_not_ge exceeds
  apply failure
  exact many_constrained_gamma_responses_extract_point_compatible_components
    published (extractedWidth29InitialWords words) point claims
    (restoredWidth29Strategy decoder
      (extractedWidth29InitialWords words) response) many

/-- The source-circle theorem may be stated on the decoder encoder.  The
proved production encoder equality transports it to the exact mathematical
encoder used by the constrained extractor. -/
theorem published_exact_of_decoder_encoder_exact
    (decoder : ExactDecoderInstantiation QM31Exact)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (published : PublishedInitialWidth29CurveDecodability
      decoder.initialEncoder) :
    PublishedInitialWidth29CurveDecodability exactInitialEncoder := by
  simpa only [initialEncoderExact] using published

/-! ## Packaging one retained restored response as a coherent trace -/

/-- A retained point-compatible response can be packaged as the ordinary
coherent-trace object without reselecting a different local component tuple. -/
theorem point_compatible_selected_chain_extracts_coherent_trace
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : InitialProjectionBinding decoder)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (point : Fin 10 → QM31Exact)
    (claims : Fin 3 → Fin 29 → QM31Exact)
    (response : QM31Exact → InitialMessage QM31Exact)
    (components : Width29InitialMessages QM31Exact)
    (gamma : QM31Exact)
    (onCurve : Width29CandidateOnCurve exactInitialEncoder
      (restoredWidth29Strategy decoder
        (extractedWidth29InitialWords words) response) components gamma)
    (shared :
      (restoredWidth29Strategy decoder
        (extractedWidth29InitialWords words) response).support gamma ⊆
      width29JointAgreementSet exactInitialEncoder
        (extractedWidth29InitialWords words) components)
    (claimsExact : ∀ row, claims row = fun lane =>
      multilinearEvalValue
        (AspisV6AcceptedPathObligations.statementPoint point row)
        (components lane))
    (disclosedFinal : FinalMessage QM31Exact)
    (schedule : ExactSchedule)
    (selected : ExactCandidatePair)
    (responseAt : response gamma = selected.1)
    (selectedEq :
      selectCandidateChain
          (decoder.decodeBoth
            (extractedIdealTranscript words gamma disclosedFinal).initial
            (foldedReceived schedule
              (extractedIdealTranscript words gamma disclosedFinal)))
          schedule disclosedFinal = some selected) :
    ∃ extraction : CoherentTraceExtraction decoder binding words gamma
        disclosedFinal schedule,
      extraction.combined = selected ∧
      extraction.components = components ∧
      extraction.components ∈ fixedWidth29TupleList decoder
        (extractedWidth29InitialWords words) ∧
      projectWidth29ToC1 extraction.components ∈
        fixedC1TupleList decoder (c1Received words) ∧
      ∀ row lane, claims row lane =
        componentPointClaim extraction point row lane := by
  have supportEq := restoredWidth29Strategy_support_eq_selected decoder
    (extractedWidth29InitialWords words) selected response gamma responseAt
  have selectedValid := selected_chain_yields_valid_width29_response decoder
    words gamma disclosedFinal schedule selected selectedEq
  have selectedShared :
      (selectedCandidateStrategy decoder
        (extractedWidth29InitialWords words) selected).support gamma ⊆
      width29JointAgreementSet decoder.initialEncoder
        (extractedWidth29InitialWords words) components := by
    rw [← supportEq]
    simpa only [initialEncoderExact] using shared
  have selectedOnCurve : Width29CandidateOnCurve decoder.initialEncoder
      (selectedCandidateStrategy decoder
        (extractedWidth29InitialWords words) selected) components gamma := by
    unfold Width29CandidateOnCurve at onCurve ⊢
    rw [selectedCandidateStrategy_candidate]
    rw [restoredWidth29Strategy_candidate, responseAt] at onCurve
    simpa only [initialEncoderExact] using onCurve
  have everyDecoded := shared_support_components_enter_decoder decoder
    (extractedWidth29InitialWords words)
    (selectedCandidateStrategy decoder
      (extractedWidth29InitialWords words) selected)
    gamma components selectedValid selectedShared
  obtain ⟨extraction, combinedExact, componentsExact⟩ :=
    selected_chain_and_matching_components_extract_coherent_trace decoder
      binding words gamma disclosedFinal schedule selected selectedEq components
      everyDecoded selectedShared selectedOnCurve
  have restoredLarge :
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold <
        ((restoredWidth29Strategy decoder
          (extractedWidth29InitialWords words) response).support gamma).card := by
    rw [supportEq]
    exact selectedValid.1
  have fixedMember : components ∈ fixedWidth29TupleList decoder
      (extractedWidth29InitialWords words) :=
    mem_fixedWidth29TupleList_of_shared_support decoder
      (extractedWidth29InitialWords words) components
      ((restoredWidth29Strategy decoder
        (extractedWidth29InitialWords words) response).support gamma)
      restoredLarge shared everyDecoded
  have c1Member := width29_member_projects_to_fixedC1TupleList decoder words
    components fixedMember
  refine ⟨extraction, combinedExact, componentsExact, ?_, ?_, ?_⟩
  · simpa only [componentsExact] using fixedMember
  · simpa only [componentsExact] using c1Member
  intro row lane
  unfold componentPointClaim
  rw [componentsExact]
  exact congrFun (claimsExact row) lane

/-! ## Accepted restoration families

The total `response : gamma → message` used by the correlated theorem needs a
default on rejecting branches.  A default must not accidentally become a
usable close response.  The following data-only family therefore carries an
explicit availability predicate, and its strategy has empty support whenever
the actual restored branch did not produce a selected candidate chain. -/

structure RestoredSelectedChainFamily
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords) where
  available : QM31Exact → Prop
  response : QM31Exact → InitialMessage QM31Exact
  disclosedFinal : QM31Exact → FinalMessage QM31Exact
  schedule : QM31Exact → ExactSchedule
  selected : QM31Exact → ExactCandidatePair
  responseAt : ∀ gamma, available gamma →
    response gamma = (selected gamma).1
  selectedExact : ∀ gamma, available gamma →
    selectCandidateChain
        (decoder.decodeBoth
          (extractedIdealTranscript words gamma (disclosedFinal gamma)).initial
          (foldedReceived (schedule gamma)
            (extractedIdealTranscript words gamma (disclosedFinal gamma))))
        (schedule gamma) (disclosedFinal gamma) = some (selected gamma)

noncomputable def acceptedRestoredWidth29Strategy
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (family : RestoredSelectedChainFamily decoder words) :
    Width29ProximateStrategy QM31Exact (Fin 1048576)
      (InitialMessage QM31Exact) := by
  classical
  exact {
    candidate := family.response
    support := fun gamma =>
      if family.available gamma then
        Finset.univ.filter fun index =>
          width29CurveValue (extractedWidth29InitialWords words) gamma index =
            decoder.initialEncoder (family.response gamma) index
      else
        ∅
  }

theorem accepted_restored_support_eq_restored_of_available
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (family : RestoredSelectedChainFamily decoder words)
    (gamma : QM31Exact) (available : family.available gamma) :
    (acceptedRestoredWidth29Strategy decoder words family).support gamma =
      (restoredWidth29Strategy decoder (extractedWidth29InitialWords words)
        family.response).support gamma := by
  classical
  simp [acceptedRestoredWidth29Strategy, restoredWidth29Strategy, available]

theorem accepted_restored_valid_implies_available
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (family : RestoredSelectedChainFamily decoder words)
    (encoder : InitialMessage QM31Exact →
      AspisPool.AlgorithmicCircleDecoderV7.InitialWord QM31Exact)
    (gamma : QM31Exact)
    (valid : Width29ValidResponse encoder
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
      (extractedWidth29InitialWords words)
      (acceptedRestoredWidth29Strategy decoder words family) gamma) :
    family.available gamma := by
  classical
  by_contra unavailable
  have emptySupport :
      (acceptedRestoredWidth29Strategy decoder words family).support gamma =
        ∅ := by
    simp [acceptedRestoredWidth29Strategy, unavailable]
  have impossible :
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold < 0 := by
    simpa only [emptySupport, Finset.card_empty] using valid.1
  exact (Nat.not_lt_zero _ impossible).elim

noncomputable def acceptedRestoredPointConstrainedGammaSet
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (point : Fin 10 → QM31Exact)
    (claims : Fin 3 → Fin 29 → QM31Exact)
    (family : RestoredSelectedChainFamily decoder words) : Finset QM31Exact :=
  width29GoodChallenges exactInitialEncoder
    AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
    (extractedWidth29InitialWords words)
    (constrainedWidth29Strategy (pointFunctional point) claims
      (acceptedRestoredWidth29Strategy decoder words family))

set_option maxHeartbeats 5000000 in
/-- One actually accepted restored branch enters the single constrained gamma
set whenever its two-level point aggregate is exact outside the earlier
degree-two `kappa` collision.  The zerocheck point is unrelated here: `point`
is the later semantic MLE point bound into the serialized claim rows. -/
theorem accepted_branch_mem_restored_point_constrained_gamma_set
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : InitialProjectionBinding decoder)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (point : Fin 10 → QM31Exact)
    (fields : FixedFieldView QM31Exact)
    (family : RestoredSelectedChainFamily decoder words)
    (gamma kappa : QM31Exact)
    (available : family.available gamma)
    {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (combinedExact : extraction.combined = family.selected gamma)
    (gammaNonzero : gamma ≠ 0)
    (aggregateExact : claimedPointBatch fields gamma kappa =
      extractedPointBatch extraction point kappa)
    (noKappaCollision :
      ¬ KappaPointRowCollision fields extraction point kappa) :
    gamma ∈ acceptedRestoredPointConstrainedGammaSet decoder words point
      fields.pointClaim family := by
  classical
  have everyRowZero :=
    every_row_gamma_discrepancy_zero_of_aggregate_exact fields extraction
      point kappa aggregateExact noKappaCollision
  have responseAt := family.responseAt gamma available
  have selectedValid := selected_chain_yields_valid_width29_response decoder
    words gamma disclosedFinal schedule
    extraction.combined extraction.combinedSelected
  have acceptedSupportEqRestored :=
    accepted_restored_support_eq_restored_of_available decoder words family
      gamma available
  have restoredSupportEqSelected :=
    restoredWidth29Strategy_support_eq_selected decoder
      (extractedWidth29InitialWords words) (family.selected gamma)
      family.response gamma responseAt
  have acceptedSupportEqSelected :
      (acceptedRestoredWidth29Strategy decoder words family).support gamma =
        (selectedCandidateStrategy decoder
          (extractedWidth29InitialWords words) extraction.combined).support gamma := by
    rw [acceptedSupportEqRestored, restoredSupportEqSelected, ← combinedExact]
  have acceptedValid : Width29ValidResponse exactInitialEncoder
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
      (extractedWidth29InitialWords words)
      (acceptedRestoredWidth29Strategy decoder words family) gamma := by
    constructor
    · rw [acceptedSupportEqSelected]
      exact selectedValid.1
    · intro index member
      have selectedMember : index ∈
          (selectedCandidateStrategy decoder
            (extractedWidth29InitialWords words) extraction.combined).support
              gamma := by
        rw [← acceptedSupportEqSelected]
        exact member
      have selectedAgreement := selectedValid.2 index selectedMember
      change width29CurveValue (extractedWidth29InitialWords words) gamma index =
        exactInitialEncoder (family.response gamma) index
      rw [responseAt, ← combinedExact, ← initialEncoderExact]
      exact selectedAgreement
  have functionalConstraint : Width29FunctionalConstraint
      (pointFunctional point) fields.pointClaim
      (acceptedRestoredWidth29Strategy decoder words family) gamma := by
    intro row
    have rowZero : rowGammaDiscrepancy fields extraction point row = 0 :=
      congrFun everyRowZero row
    have rowBatchExact :=
      (rowGammaDiscrepancy_eq_zero_iff fields extraction point row).mp rowZero
    calc
      pointFunctional point row
          ((acceptedRestoredWidth29Strategy decoder words family).candidate gamma) =
          pointFunctional point row (family.response gamma) := by rfl
      _ = pointFunctional point row (family.selected gamma).1 := by
        rw [responseAt]
      _ = pointFunctional point row extraction.combined.1 := by
        rw [combinedExact]
      _ = pointFunctional point row
          (batchInitialMessages extraction.components gamma) := by
        rw [CoherentTraceExtraction.combined_eq_batchInitialMessages extraction
          initialEncoderExact]
      _ = width29Batch
          (fun lane => componentPointClaim extraction point row lane) gamma :=
        pointFunctional_batchInitialMessages point row extraction.components gamma
      _ = width29Batch (fields.pointClaim row) gamma := rowBatchExact.symm
  unfold acceptedRestoredPointConstrainedGammaSet
  rw [mem_width29GoodChallenges_iff]
  refine ⟨gammaNonzero, ?_⟩
  constructor
  · simpa [constrainedWidth29Strategy, functionalConstraint] using
      acceptedValid.1
  · intro index member
    have acceptedMember : index ∈
        (acceptedRestoredWidth29Strategy decoder words family).support gamma := by
      simpa [constrainedWidth29Strategy, functionalConstraint] using member
    simpa [constrainedWidth29Strategy, functionalConstraint] using
      acceptedValid.2 index acceptedMember

def HasAcceptedRestoredPointCompatibleK14
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (point : Fin 10 → QM31Exact)
    (claims : Fin 3 → Fin 29 → QM31Exact)
    (family : RestoredSelectedChainFamily decoder words) : Prop :=
  ∃ (components : Width29InitialMessages QM31Exact) (gamma : QM31Exact),
    gamma ∈ acceptedRestoredPointConstrainedGammaSet decoder words point
      claims family ∧
    Width29ValidResponse exactInitialEncoder
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
      (extractedWidth29InitialWords words)
      (acceptedRestoredWidth29Strategy decoder words family) gamma ∧
    Width29CandidateOnCurve exactInitialEncoder
      (acceptedRestoredWidth29Strategy decoder words family) components gamma ∧
    (acceptedRestoredWidth29Strategy decoder words family).support gamma ⊆
      width29JointAgreementSet exactInitialEncoder
        (extractedWidth29InitialWords words) components ∧
    ∀ row, claims row = fun lane =>
      multilinearEvalValue
        (AspisV6AcceptedPathObligations.statementPoint point row)
        (components lane)

theorem no_accepted_restored_point_compatible_k14_card_le
    (decoder : ExactDecoderInstantiation QM31Exact)
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (point : Fin 10 → QM31Exact)
    (claims : Fin 3 → Fin 29 → QM31Exact)
    (family : RestoredSelectedChainFamily decoder words)
    (failure : ¬ HasAcceptedRestoredPointCompatibleK14 decoder words point
      claims family) :
    (acceptedRestoredPointConstrainedGammaSet decoder words point claims
      family).card ≤ initialBatchChallengeCap := by
  by_contra exceeds
  have many : initialBatchChallengeCap <
      (acceptedRestoredPointConstrainedGammaSet decoder words point claims
        family).card := Nat.lt_of_not_ge exceeds
  apply failure
  exact many_constrained_gamma_responses_extract_point_compatible_components
    published (extractedWidth29InitialWords words) point claims
    (acceptedRestoredWidth29Strategy decoder words family) many

set_option linter.constructorNameAsVariable false in
/-- A successful accepted restoration family now yields the ordinary K1.4
object and exact point claims on that same object. -/
theorem accepted_restored_point_compatible_k14_extracts_coherent_trace
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : InitialProjectionBinding decoder)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (point : Fin 10 → QM31Exact)
    (claims : Fin 3 → Fin 29 → QM31Exact)
    (family : RestoredSelectedChainFamily decoder words)
    (certificate : HasAcceptedRestoredPointCompatibleK14 decoder words point
      claims family) :
    ∃ (gamma : QM31Exact)
        (extraction : CoherentTraceExtraction decoder binding words gamma
          (family.disclosedFinal gamma) (family.schedule gamma)),
      extraction.combined = family.selected gamma ∧
      extraction.components ∈ fixedWidth29TupleList decoder
        (extractedWidth29InitialWords words) ∧
      projectWidth29ToC1 extraction.components ∈
        fixedC1TupleList decoder (c1Received words) ∧
      ∀ row lane, claims row lane =
        componentPointClaim extraction point row lane := by
  rcases certificate with ⟨components, gamma, member, valid, onCurve, shared,
    claimsExact⟩
  have available := accepted_restored_valid_implies_available decoder words
    family exactInitialEncoder gamma valid
  have supportEq := accepted_restored_support_eq_restored_of_available decoder
    words family gamma available
  have restoredOnCurve : Width29CandidateOnCurve exactInitialEncoder
      (restoredWidth29Strategy decoder (extractedWidth29InitialWords words)
        family.response) components gamma := by
    unfold Width29CandidateOnCurve at onCurve ⊢
    exact onCurve
  have restoredShared :
      (restoredWidth29Strategy decoder (extractedWidth29InitialWords words)
        family.response).support gamma ⊆
      width29JointAgreementSet exactInitialEncoder
        (extractedWidth29InitialWords words) components := by
    rw [← supportEq]
    exact shared
  obtain ⟨extraction, combinedExact, _componentsExact, fixedMember, c1Member,
      exactPointClaims⟩ :=
    point_compatible_selected_chain_extracts_coherent_trace decoder binding
      initialEncoderExact words point claims family.response components gamma
      restoredOnCurve restoredShared claimsExact
      (family.disclosedFinal gamma) (family.schedule gamma)
      (family.selected gamma) (family.responseAt gamma available)
      (family.selectedExact gamma available)
  exact ⟨gamma, extraction, combinedExact, fixedMember, c1Member,
    exactPointClaims⟩

#print axioms no_restored_point_compatible_k14_card_le
#print axioms published_exact_of_decoder_encoder_exact
#print axioms point_compatible_selected_chain_extracts_coherent_trace
#print axioms accepted_restored_valid_implies_available
#print axioms no_accepted_restored_point_compatible_k14_card_le
#print axioms accepted_branch_mem_restored_point_constrained_gamma_set
#print axioms
  accepted_restored_point_compatible_k14_extracts_coherent_trace

end

end AspisK1.V7Tag73RestoredPointCompatibleK14
