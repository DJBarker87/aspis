import V5AcceptedPostWorkSuccessors
import V5AcceptedEntryAlphaDecode
import V5QuerySamplerFixedCall
import AspisFormal.V5AcceptedExecutionDerivedQueries

/-!
# Accepted query sampling is the extracted without-replacement sampler

The combined accepted-entry extraction and the focused transcript extraction
come from the same `transcript.rs` source blob.  The generated entry module
therefore links its transcript type and query method directly to the focused
definition.  This file applies the focused loop proof to the query call found
by inverting one accepted execution.
-/

namespace AspisV5AcceptedTranscriptQueryBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisV5AcceptedEntrySourceBridge
open AspisV5TranscriptConnection
open V5QuerySamplerGeneratedSemantics
open V5QuerySamplerFixedCall
open V5TranscriptPrimitivesProof
open AspisV5AcceptedExecutionDerivedQueries

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev EntryTranscript :=
  V5AcceptedEntryGenerated.aspis_core.transcript.Transcript

def roundUsize (round : Fin 4) : Std.Usize :=
  if round = 0 then 0#usize
  else if round = 1 then 1#usize
  else if round = 2 then 2#usize
  else 3#usize

def alphaAt (alphas : Array EntryQM31 4#usize) (round : Fin 4) : EntryQM31 :=
  alphas.val.get ⟨round.val, by
    rw [alphas.property]
    exact round.isLt⟩

/-- The four field challenges immediately following the four accepted work
checks are exactly the four values returned by the production alpha decoder.
This is a same-execution fact: both sides are obtained by inverting the same
accepted composite call. -/
structure AcceptedFoldChallengeProjection
    (parsed : EntryParsed) (alphas : Array EntryQM31 4#usize) : Prop where
  immediate : ∀ round : Fin 4,
    ∃ nonce beforeFold afterFold afterChallenge,
      Array.index_usize parsed.v5_fold_nonces (roundUsize round) = .ok nonce ∧
      V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_fold_nonce
          beforeFold (roundUsize round) nonce = .ok (.Ok (), afterFold) ∧
      V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.challenge_qm31
          afterFold = .ok (.Ok (alphaAt alphas round), afterChallenge)

private theorem nested_ok_unique {valueType errorType : Type}
    {left right : valueType}
    (equality :
      (.ok (.Ok left) : Result (core.result.Result valueType errorType)) =
        .ok (.Ok right)) :
    left = right := by
  exact core.result.Result.Ok.inj (Result.ok.inj equality)

theorem accepted_fold_successors_and_alpha_decode_are_same_values
    (parsed : EntryParsed) (alphas : Array EntryQM31 4#usize)
    (folds : AcceptedFourFoldChallengeSuccessors parsed)
    (alphaSuccess :
      V5AcceptedEntryGenerated.v5_cu_probe.decode_v5_fri_alphas parsed =
        .ok (.Ok alphas)) :
    AcceptedFoldChallengeProjection parsed alphas := by
  obtain ⟨zero, alpha0, alpha1, alpha2, alpha3, _, decode0, decode1,
      decode2, decode3, alphasExact⟩ :=
    AspisV5AcceptedEntryAlphaDecode.decode_v5_fri_alphas_success_calls
      parsed alphas alphaSuccess
  rcases folds with ⟨fold0, fold1, fold2, fold3⟩
  constructor
  intro round
  fin_cases round
  · rcases fold0 with
      ⟨nonce, beforeFold, afterFold, sampled, decoded, afterChallenge,
        nonceExact, workExact, sampleExact, decodedExact, _, same⟩
    have decodedIsAlpha : decoded = alpha0 :=
      (nested_ok_unique (decode0.symm.trans decodedExact)).symm
    have sampledIsAlpha : sampled = alpha0 := same.trans decodedIsAlpha
    refine ⟨nonce, beforeFold, afterFold, afterChallenge, ?_, ?_, ?_⟩
    · simpa [roundUsize] using nonceExact
    · simpa [roundUsize] using workExact
    · simpa [alphaAt, alphasExact, sampledIsAlpha] using sampleExact
  · rcases fold1 with
      ⟨nonce, beforeFold, afterFold, sampled, decoded, afterChallenge,
        nonceExact, workExact, sampleExact, decodedExact, _, same⟩
    have decodedIsAlpha : decoded = alpha1 :=
      (nested_ok_unique (decode1.symm.trans decodedExact)).symm
    have sampledIsAlpha : sampled = alpha1 := same.trans decodedIsAlpha
    refine ⟨nonce, beforeFold, afterFold, afterChallenge, ?_, ?_, ?_⟩
    · simpa [roundUsize] using nonceExact
    · simpa [roundUsize] using workExact
    · simpa [alphaAt, alphasExact, sampledIsAlpha] using sampleExact
  · rcases fold2 with
      ⟨nonce, beforeFold, afterFold, sampled, decoded, afterChallenge,
        nonceExact, workExact, sampleExact, decodedExact, _, same⟩
    have decodedIsAlpha : decoded = alpha2 :=
      (nested_ok_unique (decode2.symm.trans decodedExact)).symm
    have sampledIsAlpha : sampled = alpha2 := same.trans decodedIsAlpha
    refine ⟨nonce, beforeFold, afterFold, afterChallenge, ?_, ?_, ?_⟩
    · simpa [roundUsize] using nonceExact
    · simpa [roundUsize] using workExact
    · simpa [alphaAt, alphasExact, sampledIsAlpha] using sampleExact
  · rcases fold3 with
      ⟨nonce, beforeFold, afterFold, sampled, decoded, afterChallenge,
        nonceExact, workExact, sampleExact, decodedExact, _, same⟩
    have decodedIsAlpha : decoded = alpha3 :=
      (nested_ok_unique (decode3.symm.trans decodedExact)).symm
    have sampledIsAlpha : sampled = alpha3 := same.trans decodedIsAlpha
    refine ⟨nonce, beforeFold, afterFold, afterChallenge, ?_, ?_, ?_⟩
    · simpa [roundUsize] using nonceExact
    · simpa [roundUsize] using workExact
    · simpa [alphaAt, alphasExact, sampledIsAlpha] using sampleExact

/-- Exact blocks, returned positions, and draw bound for the sampler call
which immediately follows the accepted final work check. -/
def AcceptedQuerySamplerEvidence
    (_parsed : EntryParsed) (queries : Array Std.U32 18#usize) : Prop :=
  ∃ (initialTranscript finalTranscript : EntryTranscript)
      (blocks : List (Array Std.U8 32#usize)) (finalDraws : Std.Usize),
    ExactSqueezeTrace initialTranscript blocks finalTranscript ∧
      derive18Queries (blocks.map arrayDigest) =
        some (queries.val.map UScalar.val) ∧
      finalDraws.val ≤ 64

theorem accepted_final_query_successor_is_exact_sampler
    (parsed : EntryParsed) (queries : Array Std.U32 18#usize)
    (successor : AcceptedFinalQuerySuccessor parsed queries) :
    AcceptedQuerySamplerEvidence parsed queries := by
  rcases successor with
    ⟨beforeFinal, afterFinal, selectorBytes, selectorLabel, afterSelector,
      queryBound, drawLimit, sampledQueries, afterQueries,
      finalWorkSuccess, selectorBytesSuccess, selectorLabelSuccess,
      selectorAbsorbSuccess, queryBoundSuccess, drawLimitSuccess,
      querySuccess, arraySuccess⟩
  have hbound : queryBound = 131072#u32 := by
    apply UScalar.eq_of_val_eq
    norm_num at queryBoundSuccess ⊢
    exact congrArg UScalar.val (Result.ok.inj queryBoundSuccess).symm
  have hdrawLimit : drawLimit = 64#usize := by
    simpa [V5AcceptedEntryGenerated.aspis_core.circle_hiding_prefix.PAYMENT_HIDING_QUERY_DRAW_LIMIT]
      using (Result.ok.inj drawLimitSuccess).symm
  subst queryBound
  subst drawLimit
  have hquery :
      V5TranscriptPrimitivesGenerated.aspis_core.transcript.Transcript.challenge_queries_without_replacement
          afterSelector 18#usize 131072#u32 64#usize =
        .ok (.Ok sampledQueries, afterQueries) := by
    simpa [V5AcceptedEntryGenerated.v5_cu_probe.V5_CU_PROBE_QUERY_COUNT,
      V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.challenge_queries_without_replacement]
      using querySuccess
  obtain ⟨blocks, finalDraws, htrace, hdecode, hdraws, hscan⟩ :=
    generated_fixed_call_success_is_exact afterSelector afterQueries
      sampledQueries hquery
  have hvalues : sampledQueries.val = queries.val := by
    simp only [V5AcceptedEntryGenerated.Array.Insts.CoreConvertTryFromVecVec.try_from]
      at arraySuccess
    split at arraySuccess
    · simpa using congrArg (fun result => result.val)
        (core.result.Result.Ok.inj (Result.ok.inj arraySuccess))
    · simp at arraySuccess
  refine ⟨afterSelector, afterQueries, blocks, finalDraws, htrace, ?_, hdraws⟩
  simpa [vecNats, hvalues] using hdecode

theorem accepted_post_work_successors_build_exact_query_sampler
    (parsed : EntryParsed) (verifiedPrefix : EntryVerifiedPrefix)
    (queries : Array Std.U32 18#usize)
    (postWork : AcceptedCompositePostWorkSuccessors parsed verifiedPrefix
      queries) :
    AcceptedQuerySamplerEvidence parsed queries :=
  accepted_final_query_successor_is_exact_sampler parsed queries
    postWork.finalQueries

/-- An accepted production sampler call determines the ordered released
query schedule and its exact 18-element set.  Neither the schedule nor its
injectivity, range, or set cardinality is supplied by the caller. -/
theorem accepted_query_sampler_builds_decoded_schedule
    (parsed : EntryParsed) (queries : Array Std.U32 18#usize)
    (sampler : AcceptedQuerySamplerEvidence parsed queries) :
    ∃ (blocks : List (FixedBytes 32))
        (hdecode : derive18Queries blocks =
          some (queries.val.map UScalar.val)),
      let schedule := decodedQuerySchedule blocks
        (queries.val.map UScalar.val) hdecode
      let querySet := decodedQuerySet blocks
        (queries.val.map UScalar.val) hdecode
      List.ofFn (fun index => (schedule index).val) =
          queries.val.map UScalar.val ∧
        querySet = Finset.univ.image schedule ∧
        querySet.card = 18 ∧
        (queries.val.map UScalar.val).Nodup ∧
        (∀ query ∈ queries.val.map UScalar.val, query < 131072) := by
  rcases sampler with
    ⟨initialTranscript, finalTranscript, rawBlocks, finalDraws,
      trace, decode, draws⟩
  let blocks : List (FixedBytes 32) := rawBlocks.map arrayDigest
  have hdecode : derive18Queries blocks =
      some (queries.val.map UScalar.val) := by
    simpa [blocks] using decode
  refine ⟨blocks, hdecode, ?_⟩
  have exact := decoded_queries_are_exact blocks
    (queries.val.map UScalar.val) hdecode
  exact ⟨exact.1, rfl, exact.2.1, exact.2.2.2.1, exact.2.2.2.2⟩

#print axioms accepted_final_query_successor_is_exact_sampler
#print axioms accepted_post_work_successors_build_exact_query_sampler
#print axioms accepted_query_sampler_builds_decoded_schedule

end AspisV5AcceptedTranscriptQueryBridge
