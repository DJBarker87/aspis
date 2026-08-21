import V5AcceptedPostWorkSuccessors
import V5QuerySamplerFixedCall

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

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev EntryTranscript :=
  V5AcceptedEntryGenerated.aspis_core.transcript.Transcript

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

#print axioms accepted_final_query_successor_is_exact_sampler
#print axioms accepted_post_work_successors_build_exact_query_sampler

end AspisV5AcceptedTranscriptQueryBridge
