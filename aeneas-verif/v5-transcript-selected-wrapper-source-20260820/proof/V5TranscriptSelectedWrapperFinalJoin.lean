import V5TranscriptSelectedWrapperProof
import V5TranscriptTailFinalJoin

namespace AspisV5TranscriptSelectedWrapperFinalJoin

open Aeneas Aeneas.Std
open V5TranscriptSelectedWrapperGenerated
open AspisV5TranscriptSelectedWrapperProof
open AspisV5TranscriptTailFinalJoin

/-- A successful execution of the extracted selected-query wrapper reaches the
maintained transcript tail with the exact parsed polynomial, nonce, selector,
and returned query array.  The final conjunct records the wrapper's actual
success check on that same query array; it does not replace the separate proof
of the production GoodA/GoodB predicate. -/
theorem generated_selected_wrapper_success_matches_source_tail
    (input : AspisV5TranscriptConnection.V5TranscriptInputs)
    (transcript : aspis_core.transcript.Transcript)
    (parsed : v5_cu_probe.ParsedProbeData)
    (point : Array aspis_core.field.QM31 10#usize)
    (polynomial : Array aspis_core.field.QM31 4#usize)
    (queries : Array Std.U32 18#usize)
    (hfinal : bytesOfU8 parsed.v5_final_coefficients.val =
      AspisV5TranscriptConnection.bytes input.finalPolynomial)
    (hnonce : nonceOfU64 parsed.v5_final_nonce = input.finalNonce)
    (hselector : byteOfU8 parsed.v5_query_selector = input.selector)
    (success :
      v5_cu_probe.derive_v5_selected_good_queries_from_transcript
          transcript parsed point = .ok (.Ok (polynomial, queries))) :
    ((polynomial.val = [0#usize, 1#usize, 2#usize, 3#usize] ∧
        queries.val = transcript.sampledQueries.val ∧
        transcript.sampledQueries.val.length = 18 ∧
        parsed.v5_query_selector.val < 3) ∧
      (AspisV5TranscriptTailSourceProof.expectedTailEvents
          (toTailParsed parsed) parsed.v5_query_selector).flatMap
          expandTailEvent =
        AspisV5TranscriptSourceAdapter.sourceTail input) ∧
      candidateObservation point queries = true := by
  rcases generated_selected_wrapper_success_exact
      transcript parsed point polynomial queries success with
    ⟨_selectorInRange, lowerSuccess, candidateAccepted⟩
  have tailJoin := generated_tail_success_matches_source_tail
    input transcript (toTailParsed parsed) parsed.v5_query_selector
    polynomial queries hfinal hnonce hselector lowerSuccess
  exact ⟨tailJoin, candidateAccepted⟩

#print axioms generated_selected_wrapper_success_matches_source_tail

end AspisV5TranscriptSelectedWrapperFinalJoin
