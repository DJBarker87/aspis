import V7FirstCompactCallerBridge
import AspisFormal.K1.V7Tag73Q16DeployedDecoderPrefixBridge

/-!
# Raw translated q16 array to the K1.3 decoded schedule

This isolates the only remaining source/scheduler alignment after candidate
inversion.  Once the translated sampler's ordered `u32` values are identified
with the deployed decoder's consumed digest-block scan, the literal returned
array is exactly `queryScheduleArray schedule`.
-/

open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace V7FirstCompactK13RawScheduleBridge

open V7FirstCompactCallerBridge
open V7FirstCompactFrontierK13Integration
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73Q16DeployedDecoderPrefixBridge

noncomputable section

theorem u32_list_eq_of_map_val_eq
    {left right : List Std.U32}
    (values : left.map UScalar.val = right.map UScalar.val) :
    left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons head tail ih =>
      cases right with
      | nil => simp at values
      | cons other rest =>
          simp only [List.map_cons, List.cons.injEq] at values
          have headExact : head = other := UScalar.eq_of_val_eq values.1
          subst other
          exact congrArg (List.cons head) (ih values.2)

theorem query_schedule_array_values (schedule : QuerySchedule) :
    (queryScheduleArray schedule).val.map UScalar.val =
      (List.ofFn schedule.positions).map Fin.val := by
  simp [queryScheduleArray, Std.U32.ofNatCore_val_eq]

/-- The array/decoder equality is a pure consequence of ordered sampler-value
alignment.  Hash/SHA and scheduler causality are deliberately absent here. -/
theorem raw_queries_eq_decoded_schedule
    (inputTranscript : V7FirstCompactSource.transcript.Transcript)
    (sourceCounter : Std.U8)
    (output : Option V7FirstCompactSource.v7_onefold.V7CompactQuerySchedule)
    (raw : RawCandidateExecution inputTranscript sourceCounter output)
    (counter : Fin 64) (blocks : List Digest256) (schedule : QuerySchedule)
    (decoded :
      decodeCandidateOutcome counter blocks = some (.schedule schedule))
    (sampledValues :
      raw.sampled.val.map UScalar.val = (scanQ16 blocks).positions) :
    raw.queries = queryScheduleArray schedule := by
  have decodedPositions :=
    decodeCandidateOutcome_schedule_positions counter blocks schedule decoded
  have rawValues :
      raw.queries.val.map UScalar.val =
        (queryScheduleArray schedule).val.map UScalar.val := by
    calc
      _ = raw.sampled.val.map UScalar.val := congrArg
        (List.map UScalar.val)
        (raw_candidate_queries_values_exact inputTranscript sourceCounter
          output raw)
      _ = (scanQ16 blocks).positions := sampledValues
      _ = (List.ofFn schedule.positions).map Fin.val :=
        decodedPositions.symm
      _ = _ := (query_schedule_array_values schedule).symm
  apply Subtype.eq
  exact u32_list_eq_of_map_val_eq rawValues

#print axioms u32_list_eq_of_map_val_eq
#print axioms query_schedule_array_values
#print axioms raw_queries_eq_decoded_schedule

end

end V7FirstCompactK13RawScheduleBridge
