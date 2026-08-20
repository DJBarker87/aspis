import V5TranscriptTailSourceProof
import AspisFormal.V5TranscriptSourceAdapter

namespace AspisV5TranscriptTailFinalJoin

open Aeneas Aeneas.Std
open V5TranscriptTailGenerated
open AspisFormal.V5ExactRuntimeWireRepair
open AspisV5NonceWorkAuthentication
open AspisV5TranscriptConnection
open AspisV5TranscriptSourceAdapter
open AspisV5TranscriptTailSourceProof

def byteOfU8 (value : Std.U8) :
    AspisFormal.V5ExactRuntimeWireRepair.Byte :=
  ⟨value.val % 256, Nat.mod_lt _ (by norm_num)⟩

def nonceOfU64 (value : Std.U64) : Nonce64 :=
  ⟨value.val % (2 ^ 64), Nat.mod_lt _ (by norm_num)⟩

def bytesOfU8 (values : List Std.U8) :
    List AspisFormal.V5ExactRuntimeWireRepair.Byte :=
  values.map byteOfU8

@[simp] theorem byteOfU8_19 :
    byteOfU8 19#u8 =
      (19 : AspisFormal.V5ExactRuntimeWireRepair.Byte) := by
  rfl

@[simp] theorem byteOfU8_44 :
    byteOfU8 44#u8 =
      (44 : AspisFormal.V5ExactRuntimeWireRepair.Byte) := by
  rfl

@[simp] theorem bytesOfU8_singleton (value : Std.U8) :
    bytesOfU8 [value] = [byteOfU8 value] := by
  rfl

def expandTailEvent : TailTranscriptEvent → List TranscriptEvent
  | .absorb label payload =>
      if label.val = 19 then
        [.absorb .finalPolynomial (byteOfU8 label) (bytesOfU8 payload)]
      else
        [.absorb .selector (byteOfU8 label) (bytesOfU8 payload)]
  | .finalNonce nonce =>
      let value := nonceOfU64 nonce
      [.verifyWork .finalQuery WorkKind.finalQuery.difficulty
          (List.ofFn (nonceLEBytes value)),
        .absorb .finalNonce (AbsorbSlot.label .finalNonce)
          (workAbsorbPayload .finalQuery value)]
  | .querySample _ _ _ => [.squeeze .queries]

theorem expected_tail_observation_maps_to_source
    (input : V5TranscriptInputs)
    (parsed : v5_cu_probe.ParsedProbeData)
    (selector : Std.U8)
    (hfinal : bytesOfU8 parsed.v5_final_coefficients.val =
      bytes input.finalPolynomial)
    (hnonce : nonceOfU64 parsed.v5_final_nonce = input.finalNonce)
    (hselector : byteOfU8 selector = input.selector) :
    (expectedTailEvents parsed selector).flatMap expandTailEvent =
      sourceTail input := by
  simp [expectedTailEvents, expandTailEvent, sourceTail,
    sourceAbsorb, sourceCheckAndAbsorb, absorbPayload, hfinal, hnonce,
    hselector, workAbsorbSlot, AbsorbSlot.label,
    V5TranscriptInputs.nonce, sourceSqueeze]

/-- A successful Aeneas-generated tail returns the exact decoded values and
queries, and its recorded transcript calls map to the complete maintained tail
schedule once the parsed bytes, nonce, and selector are identified with the
maintained input. -/
theorem generated_tail_success_matches_source_tail
    (input : V5TranscriptInputs)
    (transcript : aspis_core.transcript.Transcript)
    (parsed : v5_cu_probe.ParsedProbeData)
    (selector : Std.U8)
    (polynomial : Array aspis_core.field.QM31 4#usize)
    (queries : Array Std.U32 18#usize)
    (hfinal : bytesOfU8 parsed.v5_final_coefficients.val =
      bytes input.finalPolynomial)
    (hnonce : nonceOfU64 parsed.v5_final_nonce = input.finalNonce)
    (hselector : byteOfU8 selector = input.selector)
    (success :
      v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript
          transcript parsed selector = .ok (.Ok (polynomial, queries))) :
    (polynomial.val = [0#usize, 1#usize, 2#usize, 3#usize] ∧
      queries.val = transcript.sampledQueries.val ∧
      transcript.sampledQueries.val.length = 18 ∧ selector.val < 3) ∧
      (expectedTailEvents parsed selector).flatMap expandTailEvent =
        sourceTail input := by
  exact ⟨
    generated_tail_success_returns_exact_decodes_and_queries
      transcript parsed selector polynomial queries success,
    expected_tail_observation_maps_to_source input parsed selector
      hfinal hnonce hselector⟩

#print axioms expected_tail_observation_maps_to_source
#print axioms generated_tail_success_matches_source_tail

end AspisV5TranscriptTailFinalJoin
