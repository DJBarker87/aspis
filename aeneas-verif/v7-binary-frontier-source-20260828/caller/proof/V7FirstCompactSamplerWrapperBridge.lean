import V7FirstCompactSamplerOuterLoopBridge
import V7FirstCompactCallerBridge

open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace V7FirstCompactSamplerWrapperBridge

open V7FirstCompactSource
open V7FirstCompactCallerBridge
open V7FirstCompactSamplerLoop16Bridge
open V7FirstCompactSamplerOuterLoopBridge

abbrev Transcript := transcript.Transcript

def initialQ16Output : alloc.vec.Vec Std.U32 :=
  alloc.vec.Vec.with_capacity Std.U32 q16Count

@[simp] theorem initialQ16Output_values : initialQ16Output.val = [] := rfl

theorem q16_bound_is_power_of_two :
    core.num.U32.is_power_of_two 262144#u32 = .ok true := by
  have hpower : Nat.isPowerOfTwo 262144 := ⟨18, by norm_num⟩
  simp [core.num.U32.is_power_of_two, hpower]

theorem q16_bound_cast :
    lift (UScalar.cast .Usize 262144#u32) = .ok 262144#usize := by
  have hspec := UScalar.cast_inBounds_spec .Usize 262144#u32 (by scalar_tac)
  obtain ⟨value, heq, hval⟩ := Aeneas.Std.WP.spec_imp_exists hspec
  have hvalue : value = 262144#usize := by
    apply UScalar.eq_of_val_eq
    simpa using hval
  simpa [hvalue] using heq

theorem q16_query_mask :
    (262144#u32 - 1#u32 : Result Std.U32) = .ok 262143#u32 := by
  cases hresult : (262144#u32 - 1#u32 : Result Std.U32) with
  | fail error =>
      have spec := UScalar.sub_equiv 262144#u32 1#u32
      rw [hresult] at spec
      norm_num at spec
  | div =>
      have spec := UScalar.sub_equiv 262144#u32 1#u32
      rw [hresult] at spec
      contradiction
  | ok value =>
      have spec := UScalar.sub_equiv 262144#u32 1#u32
      rw [hresult] at spec
      norm_num at spec
      have valueExact : value.val = 262143 := by omega
      have : value = 262143#u32 :=
        UScalar.eq_of_val_eq (by simpa using valueExact)
      subst value
      exact hresult

/-- A successful literal public sampler call exposes the exact recursive q16
loop run from its empty output vector and zero draw counter. -/
theorem successful_wrapper_exposes_outer_loop
    (self sampledTranscript : Transcript)
    (sampled : alloc.vec.Vec Std.U32)
    (run :
      transcript.Transcript.challenge_queries_without_replacement self
          16#usize 262144#u32 64#usize =
        .ok (.Ok sampled, sampledTranscript)) :
    transcript.Transcript.challenge_queries_without_replacement_loop0
        self q16Count q16MaxDraws q16Mask initialQ16Output 0#usize =
      .ok (sampledTranscript, sampled) := by
  unfold transcript.Transcript.challenge_queries_without_replacement at run
  rw [q16_bound_is_power_of_two] at run
  simp only [bind_tc_ok, if_pos (by decide : true = true)] at run
  rw [q16_bound_cast] at run
  simp only [bind_tc_ok] at run
  have hcountBound : ¬ (262144#usize : Std.Usize) < 16#usize := by
    scalar_tac
  rw [if_neg hcountBound] at run
  have hcountNonzero : (16#usize : Std.Usize) ≠ 0#usize := by scalar_tac
  rw [if_neg hcountNonzero] at run
  rw [q16_query_mask] at run
  simp only [bind_tc_ok] at run
  change (do
      let outer ←
        transcript.Transcript.challenge_queries_without_replacement_loop0
          self 16#usize 64#usize 262143#u32 initialQ16Output 0#usize
      if alloc.vec.Vec.len outer.2 = 16#usize then
        .ok (core.result.Result.Ok outer.2, outer.1)
      else
        .ok (core.result.Result.Err
          (transcript.QuerySampleError.DrawLimitExhausted
            (alloc.vec.Vec.len outer.2) 64#usize), outer.1)) =
        .ok (core.result.Result.Ok sampled, sampledTranscript) at run
  generalize hloop :
    transcript.Transcript.challenge_queries_without_replacement_loop0
        self 16#usize 64#usize 262143#u32
          initialQ16Output 0#usize = loopResult
      at run
  cases loopResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok pair =>
      rcases pair with ⟨next, out⟩
      simp only [bind_tc_ok] at run
      by_cases hlength : alloc.vec.Vec.len out = 16#usize
      · rw [if_pos hlength] at run
        have pairExact :
            (core.result.Result.Ok out, next) =
              (core.result.Result.Ok sampled, sampledTranscript) :=
          Result.ok.inj run
        have outExact : out = sampled :=
          core.result.Result.Ok.inj (congrArg Prod.fst pairExact)
        have nextExact : next = sampledTranscript :=
          congrArg Prod.snd pairExact
        subst out
        subst next
        with_unfolding_all exact hloop
      · rw [if_neg hlength] at run
        simp at run

/-- The raw production candidate certificate carries the same exact recursive
loop run; no additional sampler premise is introduced at the caller seam. -/
theorem raw_candidate_exposes_outer_loop
    (inputTranscript : Transcript) (sourceCounter : Std.U8)
    (output : Option v7_onefold.V7CompactQuerySchedule)
    (raw : RawCandidateExecution inputTranscript sourceCounter output) :
    transcript.Transcript.challenge_queries_without_replacement_loop0
        raw.absorbed q16Count q16MaxDraws q16Mask initialQ16Output 0#usize =
      .ok (raw.sampledTranscript, raw.sampled) := by
  apply successful_wrapper_exposes_outer_loop
  have boundExact := raw_candidate_bound_exact inputTranscript sourceCounter
    output raw
  simpa [boundExact] using raw.samplerRun

/-- Literal raw-candidate success therefore produces the exact chronological
K1.3 block-scan postcondition proved for the translated outer loop. -/
theorem raw_candidate_has_exact_outer_model
    (inputTranscript : Transcript) (sourceCounter : Std.U8)
    (output : Option v7_onefold.V7CompactQuerySchedule)
    (raw : RawCandidateExecution inputTranscript sourceCounter output)
    (squeezeSucceeds : EverySqueezeSucceeds) :
    OuterSamplerPost raw.absorbed initialQ16Output 0#usize 0
      (raw.sampledTranscript, raw.sampled) := by
  have model := generated_outer_loop_matches_scanBlocks
    raw.absorbed initialQ16Output 0#usize 0 squeezeSucceeds
      (by simp [initialQ16Output, alloc.vec.Vec.with_capacity,
        alloc.vec.Vec.new])
      (by scalar_tac)
  rw [raw_candidate_exposes_outer_loop inputTranscript sourceCounter output raw]
    at model
  simpa only [Aeneas.Std.WP.spec_ok] using model

#print axioms successful_wrapper_exposes_outer_loop
#print axioms raw_candidate_exposes_outer_loop
#print axioms raw_candidate_has_exact_outer_model

end V7FirstCompactSamplerWrapperBridge
