import V7FirstCompactSamplerWrapperBridge
import V7FirstCompactK13RawScheduleBridge

open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace V7FirstCompactSamplerK13PositionBridge

open V7FirstCompactSource
open V7FirstCompactCallerBridge
open V7FirstCompactSamplerLoop16Bridge
open V7FirstCompactSamplerNativeBlockBridge
open V7FirstCompactSamplerOuterLoopBridge
open V7FirstCompactSamplerWrapperBridge
open AspisV5QuerySamplerControl
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73Q16DeployedDecoderPrefixBridge

abbrev Transcript := transcript.Transcript

theorem scanUntil_of_complete
    (count : Nat) (seen values : List Nat)
    (complete : seen.length = count) :
    scanUntil count seen values = seen := by
  cases values with
  | nil => rfl
  | cons head tail => simp [scanUntil, complete]

theorem scanUntil_append
    (count : Nat) (seen left right : List Nat) :
    scanUntil count seen (left ++ right) =
      scanUntil count (scanUntil count seen left) right := by
  induction left generalizing seen with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.cons_append, scanUntil]
      by_cases complete : seen.length = count
      · simp only [complete, ↓reduceIte]
        exact (scanUntil_of_complete count seen right complete).symm
      · simp only [complete, ↓reduceIte]
        exact ih (keepIfNew seen head)

theorem scanWords_accepted_eq_scanUntil_take
    (count maxDraws : Nat) (state : BlockScanState) (words : List Nat)
    (drawsBound : state.draws ≤ maxDraws) :
    (scanWords count maxDraws state words).state.accepted =
      scanUntil count state.accepted
        (words.take (maxDraws - state.draws)) := by
  induction words generalizing state with
  | nil => simp [scanWords, scanUntil]
  | cons value remaining ih =>
      by_cases complete : state.accepted.length = count
      · rw [scanWords]
        simp only [complete, true_or, ↓reduceIte]
        exact (scanUntil_of_complete count state.accepted
          ((value :: remaining).take (maxDraws - state.draws))
          complete).symm
      · by_cases limit : state.draws = maxDraws
        · simp [scanWords, scanUntil, complete, limit]
        · have drawLt : state.draws < maxDraws := by omega
          have nextDrawsBound : state.draws + 1 ≤ maxDraws := by omega
          rw [scanWords]
          simp only [complete, limit, false_or, ↓reduceIte]
          have budget :
              maxDraws - state.draws =
                Nat.succ (maxDraws - (state.draws + 1)) := by omega
          rw [budget, List.take_succ_cons, scanUntil]
          simp only [complete, ↓reduceIte]
          exact ih
            { state with
                accepted := keepIfNew state.accepted value
                draws := state.draws + 1 }
            nextDrawsBound

theorem scanBlocks_success_accepted_eq_scanUntil_take_flatten
    (count maxDraws : Nat) (state : BlockScanState)
    (blocks : List (List Nat)) (drawsBound : state.draws ≤ maxDraws)
    (success :
      (scanBlocks count maxDraws state blocks).accepted.length = count) :
    (scanBlocks count maxDraws state blocks).accepted =
      scanUntil count state.accepted
        (blocks.flatten.take (maxDraws - state.draws)) := by
  induction blocks generalizing state with
  | nil => simp [scanBlocks, scanUntil]
  | cons block remaining ih =>
      rw [scanBlocks] at success ⊢
      by_cases active : state.draws < maxDraws
      · simp only [if_pos active] at success ⊢
        let bumped : BlockScanState :=
          { state with consumedBlocks := state.consumedBlocks + 1 }
        let scanned := scanWords count maxDraws bumped block
        have bumpedDraws : bumped.draws ≤ maxDraws := by
          simpa [bumped] using drawsBound
        have wordScan := scanWords_accepted_eq_scanUntil_take
          count maxDraws bumped block bumpedDraws
        have scanState :
            scanned.state.accepted =
              scanUntil count state.accepted
                (block.take (maxDraws - state.draws)) := by
          simpa [scanned, bumped] using wordScan
        change (if scanned.stopOuter = true then scanned.state else
            scanBlocks count maxDraws scanned.state remaining).accepted.length =
          count at success
        change (if scanned.stopOuter = true then scanned.state else
            scanBlocks count maxDraws scanned.state remaining).accepted =
          scanUntil count state.accepted
            ((block :: remaining).flatten.take (maxDraws - state.draws))
        by_cases stopped : scanned.stopOuter = true
        · rw [if_pos stopped] at success ⊢
          rw [List.flatten_cons, List.take_append, scanUntil_append]
          rw [← scanState]
          exact (scanUntil_of_complete count scanned.state.accepted
            (remaining.flatten.take
              (maxDraws - state.draws - block.length)) success).symm
        · rw [if_neg stopped] at success ⊢
          have notStopped : scanned.stopOuter = false :=
            Bool.eq_false_of_not_eq_true stopped
          have drawsExact :=
            V5QuerySamplerGeneratedSemantics.scanWords_draws_of_not_stopped
            count maxDraws bumped block notStopped
          have scannedDraws : scanned.state.draws ≤ maxDraws :=
            scanWords_draws_le count maxDraws bumped block bumpedDraws
          have blockBudget : block.length ≤ maxDraws - state.draws := by
            have : scanned.state.draws = state.draws + block.length := by
              simpa [scanned, bumped] using drawsExact
            omega
          have recursive := ih scanned.state scannedDraws success
          calc
            (scanBlocks count maxDraws scanned.state remaining).accepted =
                scanUntil count scanned.state.accepted
                  (remaining.flatten.take
                    (maxDraws - scanned.state.draws)) := recursive
            _ = scanUntil count
                  (scanUntil count state.accepted block)
                  (remaining.flatten.take
                    (maxDraws - state.draws - block.length)) := by
              rw [scanState]
              rw [List.take_of_length_le blockBudget]
              have drawsExact' :
                  scanned.state.draws = state.draws + block.length := by
                simpa [scanned, bumped] using drawsExact
              rw [drawsExact']
              congr 2
              omega
            _ = scanUntil count state.accepted
                  (block ++ remaining.flatten.take
                    (maxDraws - state.draws - block.length)) := by
              rw [scanUntil_append]
            _ = scanUntil count state.accepted
                  ((block ++ remaining.flatten).take
                    (maxDraws - state.draws)) := by
              rw [List.take_append, List.take_of_length_le blockBudget]
      · simp only [if_neg active] at success ⊢
        have drawsExact : state.draws = maxDraws := by omega
        simp [drawsExact, scanUntil]

def sourceTraceDigests (blocks : List SourceSqueezeBlock) : List Digest256 :=
  blocks.map (fun block => nativeSourceDigest (sourceSqueezeBytes block))

/-- Flattening the exact source blocks produces precisely the chronological
masked candidate list consumed by the K1.3 decoder. -/
theorem nativeCandidateBlocks_flatten_eq_trace_words
    (blocks : List SourceSqueezeBlock) :
    (nativeGeneratedCandidateBlocks blocks).flatten =
      (flattenedWords (sourceTraceDigests blocks)).map q16Candidate := by
  simp [nativeGeneratedCandidateBlocks, sourceTraceDigests, flattenedWords,
    List.flatMap, Function.comp_def]

/-- A successful fixed block scan returns exactly `scanQ16` over the same
source digest trace. -/
theorem successful_native_block_scan_eq_scanQ16
    (blocks : List SourceSqueezeBlock)
    (success :
      (scanBlocks 16 64 initialBlockScanState
        (nativeGeneratedCandidateBlocks blocks)).accepted.length = 16) :
    (scanBlocks 16 64 initialBlockScanState
        (nativeGeneratedCandidateBlocks blocks)).accepted =
      (scanQ16 (sourceTraceDigests blocks)).positions := by
  have blockScan :=
    scanBlocks_success_accepted_eq_scanUntil_take_flatten
      16 64 initialBlockScanState (nativeGeneratedCandidateBlocks blocks)
      (by simp [initialBlockScanState]) success
  have flattened := nativeCandidateBlocks_flatten_eq_trace_words blocks
  rw [scanQ16,
    scanUniqueUntil_positions_eq_scanUntil 16 64 _ [] (by simp)]
  simpa [initialBlockScanState, flattened] using blockScan

/-- The literal successful candidate therefore supplies the exact sampled
position equality required by `raw_queries_eq_decoded_schedule`, for the
digest list actually produced by its source squeeze trace. -/
theorem raw_candidate_sampled_eq_trace_scanQ16
    (inputTranscript : Transcript) (sourceCounter : Std.U8)
    (output : Option v7_onefold.V7CompactQuerySchedule)
    (raw : RawCandidateExecution inputTranscript sourceCounter output)
    (squeezeSucceeds : EverySqueezeSucceeds) :
    ∃ blocks : List SourceSqueezeBlock,
      NativeExactSqueezeTrace raw.absorbed blocks raw.sampledTranscript ∧
      raw.sampled.val.map UScalar.val =
        (scanQ16 (sourceTraceDigests blocks)).positions := by
  have model := raw_candidate_has_exact_outer_model inputTranscript
    sourceCounter output raw squeezeSucceeds
  rcases model with
    ⟨blocks, finalDraws, trace, drawsBound, outputBound, modelExact⟩
  have sampledLength : raw.sampled.val.length = 16 := by
    have values := raw_candidate_queries_values_exact inputTranscript
      sourceCounter output raw
    rw [← values]
    simpa using raw.queries.property
  have acceptedExact := congrArg BlockScanState.accepted modelExact
  simp only [generatedBlockScanState_accepted] at acceptedExact
  have success :
      (scanBlocks 16 64 initialBlockScanState
        (nativeGeneratedCandidateBlocks blocks)).accepted.length = 16 := by
    have initialModel :
        generatedBlockScanState initialQ16Output 0#usize 0 =
          initialBlockScanState := by
      simp [generatedBlockScanState, initialBlockScanState,
        initialQ16Output, vecNats, alloc.vec.Vec.with_capacity,
        alloc.vec.Vec.new]
    rw [initialModel] at modelExact acceptedExact
    rw [acceptedExact]
    simpa [vecNats_length] using sampledLength
  refine ⟨blocks, trace, ?_⟩
  have initialModel :
      generatedBlockScanState initialQ16Output 0#usize 0 =
        initialBlockScanState := by
    simp [generatedBlockScanState, initialBlockScanState,
      initialQ16Output, vecNats, alloc.vec.Vec.with_capacity,
      alloc.vec.Vec.new]
  rw [initialModel] at modelExact
  have acceptedExact' := congrArg BlockScanState.accepted modelExact
  simp only [generatedBlockScanState_accepted] at acceptedExact'
  calc
    raw.sampled.val.map UScalar.val = vecNats raw.sampled := rfl
    _ = (scanBlocks 16 64 initialBlockScanState
          (nativeGeneratedCandidateBlocks blocks)).accepted :=
      acceptedExact'.symm
    _ = (scanQ16 (sourceTraceDigests blocks)).positions :=
      successful_native_block_scan_eq_scanQ16 blocks success

#print axioms nativeCandidateBlocks_flatten_eq_trace_words
#print axioms scanBlocks_success_accepted_eq_scanUntil_take_flatten
#print axioms successful_native_block_scan_eq_scanQ16
#print axioms raw_candidate_sampled_eq_trace_scanQ16

end V7FirstCompactSamplerK13PositionBridge
