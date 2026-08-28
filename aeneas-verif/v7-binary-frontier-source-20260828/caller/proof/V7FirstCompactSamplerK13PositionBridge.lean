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
open V7FirstCompactK13RawScheduleBridge
open V7FirstCompactFrontierK13Integration
open AspisV5QuerySamplerControl
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73Q16DeployedDecoderPrefixBridge
open AspisK1.V7Tag73Q16SemanticFrontierBridge

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

theorem drawsUntil_of_complete
    (count : Nat) (seen values : List Nat)
    (complete : seen.length = count) :
    drawsUntil count seen values = 0 := by
  cases values with
  | nil => rfl
  | cons value remaining => simp [drawsUntil, complete]

theorem drawsUntil_append
    (count : Nat) (seen left right : List Nat) :
    drawsUntil count seen (left ++ right) =
      drawsUntil count seen left +
        drawsUntil count (scanUntil count seen left) right := by
  induction left generalizing seen with
  | nil => simp [drawsUntil, scanUntil]
  | cons value remaining ih =>
      simp only [List.cons_append, drawsUntil, scanUntil]
      by_cases complete : seen.length = count
      · simp only [complete, ↓reduceIte, Nat.zero_add]
        exact (drawsUntil_of_complete count seen right complete).symm
      · simp only [complete, ↓reduceIte]
        rw [ih (keepIfNew seen value)]
        omega

theorem keepFirst_eq_keepIfNew (seen : List Nat) (value : Nat) :
    keepFirst seen value = keepIfNew seen value := by
  simp [keepFirst, keepIfNew]

theorem scanUniqueUntil_draws_eq_drawsUntil_take
    (needed fuel : Nat) (words seen : List Nat)
    (seenBound : seen.length ≤ needed) :
    (scanUniqueUntil needed fuel words seen).drawsUsed =
      drawsUntil needed seen
        ((words.take fuel).map q16Candidate) := by
  induction fuel generalizing words seen with
  | zero => simp [scanUniqueUntil, drawsUntil]
  | succ fuel ih =>
      cases words with
      | nil => simp [scanUniqueUntil, drawsUntil]
      | cons word remaining =>
          by_cases complete : seen.length = needed
          · simp [scanUniqueUntil, drawsUntil, complete]
          · have notComplete : ¬ needed ≤ seen.length := by omega
            have nextBound :
                (keepIfNew seen (q16Candidate word)).length ≤ needed := by
              unfold keepIfNew
              split
              · exact seenBound
              · simp only [List.length_append, List.length_singleton]
                omega
            simp only [scanUniqueUntil, notComplete, ↓reduceIte,
              List.take_succ_cons, List.map_cons, drawsUntil, complete]
            rw [keepFirst_eq_keepIfNew,
              ih remaining (keepIfNew seen (q16Candidate word)) nextBound]
            omega

theorem scanUniqueUntil_positions_length_le_seen_add_draws
    (needed fuel : Nat) (words seen : List Nat) :
    (scanUniqueUntil needed fuel words seen).positions.length ≤
      seen.length + (scanUniqueUntil needed fuel words seen).drawsUsed := by
  induction fuel generalizing words seen with
  | zero => simp [scanUniqueUntil]
  | succ fuel ih =>
      cases words with
      | nil => simp [scanUniqueUntil]
      | cons word remaining =>
          by_cases complete : needed ≤ seen.length
          · simp [scanUniqueUntil, complete]
          · have recursive := ih remaining
              (keepFirst seen (q16Candidate word))
            have keepBound :
                (keepFirst seen (q16Candidate word)).length ≤
                  seen.length + 1 := by
              rw [keepFirst_eq_keepIfNew]
              exact keepIfNew_length_le_succ seen (q16Candidate word)
            simp only [scanUniqueUntil, complete, ↓reduceIte]
            omega

theorem q16BlocksNeededForDraws_le_eight
    (draws : Nat) (drawsBound : draws ≤ 64) :
    q16BlocksNeededForDraws draws ≤ 8 := by
  unfold q16BlocksNeededForDraws blocksNeededForWords
  split <;> omega

theorem q16BlocksNeededForDraws_ge_two
    (draws : Nat) (drawsLower : 16 ≤ draws) :
    2 ≤ q16BlocksNeededForDraws draws := by
  unfold q16BlocksNeededForDraws blocksNeededForWords
  split <;> omega

theorem scanWords_draws_eq_drawsUntil_take
    (count maxDraws : Nat) (state : BlockScanState) (words : List Nat)
    (acceptedBound : state.accepted.length ≤ count)
    (drawsBound : state.draws ≤ maxDraws) :
    (scanWords count maxDraws state words).state.draws =
      state.draws + drawsUntil count state.accepted
        (words.take (maxDraws - state.draws)) := by
  induction words generalizing state with
  | nil => simp [scanWords, drawsUntil]
  | cons value remaining ih =>
      by_cases complete : state.accepted.length = count
      · rw [scanWords_when_complete count maxDraws state
          (value :: remaining) complete]
        simp [drawsUntil_of_complete count state.accepted _ complete]
      · by_cases limit : state.draws = maxDraws
        · simp [scanWords, complete, limit, drawsUntil]
        · have nextDrawsBound : state.draws + 1 ≤ maxDraws := by omega
          have nextAcceptedBound :
              (keepIfNew state.accepted value).length ≤ count := by
            unfold keepIfNew
            split
            · exact acceptedBound
            · simp only [List.length_append, List.length_singleton]
              omega
          have budget :
              maxDraws - state.draws =
                Nat.succ (maxDraws - (state.draws + 1)) := by omega
          rw [scanWords]
          rw [if_neg (by simp [complete, limit])]
          rw [budget, List.take_succ_cons, drawsUntil]
          simp only [complete, ↓reduceIte]
          have recursive := ih
            { state with
                accepted := keepIfNew state.accepted value
                draws := state.draws + 1 }
            nextAcceptedBound nextDrawsBound
          dsimp only at recursive
          rw [recursive]
          omega

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

theorem scanBlocks_success_draws_eq_drawsUntil_take_flatten
    (count maxDraws : Nat) (state : BlockScanState)
    (blocks : List (List Nat))
    (acceptedBound : state.accepted.length ≤ count)
    (drawsBound : state.draws ≤ maxDraws)
    (success :
      (scanBlocks count maxDraws state blocks).accepted.length = count) :
    (scanBlocks count maxDraws state blocks).draws =
      state.draws + drawsUntil count state.accepted
        (blocks.flatten.take (maxDraws - state.draws)) := by
  induction blocks generalizing state with
  | nil => simp [scanBlocks, drawsUntil]
  | cons block remaining ih =>
      rw [scanBlocks] at success ⊢
      by_cases active : state.draws < maxDraws
      · simp only [if_pos active] at success ⊢
        let bumped : BlockScanState :=
          { state with consumedBlocks := state.consumedBlocks + 1 }
        let scanned := scanWords count maxDraws bumped block
        have bumpedDraws : bumped.draws ≤ maxDraws := by
          simpa [bumped] using drawsBound
        have wordDraw := scanWords_draws_eq_drawsUntil_take
          count maxDraws bumped block acceptedBound bumpedDraws
        have wordScan := scanWords_accepted_eq_scanUntil_take
          count maxDraws bumped block bumpedDraws
        have scanState :
            scanned.state.accepted =
              scanUntil count state.accepted
                (block.take (maxDraws - state.draws)) := by
          simpa [scanned, bumped] using wordScan
        have scanDraw :
            scanned.state.draws =
              state.draws + drawsUntil count state.accepted
                (block.take (maxDraws - state.draws)) := by
          simpa [scanned, bumped] using wordDraw
        change (if scanned.stopOuter = true then scanned.state else
            scanBlocks count maxDraws scanned.state remaining).accepted.length =
          count at success
        change (if scanned.stopOuter = true then scanned.state else
            scanBlocks count maxDraws scanned.state remaining).draws =
          state.draws + drawsUntil count state.accepted
            ((block :: remaining).flatten.take (maxDraws - state.draws))
        by_cases stopped : scanned.stopOuter = true
        · rw [if_pos stopped] at success ⊢
          rw [List.flatten_cons, List.take_append, drawsUntil_append]
          rw [← scanState]
          rw [drawsUntil_of_complete count scanned.state.accepted _ success]
          simp only [Nat.add_zero]
          exact scanDraw
        · rw [if_neg stopped] at success ⊢
          have notStopped : scanned.stopOuter = false :=
            Bool.eq_false_of_not_eq_true stopped
          have drawsExact :=
            V5QuerySamplerGeneratedSemantics.scanWords_draws_of_not_stopped
              count maxDraws bumped block notStopped
          have scannedDraws : scanned.state.draws ≤ maxDraws :=
            scanWords_draws_le count maxDraws bumped block bumpedDraws
          have scannedAccepted : scanned.state.accepted.length ≤ count :=
            scanWords_accepted_length_le count maxDraws bumped block
              acceptedBound
          have blockBudget : block.length ≤ maxDraws - state.draws := by
            have exactState :
                scanned.state.draws = state.draws + block.length := by
              simpa [scanned, bumped] using drawsExact
            omega
          have exactState :
              scanned.state.draws = state.draws + block.length := by
            simpa [scanned, bumped] using drawsExact
          have blockDraws :
              drawsUntil count state.accepted block = block.length := by
            rw [List.take_of_length_le blockBudget] at scanDraw
            omega
          have recursive := ih scanned.state scannedAccepted scannedDraws success
          calc
            (scanBlocks count maxDraws scanned.state remaining).draws =
                scanned.state.draws +
                  drawsUntil count scanned.state.accepted
                    (remaining.flatten.take
                      (maxDraws - scanned.state.draws)) := recursive
            _ = state.draws + block.length +
                  drawsUntil count
                    (scanUntil count state.accepted block)
                    (remaining.flatten.take
                      (maxDraws - state.draws - block.length)) := by
              rw [exactState, scanState, List.take_of_length_le blockBudget]
              have remainingBudget :
                  maxDraws - (state.draws + block.length) =
                    maxDraws - state.draws - block.length := by omega
              rw [remainingBudget]
            _ = state.draws + drawsUntil count state.accepted
                  (block ++ remaining.flatten.take
                    (maxDraws - state.draws - block.length)) := by
              rw [drawsUntil_append, blockDraws]
              omega
            _ = state.draws + drawsUntil count state.accepted
                  ((block ++ remaining.flatten).take
                    (maxDraws - state.draws)) := by
              rw [List.take_append, List.take_of_length_le blockBudget]
      · simp only [if_neg active] at success ⊢
        have drawsExact : state.draws = maxDraws := by omega
        simp [drawsExact, drawsUntil]

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

/-- The same successful source scan consumes exactly the draw prefix recorded
by the deployed K1.3 decoder, including repeated candidates. -/
theorem successful_native_block_scan_draws_eq_scanQ16
    (blocks : List SourceSqueezeBlock)
    (success :
      (scanBlocks 16 64 initialBlockScanState
        (nativeGeneratedCandidateBlocks blocks)).accepted.length = 16) :
    (scanBlocks 16 64 initialBlockScanState
        (nativeGeneratedCandidateBlocks blocks)).draws =
      (scanQ16 (sourceTraceDigests blocks)).drawsUsed := by
  have blockDraw :=
    scanBlocks_success_draws_eq_drawsUntil_take_flatten
      16 64 initialBlockScanState (nativeGeneratedCandidateBlocks blocks)
      (by simp [initialBlockScanState])
      (by simp [initialBlockScanState]) success
  have decoderDraw :=
    scanUniqueUntil_draws_eq_drawsUntil_take 16 64
      (flattenedWords (sourceTraceDigests blocks)) [] (by simp)
  rw [scanQ16]
  rw [decoderDraw]
  rw [nativeCandidateBlocks_flatten_eq_trace_words] at blockDraw
  simpa [initialBlockScanState] using blockDraw

/-- The literal successful candidate therefore supplies the exact sampled
position equality required by `raw_queries_eq_decoded_schedule`, for the
digest list actually produced by its source squeeze trace. -/
theorem raw_candidate_sampled_eq_trace_scanQ16
    (inputTranscript : Transcript) (sourceCounter : Std.U8)
    (output : Option v7_onefold.V7CompactQuerySchedule)
    (raw : RawCandidateExecution inputTranscript sourceCounter output)
    (hashSucceeds :
      V7FirstCompactSqueezeSourceBridge.HashCallbackAlwaysSucceeds
        raw.absorbed.hash) :
    ∃ blocks : List SourceSqueezeBlock,
      NativeExactSqueezeTrace raw.absorbed blocks raw.sampledTranscript ∧
      raw.sampled.val.map UScalar.val =
        (scanQ16 (sourceTraceDigests blocks)).positions := by
  have model := raw_candidate_has_exact_outer_model inputTranscript
    sourceCounter output raw hashSucceeds
  rcases model with
    ⟨blocks, finalDraws, trace, drawsBound, outputBound, blocksExact,
      modelExact⟩
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

/-- Literal translated candidate success constructs the complete deployed
K1.3 schedule certificate.  The returned Rust array is therefore the exact
array serialized by the decoder, with no assumed evaluator result. -/
theorem raw_candidate_constructs_exact_decoded_schedule
    (inputTranscript : Transcript) (sourceCounter : Std.U8)
    (output : Option v7_onefold.V7CompactQuerySchedule)
    (raw : RawCandidateExecution inputTranscript sourceCounter output)
    (hashSucceeds :
      V7FirstCompactSqueezeSourceBridge.HashCallbackAlwaysSucceeds
        raw.absorbed.hash)
    (counter : Fin 64) :
    ∃ (blocks : List SourceSqueezeBlock) (schedule : QuerySchedule),
      NativeExactSqueezeTrace raw.absorbed blocks raw.sampledTranscript ∧
      decodeCandidateOutcome counter (sourceTraceDigests blocks) =
        some (.schedule schedule) ∧
      raw.queries = queryScheduleArray schedule := by
  have model := raw_candidate_has_exact_outer_model inputTranscript
    sourceCounter output raw hashSucceeds
  rcases model with
    ⟨blocks, finalDraws, trace, drawsBound, outputBound, blocksExact,
      modelExact⟩
  have sampledLength : raw.sampled.val.length = 16 := by
    have values := raw_candidate_queries_values_exact inputTranscript
      sourceCounter output raw
    rw [← values]
    simpa using raw.queries.property
  have initialModel :
      generatedBlockScanState initialQ16Output 0#usize 0 =
        initialBlockScanState := by
    simp [generatedBlockScanState, initialBlockScanState,
      initialQ16Output, vecNats, alloc.vec.Vec.with_capacity,
      alloc.vec.Vec.new]
  rw [initialModel] at modelExact
  have acceptedExact := congrArg BlockScanState.accepted modelExact
  simp only [generatedBlockScanState_accepted] at acceptedExact
  have success :
      (scanBlocks 16 64 initialBlockScanState
        (nativeGeneratedCandidateBlocks blocks)).accepted.length = 16 := by
    rw [acceptedExact]
    simpa [vecNats_length] using sampledLength
  let digests := sourceTraceDigests blocks
  have positionsExact : (scanQ16 digests).positions.length = 16 := by
    have positions := successful_native_block_scan_eq_scanQ16 blocks success
    simpa [digests] using (congrArg List.length positions).symm.trans success
  have modelDraw := congrArg BlockScanState.draws modelExact
  simp only [generatedBlockScanState_draws] at modelDraw
  have sourceDraw := successful_native_block_scan_draws_eq_scanQ16
    blocks success
  have finalDrawExact : finalDraws.val = (scanQ16 digests).drawsUsed := by
    rw [← sourceDraw]
    simpa [digests] using modelDraw.symm
  have exactUse :
      blocks.length = q16BlocksNeededForDraws (scanQ16 digests).drawsUsed := by
    have sourceExact := blocksExact rfl
    simpa [finalDrawExact] using sourceExact
  have blockCap : blocks.length ≤ 8 := by
    rw [exactUse]
    exact q16BlocksNeededForDraws_le_eight _ (scanQ16_draw_cap digests)
  have positionsLeDraws :
      (scanQ16 digests).positions.length ≤
        (scanQ16 digests).drawsUsed := by
    unfold scanQ16
    simpa using scanUniqueUntil_positions_length_le_seen_add_draws
      16 64 (flattenedWords digests) []
  have drawLower : 16 ≤ (scanQ16 digests).drawsUsed := by omega
  have atLeastTwo : 2 ≤ blocks.length := by
    rw [exactUse]
    exact q16BlocksNeededForDraws_ge_two _ drawLower
  have digestsLength : digests.length = blocks.length := by
    simp [digests, sourceTraceDigests]
  have digestExactUse :
      digests.length = q16BlocksNeededForDraws (scanQ16 digests).drawsUsed :=
    digestsLength.trans exactUse
  have digestBlockCap : digests.length ≤ 8 := by omega
  have digestAtLeastTwo : 2 ≤ digests.length := by omega
  have neededBlockCap :
      q16BlocksNeededForDraws (scanQ16 digests).drawsUsed ≤ 8 :=
    q16BlocksNeededForDraws_le_eight _ (scanQ16_draw_cap digests)
  have neededAtLeastTwo :
      2 ≤ q16BlocksNeededForDraws (scanQ16 digests).drawsUsed :=
    q16BlocksNeededForDraws_ge_two _ drawLower
  let schedule : QuerySchedule :=
    { positions := positionsEmbedding (scanQ16 digests).positions
        positionsExact (scanQ16_positions_nodup digests)
        (scanQ16_positions_bounded digests)
      blocksUsed := digests.length
      atLeastTwoBlocks := digestAtLeastTwo
      withinSixtyFourDraws := digestBlockCap }
  have decoded :
      decodeCandidateOutcome counter digests = some (.schedule schedule) := by
    simp [decodeCandidateOutcome, decodeCandidateDetailed, blockCap,
      positionsExact, digestExactUse, digestAtLeastTwo, digestBlockCap,
      neededBlockCap, neededAtLeastTwo, schedule]
  have sampledValues :
      raw.sampled.val.map UScalar.val = (scanQ16 digests).positions := by
    calc
      raw.sampled.val.map UScalar.val = vecNats raw.sampled := rfl
      _ = (scanBlocks 16 64 initialBlockScanState
            (nativeGeneratedCandidateBlocks blocks)).accepted :=
        acceptedExact.symm
      _ = (scanQ16 digests).positions := by
        simpa [digests] using
          successful_native_block_scan_eq_scanQ16 blocks success
  refine ⟨blocks, schedule, trace, ?_, ?_⟩
  · simpa [digests] using decoded
  · exact raw_queries_eq_decoded_schedule inputTranscript sourceCounter
      output raw counter digests schedule decoded sampledValues

/-- Candidate-level caller closure with no assumed raw-array/schedule
equality.  Literal translated success constructs the decoded schedule and
therefore fixes the translated frontier to the semantic recurrence. -/
theorem candidate_success_constructs_exact_decoded_frontier
    (inputTranscript : Transcript) (sourceCounter : Std.U8)
    (output : Option v7_onefold.V7CompactQuerySchedule)
    (success :
      v7_onefold.derive_v7_compact_candidate inputTranscript sourceCounter =
        .ok (.Ok output))
    (counterBound : sourceCounter.val < 64)
    (hashSucceeds :
      V7FirstCompactSqueezeSourceBridge.HashCallbackAlwaysSucceeds
        (candidate_success_exposes_raw_execution inputTranscript sourceCounter
          output success).absorbed.hash) :
    let raw := candidate_success_exposes_raw_execution inputTranscript
      sourceCounter output success
    ∃ (blocks : List SourceSqueezeBlock) (schedule : QuerySchedule),
      NativeExactSqueezeTrace raw.absorbed blocks raw.sampledTranscript ∧
      decodeCandidateOutcome ⟨sourceCounter.val, counterBound⟩
          (sourceTraceDigests blocks) = some (.schedule schedule) ∧
      raw.queries = queryScheduleArray schedule ∧
      raw.frontier.val = semanticFrontierNodes schedule.positions := by
  let raw := candidate_success_exposes_raw_execution inputTranscript
    sourceCounter output success
  obtain ⟨blocks, schedule, trace, decoded, queriesExact⟩ :=
    raw_candidate_constructs_exact_decoded_schedule inputTranscript
      sourceCounter output raw hashSucceeds ⟨sourceCounter.val, counterBound⟩
  have frontierExact := raw_candidate_frontier_matches_semantic
    inputTranscript sourceCounter output raw schedule queriesExact
  exact ⟨blocks, schedule, trace, decoded, queriesExact, frontierExact⟩

#print axioms nativeCandidateBlocks_flatten_eq_trace_words
#print axioms scanBlocks_success_accepted_eq_scanUntil_take_flatten
#print axioms successful_native_block_scan_eq_scanQ16
#print axioms successful_native_block_scan_draws_eq_scanQ16
#print axioms raw_candidate_sampled_eq_trace_scanQ16
#print axioms raw_candidate_constructs_exact_decoded_schedule
#print axioms candidate_success_constructs_exact_decoded_frontier

end V7FirstCompactSamplerK13PositionBridge
