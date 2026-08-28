import V7FirstCompactSamplerOuterBodyBridge
import V7FirstCompactSqueezeSourceBridge

open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace V7FirstCompactSamplerOuterLoopBridge

open V7FirstCompactSamplerLoop16Bridge
open V7FirstCompactSamplerNativeBlockBridge
open V7FirstCompactSamplerOuterBodyBridge
open AspisV5QuerySamplerControl
open AspisK1.V7Tag73SamplerDecoder

inductive NativeExactSqueezeTrace :
    Transcript → List SourceSqueezeBlock → Transcript → Prop
  | nil (self : Transcript) : NativeExactSqueezeTrace self [] self
  | cons (self next final : Transcript) (block : SourceSqueezeBlock)
      (blocks : List SourceSqueezeBlock)
      (head :
        V7FirstCompactSource.transcript.Transcript.squeeze_block self =
          .ok (block, next))
      (tail : NativeExactSqueezeTrace next blocks final) :
      NativeExactSqueezeTrace self (block :: blocks) final

def nativeGeneratedCandidateBlocks
    (blocks : List SourceSqueezeBlock) : List (List Nat) :=
  blocks.map (fun block =>
    (blockWords (nativeSourceDigest (sourceSqueezeBytes block))).map q16Candidate)

@[simp] theorem nativeGeneratedCandidateBlocks_nil :
    nativeGeneratedCandidateBlocks [] = [] := rfl

@[simp] theorem nativeGeneratedCandidateBlocks_cons
    (block : SourceSqueezeBlock) (blocks : List SourceSqueezeBlock) :
    nativeGeneratedCandidateBlocks (block :: blocks) =
      (blockWords (nativeSourceDigest (sourceSqueezeBytes block))).map q16Candidate ::
        nativeGeneratedCandidateBlocks blocks := rfl

@[simp] theorem nativeGeneratedCandidateBlocks_append
    (left right : List SourceSqueezeBlock) :
    nativeGeneratedCandidateBlocks (left ++ right) =
      nativeGeneratedCandidateBlocks left ++
        nativeGeneratedCandidateBlocks right := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.cons_append, nativeGeneratedCandidateBlocks_cons, ih,
        List.cons_append]

theorem nativeExactSqueezeTrace_append_one
    {initial current next : Transcript}
    {blocks : List SourceSqueezeBlock} {block : SourceSqueezeBlock}
    (htrace : NativeExactSqueezeTrace initial blocks current)
    (hsqueeze :
      V7FirstCompactSource.transcript.Transcript.squeeze_block current =
        .ok (block, next)) :
    NativeExactSqueezeTrace initial (blocks ++ [block]) next := by
  induction htrace generalizing next block with
  | nil traceSelf =>
      simpa using NativeExactSqueezeTrace.cons traceSelf next next block []
        hsqueeze (NativeExactSqueezeTrace.nil next)
  | cons self middle final headBlock priorBlocks head tail ih =>
      rw [List.cons_append]
      exact NativeExactSqueezeTrace.cons self middle next headBlock
        (priorBlocks ++ [block]) head (ih hsqueeze)

theorem scanWords_draws_mono
    (count maxDraws : Nat) (state : BlockScanState) (words : List Nat) :
    state.draws ≤ (scanWords count maxDraws state words).state.draws := by
  induction words generalizing state with
  | nil => rfl
  | cons value remaining ih =>
      rw [scanWords]
      split
      · rfl
      · have next := ih
          { state with
              accepted := keepIfNew state.accepted value
              draws := state.draws + 1 }
        dsimp only at next
        omega

theorem scanWords_draws_lt_add_length_of_stopped
    (count maxDraws : Nat) (state : BlockScanState) (words : List Nat)
    (stopped : (scanWords count maxDraws state words).stopOuter = true) :
    (scanWords count maxDraws state words).state.draws <
      state.draws + words.length := by
  induction words generalizing state with
  | nil => simp [scanWords] at stopped
  | cons value remaining ih =>
      by_cases hstop :
          state.accepted.length = count || state.draws = maxDraws
      · rw [scanWords, if_pos hstop] at stopped ⊢
        simp
      · rw [scanWords, if_neg hstop] at stopped ⊢
        have bound := ih
          { state with
              accepted := keepIfNew state.accepted value
              draws := state.draws + 1 } stopped
        dsimp only at bound
        simp only [List.length_cons]
        omega

def OuterSamplerInvariant
    (initialSelf : Transcript) (initialOut : alloc.vec.Vec Std.U32)
    (initialDraws : Std.Usize) (initialConsumedBlocks : Nat)
    (current : Transcript × alloc.vec.Vec Std.U32 × Std.Usize) : Prop :=
  current.1.hash = initialSelf.hash ∧
    current.2.1.val.length ≤ 16 ∧ current.2.2.val ≤ 64 ∧
    ∃ blocks : List SourceSqueezeBlock,
      NativeExactSqueezeTrace initialSelf blocks current.1 ∧
      current.2.2.val = initialDraws.val + 8 * blocks.length ∧
      ∀ suffix : List (List Nat),
        scanBlocks 16 64
            (generatedBlockScanState initialOut initialDraws
              initialConsumedBlocks)
            (nativeGeneratedCandidateBlocks blocks ++ suffix) =
          scanBlocks 16 64
            (generatedBlockScanState current.2.1 current.2.2
              (initialConsumedBlocks + blocks.length)) suffix

def OuterSamplerPost
    (initialSelf : Transcript) (initialOut : alloc.vec.Vec Std.U32)
    (initialDraws : Std.Usize) (initialConsumedBlocks : Nat)
    (result : Transcript × alloc.vec.Vec Std.U32) : Prop :=
  ∃ (blocks : List SourceSqueezeBlock) (finalDraws : Std.Usize),
    NativeExactSqueezeTrace initialSelf blocks result.1 ∧
    finalDraws.val ≤ 64 ∧ result.2.val.length ≤ 16 ∧
    (initialDraws.val = 0 →
      blocks.length = q16BlocksNeededForDraws finalDraws.val) ∧
    scanBlocks 16 64
        (generatedBlockScanState initialOut initialDraws initialConsumedBlocks)
        (nativeGeneratedCandidateBlocks blocks) =
      generatedBlockScanState result.2 finalDraws
        (initialConsumedBlocks + blocks.length)

/-- Normalize one active translated outer-loop body before entering WP.  Doing
this through the already proved stable native body keeps Aeneas' dependent
slice-length witness out of the postcondition elaboration. -/
theorem active_outer_body_is_normalized
    (self next : Transcript) (out : alloc.vec.Vec Std.U32)
    (draws : Std.Usize) (block : SourceSqueezeBlock)
    (hactive : draws < q16MaxDraws)
    (hsqueeze :
      V7FirstCompactSource.transcript.Transcript.squeeze_block self =
        .ok (block, next)) :
    V7FirstCompactSource.transcript.Transcript.challenge_queries_without_replacement_loop0.body
        q16Count q16MaxDraws q16Mask self out draws =
      (do
        let (nextOut, nextDraws, marker) ←
          V7FirstCompactSource.transcript.Transcript.challenge_queries_without_replacement_loop0_loop0
            (nativeBlockChunks (sourceSqueezeBytes block))
            q16Count q16MaxDraws q16Mask out draws
        match marker with
        | 1#uscalar => .ok (.cont (next, nextOut, nextDraws))
        | _ => .ok (.done (next, nextOut))) := by
  rw [current_outer_body_eq_native]
  unfold nativeQ16OuterBody q16OuterContinuation
  rw [if_pos hactive, hsqueeze]
  rfl

/-! The translated outer loop consumes exactly the successful squeeze blocks
recorded in `NativeExactSqueezeTrace` and implements the fixed K1.3
`scanBlocks`.
Every continuation consumes all eight chronological words from one block. -/
theorem generated_outer_loop_matches_scanBlocks
    (self : Transcript) (out : alloc.vec.Vec Std.U32)
    (draws : Std.Usize) (consumedBlocks : Nat)
    (hashSucceeds :
      V7FirstCompactSqueezeSourceBridge.HashCallbackAlwaysSucceeds self.hash)
    (hout : out.val.length ≤ 16) (hdraws : draws.val ≤ 64) :
    V7FirstCompactSource.transcript.Transcript.challenge_queries_without_replacement_loop0
        self q16Count q16MaxDraws q16Mask out draws
      ⦃ result => OuterSamplerPost self out draws consumedBlocks result ⦄ := by
  simp only [V7FirstCompactSource.transcript.Transcript.challenge_queries_without_replacement_loop0]
  apply loop.spec_decr_nat
    (fun state : Transcript × alloc.vec.Vec Std.U32 × Std.Usize =>
      64 - state.2.2.val)
    (OuterSamplerInvariant self out draws consumedBlocks)
    (OuterSamplerPost self out draws consumedBlocks)
  · rintro ⟨currentSelf, currentOut, currentDraws⟩ hinvariant
    rcases hinvariant with
      ⟨hcurrentHash, hcurrentOut, hcurrentDraws, blocks, htrace,
        hdrawAccounting, happend⟩
    dsimp only at hcurrentOut hcurrentDraws hdrawAccounting happend ⊢
    by_cases hactive : currentDraws.val < 64
    · have hactiveScalar : currentDraws < q16MaxDraws := by
        simpa [q16MaxDraws] using hactive
      have currentHashSucceeds :
          V7FirstCompactSqueezeSourceBridge.HashCallbackAlwaysSucceeds
            currentSelf.hash := by
        rw [hcurrentHash]
        exact hashSucceeds
      obtain ⟨block, nextSelf, hsqueeze⟩ :=
        V7FirstCompactSqueezeSourceBridge.hash_callback_total_implies_squeeze_success
          currentSelf
          currentHashSucceeds
      have hnextHash : nextSelf.hash = self.hash :=
        (V7FirstCompactSqueezeSourceBridge.successful_squeeze_preserves_hash
          currentSelf nextSelf block hsqueeze).trans
          hcurrentHash
      rw [active_outer_body_is_normalized currentSelf nextSelf currentOut
        currentDraws block hactiveScalar hsqueeze]
      have hinner := generated_inner_loop_matches_scanWords
        (nativeBlockChunks (sourceSqueezeBytes block))
        currentOut currentDraws (consumedBlocks + blocks.length + 1)
        (native_validWordIterator_blockChunks (sourceSqueezeBytes block))
        hcurrentOut hcurrentDraws
      obtain ⟨innerResult, hinnerRun, hinnerPost⟩ :=
        Aeneas.Std.WP.spec_imp_exists hinner
      rcases innerResult with ⟨nextOut, nextDraws, marker⟩
      rw [hinnerRun]
      simp only [bind_tc_ok]
      let bumped : BlockScanState :=
        generatedBlockScanState currentOut currentDraws
          (consumedBlocks + blocks.length + 1)
      let scanned : WordScanResult :=
        scanWords 16 64 bumped
          ((blockWords (nativeSourceDigest (sourceSqueezeBytes block))).map q16Candidate)
      have hinnerState :
          generatedBlockScanState nextOut nextDraws
              (consumedBlocks + blocks.length + 1) = scanned.state := by
        exact hinnerPost.1.trans (by
          simp only [scanned, bumped]
          rw [native_iteratorCandidates_blockChunks])
      have hmarker : marker.val = wordScanMarker scanned := by
        simpa only [scanned, bumped, native_iteratorCandidates_blockChunks] using
          hinnerPost.2
      have hnextOut : nextOut.val.length ≤ 16 := by
        have hmodel := scanWords_accepted_length_le 16 64 bumped
              ((blockWords (nativeSourceDigest (sourceSqueezeBytes block))).map q16Candidate) (by
                simpa [bumped] using hcurrentOut)
        have haccepted := congrArg
          (fun state : BlockScanState => state.accepted.length) hinnerState
        simp only [generatedBlockScanState_accepted] at haccepted
        rw [← vecNats_length nextOut]
        rw [haccepted]
        exact hmodel
      have hnextDrawsLe : nextDraws.val ≤ 64 := by
        have hmodel := scanWords_draws_le 16 64 bumped
          ((blockWords (nativeSourceDigest (sourceSqueezeBytes block))).map q16Candidate)
          (by simpa [bumped] using hcurrentDraws)
        have hdrawEq := congrArg BlockScanState.draws hinnerState
        simp only [generatedBlockScanState_draws] at hdrawEq
        rw [hdrawEq]
        exact hmodel
      by_cases hcontinue : marker = 1#u32
      · subst marker
        simp_scalar
        have hnotStopped : scanned.stopOuter = false := by
          cases hstop : scanned.stopOuter <;>
            simp [wordScanMarker, hstop] at hmarker ⊢
        have hnextDraws : nextDraws.val = currentDraws.val + 8 := by
          have hmodel :=
            V5QuerySamplerGeneratedSemantics.scanWords_draws_of_not_stopped
              16 64 bumped
                ((blockWords (nativeSourceDigest (sourceSqueezeBytes block))).map q16Candidate)
                hnotStopped
          calc
            nextDraws.val = scanned.state.draws := by
              simpa [generatedBlockScanState] using
                congrArg BlockScanState.draws hinnerState
            _ = bumped.draws +
                ((blockWords (nativeSourceDigest (sourceSqueezeBytes block))).map q16Candidate).length :=
              hmodel
            _ = currentDraws.val + 8 := by
              simp [bumped, blockWords]
        let nextBlocks := blocks ++ [block]
        have hnextTrace : NativeExactSqueezeTrace self nextBlocks nextSelf := by
          exact nativeExactSqueezeTrace_append_one htrace hsqueeze
        refine ⟨⟨hnextHash, hnextOut, hnextDrawsLe, nextBlocks, hnextTrace,
          ?_, ?_⟩, ?_⟩
        · simp only [nextBlocks, List.length_append, List.length_singleton]
          omega
        · intro suffix
          have hold := happend
            ((blockWords (nativeSourceDigest (sourceSqueezeBytes block))).map q16Candidate :: suffix)
          simp only [nextBlocks, nativeGeneratedCandidateBlocks_append,
            nativeGeneratedCandidateBlocks_cons,
            nativeGeneratedCandidateBlocks_nil,
            List.append_nil, List.append_assoc, List.singleton_append]
          rw [hold]
          rw [scanBlocks]
          simp only [generatedBlockScanState_draws, if_pos hactive]
          change (if scanned.stopOuter = true then scanned.state else
            scanBlocks 16 64 scanned.state suffix) = _
          simp only [hnotStopped, Bool.false_eq_true, ↓reduceIte]
          rw [← hinnerState]
          simpa [nextBlocks, generatedBlockScanState, Nat.add_assoc]
        · rw [hnextDraws]
          omega
      · have hstopped : scanned.stopOuter = true := by
          cases hstop : scanned.stopOuter
          · exfalso
            apply hcontinue
            apply UScalar.eq_of_val_eq
            simpa [wordScanMarker, hstop] using hmarker
          · rfl
        have hzero : marker = 0#u32 := by
          apply UScalar.eq_of_val_eq
          simpa [wordScanMarker, hstopped] using hmarker
        subst marker
        simp_scalar
        let finalBlocks := blocks ++ [block]
        refine ⟨finalBlocks, nextDraws,
          nativeExactSqueezeTrace_append_one htrace hsqueeze,
          hnextDrawsLe, hnextOut, ?_, ?_⟩
        · intro initialZero
          have currentExact : currentDraws.val = 8 * blocks.length := by
            omega
          have nextMono : currentDraws.val ≤ nextDraws.val := by
            have mono := scanWords_draws_mono 16 64 bumped
              ((blockWords
                (nativeSourceDigest (sourceSqueezeBytes block))).map
                  q16Candidate)
            rw [← hinnerState] at mono
            simpa [bumped, generatedBlockScanState] using mono
          have nextStrict : nextDraws.val < currentDraws.val + 8 := by
            have strict := scanWords_draws_lt_add_length_of_stopped 16 64
              bumped
              ((blockWords
                (nativeSourceDigest (sourceSqueezeBytes block))).map
                  q16Candidate) hstopped
            rw [← hinnerState] at strict
            simpa [bumped, generatedBlockScanState, blockWords] using strict
          simp only [finalBlocks, List.length_append, List.length_singleton]
          unfold q16BlocksNeededForDraws blocksNeededForWords
          split
          · omega
          · omega
        · have hold := happend
            [(blockWords
              (nativeSourceDigest (sourceSqueezeBytes block))).map q16Candidate]
          simp only [finalBlocks, nativeGeneratedCandidateBlocks_append,
            nativeGeneratedCandidateBlocks_cons,
            nativeGeneratedCandidateBlocks_nil,
            List.append_nil, List.append_assoc, List.singleton_append]
          rw [hold]
          rw [scanBlocks]
          simp only [generatedBlockScanState_draws, if_pos hactive]
          change (if scanned.stopOuter = true then scanned.state else
            scanBlocks 16 64 scanned.state []) = _
          simp only [hstopped, ↓reduceIte]
          rw [← hinnerState]
          simpa [finalBlocks, generatedBlockScanState, Nat.add_assoc]
    · have hdrawsEq : currentDraws.val = 64 := by omega
      have hinactiveScalar : ¬ currentDraws < q16MaxDraws := by
        simpa [q16MaxDraws] using hactive
      unfold V7FirstCompactSource.transcript.Transcript.challenge_queries_without_replacement_loop0.body
      rw [if_neg hinactiveScalar]
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨blocks, currentDraws, htrace, hcurrentDraws,
        hcurrentOut, ?_, ?_⟩
      · intro initialZero
        have currentExact : currentDraws.val = 8 * blocks.length := by
          omega
        have currentCap : currentDraws.val = 64 := by omega
        rw [currentCap]
        norm_num [q16BlocksNeededForDraws, blocksNeededForWords]
        omega
      · have hold := happend []
        simpa [scanBlocks] using hold
  · refine ⟨rfl, hout, hdraws, [], NativeExactSqueezeTrace.nil self, ?_, ?_⟩
    · simp
    · intro suffix
      rfl

#print axioms generated_outer_loop_matches_scanBlocks

end V7FirstCompactSamplerOuterLoopBridge
