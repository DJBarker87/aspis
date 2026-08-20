import V5QuerySamplerGeneratedSemantics

/-! The fixed `(18, 2^17, 64)` wrapper and its successful-output theorem. -/

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace V5QuerySamplerFixedCall

open V5TranscriptPrimitivesGenerated
open V5TranscriptPrimitivesProof
open V5QuerySamplerGeneratedSemantics
open AspisV5TranscriptConnection
open AspisV5QuerySamplerControl

theorem scanUntil_of_complete
    (count : Nat) (seen values : List Nat)
    (hcomplete : seen.length = count) :
    scanUntil count seen values = seen := by
  cases values with
  | nil => rfl
  | cons head tail => simp [scanUntil, hcomplete]

theorem scanUntil_append
    (count : Nat) (seen left right : List Nat) :
    scanUntil count seen (left ++ right) =
      scanUntil count (scanUntil count seen left) right := by
  induction left generalizing seen with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.cons_append, scanUntil]
      by_cases hcomplete : seen.length = count
      · simp only [hcomplete, ↓reduceIte]
        exact (scanUntil_of_complete count seen right hcomplete).symm
      · simp only [hcomplete, ↓reduceIte]
        exact ih (keepIfNew seen head)

/-- The word-level state used by `scanBlocks` has exactly the same accepted
prefix as `scanUntil`, with the remaining draw budget applied before the
input words are examined. -/
theorem scanWords_accepted_eq_scanUntil_take
    (count maxDraws : Nat) (state : BlockScanState) (words : List Nat)
    (hdraws : state.draws ≤ maxDraws) :
    (scanWords count maxDraws state words).state.accepted =
      scanUntil count state.accepted
        (words.take (maxDraws - state.draws)) := by
  induction words generalizing state with
  | nil => simp [scanWords, scanUntil]
  | cons value remaining ih =>
      by_cases hcomplete : state.accepted.length = count
      · rw [scanWords]
        simp only [hcomplete, true_or, ↓reduceIte]
        exact (scanUntil_of_complete count state.accepted
          ((value :: remaining).take (maxDraws - state.draws))
          hcomplete).symm
      · by_cases hlimit : state.draws = maxDraws
        · simp [scanWords, scanUntil, hcomplete, hlimit]
        · have hdrawLt : state.draws < maxDraws := by omega
          have hnextDraws : state.draws + 1 ≤ maxDraws := by omega
          rw [scanWords]
          simp only [hcomplete, hlimit, false_or, ↓reduceIte]
          have hbudget :
              maxDraws - state.draws =
                Nat.succ (maxDraws - (state.draws + 1)) := by omega
          rw [hbudget, List.take_succ_cons, scanUntil]
          simp only [hcomplete, ↓reduceIte]
          exact ih
            { state with
                accepted := keepIfNew state.accepted value
                draws := state.draws + 1 }
            hnextDraws

/-- On a successful run, whole-block control returns the same first eighteen
distinct values as a flat 64-candidate scan.  Detection-only bytes after the
eighteenth accepted value cannot change the result. -/
theorem scanBlocks_success_accepted_eq_scanUntil_take_flatten
    (count maxDraws : Nat) (state : BlockScanState)
    (blocks : List (List Nat)) (hdraws : state.draws ≤ maxDraws)
    (hsuccess :
      (scanBlocks count maxDraws state blocks).accepted.length = count) :
    (scanBlocks count maxDraws state blocks).accepted =
      scanUntil count state.accepted
        (blocks.flatten.take (maxDraws - state.draws)) := by
  induction blocks generalizing state with
  | nil => simp [scanBlocks, scanUntil]
  | cons block remaining ih =>
      rw [scanBlocks] at hsuccess ⊢
      by_cases hactive : state.draws < maxDraws
      · simp only [if_pos hactive] at hsuccess ⊢
        let bumped : BlockScanState :=
          { state with consumedBlocks := state.consumedBlocks + 1 }
        let scanned := scanWords count maxDraws bumped block
        have hbumpedDraws : bumped.draws ≤ maxDraws := by
          simpa [bumped] using hdraws
        have hscan := scanWords_accepted_eq_scanUntil_take
          count maxDraws bumped block hbumpedDraws
        have hscanState :
            scanned.state.accepted =
              scanUntil count state.accepted
                (block.take (maxDraws - state.draws)) := by
          simpa [scanned, bumped] using hscan
        change (if scanned.stopOuter = true then scanned.state else
            scanBlocks count maxDraws scanned.state remaining).accepted.length =
          count at hsuccess
        change (if scanned.stopOuter = true then scanned.state else
            scanBlocks count maxDraws scanned.state remaining).accepted =
          scanUntil count state.accepted
            ((block :: remaining).flatten.take
              (maxDraws - state.draws))
        by_cases hstop : scanned.stopOuter = true
        · rw [if_pos hstop] at hsuccess ⊢
          rw [List.flatten_cons, List.take_append, scanUntil_append]
          rw [← hscanState]
          exact (scanUntil_of_complete count scanned.state.accepted
            (remaining.flatten.take
              (maxDraws - state.draws - block.length)) hsuccess).symm
        · rw [if_neg hstop] at hsuccess ⊢
          have hnotStopped : scanned.stopOuter = false := by
            exact Bool.eq_false_of_not_eq_true hstop
          have hdrawExact := scanWords_draws_of_not_stopped
            count maxDraws bumped block hnotStopped
          have hscannedDraws : scanned.state.draws ≤ maxDraws := by
            exact scanWords_draws_le count maxDraws bumped block hbumpedDraws
          have hblockBudget : block.length ≤ maxDraws - state.draws := by
            have : scanned.state.draws = state.draws + block.length := by
              simpa [scanned, bumped] using hdrawExact
            omega
          have ihResult := ih scanned.state hscannedDraws hsuccess
          calc
            (scanBlocks count maxDraws scanned.state remaining).accepted =
                scanUntil count scanned.state.accepted
                  (remaining.flatten.take
                    (maxDraws - scanned.state.draws)) := ihResult
            _ = scanUntil count
                  (scanUntil count state.accepted block)
                  (remaining.flatten.take
                    (maxDraws - state.draws - block.length)) := by
              rw [hscanState]
              rw [List.take_of_length_le hblockBudget]
              have hdrawExact' :
                  scanned.state.draws = state.draws + block.length := by
                simpa [scanned, bumped] using hdrawExact
              rw [hdrawExact']
              congr 2
              omega
            _ = scanUntil count state.accepted
                  (block ++ remaining.flatten.take
                    (maxDraws - state.draws - block.length)) := by
              rw [scanUntil_append]
            _ = scanUntil count state.accepted
                  ((block ++ remaining.flatten).take
                    (maxDraws - state.draws)) := by
              rw [List.take_append, List.take_of_length_le hblockBudget]
      · simp only [if_neg hactive] at hsuccess ⊢
        have hdrawEq : state.draws = maxDraws := by omega
        simp [hdrawEq, scanUntil]

theorem generatedCandidateBlocks_flatten
    (blocks : List QueryBlock) :
    (generatedCandidateBlocks blocks).flatten =
      (blocks.map arrayDigest).flatMap blockQueryCandidates := by
  simp [generatedCandidateBlocks, List.flatMap, Function.comp_def]

theorem successful_block_model_returns_derive18Queries
    (blocks : List QueryBlock)
    (hsuccess :
      (scanBlocks 18 64 initialBlockScanState
        (generatedCandidateBlocks blocks)).accepted.length = 18) :
    derive18Queries (blocks.map arrayDigest) =
      some (scanBlocks 18 64 initialBlockScanState
        (generatedCandidateBlocks blocks)).accepted := by
  let final := scanBlocks 18 64 initialBlockScanState
    (generatedCandidateBlocks blocks)
  have haccepted :=
    scanBlocks_success_accepted_eq_scanUntil_take_flatten
      18 64 initialBlockScanState (generatedCandidateBlocks blocks)
      (by simp [initialBlockScanState]) hsuccess
  have hbudget :
      deployedCandidateBudget (blocks.map arrayDigest) =
        (generatedCandidateBlocks blocks).flatten.take 64 := by
    simp only [deployedCandidateBudget, generatedCandidateBlocks_flatten]
  rw [← scanDeployedQueries_eq_derive18Queries]
  unfold scanDeployedQueries
  rw [hbudget]
  change (if (scanUntil 18 []
      ((generatedCandidateBlocks blocks).flatten.take 64)).length = 18
    then some (scanUntil 18 []
      ((generatedCandidateBlocks blocks).flatten.take 64)) else none) = _
  have haccepted' :
      final.accepted = scanUntil 18 []
        ((generatedCandidateBlocks blocks).flatten.take 64) := by
    simpa [final, initialBlockScanState] using haccepted
  rw [← haccepted']
  simp [final, hsuccess]

def fixedInitialOut : alloc.vec.Vec Std.U32 :=
  alloc.vec.Vec.with_capacity Std.U32 18#usize

@[simp] theorem fixedInitialOut_values : fixedInitialOut.val = [] := rfl

theorem fixed_bound_is_power_of_two :
    core.num.U32.is_power_of_two 131072#u32 = .ok true := by
  have hpower : Nat.isPowerOfTwo 131072 := ⟨17, by norm_num⟩
  simp [core.num.U32.is_power_of_two, hpower]

theorem fixed_bound_cast :
    lift (UScalar.cast .Usize 131072#u32) = .ok 131072#usize := by
  have hspec := UScalar.cast_inBounds_spec .Usize 131072#u32 (by scalar_tac)
  obtain ⟨value, heq, hval⟩ := Aeneas.Std.WP.spec_imp_exists hspec
  have hvalue : value = 131072#usize := by
    apply UScalar.eq_of_val_eq
    simpa using hval
  simpa [hvalue] using heq

theorem fixed_query_mask :
    lift (Std.U32.wrapping_sub 131072#u32 1#u32) = .ok 131071#u32 := by
  simp only [lift]
  congr 1

/-- Successful execution of the generated fixed production call returns the
maintained `derive18Queries` result and changes transcript state by exactly
the squeeze blocks in `ExactSqueezeTrace`. -/
theorem generated_fixed_call_success_is_exact
    (self finalSelf : Transcript) (queries : alloc.vec.Vec Std.U32)
    (hsuccess :
      V5TranscriptPrimitivesGenerated.aspis_core.transcript.Transcript.challenge_queries_without_replacement
          self 18#usize 131072#u32 64#usize =
        .ok (.Ok queries, finalSelf)) :
    ∃ (blocks : List QueryBlock) (finalDraws : Std.Usize),
      ExactSqueezeTrace self blocks finalSelf ∧
      derive18Queries (blocks.map arrayDigest) = some (vecNats queries) ∧
      finalDraws.val ≤ 64 ∧
      scanBlocks 18 64 initialBlockScanState
          (generatedCandidateBlocks blocks) =
        generatedBlockScanState queries finalDraws blocks.length := by
  have houter := generated_outer_loop_matches_scanBlocks
    self fixedInitialOut 0#usize 0
      (by simp [fixedInitialOut, alloc.vec.Vec.with_capacity, alloc.vec.Vec.new])
      (by scalar_tac)
  obtain ⟨outerResult, houterRun, houterPost⟩ :=
    Aeneas.Std.WP.spec_imp_exists houter
  rcases outerResult with ⟨outerSelf, outerOut⟩
  unfold V5TranscriptPrimitivesGenerated.aspis_core.transcript.Transcript.challenge_queries_without_replacement at hsuccess
  rw [fixed_bound_is_power_of_two] at hsuccess
  simp only [bind_tc_ok, if_pos (by decide : true = true)] at hsuccess
  rw [fixed_bound_cast] at hsuccess
  simp only [bind_tc_ok] at hsuccess
  have hcountBound : ¬ (131072#usize : Std.Usize) < 18#usize := by scalar_tac
  rw [if_neg hcountBound] at hsuccess
  have hcountNonzero : (18#usize : Std.Usize) ≠ 0#usize := by scalar_tac
  rw [if_neg hcountNonzero] at hsuccess
  rw [fixed_query_mask] at hsuccess
  simp only [bind_tc_ok] at hsuccess
  change (do
      let outer ←
        V5TranscriptPrimitivesGenerated.aspis_core.transcript.Transcript.challenge_queries_without_replacement_loop0
          self 18#usize 64#usize 131071#u32 fixedInitialOut 0#usize
      if alloc.vec.Vec.len outer.2 = 18#usize then
        .ok (core.result.Result.Ok outer.2, outer.1)
      else
        .ok (core.result.Result.Err
          (V5TranscriptPrimitivesGenerated.aspis_core.transcript.QuerySampleError.DrawLimitExhausted
            (alloc.vec.Vec.len outer.2) 64#usize),
          outer.1)) = .ok (core.result.Result.Ok queries, finalSelf) at hsuccess
  rw [houterRun] at hsuccess
  simp only [bind_tc_ok] at hsuccess
  by_cases hlength : outerOut.val.length = 18
  · have hlenScalar : alloc.vec.Vec.len outerOut = 18#usize := by
      apply UScalar.eq_of_val_eq
      simpa using hlength
    simp only [hlenScalar, ↓reduceIte, Result.ok.injEq, Prod.mk.injEq] at hsuccess
    rcases hsuccess with ⟨hqueries, hfinal⟩
    have hqueriesEq : outerOut = queries := by simpa using hqueries
    clear hqueries
    subst queries
    subst finalSelf
    rcases houterPost with
      ⟨blocks, finalDraws, htrace, hdraws, houtLength, hmodel⟩
    have hmodel' :
        scanBlocks 18 64 initialBlockScanState
            (generatedCandidateBlocks blocks) =
          generatedBlockScanState outerOut finalDraws blocks.length := by
      simpa [initialBlockScanState, fixedInitialOut, fixedInitialOut_values,
        alloc.vec.Vec.with_capacity, alloc.vec.Vec.new,
        generatedBlockScanState, vecNats] using hmodel
    refine ⟨blocks, finalDraws, htrace, ?_, hdraws, ?_⟩
    · have hmodelLength :
          (scanBlocks 18 64 initialBlockScanState
            (generatedCandidateBlocks blocks)).accepted.length = 18 := by
          rw [hmodel']
          simpa [generatedBlockScanState, vecNats_length] using hlength
      have hreturn :=
        successful_block_model_returns_derive18Queries blocks hmodelLength
      have haccepted := congrArg BlockScanState.accepted hmodel'
      simp only [generatedBlockScanState_accepted] at haccepted
      rwa [haccepted] at hreturn
    · exact hmodel'
  · have hlenScalar : alloc.vec.Vec.len outerOut ≠ 18#usize := by
      intro heq
      apply hlength
      have := congrArg UScalar.val heq
      simpa using this
    simp [hlenScalar] at hsuccess

#print axioms scanWords_accepted_eq_scanUntil_take
#print axioms scanBlocks_success_accepted_eq_scanUntil_take_flatten
#print axioms successful_block_model_returns_derive18Queries
#print axioms generated_fixed_call_success_is_exact

end V5QuerySamplerFixedCall
