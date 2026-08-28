import V7BinaryFrontierSortModel
import V7FirstCompactFrontierLoopBridge

/-!
# Translated insertion-sort source bridge

This file connects the literal Aeneas translation of production's inner
insertion loop to the pure `bubbleLeft` model.  The saved key remains outside
the translated shift loop; placing it at the returned cursor yields exactly
the adjacent-swap model.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open V7FirstCompactSource

set_option autoImplicit false

namespace V7FirstCompactFrontierSortSourceBridge

open V7BinaryFrontierSortModel

private theorem array_index_run
    {T : Type} [Inhabited T] {count : Std.Usize}
    (values : Array T count) (index : Std.Usize)
    (bound : index.val < values.val.length) :
    Array.index_usize values index = .ok values.val[index.val]! := by
  obtain ⟨output, run, outputExact⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index bound)
  have bangExact : output = values.val[index.val]! := by
    rw [outputExact]
    symm
    apply List.getElem!_of_getElem?
    simp [bound]
  simpa [bangExact] using run

private theorem array_update_run
    {T : Type} {count : Std.Usize}
    (values : Array T count) (index : Std.Usize) (value : T)
    (bound : index.val < values.val.length) :
    Array.update values index value = .ok (values.set index value) := by
  obtain ⟨output, run, outputExact⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.update_spec values index value bound)
  simpa [outputExact] using run

def placedValues {Q : Std.Usize} (queries : Array Std.U32 Q)
    (cursor : Std.Usize) (value : Std.U32) : List Std.U32 :=
  (queries.set cursor value).val

private theorem placedValues_length
    {Q : Std.Usize} (queries : Array Std.U32 Q)
    (cursor : Std.Usize) (value : Std.U32) :
    (placedValues queries cursor value).length = queries.val.length := by
  simp [placedValues]

private theorem placedValues_at_cursor
    {Q : Std.Usize} (queries : Array Std.U32 Q)
    (cursor : Std.Usize) (value : Std.U32)
    (bound : cursor.val < queries.val.length) :
    (placedValues queries cursor value)[cursor.val]! = value := by
  unfold placedValues
  rw [Array.set_val_eq]
  apply List.getElem!_of_getElem?
  rw [List.getElem?_set_self bound]

private theorem placedValues_before_cursor
    {Q : Std.Usize} (queries : Array Std.U32 Q)
    (cursor : Std.Usize) (value : Std.U32)
    (positive : 0 < cursor.val)
    (bound : cursor.val < queries.val.length) :
    (placedValues queries cursor value)[cursor.val - 1]! =
      queries.val[cursor.val - 1]! := by
  unfold placedValues
  rw [Array.set_val_eq]
  apply List.getElem!_of_getElem?
  rw [List.getElem?_set_ne (by omega)]
  have previousBound : cursor.val - 1 < queries.val.length := by omega
  rw [List.getElem?_eq_getElem previousBound]
  congr 1
  symm
  apply List.getElem!_of_getElem?
  exact List.getElem?_eq_getElem previousBound

private theorem shifted_then_placed_eq_swap
    {Q : Std.Usize} (queries : Array Std.U32 Q)
    (cursor previous : Std.Usize) (value predecessor : Std.U32)
    (positive : 0 < cursor.val)
    (cursorBound : cursor.val < queries.val.length)
    (previousExact : previous.val = cursor.val - 1)
    (predecessorExact : predecessor = queries.val[cursor.val - 1]!) :
    placedValues (queries.set cursor predecessor) previous value =
      swapWithPrevious (placedValues queries cursor value) cursor.val := by
  unfold placedValues swapWithPrevious
  simp only [Array.set_val_eq]
  rw [previousExact, predecessorExact]
  have previousBound : cursor.val - 1 < queries.val.length := by omega
  have different : cursor.val ≠ cursor.val - 1 := by omega
  have readPrevious :
      (queries.val.set cursor.val value)[cursor.val - 1]! =
        queries.val[cursor.val - 1]! := by
    apply List.getElem!_of_getElem?
    rw [List.getElem?_set_ne different]
    have exactRead := List.getElem?_eq_getElem previousBound
    rw [exactRead]
    congr 1
    symm
    apply List.getElem!_of_getElem?
    exact exactRead
  have readCursor :
      (queries.val.set cursor.val value)[cursor.val]! = value := by
    apply List.getElem!_of_getElem?
    rw [List.getElem?_set_self cursorBound]
  rw [readPrevious, readCursor, List.set_set]

/-- Literal translated inner-loop success with the saved key written at its
returned cursor is exactly the pure adjacent-swap insertion model. -/
theorem translated_inner_insertion_exact
    {Q : Std.Usize} (queries : Array Std.U32 Q) (value : Std.U32)
    (cursor : Std.Usize) (cursorBound : cursor.val < queries.val.length) :
    v6_onefold.binary_frontier_nodes_loop0_loop0 queries value cursor
      ⦃ output =>
        output.2.val < output.1.val.length ∧
        placedValues output.1 output.2 value =
          bubbleLeft (placedValues queries cursor value) cursor.val ⦄ := by
  simp only [v6_onefold.binary_frontier_nodes_loop0_loop0]
  apply loop.spec_decr_nat
    (fun state : Array Std.U32 Q × Std.Usize => state.2.val)
    (fun state =>
      state.2.val < state.1.val.length ∧
      bubbleLeft (placedValues state.1 state.2 value) state.2.val =
        bubbleLeft (placedValues queries cursor value) cursor.val)
    (fun output : Array Std.U32 Q × Std.Usize =>
      output.2.val < output.1.val.length ∧
      placedValues output.1 output.2 value =
        bubbleLeft (placedValues queries cursor value) cursor.val)
  · rintro ⟨current, position⟩ ⟨positionBound, model⟩
    change position.val < current.val.length at positionBound
    change bubbleLeft (placedValues current position value) position.val =
      bubbleLeft (placedValues queries cursor value) cursor.val at model
    unfold v6_onefold.binary_frontier_nodes_loop0_loop0.body
    simp only [Prod.fst, Prod.snd]
    by_cases positive : 0 < position.val
    · have positiveScalar : position > 0#usize := by scalar_tac
      rw [if_pos positiveScalar]
      cases subtractRun : position - 1#usize with
      | fail error =>
          have facts := UScalar.sub_equiv position 1#usize
          rw [subtractRun] at facts
          norm_num at facts
          exact False.elim (by omega)
      | div =>
          have facts := UScalar.sub_equiv position 1#usize
          rw [subtractRun] at facts
          norm_num at facts
      | ok previous =>
          have facts := UScalar.sub_equiv position 1#usize
          rw [subtractRun] at facts
          norm_num at facts
          rcases facts with ⟨_, exactSum, _⟩
          have previousExact : previous.val = position.val - 1 := by
            omega
          have previousBound : previous.val < current.val.length := by omega
          simp only [bind_tc_ok]
          have readRun := array_index_run current previous previousBound
          rw [readRun]
          simp only [bind_tc_ok]
          let predecessor := current.val[previous.val]!
          by_cases less : value < predecessor
          · rw [if_pos less]
            have updateRun := array_update_run current position predecessor
              positionBound
            rw [updateRun]
            simp only [bind_tc_ok, WP.spec, WP.theta]
            have predecessorExact :
                predecessor = current.val[position.val - 1]! := by
              simp only [predecessor, previousExact]
            have nextModel :
                bubbleLeft
                    (placedValues (current.set position predecessor) previous value)
                    previous.val =
                  bubbleLeft (placedValues queries cursor value) cursor.val := by
              rw [shifted_then_placed_eq_swap current position previous value
                predecessor positive positionBound previousExact
                predecessorExact]
              have active :
                  position.val <
                    (placedValues current position value).length := by
                rw [placedValues_length]
                exact positionBound
              have positionRead :
                  (placedValues current position value)[position.val]! = value :=
                placedValues_at_cursor current position value positionBound
              have previousRead :
                  (placedValues current position value)[position.val - 1]! =
                    predecessor := by
                rw [placedValues_before_cursor current position value positive
                  positionBound, predecessorExact]
              have positionSucc : position.val = previous.val + 1 := by omega
              have positionRead' :
                  (placedValues current position value)[previous.val + 1]! =
                    value := by
                simpa only [← positionSucc] using positionRead
              have previousRead' :
                  (placedValues current position value)[previous.val]! =
                    predecessor := by
                have previousIndex : position.val - 1 = previous.val := by omega
                simpa only [previousIndex] using previousRead
              rw [positionSucc, bubbleLeft, if_pos (by omega)] at model
              rw [positionRead', previousRead', if_pos less] at model
              simpa only [positionSucc] using model
            refine ⟨⟨?_, nextModel⟩, ?_⟩
            · rw [Array.set_val_eq, List.length_set]
              exact previousBound
            · change previous.val < position.val
              omega
          · rw [if_neg less]
            simp only [WP.spec, WP.theta, WP.wp_return]
            have active :
                position.val <
                  (placedValues current position value).length := by
              rw [placedValues_length]
              exact positionBound
            have positionRead :
                (placedValues current position value)[position.val]! = value :=
              placedValues_at_cursor current position value positionBound
            have previousRead :
                (placedValues current position value)[position.val - 1]! =
                  predecessor := by
              rw [placedValues_before_cursor current position value positive
                positionBound]
              simp only [predecessor, previousExact]
            have positionSucc : position.val = previous.val + 1 := by omega
            have positionRead' :
                (placedValues current position value)[previous.val + 1]! =
                  value := by
              simpa only [← positionSucc] using positionRead
            have previousRead' :
                (placedValues current position value)[previous.val]! =
                  predecessor := by
              have previousIndex : position.val - 1 = previous.val := by omega
              simpa only [previousIndex] using previousRead
            rw [positionSucc, bubbleLeft, if_pos (by omega)] at model
            rw [positionRead', previousRead', if_neg less] at model
            exact ⟨positionBound, model⟩
    · have zero : position.val = 0 := by omega
      have notPositive : ¬ position > 0#usize := by scalar_tac
      rw [if_neg notPositive]
      simp only [WP.spec, WP.theta, WP.wp_return]
      exact ⟨positionBound, by simpa only [zero, bubbleLeft] using model⟩
  · exact ⟨cursorBound, rfl⟩

private theorem placedValues_original_at_saved_key
    {Q : Std.Usize} (queries : Array Std.U32 Q) (cursor : Std.Usize)
    (bound : cursor.val < queries.val.length) :
    placedValues queries cursor queries.val[cursor.val]! = queries.val := by
  unfold placedValues
  rw [Array.set_val_eq]
  have bangExact :
      queries.val[cursor.val]! = queries.val[cursor.val]'bound := by
    apply List.getElem!_of_getElem?
    exact List.getElem?_eq_getElem bound
  rw [bangExact, List.set_getElem_self bound]

structure OuterSortInvariant {Q : Std.Usize} (original : List Std.U32)
    (state : core.ops.range.Range Std.Usize × Array Std.U32 Q) : Prop where
  endLength : state.1.end.val = state.2.val.length
  startEnd : state.1.start.val ≤ state.1.end.val
  currentPerm : state.2.val.Perm original
  currentPrefix :
    (state.2.val.take state.1.start.val).Pairwise (· ≤ ·)

structure OuterSortPost {Q : Std.Usize} (original : List Std.U32)
    (output : Array Std.U32 Q) : Prop where
  sorted : output.val.Pairwise (· ≤ ·)
  perm : output.val.Perm original

/-- The complete translated production insertion-sort loop preserves the
input multiset and returns it in nondecreasing order. -/
theorem translated_outer_insertion_sort_exact
    {Q : Std.Usize} (original : List Std.U32)
    (iter : core.ops.range.Range Std.Usize) (queries : Array Std.U32 Q)
    (invariant : OuterSortInvariant original (iter, queries)) :
    v6_onefold.binary_frontier_nodes_loop0 iter queries
      ⦃ output => OuterSortPost original output ⦄ := by
  simp only [v6_onefold.binary_frontier_nodes_loop0]
  apply loop.spec_decr_nat
    (fun state : core.ops.range.Range Std.Usize × Array Std.U32 Q =>
      state.1.end.val - state.1.start.val)
    (OuterSortInvariant original)
    (OuterSortPost original)
  · rintro ⟨currentIter, current⟩ currentInvariant
    change OuterSortInvariant original (currentIter, current) at currentInvariant
    rcases currentInvariant with
      ⟨endLength, startEnd, currentPerm, currentPrefix⟩
    simp only [Prod.fst, Prod.snd] at endLength startEnd currentPerm currentPrefix
    simp only [Prod.fst, Prod.snd]
    by_cases active : currentIter.start.val < currentIter.end.val
    · obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextStart,
          nextEnd⟩ := WP.spec_imp_exists
        (core.iter.range.IteratorRange.next_Usize_some_spec currentIter active)
      rw [optionExact] at nextRun
      have indexBound : currentIter.start.val < current.val.length := by
        rw [← endLength]
        exact active
      have readRun := array_index_run current currentIter.start indexBound
      let saved := current.val[currentIter.start.val]!
      have readRunSaved :
          Array.index_usize current currentIter.start = .ok saved := by
        simpa only [saved] using readRun
      obtain ⟨⟨innerQueries, innerCursor⟩, innerRun, innerPost⟩ :=
        WP.spec_imp_exists
        (translated_inner_insertion_exact current saved currentIter.start
          indexBound)
      obtain ⟨nextQueries, updateRun, updateExact⟩ := WP.spec_imp_exists
        (Array.update_spec innerQueries innerCursor saved innerPost.1)
      have stepRun :
          v6_onefold.binary_frontier_nodes_loop0.body currentIter current =
            .ok (.cont (nextIter, nextQueries)) := by
        unfold v6_onefold.binary_frontier_nodes_loop0.body
        simp [nextRun, readRunSaved, innerRun, updateRun]
      rw [stepRun]
      simp only [WP.spec, WP.theta, WP.wp_return]
      change OuterSortInvariant original (nextIter, nextQueries) ∧
        nextIter.end.val - nextIter.start.val <
          currentIter.end.val - currentIter.start.val
      have savedExact : saved = current.val[currentIter.start.val]! := rfl
      have initialPlaced :
          placedValues current currentIter.start saved = current.val := by
        simpa only [savedExact] using
          placedValues_original_at_saved_key current currentIter.start indexBound
      have nextValues :
          nextQueries.val = bubbleLeft current.val currentIter.start.val := by
        have updateValue :
            nextQueries.val =
              placedValues innerQueries innerCursor saved := by
          rw [updateExact]
          rfl
        rw [updateValue, innerPost.2, initialPlaced]
      have nextSorted :
          (nextQueries.val.take (currentIter.start.val + 1)).Pairwise
            (· ≤ ·) := by
        rw [nextValues]
        exact bubbleLeft_sorted_prefix current.val currentIter.start.val
          indexBound currentPrefix
      have nextPermCurrent : nextQueries.val.Perm current.val := by
        rw [nextValues]
        exact bubbleLeft_perm current.val currentIter.start.val indexBound
          currentPrefix
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · have nextEndVal := congrArg (fun value : Std.Usize => value.val)
          nextEnd
        rw [nextEndVal, endLength]
        exact current.property.trans nextQueries.property.symm
      · have nextStartVal := nextStart
        have nextEndVal := congrArg (fun value : Std.Usize => value.val)
          nextEnd
        change nextIter.start.val ≤ nextIter.end.val
        omega
      · exact nextPermCurrent.trans currentPerm
      · have nextStartVal := nextStart
        simpa only [nextStartVal] using nextSorted
      · have nextStartVal := nextStart
        have nextEndVal := congrArg (fun value : Std.Usize => value.val)
          nextEnd
        change nextIter.end.val - nextIter.start.val <
          currentIter.end.val - currentIter.start.val
        omega
    · obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextExact⟩ :=
        WP.spec_imp_exists
          (core.iter.range.IteratorRange.next_Usize_none_spec currentIter
            (by omega))
      rw [optionExact, nextExact] at nextRun
      have stepRun :
          v6_onefold.binary_frontier_nodes_loop0.body currentIter current =
            .ok (.done current) := by
        unfold v6_onefold.binary_frontier_nodes_loop0.body
        simp [nextRun]
      rw [stepRun]
      simp only [WP.spec, WP.theta, WP.wp_return]
      change OuterSortPost original current
      constructor
      · have startLength : currentIter.start.val = current.val.length := by
          calc
            currentIter.start.val = currentIter.end.val := by omega
            _ = current.val.length := endLength
        simpa only [startLength, List.take_length] using currentPrefix
      · exact currentPerm
  · exact invariant

/-- Production's `1..Q` sort entry point returns a sorted permutation for
every nonempty fixed-size query array. -/
theorem translated_sort_from_one
    {Q : Std.Usize} (queries : Array Std.U32 Q) (positive : 0 < Q.val) :
    ∃ output : Array Std.U32 Q,
      v6_onefold.binary_frontier_nodes_loop0
          { start := 1#usize, «end» := Q } queries = .ok output ∧
      OuterSortPost queries.val output := by
  have initialPrefix :
      (queries.val.take (1#usize).val).Pairwise (· ≤ ·) := by
    cases queries.val <;> simp
  have initialInvariant : OuterSortInvariant queries.val
      ({ start := 1#usize, «end» := Q }, queries) := by
    refine ⟨?_, ?_, List.Perm.refl _, initialPrefix⟩
    · exact queries.property.symm
    · change (1#usize).val ≤ Q.val
      have oneValue : (1#usize).val = 1 := rfl
      rw [oneValue]
      omega
  exact WP.spec_imp_exists
    (translated_outer_insertion_sort_exact queries.val
      { start := 1#usize, «end» := Q } queries initialInvariant)

private theorem nodup_pairwise_val_ne (values : List Std.U32)
    (nodup : values.Nodup) :
    values.Pairwise (fun left right => left.val ≠ right.val) := by
  rw [List.pairwise_iff_getElem]
  intro left right leftBound rightBound leftRight valueEqual
  have elementEqual : values[left] = values[right] :=
    UScalar.eq_of_val_eq valueEqual
  have indexEqual : left = right := nodup.getElem_inj_iff.mp elementEqual
  omega

/-- A sorted permutation of a duplicate-free input has exactly the
pairwise-distinct property consumed by the translated validation loop. -/
theorem sorted_output_pairwise_distinct
    {Q : Std.Usize} (input output : Array Std.U32 Q)
    (inputNodup : input.val.Nodup)
    (permutation : output.val.Perm input.val) :
    output.val.Pairwise (fun left right => left.val ≠ right.val) := by
  apply nodup_pairwise_val_ne output.val
  exact permutation.nodup_iff.mpr inputNodup

theorem sorted_output_preserves_bound
    {Q : Std.Usize} (input output : Array Std.U32 Q) (limit : Nat)
    (inputBound : ∀ value ∈ input.val, value.val < limit)
    (permutation : output.val.Perm input.val) :
    ∀ value ∈ output.val, value.val < limit := by
  intro value member
  exact inputBound value (permutation.mem_iff.mp member)

private theorem u32_xor_log2_le_31 (left right : Std.U32) :
    Nat.log2 (Nat.xor left.val right.val) ≤ 31 := by
  by_cases xorZero : Nat.xor left.val right.val = 0
  · rw [xorZero]
    exact Nat.zero_le _
  · have xorLt : Nat.xor left.val right.val < 2 ^ 32 := by
      apply Nat.xor_lt_two_pow
      · simpa using left.hBounds
      · simpa using right.hBounds
    have logLt : Nat.log2 (Nat.xor left.val right.val) < 32 :=
      (Nat.log2_lt xorZero).2 xorLt
    omega

theorem adjacentXorLogSum_le_length (values : List Std.U32) :
    V7FirstCompactFrontierLoopBridge.adjacentXorLogSum values ≤
      31 * (values.length - 1) := by
  induction values with
  | nil => simp [V7FirstCompactFrontierLoopBridge.adjacentXorLogSum]
  | cons left tail ih =>
      cases tail with
      | nil => simp [V7FirstCompactFrontierLoopBridge.adjacentXorLogSum]
      | cons right rest =>
          have headBound := u32_xor_log2_le_31 left right
          simp only [V7FirstCompactFrontierLoopBridge.adjacentXorLogSum,
            List.length_cons] at ih ⊢
          omega

private theorem usize_max_gt_512 : 512 < Std.Usize.max := by
  rw [Std.Usize.max, Std.Usize.numBits, UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with bits | bits <;>
    rw [bits] <;> norm_num

private theorem q16_leaf_count_exists :
    ∃ leafCount : Std.U32,
      core.num.U32.checked_shl 1#u32
          (core.convert.num.FromU32U8.from 18#u8) =
        .ok (some leafCount) ∧
      leafCount.val = 2 ^ 18 := by
  let depth := core.convert.num.FromU32U8.from 18#u8
  have depthValue : depth.val = 18 := by simp [depth]
  obtain ⟨shifted, shiftRun, shiftSpec⟩ := WP.spec_imp_exists
    (Std.U32.ShiftLeft_spec 1#u32 depth (by omega))
  have shiftedValue : shifted.val = 2 ^ 18 := by
    rw [shiftSpec.1, depthValue, Std.U32.size, Std.U32.numBits,
      UScalarTy.U32_numBits_eq]
    norm_num [Nat.shiftLeft_eq]
  have checkedRun :
      core.num.U32.checked_shl 1#u32 depth = .ok (some shifted) := by
    unfold core.num.U32.checked_shl
    rw [if_pos (by omega)]
    congr 2
    apply Std.U32.bv_eq_imp_eq
    exact shiftSpec.2.symm
  exact ⟨shifted, checkedRun, shiftedValue⟩

private theorem q16_depth_to_usize :
    core.convert.num.FromUsizeU8.from 18#u8 = 18#usize := by
  apply UScalar.eq_of_val_eq
  rw [core.convert.num.FromUsizeU8.from_val_eq]
  rfl

private theorem q16_expanded_start_run :
    (18#usize : Std.Usize) + 1#usize =
      (.ok 19#usize : Result Std.Usize) := by
  obtain ⟨output, run, outputValue⟩ := WP.spec_imp_exists
    (Std.Usize.add_spec (x := 18#usize) (y := 1#usize) (by
      have room := usize_max_gt_512
      norm_num at room ⊢
      omega))
  have outputExact : output = 19#usize := by
    apply UScalar.eq_of_val_eq
    norm_num at outputValue ⊢
    exact outputValue
  simpa only [outputExact] using run

structure DuplicateScanInvariant {Q : Std.Usize}
    (queries : Array Std.U32 Q)
    (iter : core.ops.range.Range Std.Usize) : Prop where
  startPositive : 1 ≤ iter.start.val
  endLength : iter.end.val = queries.val.length
  startEnd : iter.start.val ≤ iter.end.val

/-- On a pairwise-distinct array, the literal translated adjacent-duplicate
scan completes normally and returns no pending error. -/
theorem translated_duplicate_scan_accepts
    {Q : Std.Usize} (queries : Array Std.U32 Q)
    (iter : core.ops.range.Range Std.Usize)
    (distinct : queries.val.Pairwise
      (fun left right => left.val ≠ right.val))
    (invariant : DuplicateScanInvariant queries iter) :
    v6_onefold.binary_frontier_nodes_loop1 iter queries
      ⦃ output => output = none ⦄ := by
  simp only [v6_onefold.binary_frontier_nodes_loop1]
  apply loop.spec_decr_nat
    (fun state : core.ops.range.Range Std.Usize =>
      state.end.val - state.start.val)
    (DuplicateScanInvariant queries)
    (fun output : Option
      (core.result.Result Std.Usize v6_onefold.V6WireError) => output = none)
  · intro currentIter currentInvariant
    rcases currentInvariant with
      ⟨startPositive, endLength, startEnd⟩
    by_cases active : currentIter.start.val < currentIter.end.val
    · obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextStart,
          nextEnd⟩ := WP.spec_imp_exists
        (core.iter.range.IteratorRange.next_Usize_some_spec currentIter active)
      rw [optionExact] at nextRun
      obtain ⟨previous, previousRun, previousExact⟩ := WP.spec_imp_exists
        (Std.Usize.sub_spec (x := currentIter.start) (y := 1#usize) (by
          simpa using startPositive))
      have previousValue : previous.val = currentIter.start.val - 1 :=
        previousExact.1
      have currentBound : currentIter.start.val < queries.val.length := by
        rw [← endLength]
        exact active
      have previousBound : previous.val < queries.val.length := by
        omega
      have previousRead := array_index_run queries previous previousBound
      have currentRead := array_index_run queries currentIter.start currentBound
      have relation := (List.pairwise_iff_getElem.mp distinct)
        previous.val currentIter.start.val previousBound currentBound (by omega)
      have stepRun :
          v6_onefold.binary_frontier_nodes_loop1.body queries currentIter =
            .ok (.cont nextIter) := by
        unfold v6_onefold.binary_frontier_nodes_loop1.body
        simp [nextRun, previousRun, previousRead, currentRead]
        rw [List.getElem?_eq_getElem previousBound,
          List.getElem?_eq_getElem currentBound]
        exact relation
      rw [stepRun]
      simp only [WP.spec, WP.theta, WP.wp_return]
      constructor
      · refine ⟨?_, ?_, ?_⟩
        · omega
        · have nextEndValue := congrArg
            (fun value : Std.Usize => value.val) nextEnd
          omega
        · have nextStartValue := nextStart
          have nextEndValue := congrArg
            (fun value : Std.Usize => value.val) nextEnd
          change nextIter.start.val ≤ nextIter.end.val
          omega
      · have nextEndValue := congrArg
          (fun value : Std.Usize => value.val) nextEnd
        have nextStartValue := nextStart
        change nextIter.end.val - nextIter.start.val <
          currentIter.end.val - currentIter.start.val
        omega
    · obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextExact⟩ :=
        WP.spec_imp_exists
          (core.iter.range.IteratorRange.next_Usize_none_spec currentIter
            (by omega))
      rw [optionExact, nextExact] at nextRun
      have stepRun :
          v6_onefold.binary_frontier_nodes_loop1.body queries currentIter =
            .ok (.done none) := by
        unfold v6_onefold.binary_frontier_nodes_loop1.body
        simp [nextRun]
      rw [stepRun]
      simp only [WP.spec, WP.theta, WP.wp_return]
  · exact invariant

/-- End-to-end source theorem for the deployed q16/depth-18 frontier helper.
It starts at the literal translated production function and returns the exact
sorted adjacent-XOR formula, with range and duplicate rejection discharged
from the decoder's native q16 invariants. -/
theorem translated_binary_frontier_q16_exact
    (queries : Array Std.U32 16#usize)
    (nodup : queries.val.Nodup)
    (bounded : ∀ value ∈ queries.val, value.val < 2 ^ 18) :
    ∃ sorted : Array Std.U32 16#usize, ∃ output : Std.Usize,
      v6_onefold.binary_frontier_nodes queries 18#u8 =
        .ok (.Ok output) ∧
      OuterSortPost queries.val sorted ∧
      output.val = 19 +
        V7FirstCompactFrontierLoopBridge.adjacentXorLogSum sorted.val - 16 := by
  have qValue : (16#usize).val = 16 := rfl
  have qPositive : 0 < (16#usize).val := by rw [qValue]; omega
  obtain ⟨sorted, sortRun, sortPost⟩ :=
    translated_sort_from_one queries qPositive
  have sortedDistinct := sorted_output_pairwise_distinct queries sorted nodup
    sortPost.perm
  have sortedBound := sorted_output_preserves_bound queries sorted (2 ^ 18)
    bounded sortPost.perm
  have duplicateInvariant : DuplicateScanInvariant sorted
      { start := 1#usize, «end» := 16#usize } := by
    refine ⟨?_, ?_, ?_⟩
    · norm_num
    · change (16#usize).val = sorted.val.length
      exact sorted.property.symm
    · norm_num
  obtain ⟨pending, duplicateRun, pendingExact⟩ := WP.spec_imp_exists
    (translated_duplicate_scan_accepts sorted
      { start := 1#usize, «end» := 16#usize }
      sortedDistinct duplicateInvariant)
  subst pending
  obtain ⟨leafCount, leafRun, leafValue⟩ := q16_leaf_count_exists
  obtain ⟨lastIndex, lastIndexRun, lastIndexSpec⟩ := WP.spec_imp_exists
    (Std.Usize.sub_spec (x := 16#usize) (y := 1#usize) (by norm_num))
  have lastIndexValue : lastIndex.val = 15 := by
    have exactValue := lastIndexSpec.1
    norm_num at exactValue ⊢
    exact exactValue
  have lastIndexBound : lastIndex.val < sorted.val.length := by
    rw [lastIndexValue, sorted.property, qValue]
    omega
  obtain ⟨lastValue, lastReadRun, lastReadExact⟩ := WP.spec_imp_exists
    (Array.index_usize_spec sorted lastIndex lastIndexBound)
  have lastMember : lastValue ∈ sorted.val := by
    rw [lastReadExact]
    exact List.getElem_mem lastIndexBound
  have lastBelowLeaf : lastValue.val < leafCount.val := by
    rw [leafValue]
    exact sortedBound lastValue lastMember
  have expandedStartRun :
      (core.convert.num.FromUsizeU8.from 18#u8) + 1#usize =
        (.ok 19#usize : Result Std.Usize) := by
    rw [q16_depth_to_usize]
    exact q16_expanded_start_run
  let sortedSlice : Slice Std.U32 := Array.to_slice sorted
  let iterator : core.slice.iter.Windows Std.U32 :=
    { slice := sortedSlice, width := 2#usize, index := 0 }
  have windowsRun :
      core.slice.Slice.windows sortedSlice 2#usize = .ok iterator := by
    have widthNonzero : (2#usize : Std.Usize) ≠ 0#usize := by
      intro equality
      have valueEquality := congrArg
        (fun value : Std.Usize => value.val) equality
      norm_num at valueEquality
    simp [core.slice.Slice.windows, widthNonzero, iterator]
  have iteratorWidth : iterator.width.val = 2 := by rfl
  have iteratorRemaining :
      iterator.slice.val.drop iterator.index = sorted.val := by
    simp [iterator, sortedSlice, Array.to_slice]
  have sumBound := adjacentXorLogSum_le_length sorted.val
  have sortedLength : sorted.val.length = 16 := by
    rw [sorted.property, qValue]
  have loopHeadroom :
      (19#usize).val +
          V7FirstCompactFrontierLoopBridge.adjacentXorLogSum sorted.val ≤
        Std.Usize.max := by
    have maxRoom := usize_max_gt_512
    norm_num at maxRoom ⊢
    rw [sortedLength] at sumBound
    omega
  obtain ⟨expandedOutput, windowsLoopRun, expandedValue⟩ :=
    V7FirstCompactFrontierLoopBridge.translated_windows_loop_exact sorted.val
      iterator 19#usize iteratorWidth iteratorRemaining sortedDistinct
      loopHeadroom
  have qLeExpanded : (16#usize).val ≤ expandedOutput.val := by
    rw [expandedValue]
    have sumNonnegative := Nat.zero_le
      (V7FirstCompactFrontierLoopBridge.adjacentXorLogSum sorted.val)
    norm_num at sumNonnegative ⊢
    omega
  obtain ⟨finalOutput, finalSubRun, finalSubSpec⟩ := WP.spec_imp_exists
    (Std.Usize.sub_spec (x := expandedOutput) (y := 16#usize) qLeExpanded)
  have checkedFinal :
      Std.Usize.checked_sub expandedOutput 16#usize = some finalOutput := by
    unfold Std.Usize.checked_sub core.num.checked_sub_UScalar
    rw [finalSubRun]
    rfl
  have finalValue : finalOutput.val = 19 +
      V7FirstCompactFrontierLoopBridge.adjacentXorLogSum sorted.val - 16 := by
    calc
      finalOutput.val = expandedOutput.val - (16#usize).val := finalSubSpec.1
      _ = ((19#usize).val +
          V7FirstCompactFrontierLoopBridge.adjacentXorLogSum sorted.val) -
            (16#usize).val := by rw [expandedValue]
      _ = 19 + V7FirstCompactFrontierLoopBridge.adjacentXorLogSum sorted.val - 16 := by
        norm_num
  have sourceRun :
      v6_onefold.binary_frontier_nodes queries 18#u8 =
        .ok (.Ok finalOutput) := by
    unfold v6_onefold.binary_frontier_nodes
    simp [sortRun, lastIndexRun, lastReadRun, duplicateRun]
    simp only [lift, bind_tc_ok]
    rw [leafRun]
    simp [core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch,
      expandedStartRun, sortedSlice, windowsRun, windowsLoopRun, checkedFinal]
    exact lastBelowLeaf
  exact ⟨sorted, finalOutput, sourceRun, sortPost, finalValue⟩

#print axioms translated_inner_insertion_exact
#print axioms translated_outer_insertion_sort_exact
#print axioms translated_sort_from_one
#print axioms sorted_output_pairwise_distinct
#print axioms sorted_output_preserves_bound
#print axioms adjacentXorLogSum_le_length
#print axioms translated_duplicate_scan_accepts
#print axioms translated_binary_frontier_q16_exact

end V7FirstCompactFrontierSortSourceBridge
