import V7BinaryFrontierSortModel

/-!
# Translated insertion-sort source bridge

This file connects the literal Aeneas translation of production's inner
insertion loop to the pure `bubbleLeft` model.  The saved key remains outside
the translated shift loop; placing it at the returned cursor yields exactly
the adjacent-swap model.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open V7BinaryFrontierSource

set_option autoImplicit false

namespace V7BinaryFrontierSortSourceBridge

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

#print axioms translated_inner_insertion_exact
#print axioms translated_outer_insertion_sort_exact

end V7BinaryFrontierSortSourceBridge
