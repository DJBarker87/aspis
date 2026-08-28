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

#print axioms translated_inner_insertion_exact

end V7BinaryFrontierSortSourceBridge
