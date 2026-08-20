import Coordinates.Funs
import V5FriCoordinateFieldSemantics

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 12000

/-!
# Exact source semantics of the V5 coordinate output loops

The accepted source path copies the flat inverse array into one two-entry
array per circle query and one three-entry array per later-layer query.  It
also computes the final doubled-x values.  These proofs follow the translated
Rust loops and rule out omission, duplication, or permutation in the returned
layout.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5FriCoordinateOutputLoops

namespace Coordinate
open V5FriCoordinateAdapter

abbrev M31 := aspis_core.field.M31
abbrev M31Vec := alloc.vec.Vec M31
abbrev PairVec := alloc.vec.Vec (Array M31 2#usize)
abbrev TripleVec := alloc.vec.Vec (Array M31 3#usize)
abbrev Point := aspis_core.circle_fri.BaseCirclePoint
abbrev PointVec := alloc.vec.Vec Point

end Coordinate

instance : Inhabited Coordinate.M31 := ⟨0#u32⟩
instance : Inhabited Coordinate.Point :=
  ⟨{ x := 0#u32, y := 0#u32 }⟩

private theorem getElemBang_eq_getElem {T : Type*} [Inhabited T]
    (values : List T) (index : Nat) (hindex : index < values.length) :
    values[index]! = values[index] := by
  apply List.getElem!_of_getElem?
  simp [hindex]

private theorem wrapping_add_exact (left right : Std.Usize)
    (hsmall : left.val + right.val < UScalar.size .Usize) :
    (Std.Usize.wrapping_add left right).val = left.val + right.val := by
  rw [Std.Usize.wrapping_add_val_eq]
  exact Nat.mod_eq_of_lt hsmall

private theorem pair_loop29_body_eq_loop19_body :
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop29.body =
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop19.body := rfl

private theorem triple_loop30_body_eq_loop20_body :
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop30.body =
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop20.body := rfl

private theorem triple_loop31_body_eq_loop20_body :
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop31.body =
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop20.body := rfl

private theorem triple_loop32_body_eq_loop22_body :
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop32.body =
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop22.body := rfl

private theorem final_loop33_body_eq_loop23_body :
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop33.body =
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop23.body := rfl

def pairAt (flat : Coordinate.M31Vec) (start ordinal : Nat) :
    Array Coordinate.M31 2#usize :=
  Array.make 2#usize
    [flat.val[start + 2 * ordinal]!, flat.val[start + 2 * ordinal + 1]!]

def pairOutput (flat : Coordinate.M31Vec) (start count : Nat) :
    List (Array Coordinate.M31 2#usize) :=
  (List.range count).map (pairAt flat start)

private def PairInvariant
    (layer : Slice Std.U32) (flat : Coordinate.M31Vec) (start : Nat)
    (state : Std.Usize × Coordinate.PairVec × Std.Usize) : Prop :=
  state.2.2.val ≤ layer.val.length ∧
  state.1.val = start + 2 * state.2.2.val ∧
  state.2.1.val = pairOutput flat start state.2.2.val

def PairPost
    (layer : Slice Std.U32) (flat : Coordinate.M31Vec) (start : Nat)
    (out : Std.Usize × Coordinate.PairVec) : Prop :=
  out.1.val = start + 2 * layer.val.length ∧
  out.2.val = pairOutput flat start layer.val.length

/-- The accepted pair-output loop copies exactly two consecutive entries per
circle query, in source order. -/
theorem pair_loop29_exact
    (layer : Slice Std.U32) (flat : Coordinate.M31Vec)
    (cursor : Std.Usize) (output : Coordinate.PairVec)
    (hcursor : cursor.val = 0) (houtput : output.val = [])
    (hbound : 2 * layer.val.length ≤ flat.val.length) :
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop29
        layer flat cursor output 0#usize
      ⦃ out => PairPost layer flat 0 out ⦄ := by
  unfold
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop29
  apply loop.spec_decr_nat
    (fun state => layer.val.length - state.2.2.val)
    (PairInvariant layer flat 0)
    (PairPost layer flat 0)
  · rintro ⟨currentCursor, currentOutput, currentOrdinal⟩ hstate
    rcases hstate with ⟨hordinalLe, hcurrentCursor, hcurrentOutput⟩
    simp only at hordinalLe hcurrentCursor hcurrentOutput
    rw [pair_loop29_body_eq_loop19_body]
    unfold
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop19.body
    by_cases hactive : currentOrdinal.val < layer.val.length
    · have hcondition : currentOrdinal < Slice.len layer := by
        simpa [UScalar.lt_equiv, Slice.len_val] using hactive
      have hcursorBound : currentCursor.val < flat.val.length := by omega
      have hcursorOneBound : currentCursor.val + 1 < flat.val.length := by
        omega
      have hsize : UScalar.size .Usize = Std.Usize.max + 1 := by
        simp [Std.Usize.size, Std.Usize.max, Std.Usize.numBits]
      have hcursorOneSmall : currentCursor.val + 1 < UScalar.size .Usize := by
        have hflatMax := flat.property
        omega
      have hcursorTwoSmall : currentCursor.val + 2 < UScalar.size .Usize := by
        have hflatMax := flat.property
        omega
      have hordinalOneSmall : currentOrdinal.val + 1 < UScalar.size .Usize := by
        have hlayerMax := layer.property
        omega
      let cursorOne := Std.Usize.wrapping_add currentCursor 1#usize
      let cursorTwo := Std.Usize.wrapping_add currentCursor 2#usize
      let ordinalOne := Std.Usize.wrapping_add currentOrdinal 1#usize
      have hcursorOne : cursorOne.val = currentCursor.val + 1 := by
        unfold cursorOne
        exact wrapping_add_exact _ _ (by simpa using hcursorOneSmall)
      have hcursorTwo : cursorTwo.val = currentCursor.val + 2 := by
        unfold cursorTwo
        exact wrapping_add_exact _ _ (by simpa using hcursorTwoSmall)
      have hordinalOne : ordinalOne.val = currentOrdinal.val + 1 := by
        unfold ordinalOne
        exact wrapping_add_exact _ _ (by simpa using hordinalOneSmall)
      have hfirstSpec := alloc.vec.Vec.index_usize_spec flat currentCursor
        hcursorBound
      obtain ⟨first, hfirstRun, hfirstValue⟩ :=
        Aeneas.Std.WP.spec_imp_exists hfirstSpec
      have hsecondSpec := alloc.vec.Vec.index_usize_spec flat cursorOne
        (by simpa [hcursorOne] using hcursorOneBound)
      obtain ⟨second, hsecondRun, hsecondValue⟩ :=
        Aeneas.Std.WP.spec_imp_exists hsecondSpec
      have hfirstBang : first = flat.val[currentCursor.val]! := by
        rw [hfirstValue,
          getElemBang_eq_getElem flat.val currentCursor.val hcursorBound]
      have hsecondBang : second = flat.val[cursorOne.val]! := by
        rw [hsecondValue,
          getElemBang_eq_getElem flat.val cursorOne.val
            (by simpa [hcursorOne] using hcursorOneBound)]
      have hcapacity : currentOutput.val.length < Std.Usize.max := by
        rw [hcurrentOutput, pairOutput, List.length_map, List.length_range]
        have hlayerMax := layer.property
        omega
      let value : Array Coordinate.M31 2#usize :=
        Array.make 2#usize [first, second]
      obtain ⟨nextOutput, hpushRun, hnextOutput⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (alloc.vec.Vec.push_spec currentOutput value hcapacity)
      simp only [if_pos hcondition, Std.lift, bind_tc_ok]
      rw [alloc.vec.Vec.index_slice_index, hfirstRun]
      simp only [bind_tc_ok]
      rw [alloc.vec.Vec.index_slice_index, hsecondRun]
      simp only [bind_tc_ok]
      rw [hpushRun]
      simp only [bind_tc_ok, WP.spec_ok]
      change PairInvariant layer flat 0
          (cursorTwo, nextOutput, ordinalOne) ∧
        layer.val.length - ordinalOne.val <
          layer.val.length - currentOrdinal.val
      refine ⟨?_, by rw [hordinalOne]; omega⟩
      unfold PairInvariant
      simp only
      refine ⟨by rw [hordinalOne]; omega, ?_, ?_⟩
      · rw [hcursorTwo, hcurrentCursor, hordinalOne]
        omega
      · rw [hnextOutput, hcurrentOutput]
        unfold pairOutput pairAt value
        rw [hordinalOne]
        rw [List.range_succ, List.map_append]
        simp only [List.map_cons, List.map_nil]
        rw [hfirstBang, hsecondBang, hcursorOne, hcurrentCursor]
    · have hdone : currentOrdinal.val = layer.val.length := by omega
      have hcondition : ¬ currentOrdinal < Slice.len layer := by
        simpa [UScalar.lt_equiv, Slice.len_val] using hactive
      simp only [if_neg hcondition, WP.spec_ok]
      rw [hdone] at hcurrentCursor hcurrentOutput
      exact ⟨hcurrentCursor, hcurrentOutput⟩
  · unfold PairInvariant
    simp only
    exact ⟨by simp, by simpa using hcursor, by simp [pairOutput, houtput]⟩

def tripleAt (flat : Coordinate.M31Vec) (start ordinal : Nat) :
    Array Coordinate.M31 3#usize :=
  Array.make 3#usize
    [flat.val[start + 3 * ordinal]!,
      flat.val[start + 3 * ordinal + 1]!,
      flat.val[start + 3 * ordinal + 2]!]

def tripleOutput (flat : Coordinate.M31Vec) (start count : Nat) :
    List (Array Coordinate.M31 3#usize) :=
  (List.range count).map (tripleAt flat start)

private def TripleInvariant
    (layer : Slice Std.U32) (flat : Coordinate.M31Vec) (start : Nat)
    (state : Std.Usize × Coordinate.TripleVec × Std.Usize) : Prop :=
  state.2.2.val ≤ layer.val.length ∧
  state.1.val = start + 3 * state.2.2.val ∧
  state.2.1.val = tripleOutput flat start state.2.2.val

def TriplePost
    (layer : Slice Std.U32) (flat : Coordinate.M31Vec) (start : Nat)
    (out : Std.Usize × Coordinate.TripleVec) : Prop :=
  out.1.val = start + 3 * layer.val.length ∧
  out.2.val = tripleOutput flat start layer.val.length

/-- The first accepted later-layer loop copies exactly three consecutive
entries per query, preserving order. -/
theorem triple_loop30_exact
    (layer : Slice Std.U32) (flat : Coordinate.M31Vec)
    (cursor : Std.Usize) (output : Coordinate.TripleVec) (start : Nat)
    (hcursor : cursor.val = start) (houtput : output.val = [])
    (hbound : start + 3 * layer.val.length ≤ flat.val.length) :
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop30
        layer flat cursor output 0#usize
      ⦃ out => TriplePost layer flat start out ⦄ := by
  unfold
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop30
  apply loop.spec_decr_nat
    (fun state => layer.val.length - state.2.2.val)
    (TripleInvariant layer flat start)
    (TriplePost layer flat start)
  · rintro ⟨currentCursor, currentOutput, currentOrdinal⟩ hstate
    rcases hstate with ⟨hordinalLe, hcurrentCursor, hcurrentOutput⟩
    simp only at hordinalLe hcurrentCursor hcurrentOutput
    rw [triple_loop30_body_eq_loop20_body]
    unfold
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop20.body
    by_cases hactive : currentOrdinal.val < layer.val.length
    · have hcondition : currentOrdinal < Slice.len layer := by
        simpa [UScalar.lt_equiv, Slice.len_val] using hactive
      have hcursorBound : currentCursor.val < flat.val.length := by omega
      have hcursorOneBound : currentCursor.val + 1 < flat.val.length := by
        omega
      have hcursorTwoBound : currentCursor.val + 2 < flat.val.length := by
        omega
      have hsize : UScalar.size .Usize = Std.Usize.max + 1 := by
        simp [Std.Usize.size, Std.Usize.max, Std.Usize.numBits]
      have hcursorOneSmall : currentCursor.val + 1 < UScalar.size .Usize := by
        have hflatMax := flat.property
        omega
      have hcursorTwoSmall : currentCursor.val + 2 < UScalar.size .Usize := by
        have hflatMax := flat.property
        omega
      have hcursorThreeSmall : currentCursor.val + 3 < UScalar.size .Usize := by
        have hflatMax := flat.property
        omega
      have hordinalOneSmall : currentOrdinal.val + 1 < UScalar.size .Usize := by
        have hlayerMax := layer.property
        omega
      let cursorOne := Std.Usize.wrapping_add currentCursor 1#usize
      let cursorTwo := Std.Usize.wrapping_add currentCursor 2#usize
      let cursorThree := Std.Usize.wrapping_add currentCursor 3#usize
      let ordinalOne := Std.Usize.wrapping_add currentOrdinal 1#usize
      have hcursorOne : cursorOne.val = currentCursor.val + 1 := by
        unfold cursorOne
        exact wrapping_add_exact _ _ (by simpa using hcursorOneSmall)
      have hcursorTwo : cursorTwo.val = currentCursor.val + 2 := by
        unfold cursorTwo
        exact wrapping_add_exact _ _ (by simpa using hcursorTwoSmall)
      have hcursorThree : cursorThree.val = currentCursor.val + 3 := by
        unfold cursorThree
        exact wrapping_add_exact _ _ (by simpa using hcursorThreeSmall)
      have hordinalOne : ordinalOne.val = currentOrdinal.val + 1 := by
        unfold ordinalOne
        exact wrapping_add_exact _ _ (by simpa using hordinalOneSmall)
      have hfirstSpec := alloc.vec.Vec.index_usize_spec flat currentCursor
        hcursorBound
      obtain ⟨first, hfirstRun, hfirstValue⟩ :=
        Aeneas.Std.WP.spec_imp_exists hfirstSpec
      have hsecondSpec := alloc.vec.Vec.index_usize_spec flat cursorOne
        (by simpa [hcursorOne] using hcursorOneBound)
      obtain ⟨second, hsecondRun, hsecondValue⟩ :=
        Aeneas.Std.WP.spec_imp_exists hsecondSpec
      have hthirdSpec := alloc.vec.Vec.index_usize_spec flat cursorTwo
        (by simpa [hcursorTwo] using hcursorTwoBound)
      obtain ⟨third, hthirdRun, hthirdValue⟩ :=
        Aeneas.Std.WP.spec_imp_exists hthirdSpec
      have hfirstBang : first = flat.val[currentCursor.val]! := by
        rw [hfirstValue,
          getElemBang_eq_getElem flat.val currentCursor.val hcursorBound]
      have hsecondBang : second = flat.val[cursorOne.val]! := by
        rw [hsecondValue,
          getElemBang_eq_getElem flat.val cursorOne.val
            (by simpa [hcursorOne] using hcursorOneBound)]
      have hthirdBang : third = flat.val[cursorTwo.val]! := by
        rw [hthirdValue,
          getElemBang_eq_getElem flat.val cursorTwo.val
            (by simpa [hcursorTwo] using hcursorTwoBound)]
      have hcapacity : currentOutput.val.length < Std.Usize.max := by
        rw [hcurrentOutput, tripleOutput, List.length_map, List.length_range]
        have hlayerMax := layer.property
        omega
      let value : Array Coordinate.M31 3#usize :=
        Array.make 3#usize [first, second, third]
      obtain ⟨nextOutput, hpushRun, hnextOutput⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (alloc.vec.Vec.push_spec currentOutput value hcapacity)
      simp only [if_pos hcondition, Std.lift, bind_tc_ok]
      rw [alloc.vec.Vec.index_slice_index, hfirstRun]
      simp only [bind_tc_ok]
      rw [alloc.vec.Vec.index_slice_index, hsecondRun]
      simp only [bind_tc_ok]
      rw [alloc.vec.Vec.index_slice_index, hthirdRun]
      simp only [bind_tc_ok]
      rw [hpushRun]
      simp only [bind_tc_ok, WP.spec_ok]
      change TripleInvariant layer flat start
          (cursorThree, nextOutput, ordinalOne) ∧
        layer.val.length - ordinalOne.val <
          layer.val.length - currentOrdinal.val
      refine ⟨?_, by rw [hordinalOne]; omega⟩
      unfold TripleInvariant
      simp only
      refine ⟨by rw [hordinalOne]; omega, ?_, ?_⟩
      · rw [hcursorThree, hcurrentCursor, hordinalOne]
        omega
      · rw [hnextOutput, hcurrentOutput]
        unfold tripleOutput tripleAt value
        rw [hordinalOne]
        rw [List.range_succ, List.map_append]
        simp only [List.map_cons, List.map_nil]
        rw [hfirstBang, hsecondBang, hthirdBang,
          hcursorOne, hcursorTwo, hcurrentCursor]
    · have hdone : currentOrdinal.val = layer.val.length := by omega
      have hcondition : ¬ currentOrdinal < Slice.len layer := by
        simpa [UScalar.lt_equiv, Slice.len_val] using hactive
      simp only [if_neg hcondition, WP.spec_ok]
      rw [hdone] at hcurrentCursor hcurrentOutput
      exact ⟨hcurrentCursor, hcurrentOutput⟩
  · unfold TripleInvariant
    simp only
    exact ⟨by simp, by simpa using hcursor,
      by simp [tripleOutput, houtput]⟩

private theorem triple_loop31_eq_loop30
    (layer : Slice Std.U32) (flat : Coordinate.M31Vec)
    (cursor : Std.Usize) (output : Coordinate.TripleVec)
    (ordinal : Std.Usize) :
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop31
        layer flat cursor output ordinal =
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop30
        layer flat cursor output ordinal := by
  rfl

/-- The second accepted later-layer loop has the same exact source semantics. -/
theorem triple_loop31_exact
    (layer : Slice Std.U32) (flat : Coordinate.M31Vec)
    (cursor : Std.Usize) (output : Coordinate.TripleVec) (start : Nat)
    (hcursor : cursor.val = start) (houtput : output.val = [])
    (hbound : start + 3 * layer.val.length ≤ flat.val.length) :
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop31
        layer flat cursor output 0#usize
      ⦃ out => TriplePost layer flat start out ⦄ := by
  rw [triple_loop31_eq_loop30]
  exact triple_loop30_exact layer flat cursor output start hcursor houtput hbound

private def TripleFinalInvariant
    (layer : Slice Std.U32) (flat : Coordinate.M31Vec) (start : Nat)
    (state : Std.Usize × Coordinate.TripleVec × Std.Usize) : Prop :=
  state.2.2.val ≤ layer.val.length ∧
  state.1.val = start + 3 * state.2.2.val ∧
  state.2.1.val = tripleOutput flat start state.2.2.val

def TripleFinalPost
    (layer : Slice Std.U32) (flat : Coordinate.M31Vec) (start : Nat)
    (out : Coordinate.TripleVec) : Prop :=
  out.val = tripleOutput flat start layer.val.length

/-- The final accepted later-layer loop copies the last three-entry segment
exactly and returns that segment without exposing the final cursor. -/
theorem triple_loop32_exact
    (layer : Slice Std.U32) (flat : Coordinate.M31Vec)
    (cursor : Std.Usize) (output : Coordinate.TripleVec) (start : Nat)
    (hcursor : cursor.val = start) (houtput : output.val = [])
    (hbound : start + 3 * layer.val.length ≤ flat.val.length) :
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop32
        layer flat cursor output 0#usize
      ⦃ out => TripleFinalPost layer flat start out ⦄ := by
  unfold
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop32
  apply loop.spec_decr_nat
    (fun state => layer.val.length - state.2.2.val)
    (TripleFinalInvariant layer flat start)
    (TripleFinalPost layer flat start)
  · rintro ⟨currentCursor, currentOutput, currentOrdinal⟩ hstate
    rcases hstate with ⟨hordinalLe, hcurrentCursor, hcurrentOutput⟩
    simp only at hordinalLe hcurrentCursor hcurrentOutput
    rw [triple_loop32_body_eq_loop22_body]
    unfold
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop22.body
    by_cases hactive : currentOrdinal.val < layer.val.length
    · have hcondition : currentOrdinal < Slice.len layer := by
        simpa [UScalar.lt_equiv, Slice.len_val] using hactive
      have hcursorBound : currentCursor.val < flat.val.length := by omega
      have hcursorOneBound : currentCursor.val + 1 < flat.val.length := by
        omega
      have hcursorTwoBound : currentCursor.val + 2 < flat.val.length := by
        omega
      have hsize : UScalar.size .Usize = Std.Usize.max + 1 := by
        simp [Std.Usize.size, Std.Usize.max, Std.Usize.numBits]
      have hcursorOneSmall : currentCursor.val + 1 < UScalar.size .Usize := by
        have hflatMax := flat.property
        omega
      have hcursorTwoSmall : currentCursor.val + 2 < UScalar.size .Usize := by
        have hflatMax := flat.property
        omega
      have hcursorThreeSmall : currentCursor.val + 3 < UScalar.size .Usize := by
        have hflatMax := flat.property
        omega
      have hordinalOneSmall : currentOrdinal.val + 1 < UScalar.size .Usize := by
        have hlayerMax := layer.property
        omega
      let cursorOne := Std.Usize.wrapping_add currentCursor 1#usize
      let cursorTwo := Std.Usize.wrapping_add currentCursor 2#usize
      let cursorThree := Std.Usize.wrapping_add currentCursor 3#usize
      let ordinalOne := Std.Usize.wrapping_add currentOrdinal 1#usize
      have hcursorOne : cursorOne.val = currentCursor.val + 1 := by
        unfold cursorOne
        exact wrapping_add_exact _ _ (by simpa using hcursorOneSmall)
      have hcursorTwo : cursorTwo.val = currentCursor.val + 2 := by
        unfold cursorTwo
        exact wrapping_add_exact _ _ (by simpa using hcursorTwoSmall)
      have hcursorThree : cursorThree.val = currentCursor.val + 3 := by
        unfold cursorThree
        exact wrapping_add_exact _ _ (by simpa using hcursorThreeSmall)
      have hordinalOne : ordinalOne.val = currentOrdinal.val + 1 := by
        unfold ordinalOne
        exact wrapping_add_exact _ _ (by simpa using hordinalOneSmall)
      have hfirstSpec := alloc.vec.Vec.index_usize_spec flat currentCursor
        hcursorBound
      obtain ⟨first, hfirstRun, hfirstValue⟩ :=
        Aeneas.Std.WP.spec_imp_exists hfirstSpec
      have hsecondSpec := alloc.vec.Vec.index_usize_spec flat cursorOne
        (by simpa [hcursorOne] using hcursorOneBound)
      obtain ⟨second, hsecondRun, hsecondValue⟩ :=
        Aeneas.Std.WP.spec_imp_exists hsecondSpec
      have hthirdSpec := alloc.vec.Vec.index_usize_spec flat cursorTwo
        (by simpa [hcursorTwo] using hcursorTwoBound)
      obtain ⟨third, hthirdRun, hthirdValue⟩ :=
        Aeneas.Std.WP.spec_imp_exists hthirdSpec
      have hfirstBang : first = flat.val[currentCursor.val]! := by
        rw [hfirstValue,
          getElemBang_eq_getElem flat.val currentCursor.val hcursorBound]
      have hsecondBang : second = flat.val[cursorOne.val]! := by
        rw [hsecondValue,
          getElemBang_eq_getElem flat.val cursorOne.val
            (by simpa [hcursorOne] using hcursorOneBound)]
      have hthirdBang : third = flat.val[cursorTwo.val]! := by
        rw [hthirdValue,
          getElemBang_eq_getElem flat.val cursorTwo.val
            (by simpa [hcursorTwo] using hcursorTwoBound)]
      have hcapacity : currentOutput.val.length < Std.Usize.max := by
        rw [hcurrentOutput, tripleOutput, List.length_map, List.length_range]
        have hlayerMax := layer.property
        omega
      let value : Array Coordinate.M31 3#usize :=
        Array.make 3#usize [first, second, third]
      obtain ⟨nextOutput, hpushRun, hnextOutput⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (alloc.vec.Vec.push_spec currentOutput value hcapacity)
      simp only [if_pos hcondition, Std.lift, bind_tc_ok]
      rw [alloc.vec.Vec.index_slice_index, hfirstRun]
      simp only [bind_tc_ok]
      rw [alloc.vec.Vec.index_slice_index, hsecondRun]
      simp only [bind_tc_ok]
      rw [alloc.vec.Vec.index_slice_index, hthirdRun]
      simp only [bind_tc_ok]
      rw [hpushRun]
      simp only [bind_tc_ok, WP.spec_ok]
      change TripleFinalInvariant layer flat start
          (cursorThree, nextOutput, ordinalOne) ∧
        layer.val.length - ordinalOne.val <
          layer.val.length - currentOrdinal.val
      refine ⟨?_, by rw [hordinalOne]; omega⟩
      unfold TripleFinalInvariant
      simp only
      refine ⟨by rw [hordinalOne]; omega, ?_, ?_⟩
      · rw [hcursorThree, hcurrentCursor, hordinalOne]
        omega
      · rw [hnextOutput, hcurrentOutput]
        unfold tripleOutput tripleAt value
        rw [hordinalOne]
        rw [List.range_succ, List.map_append]
        simp only [List.map_cons, List.map_nil]
        rw [hfirstBang, hsecondBang, hthirdBang,
          hcursorOne, hcursorTwo, hcurrentCursor]
    · have hdone : currentOrdinal.val = layer.val.length := by omega
      have hcondition : ¬ currentOrdinal < Slice.len layer := by
        simpa [UScalar.lt_equiv, Slice.len_val] using hactive
      simp only [if_neg hcondition, WP.spec_ok]
      rw [hdone] at hcurrentOutput
      exact hcurrentOutput
  · unfold TripleFinalInvariant
    simp only
    exact ⟨by simp, by simpa using hcursor,
      by simp [tripleOutput, houtput]⟩

open AspisV5FriCoordinateFieldSemantics
open AspisCircleGroupOrder

def CanonicalM31Vec (values : Coordinate.M31Vec) : Prop :=
  ∀ index, index < values.val.length → canonicalM31 values.val[index]!

def CanonicalPointXVec (points : Coordinate.PointVec) : Prop :=
  ∀ index, index < points.val.length → canonicalM31 points.val[index]!.x

def finalXFormula (x : Coordinate.M31) : ZMod P :=
  2 * (2 * m31Value x ^ 2 - 1) ^ 2 - 1

private def FinalXInvariant
    (points : Coordinate.PointVec)
    (state : Coordinate.M31Vec × Std.Usize) : Prop :=
  state.2.val ≤ points.val.length ∧
  state.1.val.length = state.2.val ∧
  CanonicalM31Vec state.1 ∧
  ∀ index, index < state.2.val →
    m31Value state.1.val[index]! = finalXFormula points.val[index]!.x

def FinalXPost
    (points : Coordinate.PointVec) (out : Coordinate.M31Vec) : Prop :=
  out.val.length = points.val.length ∧
  CanonicalM31Vec out ∧
  ∀ index, index < points.val.length →
    m31Value out.val[index]! = finalXFormula points.val[index]!.x

/-- The final accepted source loop returns the exact twice-doubled x value
for every last-layer point, in order. -/
theorem final_x_loop33_exact
    (points : Coordinate.PointVec) (output : Coordinate.M31Vec)
    (hpoints : CanonicalPointXVec points) (houtput : output.val = []) :
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop33
        points output 0#usize
      ⦃ out => FinalXPost points out ⦄ := by
  unfold
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop33
  apply loop.spec_decr_nat
    (fun state => points.val.length - state.2.val)
    (FinalXInvariant points)
    (FinalXPost points)
  · rintro ⟨currentOutput, currentOrdinal⟩ hstate
    rcases hstate with
      ⟨hordinalLe, hcurrentLength, hcurrentCanonical, hcurrentValues⟩
    simp only at hordinalLe hcurrentLength hcurrentCanonical hcurrentValues
    rw [final_loop33_body_eq_loop23_body]
    unfold
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop23.body
    by_cases hactive : currentOrdinal.val < points.val.length
    · have hcondition : currentOrdinal < alloc.vec.Vec.len points := by
        simpa [UScalar.lt_equiv] using hactive
      have hpointSpec := alloc.vec.Vec.index_usize_spec points currentOrdinal
        hactive
      obtain ⟨point, hpointRun, hpointValue⟩ :=
        Aeneas.Std.WP.spec_imp_exists hpointSpec
      have hpointRawBang : point = points.val[currentOrdinal.val]! := by
        rw [hpointValue,
          getElemBang_eq_getElem points.val currentOrdinal.val hactive]
      have hpointCanonical : canonicalM31 point.x := by
        rw [hpointRawBang]
        exact hpoints currentOrdinal.val hactive
      obtain ⟨first, hfirstRun, hfirstCanonical, hfirstValue⟩ :=
        double_x_produces_canonical point.x hpointCanonical
      obtain ⟨second, hsecondRun, hsecondCanonical, hsecondValue⟩ :=
        double_x_produces_canonical first hfirstCanonical
      have hcapacity : currentOutput.val.length < Std.Usize.max := by
        rw [hcurrentLength]
        have hpointsMax := points.property
        omega
      obtain ⟨nextOutput, hpushRun, hnextOutput⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (alloc.vec.Vec.push_spec currentOutput second hcapacity)
      have hsize : UScalar.size .Usize = Std.Usize.max + 1 := by
        simp [Std.Usize.size, Std.Usize.max, Std.Usize.numBits]
      have hordinalOneSmall : currentOrdinal.val + 1 < UScalar.size .Usize := by
        have hpointsMax := points.property
        omega
      let ordinalOne := Std.Usize.wrapping_add currentOrdinal 1#usize
      have hordinalOne : ordinalOne.val = currentOrdinal.val + 1 := by
        unfold ordinalOne
        exact wrapping_add_exact _ _ (by simpa using hordinalOneSmall)
      simp only [if_pos hcondition]
      rw [alloc.vec.Vec.index_slice_index, hpointRun]
      simp only [bind_tc_ok]
      rw [hfirstRun]
      simp only [bind_tc_ok]
      rw [hsecondRun]
      simp only [bind_tc_ok]
      rw [hpushRun]
      simp only [Std.lift, bind_tc_ok, WP.spec_ok]
      change FinalXInvariant points (nextOutput, ordinalOne) ∧
        points.val.length - ordinalOne.val <
          points.val.length - currentOrdinal.val
      refine ⟨?_, by rw [hordinalOne]; omega⟩
      unfold FinalXInvariant
      simp only
      have hnextLength : nextOutput.val.length = ordinalOne.val := by
        rw [hnextOutput, List.length_append, hcurrentLength, hordinalOne]
        simp
      have hnextCanonical : CanonicalM31Vec nextOutput := by
        intro index hindex
        rw [hnextOutput] at hindex ⊢
        by_cases hold : index < currentOutput.val.length
        · have happBound : index <
              (currentOutput.val ++ [second]).length := hindex
          rw [getElemBang_eq_getElem _ index happBound,
            List.getElem_append_left hold]
          have holdBang := getElemBang_eq_getElem currentOutput.val index hold
          rw [← holdBang]
          exact hcurrentCanonical index hold
        · have hlast : index = currentOutput.val.length := by
            simp only [List.length_append, List.length_cons, List.length_nil]
              at hindex
            omega
          subst index
          simp [hsecondCanonical]
      refine ⟨by rw [hordinalOne]; omega, hnextLength,
        hnextCanonical, ?_⟩
      intro index hindex
      by_cases hold : index < currentOrdinal.val
      · have holdOutput : index < currentOutput.val.length := by
          rwa [hcurrentLength]
        have hnextBang :
            nextOutput.val[index]! =
              (currentOutput.val ++ [second])[index]! :=
          congrArg (fun values => values[index]!) hnextOutput
        rw [hnextBang]
        have happBound : index <
            (currentOutput.val ++ [second]).length := by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        rw [getElemBang_eq_getElem _ index happBound,
          List.getElem_append_left holdOutput]
        have holdBang := getElemBang_eq_getElem currentOutput.val index
          holdOutput
        rw [← holdBang]
        exact hcurrentValues index hold
      · have hlast : index = currentOrdinal.val := by
          rw [hordinalOne] at hindex
          omega
        subst index
        have hlastValue :
            (currentOutput.val ++ [second])[currentOrdinal.val]! = second := by
          rw [← hcurrentLength]
          simp
        have hnextBang :
            nextOutput.val[currentOrdinal.val]! =
              (currentOutput.val ++ [second])[currentOrdinal.val]! :=
          congrArg (fun values => values[currentOrdinal.val]!) hnextOutput
        rw [hnextBang, hlastValue]
        rw [hsecondValue, hfirstValue, hpointRawBang]
        rfl
    · have hdone : currentOrdinal.val = points.val.length := by omega
      have hcondition : ¬ currentOrdinal < alloc.vec.Vec.len points := by
        simpa [UScalar.lt_equiv] using hactive
      simp only [if_neg hcondition, WP.spec_ok]
      rw [hdone] at hcurrentLength hcurrentValues
      exact ⟨hcurrentLength, hcurrentCanonical, hcurrentValues⟩
  · unfold FinalXInvariant CanonicalM31Vec
    simp only
    refine ⟨by simp, ?_, ?_, ?_⟩
    · simpa [houtput]
    · intro index hindex
      simp [houtput] at hindex
    · intro index hindex
      norm_num at hindex

#print axioms pair_loop29_exact
#print axioms triple_loop30_exact
#print axioms triple_loop31_exact
#print axioms triple_loop32_exact
#print axioms final_x_loop33_exact

end AspisV5FriCoordinateOutputLoops
