import RuntimeLaterFibreCorrespondence
import RuntimeRoundDeepControlFlow
import Aeneas.Tactic.Step.StepStar

set_option autoImplicit false

open Aeneas Aeneas.Std Result ControlFlow

namespace aspis_prover.ComponentCRuntimeLaterRoundLoopCorrespondence

open aspis_prover
open ComponentCRuntimeLaterFibreProof
open ComponentCRuntimeRoundDeepControlFlow

abbrev RawQM31 := aspis_core.field.QM31
abbrev RuntimeLater := Array (alloc.vec.Vec RawQM31) 3#usize
abbrev RuntimeError :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeError

def releasedFibresPrefix
    (folded : Slice RawQM31) (fibres : alloc.vec.Vec Std.U32)
    (count : Nat) : List RawQM31 :=
  (List.range count).flatMap fun ordinal =>
    releasedPrefix folded (4 * fibres.val[ordinal]!.val) 4

private theorem releasedFibresPrefix_succ
    (folded : Slice RawQM31) (fibres : alloc.vec.Vec Std.U32)
    (count : Nat) :
    releasedFibresPrefix folded fibres (count + 1) =
      releasedFibresPrefix folded fibres count ++
        releasedPrefix folded (4 * fibres.val[count]!.val) 4 := by
  simp [releasedFibresPrefix, List.range_succ]

theorem releasedFibresPrefix_length
    (folded : Slice RawQM31) (fibres : alloc.vec.Vec Std.U32)
    (count : Nat) :
    (releasedFibresPrefix folded fibres count).length = 4 * count := by
  simp [releasedFibresPrefix, releasedPrefix, Nat.mul_comm]

theorem releasedFibresPrefix_get
    (folded : Slice RawQM31) (fibres : alloc.vec.Vec Std.U32)
    (count index slot : Nat)
    (hindex : index < count) (hslot : slot < 4) :
    (releasedFibresPrefix folded fibres count)[4 * index + slot]! =
      folded.val[4 * fibres.val[index]!.val + slot]! := by
  induction count with
  | zero => omega
  | succ count ih =>
      rw [releasedFibresPrefix_succ]
      by_cases heq : index = count
      · subst index
        rw [List.getElem!_eq_getElem?_getD,
          List.getElem?_append_right]
        · rw [releasedFibresPrefix_length]
          simp [releasedPrefix, hslot]
        · rw [releasedFibresPrefix_length]
          omega
      · have hindexPrior : index < count := by omega
        rw [List.getElem!_eq_getElem?_getD,
          List.getElem?_append_left]
        · rw [← List.getElem!_eq_getElem?_getD]
          exact ih hindexPrior
        · rw [releasedFibresPrefix_length]
          omega

private theorem array_index_run
    {T : Type*} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (hindex : index.val < N.val) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, hrun, hvalue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hindex))
  have hbound : index.val < values.val.length := by
    simpa [Array.length_eq] using hindex
  have hbang : values.val[index.val]! = values.val[index.val] := by
    apply List.getElem!_of_getElem?
    exact List.getElem?_eq_getElem hbound
  simpa [hvalue, hbang] using hrun

private theorem array_index_mut_run
    {T : Type*} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (hindex : index.val < N.val) :
    Array.index_mut_usize values index =
      ok (values.val[index.val]!, values.set index) := by
  obtain ⟨result, hrun, hpost⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_mut_usize_spec values index (by
      simpa [Array.length_eq] using hindex))
  rcases result with ⟨value, restore⟩
  rcases hpost with ⟨hvalue, hrestore⟩
  have hbound : index.val < values.val.length := by
    simpa [Array.length_eq] using hindex
  have hbang : values.val[index.val]! = values.val[index.val] := by
    apply List.getElem!_of_getElem?
    exact List.getElem?_eq_getElem hbound
  simpa [hvalue, hrestore, hbang] using hrun

private theorem vec_index_run
    {T : Type} [Inhabited T]
    (values : alloc.vec.Vec T) (index : Std.Usize)
    (hindex : index.val < values.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice T)
        values index = ok values.val[index.val]! := by
  rw [alloc.vec.Vec.index_slice_index]
  obtain ⟨value, hrun, hvalue⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec values index (by simpa using hindex))
  have hbang : values.val[index.val]! = values.val[index.val] := by
    apply List.getElem!_of_getElem?
    exact List.getElem?_eq_getElem hindex
  simpa [hvalue, hbang] using hrun

private theorem selected_after_set
    (later : RuntimeLater) (round : Std.Usize)
    (value : alloc.vec.Vec RawQM31) (hround : round.val < 3) :
    (later.set round value).val[round.val]!.val = value.val := by
  simp only [Array.set_val_eq]
  rw [List.set_getElem!_eq]
  exact ⟨by simpa [Array.length_eq] using hround, rfl⟩

private theorem wrapping_succ_val
    (ordinal : Std.Usize) (h : ordinal.val + 1 < Std.Usize.size) :
    (Std.Usize.wrapping_add ordinal 1#usize).val = ordinal.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  simpa using h

private def LaterLoopInvariant
    (folded : Slice RawQM31) (fibres : alloc.vec.Vec Std.U32)
    (initial : RuntimeLater) (round : Std.Usize)
    (state : RuntimeLater × Std.Usize × Option RuntimeError) : Prop :=
  state.2.1.val ≤ fibres.val.length ∧
  state.2.2 = none ∧
  state.1.val[round.val]!.val =
    initial.val[round.val]!.val ++
      releasedFibresPrefix folded fibres state.2.1.val ∧
  ∀ layer : Fin 3, layer.val ≠ round.val →
    state.1.val[layer.val]! = initial.val[layer.val]!

private def LaterLoopPost
    (folded : Slice RawQM31) (fibres : alloc.vec.Vec Std.U32)
    (initial : RuntimeLater) (round : Std.Usize)
    (result : RuntimeLater × Option RuntimeError) : Prop :=
  result.2 = none ∧
  result.1.val[round.val]!.val =
    initial.val[round.val]!.val ++
      releasedFibresPrefix folded fibres fibres.val.length ∧
  ∀ layer : Fin 3, layer.val ≠ round.val →
    result.1.val[layer.val]! = initial.val[layer.val]!

/-- The actual generated later-fibre loop traverses every schedule fibre in
vector order and appends its four codeword slots in slot order.  This theorem
covers the array layer selection, vector indexing, mutable write-back, error
propagation, and both nested generated loops. -/
theorem generated_later_round_loop_exact
    (scheduleFibres : Array (alloc.vec.Vec Std.U32) 3#usize)
    (foldedCodeword : alloc.vec.Vec RawQM31)
    (initial : RuntimeLater) (round : Std.Usize)
    (fibres : alloc.vec.Vec Std.U32)
    (hround : round.val < 3)
    (hfibres : scheduleFibres.val[round.val]! = fibres)
    (hread : ∀ fibre ∈ fibres.val,
      4 * fibre.val + 4 ≤ foldedCodeword.val.length)
    (hcapacity :
      initial.val[round.val]!.val.length + 4 * fibres.val.length ≤
        Std.Usize.max) :
    v5_mask.component_c_runtime.evaluate_component_c_runtime_round_loop
        scheduleFibres foldedCodeword initial round 0#usize none
      ⦃ result => LaterLoopPost (alloc.vec.Vec.deref foldedCodeword)
        fibres initial round result ⦄ := by
  unfold v5_mask.component_c_runtime.evaluate_component_c_runtime_round_loop
  apply loop.spec_decr_nat
    (fun state : RuntimeLater × Std.Usize × Option RuntimeError =>
      fibres.val.length - state.2.1.val)
    (LaterLoopInvariant (alloc.vec.Vec.deref foldedCodeword)
      fibres initial round)
    (LaterLoopPost (alloc.vec.Vec.deref foldedCodeword)
      fibres initial round)
  · rintro ⟨later, ordinal, error⟩
      ⟨hordinal, herror, hlater, hother⟩
    dsimp only at hordinal herror hlater hother ⊢
    unfold
      v5_mask.component_c_runtime.evaluate_component_c_runtime_round_loop.body
    rw [herror]
    rw [array_index_run scheduleFibres round hround, hfibres]
    simp only [bind_tc_ok]
    by_cases hactive : ordinal.val < fibres.val.length
    · have hactiveScalar : ordinal < alloc.vec.Vec.len fibres := by
        simp only [alloc.vec.Vec.len]
        scalar_tac
      rw [if_pos hactiveScalar]
      simp only [core.option.Option.is_none]
      rw [if_pos (by rfl)]
      rw [vec_index_run fibres ordinal hactive]
      simp only [bind_tc_ok]
      rw [array_index_mut_run later round hround]
      simp only [bind_tc_ok]
      have hfibreMem : fibres.val[ordinal.val]! ∈ fibres.val := by
        have hbang : fibres.val[ordinal.val]! = fibres.val[ordinal.val] := by
          apply List.getElem!_of_getElem?
          exact List.getElem?_eq_getElem hactive
        rw [hbang]
        exact List.getElem_mem hactive
      have hcapacityStep :
          later.val[round.val]!.val.length + 4 ≤ Std.Usize.max := by
        rw [hlater, List.length_append]
        have hprefixLength :
            (releasedFibresPrefix (alloc.vec.Vec.deref foldedCodeword)
              fibres ordinal.val).length = 4 * ordinal.val := by
          simp [releasedFibresPrefix, releasedPrefix, Nat.mul_comm]
        rw [hprefixLength]
        omega
      have happ := extracted_append_fibre_exact
        (alloc.vec.Vec.deref foldedCodeword) later.val[round.val]!
        round fibres.val[ordinal.val]!
        (hread _ hfibreMem) hcapacityStep
      obtain ⟨appendResult, happRun, happPost⟩ :=
        Aeneas.Std.WP.spec_imp_exists happ
      rcases appendResult with ⟨appendStatus, appended⟩
      rcases happPost with ⟨happendStatus, happended⟩
      change appendStatus = core.result.Result.Ok () at happendStatus
      change appended.val = _ at happended
      rw [happRun]
      simp only [bind_tc_ok]
      rw [happendStatus]
      simp only [core.result.Result.err, bind_tc_ok]
      have hordinalSize : ordinal.val + 1 < Std.Usize.size := by
        have hlenMax := fibres.property
        have hsize : Std.Usize.size = Std.Usize.max + 1 := by
          simp [Std.Usize.size, Std.Usize.max, Std.Usize.numBits]
        rw [hsize]
        omega
      simp only [lift]
      change
        (LaterLoopInvariant (alloc.vec.Vec.deref foldedCodeword)
            fibres initial round
            (later.set round appended,
              Std.Usize.wrapping_add ordinal 1#usize, none) ∧
          fibres.val.length -
              (Std.Usize.wrapping_add ordinal 1#usize).val <
            fibres.val.length - ordinal.val)
      have hnext := wrapping_succ_val ordinal hordinalSize
      constructor
      · constructor
        · rw [hnext]
          omega
        constructor
        · rfl
        constructor
        · rw [selected_after_set later round appended hround,
              happended, hlater, hnext, releasedFibresPrefix_succ]
          simp only [List.append_assoc]
        · intro layer hne
          rw [show
            (later.set round appended).val[layer.val]! =
                later.val[layer.val]! by
              simpa using Array.getElem!_Nat_set_ne later round layer.val
                appended (Ne.symm hne)]
          exact hother layer hne
      · rw [hnext]
        omega
    · have hdone : ordinal.val = fibres.val.length := by omega
      have hnotActive : ¬ ordinal < alloc.vec.Vec.len fibres := by
        simp only [alloc.vec.Vec.len]
        scalar_tac
      rw [if_neg hnotActive]
      change LaterLoopPost (alloc.vec.Vec.deref foldedCodeword)
        fibres initial round (later, none)
      exact ⟨rfl, by simpa [hdone] using hlater, hother⟩
  · constructor
    · simp
    constructor
    · rfl
    constructor
    · simp [releasedFibresPrefix]
    · intro layer _hne
      rfl

#print axioms generated_later_round_loop_exact

/-- Equality form of the loop theorem, convenient for composing with the
source-authentic top-level round trace. -/
theorem generated_later_round_loop_success_exact
    (scheduleFibres : Array (alloc.vec.Vec Std.U32) 3#usize)
    (foldedCodeword : alloc.vec.Vec RawQM31)
    (initial output : RuntimeLater) (round : Std.Usize)
    (fibres : alloc.vec.Vec Std.U32)
    (hround : round.val < 3)
    (hfibres : scheduleFibres.val[round.val]! = fibres)
    (hread : ∀ fibre ∈ fibres.val,
      4 * fibre.val + 4 ≤ foldedCodeword.val.length)
    (hcapacity :
      initial.val[round.val]!.val.length + 4 * fibres.val.length ≤
        Std.Usize.max)
    (hrun :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_round_loop
          scheduleFibres foldedCodeword initial round 0#usize none =
        ok (output, none)) :
    output.val[round.val]!.val =
      initial.val[round.val]!.val ++
        releasedFibresPrefix (alloc.vec.Vec.deref foldedCodeword)
          fibres fibres.val.length := by
  obtain ⟨result, hgenerated, hpost⟩ := Aeneas.Std.WP.spec_imp_exists
    (generated_later_round_loop_exact scheduleFibres foldedCodeword initial
      round fibres hround hfibres hread hcapacity)
  rw [hrun] at hgenerated
  cases hgenerated
  exact hpost.2.1

/-- A later-round traversal mutates only the selected layer. -/
theorem generated_later_round_loop_success_preserves_other
    (scheduleFibres : Array (alloc.vec.Vec Std.U32) 3#usize)
    (foldedCodeword : alloc.vec.Vec RawQM31)
    (initial output : RuntimeLater) (round : Std.Usize)
    (fibres : alloc.vec.Vec Std.U32)
    (hround : round.val < 3)
    (hfibres : scheduleFibres.val[round.val]! = fibres)
    (hread : ∀ fibre ∈ fibres.val,
      4 * fibre.val + 4 ≤ foldedCodeword.val.length)
    (hcapacity :
      initial.val[round.val]!.val.length + 4 * fibres.val.length ≤
        Std.Usize.max)
    (hrun :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_round_loop
          scheduleFibres foldedCodeword initial round 0#usize none =
        ok (output, none)) :
    ∀ layer : Fin 3, layer.val ≠ round.val →
      output.val[layer.val]! = initial.val[layer.val]! := by
  obtain ⟨result, hgenerated, hpost⟩ := Aeneas.Std.WP.spec_imp_exists
    (generated_later_round_loop_exact scheduleFibres foldedCodeword initial
      round fibres hround hfibres hread hcapacity)
  rw [hrun] at hgenerated
  cases hgenerated
  exact hpost.2.2

#print axioms generated_later_round_loop_success_exact
#print axioms generated_later_round_loop_success_preserves_other

/-- Instantiation at the later loop reached by one actual successful generated
runtime round.  The only side conditions are concrete schedule/codeword bounds
needed by the four source reads and vector capacity. -/
theorem generated_runtime_round_trace_later_exact
    (schedule :
      v5_mask.component_c_runtime.V5ComponentCRuntimeSchedule)
    (relation relationOut :
      v5_mask.relation_prover.V5IncrementalRelation)
    (folded foldedOut : alloc.vec.Vec RawQM31)
    (later laterOut : RuntimeLater)
    (tables tablesOut :
      v5_mask.component_c_runtime.V5ComponentCRuntimeRelationTables)
    (round : Std.Usize) (fibres : alloc.vec.Vec Std.U32)
    (htrace : GeneratedRuntimeRoundTrace schedule relation relationOut
      folded foldedOut later laterOut tables tablesOut round)
    (hround : round.val < 3)
    (hfibres : schedule.later_fibres.val[round.val]! = fibres)
    (hread : ∀ fibre ∈ fibres.val,
      4 * fibre.val + 4 ≤ foldedOut.val.length)
    (hcapacity :
      later.val[round.val]!.val.length + 4 * fibres.val.length ≤
        Std.Usize.max) :
    laterOut.val[round.val]!.val =
      later.val[round.val]!.val ++
        releasedFibresPrefix (alloc.vec.Vec.deref foldedOut)
          fibres fibres.val.length := by
  rcases htrace with ⟨_relationTrace, _hfold, hlater, _houter⟩
  have hroundScalar : round < 3#usize := by scalar_tac
  rw [if_pos hroundScalar] at hlater
  exact generated_later_round_loop_success_exact
    schedule.later_fibres foldedOut later laterOut round fibres
    hround hfibres hread hcapacity hlater

#print axioms generated_runtime_round_trace_later_exact

theorem generated_runtime_round_trace_later_preserves_other
    (schedule :
      v5_mask.component_c_runtime.V5ComponentCRuntimeSchedule)
    (relation relationOut :
      v5_mask.relation_prover.V5IncrementalRelation)
    (folded foldedOut : alloc.vec.Vec RawQM31)
    (later laterOut : RuntimeLater)
    (tables tablesOut :
      v5_mask.component_c_runtime.V5ComponentCRuntimeRelationTables)
    (round : Std.Usize) (fibres : alloc.vec.Vec Std.U32)
    (htrace : GeneratedRuntimeRoundTrace schedule relation relationOut
      folded foldedOut later laterOut tables tablesOut round)
    (hround : round.val < 3)
    (hfibres : schedule.later_fibres.val[round.val]! = fibres)
    (hread : ∀ fibre ∈ fibres.val,
      4 * fibre.val + 4 ≤ foldedOut.val.length)
    (hcapacity :
      later.val[round.val]!.val.length + 4 * fibres.val.length ≤
        Std.Usize.max) :
    ∀ layer : Fin 3, layer.val ≠ round.val →
      laterOut.val[layer.val]! = later.val[layer.val]! := by
  rcases htrace with ⟨_relationTrace, _hfold, hlater, _houter⟩
  have hroundScalar : round < 3#usize := by scalar_tac
  rw [if_pos hroundScalar] at hlater
  exact generated_later_round_loop_success_preserves_other
    schedule.later_fibres foldedOut later laterOut round fibres
    hround hfibres hread hcapacity hlater

#print axioms generated_runtime_round_trace_later_preserves_other

end aspis_prover.ComponentCRuntimeLaterRoundLoopCorrespondence
