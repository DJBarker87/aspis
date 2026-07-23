import RuntimeRelationFinishProvenance
import RuntimeRelationRoundTraceProvenance

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeFourRoundReleasedTrace

open aspis_prover
open ComponentCRuntimeRoundDeepControlFlow
open ComponentCRuntimeRelationRoundTraceProvenance

abbrev RawQM31 := aspis_core.field.QM31
abbrev RuntimeSchedule :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeSchedule
abbrev RuntimeRelation :=
  v5_mask.relation_prover.V5IncrementalRelation
abbrev RuntimeTables :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeRelationTables
abbrev RuntimeLater := Array (alloc.vec.Vec RawQM31) 3#usize
abbrev RuntimeTrace := v5_mask.relation_prover.V5RelationTrace

private theorem wrapping_one_one :
    Std.Usize.wrapping_add 1#usize 1#usize = 2#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (2#usize).hSize; scalar_tac)]
  norm_num

private theorem wrapping_two_one :
    Std.Usize.wrapping_add 2#usize 1#usize = 3#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (3#usize).hSize; scalar_tac)]
  norm_num

private theorem wrapping_three_one :
    Std.Usize.wrapping_add 3#usize 1#usize = 4#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (4#usize).hSize; scalar_tac)]
  norm_num

private theorem array_set_get_ne
    {T : Type*} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (value : T) (other : Nat)
    (hne : other ≠ index.val) :
    (values.set index value).val[other]! = values.val[other]! := by
  simp only [Array.set_val_eq]
  apply List.set_getElem!_ne
  exact Or.inr (Or.inl hne)

private theorem two_sample_update_preserves_other
    {T : Type*} [Inhabited T]
    (values : Array (Array T 2#usize) 4#usize)
    (round : Std.Usize) (value0 value1 : T) (other : Nat)
    (hne : other ≠ round.val) :
    let after0 := values.set round
      (values.val[round.val]!.set 0#usize value0)
    let after1 := after0.set round
      (after0.val[round.val]!.set 1#usize value1)
    after1.val[other]! = values.val[other]! := by
  dsimp only
  rw [array_set_get_ne _ round _ other hne]
  exact array_set_get_ne values round _ other hne

/-- Compact witness for the twelve relation coordinates released after four
runtime rounds.  The eight OOD scalars and four complete degree-six messages
are named separately so later code/model arithmetic can bind each family. -/
structure FourRoundReleasedWitness where
  ood00 : RawQM31
  ood01 : RawQM31
  ood10 : RawQM31
  ood11 : RawQM31
  ood20 : RawQM31
  ood21 : RawQM31
  ood30 : RawQM31
  ood31 : RawQM31
  polynomial0 : Array RawQM31 7#usize
  polynomial1 : Array RawQM31 7#usize
  polynomial2 : Array RawQM31 7#usize
  polynomial3 : Array RawQM31 7#usize

def ReleasedCoordinatesMatch
    (oodValues : Array (Array RawQM31 2#usize) 4#usize)
    (sumchecks : Array (Array RawQM31 7#usize) 4#usize)
    (w : FourRoundReleasedWitness) : Prop :=
  oodValues.val[0]!.val[0]! = w.ood00 ∧
  oodValues.val[0]!.val[1]! = w.ood01 ∧
  oodValues.val[1]!.val[0]! = w.ood10 ∧
  oodValues.val[1]!.val[1]! = w.ood11 ∧
  oodValues.val[2]!.val[0]! = w.ood20 ∧
  oodValues.val[2]!.val[1]! = w.ood21 ∧
  oodValues.val[3]!.val[0]! = w.ood30 ∧
  oodValues.val[3]!.val[1]! = w.ood31 ∧
  sumchecks.val[0]! = w.polynomial0 ∧
  sumchecks.val[1]! = w.polynomial1 ∧
  sumchecks.val[2]! = w.polynomial2 ∧
  sumchecks.val[3]! = w.polynomial3

/-- Four actual generated relation-round traces compose to the exact twelve
released coordinates.  Later rounds are proved to preserve earlier rows via
their whole-array update equations; no serializer or table-order premise is
used. -/
theorem generated_four_round_traces_released_coordinates
    (schedule : RuntimeSchedule)
    (relation0 relation1 relation2 relation3 relation4 : RuntimeRelation)
    (tables0 tables1 tables2 tables3 tables4 : RuntimeTables)
    (htrace0 : GeneratedRelationRoundTrace schedule relation0 relation1
      tables0 tables1 0#usize)
    (htrace1 : GeneratedRelationRoundTrace schedule relation1 relation2
      tables1 tables2 1#usize)
    (htrace2 : GeneratedRelationRoundTrace schedule relation2 relation3
      tables2 tables3 2#usize)
    (htrace3 : GeneratedRelationRoundTrace schedule relation3 relation4
      tables3 tables4 3#usize) :
    ∃ w : FourRoundReleasedWitness,
      ReleasedCoordinatesMatch relation4.ood_values relation4.sumchecks w ∧
      relation4.round = 4#usize ∧ relation4.samples = 0#usize := by
  rcases generated_circle_round_trace_released_state
      schedule relation0 relation1 tables0 tables1 htrace0 with
    ⟨_round0Relation1, _round0Relation2, _round0Relation3,
      _point00, _point01,
      v00, v01, _table00, _table01, p0, _polyTable0,
      _hpoint00, _hpoint01, _heval00, _heval01,
      _hcoeff01, _hcoeff02,
      _hpolyCall0, _hpolyStored0,
      _htable00Stored, _htable01Stored,
      hood1, hv00, hv01, hsum1, hp0, hround1, hsamples1⟩
  rcases generated_line_round_trace_released_state
      schedule relation1 relation2 tables1 tables2 1#usize
      (by norm_num) (by norm_num) hround1 hsamples1 htrace1 with
    ⟨_round1Relation1, _round1Relation2, _round1Relation3,
      _layer10, _layer11,
      _layerPoints10, _layerPoints11, _point10, _point11,
      v10, v11, _table10, _table11, p1, _polyTable1,
      _hlayer10, _hlayer11, _hlayerPoints10, _hlayerPoints11,
      _hpoint10, _hpoint11, _heval10, _heval11,
      _hcoeff11, _hcoeff12,
      _hpolyCall1, _hpolyStored1,
      _htable10Stored, _htable11Stored,
      hood2, hv10, hv11, hsum2, hp1, hround2, hsamples2⟩
  have hround2Exact : relation2.round = 2#usize := by
    rw [hround2, wrapping_one_one]
  rcases generated_line_round_trace_released_state
      schedule relation2 relation3 tables2 tables3 2#usize
      (by norm_num) (by norm_num) hround2Exact hsamples2 htrace2 with
    ⟨_round2Relation1, _round2Relation2, _round2Relation3,
      _layer20, _layer21,
      _layerPoints20, _layerPoints21, _point20, _point21,
      v20, v21, _table20, _table21, p2, _polyTable2,
      _hlayer20, _hlayer21, _hlayerPoints20, _hlayerPoints21,
      _hpoint20, _hpoint21, _heval20, _heval21,
      _hcoeff21, _hcoeff22,
      _hpolyCall2, _hpolyStored2,
      _htable20Stored, _htable21Stored,
      hood3, hv20, hv21, hsum3, hp2, hround3, hsamples3⟩
  have hround3Exact : relation3.round = 3#usize := by
    rw [hround3, wrapping_two_one]
  rcases generated_line_round_trace_released_state
      schedule relation3 relation4 tables3 tables4 3#usize
      (by norm_num) (by norm_num) hround3Exact hsamples3 htrace3 with
    ⟨_round3Relation1, _round3Relation2, _round3Relation3,
      _layer30, _layer31,
      _layerPoints30, _layerPoints31, _point30, _point31,
      v30, v31, _table30, _table31, p3, _polyTable3,
      _hlayer30, _hlayer31, _hlayerPoints30, _hlayerPoints31,
      _hpoint30, _hpoint31, _heval30, _heval31,
      _hcoeff31, _hcoeff32,
      _hpolyCall3, _hpolyStored3,
      _htable30Stored, _htable31Stored,
      hood4, hv30, hv31, hsum4, hp3, hround4, hsamples4⟩
  have hood2row0 : relation2.ood_values.val[0]! =
      relation1.ood_values.val[0]! := by
    rw [hood2]
    exact two_sample_update_preserves_other relation1.ood_values 1#usize
      v10 v11 0 (by norm_num)
  have hood3row0 : relation3.ood_values.val[0]! =
      relation2.ood_values.val[0]! := by
    rw [hood3]
    exact two_sample_update_preserves_other relation2.ood_values 2#usize
      v20 v21 0 (by norm_num)
  have hood3row1 : relation3.ood_values.val[1]! =
      relation2.ood_values.val[1]! := by
    rw [hood3]
    exact two_sample_update_preserves_other relation2.ood_values 2#usize
      v20 v21 1 (by norm_num)
  have hood4row0 : relation4.ood_values.val[0]! =
      relation3.ood_values.val[0]! := by
    rw [hood4]
    exact two_sample_update_preserves_other relation3.ood_values 3#usize
      v30 v31 0 (by norm_num)
  have hood4row1 : relation4.ood_values.val[1]! =
      relation3.ood_values.val[1]! := by
    rw [hood4]
    exact two_sample_update_preserves_other relation3.ood_values 3#usize
      v30 v31 1 (by norm_num)
  have hood4row2 : relation4.ood_values.val[2]! =
      relation3.ood_values.val[2]! := by
    rw [hood4]
    exact two_sample_update_preserves_other relation3.ood_values 3#usize
      v30 v31 2 (by norm_num)
  have hsum2row0 : relation2.sumchecks.val[0]! =
      relation1.sumchecks.val[0]! := by
    rw [hsum2]
    exact array_set_get_ne relation1.sumchecks 1#usize p1 0 (by norm_num)
  have hsum3row0 : relation3.sumchecks.val[0]! =
      relation2.sumchecks.val[0]! := by
    rw [hsum3]
    exact array_set_get_ne relation2.sumchecks 2#usize p2 0 (by norm_num)
  have hsum3row1 : relation3.sumchecks.val[1]! =
      relation2.sumchecks.val[1]! := by
    rw [hsum3]
    exact array_set_get_ne relation2.sumchecks 2#usize p2 1 (by norm_num)
  have hsum4row0 : relation4.sumchecks.val[0]! =
      relation3.sumchecks.val[0]! := by
    rw [hsum4]
    exact array_set_get_ne relation3.sumchecks 3#usize p3 0 (by norm_num)
  have hsum4row1 : relation4.sumchecks.val[1]! =
      relation3.sumchecks.val[1]! := by
    rw [hsum4]
    exact array_set_get_ne relation3.sumchecks 3#usize p3 1 (by norm_num)
  have hsum4row2 : relation4.sumchecks.val[2]! =
      relation3.sumchecks.val[2]! := by
    rw [hsum4]
    exact array_set_get_ne relation3.sumchecks 3#usize p3 2 (by norm_num)
  let witness : FourRoundReleasedWitness := {
    ood00 := v00, ood01 := v01, ood10 := v10, ood11 := v11,
    ood20 := v20, ood21 := v21, ood30 := v30, ood31 := v31,
    polynomial0 := p0, polynomial1 := p1,
    polynomial2 := p2, polynomial3 := p3 }
  refine ⟨witness, ?_, ?_, hsamples4⟩
  · unfold ReleasedCoordinatesMatch
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hv30, hv31,
      ?_, ?_, ?_, hp3⟩
    · rw [hood4row0, hood3row0, hood2row0]
      exact hv00
    · rw [hood4row0, hood3row0, hood2row0]
      exact hv01
    · rw [hood4row1, hood3row1]
      exact hv10
    · rw [hood4row1, hood3row1]
      exact hv11
    · rw [hood4row2]
      exact hv20
    · rw [hood4row2]
      exact hv21
    · rw [hsum4row0, hsum3row0, hsum2row0]
      exact hp0
    · rw [hsum4row1, hsum3row1]
      exact hp1
    · rw [hsum4row2]
      exact hp2
  · rw [hround4, wrapping_three_one]

/-- Successful finish copies the exact four-round released arrays into the
public trace, so the same twelve-coordinate witness applies verbatim. -/
theorem generated_finish_preserves_four_round_coordinates
    (relation4 : RuntimeRelation) (trace : RuntimeTrace)
    (w : FourRoundReleasedWitness)
    (hmatch : ReleasedCoordinatesMatch relation4.ood_values relation4.sumchecks w)
    (hfinish : v5_mask.relation_prover.V5IncrementalRelation.finish relation4 =
      ok (core.result.Result.Ok trace)) :
    ReleasedCoordinatesMatch trace.ood_values trace.sumchecks w := by
  rcases ComponentCRuntimeRelationFinishProvenance.generated_finish_success_preserves_released_arrays
      relation4 trace hfinish with ⟨hood, hsumchecks, _⟩
  simpa [hood, hsumchecks] using hmatch

/-- Public-entrypoint trace capstone: a successful authentic execution exposes
all four generated relation rounds, carries their twelve released coordinates
through `finish`, and feeds those exact arrays to the authentic public packer. -/
theorem generated_public_success_has_released_trace
    (schedule : RuntimeSchedule)
    (coefficients codeword : Slice RawQM31)
    (expectedInactiveClaim : RawQM31)
    (output : alloc.vec.Vec RawQM31)
    (hrun :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_private_view
          schedule coefficients codeword expectedInactiveClaim =
        ok (core.result.Result.Ok output)) :
    ∃ later : RuntimeLater, ∃ trace : RuntimeTrace,
    ∃ w : FourRoundReleasedWitness,
      ReleasedCoordinatesMatch trace.ood_values trace.sumchecks w ∧
      v5_mask.component_c_runtime.pack_component_c_runtime_downstream
          trace.ood_values trace.sumchecks later trace.final_coefficients =
        ok (core.result.Result.Ok output) := by
  rcases generated_public_success_has_four_deep_rounds
      schedule coefficients codeword expectedInactiveClaim output hrun with
    ⟨tables, relation0, relation1, relation2, relation3, relation4,
      _folded0, _folded1, _folded2, _folded3, _folded4,
      _later0, _later1, _later2, _later3, later4,
      tables0, tables1, tables2, tables3, trace,
      hround0, hround1, hround2, hround3, hfinish, hpack⟩
  obtain ⟨w, hmatch, _hroundFinal, _hsamplesFinal⟩ :=
    generated_four_round_traces_released_coordinates
      schedule relation0 relation1 relation2 relation3 relation4
      tables0 tables1 tables2 tables3 tables
      hround0.1 hround1.1 hround2.1 hround3.1
  exact ⟨later4, trace, w,
    generated_finish_preserves_four_round_coordinates
      relation4 trace w hmatch hfinish,
    hpack⟩

#print axioms generated_four_round_traces_released_coordinates
#print axioms generated_finish_preserves_four_round_coordinates
#print axioms generated_public_success_has_released_trace

end aspis_prover.ComponentCRuntimeFourRoundReleasedTrace
