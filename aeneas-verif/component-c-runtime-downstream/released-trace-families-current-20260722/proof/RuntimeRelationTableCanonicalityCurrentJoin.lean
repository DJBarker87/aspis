import ComponentCRuntimeGenerated

set_option autoImplicit false

open Aeneas Aeneas.Std Result ControlFlow

namespace aspis_prover.RuntimeRelationTableCanonicality

open aspis_prover

abbrev RawQM31 := aspis_core.field.QM31
abbrev RuntimeError :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeError

local instance : Inhabited RawQM31 := ⟨aspis_core.field.QM31.ZERO⟩

/-- Exact representation predicate enforced by the current Rust validator.
It is deliberately stated over the four raw M31 limbs, before any field-view
quotient can identify a noncanonical word with its reduction. -/
def RuntimeCanonicalQM31 (value : RawQM31) : Prop :=
  value.c0.a < aspis_core.field.P ∧
  value.c0.b < aspis_core.field.P ∧
  value.c1.a < aspis_core.field.P ∧
  value.c1.b < aspis_core.field.P

/-- Every index in a generated relation table has a canonical raw encoding. -/
def RuntimeCanonicalList (values : List RawQM31) : Prop :=
  ∀ index, index < values.length → RuntimeCanonicalQM31 values[index]!

private theorem slice_index_run
    (values : Slice RawQM31) (index : Std.Usize)
    (hindex : index.val < values.val.length) :
    Slice.index_usize values index = ok values.val[index.val]! := by
  unfold Slice.index_usize
  rw [Slice.getElem?_Usize_eq]
  simp [hindex]

private theorem wrapping_succ_exact
    (table : Slice RawQM31) (index : Std.Usize)
    (hindex : index.val < table.val.length) :
    (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  have hlength := Slice.length_ineq table
  change index.val + 1 < UScalar.size .Usize
  rw [UScalar.size_UScalarTyUsize]
  have hsize := Usize.size_scalarTac_eq
  omega

private theorem validator_loop_success_canonical_suffix
    (table : Slice RawQM31) (round : Std.Usize) (slot : Std.U8)
    (index : Std.Usize)
    (hrun :
      v5_mask.component_c_runtime.validate_component_c_runtime_relation_table_loop
          table round slot index = ok (core.result.Result.Ok ())) :
    ∀ position, index.val ≤ position → position < table.val.length →
      RuntimeCanonicalQM31 table.val[position]! := by
  unfold
    v5_mask.component_c_runtime.validate_component_c_runtime_relation_table_loop
    at hrun
  rw [loop.eq_1] at hrun
  unfold
    v5_mask.component_c_runtime.validate_component_c_runtime_relation_table_loop.body
    at hrun
  simp only [] at hrun
  by_cases hactive : index.val < table.val.length
  · have hactiveScalar : index < Slice.len table := by scalar_tac
    rw [if_pos hactiveScalar] at hrun
    rw [slice_index_run table index hactive] at hrun
    simp only [bind_tc_ok] at hrun
    let value := table.val[index.val]!
    by_cases h0 : value.c0.a ≥ aspis_core.field.P
    · rw [if_pos h0] at hrun
      simp at hrun
    · rw [if_neg h0] at hrun
      by_cases h1 : value.c0.b ≥ aspis_core.field.P
      · rw [if_pos h1] at hrun
        simp at hrun
      · rw [if_neg h1] at hrun
        by_cases h2 : value.c1.a ≥ aspis_core.field.P
        · rw [if_pos h2] at hrun
          simp at hrun
        · rw [if_neg h2] at hrun
          by_cases h3 : value.c1.b ≥ aspis_core.field.P
          · rw [if_pos h3] at hrun
            simp at hrun
          · rw [if_neg h3] at hrun
            simp only [Std.lift, bind_tc_ok] at hrun
            have hnext := wrapping_succ_exact table index hactive
            intro position hposition hpositionBound
            by_cases heq : position = index.val
            · subst position
              exact ⟨lt_of_not_ge h0, lt_of_not_ge h1,
                lt_of_not_ge h2, lt_of_not_ge h3⟩
            · have hafter : index.val + 1 ≤ position := by omega
              exact validator_loop_success_canonical_suffix table round slot
                (Std.Usize.wrapping_add index 1#usize) hrun position
                (by simpa [hnext] using hafter) hpositionBound
  · intro position hposition hpositionBound
    omega
termination_by table.val.length - index.val
decreasing_by
  rw [hnext]
  omega

/-- A successful execution of the exact current Rust validator proves the
canonicality invariant required by the maintained direct-C table semantics. -/
theorem generated_validator_success_implies_canonical
    (table : Slice RawQM31) (round : Std.Usize) (slot : Std.U8)
    (hrun :
      v5_mask.component_c_runtime.validate_component_c_runtime_relation_table
          table round slot = ok (core.result.Result.Ok ())) :
    RuntimeCanonicalList table.val := by
  unfold
    v5_mask.component_c_runtime.validate_component_c_runtime_relation_table
    at hrun
  intro position hposition
  exact validator_loop_success_canonical_suffix table round slot 0#usize hrun
    position (by norm_num) hposition

abbrev RuntimeSchedule :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeSchedule
abbrev RuntimeRelation :=
  v5_mask.relation_prover.V5IncrementalRelation
abbrev RuntimeTables :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeRelationTables

private theorem generated_array_index_mut_run
    {T : Type*} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (hindex : index.val < N.val) :
    Array.index_mut_usize values index =
      ok (values.val[index.val]!, values.set index) := by
  obtain ⟨result, hrun, hpost⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_mut_usize_spec values index (by
      simpa [Array.length_eq] using hindex))
  rcases result with ⟨value, restore⟩
  rcases hpost with ⟨hvalue, hrestore⟩
  have harrayBound : index.val < values.val.length := by
    simpa [Array.length_eq] using hindex
  have hbang : values.val[index.val]! = values.val[index.val] := by
    apply List.getElem!_of_getElem?
    exact List.getElem?_eq_getElem harrayBound
  simpa [hvalue, hrestore, hbang] using hrun

private theorem generated_array_index_run
    {T : Type*} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (hindex : index.val < N.val) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, hrun, hvalue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hindex))
  have harrayBound : index.val < values.val.length := by
    simpa [Array.length_eq] using hindex
  have hbang : values.val[index.val]! = values.val[index.val] := by
    apply List.getElem!_of_getElem?
    exact List.getElem?_eq_getElem harrayBound
  simpa [hvalue, hbang] using hrun

private theorem array_set_get_same
    {T : Type*} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (value : T)
    (hindex : index.val < N.val) :
    (values.set index value).val[index.val]! = value := by
  simp only [Array.set_val_eq]
  apply List.set_getElem!_eq
  exact ⟨by simpa [Array.length_eq] using hindex, rfl⟩

private theorem nested_set_get_same
    {T : Type*} [Inhabited T]
    (values : Array (Array T 2#usize) 4#usize)
    (round sample : Std.Usize) (value : T)
    (hround : round.val < 4) (hsample : sample.val < 2) :
    ((values.set round
      ((values.val[round.val]!).set sample value)).val[round.val]!).val[
        sample.val]! = value := by
  rw [array_set_get_same values round
    (values.val[round.val]!.set sample value) hround]
  exact array_set_get_same values.val[round.val]! sample value hsample

/-- Every successful current sample call validates the exact table that it
stores in the selected OOD round/sample slot.  The slot byte is the generated
Rust `sample as u8`, not a free proof parameter. -/
theorem generated_sample_success_validates_stored_table
    (schedule : RuntimeSchedule)
    (relation relationOut : RuntimeRelation)
    (tables tablesOut : RuntimeTables)
    (round sample : Std.Usize)
    (hround : round.val < 4) (hsample : sample.val < 2)
    (hrun :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_sample
          schedule relation tables round sample =
        ok (core.result.Result.Ok (), relationOut, tablesOut)) :
    ∃ table slotValue,
      lift (UScalar.cast .U8 sample) = ok slotValue ∧
      v5_mask.component_c_runtime.validate_component_c_runtime_relation_table
          (alloc.vec.Vec.deref table) round slotValue =
        ok (core.result.Result.Ok ()) ∧
      tablesOut.ood.val[round.val]!.val[sample.val]! = table ∧
      tablesOut.ood =
        tables.ood.set round
          (tables.ood.val[round.val]!.set sample table) ∧
      tablesOut.polynomial = tables.polynomial := by
  unfold
    v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_sample
    at hrun
  by_cases hroundZero : round = 0#usize
  · rw [if_pos hroundZero] at hrun
    generalize hpoint :
        Array.index_usize schedule.circle_ood_points sample = pointResult
      at hrun
    cases pointResult with
    | fail error => simp at hrun
    | div => simp at hrun
    | ok point =>
      simp only [bind_tc_ok] at hrun
      generalize hood :
          v5_mask.relation_prover.V5IncrementalRelation.evaluate_circle_ood_with_table
              relation point = oodResult at hrun
      cases oodResult with
      | fail error => simp at hrun
      | div => simp at hrun
      | ok oodStatus =>
        cases oodStatus with
        | Err oodError =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            v5_mask.component_c_runtime.V5ComponentCRuntimeError.Insts.CoreConvertFromV5RelationProverError.from]
            at hrun
        | Ok oodPayload =>
          rcases oodPayload with ⟨value, table⟩
          simp only [bind_tc_ok,
            core.result.Result.Insts.CoreOpsTry.branch] at hrun
          generalize hcast : lift (UScalar.cast .U8 sample) = castResult at hrun
          cases castResult with
          | fail error => simp at hrun
          | div => simp at hrun
          | ok slotValue =>
            simp only [bind_tc_ok] at hrun
            generalize hvalidate :
                v5_mask.component_c_runtime.validate_component_c_runtime_relation_table
                    (alloc.vec.Vec.deref table) round slotValue = validateResult
              at hrun
            cases validateResult with
            | fail error => simp at hrun
            | div => simp at hrun
            | ok validateStatus =>
              cases validateStatus with
              | Err validateError =>
                simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  core.convert.FromSame.from] at hrun
              | Ok validatePayload =>
                rcases validatePayload with ⟨⟩
                simp only [bind_tc_ok] at hrun
                have hroundScalar : round < 4#usize := by scalar_tac
                have hsampleScalar : sample < 2#usize := by scalar_tac
                simp only [massert, hroundScalar, hsampleScalar] at hrun
                rw [generated_array_index_mut_run tables.ood round hround] at hrun
                simp only [bind_tc_ok] at hrun
                rw [generated_array_index_mut_run
                  tables.ood.val[round.val]! sample hsample] at hrun
                simp only [bind_tc_ok] at hrun
                let restored0 := tables.ood.set round
                  (tables.ood.val[round.val]!.set sample
                    tables.ood.val[round.val]!.val[sample.val]!)
                rw [generated_array_index_mut_run restored0 round hround] at hrun
                simp only [bind_tc_ok] at hrun
                rw [generated_array_index_mut_run
                  restored0.val[round.val]! sample hsample] at hrun
                simp only [bind_tc_ok] at hrun
                rw [generated_array_index_run schedule.ood_mixes round hround]
                  at hrun
                simp only [bind_tc_ok] at hrun
                rw [generated_array_index_run
                  schedule.ood_mixes.val[round.val]! sample hsample] at hrun
                simp only [bind_tc_ok] at hrun
                generalize hadd :
                    v5_mask.relation_prover.V5IncrementalRelation.add_circle_ood
                        relation point value
                          schedule.ood_mixes.val[round.val]!.val[sample.val]! =
                      addResult at hrun
                cases addResult with
                | fail error => simp at hrun
                | div => simp at hrun
                | ok addTuple =>
                  rcases addTuple with ⟨addStatus, relationAfter⟩
                  cases addStatus with
                  | Err addError =>
                    simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                      v5_mask.component_c_runtime.V5ComponentCRuntimeError.Insts.CoreConvertFromV5RelationProverError.from]
                      at hrun
                  | Ok addPayload =>
                    rcases addPayload with ⟨⟩
                    simp only [bind_tc_ok] at hrun
                    cases hrun
                    refine ⟨table, slotValue, rfl, hvalidate,
                      nested_set_get_same restored0 round sample table
                        hround hsample, ?_, rfl⟩
                    have hrestored : restored0 = tables.ood := by
                      dsimp [restored0]
                      rw [Array.set_getElem!_eq, Array.set_getElem!_eq]
                    change restored0.set round
                      (restored0.val[round.val]!.set sample table) =
                        tables.ood.set round
                          (tables.ood.val[round.val]!.set sample table)
                    rw [hrestored]
  · rw [if_neg hroundZero] at hrun
    generalize hlayer : lift (Std.Usize.wrapping_sub round 1#usize) = layerResult
      at hrun
    cases layerResult with
    | fail error => simp at hrun
    | div => simp at hrun
    | ok layer =>
      simp only [bind_tc_ok] at hrun
      generalize hlayerPoints :
          Array.index_usize schedule.line_ood_points layer = layerPointsResult
        at hrun
      cases layerPointsResult with
      | fail error => simp at hrun
      | div => simp at hrun
      | ok layerPoints =>
        simp only [bind_tc_ok] at hrun
        generalize hpoint : Array.index_usize layerPoints sample = pointResult
          at hrun
        cases pointResult with
        | fail error => simp at hrun
        | div => simp at hrun
        | ok point =>
          simp only [bind_tc_ok] at hrun
          generalize hood :
              v5_mask.relation_prover.V5IncrementalRelation.evaluate_line_ood_with_table
                  relation point = oodResult at hrun
          cases oodResult with
          | fail error => simp at hrun
          | div => simp at hrun
          | ok oodStatus =>
            cases oodStatus with
            | Err oodError =>
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                v5_mask.component_c_runtime.V5ComponentCRuntimeError.Insts.CoreConvertFromV5RelationProverError.from]
                at hrun
            | Ok oodPayload =>
              rcases oodPayload with ⟨value, table⟩
              simp only [bind_tc_ok,
                core.result.Result.Insts.CoreOpsTry.branch] at hrun
              generalize hcast : lift (UScalar.cast .U8 sample) = castResult at hrun
              cases castResult with
              | fail error => simp at hrun
              | div => simp at hrun
              | ok slotValue =>
                simp only [bind_tc_ok] at hrun
                generalize hvalidate :
                    v5_mask.component_c_runtime.validate_component_c_runtime_relation_table
                        (alloc.vec.Vec.deref table) round slotValue = validateResult
                  at hrun
                cases validateResult with
                | fail error => simp at hrun
                | div => simp at hrun
                | ok validateStatus =>
                  cases validateStatus with
                  | Err validateError =>
                    simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                      core.convert.FromSame.from] at hrun
                  | Ok validatePayload =>
                    rcases validatePayload with ⟨⟩
                    simp only [bind_tc_ok] at hrun
                    have hroundScalar : round < 4#usize := by scalar_tac
                    have hsampleScalar : sample < 2#usize := by scalar_tac
                    simp only [massert, hroundScalar, hsampleScalar] at hrun
                    rw [generated_array_index_mut_run tables.ood round hround]
                      at hrun
                    simp only [bind_tc_ok] at hrun
                    rw [generated_array_index_mut_run
                      tables.ood.val[round.val]! sample hsample] at hrun
                    simp only [bind_tc_ok] at hrun
                    let restored0 := tables.ood.set round
                      (tables.ood.val[round.val]!.set sample
                        tables.ood.val[round.val]!.val[sample.val]!)
                    rw [generated_array_index_mut_run restored0 round hround]
                      at hrun
                    simp only [bind_tc_ok] at hrun
                    rw [generated_array_index_mut_run
                      restored0.val[round.val]! sample hsample] at hrun
                    simp only [bind_tc_ok] at hrun
                    rw [generated_array_index_run schedule.ood_mixes round hround]
                      at hrun
                    simp only [bind_tc_ok] at hrun
                    rw [generated_array_index_run
                      schedule.ood_mixes.val[round.val]! sample hsample] at hrun
                    simp only [bind_tc_ok] at hrun
                    generalize hadd :
                        v5_mask.relation_prover.V5IncrementalRelation.add_line_ood
                            relation point value
                              schedule.ood_mixes.val[round.val]!.val[sample.val]! =
                          addResult at hrun
                    cases addResult with
                    | fail error => simp at hrun
                    | div => simp at hrun
                    | ok addTuple =>
                      rcases addTuple with ⟨addStatus, relationAfter⟩
                      cases addStatus with
                      | Err addError =>
                        simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                          v5_mask.component_c_runtime.V5ComponentCRuntimeError.Insts.CoreConvertFromV5RelationProverError.from]
                          at hrun
                      | Ok addPayload =>
                        rcases addPayload with ⟨⟩
                        simp only [bind_tc_ok] at hrun
                        cases hrun
                        refine ⟨table, slotValue, rfl, hvalidate,
                          nested_set_get_same restored0 round sample table
                            hround hsample, ?_, rfl⟩
                        have hrestored : restored0 = tables.ood := by
                          dsimp [restored0]
                          rw [Array.set_getElem!_eq, Array.set_getElem!_eq]
                        change restored0.set round
                          (restored0.val[round.val]!.set sample table) =
                            tables.ood.set round
                              (tables.ood.val[round.val]!.set sample table)
                        rw [hrestored]

/-- Consequently, every table successfully stored by an OOD sample is
canonical in all four base-field limbs. -/
theorem generated_sample_success_stores_canonical_table
    (schedule : RuntimeSchedule)
    (relation relationOut : RuntimeRelation)
    (tables tablesOut : RuntimeTables)
    (round sample : Std.Usize)
    (hround : round.val < 4) (hsample : sample.val < 2)
    (hrun :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_sample
          schedule relation tables round sample =
        ok (core.result.Result.Ok (), relationOut, tablesOut)) :
    RuntimeCanonicalList
      tablesOut.ood.val[round.val]!.val[sample.val]!.val := by
  obtain ⟨table, slotValue, _, hvalidate, hstored, _, _⟩ :=
    generated_sample_success_validates_stored_table schedule relation relationOut
      tables tablesOut round sample hround hsample hrun
  rw [hstored]
  exact generated_validator_success_implies_canonical
    (alloc.vec.Vec.deref table) round slotValue hvalidate

private theorem array_set_get_other
    {T : Type*} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index target : Std.Usize) (value : T)
    (hne : index.val ≠ target.val) :
    (values.set index value).val[target.val]! = values.val[target.val]! := by
  simp only [Array.set_val_eq]
  exact List.set_getElem!_ne values.val index.val target.val value (Or.inl hne)

private theorem nested_set_get_other
    {T : Type*} [Inhabited T]
    (values : Array (Array T 2#usize) 4#usize)
    (round sample targetRound targetSample : Std.Usize) (value : T)
    (hround : round.val < 4) (htargetRound : targetRound.val < 4)
    (hother : targetRound ≠ round ∨ targetSample ≠ sample) :
    ((values.set round
      (values.val[round.val]!.set sample value)).val[targetRound.val]!).val[
        targetSample.val]! =
      values.val[targetRound.val]!.val[targetSample.val]! := by
  by_cases hsameRound : targetRound = round
  · subst targetRound
    rw [array_set_get_same values round
      (values.val[round.val]!.set sample value) hround]
    have hsampleNe : sample.val ≠ targetSample.val := by
      intro heq
      have hscalar : sample = targetSample := by
        apply UScalar.eq_of_val_eq
        exact heq
      exact hother.elim (fun h => h rfl) (fun h => h hscalar.symm)
    exact array_set_get_other values.val[round.val]!
      sample targetSample value hsampleNe
  · have hroundNe : round.val ≠ targetRound.val := by
      intro heq
      apply hsameRound
      apply UScalar.eq_of_val_eq
      exact heq.symm
    rw [array_set_get_other values round targetRound
      (values.val[round.val]!.set sample value) hroundNe]

/-- A successful sample update changes no OOD coordinate other than its exact
selected round/sample slot, and never changes the polynomial table array. -/
theorem generated_sample_success_preserves_other_tables
    (schedule : RuntimeSchedule)
    (relation relationOut : RuntimeRelation)
    (tables tablesOut : RuntimeTables)
    (round sample targetRound targetSample : Std.Usize)
    (hround : round.val < 4) (hsample : sample.val < 2)
    (htargetRound : targetRound.val < 4)
    (hother : targetRound ≠ round ∨ targetSample ≠ sample)
    (hrun :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_sample
          schedule relation tables round sample =
        ok (core.result.Result.Ok (), relationOut, tablesOut)) :
    tablesOut.ood.val[targetRound.val]!.val[targetSample.val]! =
        tables.ood.val[targetRound.val]!.val[targetSample.val]! ∧
      tablesOut.polynomial = tables.polynomial := by
  obtain ⟨table, _, _, _, _, htables, hpolynomial⟩ :=
    generated_sample_success_validates_stored_table schedule relation relationOut
      tables tablesOut round sample hround hsample hrun
  rw [htables]
  exact ⟨nested_set_get_other tables.ood round sample targetRound targetSample
    table hround htargetRound hother, hpolynomial⟩

/-- If the target round differs, the sample setter preserves the entire
two-table OOD row at once. -/
theorem generated_sample_success_preserves_other_round
    (schedule : RuntimeSchedule)
    (relation relationOut : RuntimeRelation)
    (tables tablesOut : RuntimeTables)
    (round sample targetRound : Std.Usize)
    (hround : round.val < 4) (hsample : sample.val < 2)
    (htargetRound : targetRound.val < 4)
    (htargetNe : targetRound ≠ round)
    (hrun :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_sample
          schedule relation tables round sample =
        ok (core.result.Result.Ok (), relationOut, tablesOut)) :
    tablesOut.ood.val[targetRound.val]! =
        tables.ood.val[targetRound.val]! ∧
      tablesOut.polynomial = tables.polynomial := by
  obtain ⟨table, _, _, _, _, htables, hpolynomial⟩ :=
    generated_sample_success_validates_stored_table schedule relation relationOut
      tables tablesOut round sample hround hsample hrun
  have hvalNe : round.val ≠ targetRound.val := by
    intro heq
    apply htargetNe
    apply UScalar.eq_of_val_eq
    exact heq.symm
  rw [htables,
    array_set_get_other tables.ood round targetRound
      (tables.ood.val[round.val]!.set sample table) hvalNe]
  exact ⟨rfl, hpolynomial⟩

/-- Inverting a successful current relation round exposes both successful OOD
sample transitions and the exact validated polynomial table setter. -/
theorem generated_round_success_decomposes_validated
    (schedule : RuntimeSchedule)
    (relation0 relationOut : RuntimeRelation)
    (tables0 tablesOut : RuntimeTables)
    (round : Std.Usize)
    (hrun :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_round
          schedule relation0 tables0 round =
        ok (core.result.Result.Ok (), relationOut, tablesOut)) :
    ∃ relation1 relation2 relation3,
    ∃ tables1 tables2 : RuntimeTables,
    ∃ polynomial : Array RawQM31 7#usize,
    ∃ table : alloc.vec.Vec RawQM31,
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_sample
          schedule relation0 tables0 round 0#usize =
        ok (core.result.Result.Ok (), relation1, tables1) ∧
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_sample
          schedule relation1 tables1 round 1#usize =
        ok (core.result.Result.Ok (), relation2, tables2) ∧
      v5_mask.relation_prover.V5IncrementalRelation.polynomial_with_table
          relation2 =
        ok (core.result.Result.Ok (polynomial, table), relation3) ∧
      v5_mask.component_c_runtime.validate_component_c_runtime_relation_table
          (alloc.vec.Vec.deref table) round 2#u8 =
        ok (core.result.Result.Ok ()) ∧
      round.val < 4 ∧
      tablesOut.ood = tables2.ood ∧
      tablesOut.polynomial = tables2.polynomial.set round table := by
  unfold
    v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_round
    at hrun
  generalize hsample0 :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_sample
          schedule relation0 tables0 round 0#usize = sample0Result at hrun
  cases sample0Result with
  | fail error => simp at hrun
  | div => simp at hrun
  | ok sample0Tuple =>
    rcases sample0Tuple with ⟨sample0Status, relation1, tables1⟩
    cases sample0Status with
    | Err sample0Error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at hrun
    | Ok sample0Payload =>
      rcases sample0Payload with ⟨⟩
      simp only [bind_tc_ok,
        core.result.Result.Insts.CoreOpsTry.branch] at hrun
      generalize hsample1 :
          v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_sample
              schedule relation1 tables1 round 1#usize = sample1Result at hrun
      cases sample1Result with
      | fail error => simp at hrun
      | div => simp at hrun
      | ok sample1Tuple =>
        rcases sample1Tuple with ⟨sample1Status, relation2, tables2⟩
        cases sample1Status with
        | Err sample1Error =>
          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at hrun
        | Ok sample1Payload =>
          rcases sample1Payload with ⟨⟩
          simp only [bind_tc_ok] at hrun
          generalize hpolynomial :
              v5_mask.relation_prover.V5IncrementalRelation.polynomial_with_table
                  relation2 = polynomialResult at hrun
          cases polynomialResult with
          | fail error => simp at hrun
          | div => simp at hrun
          | ok polynomialTuple =>
            rcases polynomialTuple with ⟨polynomialStatus, relation3⟩
            cases polynomialStatus with
            | Err polynomialError =>
              simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                v5_mask.component_c_runtime.V5ComponentCRuntimeError.Insts.CoreConvertFromV5RelationProverError.from]
                at hrun
            | Ok polynomialPayload =>
              rcases polynomialPayload with ⟨polynomial, table⟩
              simp only [bind_tc_ok] at hrun
              generalize hvalidate :
                  v5_mask.component_c_runtime.validate_component_c_runtime_relation_table
                      (alloc.vec.Vec.deref table) round 2#u8 = validateResult
                at hrun
              cases validateResult with
              | fail error => simp at hrun
              | div => simp at hrun
              | ok validateStatus =>
                cases validateStatus with
                | Err validateError =>
                  simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame.from] at hrun
                | Ok validatePayload =>
                  rcases validatePayload with ⟨⟩
                  simp only [bind_tc_ok] at hrun
                  by_cases hround : round < 4#usize
                  · simp only [massert, hround] at hrun
                    rw [generated_array_index_mut_run tables2.polynomial round
                      (by scalar_tac)] at hrun
                    simp only [bind_tc_ok] at hrun
                    let restored := tables2.polynomial.set round
                      tables2.polynomial.val[round.val]!
                    rw [generated_array_index_mut_run restored round
                      (by scalar_tac)] at hrun
                    simp only [bind_tc_ok] at hrun
                    generalize halpha :
                        Array.index_usize schedule.alphas round = alphaResult
                      at hrun
                    cases alphaResult with
                    | fail error => simp at hrun
                    | div => simp at hrun
                    | ok alpha =>
                      simp only [bind_tc_ok] at hrun
                      generalize hfold :
                          v5_mask.relation_prover.V5IncrementalRelation.fold
                              relation3 alpha = foldResult at hrun
                      cases foldResult with
                      | fail error => simp at hrun
                      | div => simp at hrun
                      | ok foldTuple =>
                        rcases foldTuple with ⟨foldStatus, relationAfter⟩
                        cases foldStatus with
                        | Err foldError =>
                          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                            v5_mask.component_c_runtime.V5ComponentCRuntimeError.Insts.CoreConvertFromV5RelationProverError.from]
                            at hrun
                        | Ok foldPayload =>
                          rcases foldPayload with ⟨⟩
                          simp only [bind_tc_ok] at hrun
                          cases hrun
                          refine ⟨relation1, relation2, relation3,
                            tables1, tables2, polynomial, table,
                            by simp,
                            by simpa using hsample1,
                            by simpa using hpolynomial,
                            by simpa using hvalidate,
                            by scalar_tac, rfl, ?_⟩
                          have hrestored : restored = tables2.polynomial := by
                            dsimp [restored]
                            rw [Array.set_getElem!_eq]
                          change restored.set round table =
                            tables2.polynomial.set round table
                          rw [hrestored]
                  · simp [massert, hround] at hrun

/-- The polynomial relation table stored by a successful round is canonical
in all four raw limbs. -/
theorem generated_round_success_stores_canonical_polynomial
    (schedule : RuntimeSchedule)
    (relation0 relationOut : RuntimeRelation)
    (tables0 tablesOut : RuntimeTables)
    (round : Std.Usize)
    (hrun :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_round
          schedule relation0 tables0 round =
        ok (core.result.Result.Ok (), relationOut, tablesOut)) :
    RuntimeCanonicalList tablesOut.polynomial.val[round.val]!.val := by
  obtain ⟨_, _, _, _, tables2, _, table, _, _, _, hvalidate,
      hround, _, htables⟩ :=
    generated_round_success_decomposes_validated schedule relation0 relationOut
      tables0 tablesOut round hrun
  rw [htables, array_set_get_same tables2.polynomial round table hround]
  exact generated_validator_success_implies_canonical
    (alloc.vec.Vec.deref table) round 2#u8 hvalidate

/-- Both OOD tables stored by a successful round are canonical in the final
round output, including preservation of sample zero across the sample-one
setter. -/
theorem generated_round_success_stores_canonical_ood
    (schedule : RuntimeSchedule)
    (relation0 relationOut : RuntimeRelation)
    (tables0 tablesOut : RuntimeTables)
    (round : Std.Usize)
    (hrun :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_round
          schedule relation0 tables0 round =
        ok (core.result.Result.Ok (), relationOut, tablesOut)) :
    ∀ sample : Fin 2,
      RuntimeCanonicalList
        tablesOut.ood.val[round.val]!.val[sample.val]!.val := by
  obtain ⟨relation1, relation2, _, tables1, tables2, _, _,
      hsample0, hsample1, _, _, hround, htables, _⟩ :=
    generated_round_success_decomposes_validated schedule relation0 relationOut
      tables0 tablesOut round hrun
  have hcanonical0 : RuntimeCanonicalList
      tables1.ood.val[round.val]!.val[0]!.val :=
    generated_sample_success_stores_canonical_table schedule relation0 relation1
      tables0 tables1 round 0#usize hround (by norm_num) hsample0
  have hpreserved0 :=
    (generated_sample_success_preserves_other_tables schedule relation1 relation2
      tables1 tables2 round 1#usize round 0#usize hround (by norm_num)
      hround (Or.inr (by norm_num)) hsample1).1
  change tables2.ood.val[round.val]!.val[0]! =
    tables1.ood.val[round.val]!.val[0]! at hpreserved0
  have hcanonical0After : RuntimeCanonicalList
      tables2.ood.val[round.val]!.val[0]!.val := by
    rw [hpreserved0]
    exact hcanonical0
  have hcanonical1 : RuntimeCanonicalList
      tables2.ood.val[round.val]!.val[1]!.val :=
    generated_sample_success_stores_canonical_table schedule relation1 relation2
      tables1 tables2 round 1#usize hround (by norm_num) hsample1
  intro sample
  rw [htables]
  fin_cases sample
  · exact hcanonical0After
  · exact hcanonical1

/-- A round setter preserves every OOD and polynomial table belonging to a
different round. -/
theorem generated_round_success_preserves_other_round
    (schedule : RuntimeSchedule)
    (relation0 relationOut : RuntimeRelation)
    (tables0 tablesOut : RuntimeTables)
    (round targetRound targetSample : Std.Usize)
    (htargetRound : targetRound.val < 4)
    (htargetNe : targetRound ≠ round)
    (hrun :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_round
          schedule relation0 tables0 round =
        ok (core.result.Result.Ok (), relationOut, tablesOut)) :
    tablesOut.ood.val[targetRound.val]!.val[targetSample.val]! =
        tables0.ood.val[targetRound.val]!.val[targetSample.val]! ∧
      tablesOut.polynomial.val[targetRound.val]! =
        tables0.polynomial.val[targetRound.val]! := by
  obtain ⟨relation1, relation2, _, tables1, tables2, _, table,
      hsample0, hsample1, _, _, hround, htables, hpolynomial⟩ :=
    generated_round_success_decomposes_validated schedule relation0 relationOut
      tables0 tablesOut round hrun
  have hpreserve0 :=
    generated_sample_success_preserves_other_tables schedule relation0 relation1
      tables0 tables1 round 0#usize targetRound targetSample hround
      (by norm_num) htargetRound (Or.inl htargetNe) hsample0
  have hpreserve1 :=
    generated_sample_success_preserves_other_tables schedule relation1 relation2
      tables1 tables2 round 1#usize targetRound targetSample hround
      (by norm_num) htargetRound (Or.inl htargetNe) hsample1
  have hvalNe : round.val ≠ targetRound.val := by
    intro heq
    apply htargetNe
    apply UScalar.eq_of_val_eq
    exact heq.symm
  constructor
  · rw [htables, hpreserve1.1, hpreserve0.1]
  · rw [hpolynomial,
      array_set_get_other tables2.polynomial round targetRound table hvalNe,
      hpreserve1.2, hpreserve0.2]

/-- Whole-row form used to carry an already-certified earlier round through
later successful rounds. -/
theorem generated_round_success_preserves_other_round_row
    (schedule : RuntimeSchedule)
    (relation0 relationOut : RuntimeRelation)
    (tables0 tablesOut : RuntimeTables)
    (round targetRound : Std.Usize)
    (htargetRound : targetRound.val < 4)
    (htargetNe : targetRound ≠ round)
    (hrun :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_round
          schedule relation0 tables0 round =
        ok (core.result.Result.Ok (), relationOut, tablesOut)) :
    tablesOut.ood.val[targetRound.val]! =
        tables0.ood.val[targetRound.val]! ∧
      tablesOut.polynomial.val[targetRound.val]! =
        tables0.polynomial.val[targetRound.val]! := by
  obtain ⟨relation1, relation2, _, tables1, tables2, _, table,
      hsample0, hsample1, _, _, hround, htables, hpolynomial⟩ :=
    generated_round_success_decomposes_validated schedule relation0 relationOut
      tables0 tablesOut round hrun
  have hpreserve0 :=
    generated_sample_success_preserves_other_round schedule relation0 relation1
      tables0 tables1 round 0#usize targetRound hround (by norm_num)
      htargetRound htargetNe hsample0
  have hpreserve1 :=
    generated_sample_success_preserves_other_round schedule relation1 relation2
      tables1 tables2 round 1#usize targetRound hround (by norm_num)
      htargetRound htargetNe hsample1
  have hvalNe : round.val ≠ targetRound.val := by
    intro heq
    apply htargetNe
    apply UScalar.eq_of_val_eq
    exact heq.symm
  constructor
  · rw [htables, hpreserve1.1, hpreserve0.1]
  · rw [hpolynomial,
      array_set_get_other tables2.polynomial round targetRound table hvalNe,
      hpreserve1.2, hpreserve0.2]

/-! ## Actual four-round canonicality capstone -/

def GeneratedRelationTablesCanonical (tables : RuntimeTables) : Prop :=
  ∀ round : Fin 4,
    (∀ sample : Fin 2,
      RuntimeCanonicalList
        tables.ood.val[round.val]!.val[sample.val]!.val) ∧
    RuntimeCanonicalList tables.polynomial.val[round.val]!.val

private theorem runtimeCanonicalList_vec_transport
    {left right : alloc.vec.Vec RawQM31}
    (h : left = right) (hright : RuntimeCanonicalList right.val) :
    RuntimeCanonicalList left.val := by
  cases h
  exact hright

theorem generated_four_relation_rounds_tables_canonical
    (schedule : RuntimeSchedule)
    (relation0 relation1 relation2 relation3 relation4 : RuntimeRelation)
    (tables0 tables1 tables2 tables3 tables4 : RuntimeTables)
    (hrun0 :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_round
          schedule relation0 tables0 0#usize =
        ok (core.result.Result.Ok (), relation1, tables1))
    (hrun1 :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_round
          schedule relation1 tables1 1#usize =
        ok (core.result.Result.Ok (), relation2, tables2))
    (hrun2 :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_round
          schedule relation2 tables2 2#usize =
        ok (core.result.Result.Ok (), relation3, tables3))
    (hrun3 :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_round
          schedule relation3 tables3 3#usize =
        ok (core.result.Result.Ok (), relation4, tables4)) :
    GeneratedRelationTablesCanonical tables4 := by
  have hood0 := generated_round_success_stores_canonical_ood
    schedule relation0 relation1 tables0 tables1 0#usize hrun0
  have hood1 := generated_round_success_stores_canonical_ood
    schedule relation1 relation2 tables1 tables2 1#usize hrun1
  have hood2 := generated_round_success_stores_canonical_ood
    schedule relation2 relation3 tables2 tables3 2#usize hrun2
  have hood3 := generated_round_success_stores_canonical_ood
    schedule relation3 relation4 tables3 tables4 3#usize hrun3
  have hpoly0 := generated_round_success_stores_canonical_polynomial
    schedule relation0 relation1 tables0 tables1 0#usize hrun0
  have hpoly1 := generated_round_success_stores_canonical_polynomial
    schedule relation1 relation2 tables1 tables2 1#usize hrun1
  have hpoly2 := generated_round_success_stores_canonical_polynomial
    schedule relation2 relation3 tables2 tables3 2#usize hrun2
  have hpoly3 := generated_round_success_stores_canonical_polynomial
    schedule relation3 relation4 tables3 tables4 3#usize hrun3
  have h10 := generated_round_success_preserves_other_round_row
    schedule relation1 relation2 tables1 tables2 1#usize 0#usize
      (by norm_num) (by norm_num) hrun1
  have h20 := generated_round_success_preserves_other_round_row
    schedule relation2 relation3 tables2 tables3 2#usize 0#usize
      (by norm_num) (by norm_num) hrun2
  have h21 := generated_round_success_preserves_other_round_row
    schedule relation2 relation3 tables2 tables3 2#usize 1#usize
      (by norm_num) (by norm_num) hrun2
  have h30 := generated_round_success_preserves_other_round_row
    schedule relation3 relation4 tables3 tables4 3#usize 0#usize
      (by norm_num) (by norm_num) hrun3
  have h31 := generated_round_success_preserves_other_round_row
    schedule relation3 relation4 tables3 tables4 3#usize 1#usize
      (by norm_num) (by norm_num) hrun3
  have h32 := generated_round_success_preserves_other_round_row
    schedule relation3 relation4 tables3 tables4 3#usize 2#usize
      (by norm_num) (by norm_num) hrun3
  intro round
  have hcases : round.val = 0 ∨ round.val = 1 ∨
      round.val = 2 ∨ round.val = 3 := by omega
  rcases hcases with hround | hround | hround | hround
  · have hr : round = 0 := Fin.eq_of_val_eq hround
    subst round
    constructor
    · intro sample
      apply runtimeCanonicalList_vec_transport
        (right := tables1.ood.val[(0#usize).val]!.val[sample.val]!)
      · exact (congrArg (fun row => row.val[sample.val]!) h30.1).trans
          ((congrArg (fun row => row.val[sample.val]!) h20.1).trans
            (congrArg (fun row => row.val[sample.val]!) h10.1))
      · exact hood0 sample
    · apply runtimeCanonicalList_vec_transport
        (right := tables1.polynomial.val[(0#usize).val]!)
      · exact h30.2.trans (h20.2.trans h10.2)
      · exact hpoly0
  · have hr : round = 1 := Fin.eq_of_val_eq hround
    subst round
    constructor
    · intro sample
      apply runtimeCanonicalList_vec_transport
        (right := tables2.ood.val[(1#usize).val]!.val[sample.val]!)
      · exact (congrArg (fun row => row.val[sample.val]!) h31.1).trans
          (congrArg (fun row => row.val[sample.val]!) h21.1)
      · exact hood1 sample
    · apply runtimeCanonicalList_vec_transport
        (right := tables2.polynomial.val[(1#usize).val]!)
      · exact h31.2.trans h21.2
      · exact hpoly1
  · have hr : round = 2 := Fin.eq_of_val_eq hround
    subst round
    constructor
    · intro sample
      apply runtimeCanonicalList_vec_transport
        (right := tables3.ood.val[(2#usize).val]!.val[sample.val]!)
      · exact congrArg (fun row => row.val[sample.val]!) h32.1
      · exact hood2 sample
    · apply runtimeCanonicalList_vec_transport
        (right := tables3.polynomial.val[(2#usize).val]!)
      · exact h32.2
      · exact hpoly2
  · have hr : round = 3 := Fin.eq_of_val_eq hround
    subst round
    exact ⟨hood3, hpoly3⟩

#print axioms generated_four_relation_rounds_tables_canonical

/-- Permanent negative tooth: the public raw QM31 representation can encode
the modulus itself, and the validator rejects that encoding. -/
def noncanonicalRawQM31 : RawQM31 :=
  { c0 := { a := 2147483647#u32, b := 0#u32 }
    c1 := { a := 0#u32, b := 0#u32 } }

theorem noncanonical_raw_qm31_tooth :
    ¬ RuntimeCanonicalQM31 noncanonicalRawQM31 := by
  norm_num [RuntimeCanonicalQM31, noncanonicalRawQM31, aspis_core.field.P]

theorem generated_validator_rejects_noncanonical_tooth
    (round : Std.Usize) (slot : Std.U8) :
    v5_mask.component_c_runtime.validate_component_c_runtime_relation_table
        ⟨[noncanonicalRawQM31], by simp; scalar_tac⟩ round slot =
      ok (core.result.Result.Err
        (v5_mask.component_c_runtime.V5ComponentCRuntimeError.NonCanonicalRelationTable
          round slot 0#usize)) := by
  unfold
    v5_mask.component_c_runtime.validate_component_c_runtime_relation_table
    v5_mask.component_c_runtime.validate_component_c_runtime_relation_table_loop
  rw [loop.eq_1]
  unfold
    v5_mask.component_c_runtime.validate_component_c_runtime_relation_table_loop.body
  norm_num [noncanonicalRawQM31, aspis_core.field.P, Slice.index_usize]

#print axioms generated_validator_success_implies_canonical
#print axioms generated_sample_success_validates_stored_table
#print axioms generated_sample_success_stores_canonical_table
#print axioms noncanonical_raw_qm31_tooth
#print axioms generated_validator_rejects_noncanonical_tooth

end aspis_prover.RuntimeRelationTableCanonicality
