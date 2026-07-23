import RuntimeRelationReleasedArithmetic

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeRelationSampleStorage

open aspis_prover

abbrev RawQM31 := aspis_core.field.QM31
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

private theorem generated_array_update_run
    {T : Type*} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (value : T)
    (hindex : index.val < N.val) :
    Array.update values index value = ok (values.set index value) := by
  obtain ⟨updated, hrun, hupdated⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.update_spec values index value (by
      simpa [Array.length_eq] using hindex))
  simpa [hupdated] using hrun

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
      ((values.val[round.val]!).set sample value)).val[round.val]!).val[sample.val]! =
        value := by
  rw [array_set_get_same values round
    (values.val[round.val]!.set sample value) hround]
  exact array_set_get_same values.val[round.val]! sample value hsample

/-- A successful source-authentic circle sample exposes not only the OOD
evaluation but also the exact mix/add call and the table written into the
round/sample slot. -/
theorem generated_circle_sample_success_stores_table
    (schedule : RuntimeSchedule)
    (relation relationOut : RuntimeRelation)
    (tables tablesOut : RuntimeTables)
    (round sample : Std.Usize)
    (hroundZero : round = 0#usize)
    (hsample : sample.val < 2)
    (hrun :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_sample
          schedule relation tables round sample =
        ok (core.result.Result.Ok (), relationOut, tablesOut)) :
    ∃ point value table mix,
      Array.index_usize schedule.circle_ood_points sample = ok point ∧
      v5_mask.relation_prover.V5IncrementalRelation.evaluate_circle_ood_with_table
          relation point = ok (core.result.Result.Ok (value, table)) ∧
      Array.index_usize schedule.ood_mixes round =
        ok schedule.ood_mixes.val[round.val]! ∧
      Array.index_usize schedule.ood_mixes.val[round.val]! sample = ok mix ∧
      v5_mask.relation_prover.V5IncrementalRelation.add_circle_ood
          relation point value mix =
        ok (core.result.Result.Ok (), relationOut) ∧
      tablesOut.ood.val[round.val]!.val[sample.val]! = table ∧
      tablesOut.ood = tables.ood.set round
        (tables.ood.val[round.val]!.set sample table) := by
  have hrunZero :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_sample
          schedule relation tables 0#usize sample =
        ok (core.result.Result.Ok (), relationOut, tablesOut) := by
    simpa [hroundZero] using hrun
  obtain ⟨point, value, table, hpoint, hood⟩ :=
    ComponentCRuntimeRelationSampleOodCall.generated_circle_sample_success_has_ood_call
      schedule relation relationOut tables tablesOut sample hrunZero
  have hround : round.val < 4 := by
    rw [hroundZero]
    norm_num
  have hmixRound :
      Array.index_usize schedule.ood_mixes round =
        ok schedule.ood_mixes.val[round.val]! :=
    generated_array_index_run schedule.ood_mixes round hround
  let mix := schedule.ood_mixes.val[round.val]!.val[sample.val]!
  have hmix :
      Array.index_usize schedule.ood_mixes.val[round.val]! sample = ok mix :=
    generated_array_index_run schedule.ood_mixes.val[round.val]! sample hsample
  unfold
    v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_sample
    at hrun
  rw [if_pos hroundZero] at hrun
  rw [hpoint] at hrun
  simp only [bind_tc_ok] at hrun
  rw [hood] at hrun
  simp only [bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch] at hrun
  simp only [massert] at hrun
  have hroundScalar : round < 4#usize := by scalar_tac
  have hsampleScalar : sample < 2#usize := by scalar_tac
  rw [if_pos hroundScalar, if_pos hsampleScalar] at hrun
  simp only [bind_tc_ok] at hrun
  rw [generated_array_index_mut_run tables.ood round hround] at hrun
  simp only [bind_tc_ok] at hrun
  rw [generated_array_index_mut_run tables.ood.val[round.val]! sample hsample]
    at hrun
  simp only [bind_tc_ok] at hrun
  let restored0 := tables.ood.set round
    (tables.ood.val[round.val]!.set sample
      tables.ood.val[round.val]!.val[sample.val]!)
  rw [generated_array_index_mut_run restored0 round hround] at hrun
  simp only [bind_tc_ok] at hrun
  rw [generated_array_index_mut_run restored0.val[round.val]! sample hsample]
    at hrun
  simp only [bind_tc_ok] at hrun
  rw [hmixRound] at hrun
  simp only [bind_tc_ok] at hrun
  rw [hmix] at hrun
  simp only [bind_tc_ok] at hrun
  generalize hadd :
      v5_mask.relation_prover.V5IncrementalRelation.add_circle_ood
          relation point value mix = addResult at hrun
  cases addResult with
  | fail error => simp at hrun
  | div => simp at hrun
  | ok addTuple =>
    rcases addTuple with ⟨addStatus, relationAfter⟩
    cases addStatus with
    | Err addError =>
      simp [
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        v5_mask.component_c_runtime.V5ComponentCRuntimeError.Insts.CoreConvertFromV5RelationProverError.from]
        at hrun
    | Ok payload =>
      rcases payload with ⟨⟩
      simp only [bind_tc_ok] at hrun
      cases hrun
      refine ⟨point, value, table, mix, hpoint, hood,
        hmixRound, hmix, hadd, ?_, ?_⟩
      · exact nested_set_get_same restored0 round sample table hround hsample
      · have hrestored : restored0 = tables.ood := by
          dsimp [restored0]
          rw [Array.set_getElem!_eq, Array.set_getElem!_eq]
        change restored0.set round
          (restored0.val[round.val]!.set sample table) =
            tables.ood.set round
              (tables.ood.val[round.val]!.set sample table)
        rw [hrestored]

#print axioms generated_circle_sample_success_stores_table

/-- The nonzero line-round branch has the identical authenticated storage
property, with its layer index and line point read kept explicit. -/
theorem generated_line_sample_success_stores_table
    (schedule : RuntimeSchedule)
    (relation relationOut : RuntimeRelation)
    (tables tablesOut : RuntimeTables)
    (round sample : Std.Usize)
    (hroundNonzero : round ≠ 0#usize)
    (hround : round.val < 4)
    (hsample : sample.val < 2)
    (hrun :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_sample
          schedule relation tables round sample =
        ok (core.result.Result.Ok (), relationOut, tablesOut)) :
    ∃ layer layerPoints point value table mix,
      lift (Std.Usize.wrapping_sub round 1#usize) = ok layer ∧
      Array.index_usize schedule.line_ood_points layer = ok layerPoints ∧
      Array.index_usize layerPoints sample = ok point ∧
      v5_mask.relation_prover.V5IncrementalRelation.evaluate_line_ood_with_table
          relation point = ok (core.result.Result.Ok (value, table)) ∧
      Array.index_usize schedule.ood_mixes round =
        ok schedule.ood_mixes.val[round.val]! ∧
      Array.index_usize schedule.ood_mixes.val[round.val]! sample = ok mix ∧
      v5_mask.relation_prover.V5IncrementalRelation.add_line_ood
          relation point value mix =
        ok (core.result.Result.Ok (), relationOut) ∧
      tablesOut.ood.val[round.val]!.val[sample.val]! = table ∧
      tablesOut.ood = tables.ood.set round
        (tables.ood.val[round.val]!.set sample table) := by
  obtain ⟨layer, layerPoints, point, value, table,
      hlayer, hlayerPoints, hpoint, hood⟩ :=
    ComponentCRuntimeRelationSampleOodCall.generated_line_sample_success_has_ood_call
      schedule relation relationOut tables tablesOut round sample
      hroundNonzero hrun
  have hmixRound :
      Array.index_usize schedule.ood_mixes round =
        ok schedule.ood_mixes.val[round.val]! :=
    generated_array_index_run schedule.ood_mixes round hround
  let mix := schedule.ood_mixes.val[round.val]!.val[sample.val]!
  have hmix :
      Array.index_usize schedule.ood_mixes.val[round.val]! sample = ok mix :=
    generated_array_index_run schedule.ood_mixes.val[round.val]! sample hsample
  unfold
    v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_sample
    at hrun
  simp only [if_neg hroundNonzero] at hrun
  rw [hlayer] at hrun
  simp only [bind_tc_ok] at hrun
  rw [hlayerPoints] at hrun
  simp only [bind_tc_ok] at hrun
  rw [hpoint] at hrun
  simp only [bind_tc_ok] at hrun
  rw [hood] at hrun
  simp only [bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch] at hrun
  simp only [massert] at hrun
  have hroundScalar : round < 4#usize := by scalar_tac
  have hsampleScalar : sample < 2#usize := by scalar_tac
  rw [if_pos hroundScalar, if_pos hsampleScalar] at hrun
  simp only [bind_tc_ok] at hrun
  rw [generated_array_index_mut_run tables.ood round hround] at hrun
  simp only [bind_tc_ok] at hrun
  rw [generated_array_index_mut_run tables.ood.val[round.val]! sample hsample]
    at hrun
  simp only [bind_tc_ok] at hrun
  let restored0 := tables.ood.set round
    (tables.ood.val[round.val]!.set sample
      tables.ood.val[round.val]!.val[sample.val]!)
  rw [generated_array_index_mut_run restored0 round hround] at hrun
  simp only [bind_tc_ok] at hrun
  rw [generated_array_index_mut_run restored0.val[round.val]! sample hsample]
    at hrun
  simp only [bind_tc_ok] at hrun
  rw [hmixRound] at hrun
  simp only [bind_tc_ok] at hrun
  rw [hmix] at hrun
  simp only [bind_tc_ok] at hrun
  generalize hadd :
      v5_mask.relation_prover.V5IncrementalRelation.add_line_ood
          relation point value mix = addResult at hrun
  cases addResult with
  | fail error => simp at hrun
  | div => simp at hrun
  | ok addTuple =>
    rcases addTuple with ⟨addStatus, relationAfter⟩
    cases addStatus with
    | Err addError =>
      simp [
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        v5_mask.component_c_runtime.V5ComponentCRuntimeError.Insts.CoreConvertFromV5RelationProverError.from]
        at hrun
    | Ok payload =>
      rcases payload with ⟨⟩
      simp only [bind_tc_ok] at hrun
      cases hrun
      refine ⟨layer, layerPoints, point, value, table, mix,
        hlayer, hlayerPoints, hpoint, hood, hmixRound, hmix, hadd, ?_, ?_⟩
      · exact nested_set_get_same restored0 round sample table hround hsample
      · have hrestored : restored0 = tables.ood := by
          dsimp [restored0]
          rw [Array.set_getElem!_eq, Array.set_getElem!_eq]
        change restored0.set round
          (restored0.val[round.val]!.set sample table) =
            tables.ood.set round
              (tables.ood.val[round.val]!.set sample table)
        rw [hrestored]

#print axioms generated_line_sample_success_stores_table

/-- A successful generated circle-claim insertion writes exactly the supplied
value and preserves every already-released relation array other than that one
OOD coordinate. -/
theorem generated_add_circle_success_state
    (relation relationOut : RuntimeRelation)
    (point : aspis_core.circle.SecureCirclePoint)
    (value mix : RawQM31)
    (hround : relation.round = 0#usize)
    (hsample : relation.samples.val < 2)
    (hrun :
      v5_mask.relation_prover.V5IncrementalRelation.add_circle_ood
          relation point value mix =
        ok (core.result.Result.Ok (), relationOut)) :
    relationOut.ood_values =
      relation.ood_values.set 0#usize
        (relation.ood_values.val[0]!.set relation.samples value) ∧
    relationOut.ood_values.val[0]!.val[relation.samples.val]! = value ∧
    relationOut.sumchecks = relation.sumchecks ∧
    relationOut.coefficients = relation.coefficients ∧
    relationOut.round = relation.round ∧
    relationOut.samples =
      Std.Usize.wrapping_add relation.samples 1#usize := by
  unfold v5_mask.relation_prover.V5IncrementalRelation.add_circle_ood at hrun
  have hroundGuard : (relation.round != 0#usize) = false := by
    simp [hround]
  simp only [hroundGuard, Bool.false_eq_true, if_false] at hrun
  have hsampleGuard :
      ¬ relation.samples >= aspis_core.circle_prefix.CANDIDATE_OOD_SAMPLES := by
    simp only [aspis_core.circle_prefix.CANDIDATE_OOD_SAMPLES]
    scalar_tac
  rw [if_neg hsampleGuard] at hrun
  generalize htensor :
      aspis_core.sumcheck.WeightAccumulator.add_circle_tensor relation.weights
          mix point = tensorResult at hrun
  cases tensorResult with
  | fail error => simp at hrun
  | div => simp at hrun
  | ok tensorTuple =>
    rcases tensorTuple with ⟨tensorStatus, weightsAfter⟩
    cases tensorStatus with
    | Err tensorError =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        v5_mask.relation_prover.V5RelationProverError.Insts.CoreConvertFromTensorWeightError.from]
        at hrun
    | Ok payload =>
      rcases payload with ⟨⟩
      simp only [bind_tc_ok,
        core.result.Result.Insts.CoreOpsTry.branch] at hrun
      rw [generated_array_index_mut_run relation.ood_values 0#usize (by norm_num)]
        at hrun
      simp only [bind_tc_ok] at hrun
      generalize hrowArray :
          relation.ood_values.val[(0#usize).val]! = oodRow at hrun
      rw [generated_array_update_run oodRow relation.samples value hsample]
        at hrun
      simp only [bind_tc_ok] at hrun
      generalize hmul : aspis_core.field.QM31.mul mix value = mulResult at hrun
      cases mulResult with
      | fail error => simp at hrun
      | div => simp at hrun
      | ok product =>
        simp only [bind_tc_ok] at hrun
        generalize hadd :
            aspis_core.field.QM31.add relation.running_claim product =
              addResult at hrun
        cases addResult with
        | fail error => simp at hrun
        | div => simp at hrun
        | ok runningClaim =>
          simp only [bind_tc_ok] at hrun
          generalize hnext :
              lift (Std.Usize.wrapping_add relation.samples 1#usize) =
                nextResult at hrun
          cases nextResult with
          | fail error => simp at hrun
          | div => simp at hrun
          | ok nextSample =>
            simp only [bind_tc_ok] at hrun
            simp only [Std.lift] at hnext
            cases hnext
            subst oodRow
            cases hrun
            refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
            change
              ((relation.ood_values.set 0#usize
                (relation.ood_values.val[0]!.set relation.samples value)).val[0]!).val[
                  relation.samples.val]! = value
            have houter := array_set_get_same relation.ood_values 0#usize
              (relation.ood_values.val[0]!.set relation.samples value)
              (by norm_num)
            have houter' :
                (relation.ood_values.set 0#usize
                  (relation.ood_values.val[0]!.set relation.samples value)).val[0]! =
                    relation.ood_values.val[0]!.set relation.samples value := by
              simpa using houter
            rw [houter']
            exact array_set_get_same relation.ood_values.val[0]!
              relation.samples value hsample

#print axioms generated_add_circle_success_state

/-- Nonzero line-round insertion has the same exact state effect. -/
theorem generated_add_line_success_state
    (relation relationOut : RuntimeRelation)
    (point value mix : RawQM31)
    (hroundNonzero : relation.round ≠ 0#usize)
    (hround : relation.round.val < 4)
    (hsample : relation.samples.val < 2)
    (hrun :
      v5_mask.relation_prover.V5IncrementalRelation.add_line_ood
          relation point value mix =
        ok (core.result.Result.Ok (), relationOut)) :
    relationOut.ood_values =
      relation.ood_values.set relation.round
        (relation.ood_values.val[relation.round.val]!.set
          relation.samples value) ∧
    relationOut.ood_values.val[relation.round.val]!.val[
        relation.samples.val]! = value ∧
    relationOut.sumchecks = relation.sumchecks ∧
    relationOut.coefficients = relation.coefficients ∧
    relationOut.round = relation.round ∧
    relationOut.samples =
      Std.Usize.wrapping_add relation.samples 1#usize := by
  unfold v5_mask.relation_prover.V5IncrementalRelation.add_line_ood at hrun
  rw [if_neg hroundNonzero] at hrun
  have hroundNotGe :
      ¬ relation.round >= aspis_core.circle_prefix.CANDIDATE_ROUND_COUNT := by
    simp only [aspis_core.circle_prefix.CANDIDATE_ROUND_COUNT]
    scalar_tac
  rw [if_neg hroundNotGe] at hrun
  have hsampleNotGe :
      ¬ relation.samples >= aspis_core.circle_prefix.CANDIDATE_OOD_SAMPLES := by
    simp only [aspis_core.circle_prefix.CANDIDATE_OOD_SAMPLES]
    scalar_tac
  rw [if_neg hsampleNotGe] at hrun
  generalize htensor :
      aspis_core.sumcheck.WeightAccumulator.add_line_tensor relation.weights
          mix point = tensorResult at hrun
  cases tensorResult with
  | fail error => simp at hrun
  | div => simp at hrun
  | ok tensorTuple =>
    rcases tensorTuple with ⟨tensorStatus, weightsAfter⟩
    cases tensorStatus with
    | Err tensorError =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        v5_mask.relation_prover.V5RelationProverError.Insts.CoreConvertFromTensorWeightError.from]
        at hrun
    | Ok payload =>
      rcases payload with ⟨⟩
      simp only [bind_tc_ok,
        core.result.Result.Insts.CoreOpsTry.branch] at hrun
      rw [generated_array_index_mut_run relation.ood_values relation.round hround]
        at hrun
      simp only [bind_tc_ok] at hrun
      rw [generated_array_update_run
        relation.ood_values.val[relation.round.val]!
        relation.samples value hsample] at hrun
      simp only [bind_tc_ok] at hrun
      generalize hmul : aspis_core.field.QM31.mul mix value = mulResult at hrun
      cases mulResult with
      | fail error => simp at hrun
      | div => simp at hrun
      | ok product =>
        simp only [bind_tc_ok] at hrun
        generalize hadd :
            aspis_core.field.QM31.add relation.running_claim product =
              addResult at hrun
        cases addResult with
        | fail error => simp at hrun
        | div => simp at hrun
        | ok runningClaim =>
          simp only [bind_tc_ok] at hrun
          generalize hnext :
              lift (Std.Usize.wrapping_add relation.samples 1#usize) =
                nextResult at hrun
          cases nextResult with
          | fail error => simp at hrun
          | div => simp at hrun
          | ok nextSample =>
            simp only [bind_tc_ok] at hrun
            simp only [Std.lift] at hnext
            cases hnext
            cases hrun
            refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
            change
              ((relation.ood_values.set relation.round
                (relation.ood_values.val[relation.round.val]!.set
                  relation.samples value)).val[relation.round.val]!).val[
                    relation.samples.val]! = value
            rw [array_set_get_same relation.ood_values relation.round
              (relation.ood_values.val[relation.round.val]!.set
                relation.samples value) hround]
            exact array_set_get_same
              relation.ood_values.val[relation.round.val]!
              relation.samples value hsample

#print axioms generated_add_line_success_state

end aspis_prover.ComponentCRuntimeRelationSampleStorage
