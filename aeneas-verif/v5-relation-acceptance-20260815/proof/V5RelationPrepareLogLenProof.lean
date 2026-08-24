import Mathlib
import Aeneas.Tactic.Step.DspecInduction
import V5RelationCallerGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5RelationPrepareLogLenProof

namespace Prepare

open V5RelationPrepareGenerated

/-- The scalar calls that construct the initial claim consumed by the
relation verifier.  All fields come from one successful translated
preparation call. -/
structure PrepareRelationArithmeticTrace
    (kappa inactiveClaim :
      V5RelationPrepareGenerated.aspis_core.field.QM31)
    (preparedClaims :
      V5RelationPrepareGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims)
    (relation : V5RelationPrepareGenerated.v5_cu_probe.PreparedRelation) :
    Type where
  kappa2 : V5RelationPrepareGenerated.aspis_core.field.QM31
  kappa3 : V5RelationPrepareGenerated.aspis_core.field.QM31
  claim0 : V5RelationPrepareGenerated.aspis_core.field.QM31
  claim1 : V5RelationPrepareGenerated.aspis_core.field.QM31
  claim2 : V5RelationPrepareGenerated.aspis_core.field.QM31
  claim3 : V5RelationPrepareGenerated.aspis_core.field.QM31
  relationValue0 : V5RelationPrepareGenerated.aspis_core.field.QM31
  scaled1 : V5RelationPrepareGenerated.aspis_core.field.QM31
  relationValue1 : V5RelationPrepareGenerated.aspis_core.field.QM31
  scaled2 : V5RelationPrepareGenerated.aspis_core.field.QM31
  relationValue2 : V5RelationPrepareGenerated.aspis_core.field.QM31
  scaled3 : V5RelationPrepareGenerated.aspis_core.field.QM31
  relationValue3 : V5RelationPrepareGenerated.aspis_core.field.QM31
  kappa2Run :
    V5RelationPrepareGenerated.aspis_core.field.QM31.square kappa =
      .ok kappa2
  kappa3Run :
    V5RelationPrepareGenerated.aspis_core.field.QM31.mul kappa2 kappa =
      .ok kappa3
  claim0Run :
    V5RelationPrepareGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims.point_claim_at_for_extraction
        preparedClaims 0#usize = .ok claim0
  relationValue0Run :
    V5RelationPrepareGenerated.aspis_core.field.QM31.add inactiveClaim claim0 =
      .ok relationValue0
  claim1Run :
    V5RelationPrepareGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims.point_claim_at_for_extraction
        preparedClaims 1#usize = .ok claim1
  scaled1Run :
    V5RelationPrepareGenerated.aspis_core.field.QM31.mul kappa claim1 =
      .ok scaled1
  relationValue1Run :
    V5RelationPrepareGenerated.aspis_core.field.QM31.add relationValue0 scaled1 =
      .ok relationValue1
  claim2Run :
    V5RelationPrepareGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims.point_claim_at_for_extraction
        preparedClaims 2#usize = .ok claim2
  scaled2Run :
    V5RelationPrepareGenerated.aspis_core.field.QM31.mul kappa2 claim2 =
      .ok scaled2
  relationValue2Run :
    V5RelationPrepareGenerated.aspis_core.field.QM31.add relationValue1 scaled2 =
      .ok relationValue2
  claim3Run :
    V5RelationPrepareGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims.point_claim_at_for_extraction
        preparedClaims 3#usize = .ok claim3
  scaled3Run :
    V5RelationPrepareGenerated.aspis_core.field.QM31.mul kappa3 claim3 =
      .ok scaled3
  relationValue3Run :
    V5RelationPrepareGenerated.aspis_core.field.QM31.add relationValue2 scaled3 =
      .ok relationValue3
  returnedRelationValue : relation.relation_value = relationValue3

private theorem prepare_closure0_maps_error
    (error : V5RelationPrepareGenerated.aspis_core.sumcheck.TensorWeightError) :
    V5RelationPrepareGenerated.core.result.Result.map_err
        V5RelationPrepareGenerated.v5_cu_probe.prepare_relation_base_with_kappa_prepared_for_extraction.closure.Insts.CoreOpsFunctionFnOnceTupleTensorWeightErrorProgramError
        (.Err error : core.result.Result Unit
          V5RelationPrepareGenerated.aspis_core.sumcheck.TensorWeightError) () =
      .ok (.Err
        V5RelationPrepareGenerated.solana_program_error.ProgramError.InvalidAccountData :
          core.result.Result Unit
            V5RelationPrepareGenerated.solana_program_error.ProgramError) := by
  rfl

private theorem prepare_closure1_maps_error
    (error : V5RelationPrepareGenerated.aspis_core.sumcheck.TensorWeightError) :
    V5RelationPrepareGenerated.core.result.Result.map_err
        V5RelationPrepareGenerated.v5_cu_probe.prepare_relation_base_with_kappa_prepared_for_extraction.closure_1.Insts.CoreOpsFunctionFnOnceTupleTensorWeightErrorProgramError
        (.Err error : core.result.Result Unit
          V5RelationPrepareGenerated.aspis_core.sumcheck.TensorWeightError) () =
      .ok (.Err
        V5RelationPrepareGenerated.solana_program_error.ProgramError.InvalidAccountData :
          core.result.Result Unit
            V5RelationPrepareGenerated.solana_program_error.ProgramError) := by
  rfl

private theorem prepare_closure2_maps_error
    (error : V5RelationPrepareGenerated.aspis_core.sumcheck.TensorWeightError) :
    V5RelationPrepareGenerated.core.result.Result.map_err
        V5RelationPrepareGenerated.v5_cu_probe.prepare_relation_base_with_kappa_prepared_for_extraction.closure_2.Insts.CoreOpsFunctionFnOnceTupleTensorWeightErrorProgramError
        (.Err error : core.result.Result Unit
          V5RelationPrepareGenerated.aspis_core.sumcheck.TensorWeightError) () =
      .ok (.Err
        V5RelationPrepareGenerated.solana_program_error.ProgramError.InvalidAccountData :
          core.result.Result Unit
            V5RelationPrepareGenerated.solana_program_error.ProgramError) := by
  rfl

private theorem prepare_closure3_maps_error
    (error : V5RelationPrepareGenerated.aspis_core.sumcheck.TensorWeightError) :
    V5RelationPrepareGenerated.core.result.Result.map_err
        V5RelationPrepareGenerated.v5_cu_probe.prepare_relation_base_with_kappa_prepared_for_extraction.closure_3.Insts.CoreOpsFunctionFnOnceTupleTensorWeightErrorProgramError
        (.Err error : core.result.Result Unit
          V5RelationPrepareGenerated.aspis_core.sumcheck.TensorWeightError) () =
      .ok (.Err
        V5RelationPrepareGenerated.solana_program_error.ProgramError.InvalidAccountData :
          core.result.Result Unit
            V5RelationPrepareGenerated.solana_program_error.ProgramError) := by
  rfl

private theorem core_error_ne_ok {T E : Type} (error : E) (value : T) :
    (core.result.Result.Err error : core.result.Result T E) ≠
      core.result.Result.Ok value := by
  intro h
  cases h

private theorem unwrap_or_succeeds {T E : Type}
    (value : core.result.Result T E) (fallback : T) :
    ∃ output,
      V5RelationPrepareGenerated.core.result.Result.unwrap_or value fallback =
        .ok output := by
  cases value <;> simp [V5RelationPrepareGenerated.core.result.Result.unwrap_or]

private theorem returned_relation_has_log_len_ten
    (produced expected : V5RelationPrepareGenerated.v5_cu_probe.PreparedRelation)
    (producedPoint expectedPoint :
      Array V5RelationPrepareGenerated.aspis_core.field.QM31 10#usize)
    (producedScale expectedScale :
      V5RelationPrepareGenerated.aspis_core.field.QM31)
    (hlog : produced.weights.log_len = 10#u32)
    (hrun :
      (.ok (.Ok (produced, producedPoint, producedScale)) :
        Result (core.result.Result
          (V5RelationPrepareGenerated.v5_cu_probe.PreparedRelation ×
            Array V5RelationPrepareGenerated.aspis_core.field.QM31 10#usize ×
            V5RelationPrepareGenerated.aspis_core.field.QM31)
          V5RelationPrepareGenerated.solana_program_error.ProgramError)) =
      .ok (.Ok (expected, expectedPoint, expectedScale))) :
    expected.weights.log_len = 10#u32 ∧
      expected.relation_value = produced.relation_value := by
  have houter := Result.ok.inj hrun
  have htriple := core.result.Result.Ok.inj houter
  have hrelation : produced = expected := congrArg Prod.fst htriple
  subst expected
  exact ⟨hlog, rfl⟩

private theorem checked_nonreal_relation_has_log_len_ten
    (weights : V5RelationPrepareGenerated.aspis_core.sumcheck.WeightAccumulator)
    (relationValue : V5RelationPrepareGenerated.aspis_core.field.QM31)
    (alphas finalValues :
      Array V5RelationPrepareGenerated.aspis_core.field.QM31 4#usize)
    (producedPoint :
      Array V5RelationPrepareGenerated.aspis_core.field.QM31 10#usize)
    (producedScale : V5RelationPrepareGenerated.aspis_core.field.QM31)
    (expected : V5RelationPrepareGenerated.v5_cu_probe.PreparedRelation)
    (expectedPoint :
      Array V5RelationPrepareGenerated.aspis_core.field.QM31 10#usize)
    (expectedScale : V5RelationPrepareGenerated.aspis_core.field.QM31)
    (hlog : weights.log_len = 10#u32)
    (hrun :
      (do
        let hasZeroAlpha ← core.slice.Slice.contains
          V5RelationPrepareGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
          (Array.to_slice alphas)
          V5RelationPrepareGenerated.aspis_core.field.QM31.ZERO
        if hasZeroAlpha
        then .ok (.Err
          V5RelationPrepareGenerated.solana_program_error.ProgramError.InvalidAccountData)
        else
          let hasZeroFinal ← core.slice.Slice.contains
            V5RelationPrepareGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
            (Array.to_slice finalValues)
            V5RelationPrepareGenerated.aspis_core.field.QM31.ZERO
          if hasZeroFinal
          then .ok (.Err
            V5RelationPrepareGenerated.solana_program_error.ProgramError.InvalidAccountData)
          else .ok (.Ok
            ({ weights := weights
               relation_value := relationValue
               alphas := alphas
               final_values := finalValues
               extra_work :=
                 V5RelationPrepareGenerated.v5_cu_probe.RelationExtraWork.None },
              producedPoint, producedScale)) :
        Result (core.result.Result
          (V5RelationPrepareGenerated.v5_cu_probe.PreparedRelation ×
            Array V5RelationPrepareGenerated.aspis_core.field.QM31 10#usize ×
            V5RelationPrepareGenerated.aspis_core.field.QM31)
          V5RelationPrepareGenerated.solana_program_error.ProgramError)) =
        .ok (.Ok (expected, expectedPoint, expectedScale))) :
    expected.weights.log_len = 10#u32 ∧
      expected.relation_value = relationValue := by
  cases hcontains0 : core.slice.Slice.contains
      V5RelationPrepareGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
      (Array.to_slice alphas)
      V5RelationPrepareGenerated.aspis_core.field.QM31.ZERO with
  | fail error => simp [hcontains0] at hrun
  | div => simp [hcontains0] at hrun
  | ok contains0 =>
    simp only [hcontains0, bind_tc_ok] at hrun
    cases contains0 with
    | true =>
      simp only [if_pos rfl] at hrun
      exact (core_error_ne_ok
        V5RelationPrepareGenerated.solana_program_error.ProgramError.InvalidAccountData
        (expected, expectedPoint, expectedScale) (Result.ok.inj hrun)).elim
    | false =>
      simp only [Bool.false_eq_true, if_false] at hrun
      cases hcontains1 : core.slice.Slice.contains
          V5RelationPrepareGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
          (Array.to_slice finalValues)
          V5RelationPrepareGenerated.aspis_core.field.QM31.ZERO with
      | fail error => simp [hcontains1] at hrun
      | div => simp [hcontains1] at hrun
      | ok contains1 =>
        simp only [hcontains1, bind_tc_ok] at hrun
        cases contains1 with
        | true =>
          simp only [if_pos rfl] at hrun
          exact (core_error_ne_ok
            V5RelationPrepareGenerated.solana_program_error.ProgramError.InvalidAccountData
            (expected, expectedPoint, expectedScale) (Result.ok.inj hrun)).elim
        | false =>
          simp only [Bool.false_eq_true, if_false] at hrun
          exact returned_relation_has_log_len_ten _ expected _ expectedPoint
            _ expectedScale hlog hrun

private theorem same_error_residual
    {T E : Type} (error : E) :
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        T (core.convert.FromSame E) (.Err error) =
      .ok (.Err error) := by
  rfl

theorem grouped_loop_preserves_log_len
    (logLen : Std.U32)
    (components : alloc.vec.Vec
      V5RelationPrepareGenerated.aspis_core.sumcheck.WeightComponent)
    (rows : Array Std.U8 64#usize) (masks : Slice Std.U16)
    (high : Std.Usize)
    (hcapacity : components.val.length < Std.Usize.max) :
    V5RelationPrepareGenerated.aspis_core.sumcheck.WeightAccumulator.add_grouped_64x16_binary_masks_deferred_prepared_loop
        logLen components rows masks high
      ⦃ output => output.2.log_len = logLen ⦄div := by
  unfold
    V5RelationPrepareGenerated.aspis_core.sumcheck.WeightAccumulator.add_grouped_64x16_binary_masks_deferred_prepared_loop
  generalize high = current
  revert current
  dspec_induction loop
  intro loop' ih current
  simp only
  unfold
    V5RelationPrepareGenerated.aspis_core.sumcheck.WeightAccumulator.add_grouped_64x16_binary_masks_deferred_prepared_loop.body
  simp only [Aeneas.Std.lift, bind_tc_ok]
  by_cases active : current < Slice.len (Array.to_slice rows)
  · rw [if_pos active]
    have hbound : current.val < rows.val.length := by
      simpa [UScalar.lt_equiv, Slice.len_val] using active
    obtain ⟨row, hrow, _⟩ :=
      Aeneas.Std.WP.spec_imp_exists
        (Array.index_usize_spec rows current hbound)
    rw [hrow]
    simp only [lift, bind_tc_ok]
    by_cases invalid : core.convert.num.FromUsizeU8.from row >= Slice.len masks
    · rw [if_pos invalid]
      simp
    · rw [if_neg invalid]
      simp only [lift, bind_tc_ok]
      exact ih _
  · rw [if_neg active]
    unfold
      V5RelationPrepareGenerated.aspis_core.sumcheck.WeightAccumulator.install_grouped_64x16_binary_masks_deferred_prepared
    simp only [lift, bind_tc_ok]
    obtain ⟨rowVec, hrows, _⟩ :=
      Aeneas.Std.WP.spec_imp_exists
        (alloc.slice.Slice.to_vec_spec core.clone.CloneU8
          (Array.to_slice rows) (by simp))
    rw [hrows]
    simp only [bind_tc_ok]
    obtain ⟨maskVec, hmasks, _⟩ :=
      Aeneas.Std.WP.spec_imp_exists
        (alloc.slice.Slice.to_vec_spec core.clone.CloneU16 masks (by simp))
    rw [hmasks]
    simp only [bind_tc_ok]
    let component :=
      V5RelationPrepareGenerated.aspis_core.sumcheck.WeightComponent.Grouped64x16BinaryDeferred
        rowVec maskVec none
        (alloc.vec.Vec.new V5RelationPrepareGenerated.aspis_core.field.QM31)
    obtain ⟨next, hpush, _⟩ :=
      Aeneas.Std.WP.spec_imp_exists
        (alloc.vec.Vec.push_spec components component hcapacity)
    rw [hpush]
    simp

/-- A successful generated grouped-mask installation has the exact released
relation log length.  The capacity premise is the ordinary translated `Vec`
allocation side condition; the preparation driver below reaches this call
with three components. -/
theorem add_grouped_success_has_log_len_ten
    (self : V5RelationPrepareGenerated.aspis_core.sumcheck.WeightAccumulator)
    (rows : Array Std.U8 64#usize) (masks : Slice Std.U16)
    (output : V5RelationPrepareGenerated.aspis_core.sumcheck.WeightAccumulator)
    (hcapacity : self.components.val.length < Std.Usize.max)
    (hrun :
      V5RelationPrepareGenerated.aspis_core.sumcheck.WeightAccumulator.add_grouped_64x16_binary_masks_deferred_prepared
          self rows masks = .ok (.Ok (), output)) :
    output.log_len = 10#u32 := by
  unfold
    V5RelationPrepareGenerated.aspis_core.sumcheck.WeightAccumulator.add_grouped_64x16_binary_masks_deferred_prepared at hrun
  simp only [core.slice.Slice.is_empty, bind_tc_ok] at hrun
  by_cases hlog : self.log_len != 10#u32
  · simp [hlog] at hrun
  rw [if_neg hlog] at hrun
  by_cases hempty : masks.length = 0
  · simp [hempty] at hrun
  simp [hempty] at hrun
  have hloop := grouped_loop_preserves_log_len self.log_len self.components
    rows masks 0#usize hcapacity
  have hout := Aeneas.Std.WP.dspec_imp_forall hloop (.Ok (), output) hrun
  have hself : self.log_len = 10#u32 := by
    scalar_tac
  simpa [hself] using hout

/-- Successful insertion of one multilinear component preserves `log_len`
and appends exactly one component. -/
theorem add_multilinear_success_shape
    (self : V5RelationPrepareGenerated.aspis_core.sumcheck.WeightAccumulator)
    (scale : V5RelationPrepareGenerated.aspis_core.field.QM31)
    (point : alloc.vec.Vec V5RelationPrepareGenerated.aspis_core.field.QM31)
    (output : V5RelationPrepareGenerated.aspis_core.sumcheck.WeightAccumulator)
    (hcapacity : self.components.val.length < Std.Usize.max)
    (hrun :
      V5RelationPrepareGenerated.aspis_core.sumcheck.WeightAccumulator.add_multilinear
          self scale point = .ok (.Ok (), output)) :
    output.log_len = self.log_len ∧
      output.components.val.length = self.components.val.length + 1 := by
  let component :=
    V5RelationPrepareGenerated.aspis_core.sumcheck.WeightComponent.Multilinear
      scale point
  obtain ⟨next, hpush, hnext⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (alloc.vec.Vec.push_spec self.components component hcapacity)
  unfold
    V5RelationPrepareGenerated.aspis_core.sumcheck.WeightAccumulator.add_multilinear at hrun
  simp only [lift, bind_tc_ok] at hrun
  by_cases hlength : alloc.vec.Vec.len point != UScalar.cast .Usize self.log_len
  · simp [hlength] at hrun
  rw [if_neg hlength, hpush] at hrun
  simp only [bind_tc_ok, ok.injEq, Prod.mk.injEq,
    core.result.Result.Ok.injEq] at hrun
  rcases hrun with ⟨_, rfl⟩
  refine ⟨rfl, ?_⟩
  rw [hnext, List.length_append]
  simp

theorem prepare_for_extraction_success_exposes_arithmetic
    (parsed : V5RelationPrepareGenerated.v5_cu_probe.ParsedProbeData)
    (kappa inactiveClaim : V5RelationPrepareGenerated.aspis_core.field.QM31)
    (preparedClaims :
      V5RelationPrepareGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims)
    (relation : V5RelationPrepareGenerated.v5_cu_probe.PreparedRelation)
    (point : Array V5RelationPrepareGenerated.aspis_core.field.QM31 10#usize)
    (denseScale : V5RelationPrepareGenerated.aspis_core.field.QM31)
    (hrun :
      V5RelationPrepareGenerated.v5_cu_probe.prepare_relation_base_with_kappa_prepared_for_extraction
          parsed kappa inactiveClaim preparedClaims =
        .ok (.Ok (relation, point, denseScale))) :
    relation.weights.log_len = 10#u32 ∧
      Nonempty (PrepareRelationArithmeticTrace kappa inactiveClaim
        preparedClaims relation) := by
  unfold
    V5RelationPrepareGenerated.v5_cu_probe.prepare_relation_base_with_kappa_prepared_for_extraction at hrun
  simp only [
    V5RelationPrepareGenerated.aspis_core.sumcheck.WeightAccumulator.empty,
    lift, bind_tc_ok] at hrun
  cases hkappa2 : V5RelationPrepareGenerated.aspis_core.field.QM31.square kappa with
  | fail error => simp [hkappa2] at hrun
  | div => simp [hkappa2] at hrun
  | ok kappa2 =>
    simp only [hkappa2, bind_tc_ok] at hrun
    cases hkappa3 : V5RelationPrepareGenerated.aspis_core.field.QM31.mul kappa2 kappa with
    | fail error => simp [hkappa3] at hrun
    | div => simp [hkappa3] at hrun
    | ok kappa3 =>
      simp only [hkappa3, bind_tc_ok] at hrun
      cases hdecode0 :
          V5RelationPrepareGenerated.v5_cu_probe.decode_relation_point_for_extraction
            parsed 0#usize with
      | fail error => simp [hdecode0] at hrun
      | div => simp [hdecode0] at hrun
      | ok decoded0 =>
        simp only [hdecode0, bind_tc_ok] at hrun
        cases decoded0 with
        | Err error =>
          simp only [
            core.result.Result.Insts.CoreOpsTry.branch,
            bind_tc_ok, same_error_residual] at hrun
          exact (core_error_ne_ok error (relation, point, denseScale)
            (Result.ok.inj hrun)).elim
        | Ok point0 =>
          simp only [
            core.result.Result.Insts.CoreOpsTry.branch,
            core.ops.control_flow.ControlFlow.Continue.injEq] at hrun
          cases hvec0 :
              V5RelationPrepareGenerated.v5_cu_probe.relation_point_vec_for_extraction
                point0 with
          | fail error => simp [hvec0] at hrun
          | div => simp [hvec0] at hrun
          | ok vec0 =>
            simp only [hvec0, bind_tc_ok] at hrun
            let weights0 :
                V5RelationPrepareGenerated.aspis_core.sumcheck.WeightAccumulator :=
              { log_len :=
                  V5RelationPrepareGenerated.v5_cu_probe.V5_CU_PROBE_RELATION_LOG_ROWS
                components := alloc.vec.Vec.new _ }
            cases hadd0 :
                V5RelationPrepareGenerated.aspis_core.sumcheck.WeightAccumulator.add_multilinear
                  weights0 V5RelationPrepareGenerated.aspis_core.field.QM31.ONE vec0 with
            | fail error => simp [weights0, hadd0] at hrun
            | div => simp [weights0, hadd0] at hrun
            | ok added0 =>
              cases added0 with
              | mk result0 weights1 =>
                cases result0 with
                | Err error =>
                  simp only [weights0, hadd0, bind_tc_ok,
                    prepare_closure0_maps_error,
                    core.result.Result.Insts.CoreOpsTry.branch,
                    same_error_residual] at hrun
                  exact (core_error_ne_ok
                    V5RelationPrepareGenerated.solana_program_error.ProgramError.InvalidAccountData
                    (relation, point, denseScale) (Result.ok.inj hrun)).elim
                | Ok unit =>
                  cases unit
                  have hshape1 := add_multilinear_success_shape
                    weights0 V5RelationPrepareGenerated.aspis_core.field.QM31.ONE
                    vec0 weights1 (by scalar_tac) hadd0
                  simp only [weights0, hadd0, bind_tc_ok,
                    core.result.Result.map_err,
                    core.result.Result.Insts.CoreOpsTry.branch] at hrun
                  cases hclaim0 :
                      V5RelationPrepareGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims.point_claim_at_for_extraction
                        preparedClaims 0#usize with
                  | fail error => simp [hclaim0] at hrun
                  | div => simp [hclaim0] at hrun
                  | ok claim0 =>
                    simp only [hclaim0, bind_tc_ok] at hrun
                    cases hvalue0 :
                        V5RelationPrepareGenerated.aspis_core.field.QM31.add
                          inactiveClaim claim0 with
                    | fail error => simp [hvalue0] at hrun
                    | div => simp [hvalue0] at hrun
                    | ok relationValue0 =>
                      simp only [hvalue0, bind_tc_ok] at hrun
                      cases hdecode1 :
                          V5RelationPrepareGenerated.v5_cu_probe.decode_relation_point_for_extraction
                            parsed 1#usize with
                      | fail error => simp [hdecode1] at hrun
                      | div => simp [hdecode1] at hrun
                      | ok decoded1 =>
                        simp only [hdecode1, bind_tc_ok] at hrun
                        cases decoded1 with
                        | Err error =>
                          simp only [
                            core.result.Result.Insts.CoreOpsTry.branch,
                            bind_tc_ok, same_error_residual] at hrun
                          exact (core_error_ne_ok error
                            (relation, point, denseScale)
                            (Result.ok.inj hrun)).elim
                        | Ok point1 =>
                          simp only [
                            core.result.Result.Insts.CoreOpsTry.branch] at hrun
                          cases hvec1 :
                              V5RelationPrepareGenerated.v5_cu_probe.relation_point_vec_for_extraction
                                point1 with
                          | fail error => simp [hvec1] at hrun
                          | div => simp [hvec1] at hrun
                          | ok vec1 =>
                            simp only [hvec1, bind_tc_ok] at hrun
                            cases hadd1 :
                                V5RelationPrepareGenerated.aspis_core.sumcheck.WeightAccumulator.add_multilinear
                                  weights1 kappa vec1 with
                            | fail error => simp [hadd1] at hrun
                            | div => simp [hadd1] at hrun
                            | ok added1 =>
                              cases added1 with
                              | mk result1 weights2 =>
                                cases result1 with
                                | Err error =>
                                  simp only [hadd1, bind_tc_ok,
                                    prepare_closure1_maps_error,
                                    core.result.Result.Insts.CoreOpsTry.branch,
                                    same_error_residual] at hrun
                                  exact (core_error_ne_ok
                                    V5RelationPrepareGenerated.solana_program_error.ProgramError.InvalidAccountData
                                    (relation, point, denseScale)
                                    (Result.ok.inj hrun)).elim
                                | Ok unit =>
                                  cases unit
                                  have hcap1 :
                                      weights1.components.val.length <
                                        Std.Usize.max := by
                                    rw [hshape1.2]
                                    simp [weights0]
                                    scalar_tac
                                  have hshape2 := add_multilinear_success_shape
                                    weights1 kappa vec1 weights2 hcap1 hadd1
                                  simp only [hadd1, bind_tc_ok,
                                    core.result.Result.map_err,
                                    core.result.Result.Insts.CoreOpsTry.branch] at hrun
                                  cases hclaim1 :
                                      V5RelationPrepareGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims.point_claim_at_for_extraction
                                        preparedClaims 1#usize with
                                  | fail error => simp [hclaim1] at hrun
                                  | div => simp [hclaim1] at hrun
                                  | ok claim1 =>
                                    simp only [hclaim1, bind_tc_ok] at hrun
                                    cases hscaled1 :
                                        V5RelationPrepareGenerated.aspis_core.field.QM31.mul
                                          kappa claim1 with
                                    | fail error => simp [hscaled1] at hrun
                                    | div => simp [hscaled1] at hrun
                                    | ok scaled1 =>
                                      simp only [hscaled1, bind_tc_ok] at hrun
                                      cases hvalue1 :
                                          V5RelationPrepareGenerated.aspis_core.field.QM31.add
                                            relationValue0 scaled1 with
                                      | fail error => simp [hvalue1] at hrun
                                      | div => simp [hvalue1] at hrun
                                      | ok relationValue1 =>
                                        simp only [hvalue1, bind_tc_ok] at hrun
                                        cases hdecode2 :
                                            V5RelationPrepareGenerated.v5_cu_probe.decode_relation_point_for_extraction
                                              parsed 2#usize with
                                        | fail error => simp [hdecode2] at hrun
                                        | div => simp [hdecode2] at hrun
                                        | ok decoded2 =>
                                          simp only [hdecode2, bind_tc_ok] at hrun
                                          cases decoded2 with
                                          | Err error =>
                                            simp only [
                                              core.result.Result.Insts.CoreOpsTry.branch,
                                              bind_tc_ok, same_error_residual] at hrun
                                            exact (core_error_ne_ok error
                                              (relation, point, denseScale)
                                              (Result.ok.inj hrun)).elim
                                          | Ok point2 =>
                                            simp only [
                                              core.result.Result.Insts.CoreOpsTry.branch] at hrun
                                            cases hvec2 :
                                                V5RelationPrepareGenerated.v5_cu_probe.relation_point_vec_for_extraction
                                                  point2 with
                                            | fail error => simp [hvec2] at hrun
                                            | div => simp [hvec2] at hrun
                                            | ok vec2 =>
                                              simp only [hvec2, bind_tc_ok] at hrun
                                              cases hadd2 :
                                                  V5RelationPrepareGenerated.aspis_core.sumcheck.WeightAccumulator.add_multilinear
                                                    weights2 kappa2 vec2 with
                                              | fail error => simp [hadd2] at hrun
                                              | div => simp [hadd2] at hrun
                                              | ok added2 =>
                                                cases added2 with
                                                | mk result2 weights3 =>
                                                  cases result2 with
                                                  | Err error =>
                                                    simp only [hadd2, bind_tc_ok,
                                                      prepare_closure2_maps_error,
                                                      core.result.Result.Insts.CoreOpsTry.branch,
                                                      same_error_residual] at hrun
                                                    exact (core_error_ne_ok
                                                      V5RelationPrepareGenerated.solana_program_error.ProgramError.InvalidAccountData
                                                      (relation, point, denseScale)
                                                      (Result.ok.inj hrun)).elim
                                                  | Ok unit =>
                                                    cases unit
                                                    have hcap2 :
                                                        weights2.components.val.length <
                                                          Std.Usize.max := by
                                                      rw [hshape2.2, hshape1.2]
                                                      simp [weights0]
                                                      scalar_tac
                                                    have hshape3 :=
                                                      add_multilinear_success_shape
                                                        weights2 kappa2 vec2 weights3
                                                        hcap2 hadd2
                                                    simp only [hadd2, bind_tc_ok,
                                                      core.result.Result.map_err,
                                                      core.result.Result.Insts.CoreOpsTry.branch] at hrun
                                                    cases hclaim2 :
                                                        V5RelationPrepareGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims.point_claim_at_for_extraction
                                                          preparedClaims 2#usize with
                                                    | fail error => simp [hclaim2] at hrun
                                                    | div => simp [hclaim2] at hrun
                                                    | ok claim2 =>
                                                      simp only [hclaim2, bind_tc_ok] at hrun
                                                      cases hscaled2 :
                                                          V5RelationPrepareGenerated.aspis_core.field.QM31.mul
                                                            kappa2 claim2 with
                                                      | fail error => simp [hscaled2] at hrun
                                                      | div => simp [hscaled2] at hrun
                                                      | ok scaled2 =>
                                                        simp only [hscaled2, bind_tc_ok] at hrun
                                                        cases hvalue2 :
                                                            V5RelationPrepareGenerated.aspis_core.field.QM31.add
                                                              relationValue1 scaled2 with
                                                        | fail error => simp [hvalue2] at hrun
                                                        | div => simp [hvalue2] at hrun
                                                        | ok relationValue2 =>
                                                          simp only [hvalue2, bind_tc_ok] at hrun
                                                          cases hclaim3 :
                                                              V5RelationPrepareGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims.point_claim_at_for_extraction
                                                                preparedClaims 3#usize with
                                                          | fail error => simp [hclaim3] at hrun
                                                          | div => simp [hclaim3] at hrun
                                                          | ok claim3 =>
                                                            simp only [hclaim3, bind_tc_ok] at hrun
                                                            cases hscaled3 :
                                                                V5RelationPrepareGenerated.aspis_core.field.QM31.mul
                                                                  kappa3 claim3 with
                                                            | fail error => simp [hscaled3] at hrun
                                                            | div => simp [hscaled3] at hrun
                                                            | ok scaled3 =>
                                                              simp only [hscaled3, bind_tc_ok] at hrun
                                                              cases hvalue3 :
                                                                  V5RelationPrepareGenerated.aspis_core.field.QM31.add
                                                                    relationValue2 scaled3 with
                                                              | fail error => simp [hvalue3] at hrun
                                                              | div => simp [hvalue3] at hrun
                                                              | ok relationValue3 =>
                                                                simp only [hvalue3, bind_tc_ok] at hrun
                                                                cases hgroup :
                                                                    V5RelationPrepareGenerated.aspis_core.sumcheck.WeightAccumulator.add_grouped_64x16_binary_masks_deferred_prepared
                                                                      weights3
                                                                      V5RelationPrepareGenerated.v5_cu_probe.V5_ATOMIC_V3_INACTIVE_ROW_GROUPS
                                                                      (Array.to_slice V5RelationPrepareGenerated.v5_cu_probe.V5_ATOMIC_V3_INACTIVE_GROUP_MASKS) with
                                                                | fail error => simp [hgroup] at hrun
                                                                | div => simp [hgroup] at hrun
                                                                | ok grouped =>
                                                                  cases grouped with
                                                                  | mk groupResult weights4 =>
                                                                    cases groupResult with
                                                                    | Err error =>
                                                                      simp only [hgroup, bind_tc_ok,
                                                                        prepare_closure3_maps_error,
                                                                        core.result.Result.Insts.CoreOpsTry.branch,
                                                                        same_error_residual] at hrun
                                                                      exact (core_error_ne_ok
                                                                        V5RelationPrepareGenerated.solana_program_error.ProgramError.InvalidAccountData
                                                                        (relation, point, denseScale)
                                                                        (Result.ok.inj hrun)).elim
                                                                    | Ok unit =>
                                                                      cases unit
                                                                      have hcap3 :
                                                                          weights3.components.val.length <
                                                                            Std.Usize.max := by
                                                                        rw [hshape3.2, hshape2.2,
                                                                          hshape1.2]
                                                                        simp [weights0]
                                                                        scalar_tac
                                                                      have hlog4 :=
                                                                        add_grouped_success_has_log_len_ten
                                                                          weights3
                                                                          V5RelationPrepareGenerated.v5_cu_probe.V5_ATOMIC_V3_INACTIVE_ROW_GROUPS
                                                                          (Array.to_slice V5RelationPrepareGenerated.v5_cu_probe.V5_ATOMIC_V3_INACTIVE_GROUP_MASKS)
                                                                          weights4 hcap3 hgroup
                                                                      simp only [hgroup, bind_tc_ok,
                                                                        core.result.Result.map_err,
                                                                        core.result.Result.Insts.CoreOpsTry.branch] at hrun
                                                                      cases halpha0 :
                                                                          V5RelationPrepareGenerated.v5_cu_probe.decode_qm31
                                                                            parsed.relation_alphas 0#usize with
                                                                      | fail error => simp [halpha0] at hrun
                                                                      | div => simp [halpha0] at hrun
                                                                      | ok rawAlpha0 =>
                                                                        simp only [halpha0, bind_tc_ok] at hrun
                                                                        obtain ⟨alpha0, hunwrapAlpha0⟩ :=
                                                                          unwrap_or_succeeds rawAlpha0
                                                                            V5RelationPrepareGenerated.aspis_core.field.QM31.ZERO
                                                                        rw [hunwrapAlpha0] at hrun
                                                                        simp only [bind_tc_ok] at hrun
                                                                        cases halpha1 :
                                                                            V5RelationPrepareGenerated.v5_cu_probe.decode_qm31
                                                                              parsed.relation_alphas 1#usize with
                                                                        | fail error => simp [halpha1] at hrun
                                                                        | div => simp [halpha1] at hrun
                                                                        | ok rawAlpha1 =>
                                                                          simp only [halpha1, bind_tc_ok] at hrun
                                                                          obtain ⟨alpha1, hunwrapAlpha1⟩ :=
                                                                            unwrap_or_succeeds rawAlpha1
                                                                              V5RelationPrepareGenerated.aspis_core.field.QM31.ZERO
                                                                          rw [hunwrapAlpha1] at hrun
                                                                          simp only [bind_tc_ok] at hrun
                                                                          cases halpha2 :
                                                                              V5RelationPrepareGenerated.v5_cu_probe.decode_qm31
                                                                                parsed.relation_alphas 2#usize with
                                                                          | fail error => simp [halpha2] at hrun
                                                                          | div => simp [halpha2] at hrun
                                                                          | ok rawAlpha2 =>
                                                                            simp only [halpha2, bind_tc_ok] at hrun
                                                                            obtain ⟨alpha2, hunwrapAlpha2⟩ :=
                                                                              unwrap_or_succeeds rawAlpha2
                                                                                V5RelationPrepareGenerated.aspis_core.field.QM31.ZERO
                                                                            rw [hunwrapAlpha2] at hrun
                                                                            simp only [bind_tc_ok] at hrun
                                                                            cases halpha3 :
                                                                                V5RelationPrepareGenerated.v5_cu_probe.decode_qm31
                                                                                  parsed.relation_alphas 3#usize with
                                                                            | fail error => simp [halpha3] at hrun
                                                                            | div => simp [halpha3] at hrun
                                                                            | ok rawAlpha3 =>
                                                                              simp only [halpha3, bind_tc_ok] at hrun
                                                                              obtain ⟨alpha3, hunwrapAlpha3⟩ :=
                                                                                unwrap_or_succeeds rawAlpha3
                                                                                  V5RelationPrepareGenerated.aspis_core.field.QM31.ZERO
                                                                              rw [hunwrapAlpha3] at hrun
                                                                              simp only [bind_tc_ok] at hrun
                                                                              generalize hprefix :
                                                                                core.slice.Slice.get
                                                                                  (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)
                                                                                  parsed.v5_wire_prefix
                                                                                  { «end» := 8#usize } = prefixResult at hrun
                                                                              cases prefixResult with
                                                                              | fail error => simp [hprefix] at hrun
                                                                              | div => simp [hprefix] at hrun
                                                                              | ok prefixValue =>
                                                                                simp only [hprefix, bind_tc_ok] at hrun
                                                                                generalize heq :
                                                                                  core.option.Option.Insts.CoreCmpPartialEqOption.eq
                                                                                    (core.cmp.PartialEqShared
                                                                                      (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8))
                                                                                    prefixValue
                                                                                    (some (Array.to_slice
                                                                                      V5RelationPrepareGenerated.v5_cu_probe.V5_CU_REAL_PREFIX_MAGIC)) = eqResult at hrun
                                                                                cases eqResult with
                                                                                | fail error => simp [heq] at hrun
                                                                                | div => simp [heq] at hrun
                                                                                | ok realPrefix =>
                                                                                  simp only [heq, bind_tc_ok] at hrun
                                                                                  cases realPrefix <;>
                                                                                    simp_all only [Bool.false_eq_true,
                                                                                      if_false, if_true]
                                                                                  all_goals
                                                                                    generalize hfinal0 :
                                                                                      V5RelationPrepareGenerated.v5_cu_probe.decode_qm31
                                                                                        _ 0#usize = final0 at hrun
                                                                                    cases final0 with
                                                                                    | fail error => simp [hfinal0] at hrun
                                                                                    | div => simp [hfinal0] at hrun
                                                                                    | ok rawFinal0 =>
                                                                                      simp only [hfinal0, bind_tc_ok] at hrun
                                                                                      obtain ⟨final0, hunwrapFinal0⟩ :=
                                                                                        unwrap_or_succeeds rawFinal0
                                                                                          V5RelationPrepareGenerated.aspis_core.field.QM31.ZERO
                                                                                      rw [hunwrapFinal0] at hrun
                                                                                      simp only [bind_tc_ok] at hrun
                                                                                      generalize hfinal1 :
                                                                                        V5RelationPrepareGenerated.v5_cu_probe.decode_qm31
                                                                                          _ 1#usize = final1Result at hrun
                                                                                      cases final1Result with
                                                                                      | fail error => simp [hfinal1] at hrun
                                                                                      | div => simp [hfinal1] at hrun
                                                                                      | ok rawFinal1 =>
                                                                                        simp only [hfinal1, bind_tc_ok] at hrun
                                                                                        obtain ⟨final1, hunwrapFinal1⟩ :=
                                                                                          unwrap_or_succeeds rawFinal1
                                                                                            V5RelationPrepareGenerated.aspis_core.field.QM31.ZERO
                                                                                        rw [hunwrapFinal1] at hrun
                                                                                        simp only [bind_tc_ok] at hrun
                                                                                        generalize hfinal2 :
                                                                                          V5RelationPrepareGenerated.v5_cu_probe.decode_qm31
                                                                                            _ 2#usize = final2Result at hrun
                                                                                        cases final2Result with
                                                                                        | fail error => simp [hfinal2] at hrun
                                                                                        | div => simp [hfinal2] at hrun
                                                                                        | ok rawFinal2 =>
                                                                                          simp only [hfinal2, bind_tc_ok] at hrun
                                                                                          obtain ⟨final2, hunwrapFinal2⟩ :=
                                                                                            unwrap_or_succeeds rawFinal2
                                                                                              V5RelationPrepareGenerated.aspis_core.field.QM31.ZERO
                                                                                          rw [hunwrapFinal2] at hrun
                                                                                          simp only [bind_tc_ok] at hrun
                                                                                          generalize hfinal3 :
                                                                                            V5RelationPrepareGenerated.v5_cu_probe.decode_qm31
                                                                                              _ 3#usize = final3Result at hrun
                                                                                          cases final3Result with
                                                                                          | fail error => simp [hfinal3] at hrun
                                                                                          | div => simp [hfinal3] at hrun
                                                                                          | ok rawFinal3 =>
                                                                                            simp only [hfinal3, bind_tc_ok] at hrun
                                                                                            obtain ⟨final3, hunwrapFinal3⟩ :=
                                                                                              unwrap_or_succeeds rawFinal3
                                                                                                V5RelationPrepareGenerated.aspis_core.field.QM31.ZERO
                                                                                            rw [hunwrapFinal3] at hrun
                                                                                            simp only [bind_tc_ok] at hrun
                                                                                            first
                                                                                            | let properties :=
                                                                                                returned_relation_has_log_len_ten
                                                                                                  _ relation _ point _ denseScale hlog4 hrun
                                                                                              exact ⟨properties.1, ⟨{
                                                                                                kappa2 := kappa2
                                                                                                kappa3 := kappa3
                                                                                                claim0 := claim0
                                                                                                claim1 := claim1
                                                                                                claim2 := claim2
                                                                                                claim3 := claim3
                                                                                                relationValue0 := relationValue0
                                                                                                scaled1 := scaled1
                                                                                                relationValue1 := relationValue1
                                                                                                scaled2 := scaled2
                                                                                                relationValue2 := relationValue2
                                                                                                scaled3 := scaled3
                                                                                                relationValue3 := relationValue3
                                                                                                kappa2Run := hkappa2
                                                                                                kappa3Run := hkappa3
                                                                                                claim0Run := hclaim0
                                                                                                relationValue0Run := hvalue0
                                                                                                claim1Run := hclaim1
                                                                                                scaled1Run := hscaled1
                                                                                                relationValue1Run := hvalue1
                                                                                                claim2Run := hclaim2
                                                                                                scaled2Run := hscaled2
                                                                                                relationValue2Run := hvalue2
                                                                                                claim3Run := hclaim3
                                                                                                scaled3Run := hscaled3
                                                                                                relationValue3Run := hvalue3
                                                                                                returnedRelationValue := properties.2 }⟩⟩
                                                                                            | let properties :=
                                                                                                checked_nonreal_relation_has_log_len_ten
                                                                                                  weights4 relationValue3 _ _ point0 kappa3
                                                                                                  relation point denseScale hlog4 hrun
                                                                                              exact ⟨properties.1, ⟨{
                                                                                                kappa2 := kappa2
                                                                                                kappa3 := kappa3
                                                                                                claim0 := claim0
                                                                                                claim1 := claim1
                                                                                                claim2 := claim2
                                                                                                claim3 := claim3
                                                                                                relationValue0 := relationValue0
                                                                                                scaled1 := scaled1
                                                                                                relationValue1 := relationValue1
                                                                                                scaled2 := scaled2
                                                                                                relationValue2 := relationValue2
                                                                                                scaled3 := scaled3
                                                                                                relationValue3 := relationValue3
                                                                                                kappa2Run := hkappa2
                                                                                                kappa3Run := hkappa3
                                                                                                claim0Run := hclaim0
                                                                                                relationValue0Run := hvalue0
                                                                                                claim1Run := hclaim1
                                                                                                scaled1Run := hscaled1
                                                                                                relationValue1Run := hvalue1
                                                                                                claim2Run := hclaim2
                                                                                                scaled2Run := hscaled2
                                                                                                relationValue2Run := hvalue2
                                                                                                claim3Run := hclaim3
                                                                                                scaled3Run := hscaled3
                                                                                                relationValue3Run := hvalue3
                                                                                                returnedRelationValue := properties.2 }⟩⟩

/-- The log-length projection retained for existing callers. -/
theorem prepare_for_extraction_success_has_log_len_ten
    (parsed : V5RelationPrepareGenerated.v5_cu_probe.ParsedProbeData)
    (kappa inactiveClaim : V5RelationPrepareGenerated.aspis_core.field.QM31)
    (preparedClaims :
      V5RelationPrepareGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims)
    (relation : V5RelationPrepareGenerated.v5_cu_probe.PreparedRelation)
    (point : Array V5RelationPrepareGenerated.aspis_core.field.QM31 10#usize)
    (denseScale : V5RelationPrepareGenerated.aspis_core.field.QM31)
    (hrun :
      V5RelationPrepareGenerated.v5_cu_probe.prepare_relation_base_with_kappa_prepared_for_extraction
          parsed kappa inactiveClaim preparedClaims =
        .ok (.Ok (relation, point, denseScale))) :
    relation.weights.log_len = 10#u32 :=
  (prepare_for_extraction_success_exposes_arithmetic parsed kappa inactiveClaim
    preparedClaims relation point denseScale hrun).1

/-- The exact caller-facing theorem needed by the accepted relation/Fri
composition: every successful released four-claim preparation returns weights
with ten variables. -/
theorem prepareSuccess_implies_weights_log_len
    (parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData)
    (kappa inactiveClaim : V5RelationCallerGenerated.aspis_core.field.QM31)
    (preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims)
    (relation : V5RelationCallerGenerated.v5_cu_probe.PreparedRelation)
    (ignoredAlphas :
      Array V5RelationCallerGenerated.aspis_core.field.QM31 10#usize)
    (denseScale : V5RelationCallerGenerated.aspis_core.field.QM31)
    (hrun :
      V5RelationCallerGenerated.v5_cu_probe.prepare_relation_base_with_kappa_prepared
          parsed
          V5RelationCallerGenerated.v5_cu_probe.RelationVariant.FourClaimsCompact
          kappa inactiveClaim preparedClaims =
        .ok (.Ok (relation, ignoredAlphas, denseScale))) :
    relation.weights.log_len = 10#u32 := by
  unfold
    V5RelationCallerGenerated.v5_cu_probe.prepare_relation_base_with_kappa_prepared at hrun
  generalize hsource :
      V5RelationPrepareGenerated.v5_cu_probe.prepare_relation_base_with_kappa_prepared_for_extraction
        _ _ _ _ = sourceResult at hrun
  cases sourceResult with
  | fail error => simp [hsource] at hrun
  | div => simp [hsource] at hrun
  | ok sourceResult =>
    simp only [hsource, bind_tc_ok] at hrun
    cases sourceResult with
    | Err error =>
      simp only at hrun
      exact (core_error_ne_ok
        V5RelationCallerGenerated.solana_program_error.ProgramError.InvalidAccountData
        (relation, ignoredAlphas, denseScale) (Result.ok.inj hrun)).elim
    | Ok sourceTriple =>
      rcases sourceTriple with ⟨sourceRelation, sourcePoint, sourceScale⟩
      have hsourceLog := prepare_for_extraction_success_has_log_len_ten
        _ _ _ _ sourceRelation sourcePoint sourceScale hsource
      simp only at hrun
      have houter := Result.ok.inj hrun
      have htriple := core.result.Result.Ok.inj houter
      have hlogLen := congrArg (fun triple => triple.1.weights.log_len) htriple
      change sourceRelation.weights.log_len = relation.weights.log_len at hlogLen
      exact hlogLen.symm.trans hsourceLog

end Prepare

end AspisV5RelationPrepareLogLenProof
