import RuntimeFourRoundLaterMaintained
import RuntimeFourRoundFinalCoefficients
import RuntimePublicPackerCapstone
import RuntimeRelationRoundOodSemantics
import RuntimeRelationRoundPolynomialSemantics
import RuntimeTraceCodewordMaintainedLayer

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeReleasedTraceFamiliesSourceJoin

open aspis_prover
open AspisV5ComponentCDownstreamDeployed
open ComponentCRuntimeFoldPrimitiveInstantiation
open ComponentCRuntimeMaterializedRelationArithmetic

abbrev RawQM31 := aspis_core.field.QM31
abbrev RuntimeRelation :=
  v5_mask.relation_prover.V5IncrementalRelation
abbrev RuntimeTrace := v5_mask.relation_prover.V5RelationTrace
abbrev RuntimeTables :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeRelationTables

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-! ## Source-defined relation-table schedule packaging -/

/-- Replace the relation OOD/polynomial fields of a maintained schedule by
the exact tables stored by the generated four-round runtime.  This makes the
table/view equalities definitional while preserving every FRI/later field.
Length and canonicality are deliberately not asserted by this constructor. -/
def withGeneratedRelationTables
    (base : DeployedRuntimeSchedule F K) (tables : RuntimeTables)
    (view : RawQM31 → K) : DeployedRuntimeSchedule F K where
  alpha := base.alpha
  ood0 := fun sample index =>
    view tables.ood.val[0]!.val[sample.val]!.val[index.val]!
  ood1 := fun sample index =>
    view tables.ood.val[1]!.val[sample.val]!.val[index.val]!
  ood2 := fun sample index =>
    view tables.ood.val[2]!.val[sample.val]!.val[index.val]!
  ood3 := fun sample index =>
    view tables.ood.val[3]!.val[sample.val]!.val[index.val]!
  poly0 := fun index =>
    view tables.polynomial.val[0]!.val[index.val]!
  poly1 := fun index =>
    view tables.polynomial.val[1]!.val[index.val]!
  poly2 := fun index =>
    view tables.polynomial.val[2]!.val[index.val]!
  poly3 := fun index =>
    view tables.polynomial.val[3]!.val[index.val]!
  circleInv2x := base.circleInv2x
  circleInv2y := base.circleInv2y
  line1Inverse := base.line1Inverse
  line2Inverse := base.line2Inverse
  line3Inverse := base.line3Inverse
  later1Count := base.later1Count
  later2Count := base.later2Count
  later3Count := base.later3Count
  later1Fibre := base.later1Fibre
  later2Fibre := base.later2Fibre
  later3Fibre := base.later3Fibre
  finalX := base.finalX

@[simp] theorem withGeneratedRelationTables_ood0
    (base : DeployedRuntimeSchedule F K) (tables : RuntimeTables)
    (view : RawQM31 → K) (sample : Fin 2) (index : Fin 1024) :
    (withGeneratedRelationTables base tables view).ood0 sample index =
      view tables.ood.val[0]!.val[sample.val]!.val[index.val]! := rfl

@[simp] theorem withGeneratedRelationTables_ood1
    (base : DeployedRuntimeSchedule F K) (tables : RuntimeTables)
    (view : RawQM31 → K) (sample : Fin 2) (index : Fin 256) :
    (withGeneratedRelationTables base tables view).ood1 sample index =
      view tables.ood.val[1]!.val[sample.val]!.val[index.val]! := rfl

@[simp] theorem withGeneratedRelationTables_ood2
    (base : DeployedRuntimeSchedule F K) (tables : RuntimeTables)
    (view : RawQM31 → K) (sample : Fin 2) (index : Fin 64) :
    (withGeneratedRelationTables base tables view).ood2 sample index =
      view tables.ood.val[2]!.val[sample.val]!.val[index.val]! := rfl

@[simp] theorem withGeneratedRelationTables_ood3
    (base : DeployedRuntimeSchedule F K) (tables : RuntimeTables)
    (view : RawQM31 → K) (sample : Fin 2) (index : Fin 16) :
    (withGeneratedRelationTables base tables view).ood3 sample index =
      view tables.ood.val[3]!.val[sample.val]!.val[index.val]! := rfl

@[simp] theorem withGeneratedRelationTables_poly0
    (base : DeployedRuntimeSchedule F K) (tables : RuntimeTables)
    (view : RawQM31 → K) (index : Fin 1024) :
    (withGeneratedRelationTables base tables view).poly0 index =
      view tables.polynomial.val[0]!.val[index.val]! := rfl

@[simp] theorem withGeneratedRelationTables_poly1
    (base : DeployedRuntimeSchedule F K) (tables : RuntimeTables)
    (view : RawQM31 → K) (index : Fin 256) :
    (withGeneratedRelationTables base tables view).poly1 index =
      view tables.polynomial.val[1]!.val[index.val]! := rfl

@[simp] theorem withGeneratedRelationTables_poly2
    (base : DeployedRuntimeSchedule F K) (tables : RuntimeTables)
    (view : RawQM31 → K) (index : Fin 64) :
    (withGeneratedRelationTables base tables view).poly2 index =
      view tables.polynomial.val[2]!.val[index.val]! := rfl

@[simp] theorem withGeneratedRelationTables_poly3
    (base : DeployedRuntimeSchedule F K) (tables : RuntimeTables)
    (view : RawQM31 → K) (index : Fin 16) :
    (withGeneratedRelationTables base tables view).poly3 index =
      view tables.polynomial.val[3]!.val[index.val]! := rfl

/-! ## Generated coefficient-state fields omitted by the earlier projections -/

/-- A successful generated relation fold installs the exact vector returned by
`fold_adjacent_natural_arity4` in the next relation state.  This is a direct
field equation about the extracted Rust definition; no maintained evaluator
premise is involved. -/
theorem generated_fold_success_sets_coefficients
    (relation relationOut : RuntimeRelation) (alpha : RawQM31)
    (hround : relation.round.val < 4)
    (hsamples : relation.samples = 2#usize)
    (hrun :
      v5_mask.relation_prover.V5IncrementalRelation.fold relation alpha =
        ok (core.result.Result.Ok (), relationOut)) :
    ∃ coefficientsAfter : alloc.vec.Vec RawQM31,
      circle_candidate.fold_adjacent_natural_arity4
          (alloc.vec.Vec.deref relation.coefficients) alpha =
        ok coefficientsAfter ∧
      relationOut.coefficients = coefficientsAfter := by
  unfold v5_mask.relation_prover.V5IncrementalRelation.fold at hrun
  have hroundNotGe :
      ¬ relation.round >= aspis_core.circle_prefix.CANDIDATE_ROUND_COUNT := by
    simp only [aspis_core.circle_prefix.CANDIDATE_ROUND_COUNT]
    scalar_tac
  rw [if_neg hroundNotGe] at hrun
  have hsamplesEq :
      (relation.samples != aspis_core.circle_prefix.CANDIDATE_OOD_SAMPLES) =
        false := by
    simp [hsamples, aspis_core.circle_prefix.CANDIDATE_OOD_SAMPLES]
  simp only [hsamplesEq, Bool.false_eq_true, if_false] at hrun
  generalize hsumcheck :
      Array.index_usize relation.sumchecks relation.round =
        sumcheckResult at hrun
  cases sumcheckResult with
  | fail error => simp at hrun
  | div => simp at hrun
  | ok sumcheck =>
    simp only [bind_tc_ok] at hrun
    generalize hevaluate :
        aspis_core.sumcheck.evaluate sumcheck alpha = evaluateResult at hrun
    cases evaluateResult with
    | fail error => simp at hrun
    | div => simp at hrun
    | ok claim =>
      simp only [bind_tc_ok] at hrun
      generalize hnext :
          lift (Std.Usize.wrapping_add relation.round 1#usize) =
            nextResult at hrun
      cases nextResult with
      | fail error => simp at hrun
      | div => simp at hrun
      | ok next =>
        simp only [bind_tc_ok] at hrun
        simp only [Std.lift] at hnext
        cases hnext
        generalize hclaimsBorrow :
            Array.index_mut_usize relation.running_claims
                (Std.Usize.wrapping_add relation.round 1#usize) =
              claimsBorrowResult at hrun
        cases claimsBorrowResult with
        | fail error => simp at hrun
        | div => simp at hrun
        | ok claimsBorrow =>
          rcases claimsBorrow with ⟨oldClaim, restoreClaim⟩
          simp only [bind_tc_ok] at hrun
          generalize hweights :
              aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4
                  relation.weights alpha = weightsResult at hrun
          cases weightsResult with
          | fail error => simp at hrun
          | div => simp at hrun
          | ok weightsAfter =>
            simp only [bind_tc_ok] at hrun
            generalize hcoefficients :
                circle_candidate.fold_adjacent_natural_arity4
                    (alloc.vec.Vec.deref relation.coefficients) alpha =
                  coefficientsResult at hrun
            cases coefficientsResult with
            | fail error => simp at hrun
            | div => simp at hrun
            | ok coefficientsAfter =>
              simp only [bind_tc_ok] at hrun
              generalize hdot :
                  aspis_core.sumcheck.WeightAccumulator.dot weightsAfter
                      (alloc.vec.Vec.deref coefficientsAfter) = dotResult at hrun
              cases dotResult with
              | fail error => simp at hrun
              | div => simp at hrun
              | ok foldedClaim =>
                simp only [bind_tc_ok] at hrun
                generalize hne :
                    core.cmp.PartialEq.ne.trait_default
                        aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                        foldedClaim claim = neResult at hrun
                cases neResult with
                | fail error => simp at hrun
                | div => simp at hrun
                | ok differs =>
                  by_cases hdiffers : differs = true
                  · simp [hdiffers] at hrun
                  · simp only [hdiffers] at hrun
                    cases hrun
                    exact ⟨coefficientsAfter, rfl, rfl⟩

/-- Successful `finish` copies the four final relation coefficients into the
released trace without a permutation. -/
theorem generated_finish_success_final_coefficients
    (relation : RuntimeRelation) (trace : RuntimeTrace)
    (hrun :
      v5_mask.relation_prover.V5IncrementalRelation.finish relation =
        ok (core.result.Result.Ok trace)) :
    trace.final_coefficients.val = relation.coefficients.val := by
  unfold v5_mask.relation_prover.V5IncrementalRelation.finish at hrun
  by_cases hround :
      (relation.round != aspis_core.circle_prefix.CANDIDATE_ROUND_COUNT) = true
  · simp [hround] at hrun
  · simp only [hround, Bool.false_eq_true, if_false] at hrun
    by_cases hsamples : (relation.samples != 0#usize) = true
    · simp [hsamples] at hrun
    · simp only [hsamples, Bool.false_eq_true, if_false] at hrun
      generalize hfinalLen :
          aspis_core.circle_prefix.CANDIDATE_FINAL_POLY_LEN = finalLenResult
        at hrun
      cases finalLenResult with
      | fail error => simp at hrun
      | div => simp at hrun
      | ok finalLen =>
        simp only [bind_tc_ok] at hrun
        by_cases hlength :
            (alloc.vec.Vec.len relation.coefficients != finalLen) = true
        · simp [hlength] at hrun
        · simp only [hlength, Bool.false_eq_true, if_false] at hrun
          generalize hslice :
              alloc.vec.Vec.as_slice Global relation.coefficients = sliceResult
            at hrun
          cases sliceResult with
          | fail error => simp at hrun
          | div => simp at hrun
          | ok coefficientsSlice =>
            simp only [bind_tc_ok] at hrun
            have hsliceValues :
                coefficientsSlice.val = relation.coefficients.val := by
              change
                ok (⟨relation.coefficients.val,
                  relation.coefficients.property⟩ : Slice RawQM31) =
                    ok coefficientsSlice at hslice
              injection hslice with hsliceEq
              exact congrArg (fun values : Slice RawQM31 => values.val)
                hsliceEq.symm
            generalize harray :
                core.array.TryFromArrayCopySlice.try_from 4#usize
                    aspis_core.field.QM31.Insts.CoreMarkerCopy coefficientsSlice =
                  arrayResult at hrun
            cases arrayResult with
            | fail error => simp at hrun
            | div => simp at hrun
            | ok arrayStatus =>
              cases arrayStatus with
              | Err arrayError =>
                simp [core.result.Result.map_err,
                  v5_mask.relation_prover.V5IncrementalRelation.finish.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorV5RelationProverError.call_once,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  core.convert.FromSame.from] at hrun
              | Ok finalCoefficients =>
                have harrayValues :
                    finalCoefficients.val = coefficientsSlice.val := by
                  have hspec :=
                    core.array.TryFromArrayCopySlice.try_from.step
                      4#usize
                      aspis_core.field.QM31.Insts.CoreMarkerCopy
                      coefficientsSlice
                  obtain ⟨result, hresult, hpost⟩ :=
                    Aeneas.Std.WP.spec_imp_exists hspec
                  rw [harray] at hresult
                  simp only [ok.injEq] at hresult
                  subst result
                  exact hpost.1
                simp only [core.result.Result.map_err, bind_tc_ok,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  Std.lift] at hrun
                let finalSlice := Array.to_slice finalCoefficients
                change (do
                    let q ← aspis_core.sumcheck.WeightAccumulator.dot
                      relation.weights finalSlice
                    let b ← core.cmp.PartialEq.ne.trait_default
                      aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 q
                      relation.running_claim
                    if b = true then
                      ok (core.result.Result.Err
                        v5_mask.relation_prover.V5RelationProverError.FoldMismatch)
                    else
                      ok (core.result.Result.Ok {
                        point_claims := relation.point_claims,
                        terminal_claim := relation.terminal_claim,
                        ood_values := relation.ood_values,
                        sumchecks := relation.sumchecks,
                        running_claims := relation.running_claims,
                        final_coefficients := finalCoefficients })) =
                  ok (core.result.Result.Ok trace) at hrun
                generalize hdot :
                    aspis_core.sumcheck.WeightAccumulator.dot
                        relation.weights finalSlice = dotResult at hrun
                cases dotResult with
                | fail error => simp at hrun
                | div => simp at hrun
                | ok dot =>
                  simp only [bind_tc_ok] at hrun
                  generalize hne :
                      core.cmp.PartialEq.ne.trait_default
                          aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                          dot relation.running_claim = neResult at hrun
                  cases neResult with
                  | fail error => simp at hrun
                  | div => simp at hrun
                  | ok differs =>
                    by_cases hdiffers : differs = true
                    · simp [hdiffers] at hrun
                    · simp only [hdiffers] at hrun
                      cases hrun
                      exact harrayValues.trans hsliceValues

/-! ## Materialized-table shape -/

private theorem wrapping_succ_val
    (index : Std.Usize) (hindex : index.val < 1024) :
    (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  have hroom : 1025 < UScalar.size .Usize := by
    have h := (1025#usize).hSize
    scalar_tac
  change index.val + 1 < UScalar.size .Usize
  omega

private theorem materialize_weights_loop_success_length
    (weights : aspis_core.sumcheck.WeightAccumulator)
    (len : Std.Usize) (table : alloc.vec.Vec RawQM31)
    (index : Std.Usize) (out : alloc.vec.Vec RawQM31)
    (hindex : index.val ≤ len.val)
    (hlen : len.val ≤ 1024)
    (htable : table.val.length = index.val)
    (hrun :
      v5_mask.relation_prover.V5IncrementalRelation.materialize_weights_loop
          weights len table index = ok out) :
    out.val.length = len.val := by
  unfold
    v5_mask.relation_prover.V5IncrementalRelation.materialize_weights_loop
    at hrun
  rw [loop.eq_1] at hrun
  unfold
    v5_mask.relation_prover.V5IncrementalRelation.materialize_weights_loop.body
    at hrun
  simp only [] at hrun
  by_cases hactive : index.val < len.val
  · have hactiveScalar : index < len := by scalar_tac
    rw [if_pos hactiveScalar] at hrun
    generalize hcast :
        lift (UScalar.cast .U32 index) = castResult at hrun
    cases castResult with
    | fail error => simp at hrun
    | div => simp at hrun
    | ok rawIndex =>
      simp only [bind_tc_ok] at hrun
      generalize hweight :
          aspis_core.sumcheck.WeightAccumulator.weight_at weights rawIndex =
            weightResult at hrun
      cases weightResult with
      | fail error => simp at hrun
      | div => simp at hrun
      | ok weight =>
        simp only [bind_tc_ok] at hrun
        generalize hpush : alloc.vec.Vec.push table weight = pushResult at hrun
        cases pushResult with
        | fail error => simp at hrun
        | div => simp at hrun
        | ok tableAfter =>
          simp only [bind_tc_ok] at hrun
          generalize hnext :
              lift (Std.Usize.wrapping_add index 1#usize) = nextResult at hrun
          cases nextResult with
          | fail error => simp at hrun
          | div => simp at hrun
          | ok nextIndex =>
            simp only [bind_tc_ok] at hrun
            simp only [Std.lift] at hnext
            cases hnext
            have hindexSmall : index.val < 1024 := by omega
            have hnextValue :
                (Std.Usize.wrapping_add index 1#usize).val =
                  index.val + 1 :=
              wrapping_succ_val index hindexSmall
            have htableRoom : table.val.length < Std.Usize.max := by
              rw [htable]
              have hmax := (1025#usize).hSize
              scalar_tac
            have hpushSpec := alloc.vec.Vec.push_spec table weight htableRoom
            obtain ⟨actual, hactual, hactualValues⟩ :=
              Aeneas.Std.WP.spec_imp_exists hpushSpec
            rw [hpush] at hactual
            simp only [ok.injEq] at hactual
            subst actual
            have htableAfter :
                tableAfter.val.length =
                  (Std.Usize.wrapping_add index 1#usize).val := by
              rw [hactualValues, List.length_append, List.length_singleton,
                htable, hnextValue]
            exact materialize_weights_loop_success_length
              weights len tableAfter (Std.Usize.wrapping_add index 1#usize)
              out (by rw [hnextValue]; omega) hlen htableAfter hrun
  · have hdone : index.val = len.val := by omega
    have hdoneScalar : ¬ index < len := by scalar_tac
    rw [if_neg hdoneScalar] at hrun
    simp only [ok.injEq] at hrun
    subst out
    omega
termination_by len.val - index.val
decreasing_by
  rw [hnextValue]
  omega

/-- A successful generated materialization has exactly the requested length.
Thus table shape is not the remaining relation-family seam. -/
theorem generated_materialize_weights_success_length
    (weights : aspis_core.sumcheck.WeightAccumulator)
    (len : Std.Usize) (table : alloc.vec.Vec RawQM31)
    (hlen : len.val ≤ 1024)
    (hrun :
      v5_mask.relation_prover.V5IncrementalRelation.materialize_weights
          weights len = ok table) :
    table.val.length = len.val := by
  unfold v5_mask.relation_prover.V5IncrementalRelation.materialize_weights
    at hrun
  exact materialize_weights_loop_success_length weights len
    (alloc.vec.Vec.with_capacity RawQM31 len) 0#usize table
    (by simp) hlen (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new])
    hrun

/-! ## Exact unresolved generated invariant -/

/-- The missing representation invariant at the first unresolved generated
boundary.  It speaks only about a materialized weight vector returned by the
actual extracted helper.  Unlike a released-family premise, it mentions no
OOD value, polynomial coefficient, maintained row, or serializer coordinate. -/
def MaterializedWeightsCanonical
    (weights : aspis_core.sumcheck.WeightAccumulator) : Prop :=
  ∀ (len : Std.Usize) (table : alloc.vec.Vec RawQM31),
    v5_mask.relation_prover.V5IncrementalRelation.materialize_weights
        weights len = ok table →
    RuntimeCanonicalList table.val

/-- The exact state invariant missing from the generated four-round relation
trace.  These are the eight OOD covector tables and four polynomial weight
tables actually stored by `evaluate_component_c_runtime_relation_round`; no
released value or maintained row equality is included. -/
def GeneratedRelationTablesCanonical (tables : RuntimeTables) : Prop :=
  ∀ round : Fin 4,
    (∀ sample : Fin 2,
      RuntimeCanonicalList
        tables.ood.val[round.val]!.val[sample.val]!.val) ∧
    RuntimeCanonicalList tables.polynomial.val[round.val]!.val

/-- The generated accumulator representation itself carries no corresponding
payload invariant. -/
def DensePayloadsCanonical
    (weights : aspis_core.sumcheck.WeightAccumulator) : Prop :=
  ∀ values : alloc.vec.Vec RawQM31,
    aspis_core.sumcheck.WeightComponent.Dense values ∈
      weights.components.val →
    RuntimeCanonicalList values.val

/-- Public raw constructors permit noncanonical words, so canonical
materialization cannot be inferred from the generated `WeightAccumulator`
type alone. -/
def noncanonicalRawQM31 : RawQM31 :=
  { c0 := { a := 4294967294#u32, b := 0#u32 }
    c1 := { a := 0#u32, b := 0#u32 } }

def noncanonicalDenseAccumulator : aspis_core.sumcheck.WeightAccumulator :=
  { log_len := 0#u32
    components :=
      ⟨[aspis_core.sumcheck.WeightComponent.Dense
        ⟨[noncanonicalRawQM31], by simp; scalar_tac⟩], by simp; scalar_tac⟩ }

theorem noncanonical_raw_qm31_tooth :
    ¬ runtimeCanonicalQM31 noncanonicalRawQM31 := by
  norm_num [noncanonicalRawQM31, runtimeCanonicalQM31,
    runtimeCanonicalCM31, runtimeCanonicalM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31]

/-- Concrete representation tooth: a generated `WeightAccumulator` value can
carry a noncanonical dense payload.  Therefore the missing canonical-table
invariant cannot be recovered from the generated structure type alone. -/
theorem noncanonical_dense_payload_tooth :
    ¬ DensePayloadsCanonical noncanonicalDenseAccumulator := by
  intro hcanonical
  have hdense := hcanonical
    (⟨[noncanonicalRawQM31], by simp; scalar_tac⟩ :
      alloc.vec.Vec RawQM31) (by simp [noncanonicalDenseAccumulator])
  exact noncanonical_raw_qm31_tooth
    (hdense noncanonicalRawQM31 (by simp))

/-- Canonical materialization is exactly sufficient to discharge the table
side condition consumed by the existing exact dot/polynomial arithmetic. -/
theorem materialized_weights_canonical_applies
    (weights : aspis_core.sumcheck.WeightAccumulator)
    (hinvariant : MaterializedWeightsCanonical weights)
    (len : Std.Usize) (table : alloc.vec.Vec RawQM31)
    (hrun :
      v5_mask.relation_prover.V5IncrementalRelation.materialize_weights
          weights len = ok table) :
    RuntimeCanonicalList table.val :=
  hinvariant len table hrun

#print axioms generated_fold_success_sets_coefficients
#print axioms generated_finish_success_final_coefficients
#print axioms generated_materialize_weights_success_length
#print axioms withGeneratedRelationTables_ood0
#print axioms withGeneratedRelationTables_ood1
#print axioms withGeneratedRelationTables_ood2
#print axioms withGeneratedRelationTables_ood3
#print axioms withGeneratedRelationTables_poly0
#print axioms withGeneratedRelationTables_poly1
#print axioms withGeneratedRelationTables_poly2
#print axioms withGeneratedRelationTables_poly3
#print axioms noncanonical_raw_qm31_tooth
#print axioms noncanonical_dense_payload_tooth
#print axioms materialized_weights_canonical_applies

end aspis_prover.ComponentCRuntimeReleasedTraceFamiliesSourceJoin
