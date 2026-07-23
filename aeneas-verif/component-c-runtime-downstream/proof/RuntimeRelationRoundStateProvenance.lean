import RuntimeRelationSampleStorage
import RuntimeRelationRoundControlFlow

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeRelationRoundStateProvenance

open aspis_prover

abbrev RawQM31 := aspis_core.field.QM31
abbrev RuntimeRelation :=
  v5_mask.relation_prover.V5IncrementalRelation

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

/-- The actual generated polynomial step installs the exact returned seven
coefficients in the current round and preserves the accumulated OOD values. -/
theorem generated_polynomial_success_state
    (relation relationOut : RuntimeRelation)
    (polynomial : Array RawQM31 7#usize)
    (table : alloc.vec.Vec RawQM31)
    (hround : relation.round.val < 4)
    (hsamples : relation.samples = 2#usize)
    (hrun :
      v5_mask.relation_prover.V5IncrementalRelation.polynomial_with_table
          relation =
        ok (core.result.Result.Ok (polynomial, table), relationOut)) :
    relationOut.sumchecks =
      relation.sumchecks.set relation.round polynomial ∧
    relationOut.sumchecks.val[relation.round.val]! = polynomial ∧
    relationOut.ood_values = relation.ood_values ∧
    relationOut.coefficients = relation.coefficients ∧
    relationOut.round = relation.round ∧
    relationOut.samples = relation.samples := by
  unfold
    v5_mask.relation_prover.V5IncrementalRelation.polynomial_with_table at hrun
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
  generalize hmaterialize :
      v5_mask.relation_prover.V5IncrementalRelation.materialize_weights
          relation.weights (alloc.vec.Vec.len relation.coefficients) =
        tableResult at hrun
  cases tableResult with
  | fail error => simp at hrun
  | div => simp at hrun
  | ok generatedTable =>
    simp only [bind_tc_ok] at hrun
    generalize hpolynomial :
        v5_mask.relation_prover.V5IncrementalRelation.materialized_polynomial
            (alloc.vec.Vec.deref relation.coefficients)
            (alloc.vec.Vec.deref generatedTable) = polynomialResult at hrun
    cases polynomialResult with
    | fail error => simp at hrun
    | div => simp at hrun
    | ok generatedPolynomial =>
      simp only [bind_tc_ok] at hrun
      generalize hboundary :
          aspis_core.sumcheck.boundary_sum generatedPolynomial =
            boundaryResult at hrun
      cases boundaryResult with
      | fail error => simp at hrun
      | div => simp at hrun
      | ok boundary =>
        simp only [bind_tc_ok] at hrun
        generalize hne :
            core.cmp.PartialEq.ne.trait_default
                aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                boundary relation.running_claim = neResult at hrun
        cases neResult with
        | fail error => simp at hrun
        | div => simp at hrun
        | ok differs =>
          by_cases hdiffers : differs = true
          · simp [hdiffers] at hrun
          · simp only [hdiffers] at hrun
            rw [generated_array_update_run relation.sumchecks relation.round
              generatedPolynomial hround] at hrun
            simp only [bind_tc_ok] at hrun
            cases hrun
            refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
            exact array_set_get_same relation.sumchecks relation.round
              polynomial hround

#print axioms generated_polynomial_success_state

/-- Success of the generated polynomial step proves its own round/sample
guards.  Keeping this as a conclusion removes the need for callers to carry a
separate pre-fold state premise. -/
theorem generated_polynomial_success_requires_state
    (relation relationOut : RuntimeRelation)
    (polynomial : Array RawQM31 7#usize)
    (table : alloc.vec.Vec RawQM31)
    (hrun :
      v5_mask.relation_prover.V5IncrementalRelation.polynomial_with_table
          relation =
        ok (core.result.Result.Ok (polynomial, table), relationOut)) :
    relation.round.val < 4 ∧ relation.samples = 2#usize := by
  unfold
    v5_mask.relation_prover.V5IncrementalRelation.polynomial_with_table at hrun
  by_cases hround :
      relation.round >= aspis_core.circle_prefix.CANDIDATE_ROUND_COUNT
  · simp [hround] at hrun
  · rw [if_neg hround] at hrun
    by_cases hsamples :
        (relation.samples !=
          aspis_core.circle_prefix.CANDIDATE_OOD_SAMPLES) = true
    · simp [hsamples] at hrun
    · have hsamplesEq :
          relation.samples =
            aspis_core.circle_prefix.CANDIDATE_OOD_SAMPLES := by
        apply UScalar.eq_of_val_eq
        simpa using hsamples
      constructor
      · simp only [aspis_core.circle_prefix.CANDIDATE_ROUND_COUNT] at hround
        scalar_tac
      · simpa [aspis_core.circle_prefix.CANDIDATE_OOD_SAMPLES] using
          hsamplesEq

#print axioms generated_polynomial_success_requires_state

/-- A successful generated relation fold changes the coefficient/weight
state but carries both released arrays through byte-for-byte. -/
theorem generated_fold_success_preserves_released_arrays
    (relation relationOut : RuntimeRelation) (alpha : RawQM31)
    (hround : relation.round.val < 4)
    (hsamples : relation.samples = 2#usize)
    (hrun :
      v5_mask.relation_prover.V5IncrementalRelation.fold relation alpha =
        ok (core.result.Result.Ok (), relationOut)) :
    relationOut.ood_values = relation.ood_values ∧
    relationOut.sumchecks = relation.sumchecks ∧
    relationOut.round = Std.Usize.wrapping_add relation.round 1#usize ∧
    relationOut.samples = 0#usize := by
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
      generalize hnext0 :
          lift (Std.Usize.wrapping_add relation.round 1#usize) =
            next0Result at hrun
      cases next0Result with
      | fail error => simp at hrun
      | div => simp at hrun
      | ok next0 =>
        simp only [bind_tc_ok] at hrun
        simp only [Std.lift] at hnext0
        cases hnext0
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
                    exact ⟨rfl, rfl, rfl, rfl⟩

#print axioms generated_fold_success_preserves_released_arrays

/-- The successful relation fold installs the output of the very same
source-extracted natural arity-four coefficient fold call.  This is the
missing state edge needed to connect four generated relation rounds to the
maintained final-coefficient map; no pre-fold coefficient equality is
assumed. -/
theorem generated_fold_success_exposes_coefficients
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
      generalize hnext0 :
          lift (Std.Usize.wrapping_add relation.round 1#usize) =
            next0Result at hrun
      cases next0Result with
      | fail error => simp at hrun
      | div => simp at hrun
      | ok next0 =>
        simp only [bind_tc_ok] at hrun
        simp only [Std.lift] at hnext0
        cases hnext0
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

#print axioms generated_fold_success_exposes_coefficients

/-- Success of the generated fold likewise proves its own order guards. -/
theorem generated_fold_success_requires_state
    (relation relationOut : RuntimeRelation) (alpha : RawQM31)
    (hrun :
      v5_mask.relation_prover.V5IncrementalRelation.fold relation alpha =
        ok (core.result.Result.Ok (), relationOut)) :
    relation.round.val < 4 ∧ relation.samples = 2#usize := by
  unfold v5_mask.relation_prover.V5IncrementalRelation.fold at hrun
  by_cases hround :
      relation.round >= aspis_core.circle_prefix.CANDIDATE_ROUND_COUNT
  · simp [hround] at hrun
  · rw [if_neg hround] at hrun
    by_cases hsamples :
        (relation.samples !=
          aspis_core.circle_prefix.CANDIDATE_OOD_SAMPLES) = true
    · simp [hsamples] at hrun
    · have hsamplesEq :
          relation.samples =
            aspis_core.circle_prefix.CANDIDATE_OOD_SAMPLES := by
        apply UScalar.eq_of_val_eq
        simpa using hsamples
      constructor
      · simp only [aspis_core.circle_prefix.CANDIDATE_ROUND_COUNT] at hround
        scalar_tac
      · simpa [aspis_core.circle_prefix.CANDIDATE_OOD_SAMPLES] using
          hsamplesEq

#print axioms generated_fold_success_requires_state

end aspis_prover.ComponentCRuntimeRelationRoundStateProvenance
