import V7K13AddBatch.Funs

/-!
# Literal source trace for Tag-73 query-batch insertion

This theorem decomposes one successful translated execution of
`add_v7_final256_query_batch_shifted`.  It exposes the exact ordered shifted
rho scale chain,
the exact line-covector insertion call, the exact dot-product call over the
authenticated folded values, and the exact running-claim update.  It makes no
pointwise final-polynomial claim.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7K13AddBatchGenerated

namespace AspisV7K13QueryBatchInsertionTrace

abbrev RawQM31 := field.QM31
abbrev RawWeights := sumcheck.WeightAccumulator
abbrev AuthenticatedBatch := v6_query_batch.V6AuthenticatedQueryBatch

/-- Every field is an actual intermediate result from the same successful
translated call.  In particular, the scale array is fixed syntactically and
cannot be supplied by a source-facing premise. -/
structure AcceptedQueryBatchInsertionTrace
    (weights : RawWeights) (runningClaim : RawQM31)
    (queries : Array Std.U32 16#usize)
    (authenticated : AuthenticatedBatch) (rho : RawQM31)
    (claimIncrement : RawQM31) (weightsAfter : RawWeights)
    (runningClaimAfter : RawQM31) : Type where
  preparedRho : field.PreparedQm31Multiplier
  preparedRhoSuccess :
    field.PreparedQm31Multiplier.new rho = ok preparedRho
  scale1 : RawQM31
  scale2 : RawQM31
  scale3 : RawQM31
  scale4 : RawQM31
  scale5 : RawQM31
  scale6 : RawQM31
  scale7 : RawQM31
  scale8 : RawQM31
  scale9 : RawQM31
  scale10 : RawQM31
  scale11 : RawQM31
  scale12 : RawQM31
  scale13 : RawQM31
  scale14 : RawQM31
  scale15 : RawQM31
  scale1Success :
    field.PreparedQm31Multiplier.mul preparedRho rho = ok scale1
  scale2Success : field.PreparedQm31Multiplier.mul preparedRho scale1 = ok scale2
  scale3Success : field.PreparedQm31Multiplier.mul preparedRho scale2 = ok scale3
  scale4Success : field.PreparedQm31Multiplier.mul preparedRho scale3 = ok scale4
  scale5Success : field.PreparedQm31Multiplier.mul preparedRho scale4 = ok scale5
  scale6Success : field.PreparedQm31Multiplier.mul preparedRho scale5 = ok scale6
  scale7Success : field.PreparedQm31Multiplier.mul preparedRho scale6 = ok scale7
  scale8Success : field.PreparedQm31Multiplier.mul preparedRho scale7 = ok scale8
  scale9Success : field.PreparedQm31Multiplier.mul preparedRho scale8 = ok scale9
  scale10Success : field.PreparedQm31Multiplier.mul preparedRho scale9 = ok scale10
  scale11Success : field.PreparedQm31Multiplier.mul preparedRho scale10 = ok scale11
  scale12Success : field.PreparedQm31Multiplier.mul preparedRho scale11 = ok scale12
  scale13Success : field.PreparedQm31Multiplier.mul preparedRho scale12 = ok scale13
  scale14Success : field.PreparedQm31Multiplier.mul preparedRho scale13 = ok scale14
  scale15Success : field.PreparedQm31Multiplier.mul preparedRho scale14 = ok scale15
  scales : Array RawQM31 16#usize
  scalesExact : scales = Array.make 16#usize
    [rho, scale1, scale2, scale3, scale4, scale5, scale6, scale7,
     scale8, scale9, scale10, scale11, scale12, scale13, scale14, scale15]
  weightsInsertSuccess :
    sumcheck.WeightAccumulator.add_line_m31_batch weights
        (Array.to_slice scales) (Array.to_slice authenticated.line_x) =
      ok (core.result.Result.Ok (), weightsAfter)
  claimDotSuccess :
    field.qm31_dot (Array.to_slice scales)
      (Array.to_slice authenticated.values) =
        ok claimIncrement
  runningClaimSuccess :
    field.QM31.add runningClaim claimIncrement = ok runningClaimAfter

/-- Accepted normalized production source exposes the exact query-batch
insertion data.  Validation intermediates are eliminated from the conclusion:
their only role here is selecting the successful branch before the arithmetic
shown in the trace. -/
theorem accepted_query_batch_exposes_exact_insertion
    (weights : RawWeights) (runningClaim : RawQM31)
    (queries : Array Std.U32 16#usize)
    (authenticated : AuthenticatedBatch) (rho : RawQM31)
    (claimIncrement : RawQM31) (weightsAfter : RawWeights)
    (runningClaimAfter : RawQM31)
    (success : v6_query_batch.add_v7_final256_query_batch_shifted weights runningClaim
      queries authenticated rho =
        ok (core.result.Result.Ok claimIncrement, weightsAfter,
          runningClaimAfter)) :
    Nonempty (AcceptedQueryBatchInsertionTrace weights runningClaim queries
      authenticated rho claimIncrement weightsAfter runningClaimAfter) := by
  unfold v6_query_batch.add_v7_final256_query_batch_shifted at success
  unfold v6_query_batch.add_final256_query_batch_with_initial_scale at success
  simp only [lift, Array.to_slice_mut, Bind.bind,
    Aeneas.Std.bind] at success
  cases hsort : core.slice.Slice.sort_unstable core.cmp.OrdU32
      (Array.to_slice queries) <;> simp [hsort] at success
  rename_i sortedSlice
  cases hcountMinus : v6_query_batch.V6_QUERY_BATCH_COUNT - 1#usize <;>
    simp [hcountMinus] at success
  rename_i lastOrdinal
  cases hlast : Array.index_usize
      (Array.from_slice queries sortedSlice) lastOrdinal <;>
    simp [hlast] at success
  rename_i lastQuery
  cases hshift : 1#u32 <<< v6_query_batch.V6_QUERY_BATCH_TREE_DEPTH <;>
    simp [hshift] at success
  rename_i domainSize
  by_cases hout : domainSize.val ≤ lastQuery.val
  · simp [hout] at success
  · simp [hout] at success
    cases hwindows : core.slice.Slice.windows
        (Array.to_slice (Array.from_slice queries sortedSlice)) 2#usize <;>
      simp [hwindows] at success
    rename_i windows
    cases hany : core.iter.traits.iterator.Iterator.any.default
        (core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice
          Std.U32)
        v6_query_batch.add_final256_query_batch_with_initial_scale.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU32Bool
        windows () <;> simp [hany] at success
    rename_i anyResult
    rcases anyResult with ⟨hasDuplicate, windowsAfter⟩
    cases hasDuplicate
    · simp at success
      cases hprepared : field.PreparedQm31Multiplier.new rho <;>
        simp [hprepared] at success
      rename_i preparedRho
      cases hscale1 : field.PreparedQm31Multiplier.mul preparedRho rho <;>
        simp [hscale1] at success
      rename_i scale1
      cases hscale2 : field.PreparedQm31Multiplier.mul preparedRho scale1 <;>
        simp [hscale2] at success
      rename_i scale2
      cases hscale3 : field.PreparedQm31Multiplier.mul preparedRho scale2 <;>
        simp [hscale3] at success
      rename_i scale3
      cases hscale4 : field.PreparedQm31Multiplier.mul preparedRho scale3 <;>
        simp [hscale4] at success
      rename_i scale4
      cases hscale5 : field.PreparedQm31Multiplier.mul preparedRho scale4 <;>
        simp [hscale5] at success
      rename_i scale5
      cases hscale6 : field.PreparedQm31Multiplier.mul preparedRho scale5 <;>
        simp [hscale6] at success
      rename_i scale6
      cases hscale7 : field.PreparedQm31Multiplier.mul preparedRho scale6 <;>
        simp [hscale7] at success
      rename_i scale7
      cases hscale8 : field.PreparedQm31Multiplier.mul preparedRho scale7 <;>
        simp [hscale8] at success
      rename_i scale8
      cases hscale9 : field.PreparedQm31Multiplier.mul preparedRho scale8 <;>
        simp [hscale9] at success
      rename_i scale9
      cases hscale10 : field.PreparedQm31Multiplier.mul preparedRho scale9 <;>
        simp [hscale10] at success
      rename_i scale10
      cases hscale11 : field.PreparedQm31Multiplier.mul preparedRho scale10 <;>
        simp [hscale11] at success
      rename_i scale11
      cases hscale12 : field.PreparedQm31Multiplier.mul preparedRho scale11 <;>
        simp [hscale12] at success
      rename_i scale12
      cases hscale13 : field.PreparedQm31Multiplier.mul preparedRho scale12 <;>
        simp [hscale13] at success
      rename_i scale13
      cases hscale14 : field.PreparedQm31Multiplier.mul preparedRho scale13 <;>
        simp [hscale14] at success
      rename_i scale14
      cases hscale15 : field.PreparedQm31Multiplier.mul preparedRho scale14 <;>
        simp [hscale15] at success
      rename_i scale15
      let scales : Array RawQM31 16#usize := Array.make 16#usize
        [rho, scale1, scale2, scale3, scale4, scale5, scale6,
         scale7, scale8, scale9, scale10, scale11, scale12, scale13, scale14,
         scale15]
      cases hweights : sumcheck.WeightAccumulator.add_line_m31_batch weights
          (Array.to_slice scales) (Array.to_slice authenticated.line_x) <;>
        simp [scales, hweights] at success
      rename_i weightResult
      rcases weightResult with ⟨result, weightsCandidate⟩
      cases result with
      | Err error =>
        simp [core.result.Result.map_err,
          v6_query_batch.add_final256_query_batch_with_initial_scale.closure_1.Insts.CoreOpsFunctionFnOnceTupleTensorWeightErrorV6QueryBatchError.call_once,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
          at success
      | Ok weightUnit =>
        simp [core.result.Result.map_err,
          core.result.Result.Insts.CoreOpsTry.branch] at success
        cases hdot : field.qm31_dot
            (Array.to_slice scales) (Array.to_slice authenticated.values) <;>
          simp [scales, hdot] at success
        rename_i claimCandidate
        cases hadd : field.QM31.add runningClaim claimCandidate <;>
          simp [hadd] at success
        rename_i runningCandidate
        rcases success with ⟨hclaim, hweightsAfter, hrunningAfter⟩
        subst claimCandidate
        subst weightsCandidate
        subst runningCandidate
        cases weightUnit
        refine ⟨{
          preparedRho := preparedRho
          preparedRhoSuccess := hprepared
          scale1 := scale1
          scale2 := scale2
          scale3 := scale3
          scale4 := scale4
          scale5 := scale5
          scale6 := scale6
          scale7 := scale7
          scale8 := scale8
          scale9 := scale9
          scale10 := scale10
          scale11 := scale11
          scale12 := scale12
          scale13 := scale13
          scale14 := scale14
          scale15 := scale15
          scale1Success := hscale1
          scale2Success := hscale2
          scale3Success := hscale3
          scale4Success := hscale4
          scale5Success := hscale5
          scale6Success := hscale6
          scale7Success := hscale7
          scale8Success := hscale8
          scale9Success := hscale9
          scale10Success := hscale10
          scale11Success := hscale11
          scale12Success := hscale12
          scale13Success := hscale13
          scale14Success := hscale14
          scale15Success := hscale15
          scales := scales
          scalesExact := rfl
          weightsInsertSuccess := by simpa [scales] using hweights
          claimDotSuccess := by simpa [scales] using hdot
          runningClaimSuccess := hadd }⟩
    · simp at success

#print axioms accepted_query_batch_exposes_exact_insertion

end AspisV7K13QueryBatchInsertionTrace
