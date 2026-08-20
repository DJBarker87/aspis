import V5RelationFullSourceProof

namespace AspisV5RelationFullSuccessInversion

open Aeneas Aeneas.Std Result ControlFlow Error
open V5RelationFullGenerated

abbrev Verified :=
  V5RelationFullGenerated.relation_stress.VerifiedV5RelationStress

abbrev VError :=
  V5RelationFullGenerated.relation_stress.V5RelationStressError

def SafeRoundReturn
    (pending : Option (core.result.Result Verified VError))
    (status : Std.U32) : Prop :=
  (pending = none ∧ status = 1#u32) ∨
    ∃ error, pending = some (.Err error) ∧ status = 0#u32

theorem safeRoundReturn_of_error_output_eq
    {Weight Claim A : Type}
    (weight : Weight) (claim : Claim) (additive : A) (error : VError)
    (nextWeight : Weight) (nextClaim : Claim) (nextAdditive : A)
    (pending : Option (core.result.Result Verified VError))
    (status : Std.U32)
    (outputEq :
      (weight, claim, additive, some (.Err error), 0#u32) =
        (nextWeight, nextClaim, nextAdditive, pending, status)) :
    SafeRoundReturn pending status := by
  have pendingEq := congrArg (fun output => output.2.2.2.1) outputEq
  have statusEq := congrArg (fun output => output.2.2.2.2) outputEq
  right
  exact ⟨error, pendingEq.symm, statusEq.symm⟩

private theorem usizeAddExactLocal (x y z : Std.Usize)
    (hbound : x.val + y.val ≤ Std.Usize.max)
    (hval : z.val = x.val + y.val) :
    x + y = ok z := by
  have hspec := Std.Usize.add_spec (x := x) (y := y) hbound
  obtain ⟨value, valueEquation, valueVal⟩ := WP.spec_imp_exists hspec
  have valueIsZ : value = z := by
    apply UScalar.eq_of_val_eq
    omega
  rw [valueEquation, valueIsZ]

def HasDoneOrigin {State Output : Type}
    (body : State → Aeneas.Std.Result (ControlFlow State Output))
    (result : Aeneas.Std.Result Output) : Prop :=
  match result with
  | .ok output => ∃ state, body state = .ok (.done output)
  | .fail _ | .div => True

theorem loop_ok_has_done_origin
    {State Output : Type}
    (body : State → Aeneas.Std.Result (ControlFlow State Output))
    (initial : State) :
    HasDoneOrigin body (Aeneas.Std.loop body initial) := by
  generalize initial = state
  revert state
  apply Aeneas.Std.loop.fixpoint_induct
    (motive := fun loop' => ∀ state,
      HasDoneOrigin body (loop' state))
  · apply Lean.Order.admissible_pi
    intro state
    apply Lean.Order.admissible_apply
      (fun _ result => HasDoneOrigin body result) state
    apply Lean.Order.admissible_flatOrder
    simp [HasDoneOrigin]
  · intro loop' ih state
    simp only
    cases bodyResult : body state with
    | div => simp [HasDoneOrigin]
    | fail error => simp [HasDoneOrigin]
    | ok flow =>
        cases flow with
        | done output =>
            simp [HasDoneOrigin]
            exact ⟨state, bodyResult⟩
        | cont next =>
            simpa [HasDoneOrigin] using ih next

theorem loop_ok_has_done_origin_eq
    {State Output : Type}
    (body : State → Aeneas.Std.Result (ControlFlow State Output))
    (initial : State) (output : Output)
    (run : Aeneas.Std.loop body initial = .ok output) :
    ∃ state, body state = .ok (.done output) := by
  have origin := loop_ok_has_done_origin body initial
  simpa [HasDoneOrigin, run] using origin

theorem polynomial_loop_safe_round_return
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (toSliceBack : Slice V5RelationFullGenerated.aspis_core.field.QM31 →
      Array V5RelationFullGenerated.aspis_core.field.QM31 7#usize)
    (iterBack : core.slice.iter.IterMut
      V5RelationFullGenerated.aspis_core.field.QM31 →
      Slice V5RelationFullGenerated.aspis_core.field.QM31)
    (enumerateBack : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.IterMut V5RelationFullGenerated.aspis_core.field.QM31) →
      core.slice.iter.IterMut V5RelationFullGenerated.aspis_core.field.QM31)
    (iter : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.IterMut V5RelationFullGenerated.aspis_core.field.QM31))
    (back : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.IterMut V5RelationFullGenerated.aspis_core.field.QM31) →
      core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.IterMut V5RelationFullGenerated.aspis_core.field.QM31))
    (weights nextWeights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (claim nextClaim alpha :
      V5RelationFullGenerated.aspis_core.field.QM31)
    (bytes : Array Std.U8 928#usize)
    (additive nextAdditive : A)
    (round : Std.Usize)
    (pending : Option (core.result.Result Verified VError))
    (status : Std.U32)
    (run :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0
          additiveInst toSliceBack iterBack enumerateBack iter back weights claim
          bytes additive round alpha none =
        .ok (nextWeights, nextClaim, nextAdditive, pending, status)) :
    SafeRoundReturn pending status := by
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0
    at run
  have origin := loop_ok_has_done_origin_eq
    (fun state =>
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0.body
        additiveInst toSliceBack iterBack enumerateBack weights claim bytes additive
        round alpha none state.1 state.2)
    (iter, back) (nextWeights, nextClaim, nextAdditive, pending, status) run
  rcases origin with ⟨⟨originIter, originBack⟩, bodyRun⟩
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0.body
    at bodyRun
  generalize nextEquation : V5MutableEnumerateSupport.next originIter = nextResult
    at bodyRun
  cases nextResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
  | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
  | ok next =>
      rcases next with ⟨option, nextIter, nextBack⟩
      simp only [bind_tc_ok] at bodyRun
      cases option with
      | none =>
          simp only at bodyRun
          generalize boundaryEquation :
            V5RelationFullGenerated.aspis_core.sumcheck.boundary_sum
              (toSliceBack (iterBack (enumerateBack
                (originBack (nextBack nextIter none))))) = boundaryResult
            at bodyRun
          cases boundaryResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
          | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
          | ok boundary =>
              simp only [bind_tc_ok] at bodyRun
              generalize neEquation :
                core.cmp.PartialEq.ne.trait_default
                  V5RelationFullGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                  boundary claim = neResult at bodyRun
              cases neResult with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
              | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
              | ok differs =>
                  simp only [bind_tc_ok] at bodyRun
                  cases differs with
                  | true =>
                      simp only [if_pos rfl] at bodyRun
                      injection bodyRun with tupleEq
                      injection tupleEq with outputEq
                      have pendingEq := congrArg (fun output => output.2.2.2.1)
                        outputEq
                      have statusEq := congrArg (fun output => output.2.2.2.2)
                        outputEq
                      right
                      exact ⟨V5RelationFullGenerated.relation_stress.V5RelationStressError.BoundaryMismatch round,
                        pendingEq.symm, statusEq.symm⟩
                  | false =>
                      simp only [Bool.false_eq_true, if_false] at bodyRun
                      generalize evaluateEquation :
                        V5RelationFullGenerated.aspis_core.sumcheck.evaluate
                          (toSliceBack (iterBack (enumerateBack
                            (originBack (nextBack nextIter none))))) alpha = evaluateResult
                        at bodyRun
                      cases evaluateResult with
                      | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                      | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                      | ok evaluated =>
                          simp only [bind_tc_ok] at bodyRun
                          generalize foldEquation :
                            aspis_core.sumcheck.WeightAccumulator.fold weights alpha =
                              foldResult at bodyRun
                          cases foldResult with
                          | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                          | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                          | ok folded =>
                              simp only [bind_tc_ok] at bodyRun
                              generalize additiveEquation :
                                additiveInst.fold additive alpha = additiveResult at bodyRun
                              cases additiveResult with
                              | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                              | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                              | ok foldedAdditive =>
                                  simp only [bind_tc_ok] at bodyRun
                                  injection bodyRun with tupleEq
                                  injection tupleEq with outputEq
                                  have pendingEq := congrArg
                                    (fun output => output.2.2.2.1) outputEq
                                  have statusEq := congrArg
                                    (fun output => output.2.2.2.2) outputEq
                                  left
                                  exact ⟨pendingEq.symm, statusEq.symm⟩
      | some item =>
          rcases item with ⟨coefficient, value⟩
          simp only [Aeneas.Std.lift, bind_tc_ok] at bodyRun
          generalize offsetEquation :
            V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_SUMCHECK_OFFSET =
              offsetResult at bodyRun
          cases offsetResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
          | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
          | ok offset =>
              simp only [bind_tc_ok] at bodyRun
              generalize decodeEquation :
                V5RelationFullGenerated.relation_stress.decode_indexed bytes offset
                  (Std.Usize.wrapping_add
                    (Std.Usize.wrapping_mul round
                      V5RelationFullGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS)
                    coefficient) = decodeResult at bodyRun
              cases decodeResult with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
              | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
              | ok decoded =>
                  simp only [bind_tc_ok] at bodyRun
                  cases decoded with
                  | Ok decodedValue =>
                      simp only [
                        core.result.Result.Insts.CoreOpsTry.branch,
                        bind_tc_ok] at bodyRun
                      simp at bodyRun
                  | Err decodeError =>
                      simp only [
                        core.result.Result.Insts.CoreOpsTry.branch,
                        bind_tc_ok,
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                        core.convert.FromSame,
                        core.convert.FromSame.from] at bodyRun
                      injection bodyRun with tupleEq
                      injection tupleEq with outputEq
                      have pendingEq := congrArg
                        (fun output => output.2.2.2.1) outputEq
                      have statusEq := congrArg
                        (fun output => output.2.2.2.2) outputEq
                      right
                      exact ⟨decodeError, pendingEq.symm, statusEq.symm⟩

theorem two_sample_loop_safe_round_return
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (range : core.ops.range.Range Std.Usize)
    (weights nextWeights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (claim nextClaim alpha :
      V5RelationFullGenerated.aspis_core.field.QM31)
    (bytes : Array Std.U8 928#usize)
    (additive nextAdditive : A)
    (circlePoints : Array
      V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize)
    (round : Std.Usize)
    (pending : Option (core.result.Result Verified VError))
    (status : Std.U32)
    (run :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0
          additiveInst range weights claim bytes additive circlePoints round alpha none =
        .ok (nextWeights, nextClaim, nextAdditive, pending, status)) :
    SafeRoundReturn pending status := by
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0
    at run
  have origin := loop_ok_has_done_origin_eq
    (fun state =>
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0.body
        additiveInst bytes additive circlePoints round alpha none state.1
        state.2.1 state.2.2)
    (range, weights, claim)
    (nextWeights, nextClaim, nextAdditive, pending, status) run
  rcases origin with ⟨⟨originRange, originWeights, originClaim⟩, bodyRun⟩
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0.body
    at bodyRun
  generalize nextEquation :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize originRange =
      nextResult at bodyRun
  cases nextResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
  | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
  | ok next =>
      rcases next with ⟨option, nextRange⟩
      simp only [bind_tc_ok] at bodyRun
      cases option with
      | none =>
          simp only [Aeneas.Std.lift, bind_tc_ok,
            core.slice.Slice.iter_mut,
            V5MutableEnumerateSupport.enumerate] at bodyRun
          let polynomialIterator : V5MutableEnumerateSupport.MutEnumerate
              V5RelationFullGenerated.aspis_core.field.QM31 :=
            { iter := { slice := (Array.repeat 7#usize
                V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1 }
              count := 0#usize }
          generalize polynomialEquation :
            V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0
              additiveInst
              (Array.repeat 7#usize
                V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.2
              (fun iterator => iterator.slice)
              (fun enumerated => enumerated.iter)
              polynomialIterator
              (fun e => e) originWeights originClaim bytes additive round alpha none =
                polynomialResult at bodyRun
          cases polynomialResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
          | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
          | ok polynomialOutput =>
              rcases polynomialOutput with
                ⟨polynomialWeights, polynomialClaim, polynomialAdditive,
                  polynomialPending, polynomialStatus⟩
              simp only [bind_tc_ok] at bodyRun
              have safe := polynomial_loop_safe_round_return
                (additiveInst := additiveInst)
                (toSliceBack := (Array.repeat 7#usize
                  V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.2)
                (iterBack := fun iterator => iterator.slice)
                (enumerateBack := fun enumerated => enumerated.iter)
                (iter := polynomialIterator)
                (back := fun e => e)
                (weights := originWeights) (nextWeights := polynomialWeights)
                (claim := originClaim) (nextClaim := polynomialClaim)
                (alpha := alpha) (bytes := bytes)
                (additive := additive) (nextAdditive := polynomialAdditive)
                (round := round) (pending := polynomialPending)
                (status := polynomialStatus) polynomialEquation
              rcases safe with success | failure
              · rcases success with ⟨pendingExact, statusExact⟩
                rw [pendingExact, statusExact] at bodyRun
                injection bodyRun with tupleEq
                injection tupleEq with outputEq
                have pendingEq := congrArg
                  (fun output => output.2.2.2.1) outputEq
                have statusEq := congrArg
                  (fun output => output.2.2.2.2) outputEq
                left
                exact ⟨pendingEq.symm, statusEq.symm⟩
              · rcases failure with ⟨error, pendingExact, statusExact⟩
                rw [pendingExact, statusExact] at bodyRun
                injection bodyRun with tupleEq
                injection tupleEq with outputEq
                have pendingEq := congrArg
                  (fun output => output.2.2.2.1) outputEq
                have statusEq := congrArg
                  (fun output => output.2.2.2.2) outputEq
                right
                exact ⟨error, pendingEq.symm, statusEq.symm⟩
      | some sample =>
          simp only [Aeneas.Std.lift, bind_tc_ok] at bodyRun
          generalize oodOffsetEquation :
            V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_OFFSET =
              oodOffsetResult at bodyRun
          cases oodOffsetResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
          | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
          | ok oodOffset =>
              simp only [bind_tc_ok] at bodyRun
              generalize oodDecodeEquation :
                V5RelationFullGenerated.relation_stress.decode_indexed bytes
                  oodOffset
                  (Std.Usize.wrapping_add
                    (Std.Usize.wrapping_mul round
                      V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES)
                    sample) = oodDecodeResult at bodyRun
              cases oodDecodeResult with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
              | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
              | ok oodDecoded =>
                  simp only [bind_tc_ok] at bodyRun
                  cases oodDecoded with
                  | Err oodError =>
                      simp only [
                        core.result.Result.Insts.CoreOpsTry.branch,
                        bind_tc_ok,
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                        core.convert.FromSame.from] at bodyRun
                      injection bodyRun with tupleEq
                      injection tupleEq with outputEq
                      exact safeRoundReturn_of_error_output_eq
                        originWeights originClaim additive oodError
                        nextWeights nextClaim nextAdditive pending status outputEq
                  | Ok oodValue =>
                      simp only [
                        core.result.Result.Insts.CoreOpsTry.branch,
                        bind_tc_ok] at bodyRun
                      generalize mixOffsetEquation :
                        V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_MIX_OFFSET =
                          mixOffsetResult at bodyRun
                      cases mixOffsetResult with
                      | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                      | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                      | ok mixOffset =>
                          simp only [bind_tc_ok] at bodyRun
                          generalize mixDecodeEquation :
                            V5RelationFullGenerated.relation_stress.decode_indexed bytes
                              mixOffset
                              (Std.Usize.wrapping_add
                                (Std.Usize.wrapping_mul round
                                  V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES)
                                sample) = mixDecodeResult at bodyRun
                          cases mixDecodeResult with
                          | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                          | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                          | ok mixDecoded =>
                              simp only [bind_tc_ok] at bodyRun
                              cases mixDecoded with
                              | Err mixError =>
                                  simp only [
                                    core.result.Result.Insts.CoreOpsTry.branch,
                                    bind_tc_ok,
                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                    core.convert.FromSame.from] at bodyRun
                                  injection bodyRun with tupleEq
                                  injection tupleEq with outputEq
                                  exact safeRoundReturn_of_error_output_eq
                                    originWeights originClaim additive mixError
                                    nextWeights nextClaim nextAdditive pending status outputEq
                              | Ok mixValue =>
                                  simp only [
                                    core.result.Result.Insts.CoreOpsTry.branch,
                                    bind_tc_ok] at bodyRun
                                  by_cases roundZero : round = 0#usize
                                  · rw [roundZero] at bodyRun
                                    simp only [if_true] at bodyRun
                                    generalize pointEquation :
                                      Array.index_usize circlePoints sample =
                                        pointResult at bodyRun
                                    cases pointResult with
                                    | fail error =>
                                        simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                                    | div =>
                                        simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                                    | ok point =>
                                        simp only [bind_tc_ok] at bodyRun
                                        generalize tensorEquation :
                                          V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_circle_tensor
                                            originWeights mixValue point = tensorResult
                                          at bodyRun
                                        cases tensorResult with
                                        | fail error =>
                                            simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                                        | div =>
                                            simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                                        | ok tensorOutput =>
                                            rcases tensorOutput with
                                              ⟨tensorResult, tensorWeights⟩
                                            simp only [bind_tc_ok] at bodyRun
                                            cases tensorResult with
                                            | Err tensorError =>
                                                simp only [
                                                  core.result.Result.Insts.CoreOpsTry.branch,
                                                  bind_tc_ok,
                                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                                  V5RelationFullGenerated.relation_stress.V5RelationStressError.Insts.CoreConvertFromTensorWeightError.from]
                                                  at bodyRun
                                                injection bodyRun with tupleEq
                                                injection tupleEq with outputEq
                                                exact safeRoundReturn_of_error_output_eq
                                                  tensorWeights originClaim additive
                                                  (.WeightShape tensorError)
                                                  nextWeights nextClaim nextAdditive
                                                  pending status outputEq
                                            | Ok unitValue =>
                                                simp only [
                                                  core.result.Result.Insts.CoreOpsTry.branch,
                                                  bind_tc_ok] at bodyRun
                                                generalize productEquation :
                                                  V5RelationFullGenerated.aspis_core.field.QM31.mul
                                                    mixValue oodValue = productResult
                                                  at bodyRun
                                                cases productResult with
                                                | fail error =>
                                                    simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                                                | div =>
                                                    simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                                                | ok product =>
                                                    simp only [bind_tc_ok] at bodyRun
                                                    generalize claimEquation :
                                                      V5RelationFullGenerated.aspis_core.field.QM31.add
                                                        originClaim product = claimResult
                                                      at bodyRun
                                                    cases claimResult with
                                                    | fail error =>
                                                        simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                                                    | div =>
                                                        simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                                                    | ok updatedClaim =>
                                                        simp only [bind_tc_ok] at bodyRun
                                                        simp at bodyRun
                                  · simp only [roundZero, if_false] at bodyRun
                                    generalize lineOffsetEquation :
                                      V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_LINE_OFFSET =
                                        lineOffsetResult at bodyRun
                                    cases lineOffsetResult with
                                    | fail error =>
                                        simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                                    | div =>
                                        simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                                    | ok lineOffset =>
                                        simp only [bind_tc_ok] at bodyRun
                                        generalize lineDecodeEquation :
                                          V5RelationFullGenerated.relation_stress.decode_indexed
                                            bytes lineOffset
                                            (Std.Usize.wrapping_add
                                              (Std.Usize.wrapping_mul
                                                (Std.Usize.wrapping_sub round 1#usize)
                                                V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES)
                                              sample) = lineDecodeResult
                                          at bodyRun
                                        cases lineDecodeResult with
                                        | fail error =>
                                            simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                                        | div =>
                                            simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                                        | ok lineDecoded =>
                                            simp only [bind_tc_ok] at bodyRun
                                            cases lineDecoded with
                                            | Err lineError =>
                                                simp only [
                                                  core.result.Result.Insts.CoreOpsTry.branch,
                                                  bind_tc_ok,
                                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                                  core.convert.FromSame.from] at bodyRun
                                                injection bodyRun with tupleEq
                                                injection tupleEq with outputEq
                                                exact safeRoundReturn_of_error_output_eq
                                                  originWeights originClaim additive lineError
                                                  nextWeights nextClaim nextAdditive
                                                  pending status outputEq
                                            | Ok lineValue =>
                                                simp only [
                                                  core.result.Result.Insts.CoreOpsTry.branch,
                                                  bind_tc_ok] at bodyRun
                                                generalize tensorEquation :
                                                  V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_line_tensor
                                                    originWeights mixValue lineValue =
                                                      tensorResult at bodyRun
                                                cases tensorResult with
                                                | fail error =>
                                                    simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                                                | div =>
                                                    simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                                                | ok tensorOutput =>
                                                    rcases tensorOutput with
                                                      ⟨tensorResult, tensorWeights⟩
                                                    simp only [bind_tc_ok] at bodyRun
                                                    cases tensorResult with
                                                    | Err tensorError =>
                                                        simp only [
                                                          core.result.Result.Insts.CoreOpsTry.branch,
                                                          bind_tc_ok,
                                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                                          V5RelationFullGenerated.relation_stress.V5RelationStressError.Insts.CoreConvertFromTensorWeightError.from]
                                                          at bodyRun
                                                        injection bodyRun with tupleEq
                                                        injection tupleEq with outputEq
                                                        exact safeRoundReturn_of_error_output_eq
                                                          tensorWeights originClaim additive
                                                          (.WeightShape tensorError)
                                                          nextWeights nextClaim nextAdditive
                                                          pending status outputEq
                                                    | Ok unitValue =>
                                                        simp only [
                                                          core.result.Result.Insts.CoreOpsTry.branch,
                                                          bind_tc_ok] at bodyRun
                                                        generalize productEquation :
                                                          V5RelationFullGenerated.aspis_core.field.QM31.mul
                                                            mixValue oodValue = productResult
                                                          at bodyRun
                                                        cases productResult with
                                                        | fail error =>
                                                            simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                                                        | div =>
                                                            simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                                                        | ok product =>
                                                            simp only [bind_tc_ok] at bodyRun
                                                            generalize claimEquation :
                                                              V5RelationFullGenerated.aspis_core.field.QM31.add
                                                                originClaim product = claimResult
                                                              at bodyRun
                                                            cases claimResult with
                                                            | fail error =>
                                                                simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                                                            | div =>
                                                                simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                                                            | ok updatedClaim =>
                                                                simp only [bind_tc_ok] at bodyRun
                                                                simp at bodyRun

theorem accepted_outer_loop_first_round_is_cont
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (alphas : Array V5RelationFullGenerated.aspis_core.field.QM31 4#usize)
    (bytes : Array Std.U8 928#usize)
    (circlePoints : Array
      V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize)
    (weights0 :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (claim0 : V5RelationFullGenerated.aspis_core.field.QM31)
    (additive0 : A)
    (output : Verified)
    (run :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0
        additiveInst
        (AspisV5RelationFullSourceProof.alphaIteratorAt alphas 0 0#usize)
        weights0 claim0 bytes additive0 circlePoints none =
          .ok (some (.Ok output))) :
    ∃ weights1 claim1 additive1,
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0.body
          additiveInst bytes circlePoints
          (AspisV5RelationFullSourceProof.alphaIteratorAt alphas 0 0#usize)
          weights0 claim0 additive0 none =
        .ok (.cont
          (AspisV5RelationFullSourceProof.alphaIteratorAt alphas 1 1#usize,
            weights1, claim1, additive1, none)) := by
  have alphaLength : alphas.val.length = 4 := by
    simpa using alphas.property
  let alpha0 := alphas.val[0]
  have alpha0Exact : alphas.val[0] = alpha0 := rfl
  have count0Next : 0#usize + 1#usize = ok 1#usize := by
    apply usizeAddExactLocal <;> scalar_tac
  have next0 :=
    AspisV5RelationFullSourceProof.alpha_iterator_next_some_exact
      alphas 0 0#usize 1#usize alpha0 (by omega) alpha0Exact count0Next
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0
    at run
  rw [Aeneas.Std.loop.eq_def] at run
  simp only at run
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0.body
    at run
  rw [next0] at run
  simp only [bind_tc_ok] at run
  let initialRange : core.ops.range.Range Std.Usize :=
    { start := 0#usize
      «end» :=
        V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES }
  generalize innerEquation :
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0
      additiveInst
      initialRange
      weights0 claim0 bytes additive0 circlePoints 0#usize alpha0 none =
        innerResult at run
  cases innerResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok innerOutput =>
      rcases innerOutput with
        ⟨weights1, claim1, additive1, pending1, status1⟩
      simp only [bind_tc_ok] at run
      have safe := two_sample_loop_safe_round_return
        (additiveInst := additiveInst)
        (range := initialRange)
        (weights := weights0) (nextWeights := weights1)
        (claim := claim0) (nextClaim := claim1) (alpha := alpha0)
        (bytes := bytes) (additive := additive0) (nextAdditive := additive1)
        (circlePoints := circlePoints) (round := 0#usize)
        (pending := pending1) (status := status1) innerEquation
      rcases safe with success | failure
      · rcases success with ⟨pendingExact, statusExact⟩
        subst pending1
        subst status1
        have roundEquation :
            V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0
              additiveInst (AspisV5RelationFullSourceProof.range2At 0#usize)
              weights0 claim0 bytes additive0 circlePoints 0#usize alpha0 none =
                .ok (weights1, claim1, additive1, none, 1#u32) := by
          simpa [initialRange, AspisV5RelationFullSourceProof.range2At,
            V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES]
            using innerEquation
        refine ⟨weights1, claim1, additive1, ?_⟩
        apply AspisV5RelationFullSourceProof.generated_active_round_body_exact
          (iter := AspisV5RelationFullSourceProof.alphaIteratorAt alphas 0 0#usize)
          (nextIter := AspisV5RelationFullSourceProof.alphaIteratorAt alphas 1 1#usize)
          (round := 0#usize) (alpha := alpha0)
          (weights := weights0) (nextWeights := weights1)
          (runningClaim := claim0) (nextClaim := claim1)
          (additive := additive0) (nextAdditive := additive1)
          (pending := none)
        · exact next0
        · exact roundEquation
      · rcases failure with ⟨error, pendingExact, statusExact⟩
        rw [pendingExact, statusExact] at run
        change (.ok (some (.Err error)) : Aeneas.Std.Result
          (Option (core.result.Result Verified VError))) =
            .ok (some (.Ok output)) at run
        simp at run

theorem accepted_outer_loop_active_body_is_cont
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (bytes : Array Std.U8 928#usize)
    (circlePoints : Array
      V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize)
    (iter nextIter : core.iter.adapters.enumerate.Enumerate
      (core.array.iter.IntoIter
        V5RelationFullGenerated.aspis_core.field.QM31 4#usize))
    (round : Std.Usize)
    (alpha : V5RelationFullGenerated.aspis_core.field.QM31)
    (weights0 :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (claim0 : V5RelationFullGenerated.aspis_core.field.QM31)
    (additive0 : A)
    (output : Verified)
    (nextExact :
      core.iter.adapters.enumerate.IteratorEnumerate.next
        (V5RelationFullGenerated.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
          V5RelationFullGenerated.aspis_core.field.QM31 4#usize) iter =
        .ok (some (round, alpha), nextIter))
    (run :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0
        additiveInst iter weights0 claim0 bytes additive0 circlePoints none =
          .ok (some (.Ok output))) :
    ∃ weights1 claim1 additive1,
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0.body
          additiveInst bytes circlePoints iter weights0 claim0 additive0 none =
        .ok (.cont (nextIter, weights1, claim1, additive1, none)) := by
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0
    at run
  rw [Aeneas.Std.loop.eq_def] at run
  simp only at run
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0.body
    at run
  rw [nextExact] at run
  simp only [bind_tc_ok] at run
  let initialRange : core.ops.range.Range Std.Usize :=
    { start := 0#usize
      «end» :=
        V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES }
  generalize innerEquation :
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0
      additiveInst initialRange weights0 claim0 bytes additive0 circlePoints
        round alpha none = innerResult at run
  cases innerResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok innerOutput =>
      rcases innerOutput with
        ⟨weights1, claim1, additive1, pending1, status1⟩
      simp only [bind_tc_ok] at run
      have safe := two_sample_loop_safe_round_return
        (additiveInst := additiveInst) (range := initialRange)
        (weights := weights0) (nextWeights := weights1)
        (claim := claim0) (nextClaim := claim1) (alpha := alpha)
        (bytes := bytes) (additive := additive0) (nextAdditive := additive1)
        (circlePoints := circlePoints) (round := round)
        (pending := pending1) (status := status1) innerEquation
      rcases safe with success | failure
      · rcases success with ⟨pendingExact, statusExact⟩
        subst pending1
        subst status1
        have roundEquation :
            V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0
              additiveInst (AspisV5RelationFullSourceProof.range2At 0#usize)
              weights0 claim0 bytes additive0 circlePoints round alpha none =
                .ok (weights1, claim1, additive1, none, 1#u32) := by
          simpa [initialRange, AspisV5RelationFullSourceProof.range2At,
            V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES]
            using innerEquation
        refine ⟨weights1, claim1, additive1, ?_⟩
        apply AspisV5RelationFullSourceProof.generated_active_round_body_exact
          (iter := iter) (nextIter := nextIter)
          (round := round) (alpha := alpha)
          (weights := weights0) (nextWeights := weights1)
          (runningClaim := claim0) (nextClaim := claim1)
          (additive := additive0) (nextAdditive := additive1)
          (pending := none)
        · exact nextExact
        · exact roundEquation
      · rcases failure with ⟨error, pendingExact, statusExact⟩
        rw [pendingExact, statusExact] at run
        change (.ok (some (.Err error)) : Aeneas.Std.Result
          (Option (core.result.Result Verified VError))) =
            .ok (some (.Ok output)) at run
        simp at run

theorem accepted_outer_loop_tail_after_cont
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (bytes : Array Std.U8 928#usize)
    (circlePoints : Array
      V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize)
    (iter nextIter : core.iter.adapters.enumerate.Enumerate
      (core.array.iter.IntoIter
        V5RelationFullGenerated.aspis_core.field.QM31 4#usize))
    (weights0 weights1 :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (claim0 claim1 : V5RelationFullGenerated.aspis_core.field.QM31)
    (additive0 additive1 : A)
    (output : Verified)
    (bodyExact :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0.body
          additiveInst bytes circlePoints iter weights0 claim0 additive0 none =
        .ok (.cont (nextIter, weights1, claim1, additive1, none)))
    (run :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0
        additiveInst iter weights0 claim0 bytes additive0 circlePoints none =
          .ok (some (.Ok output))) :
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0
      additiveInst nextIter weights1 claim1 bytes additive1 circlePoints none =
        .ok (some (.Ok output)) := by
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0
    at run ⊢
  rw [Aeneas.Std.loop.eq_def] at run
  simp only at run
  rw [bodyExact] at run
  simpa using run

theorem accepted_outer_loop_yields_four_ordered_rounds
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (alphas : Array V5RelationFullGenerated.aspis_core.field.QM31 4#usize)
    (bytes : Array Std.U8 928#usize)
    (circlePoints : Array
      V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize)
    (weights0 :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (claim0 : V5RelationFullGenerated.aspis_core.field.QM31)
    (additive0 : A)
    (output : Verified)
    (run :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0
        additiveInst
        (AspisV5RelationFullSourceProof.alphaIteratorAt alphas 0 0#usize)
        weights0 claim0 bytes additive0 circlePoints none =
          .ok (some (.Ok output))) :
    ∃ weights1 claim1 additive1 weights2 claim2 additive2
        weights3 claim3 additive3 weights4 claim4 additive4,
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0.body
          additiveInst bytes circlePoints
          (AspisV5RelationFullSourceProof.alphaIteratorAt alphas 0 0#usize)
          weights0 claim0 additive0 none =
        .ok (.cont
          (AspisV5RelationFullSourceProof.alphaIteratorAt alphas 1 1#usize,
            weights1, claim1, additive1, none)) ∧
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0.body
          additiveInst bytes circlePoints
          (AspisV5RelationFullSourceProof.alphaIteratorAt alphas 1 1#usize)
          weights1 claim1 additive1 none =
        .ok (.cont
          (AspisV5RelationFullSourceProof.alphaIteratorAt alphas 2 2#usize,
            weights2, claim2, additive2, none)) ∧
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0.body
          additiveInst bytes circlePoints
          (AspisV5RelationFullSourceProof.alphaIteratorAt alphas 2 2#usize)
          weights2 claim2 additive2 none =
        .ok (.cont
          (AspisV5RelationFullSourceProof.alphaIteratorAt alphas 3 3#usize,
            weights3, claim3, additive3, none)) ∧
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0.body
          additiveInst bytes circlePoints
          (AspisV5RelationFullSourceProof.alphaIteratorAt alphas 3 3#usize)
          weights3 claim3 additive3 none =
        .ok (.cont
          (AspisV5RelationFullSourceProof.alphaIteratorAt alphas 4 4#usize,
            weights4, claim4, additive4, none)) ∧
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0
          additiveInst
          (AspisV5RelationFullSourceProof.alphaIteratorAt alphas 4 4#usize)
          weights4 claim4 bytes additive4 circlePoints none =
        .ok (some (.Ok output)) := by
  have alphaLength : alphas.val.length = 4 := by
    simpa using alphas.property
  let alpha0 := alphas.val[0]
  let alpha1 := alphas.val[1]
  let alpha2 := alphas.val[2]
  let alpha3 := alphas.val[3]
  have count0Next : 0#usize + 1#usize = ok 1#usize := by
    apply usizeAddExactLocal <;> scalar_tac
  have count1Next : 1#usize + 1#usize = ok 2#usize := by
    apply usizeAddExactLocal <;> scalar_tac
  have count2Next : 2#usize + 1#usize = ok 3#usize := by
    apply usizeAddExactLocal <;> scalar_tac
  have count3Next : 3#usize + 1#usize = ok 4#usize := by
    apply usizeAddExactLocal <;> scalar_tac
  have next0 :
      core.iter.adapters.enumerate.IteratorEnumerate.next
        (V5RelationFullGenerated.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
          V5RelationFullGenerated.aspis_core.field.QM31 4#usize)
        (AspisV5RelationFullSourceProof.alphaIteratorAt alphas 0 0#usize) =
      .ok (some (0#usize, alpha0),
        AspisV5RelationFullSourceProof.alphaIteratorAt alphas 1 1#usize) := by
    simpa using AspisV5RelationFullSourceProof.alpha_iterator_next_some_exact
      alphas 0 0#usize 1#usize alpha0 (by omega) rfl count0Next
  have next1 :
      core.iter.adapters.enumerate.IteratorEnumerate.next
        (V5RelationFullGenerated.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
          V5RelationFullGenerated.aspis_core.field.QM31 4#usize)
        (AspisV5RelationFullSourceProof.alphaIteratorAt alphas 1 1#usize) =
      .ok (some (1#usize, alpha1),
        AspisV5RelationFullSourceProof.alphaIteratorAt alphas 2 2#usize) := by
    simpa using AspisV5RelationFullSourceProof.alpha_iterator_next_some_exact
      alphas 1 1#usize 2#usize alpha1 (by omega) rfl count1Next
  have next2 :
      core.iter.adapters.enumerate.IteratorEnumerate.next
        (V5RelationFullGenerated.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
          V5RelationFullGenerated.aspis_core.field.QM31 4#usize)
        (AspisV5RelationFullSourceProof.alphaIteratorAt alphas 2 2#usize) =
      .ok (some (2#usize, alpha2),
        AspisV5RelationFullSourceProof.alphaIteratorAt alphas 3 3#usize) := by
    simpa using AspisV5RelationFullSourceProof.alpha_iterator_next_some_exact
      alphas 2 2#usize 3#usize alpha2 (by omega) rfl count2Next
  have next3 :
      core.iter.adapters.enumerate.IteratorEnumerate.next
        (V5RelationFullGenerated.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
          V5RelationFullGenerated.aspis_core.field.QM31 4#usize)
        (AspisV5RelationFullSourceProof.alphaIteratorAt alphas 3 3#usize) =
      .ok (some (3#usize, alpha3),
        AspisV5RelationFullSourceProof.alphaIteratorAt alphas 4 4#usize) := by
    simpa using AspisV5RelationFullSourceProof.alpha_iterator_next_some_exact
      alphas 3 3#usize 4#usize alpha3 (by omega) rfl count3Next
  obtain ⟨weights1, claim1, additive1, round0⟩ :=
    accepted_outer_loop_active_body_is_cont additiveInst bytes circlePoints
      _ _ 0#usize alpha0 weights0 claim0 additive0 output next0 run
  have run1 := accepted_outer_loop_tail_after_cont additiveInst bytes circlePoints
    _ _ weights0 weights1 claim0 claim1 additive0 additive1 output round0 run
  obtain ⟨weights2, claim2, additive2, round1⟩ :=
    accepted_outer_loop_active_body_is_cont additiveInst bytes circlePoints
      _ _ 1#usize alpha1 weights1 claim1 additive1 output next1 run1
  have run2 := accepted_outer_loop_tail_after_cont additiveInst bytes circlePoints
    _ _ weights1 weights2 claim1 claim2 additive1 additive2 output round1 run1
  obtain ⟨weights3, claim3, additive3, round2⟩ :=
    accepted_outer_loop_active_body_is_cont additiveInst bytes circlePoints
      _ _ 2#usize alpha2 weights2 claim2 additive2 output next2 run2
  have run3 := accepted_outer_loop_tail_after_cont additiveInst bytes circlePoints
    _ _ weights2 weights3 claim2 claim3 additive2 additive3 output round2 run2
  obtain ⟨weights4, claim4, additive4, round3⟩ :=
    accepted_outer_loop_active_body_is_cont additiveInst bytes circlePoints
      _ _ 3#usize alpha3 weights3 claim3 additive3 output next3 run3
  have run4 := accepted_outer_loop_tail_after_cont additiveInst bytes circlePoints
    _ _ weights3 weights4 claim3 claim4 additive3 additive4 output round3 run3
  exact ⟨weights1, claim1, additive1, weights2, claim2, additive2,
    weights3, claim3, additive3, weights4, claim4, additive4,
    round0, round1, round2, round3, run4⟩

/-- An accepted tail after the four released rounds must execute the real
terminal decoder and both production dot calls.  In particular, the two dot
results add to the running claim; an error, a decoded Rust `Err`, or a
terminal mismatch cannot produce the accepted result. -/
theorem accepted_outer_loop_terminal_calls_are_exact
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (alphas : Array V5RelationFullGenerated.aspis_core.field.QM31 4#usize)
    (bytes : Array Std.U8 928#usize)
    (circlePoints : Array
      V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize)
    (weights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (runningClaim : V5RelationFullGenerated.aspis_core.field.QM31)
    (additive : A)
    (output : Verified)
    (run :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0
          additiveInst
          (AspisV5RelationFullSourceProof.alphaIteratorAt alphas 4 4#usize)
          weights runningClaim bytes additive circlePoints none =
        .ok (some (.Ok output))) :
    ∃ finalCoefficients mainDot additiveDot,
      V5RelationFullGenerated.relation_stress.decode_v5_relation_stress_final
          bytes = .ok (.Ok finalCoefficients) ∧
      aspis_core.sumcheck.WeightAccumulator.dot
          weights (Array.to_slice finalCoefficients) = .ok mainDot ∧
      additiveInst.dot additive finalCoefficients = .ok additiveDot ∧
      V5RelationFullGenerated.aspis_core.field.QM31.add mainDot additiveDot =
        .ok runningClaim ∧
      output =
        { final_coefficients := finalCoefficients
          terminal_claim := runningClaim } := by
  have alphaLength : alphas.val.length = 4 := by
    simpa using alphas.property
  have next4 :=
    AspisV5RelationFullSourceProof.alpha_iterator_next_none_exact
      alphas 4 4#usize (by omega)
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0
    at run
  rw [Aeneas.Std.loop.eq_def] at run
  simp only at run
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0.body
    at run
  rw [next4] at run
  simp only [bind_tc_ok] at run
  generalize decoderEquation :
    V5RelationFullGenerated.relation_stress.decode_v5_relation_stress_final
      bytes = decoderResult at run
  cases decoderResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok decoded =>
      simp only [bind_tc_ok] at run
      cases decoded with
      | Err decodeError =>
          simp only [
            core.result.Result.Insts.CoreOpsTry.branch,
            bind_tc_ok,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at run
          simp at run
      | Ok finalCoefficients =>
          simp only [
            core.result.Result.Insts.CoreOpsTry.branch,
            Aeneas.Std.lift,
            bind_tc_ok] at run
          generalize mainDotEquation :
            aspis_core.sumcheck.WeightAccumulator.dot
              weights (Array.to_slice finalCoefficients) = mainDotResult at run
          cases mainDotResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
          | div => simp [Bind.bind, Aeneas.Std.bind] at run
          | ok mainDot =>
              simp only [bind_tc_ok] at run
              generalize additiveDotEquation :
                additiveInst.dot additive finalCoefficients =
                  additiveDotResult at run
              cases additiveDotResult with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
              | div => simp [Bind.bind, Aeneas.Std.bind] at run
              | ok additiveDot =>
                  simp only [bind_tc_ok] at run
                  generalize combinedEquation :
                    V5RelationFullGenerated.aspis_core.field.QM31.add
                      mainDot additiveDot = combinedResult at run
                  cases combinedResult with
                  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
                  | div => simp [Bind.bind, Aeneas.Std.bind] at run
                  | ok combined =>
                      simp only [bind_tc_ok] at run
                      generalize mismatchEquation :
                        core.cmp.PartialEq.ne.trait_default
                          V5RelationFullGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                          combined runningClaim = mismatchResult at run
                      cases mismatchResult with
                      | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
                      | div => simp [Bind.bind, Aeneas.Std.bind] at run
                      | ok mismatch =>
                          cases mismatch with
                          | true => simp at run
                          | false =>
                              change
                                (.ok (some (.Ok
                                  { final_coefficients := finalCoefficients
                                    terminal_claim := runningClaim })) :
                                  Aeneas.Std.Result
                                    (Option (core.result.Result Verified VError))) =
                                  .ok (some (.Ok output)) at run
                              injection run with resultEquation
                              injection resultEquation with outputEquation
                              have combinedExact : combined = runningClaim := by
                                by_contra different
                                have specification :=
                                  AspisV5RelationFullSourceProof.raw_qm31_ne_spec
                                    combined runningClaim
                                rw [mismatchEquation] at specification
                                simp [different] at specification
                              have outputExact : output =
                                  { final_coefficients := finalCoefficients
                                    terminal_claim := runningClaim } := by
                                injection outputEquation.symm
                              subst combined
                              exact ⟨finalCoefficients, mainDot, additiveDot,
                                rfl, mainDotEquation,
                                additiveDotEquation, combinedEquation,
                                outputExact⟩

#print axioms loop_ok_has_done_origin
#print axioms accepted_outer_loop_yields_four_ordered_rounds
#print axioms accepted_outer_loop_terminal_calls_are_exact

end AspisV5RelationFullSuccessInversion
