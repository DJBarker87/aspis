import V5RelationFullSuccessInversion

namespace AspisV5RelationTopLevelSuccessInversion

open Aeneas Aeneas.Std Result ControlFlow Error
open V5RelationFullGenerated
open AspisV5RelationFullSuccessInversion

abbrev Verified :=
  V5RelationFullGenerated.relation_stress.VerifiedV5RelationStress

abbrev VError :=
  V5RelationFullGenerated.relation_stress.V5RelationStressError

theorem accepted_complete_relation_enters_circle_loop
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (weights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (runningClaim : V5RelationFullGenerated.aspis_core.field.QM31)
    (alphas : Array V5RelationFullGenerated.aspis_core.field.QM31 4#usize)
    (bytes : Array Std.U8 928#usize)
    (additive : A)
    (output : Verified)
    (run :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive
        additiveInst weights runningClaim alphas bytes additive =
          .ok (.Ok output)) :
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0
        additiveInst
        (Array.repeat 2#usize
          ({ x := V5RelationFullGenerated.aspis_core.field.QM31.ZERO
             y := V5RelationFullGenerated.aspis_core.field.QM31.ZERO } :
            V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint)).to_slice_mut.2
        (fun iterator => iterator.slice)
        (fun enumerated => enumerated.iter)
        { iter :=
            { slice := (Array.repeat 2#usize
                ({ x := V5RelationFullGenerated.aspis_core.field.QM31.ZERO
                   y := V5RelationFullGenerated.aspis_core.field.QM31.ZERO } :
                  V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint)).to_slice_mut.1 }
          count := 0#usize }
        (fun e => e) weights runningClaim alphas bytes additive =
      .ok (some (.Ok output)) := by
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive
    at run
  simp only [Aeneas.Std.lift, bind_tc_ok,
    core.slice.Slice.iter_mut, V5MutableEnumerateSupport.enumerate] at run
  generalize outerEquation :
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0
        additiveInst
        (Array.repeat 2#usize
          ({ x := V5RelationFullGenerated.aspis_core.field.QM31.ZERO
             y := V5RelationFullGenerated.aspis_core.field.QM31.ZERO } :
            V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint)).to_slice_mut.2
        (fun iterator => iterator.slice)
        (fun enumerated => enumerated.iter)
        { iter :=
            { slice := (Array.repeat 2#usize
                ({ x := V5RelationFullGenerated.aspis_core.field.QM31.ZERO
                   y := V5RelationFullGenerated.aspis_core.field.QM31.ZERO } :
                  V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint)).to_slice_mut.1 }
          count := 0#usize }
        (fun e => e) weights runningClaim alphas bytes additive = outerResult
      at run
  cases outerResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok pending =>
      simp only [bind_tc_ok] at run
      cases pending with
      | none => simp at run
      | some result =>
          cases result with
          | Err error => simp at run
          | Ok accepted =>
              injection run with outputExact
              injection outputExact with acceptedExact
              subst accepted
              rfl

theorem accepted_circle_loop_exposes_relation_loop
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (toSliceBack : Slice
      V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint →
      Array V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize)
    (iterBack : core.slice.iter.IterMut
      V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint →
      Slice V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint)
    (enumerateBack : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.IterMut
        V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint) →
      core.slice.iter.IterMut
        V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint)
    (iter : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.IterMut
        V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint))
    (back : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.IterMut
        V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint) →
      core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.IterMut
          V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint))
    (weights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (runningClaim : V5RelationFullGenerated.aspis_core.field.QM31)
    (alphas : Array V5RelationFullGenerated.aspis_core.field.QM31 4#usize)
    (bytes : Array Std.U8 928#usize)
    (additive : A)
    (output : Verified)
    (run :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0
        additiveInst toSliceBack iterBack enumerateBack iter back weights
          runningClaim alphas bytes additive = .ok (some (.Ok output))) :
    ∃ circlePoints,
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0
          additiveInst
          (AspisV5RelationFullSourceProof.alphaIteratorAt alphas 0 0#usize)
          weights runningClaim bytes additive circlePoints none =
        .ok (some (.Ok output)) := by
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0
    at run
  have origin := loop_ok_has_done_origin_eq
    (fun state =>
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0.body
        additiveInst toSliceBack iterBack enumerateBack weights runningClaim
          alphas bytes additive state.1 state.2)
    (iter, back) (some (.Ok output)) run
  rcases origin with ⟨⟨originIter, originBack⟩, bodyRun⟩
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0.body
    at bodyRun
  generalize nextEquation :
    V5MutableEnumerateSupport.next originIter = nextResult at bodyRun
  cases nextResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
  | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
  | ok next =>
      rcases next with ⟨option, nextIter, nextBack⟩
      simp only [bind_tc_ok] at bodyRun
      cases option with
      | none =>
          simp only [
            Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
            core.iter.traits.iterator.Iterator.enumerate.trait_default,
            core.iter.traits.iterator.Iterator.enumerate.default,
            bind_tc_ok] at bodyRun
          let circlePoints :=
            toSliceBack (iterBack (enumerateBack
              (originBack (nextBack nextIter none))))
          generalize relationEquation :
            V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0
              additiveInst
              ({ iter := { array := alphas }, count := 0#usize } :
                core.iter.adapters.enumerate.Enumerate
                  (core.array.iter.IntoIter
                    V5RelationFullGenerated.aspis_core.field.QM31 4#usize))
              weights runningClaim bytes additive circlePoints none =
                relationResult at bodyRun
          cases relationResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
          | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
          | ok pending =>
              simp only [bind_tc_ok] at bodyRun
              cases pending with
              | none => simp at bodyRun
              | some result =>
                  cases result with
                  | Err error => simp at bodyRun
                  | Ok accepted =>
                      injection bodyRun with wrappedExact
                      injection wrappedExact with acceptedExact
                      injection acceptedExact with valueExact
                      injection valueExact with acceptedValueExact
                      subst accepted
                      refine ⟨circlePoints, ?_⟩
                      simpa [AspisV5RelationFullSourceProof.alphaIteratorAt]
                        using relationEquation
      | some item =>
          rcases item with ⟨sample, oldPoint⟩
          simp only [Aeneas.Std.lift, bind_tc_ok] at bodyRun
          generalize xEquation :
            V5RelationFullGenerated.relation_stress.decode_indexed bytes
              V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_CIRCLE_OFFSET
              (Std.Usize.wrapping_mul 2#usize sample) = xResult at bodyRun
          cases xResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
          | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
          | ok decodedX =>
              simp only [bind_tc_ok] at bodyRun
              cases decodedX with
              | Err error =>
                  simp only [
                    core.result.Result.Insts.CoreOpsTry.branch,
                    bind_tc_ok,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame.from] at bodyRun
                  simp at bodyRun
              | Ok x =>
                  simp only [
                    core.result.Result.Insts.CoreOpsTry.branch,
                    Aeneas.Std.lift,
                    bind_tc_ok] at bodyRun
                  generalize yEquation :
                    V5RelationFullGenerated.relation_stress.decode_indexed bytes
                      V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_CIRCLE_OFFSET
                      (Std.Usize.wrapping_add
                        (Std.Usize.wrapping_mul 2#usize sample) 1#usize) =
                          yResult at bodyRun
                  cases yResult with
                  | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                  | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                  | ok decodedY =>
                      simp only [bind_tc_ok] at bodyRun
                      cases decodedY with
                      | Err error =>
                          simp only [
                            core.result.Result.Insts.CoreOpsTry.branch,
                            bind_tc_ok,
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                            core.convert.FromSame.from] at bodyRun
                          simp at bodyRun
                      | Ok y =>
                          simp only [
                            core.result.Result.Insts.CoreOpsTry.branch,
                            bind_tc_ok] at bodyRun
                          generalize xSquareEquation :
                            V5RelationFullGenerated.aspis_core.field.QM31.square x =
                              xSquareResult at bodyRun
                          cases xSquareResult with
                          | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                          | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                          | ok xSquare =>
                              simp only [bind_tc_ok] at bodyRun
                              generalize ySquareEquation :
                                V5RelationFullGenerated.aspis_core.field.QM31.square y =
                                  ySquareResult at bodyRun
                              cases ySquareResult with
                              | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                              | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                              | ok ySquare =>
                                  simp only [bind_tc_ok] at bodyRun
                                  generalize sumEquation :
                                    V5RelationFullGenerated.aspis_core.field.QM31.add
                                      xSquare ySquare = sumResult at bodyRun
                                  cases sumResult with
                                  | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                                  | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                                  | ok sum =>
                                      simp only [bind_tc_ok] at bodyRun
                                      generalize mismatchEquation :
                                        core.cmp.PartialEq.ne.trait_default
                                          V5RelationFullGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                                          sum
                                          V5RelationFullGenerated.aspis_core.field.QM31.ONE =
                                            mismatchResult at bodyRun
                                      cases mismatchResult with
                                      | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                                      | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                                      | ok mismatch =>
                                          cases mismatch with
                                          | true => simp at bodyRun
                                          | false => simp at bodyRun

#print axioms accepted_complete_relation_enters_circle_loop
#print axioms accepted_circle_loop_exposes_relation_loop

end AspisV5RelationTopLevelSuccessInversion
