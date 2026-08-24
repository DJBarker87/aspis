import V5AcceptedAccumulatorCanonicalSchedule

namespace AspisV5AcceptedCirclePointCanonical

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisV5RelationAcceptanceSourceProof
open AspisV5AcceptedRelationRoundInversion
open AspisV5AcceptedAccumulatorCanonicalSchedule
open AspisV5RelationFullSourceProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev RawQM31 := V5RelationFullGenerated.aspis_core.field.QM31
abbrev CirclePoint :=
  V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint
abbrev Verified :=
  V5RelationFullGenerated.relation_stress.VerifiedV5RelationStress

private theorem usizeAddExactLocal (x y z : Std.Usize)
    (bound : x.val + y.val ≤ Std.Usize.max)
    (value : z.val = x.val + y.val) :
    (x + y : Result Std.Usize) = .ok z := by
  have specification := Std.Usize.add_spec (x := x) (y := y) bound
  obtain ⟨actual, actualRun, actualValue⟩ :=
    Aeneas.Std.WP.spec_imp_exists specification
  have actualExact : actual = z := by
    apply UScalar.eq_of_val_eq
    omega
  rw [actualRun, actualExact]

theorem acceptedCompleteRelationExposesCanonicalCirclePoints
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (weights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (runningClaim : RawQM31)
    (alphas : Array RawQM31 4#usize)
    (bytes : Array Std.U8 928#usize) (additive : A)
    (output : Verified)
    (run :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive
          additiveInst weights runningClaim alphas bytes additive =
        .ok (.Ok output)) :
    ∃ points : Array CirclePoint 2#usize,
      CanonicalCirclePoints points ∧
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0
          additiveInst (alphaIteratorAt alphas 0 0#usize) weights
          runningClaim bytes additive points none = .ok (some (.Ok output)) := by
  have loopRun :=
    AspisV5RelationTopLevelSuccessInversion.accepted_complete_relation_enters_circle_loop
      additiveInst weights runningClaim alphas bytes additive output run
  have firstInBounds :
      (0 : Nat) < (Array.repeat 2#usize
        ({ x := V5RelationFullGenerated.aspis_core.field.QM31.ZERO,
           y := V5RelationFullGenerated.aspis_core.field.QM31.ZERO } :
          CirclePoint)).to_slice_mut.1.len.val := by
    change 0 < (Array.repeat 2#usize
      ({ x := V5RelationFullGenerated.aspis_core.field.QM31.ZERO,
         y := V5RelationFullGenerated.aspis_core.field.QM31.ZERO } :
        CirclePoint)).val.length
    rw [Array.repeat_val]
    decide
  have count0Next : (0#usize + 1#usize : Result Std.Usize) =
      .ok 1#usize := by
    apply usizeAddExactLocal <;> scalar_tac
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0
    at loopRun
  rw [Aeneas.Std.loop.eq_def] at loopRun
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0.body
    at loopRun
  simp only [V5MutableEnumerateSupport.next,
    core.slice.iter.IteratorIterMut.next] at loopRun
  simp only [dif_pos firstInBounds] at loopRun
  simp only [bind_tc_ok] at loopRun
  rw [count0Next] at loopRun
  simp only [bind_tc_ok, Aeneas.Std.lift] at loopRun
  generalize readX0 :
      V5RelationFullGenerated.relation_stress.decode_indexed bytes
        V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_CIRCLE_OFFSET
        (Std.Usize.wrapping_mul 2#usize 0#usize) = x0Result at loopRun
  cases x0Result with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at loopRun
  | div => simp [Bind.bind, Aeneas.Std.bind] at loopRun
  | ok decodedX0 =>
      cases decodedX0 with
      | Err error =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at loopRun
          simp at loopRun
      | Ok x0 =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            bind_tc_ok] at loopRun
          generalize readY0 :
              V5RelationFullGenerated.relation_stress.decode_indexed bytes
                V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_CIRCLE_OFFSET
                (Std.Usize.wrapping_add
                  (Std.Usize.wrapping_mul 2#usize 0#usize) 1#usize) =
                    y0Result at loopRun
          cases y0Result with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at loopRun
          | div => simp [Bind.bind, Aeneas.Std.bind] at loopRun
          | ok decodedY0 =>
              cases decodedY0 with
              | Err error =>
                  simp only [core.result.Result.Insts.CoreOpsTry.branch,
                    bind_tc_ok,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame.from] at loopRun
                  simp at loopRun
              | Ok y0 =>
                  simp only [core.result.Result.Insts.CoreOpsTry.branch,
                    bind_tc_ok] at loopRun
                  generalize squareX0 :
                      V5RelationFullGenerated.aspis_core.field.QM31.square x0 =
                        squareX0Result at loopRun
                  cases squareX0Result with
                  | fail error => simp at loopRun
                  | div => simp at loopRun
                  | ok x0Square =>
                      simp only [bind_tc_ok] at loopRun
                      generalize squareY0 :
                          V5RelationFullGenerated.aspis_core.field.QM31.square y0 =
                            squareY0Result at loopRun
                      cases squareY0Result with
                      | fail error => simp at loopRun
                      | div => simp at loopRun
                      | ok y0Square =>
                          simp only [bind_tc_ok] at loopRun
                          generalize circle0 :
                              V5RelationFullGenerated.aspis_core.field.QM31.add
                                x0Square y0Square = circle0Result at loopRun
                          cases circle0Result with
                          | fail error => simp at loopRun
                          | div => simp at loopRun
                          | ok circleValue0 =>
                              simp only [bind_tc_ok] at loopRun
                              generalize compare0 :
                                  core.cmp.PartialEq.ne.trait_default
                                    V5RelationFullGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                                    circleValue0
                                    V5RelationFullGenerated.aspis_core.field.QM31.ONE =
                                      compare0Result at loopRun
                              cases compare0Result with
                              | fail error => simp at loopRun
                              | div => simp at loopRun
                              | ok mismatch0 =>
                                  simp only [bind_tc_ok] at loopRun
                                  by_cases mismatch : mismatch0 = true
                                  · rw [if_pos mismatch] at loopRun
                                    simp at loopRun
                                  · rw [if_neg mismatch] at loopRun
                                    dsimp only at loopRun
                                    have secondInBounds :
                                        (1 : Nat) < (Array.repeat 2#usize
                                          ({ x := V5RelationFullGenerated.aspis_core.field.QM31.ZERO,
                                             y := V5RelationFullGenerated.aspis_core.field.QM31.ZERO } :
                                            CirclePoint)).to_slice_mut.1.len.val := by
                                      change 1 < (Array.repeat 2#usize
                                        ({ x := V5RelationFullGenerated.aspis_core.field.QM31.ZERO,
                                           y := V5RelationFullGenerated.aspis_core.field.QM31.ZERO } :
                                          CirclePoint)).val.length
                                      rw [Array.repeat_val]
                                      decide
                                    have count1Next :
                                        (1#usize + 1#usize : Result Std.Usize) =
                                          .ok 2#usize := by
                                      apply usizeAddExactLocal <;> scalar_tac
                                    rw [Aeneas.Std.loop.eq_def] at loopRun
                                    dsimp only at loopRun
                                    simp only [dif_pos secondInBounds] at loopRun
                                    simp only [bind_tc_ok] at loopRun
                                    rw [count1Next] at loopRun
                                    simp only [bind_tc_ok, Aeneas.Std.lift]
                                      at loopRun
                                    generalize readX1 :
                                        V5RelationFullGenerated.relation_stress.decode_indexed
                                          bytes
                                          V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_CIRCLE_OFFSET
                                          (Std.Usize.wrapping_mul 2#usize
                                            1#usize) = x1Result at loopRun
                                    cases x1Result with
                                    | fail error =>
                                        simp [Bind.bind, Aeneas.Std.bind]
                                          at loopRun
                                    | div =>
                                        simp [Bind.bind, Aeneas.Std.bind]
                                          at loopRun
                                    | ok decodedX1 =>
                                        cases decodedX1 with
                                        | Err error =>
                                            simp only [bind_tc_ok,
                                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                              core.convert.FromSame.from]
                                              at loopRun
                                            simp at loopRun
                                        | Ok x1 =>
                                            simp only [bind_tc_ok] at loopRun
                                            generalize readY1 :
                                                V5RelationFullGenerated.relation_stress.decode_indexed
                                                  bytes
                                                  V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_CIRCLE_OFFSET
                                                  (Std.Usize.wrapping_add
                                                    (Std.Usize.wrapping_mul
                                                      2#usize 1#usize)
                                                    1#usize) = y1Result
                                                      at loopRun
                                            cases y1Result with
                                            | fail error =>
                                                simp [Bind.bind,
                                                  Aeneas.Std.bind] at loopRun
                                            | div =>
                                                simp [Bind.bind,
                                                  Aeneas.Std.bind] at loopRun
                                            | ok decodedY1 =>
                                                cases decodedY1 with
                                                | Err error =>
                                                    simp only [bind_tc_ok,
                                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                                      core.convert.FromSame.from]
                                                      at loopRun
                                                    simp at loopRun
                                                | Ok y1 =>
                                                    simp only [bind_tc_ok]
                                                      at loopRun
                                                    generalize squareX1 :
                                                        V5RelationFullGenerated.aspis_core.field.QM31.square
                                                          x1 = squareX1Result
                                                            at loopRun
                                                    cases squareX1Result with
                                                    | fail error =>
                                                        simp at loopRun
                                                    | div => simp at loopRun
                                                    | ok x1Square =>
                                                        simp only [bind_tc_ok]
                                                          at loopRun
                                                        generalize squareY1 :
                                                            V5RelationFullGenerated.aspis_core.field.QM31.square
                                                              y1 = squareY1Result
                                                                at loopRun
                                                        cases squareY1Result with
                                                        | fail error =>
                                                            simp at loopRun
                                                        | div => simp at loopRun
                                                        | ok y1Square =>
                                                            simp only [bind_tc_ok]
                                                              at loopRun
                                                            generalize circle1 :
                                                                V5RelationFullGenerated.aspis_core.field.QM31.add
                                                                  x1Square
                                                                  y1Square =
                                                                    circle1Result
                                                                      at loopRun
                                                            cases circle1Result with
                                                            | fail error =>
                                                                simp at loopRun
                                                            | div =>
                                                                simp at loopRun
                                                            | ok circleValue1 =>
                                                                simp only [bind_tc_ok]
                                                                  at loopRun
                                                                generalize compare1 :
                                                                    core.cmp.PartialEq.ne.trait_default
                                                                      V5RelationFullGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                                                                      circleValue1
                                                                      V5RelationFullGenerated.aspis_core.field.QM31.ONE =
                                                                        compare1Result
                                                                          at loopRun
                                                                cases compare1Result with
                                                                | fail error =>
                                                                    simp at loopRun
                                                                | div =>
                                                                    simp at loopRun
                                                                | ok mismatch1 =>
                                                                    simp only [bind_tc_ok]
                                                                      at loopRun
                                                                    by_cases secondMismatch :
                                                                        mismatch1 = true
                                                                    · rw [if_pos secondMismatch]
                                                                        at loopRun
                                                                      simp at loopRun
                                                                    · rw [if_neg secondMismatch]
                                                                        at loopRun
                                                                      dsimp only at loopRun
                                                                      have exhausted :
                                                                          ¬ (2 : Nat) <
                                                                            (Array.repeat 2#usize
                                                                              ({ x := V5RelationFullGenerated.aspis_core.field.QM31.ZERO,
                                                                                 y := V5RelationFullGenerated.aspis_core.field.QM31.ZERO } :
                                                                                CirclePoint)).to_slice_mut.1.len.val := by
                                                                        change ¬ 2 <
                                                                          (Array.repeat 2#usize
                                                                            ({ x := V5RelationFullGenerated.aspis_core.field.QM31.ZERO,
                                                                               y := V5RelationFullGenerated.aspis_core.field.QM31.ZERO } :
                                                                              CirclePoint)).val.length
                                                                        rw [Array.repeat_val]
                                                                        decide
                                                                      rw [Aeneas.Std.loop.eq_def]
                                                                        at loopRun
                                                                      dsimp only at loopRun
                                                                      simp only [dif_neg exhausted]
                                                                        at loopRun
                                                                      simp only [bind_tc_ok]
                                                                        at loopRun
                                                                      simp [
                                                                        Array.to_slice_mut,
                                                                        Array.to_slice,
                                                                        Array.from_slice,
                                                                        Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
                                                                        core.iter.traits.iterator.Iterator.enumerate.trait_default,
                                                                        core.iter.traits.iterator.Iterator.enumerate.default,
                                                                        alphaIteratorAt]
                                                                        at loopRun
                                                                      simp only [
                                                                        Slice.setAtNat,
                                                                        List.set]
                                                                        at loopRun
                                                                      generalize roundRun :
                                                                          V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0
                                                                            additiveInst _ weights
                                                                            runningClaim bytes additive
                                                                            _ none = roundResult
                                                                        at loopRun
                                                                      have roundResultExact :
                                                                          roundResult =
                                                                            .ok (some (.Ok output)) := by
                                                                        cases roundResult with
                                                                        | fail error =>
                                                                            simp at loopRun
                                                                        | div =>
                                                                            simp at loopRun
                                                                        | ok maybe =>
                                                                            cases maybe with
                                                                            | none =>
                                                                                simp at loopRun
                                                                            | some result =>
                                                                                have resultExact :
                                                                                    result = .Ok output := by
                                                                                  simpa using loopRun
                                                                                simp [resultExact]
                                                                      have x0Canonical :=
                                                                        accepted_decode_indexed_is_canonical
                                                                          bytes
                                                                          V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_CIRCLE_OFFSET
                                                                          (Std.Usize.wrapping_mul
                                                                            2#usize 0#usize)
                                                                          x0 readX0
                                                                      have y0Canonical :=
                                                                        accepted_decode_indexed_is_canonical
                                                                          bytes
                                                                          V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_CIRCLE_OFFSET
                                                                          (Std.Usize.wrapping_add
                                                                            (Std.Usize.wrapping_mul
                                                                              2#usize 0#usize)
                                                                            1#usize)
                                                                          y0 readY0
                                                                      have x1Canonical :=
                                                                        accepted_decode_indexed_is_canonical
                                                                          bytes
                                                                          V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_CIRCLE_OFFSET
                                                                          (Std.Usize.wrapping_mul
                                                                            2#usize 1#usize)
                                                                          x1 readX1
                                                                      have y1Canonical :=
                                                                        accepted_decode_indexed_is_canonical
                                                                          bytes
                                                                          V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_CIRCLE_OFFSET
                                                                          (Std.Usize.wrapping_add
                                                                            (Std.Usize.wrapping_mul
                                                                              2#usize 1#usize)
                                                                            1#usize)
                                                                          y1 readY1
                                                                      have x0LinkedCanonical :
                                                                          AspisV5RelationLinkedFieldProjection.CanonicalQM31
                                                                            x0 := by
                                                                        simpa [
                                                                          AspisV5RelationGeneratedFieldProjection.CanonicalQM31,
                                                                          AspisV5RelationGeneratedFieldProjection.CanonicalCM31,
                                                                          AspisV5RelationLinkedFieldProjection.CanonicalQM31,
                                                                          AspisV5RelationLinkedFieldProjection.CanonicalCM31]
                                                                          using x0Canonical
                                                                      have y0LinkedCanonical :
                                                                          AspisV5RelationLinkedFieldProjection.CanonicalQM31
                                                                            y0 := by
                                                                        simpa [
                                                                          AspisV5RelationGeneratedFieldProjection.CanonicalQM31,
                                                                          AspisV5RelationGeneratedFieldProjection.CanonicalCM31,
                                                                          AspisV5RelationLinkedFieldProjection.CanonicalQM31,
                                                                          AspisV5RelationLinkedFieldProjection.CanonicalCM31]
                                                                          using y0Canonical
                                                                      have x1LinkedCanonical :
                                                                          AspisV5RelationLinkedFieldProjection.CanonicalQM31
                                                                            x1 := by
                                                                        simpa [
                                                                          AspisV5RelationGeneratedFieldProjection.CanonicalQM31,
                                                                          AspisV5RelationGeneratedFieldProjection.CanonicalCM31,
                                                                          AspisV5RelationLinkedFieldProjection.CanonicalQM31,
                                                                          AspisV5RelationLinkedFieldProjection.CanonicalCM31]
                                                                          using x1Canonical
                                                                      have y1LinkedCanonical :
                                                                          AspisV5RelationLinkedFieldProjection.CanonicalQM31
                                                                            y1 := by
                                                                        simpa [
                                                                          AspisV5RelationGeneratedFieldProjection.CanonicalQM31,
                                                                          AspisV5RelationGeneratedFieldProjection.CanonicalCM31,
                                                                          AspisV5RelationLinkedFieldProjection.CanonicalQM31,
                                                                          AspisV5RelationLinkedFieldProjection.CanonicalCM31]
                                                                          using y1Canonical
                                                                      refine ⟨twoCirclePoints x0 y0 x1 y1, ?_, ?_⟩
                                                                      · intro index
                                                                        fin_cases index
                                                                        · simpa [twoCirclePoints,
                                                                            Array.make] using
                                                                            And.intro x0LinkedCanonical
                                                                              y0LinkedCanonical
                                                                        · simpa [twoCirclePoints,
                                                                            Array.make] using
                                                                            And.intro x1LinkedCanonical
                                                                              y1LinkedCanonical
                                                                      · have exactRounds :=
                                                                          roundRun.trans roundResultExact
                                                                        simpa [twoCirclePoints,
                                                                          Array.make,
                                                                          alphaIteratorAt] using
                                                                          exactRounds

/-- Rebuild the complete accepted relation trace from the canonical points
decoded by the accepted outer relation call.  The earlier trace constructor
chose an existential point array and then discarded its canonicality proof;
this constructor keeps both facts from the same inversion. -/
theorem extracted_mode9_success_exposes_canonical_full_relation_trace
    (parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData)
    (finalPolynomial : Array RawQM31 4#usize)
    (alphas : Array RawQM31 4#usize)
    (kappa inactiveClaim : RawQM31)
    (roundChallenges : Array RawQM31 10#usize)
    (preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims)
    (terminalClaim : RawQM31)
    (success :
      V5RelationCallerGenerated.v5_cu_probe.verify_mode9_relation_phase
          parsed finalPolynomial alphas kappa inactiveClaim roundChallenges
          preparedClaims = .ok (.Ok terminalClaim)) :
    ∃ trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
        kappa inactiveClaim roundChallenges preparedClaims terminalClaim,
      CanonicalCirclePoints trace.circlePoints := by
  obtain ⟨calls⟩ := extracted_mode9_success_exposes_helper_calls parsed
    finalPolynomial alphas kappa inactiveClaim roundChallenges preparedClaims
    terminalClaim success
  have completeRun :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive
          productionAdditiveInst calls.relation.weights
          calls.relation.relation_value alphas parsed.v5_relation_stress
          calls.compact = .ok (.Ok calls.output) := by
    simpa [productionAdditiveInst,
      V5RelationCallerGenerated.v5_relation_stress.verify_v5_relation_stress_with_additive]
      using calls.relationSuccess
  obtain ⟨circlePoints, circleCanonical, relationLoop⟩ :=
    acceptedCompleteRelationExposesCanonicalCirclePoints
      productionAdditiveInst calls.relation.weights
      calls.relation.relation_value alphas parsed.v5_relation_stress
      calls.compact calls.output completeRun
  obtain ⟨weights1, claim1, additive1, weights2, claim2, additive2,
      weights3, claim3, additive3, weights4, claim4, additive4,
      round0, round1, round2, round3, terminalLoop⟩ :=
    AspisV5RelationFullSuccessInversion.accepted_outer_loop_yields_four_ordered_rounds
      productionAdditiveInst alphas parsed.v5_relation_stress circlePoints
      calls.relation.weights calls.relation.relation_value calls.compact
      calls.output relationLoop
  obtain ⟨finalCoefficients, mainDot, additiveDot, finalDecode, mainDotRun,
      additiveDotRun, terminalAdd, outputExact⟩ :=
    AspisV5RelationFullSuccessInversion.accepted_outer_loop_terminal_calls_are_exact
      productionAdditiveInst alphas parsed.v5_relation_stress circlePoints
      weights4 claim4 additive4 calls.output terminalLoop
  let trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim := {
    calls := calls
    circlePoints := circlePoints
    weights1 := weights1
    weights2 := weights2
    weights3 := weights3
    weights4 := weights4
    claim1 := claim1
    claim2 := claim2
    claim3 := claim3
    claim4 := claim4
    additive1 := additive1
    additive2 := additive2
    additive3 := additive3
    additive4 := additive4
    round0Success := round0
    round1Success := round1
    round2Success := round2
    round3Success := round3
    finalCoefficients := finalCoefficients
    mainDot := mainDot
    additiveDot := additiveDot
    finalDecodeSuccess := finalDecode
    mainDotSuccess := mainDotRun
    additiveDotSuccess := additiveDotRun
    terminalAddSuccess := terminalAdd
    outputExact := outputExact }
  exact ⟨trace, circleCanonical⟩

#print axioms acceptedCompleteRelationExposesCanonicalCirclePoints
#print axioms extracted_mode9_success_exposes_canonical_full_relation_trace

end AspisV5AcceptedCirclePointCanonical
