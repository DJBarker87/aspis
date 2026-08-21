import V5RelationCallerGenerated
import V5RelationFullSourceProof
import V5RelationTopLevelSuccessInversion

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxRecDepth 3000

namespace AspisV5RelationAcceptanceSourceProof

open V5RelationCallerGenerated

abbrev RawQM31 := V5RelationCallerGenerated.aspis_core.field.QM31

theorem raw_qm31_eq_spec (left right : RawQM31) :
    V5RelationCallerGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq
        left right = .ok (decide (left = right)) := by
  rcases left with ⟨⟨la0, la1⟩, ⟨lb0, lb1⟩⟩
  rcases right with ⟨⟨ra0, ra1⟩, ⟨rb0, rb1⟩⟩
  by_cases h0 : la0 = ra0 <;> by_cases h1 : la1 = ra1 <;>
    by_cases h2 : lb0 = rb0 <;> by_cases h3 : lb1 = rb1 <;>
    simp_all [V5RelationCallerGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq,
      V5RelationCallerGenerated.aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq,
      V5RelationCallerGenerated.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq]

theorem raw_qm31_ne_spec (left right : RawQM31) :
    core.cmp.PartialEq.ne.trait_default
        V5RelationCallerGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
        left right = .ok (decide (left ≠ right)) := by
  simp [core.cmp.PartialEq.ne.trait_default,
    core.cmp.PartialEq.ne.default, raw_qm31_eq_spec]

theorem raw_qm31_ne_default_spec (left right : RawQM31) :
    core.cmp.PartialEq.ne.default
        V5RelationCallerGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq
        left right = .ok (decide (left ≠ right)) := by
  simp [core.cmp.PartialEq.ne.default, raw_qm31_eq_spec]

private theorem allM_zip_no_raw_qm31_difference
    (left right : List RawQM31) (sameLength : left.length = right.length) :
    List.allM
        (fun pair => do
          let differs ← core.cmp.PartialEq.ne.default
            V5RelationCallerGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq
            pair.1 pair.2
          ok (decide (¬ differs = true)))
        (List.zip left right) = .ok true →
      left = right := by
  induction left generalizing right with
  | nil =>
      intro hrun
      cases right <;> simp_all
  | cons head tail ih =>
      cases right with
      | nil => simp at sameLength
      | cons head' tail' =>
          intro hrun
          simp only [List.length_cons, Nat.add_right_cancel_iff] at sameLength
          simp only [List.zip_cons_cons, List.allM] at hrun
          generalize htail : List.allM
              (fun pair => do
                let differs ← core.cmp.PartialEq.ne.default
                  V5RelationCallerGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq
                  pair.1 pair.2
                ok (decide (¬ differs = true)))
              (List.zip tail tail') = tailResult at hrun
          rw [raw_qm31_ne_default_spec head head'] at hrun
          by_cases hHead : head = head'
          · subst head'
            simp [pure] at hrun
            have hTail := ih tail' sameLength (hrun ▸ htail)
            subst tail'
            rfl
          · simp [hHead, pure] at hrun

theorem raw_qm31_array_ne_false_implies_eq {size : Std.Usize}
    (left right : Array RawQM31 size) :
    core.array.equality.PartialEqArray.ne
        V5RelationCallerGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
        left right = .ok false → left = right := by
  intro hrun
  unfold core.array.equality.PartialEqArray.ne at hrun
  unfold core.array.equality.PartialEqArray.eq at hrun
  have sameLength : left.length = right.length := by simp
  simp only [sameLength, ↓reduceIte] at hrun
  generalize hresult : List.allM
      (fun pair => do
        let differs ← core.cmp.PartialEq.ne.default
          V5RelationCallerGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq
          pair.1 pair.2
        ok (decide (¬ differs = true)))
      (List.zip left.val right.val) = result at hrun
  cases result with
  | fail error => simp at hrun
  | div => simp at hrun
  | ok equal =>
      cases equal <;> simp at hrun
      apply Subtype.ext
      exact allM_zip_no_raw_qm31_difference left.val right.val
        (by simp_all) hresult

/-- The exact helper calls reached by one successful extracted mode-9 caller.
This record retains the successful preparation, compact-state construction,
and complete relation-checker call so that a separately extracted complete
relation body can be connected to this *same* execution. -/
structure AcceptedMode9RelationHelperCalls
    (parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData)
    (finalPolynomial : Array RawQM31 4#usize)
    (alphas : Array RawQM31 4#usize)
    (kappa inactiveClaim : RawQM31)
    (roundChallenges : Array RawQM31 10#usize)
    (preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims)
    (terminalClaim : RawQM31) : Type where
  relation : V5RelationCallerGenerated.v5_cu_probe.PreparedRelation
  ignoredAlphas : Array RawQM31 10#usize
  denseScale : RawQM31
  compact : V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights
  output : V5RelationCallerGenerated.v5_relation_stress.VerifiedV5RelationStress
  prepareSuccess :
    V5RelationCallerGenerated.v5_cu_probe.prepare_relation_base_with_kappa_prepared
        parsed V5RelationCallerGenerated.v5_cu_probe.RelationVariant.FourClaimsCompact
        kappa inactiveClaim preparedClaims =
      .ok (.Ok (relation, ignoredAlphas, denseScale))
  compactSuccess :
    V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.new
        roundChallenges denseScale = .ok compact
  relationSuccess :
    V5RelationCallerGenerated.v5_relation_stress.verify_v5_relation_stress_with_additive
        V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.Insts.V5_relation_production_harnessV5_relation_stressV5RelationStressAdditive
        relation.weights relation.relation_value alphas
        parsed.v5_relation_stress compact = .ok (.Ok output)
  finalPolynomialMatch : output.final_coefficients = finalPolynomial
  terminalClaimMatch : output.terminal_claim = terminalClaim

/-- Invert one successful outer caller and retain all three actual helper
calls.  No equality to a separately chosen relation execution is supplied. -/
theorem extracted_mode9_success_exposes_helper_calls
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
    Nonempty (AcceptedMode9RelationHelperCalls parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim) := by
  unfold V5RelationCallerGenerated.v5_cu_probe.verify_mode9_relation_phase at success
  generalize hprepare :
      V5RelationCallerGenerated.v5_cu_probe.prepare_relation_base_with_kappa_prepared
        parsed V5RelationCallerGenerated.v5_cu_probe.RelationVariant.FourClaimsCompact
        kappa inactiveClaim preparedClaims = prepareResult at success
  cases prepareResult with
  | fail error => simp at success
  | div => simp at success
  | ok prepared =>
      cases prepared with
      | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
            at success
      | Ok value =>
          rcases value with ⟨relation, ignoredAlphas, denseScale⟩
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at success
          generalize hnew :
              V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.new
                roundChallenges denseScale = newResult at success
          cases newResult with
          | fail error =>
              cases success
          | div =>
              cases success
          | ok compact =>
              simp only [bind_tc_ok] at success
              generalize hverify :
                  V5RelationCallerGenerated.v5_relation_stress.verify_v5_relation_stress_with_additive
                    V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.Insts.V5_relation_production_harnessV5_relation_stressV5RelationStressAdditive
                    relation.weights relation.relation_value alphas
                    parsed.v5_relation_stress compact = verifyResult at success
              cases verifyResult with
              | fail error =>
                  cases success
              | div =>
                  cases success
              | ok verified =>
                  simp only [bind_tc_ok] at success
                  cases verified with
                  | Err error =>
                      simp [V5RelationCallerGenerated.core.result.Result.map_err,
                        V5RelationCallerGenerated.v5_cu_probe.verify_mode9_relation_phase.closure.Insts.CoreOpsFunctionFnOnceTupleV5RelationStressErrorProgramError.call_once,
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                        at success
                  | Ok output =>
                      simp only [V5RelationCallerGenerated.core.result.Result.map_err,
                        bind_tc_ok] at success
                      generalize hne :
                          core.array.equality.PartialEqArray.ne
                            V5RelationCallerGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                            output.final_coefficients finalPolynomial = neResult at success
                      cases neResult with
                      | fail error => simp at success
                      | div => simp at success
                      | ok differs =>
                          by_cases hdiffers : differs = true
                          · simp [hdiffers] at success
                          · have hfalse : differs = false := Bool.eq_false_of_not_eq_true hdiffers
                            subst differs
                            simp at success
                            cases success
                            exact ⟨{
                              relation := relation
                              ignoredAlphas := ignoredAlphas
                              denseScale := denseScale
                              compact := compact
                              output := output
                              prepareSuccess := hprepare
                              compactSuccess := hnew
                              relationSuccess := hverify
                              finalPolynomialMatch :=
                                raw_qm31_array_ne_false_implies_eq _ _ hne
                              terminalClaimMatch := rfl }⟩

/-- The exact extracted mode-9 caller cannot return success unless the four
coefficients returned by the relation checker equal the four coefficients
already accepted by the FRI phase. -/
theorem extracted_mode9_success_implies_final_polynomial_match
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
    ∃ output : V5RelationCallerGenerated.v5_relation_stress.VerifiedV5RelationStress,
      output.final_coefficients = finalPolynomial ∧
      output.terminal_claim = terminalClaim := by
  obtain ⟨calls⟩ := extracted_mode9_success_exposes_helper_calls parsed
    finalPolynomial alphas kappa inactiveClaim roundChallenges preparedClaims
    terminalClaim success
  exact ⟨calls.output, calls.finalPolynomialMatch,
    calls.terminalClaimMatch⟩

/-- The successful relation helper retained above is definitionally the
unchanged full Charon/Aeneas relation verifier.  Thus the *same* accepted
caller execution enters the generated four-round relation loop; no second
relation run or equality premise is introduced. -/
theorem accepted_helper_calls_expose_full_relation_loop
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    (calls : AcceptedMode9RelationHelperCalls parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim) :
    ∃ circlePoints,
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0
          V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.Insts.V5_relation_production_harnessV5_relation_stressV5RelationStressAdditive
          (AspisV5RelationFullSourceProof.alphaIteratorAt alphas 0 0#usize)
          calls.relation.weights calls.relation.relation_value
          parsed.v5_relation_stress calls.compact circlePoints none =
        .ok (some (.Ok calls.output)) := by
  have completeRun :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive
          V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.Insts.V5_relation_production_harnessV5_relation_stressV5RelationStressAdditive
          calls.relation.weights calls.relation.relation_value alphas
          parsed.v5_relation_stress calls.compact = .ok (.Ok calls.output) := by
    simpa [
      V5RelationCallerGenerated.v5_relation_stress.verify_v5_relation_stress_with_additive]
      using calls.relationSuccess
  have circleRun :=
    AspisV5RelationTopLevelSuccessInversion.accepted_complete_relation_enters_circle_loop
      V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.Insts.V5_relation_production_harnessV5_relation_stressV5RelationStressAdditive
      calls.relation.weights calls.relation.relation_value alphas
      parsed.v5_relation_stress calls.compact calls.output completeRun
  exact
    AspisV5RelationTopLevelSuccessInversion.accepted_circle_loop_exposes_relation_loop
      V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.Insts.V5_relation_production_harnessV5_relation_stressV5RelationStressAdditive
      _ _ _ _ _ calls.relation.weights calls.relation.relation_value alphas
      parsed.v5_relation_stress calls.compact calls.output circleRun

/-- One same-run trace from the accepted outer caller through all four
generated relation rounds and the terminal decoder/dot checks.  The embedded
`calls` record retains the exact preparation, compact constructor, complete
verifier, final-polynomial, and returned-terminal equalities. -/
structure AcceptedMode9FullRelationTrace
    (parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData)
    (finalPolynomial : Array RawQM31 4#usize)
    (alphas : Array RawQM31 4#usize)
    (kappa inactiveClaim : RawQM31)
    (roundChallenges : Array RawQM31 10#usize)
    (preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims)
    (terminalClaim : RawQM31) : Type where
  calls : AcceptedMode9RelationHelperCalls parsed finalPolynomial alphas
    kappa inactiveClaim roundChallenges preparedClaims terminalClaim
  circlePoints : Array
    V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize
  weights1 : V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator
  claim1 : RawQM31
  additive1 : V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights
  weights2 : V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator
  claim2 : RawQM31
  additive2 : V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights
  weights3 : V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator
  claim3 : RawQM31
  additive3 : V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights
  weights4 : V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator
  claim4 : RawQM31
  additive4 : V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights
  round0Success :
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0.body
        V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.Insts.V5_relation_production_harnessV5_relation_stressV5RelationStressAdditive
        parsed.v5_relation_stress circlePoints
        (AspisV5RelationFullSourceProof.alphaIteratorAt alphas 0 0#usize)
        calls.relation.weights calls.relation.relation_value calls.compact none =
      .ok (.cont
        (AspisV5RelationFullSourceProof.alphaIteratorAt alphas 1 1#usize,
          weights1, claim1, additive1, none))
  round1Success :
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0.body
        V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.Insts.V5_relation_production_harnessV5_relation_stressV5RelationStressAdditive
        parsed.v5_relation_stress circlePoints
        (AspisV5RelationFullSourceProof.alphaIteratorAt alphas 1 1#usize)
        weights1 claim1 additive1 none =
      .ok (.cont
        (AspisV5RelationFullSourceProof.alphaIteratorAt alphas 2 2#usize,
          weights2, claim2, additive2, none))
  round2Success :
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0.body
        V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.Insts.V5_relation_production_harnessV5_relation_stressV5RelationStressAdditive
        parsed.v5_relation_stress circlePoints
        (AspisV5RelationFullSourceProof.alphaIteratorAt alphas 2 2#usize)
        weights2 claim2 additive2 none =
      .ok (.cont
        (AspisV5RelationFullSourceProof.alphaIteratorAt alphas 3 3#usize,
          weights3, claim3, additive3, none))
  round3Success :
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0.body
        V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.Insts.V5_relation_production_harnessV5_relation_stressV5RelationStressAdditive
        parsed.v5_relation_stress circlePoints
        (AspisV5RelationFullSourceProof.alphaIteratorAt alphas 3 3#usize)
        weights3 claim3 additive3 none =
      .ok (.cont
        (AspisV5RelationFullSourceProof.alphaIteratorAt alphas 4 4#usize,
          weights4, claim4, additive4, none))
  finalCoefficients : Array RawQM31 4#usize
  mainDot : RawQM31
  additiveDot : RawQM31
  finalDecodeSuccess :
    V5RelationFullGenerated.relation_stress.decode_v5_relation_stress_final
        parsed.v5_relation_stress = .ok (.Ok finalCoefficients)
  mainDotSuccess :
    aspis_core.sumcheck.WeightAccumulator.dot
        weights4 (Array.to_slice finalCoefficients) = .ok mainDot
  additiveDotSuccess :
    V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.Insts.V5_relation_production_harnessV5_relation_stressV5RelationStressAdditive.dot
        additive4 finalCoefficients = .ok additiveDot
  terminalAddSuccess :
    V5RelationFullGenerated.aspis_core.field.QM31.add mainDot additiveDot =
      .ok claim4
  outputExact : calls.output =
    { final_coefficients := finalCoefficients
      terminal_claim := claim4 }

/-- Invert one accepted extracted caller into its complete same-run generated
relation trace. -/
theorem extracted_mode9_success_exposes_full_relation_trace
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
    Nonempty (AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim) := by
  obtain ⟨calls⟩ := extracted_mode9_success_exposes_helper_calls parsed
    finalPolynomial alphas kappa inactiveClaim roundChallenges preparedClaims
    terminalClaim success
  obtain ⟨circlePoints, relationLoop⟩ :=
    accepted_helper_calls_expose_full_relation_loop calls
  obtain ⟨weights1, claim1, additive1, weights2, claim2, additive2,
      weights3, claim3, additive3, weights4, claim4, additive4,
      round0, round1, round2, round3, terminalLoop⟩ :=
    AspisV5RelationFullSuccessInversion.accepted_outer_loop_yields_four_ordered_rounds
      V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.Insts.V5_relation_production_harnessV5_relation_stressV5RelationStressAdditive
      alphas parsed.v5_relation_stress circlePoints calls.relation.weights
      calls.relation.relation_value calls.compact calls.output relationLoop
  obtain ⟨finalCoefficients, mainDot, additiveDot, finalDecode, mainDotRun,
      additiveDotRun, terminalAdd, outputExact⟩ :=
    AspisV5RelationFullSuccessInversion.accepted_outer_loop_terminal_calls_are_exact
      V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.Insts.V5_relation_production_harnessV5_relation_stressV5RelationStressAdditive
      alphas parsed.v5_relation_stress circlePoints weights4 claim4 additive4
      calls.output terminalLoop
  exact ⟨{
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
    outputExact := outputExact }⟩

#print axioms raw_qm31_eq_spec
#print axioms raw_qm31_ne_spec
#print axioms raw_qm31_array_ne_false_implies_eq
#print axioms extracted_mode9_success_exposes_helper_calls
#print axioms extracted_mode9_success_implies_final_polynomial_match
#print axioms accepted_helper_calls_expose_full_relation_loop
#print axioms extracted_mode9_success_exposes_full_relation_trace

end AspisV5RelationAcceptanceSourceProof
