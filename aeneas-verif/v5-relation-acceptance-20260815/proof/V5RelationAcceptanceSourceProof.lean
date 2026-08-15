import V5RelationCallerGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxRecDepth 3000

namespace AspisV5RelationAcceptanceSourceProof

open V5RelationCallerGenerated

abbrev RawQM31 := V5RelationCallerGenerated.aspis_core.field.QM31

deriving instance DecidableEq for
  V5RelationCallerGenerated.aspis_core.field.CM31
deriving instance DecidableEq for
  V5RelationCallerGenerated.aspis_core.field.QM31

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

/-- The exact extracted mode-9 caller cannot return success unless the four
coefficients returned by the relation checker equal the four coefficients
already accepted by the FRI phase.  The relation checker itself is opaque in
this extraction because pinned Aeneas rejects its nested early-return loops;
the theorem holds for every possible result of that opaque call. -/
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
                            exact ⟨output,
                              raw_qm31_array_ne_false_implies_eq _ _ hne,
                              rfl⟩

#print axioms raw_qm31_eq_spec
#print axioms raw_qm31_ne_spec
#print axioms raw_qm31_array_ne_false_implies_eq
#print axioms extracted_mode9_success_implies_final_polynomial_match

end AspisV5RelationAcceptanceSourceProof
