import ComponentBSamplerMixingEvaluateUnified20260722

open Aeneas Aeneas.Std Result ControlFlow Error

namespace ComponentBGenerated.v5_sumcheck_mask

private abbrev QM31 := aspis_core.field.QM31
private abbrev Polynomial := Array QM31 28#usize

private theorem coefficientsEq :
    aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_COEFFICIENTS =
      ok 28#usize := by
  have hspec := Usize.add_spec (x := 27#usize) (y := 1#usize) (by
    scalar_tac)
  obtain ⟨value, valueEquation, valueVal⟩ := WP.spec_imp_exists hspec
  have valueIs28 : value = 28#usize := by
    apply UScalar.eq_of_val_eq
    simpa using valueVal
  unfold aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_COEFFICIENTS
    aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_DEGREE
  rw [valueEquation, valueIs28]

private def prefixMixed
  (base current : Polynomial) (combined : Fin 28 → QM31)
    (coefficient : Std.Usize) : Prop :=
  ∀ i : Fin 28,
    current.val[i.val]? =
      some (if i.val < coefficient.val then combined i else base.val[i.val])

private theorem wrappingAddOneVal
  (coefficient : Std.Usize) (hcoefficient : coefficient.val < 28) :
    (coefficient.wrapping_add 1#usize).val = coefficient.val + 1 := by
  rw [Usize.wrapping_add_val_eq, UScalar.size_UScalarTyUsize]
  simp only [UScalar.ofNatCore_val_eq]
  have hsize : 28 < Usize.size := by
    simpa using UScalar.hSize (28#usize)
  exact Nat.mod_eq_of_lt (by omega)

private theorem prefixMixedSetCurrent
    (base current : Polynomial) (combined : Fin 28 → QM31)
    (coefficient : Std.Usize) (hcoefficient : coefficient.val < 28)
    (hprefix : prefixMixed base current combined coefficient) :
    prefixMixed base (current.set coefficient
      (combined ⟨coefficient.val, hcoefficient⟩)) combined
      (coefficient.wrapping_add 1#usize) := by
  intro i
  have hnext := wrappingAddOneVal coefficient hcoefficient
  rw [Array.set_val_eq]
  by_cases hi : i.val = coefficient.val
  · have hiFin : i = ⟨coefficient.val, hcoefficient⟩ := Fin.ext hi
    subst i
    rw [List.getElem?_set_self (by simpa using hcoefficient)]
    simp [hnext]
  · rw [List.getElem?_set_ne (Ne.symm hi)]
    · have hold := hprefix i
      rw [List.getElem?_eq_getElem (by simpa using i.isLt)] at hold
      rw [hnext]
      by_cases hbefore : i.val < coefficient.val
      · have hle : i.val ≤ coefficient.val := Nat.le_of_lt hbefore
        simpa [hbefore, hle] using hold
      · have hnle : ¬ i.val ≤ coefficient.val := by omega
        simpa [hbefore, hnle] using hold

private theorem generatedMixedLoopPrefix
    (eta : QM31) (real base current : Polynomial)
    (products combined : Fin 28 → QM31)
    (coefficient : Std.Usize) (remaining : Nat)
    (hspan : coefficient.val + remaining = 28)
    (hprefix : prefixMixed base current combined coefficient)
    (hmul : ∀ i : Fin 28,
      aspis_core.field.QM31.mul eta real.val[i.val] = ok (products i))
    (hadd : ∀ i : Fin 28,
      aspis_core.field.QM31.add base.val[i.val] (products i) =
        ok (combined i)) :
    ∃ output,
      V5SumcheckMask.mixed_round_polynomial_loop eta real current coefficient =
        ok output ∧
      ∀ i : Fin 28, output.val[i.val] = combined i := by
  induction remaining generalizing coefficient current with
  | zero =>
      have hcoefficient : coefficient.val = 28 := by omega
      have hnot : ¬ coefficient < 28#usize := by
        scalar_tac
      refine ⟨current, ?_, ?_⟩
      · rw [V5SumcheckMask.mixed_round_polynomial_loop]
        rw [Aeneas.Std.loop.eq_def]
        unfold V5SumcheckMask.mixed_round_polynomial_loop.body
        rw [coefficientsEq]
        simp only [bind_tc_ok]
        rw [if_neg hnot]
      · intro i
        have hi := hprefix i
        rw [List.getElem?_eq_getElem (by simpa using i.isLt)] at hi
        simpa [hcoefficient] using hi
  | succ n ih =>
      have hcoefficient : coefficient.val < 28 := by omega
      have hlt : coefficient < 28#usize := by
        simpa using hcoefficient
      let i : Fin 28 := ⟨coefficient.val, hcoefficient⟩
      have hcurrentBound : coefficient.val < current.length := by
        simpa using hcoefficient
      obtain ⟨currentValue, currentEquation, currentAt⟩ := WP.spec_imp_exists
        (Array.index_usize_spec current coefficient hcurrentBound)
      have hrealBound : coefficient.val < real.length := by
        simpa using hcoefficient
      obtain ⟨realValue, realEquation, realAt⟩ := WP.spec_imp_exists
        (Array.index_usize_spec real coefficient hrealBound)
      have currentIsBase : currentValue = base.val[i.val] := by
        have hcurrent := hprefix i
        rw [List.getElem?_eq_getElem (by simpa using i.isLt)] at hcurrent
        rw [currentAt]
        simpa [i] using hcurrent
      have realIsCurrent : realValue = real.val[i.val] := by
        simpa [i] using realAt
      have mulEquation :
          aspis_core.field.QM31.mul eta realValue = ok (products i) := by
        simpa [realIsCurrent] using hmul i
      have addEquation :
          aspis_core.field.QM31.add currentValue (products i) =
            ok (combined i) := by
        simpa [currentIsBase] using hadd i
      obtain ⟨updated, updatedEquation, updatedIsSet⟩ := WP.spec_imp_exists
        (Array.update_spec current coefficient (combined i) hcurrentBound)
      have hnext := wrappingAddOneVal coefficient hcoefficient
      have hspanNext :
          (coefficient.wrapping_add 1#usize).val + n = 28 := by
        rw [hnext]
        omega
      have hprefixNext :
          prefixMixed base updated combined
            (coefficient.wrapping_add 1#usize) := by
        rw [updatedIsSet]
        exact prefixMixedSetCurrent base current combined coefficient
          hcoefficient hprefix
      obtain ⟨output, loopEquation, outputPointwise⟩ :=
        ih updated (coefficient.wrapping_add 1#usize) hspanNext hprefixNext
      refine ⟨output, ?_, outputPointwise⟩
      rw [V5SumcheckMask.mixed_round_polynomial_loop]
      rw [Aeneas.Std.loop.eq_def]
      unfold V5SumcheckMask.mixed_round_polynomial_loop.body
      rw [coefficientsEq]
      simp only [bind_tc_ok]
      rw [if_pos hlt, currentEquation, realEquation]
      simp only [bind_tc_ok]
      rw [mulEquation]
      simp only [bind_tc_ok]
      rw [addEquation]
      simp only [bind_tc_ok]
      rw [updatedEquation]
      simp only [lift, bind_tc_ok]
      rw [V5SumcheckMask.mixed_round_polynomial_loop] at loopEquation
      unfold V5SumcheckMask.mixed_round_polynomial_loop.body at loopEquation
      rw [coefficientsEq] at loopEquation
      exact loopEquation

/-- The recursive rendering of the actual generated 28-step mixing loop is
    coefficientwise `base + eta * real`, stated using the actual extracted
    QM31 multiplication and addition results at every coefficient. -/
theorem generated_mixed_loop_coefficientwise
    (eta : QM31) (real base : Polynomial)
    (products combined : Fin 28 → QM31)
    (hmul : ∀ i : Fin 28,
      aspis_core.field.QM31.mul eta real.val[i.val] = ok (products i))
    (hadd : ∀ i : Fin 28,
      aspis_core.field.QM31.add base.val[i.val] (products i) =
        ok (combined i)) :
    ∃ output,
      V5SumcheckMask.mixed_round_polynomial_loop eta real base 0#usize =
        ok output ∧
      ∀ i : Fin 28, output.val[i.val] = combined i := by
  apply generatedMixedLoopPrefix eta real base base products combined 0#usize 28
  · norm_num
  · intro i
    simp
  · exact hmul
  · exact hadd

/-- Conditional operational composition of the actual generated deterministic
    mixing wrapper.  Its boundary, claim-arithmetic, round, and per-coefficient
    field-operation premises are all explicit. -/
theorem generated_mixed_round_polynomial_composition
    (mask : V5SumcheckMask) (round : Std.Usize)
    (totalClaim eta realClaim claimProduct maskClaim : QM31)
    (real base : Polynomial) (products combined : Fin 28 → QM31)
    (hboundary :
      aspis_core.state_only_sumcheck.state_only_boundary_sum real =
        ok realClaim)
    (hclaimMul :
      aspis_core.field.QM31.mul eta realClaim = ok claimProduct)
    (hclaimSub :
      aspis_core.field.QM31.sub totalClaim claimProduct = ok maskClaim)
    (hround :
      V5SumcheckMask.round_polynomial mask round maskClaim = ok (some base))
    (hmul : ∀ i : Fin 28,
      aspis_core.field.QM31.mul eta real.val[i.val] = ok (products i))
    (hadd : ∀ i : Fin 28,
      aspis_core.field.QM31.add base.val[i.val] (products i) =
        ok (combined i)) :
    ∃ output,
      V5SumcheckMask.mixed_round_polynomial mask round totalClaim eta real =
        ok (some output) ∧
      ∀ i : Fin 28, output.val[i.val] = combined i := by
  obtain ⟨output, loopEquation, outputPointwise⟩ :=
    generated_mixed_loop_coefficientwise eta real base products combined
      hmul hadd
  refine ⟨output, ?_, outputPointwise⟩
  unfold V5SumcheckMask.mixed_round_polynomial
  rw [hboundary]
  simp only [bind_tc_ok]
  rw [hclaimMul]
  simp only [bind_tc_ok]
  rw [hclaimSub]
  simp only [bind_tc_ok]
  rw [hround]
  simp only [bind_tc_ok]
  rw [loopEquation]
  rfl

#print axioms generated_mixed_loop_coefficientwise
#print axioms generated_mixed_round_polynomial_composition

end ComponentBGenerated.v5_sumcheck_mask
