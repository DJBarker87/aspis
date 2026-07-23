import RuntimeComponentCWire
import Aeneas.Tactic.Step.StepStar

set_option autoImplicit false

/-!
# Source-authentic Component-C runtime schedule validation

The candidate runtime schedule checks every later-layer vector before any
relation or fold evaluation.  This file proves the success branch of that
actual extracted Rust loop: at most 18 fibres, and every fibre strictly below
the supplied layer limit, are sufficient for the generated validator to
return `Ok(())`.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace aspis_prover.ComponentCRuntimeScheduleValidatorProof

open aspis_prover

private def ValidatorLoopInvariant
    (fibres : Slice Std.U32) (ordinal : Std.Usize) : Prop :=
  ordinal.val ≤ fibres.val.length

private def ValidatorLoopPost
    (result : core.result.Result Unit
      v5_mask.component_c_runtime.V5ComponentCRuntimeError) : Prop :=
  result = core.result.Result.Ok ()

private def ValidatorAuditInvariant
    (fibres : Slice Std.U32) (fibreLimit : Std.U32)
    (ordinal : Std.Usize) : Prop :=
  ordinal.val ≤ fibres.val.length ∧
  ∀ fibre ∈ fibres.val.take ordinal.val,
    fibre.val < fibreLimit.val

private def ValidatorAuditPost
    (fibres : Slice Std.U32) (fibreLimit : Std.U32)
    (result : core.result.Result Unit
      v5_mask.component_c_runtime.V5ComponentCRuntimeError) : Prop :=
  result = core.result.Result.Ok () →
    ∀ fibre ∈ fibres.val, fibre.val < fibreLimit.val

/-- The generated loop succeeds when every indexed fibre is below the exact
layer limit.  This theorem is universal in the vector, layer tag, and limit;
it is not a KAT for the three deployed constants. -/
theorem extracted_validator_loop_succeeds
    (fibres : Slice Std.U32) (layer : Std.U8) (fibreLimit : Std.U32)
    (hrange : ∀ fibre ∈ fibres.val, fibre.val < fibreLimit.val) :
    v5_mask.component_c_runtime.validate_component_c_runtime_later_layer_loop
        fibres layer fibreLimit 0#usize
      ⦃ result => ValidatorLoopPost result ⦄ := by
  unfold v5_mask.component_c_runtime.validate_component_c_runtime_later_layer_loop
  apply loop.spec_decr_nat
    (fun ordinal => fibres.val.length - ordinal.val)
    (ValidatorLoopInvariant fibres)
    ValidatorLoopPost
  · intro ordinal hordinal
    unfold ValidatorLoopInvariant at hordinal
    unfold v5_mask.component_c_runtime.validate_component_c_runtime_later_layer_loop.body
    by_cases hactive : ordinal.val < fibres.val.length
    · have hactiveScalar : ordinal < Slice.len fibres := by
        simp only [Slice.len]
        scalar_tac
      have hnextFits : ordinal.val + 1 < Std.Usize.size := by
        have hsliceMax := fibres.property
        have hUsizeSize : Std.Usize.size = Std.Usize.max + 1 := by
          simp [Std.Usize.size, Std.Usize.max, Std.Usize.numBits]
        rw [hUsizeSize]
        omega
      rw [if_pos hactiveScalar]
      step as ⟨fibre, hfibre⟩
      change fibre = fibres.val[ordinal.val] at hfibre
      have hfibreRange : fibre.val < fibreLimit.val := by
        apply hrange fibre
        rw [hfibre]
        exact List.getElem_mem hactive
      have hnotGe : ¬ fibre ≥ fibreLimit := by scalar_tac
      rw [if_neg hnotGe]
      step as ⟨ordinal1, hordinal1⟩
      have hordinal1Val : ordinal1.val = ordinal.val + 1 := by
        rw [hordinal1, Std.Usize.wrapping_add_val_eq]
        apply Nat.mod_eq_of_lt
        simpa using hnextFits
      unfold ValidatorLoopInvariant
      rw [hordinal1Val]
      omega
    · have hdone : ordinal.val = fibres.val.length := by omega
      have hnotActive : ¬ ordinal < Slice.len fibres := by
        simp only [Slice.len]
        scalar_tac
      rw [if_neg hnotActive]
      simp [ValidatorLoopPost]
  · simp [ValidatorLoopInvariant]

/-- The actual extracted validator accepts every vector satisfying its exact
count and range contract.  Both the `> 18` guard and every loop read are part
of this result. -/
theorem extracted_validator_succeeds
    (fibres : Slice Std.U32) (layer : Std.U8) (fibreLimit : Std.U32)
    (hcount : fibres.val.length ≤ 18)
    (hrange : ∀ fibre ∈ fibres.val, fibre.val < fibreLimit.val) :
    v5_mask.component_c_runtime.validate_component_c_runtime_later_layer
        fibres layer fibreLimit =
      ok (core.result.Result.Ok ()) := by
  unfold v5_mask.component_c_runtime.validate_component_c_runtime_later_layer
  have hnotTooMany : ¬ Slice.len fibres >
      v5_mask.component_c_runtime.V5_COMPONENT_C_RUNTIME_MAX_LATER_COUNT := by
    simp only [v5_mask.component_c_runtime.V5_COMPONENT_C_RUNTIME_MAX_LATER_COUNT,
      Slice.len]
    scalar_tac
  rw [if_neg hnotTooMany]
  have hloop := extracted_validator_loop_succeeds fibres layer fibreLimit hrange
  obtain ⟨result, hrun, hpost⟩ := Aeneas.Std.WP.spec_imp_exists hloop
  unfold ValidatorLoopPost at hpost
  simpa [hpost] using hrun

/-- Independently of whether validation succeeds, the generated loop's `Ok`
branch certifies that every slice entry is below the supplied limit.  An
out-of-range entry follows the source's error branch, so the implication is
not an assumed invariant. -/
theorem extracted_validator_loop_audits_range
    (fibres : Slice Std.U32) (layer : Std.U8) (fibreLimit : Std.U32) :
    v5_mask.component_c_runtime.validate_component_c_runtime_later_layer_loop
        fibres layer fibreLimit 0#usize
      ⦃ result => ValidatorAuditPost fibres fibreLimit result ⦄ := by
  unfold v5_mask.component_c_runtime.validate_component_c_runtime_later_layer_loop
  apply loop.spec_decr_nat
    (fun ordinal => fibres.val.length - ordinal.val)
    (ValidatorAuditInvariant fibres fibreLimit)
    (ValidatorAuditPost fibres fibreLimit)
  · rintro ordinal ⟨hordinal, hchecked⟩
    unfold v5_mask.component_c_runtime.validate_component_c_runtime_later_layer_loop.body
    by_cases hactive : ordinal.val < fibres.val.length
    · have hactiveScalar : ordinal < Slice.len fibres := by
        simp only [Slice.len]
        scalar_tac
      have hnextFits : ordinal.val + 1 < Std.Usize.size := by
        have hsliceMax := fibres.property
        have hUsizeSize : Std.Usize.size = Std.Usize.max + 1 := by
          simp [Std.Usize.size, Std.Usize.max, Std.Usize.numBits]
        rw [hUsizeSize]
        omega
      rw [if_pos hactiveScalar]
      step as ⟨fibre, hfibre⟩
      change fibre = fibres.val[ordinal.val] at hfibre
      by_cases hge : fibre ≥ fibreLimit
      · rw [if_pos hge]
        step*
        simp [ValidatorAuditPost]
      · rw [if_neg hge]
        step as ⟨ordinal1, hordinal1⟩
        have hordinal1Val : ordinal1.val = ordinal.val + 1 := by
          rw [hordinal1, Std.Usize.wrapping_add_val_eq]
          apply Nat.mod_eq_of_lt
          simpa using hnextFits
        constructor
        · constructor
          · rw [hordinal1Val]
            omega
          · intro value hmember
            have hprefix :
                fibres.val.take ordinal.val ++ [fibre] =
                  fibres.val.take (ordinal.val + 1) := by
              calc
                fibres.val.take ordinal.val ++ [fibre] =
                    fibres.val.take ordinal.val ++
                      [fibres.val[ordinal.val]] := by rw [hfibre]
                _ = fibres.val.take (ordinal.val + 1) :=
                  List.take_append_getElem hactive
            rw [hordinal1Val, ← hprefix] at hmember
            simp only [List.mem_append, List.mem_singleton] at hmember
            rcases hmember with hprior | rfl
            · exact hchecked value hprior
            · scalar_tac
        · rw [hordinal1Val]
          omega
    · have hdone : ordinal.val = fibres.val.length := by omega
      have hnotActive : ¬ ordinal < Slice.len fibres := by
        simp only [Slice.len]
        scalar_tac
      rw [if_neg hnotActive]
      unfold ValidatorAuditPost
      intro _hok value hmember
      apply hchecked value
      simpa [hdone] using hmember
  · constructor
    · simp
    · intro value hmember
      simp at hmember

/-- A successful call of the actual extracted validator entails both source
guards: at most 18 entries and every entry below the layer limit. -/
theorem extracted_validator_success_implies_contract
    (fibres : Slice Std.U32) (layer : Std.U8) (fibreLimit : Std.U32)
    (hrun :
      v5_mask.component_c_runtime.validate_component_c_runtime_later_layer
          fibres layer fibreLimit = ok (core.result.Result.Ok ())) :
    fibres.val.length ≤ 18 ∧
      ∀ fibre ∈ fibres.val, fibre.val < fibreLimit.val := by
  unfold v5_mask.component_c_runtime.validate_component_c_runtime_later_layer at hrun
  by_cases htooMany : Slice.len fibres >
      v5_mask.component_c_runtime.V5_COMPONENT_C_RUNTIME_MAX_LATER_COUNT
  · rw [if_pos htooMany] at hrun
    simp at hrun
  · rw [if_neg htooMany] at hrun
    have hcount : fibres.val.length ≤ 18 := by
      simp only [v5_mask.component_c_runtime.V5_COMPONENT_C_RUNTIME_MAX_LATER_COUNT,
        Slice.len] at htooMany
      scalar_tac
    have hspec := extracted_validator_loop_audits_range fibres layer fibreLimit
    obtain ⟨result, hloop, haudit⟩ := Aeneas.Std.WP.spec_imp_exists hspec
    rw [hrun] at hloop
    simp only [ok.injEq] at hloop
    subst result
    exact ⟨hcount, haudit rfl⟩

#print axioms extracted_validator_loop_succeeds
#print axioms extracted_validator_succeeds
#print axioms extracted_validator_loop_audits_range
#print axioms extracted_validator_success_implies_contract

end aspis_prover.ComponentCRuntimeScheduleValidatorProof
