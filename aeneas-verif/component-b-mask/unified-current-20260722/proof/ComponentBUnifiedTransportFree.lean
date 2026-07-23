import ComponentBGeneratedBoundaryBridge
import ComponentBMaintainedTerminalCapstone

open Aeneas Aeneas.Std Result ControlFlow Error
open scoped BigOperators

namespace ComponentBUnifiedTransportFree

abbrev Mask := ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask

noncomputable local instance : Field ComponentBRealEvaluatorProof.ExactQM31 := by
  change Field AspisV5ComponentCQM31TowerExact.QM31Exact
  infer_instance

private theorem terminalCanonicalIffMixingCanonical (value : QM31) :
    ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 value ↔
      ComponentBGenerated.MultilinearEvalProofs.GeneratedCanonicalQM31 value := by
  simp [ComponentBRealEvaluatorProof.GeneratedCanonicalQM31,
    ComponentBRealEvaluatorProof.GeneratedCanonicalCM31,
    ComponentBGenerated.MultilinearEvalProofs.GeneratedCanonicalQM31,
    ComponentBGenerated.MultilinearEvalProofs.GeneratedCanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus]

private theorem selectedStoredEq
    (mask : Mask) (round : Fin 10) :
    ComponentBGenerated.v5_sumcheck_mask.roundStored mask
        (ComponentBMaintainedTerminalBridge.roundUsize round)
        (by simpa using round.isLt) =
      ComponentBMaintainedTerminalBridge.storedRound mask round := by
  rfl

/-- Transport-free Component-B correspondence in one source-authentic
generated universe.  The private extraction helper calls the actual production
mixed-round wrapper and actual production ten-round evaluator.  Generated
zero-boundary executions are converted internally to the exact invariant used
by the maintained terminal-covector theorem; no field-adapter, state-copy, or
"faithfulness" premise is accepted from the caller. -/
theorem generated_helper_mixing_and_terminal_covector
    (mask : Mask) (selectedRound : Fin 10)
    (totalClaim eta : QM31) (real : Polynomial)
    (point : Array QM31 10#usize)
    (hinitial : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31
      mask.initial_claim)
    (hstored : ∀ round : Fin 10,
      ComponentBRealEvaluatorProof.CanonicalArray
        (ComponentBMaintainedTerminalBridge.storedRound mask round))
    (hzero : ∀ round : Fin 10,
      ComponentBMaintainedTerminalBridge.ExactZeroBoundary
        (ComponentBMaintainedTerminalBridge.storedRound mask round))
    (hpoint : ∀ round : Fin 10,
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 point.val[round.val])
    (htotal : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 totalClaim)
    (heta : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 eta)
    (hreal : ComponentBRealEvaluatorProof.CanonicalArray real) :
    ∃ mixed terminal,
      ComponentBGenerated.v5_sumcheck_mask.v5_sumcheck_mask_mixing_evaluate_correspondence
          mask
          (ComponentBMaintainedTerminalBridge.roundUsize selectedRound)
          totalClaim eta real point = .ok (.some mixed, terminal) ∧
      ComponentBGenerated.aspis_core.state_only_sumcheck.state_only_boundary_sum
          mixed = .ok totalClaim ∧
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 terminal ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact terminal =
        AspisV5SumcheckCommitment.terminalCovector
          (fun round : Fin 10 ↦
            ComponentBRealEvaluatorProof.generatedQm31ToExact
              point.val[round.val])
          (ComponentBRealEvaluatorProof.generatedQm31ToExact mask.initial_claim)
          (fun round ↦ ComponentBMaintainedTerminalBridge.exactTail
            (ComponentBMaintainedTerminalBridge.storedRound mask round)) := by
  let roundScalar :=
    ComponentBMaintainedTerminalBridge.roundUsize selectedRound
  have roundInRange : roundScalar.val < 10 := by
    simpa [roundScalar] using selectedRound.isLt
  have selectedEq :
      ComponentBGenerated.v5_sumcheck_mask.roundStored mask roundScalar
          roundInRange =
        ComponentBMaintainedTerminalBridge.storedRound mask selectedRound := by
    simpa [roundScalar] using selectedStoredEq mask selectedRound
  have totalCanonical :
      ComponentBGenerated.MultilinearEvalProofs.GeneratedCanonicalQM31
        totalClaim :=
    (terminalCanonicalIffMixingCanonical totalClaim).mp htotal
  have etaCanonical :
      ComponentBGenerated.MultilinearEvalProofs.GeneratedCanonicalQM31 eta :=
    (terminalCanonicalIffMixingCanonical eta).mp heta
  have realCanonical : ∀ coefficient : Fin 28,
      ComponentBGenerated.MultilinearEvalProofs.GeneratedCanonicalQM31
        real.val[coefficient.val] := by
    intro coefficient
    exact (terminalCanonicalIffMixingCanonical _).mp (hreal coefficient)
  have selectedCanonical : ∀ coefficient : Fin 28,
      ComponentBGenerated.MultilinearEvalProofs.GeneratedCanonicalQM31
        (ComponentBGenerated.v5_sumcheck_mask.roundStored mask roundScalar
          roundInRange).val[coefficient.val] := by
    intro coefficient
    rw [selectedEq]
    exact (terminalCanonicalIffMixingCanonical _).mp
      (hstored selectedRound coefficient)
  have selectedZero :
      ComponentBGenerated.aspis_core.state_only_sumcheck.state_only_boundary_sum
          (ComponentBGenerated.v5_sumcheck_mask.roundStored mask roundScalar
            roundInRange) =
        .ok ComponentBGenerated.v5_sumcheck_mask.extractedQM31Zero := by
    rw [selectedEq]
    exact exact_zero_boundary_implies_generated _ selectedCanonical
      (hzero selectedRound)
  obtain ⟨mixed, mixedCall, mixedBoundary⟩ :=
    ComponentBGenerated.v5_sumcheck_mask.generated_mixed_round_polynomial_endpoint
      mask roundScalar totalClaim eta real roundInRange totalCanonical
      etaCanonical realCanonical selectedCanonical selectedZero
  obtain ⟨terminal, evaluateCall, terminalCanonical, terminalExact⟩ :=
    ComponentBMaintainedTerminalBridge.generated_public_evaluate_exists_terminal_current_field
      mask point hinitial hstored hzero hpoint
  refine ⟨mixed, terminal, ?_, mixedBoundary, terminalCanonical, terminalExact⟩
  unfold ComponentBGenerated.v5_sumcheck_mask.v5_sumcheck_mask_mixing_evaluate_correspondence
  rw [mixedCall]
  simp only [bind_tc_ok]
  rw [evaluateCall]
  rfl

#print axioms generated_helper_mixing_and_terminal_covector

end ComponentBUnifiedTransportFree
