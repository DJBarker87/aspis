import ComponentBSamplerMaintainedPredicatesBridge
import ComponentBMaintainedTerminalCapstone
import ComponentBCurrentFieldEvaluatorCorrespondence

open Aeneas Aeneas.Std Result ControlFlow Error

namespace ComponentBSamplerTerminalCapstone

open ComponentBSamplerMaintainedPredicatesBridge

/- The maintained exact tower instance is intentionally local to each bridge
module.  Reinstall the same certificate for this final composition instead of
relying on an import-side instance leak. -/
noncomputable local instance :
    Field ComponentBRealEvaluatorProof.ExactQM31 := by
  change Field AspisV5ComponentCQM31TowerExact.QM31Exact
  infer_instance

/-- A successful authentic Component-B mask sample, followed by evaluation at
a canonical ten-coordinate point, has a successful authentic extracted result
whose exact value is the maintained terminal covector.  The sampler word-source
totality and the recorded 64-bit extraction target are the only executable
interfaces carried into this composition; the optimized field primitives are
instantiated by the current owning-crate extraction.  No distributional claim
is made. -/
theorem sample_success_evaluates_to_terminal
    {S : Type} (sourceInst : aspis_prover.v5_mask.Qm31WordSource S)
    (nextWordTotal : ∀ source : S,
      ∃ word source', sourceInst.next_word source = .ok (word, source'))
    (source finalSource : S) (mask : SamplerMask)
    (run : aspis_prover.v5_sumcheck_mask.V5SumcheckMask.sample
      sourceInst source = .ok (.Ok mask, finalSource))
    (targetWidth : System.Platform.numBits = 64)
    (point : Array ComponentBMaintainedTerminalBridge.QM31 10#usize)
    (hpoint : ∀ i : Fin 10,
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 point.val[i.val]) :
    ∃ out,
      ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.evaluate
          (toMaintainedMask mask) point = .ok out ∧
        ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 out ∧
        ComponentBRealEvaluatorProof.generatedQm31ToExact out =
          AspisV5SumcheckCommitment.terminalCovector
            (fun i : Fin 10 ↦
              ComponentBRealEvaluatorProof.generatedQm31ToExact point.val[i.val])
            (ComponentBRealEvaluatorProof.generatedQm31ToExact
              (toMaintainedMask mask).initial_claim)
            (fun i ↦ ComponentBMaintainedTerminalBridge.exactTail
              (ComponentBMaintainedTerminalBridge.storedRound
                (toMaintainedMask mask) i)) := by
  obtain ⟨initialCanonical, rounds⟩ :=
    sample_success_supplies_maintained_predicates sourceInst nextWordTotal
      source finalSource mask run
  exact
    ComponentBMaintainedTerminalBridge.generated_public_evaluate_exists_terminal
      (ComponentBRealEvaluatorProof.optimizedPrimitiveCorrespondence_current_field
        targetWidth)
      (toMaintainedMask mask) point initialCanonical
      (fun i ↦ (rounds i).1) (fun i ↦ (rounds i).2) hpoint

#print axioms sample_success_evaluates_to_terminal

end ComponentBSamplerTerminalCapstone
