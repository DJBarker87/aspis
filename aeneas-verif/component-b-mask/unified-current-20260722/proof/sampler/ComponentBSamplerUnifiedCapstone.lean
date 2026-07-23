import ComponentBSamplerMaintainedPredicatesBridge
import ComponentBUnifiedTransportFree

open Aeneas Aeneas.Std Result ControlFlow Error

namespace ComponentBSamplerUnifiedCapstone

open ComponentBSamplerMaintainedPredicatesBridge

noncomputable local instance :
    Field ComponentBRealEvaluatorProof.ExactQM31 := by
  change Field AspisV5ComponentCQM31TowerExact.QM31Exact
  infer_instance

/-- Strong source-authentic Component-B chain.  A successful execution of the
real generated generic sampler supplies the canonical and zero-boundary state
invariants internally.  The same generated mask is then passed to the actual
call-through helper, which returns the actual mixed round and actual ten-round
evaluation.  The mixed endpoint is `totalClaim`, and the evaluation is the
maintained terminal covector.  No platform-width, copied-state, field-adapter,
or generic transport premise is exposed. -/
theorem sampled_helper_mixing_and_terminal_covector
    {S : Type} (sourceInst : ComponentBGenerated.v5_mask.Qm31WordSource S)
    (nextWordTotal : ∀ source : S,
      ∃ word source', sourceInst.next_word source = .ok (word, source'))
    (source finalSource : S)
    (mask : ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask)
    (sampleRun :
      ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.sample
          sourceInst source = .ok (.Ok mask, finalSource))
    (selectedRound : Fin 10)
    (totalClaim eta : ComponentBGenerated.aspis_core.field.QM31)
    (real : Array ComponentBGenerated.aspis_core.field.QM31 28#usize)
    (point : Array ComponentBGenerated.aspis_core.field.QM31 10#usize)
    (hpoint : ∀ round : Fin 10,
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 point.val[round.val])
    (htotal : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 totalClaim)
    (heta : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 eta)
    (hreal : ComponentBRealEvaluatorProof.CanonicalArray real) :
    ∃ mixed terminal,
      ComponentBGenerated.v5_sumcheck_mask.v5_sumcheck_mask_mixing_evaluate_correspondence
          mask (ComponentBMaintainedTerminalBridge.roundUsize selectedRound)
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
  obtain ⟨initialCanonical, rounds⟩ :=
    sample_success_supplies_maintained_predicates sourceInst nextWordTotal
      source finalSource mask sampleRun
  have maskIdentity := toMaintainedMask_eq mask
  rw [maskIdentity] at initialCanonical rounds
  exact
    ComponentBUnifiedTransportFree.generated_helper_mixing_and_terminal_covector
      mask selectedRound totalClaim eta real point initialCanonical
      (fun round ↦ (rounds round).1) (fun round ↦ (rounds round).2)
      hpoint htotal heta hreal

#print axioms sampled_helper_mixing_and_terminal_covector

end ComponentBSamplerUnifiedCapstone
