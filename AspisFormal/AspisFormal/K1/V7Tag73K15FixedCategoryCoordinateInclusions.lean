import AspisFormal.K1.V7Tag73K15FixedActualLawAdapters

/-!
# Deterministic coordinate inclusions for six fixed Tag-73 K1.5 families

This file is the proposition-level end of the actual-law routing obligation.
It adds the four one-ordinary-call membership endpoints needed after an
executable compiler router has identified the literal returned sampler value.
The other two already-adapted categories retain their existing exact endpoints:
`oodMixCancellation_has_exact_pair_set` and
`kappaPointRowCollision_has_exact_two_root_set`.

There is deliberately no coordinate equivalence, source equality, event cover,
or probability statement among the hypotheses below.  The still-required
operational routers must prove that their isolated values are the literal
challenges appearing in these predicates; these lemmas then discharge the
remaining deterministic membership step without any quantifier exchange.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73K15FixedCategoryCoordinateInclusions

open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73K15FixedActualLawAdapters
open AspisK1.V7Tag73K15FixedSamplerProbabilityAdapters
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7DeployedCopyEvaluatorBalanceBridge
open AspisPool.V7DeployedCopyLogUpAliasClosure
open AspisPool.V7FixedC1CopyCollisionSecurity
open AspisPool.V7FixedWidth29TupleList
open AspisPool.V7K15FixedFamilyCausalCover
open AspisPool.V7K15IndependentRootCertificates
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-! ## One ordinary challenge -/

/-- A fixed-C1 lambda failure is in the exact target selected by the complete
ordinary sampler nuisance coordinate. -/
theorem copy_lambda_failure_mem_complete_ordinary_target
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : C1InitialWords)
    (sample : SuccessfulTag73DuplexOrdinaryAttempt)
    (failure : ∃ candidate : FixedC1TupleCandidate decoder lanes,
      CopyTupleCompressionCollision
        (fixedC1CopySourceFamily decoder lanes candidate).registry
        (successfulDuplexOrdinaryValue sample)) :
    sample ∈ fixedOrdinarySamplerTargetEvent (fun _ ↦
      familyLambdaBad (fixedC1CopySourceFamily decoder lanes)) := by
  exact copy_lambda_category_mem_fixed_family_target decoder lanes
    (successfulDuplexOrdinaryValue sample) failure

/-- A fixed-C1 pole or rational chi failure is in the exact conditional target
selected before the isolated chi value. -/
theorem copy_chi_failure_mem_complete_ordinary_target
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : C1InitialWords) (lambda : QM31Exact)
    (sample : SuccessfulTag73DuplexOrdinaryAttempt)
    (failure : ∃ candidate : FixedC1TupleCandidate decoder lanes,
      DeployedCopyActivePole
          (fixedC1CopySourceFamily decoder lanes candidate).registry
          lambda (successfulDuplexOrdinaryValue sample) ∨
        CopyChiCollision
          (fixedC1CopySourceFamily decoder lanes candidate).registry
          lambda (successfulDuplexOrdinaryValue sample)) :
    sample ∈ fixedOrdinarySamplerTargetEvent (fun _ ↦
      familyChiBad (fixedC1CopySourceFamily decoder lanes) lambda) := by
  exact packedSourceFamilyChiWitness_mem_familyChiBad
    (fixedC1CopySourceFamily decoder lanes)
    lambda (successfulDuplexOrdinaryValue sample) failure

/-- The literal `mu = 0` failure is membership in the singleton target of the
complete ordinary sampler. -/
theorem mu_zero_failure_mem_complete_ordinary_target
    (sample : SuccessfulTag73DuplexOrdinaryAttempt)
    (failure : successfulDuplexOrdinaryValue sample = 0) :
    sample ∈ fixedOrdinarySamplerTargetEvent (fun _ ↦ zeroChallengeSet) := by
  exact muZero_mem_zeroChallengeSet failure

/-- The deployed inactive-slot collision is the same singleton-zero target for
the isolated chi sampler. -/
theorem inactive_chi_failure_mem_complete_ordinary_target
    (sample : SuccessfulTag73DuplexOrdinaryAttempt)
    (failure : DeployedCopyInactiveSlotCollision
      (successfulDuplexOrdinaryValue sample)) :
    sample ∈ fixedOrdinarySamplerTargetEvent (fun _ ↦ zeroChallengeSet) := by
  exact inactiveChi_mem_zeroChallengeSet failure

#print axioms copy_lambda_failure_mem_complete_ordinary_target
#print axioms copy_chi_failure_mem_complete_ordinary_target
#print axioms mu_zero_failure_mem_complete_ordinary_target
#print axioms inactive_chi_failure_mem_complete_ordinary_target

end

end AspisK1.V7Tag73K15FixedCategoryCoordinateInclusions
