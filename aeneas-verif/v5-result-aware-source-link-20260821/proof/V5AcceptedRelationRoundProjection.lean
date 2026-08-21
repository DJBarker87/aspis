import V5RelationGeneratedKernelProjection

/-!
# Exact projection of one accepted production relation round

This file isolates the scalar part of one successful round of the translated
production relation verifier.  It records the two multiply/add updates, the
boundary call, and the polynomial evaluation call made by that execution.
The main theorem proves that those calls are exactly one successful step of
the maintained field-level relation model.
-/

namespace AspisV5AcceptedRelationRoundProjection

open Aeneas Aeneas.Std Result
open AspisV5RelationGeneratedFieldProjection
open AspisV5RelationGeneratedKernelProjection
open AspisV5RelationStressSourceBridge
open AspisV5RelationSumcheckSoundness

set_option autoImplicit false

abbrev RawQM31 := V5RelationFullGenerated.aspis_core.field.QM31
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

def toField (value : RawQM31) : ExactQM31 :=
  AspisV5RelationGeneratedFieldProjection.toMaintainedExact value

/-- The exact scalar calls retained from one successful production round.
The weight-accumulator calls are intentionally absent: they do not affect the
round's running-claim recurrence and are connected separately at the final
dot. -/
structure AcceptedRawRoundArithmetic : Type where
  incoming : RawQM31
  firstValue : RawQM31
  secondValue : RawQM31
  firstMix : RawQM31
  secondMix : RawQM31
  firstProduct : RawQM31
  claimAfterFirst : RawQM31
  secondProduct : RawQM31
  claimAfterSecond : RawQM31
  polynomial : Array RawQM31 7#usize
  alpha : RawQM31
  outgoing : RawQM31
  incomingCanonical : CanonicalQM31 incoming
  firstValueCanonical : CanonicalQM31 firstValue
  secondValueCanonical : CanonicalQM31 secondValue
  firstMixCanonical : CanonicalQM31 firstMix
  secondMixCanonical : CanonicalQM31 secondMix
  polynomialCanonical : CanonicalArray polynomial
  alphaCanonical : CanonicalQM31 alpha
  firstProductRun :
    V5RelationFullGenerated.aspis_core.field.QM31.mul
      firstMix firstValue = .ok firstProduct
  firstClaimRun :
    V5RelationFullGenerated.aspis_core.field.QM31.add
      incoming firstProduct = .ok claimAfterFirst
  secondProductRun :
    V5RelationFullGenerated.aspis_core.field.QM31.mul
      secondMix secondValue = .ok secondProduct
  secondClaimRun :
    V5RelationFullGenerated.aspis_core.field.QM31.add
      claimAfterFirst secondProduct = .ok claimAfterSecond
  boundaryRun :
    V5RelationFullGenerated.aspis_core.sumcheck.boundary_sum polynomial =
      .ok claimAfterSecond
  evaluateRun :
    V5RelationFullGenerated.aspis_core.sumcheck.evaluate polynomial alpha =
      .ok outgoing

/-- The maintained relation round represented by the exact values consumed
by the production calls above. -/
def projectedRound (trace : AcceptedRawRoundArithmetic) :
    SourceRelationRound ExactQM31 where
  firstValue := toField trace.firstValue
  secondValue := toField trace.secondValue
  firstMix := toField trace.firstMix
  secondMix := toField trace.secondMix
  polynomial := exactCoefficients trace.polynomial
  alpha := toField trace.alpha

/-- The two successful generated multiply/add updates are exactly the
maintained running-claim update. -/
theorem accepted_raw_round_claim_after_mixes
    (trace : AcceptedRawRoundArithmetic) :
    toField trace.claimAfterSecond =
      sourceClaimAfterMixes (toField trace.incoming)
        (projectedRound trace) := by
  have firstProduct := generated_qm31_mul_run_corresponds
    trace.firstMix trace.firstValue trace.firstProduct
    trace.firstMixCanonical trace.firstValueCanonical trace.firstProductRun
  have firstClaim := generated_qm31_add_run_corresponds
    trace.incoming trace.firstProduct trace.claimAfterFirst
    trace.incomingCanonical firstProduct.1 trace.firstClaimRun
  have secondProduct := generated_qm31_mul_run_corresponds
    trace.secondMix trace.secondValue trace.secondProduct
    trace.secondMixCanonical trace.secondValueCanonical trace.secondProductRun
  have secondClaim := generated_qm31_add_run_corresponds
    trace.claimAfterFirst trace.secondProduct trace.claimAfterSecond
    firstClaim.1 secondProduct.1 trace.secondClaimRun
  change
    AspisV5RelationGeneratedFieldProjection.toExact trace.claimAfterSecond = _
  rw [secondClaim.2, firstClaim.2, firstProduct.2, secondProduct.2]
  rfl

/-- A successful generated boundary call is the exact maintained arity-four
boundary for the projected polynomial. -/
theorem accepted_raw_round_boundary
    (trace : AcceptedRawRoundArithmetic) :
    relationBoundary (projectedRound trace).polynomial =
      toField trace.claimAfterSecond := by
  have boundary := generated_boundary_success_exact trace.polynomial
    trace.claimAfterSecond trace.polynomialCanonical trace.boundaryRun
  exact boundary.2.symm

/-- The generated evaluator's returned value is the maintained polynomial
evaluation at the exact accepted alpha. -/
theorem accepted_raw_round_evaluation
    (trace : AcceptedRawRoundArithmetic) :
    (relationPolynomial (projectedRound trace).polynomial).eval
        (projectedRound trace).alpha =
      toField trace.outgoing := by
  have evaluated := generated_evaluate_success_relationPolynomial
    trace.polynomial trace.alpha trace.outgoing trace.polynomialCanonical
    trace.alphaCanonical trace.evaluateRun
  exact evaluated.2.symm

/-- The value returned by an accepted round is itself canonical. -/
theorem accepted_raw_round_outgoing_canonical
    (trace : AcceptedRawRoundArithmetic) :
    CanonicalQM31 trace.outgoing := by
  exact (generated_evaluate_success_relationPolynomial trace.polynomial
    trace.alpha trace.outgoing trace.polynomialCanonical
    trace.alphaCanonical trace.evaluateRun).1

/-- One accepted production scalar trace therefore executes one successful
round of the maintained source model. -/
theorem accepted_raw_round_runs_source_round
    (trace : AcceptedRawRoundArithmetic) :
    runSourceRelationRound (toField trace.incoming)
        (projectedRound trace) = some (toField trace.outgoing) := by
  have boundary :
      relationBoundary (projectedRound trace).polynomial =
        sourceClaimAfterMixes (toField trace.incoming)
          (projectedRound trace) := by
    rw [accepted_raw_round_boundary trace,
      accepted_raw_round_claim_after_mixes trace]
  simp [runSourceRelationRound, boundary,
    accepted_raw_round_evaluation trace]

#print axioms accepted_raw_round_claim_after_mixes
#print axioms accepted_raw_round_boundary
#print axioms accepted_raw_round_evaluation
#print axioms accepted_raw_round_outgoing_canonical
#print axioms accepted_raw_round_runs_source_round

end AspisV5AcceptedRelationRoundProjection
