import AspisFormal.K1.V7Tag73OperationalRelationSourceFacts
import AspisFormal.K1.V7Tag73JointQueryBatchSoundness

/-!
# Honest source handoff for the Tag-73 rho-batched query check

The deployed Tag-73 verifier does not compare sixteen one-fold answers with
sixteen `final256` evaluations separately.  Its authenticated callback returns
the sixteen folded answers, and `add_v7_final256_query_batch_shifted` installs
the single claim `sum_i rho^(i+1) * authenticated_i` together with the
corresponding `final256` evaluation covector.  Pointwise equality is not a
deterministic source consequence; the joint degree-at-most-sixteen event owns
that soundness step.

This file records that literal source shape.  In particular, the source-facing
record below does not contain `QueryInjectionExact`, pointwise
`QueryConsistent`, or `IdealAccepts`.  The final theorem derives the former
only from an explicit shifted-claim equality supplied by the joint discrepancy
proof.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73BatchedQuerySourceBridge

open AspisK1.V7Tag73OperationalRelationSourceFacts
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisPool.V7RelationCandidateBinding
open AspisV5ComponentCQM31TowerExact
open AspisV5FriRelationCandidateBridge
open AspisV6AcceptedPathObligations
open AspisV6QueryBatchSoundness
open AspisK1.V7Tag73JointQueryBatchSoundness

noncomputable section

/-- Exact shifted Tag-73 covector.  It is `rho` times the frozen V6 covector,
matching the source helper's initial scale `rho`. -/
def exactShiftedQueryBatchWeights
    (queries : Fin 16 → Fin 262144) (rho : QM31Exact) :
    Fin 256 → QM31Exact :=
  fun coefficient => rho * exactQueryBatchWeights queries rho coefficient

/-- Exact shifted authenticated scalar installed by Tag-73. -/
def shiftedQueryBatchClaim
    (values : Fin 16 → QM31Exact) (rho : QM31Exact) : QM31Exact :=
  rho * queryBatchClaim values rho

theorem exactShiftedQueryBatchWeights_eq_sum
    (queries : Fin 16 → Fin 262144) (rho : QM31Exact)
    (coefficient : Fin 256) :
    exactShiftedQueryBatchWeights queries rho coefficient =
      ∑ ordinal : Fin 16,
        rho ^ (ordinal.val + 1) *
          exactFinalQueryWeight (queries ordinal) coefficient := by
  classical
  unfold exactShiftedQueryBatchWeights exactQueryBatchWeights
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ordinal _
  rw [pow_succ]
  ring

theorem shiftedQueryBatchClaim_eq_sum
    (values : Fin 16 → QM31Exact) (rho : QM31Exact) :
    shiftedQueryBatchClaim values rho =
      ∑ ordinal : Fin 16, rho ^ (ordinal.val + 1) * values ordinal := by
  classical
  unfold shiftedQueryBatchClaim queryBatchClaim
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ordinal _
  rw [pow_succ]
  ring

/-- The difference between the two shifted scalar claims is exactly the
shifted residual used by the repaired joint K1.3 event. -/
theorem shifted_claim_difference_eq_shifted_residual
    (expected authenticated : Fin 16 → QM31Exact) (rho : QM31Exact) :
    shiftedQueryBatchClaim expected rho -
        shiftedQueryBatchClaim authenticated rho =
      shiftedQueryBatchResidual expected authenticated rho := by
  classical
  unfold shiftedQueryBatchClaim shiftedQueryBatchResidual queryBatchClaim
  rw [← mul_sub]
  apply congrArg (fun value : QM31Exact => rho * value)
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ordinal _
  ring

theorem candidateClaim_exactShiftedQueryBatchWeights
    (queries : Fin 16 → Fin 262144) (rho : QM31Exact)
    (coefficients : Fin 256 → QM31Exact) :
    candidateClaim (exactShiftedQueryBatchWeights queries rho) coefficients =
      shiftedQueryBatchClaim
        (fun ordinal => exactFinalEncoder coefficients (queries ordinal)) rho := by
  calc
    candidateClaim (exactShiftedQueryBatchWeights queries rho) coefficients =
        rho * candidateClaim (exactQueryBatchWeights queries rho)
          coefficients := by
      classical
      unfold candidateClaim exactShiftedQueryBatchWeights
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro coefficient _
      ring
    _ = rho * queryBatchClaim
        (fun ordinal => exactFinalEncoder coefficients (queries ordinal))
          rho := congrArg (fun value => rho * value)
        (candidateClaim_exactQueryBatchWeights queries rho coefficients)
    _ = shiftedQueryBatchClaim
        (fun ordinal => exactFinalEncoder coefficients (queries ordinal))
          rho := rfl

/-- Literal data equalities exposed by the successful query-batch source
path.  `authenticated` is the array returned by the Merkle/authentication and
circle-fold callback.  The source installs that array's rho-weighted claim;
it does not install the claim of the disclosed final polynomial directly. -/
structure ExactAuthenticatedQueryBatchSourceBinding
    (execution : CandidateExecution QM31Exact)
    (queries : Fin 16 → Fin 262144) (rho : QM31Exact)
    (authenticated : Fin 16 → QM31Exact) : Prop where
  queryWeightsExact :
    execution.queryWeights = exactShiftedQueryBatchWeights queries rho
  queryClaimExact :
    execution.queryClaim = shiftedQueryBatchClaim authenticated rho

/-- The exact scalar carried immediately before the source's shifted query
injection.  Naming it separately matches the corrected K1.3 obligation and
keeps it independent of the authenticated query values. -/
def preQueryDiscrepancy (execution : CandidateExecution QM31Exact) :
    QM31Exact :=
  execution.claimAfterRound0 -
    candidateClaim execution.foldedOodWeights256 execution.disclosedFinal256

/-- The literal shifted weight/claim insertion gives exactly the repaired
joint discrepancy at `before 1`.  This is the source-facing equality needed
by K1.3: it neither assumes nor concludes that the discrepancy is zero. -/
theorem before_one_eq_joint_discrepancy_of_authenticated_source
    {execution : CandidateExecution QM31Exact}
    {queries : Fin 16 → Fin 262144} {rho : QM31Exact}
    {authenticated : Fin 16 → QM31Exact}
    (source : ExactAuthenticatedQueryBatchSourceBinding execution queries rho
      authenticated) :
    execution.discrepancyTrace.before 1 =
      jointQueryBatchDiscrepancy (preQueryDiscrepancy execution)
        (fun ordinal =>
          exactFinalEncoder execution.disclosedFinal256 (queries ordinal))
        authenticated rho := by
  classical
  change execution.claim1 -
      candidateClaim execution.weights1 execution.disclosedFinal256 = _
  unfold CandidateExecution.claim1 CandidateExecution.weights1
  rw [source.queryWeightsExact, source.queryClaimExact]
  rw [CandidateExecution.candidateClaim_add_weights]
  rw [candidateClaim_exactShiftedQueryBatchWeights]
  unfold preQueryDiscrepancy jointQueryBatchDiscrepancy
  rw [← shifted_claim_difference_eq_shifted_residual]
  ring

/-- The downstream handoff consumes an explicit equality of the two shifted
claims. Source execution itself does not manufacture this equality. -/
theorem equal_shifted_claims_of_explicit_equality
    (expected authenticated : Fin 16 → QM31Exact) (rho : QM31Exact)
    (claimsEqual : shiftedQueryBatchClaim expected rho =
      shiftedQueryBatchClaim authenticated rho) :
    shiftedQueryBatchClaim expected rho =
      shiftedQueryBatchClaim authenticated rho :=
  claimsEqual

/-- The existing K1.5 `QueryInjectionExact` fact is obtained from the literal
authenticated source output only after the joint proof supplies equality of
the shifted expected and authenticated claims. This is deliberately not a
source-record field. -/
theorem query_injection_exact_of_authenticated_source_and_explicit_claim_equality
    {execution : CandidateExecution QM31Exact}
    {queries : Fin 16 → Fin 262144} {rho : QM31Exact}
    {authenticated : Fin 16 → QM31Exact}
    (source : ExactAuthenticatedQueryBatchSourceBinding execution queries rho
      authenticated)
    (shiftedClaimsEqual :
      shiftedQueryBatchClaim
          (fun ordinal =>
            exactFinalEncoder execution.disclosedFinal256 (queries ordinal))
          rho = shiftedQueryBatchClaim authenticated rho) :
    execution.QueryInjectionExact := by
  unfold CandidateExecution.QueryInjectionExact
  rw [source.queryWeightsExact, candidateClaim_exactShiftedQueryBatchWeights,
    source.queryClaimExact]
  exact shiftedClaimsEqual.symm

/-- A pointwise-equal callback is one sufficient way to obtain the residual
premise, but the deployed verifier does not establish this deterministically;
the theorem is retained only as an algebraic sanity check. -/
theorem shifted_claims_equal_of_authenticated_values_exact
    (expected authenticated : Fin 16 → QM31Exact) (rho : QM31Exact)
    (exactValues : authenticated = expected) :
    shiftedQueryBatchClaim expected rho =
      shiftedQueryBatchClaim authenticated rho := by
  subst authenticated
  rfl

#print axioms candidateClaim_exactShiftedQueryBatchWeights
#print axioms exactShiftedQueryBatchWeights_eq_sum
#print axioms shiftedQueryBatchClaim_eq_sum
#print axioms shifted_claim_difference_eq_shifted_residual
#print axioms before_one_eq_joint_discrepancy_of_authenticated_source
#print axioms equal_shifted_claims_of_explicit_equality
#print axioms query_injection_exact_of_authenticated_source_and_explicit_claim_equality
#print axioms shifted_claims_equal_of_authenticated_values_exact

end

end AspisK1.V7Tag73BatchedQuerySourceBridge
