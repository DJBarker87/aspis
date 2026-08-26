import AspisFormal.V6Width29ConstrainedFunctionalExtraction
import AspisFormal.V6PublishedTheoremInterfaces
import AspisFormal.Pool.V7AcceptedSemanticRelationComposition
import AspisFormal.Pool.V7C1ConcreteProjectionBinding

/-!
# Restoration-wide correlated extraction of the 87 point claims

The locally selected width-29 tuple may depend on `gamma`, so the three
degree-28 root counts in `V7PointClaimBatchBinding` cannot be promoted to a
ROM probability statement without an additional consistency argument.  This
module supplies that argument at the correct, restoration-wide level.

If more than the published correlated-decoding cap of gamma responses are
both close and consistent with all three serialized point-claim rows, then
one fixed twenty-nine-message tuple realizes every one of the 87 claims.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000

namespace AspisPool.V7CorrelatedPointClaimExtraction

open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedSemanticRelationComposition
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7CombinedCandidateExact
open AspisPool.V7StatementPointCompatibility
open AspisPool.V7Width29ComponentExtraction
open AspisV5ComponentADeployedTerminalApplicability
open AspisV5ComponentCQM31TowerExact
open AspisV6OneFoldCandidateExtraction
open AspisV6AcceptedPathObligations
open AspisV6PublishedTheoremInterfaces
open AspisV6Width29ConstrainedFunctionalExtraction
open AspisV6Width29CorrelatedAgreement

/-- The three exact statement-point MLE functionals. -/
noncomputable def pointFunctional (point : Fin 10 → QM31Exact) :
    Fin 3 → InitialMessage QM31Exact → QM31Exact :=
  fun row message => multilinearEvalValue (statementPoint point row) message

/-- Functional batching is literal coefficient-level linearity. -/
theorem pointFunctional_batchInitialMessages
    (point : Fin 10 → QM31Exact) (row : Fin 3)
    (components : Width29InitialMessages QM31Exact) (gamma : QM31Exact) :
    pointFunctional point row (batchInitialMessages components gamma) =
      width29Batch
        (fun lane => pointFunctional point row (components lane)) gamma := by
  exact multilinearEvalValue_batchInitialMessages components gamma
    (statementPoint point row)

/-- Injectivity of the exact log-20 mathematical encoder, obtained from its
proved 1024-position overlap cap. -/
theorem exactInitialEncoder_injective :
    Function.Injective exactInitialEncoder := by
  classical
  intro left right encodedEqual
  by_contra different
  have overlap := exactInitialEncoder_overlap_cap left right different
  have full :
      agreementCount (exactInitialEncoder left)
          (exactInitialEncoder right) = 1048576 := by
    rw [encodedEqual]
    simp [agreementCount]
  omega

/-- More than the published adaptive gamma cap fixes all 87 claims to one
component tuple.  The tuple is outside the sampled-gamma quantifier. -/
theorem many_constrained_gamma_responses_fix_all_point_claims
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    (lanes : Fin 29 → Fin 1048576 → QM31Exact)
    (point : Fin 10 → QM31Exact)
    (claims : Fin 3 → Fin 29 → QM31Exact)
    (strategy : Width29ProximateStrategy QM31Exact (Fin 1048576)
      (InitialMessage QM31Exact))
    (many : initialBatchChallengeCap <
      (width29GoodChallenges exactInitialEncoder
        AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
        lanes
        (constrainedWidth29Strategy (pointFunctional point) claims
          strategy)).card) :
    ∃ components : Width29InitialMessages QM31Exact,
      ∀ row lane,
        claims row lane =
          multilinearEvalValue (statementPoint point row)
            (components lane) := by
  obtain ⟨components, exactClaims⟩ :=
    constrained_width29_many_responses_fix_all_functionals
      exactInitialEncoder
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
      initialBatchChallengeCap
      published lanes (pointFunctional point) claims strategy
      batchInitialMessages exactInitialEncoder_injective
      exactInitialEncoder_batchInitialMessages
      (pointFunctional_batchInitialMessages point)
      (by simp) many
  refine ⟨components, ?_⟩
  intro row lane
  exact congrFun (exactClaims row) lane

/-- Retain one restored good gamma whose response is jointly close to the same
fixed point-compatible tuple.  This is the direct input needed to construct
the strengthened K1.4 certificate. -/
theorem many_constrained_gamma_responses_extract_point_compatible_components
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    (lanes : Fin 29 → Fin 1048576 → QM31Exact)
    (point : Fin 10 → QM31Exact)
    (claims : Fin 3 → Fin 29 → QM31Exact)
    (strategy : Width29ProximateStrategy QM31Exact (Fin 1048576)
      (InitialMessage QM31Exact))
    (many : initialBatchChallengeCap <
      (width29GoodChallenges exactInitialEncoder
        AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
        lanes
        (constrainedWidth29Strategy (pointFunctional point) claims
          strategy)).card) :
    ∃ (components : Width29InitialMessages QM31Exact) (gamma : QM31Exact),
      gamma ∈ width29GoodChallenges exactInitialEncoder
        AspisV6PublishedTheoremInterfaces.initialAgreementThreshold lanes
        (constrainedWidth29Strategy (pointFunctional point) claims strategy) ∧
      Width29ValidResponse exactInitialEncoder
        AspisV6PublishedTheoremInterfaces.initialAgreementThreshold lanes
        strategy gamma ∧
      Width29CandidateOnCurve exactInitialEncoder strategy components gamma ∧
      strategy.support gamma ⊆
        width29JointAgreementSet exactInitialEncoder lanes components ∧
      ∀ row, claims row = fun lane =>
        multilinearEvalValue (statementPoint point row)
          (components lane) := by
  simpa only [pointFunctional] using
    (constrained_width29_many_responses_extract_fixed_components
      exactInitialEncoder
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
      initialBatchChallengeCap published lanes (pointFunctional point) claims
      strategy batchInitialMessages exactInitialEncoder_injective
      exactInitialEncoder_batchInitialMessages
      (pointFunctional_batchInitialMessages point) (by simp) many)

#print axioms pointFunctional_batchInitialMessages
#print axioms exactInitialEncoder_injective
#print axioms many_constrained_gamma_responses_fix_all_point_claims
#print axioms
  many_constrained_gamma_responses_extract_point_compatible_components

end AspisPool.V7CorrelatedPointClaimExtraction
