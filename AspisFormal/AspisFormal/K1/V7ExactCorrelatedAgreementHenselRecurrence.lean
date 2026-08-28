import AspisFormal.K1.V7ExactCorrelatedAgreementPowerSeriesLift
import AspisFormal.K1.V7ExactCorrelatedAgreementHenselCombinatorics

/-!
# Exact fixed-branch Hensel coefficient recurrence

This module joins the shifted-X branch lift to the characteristic-free
coefficient split.  It is kept after both foundational developments in the
import graph, avoiding any circular dependence between power-series lifting
and regular-quotient weight estimates.
-/

set_option autoImplicit false

namespace AspisK1.V7ExactCorrelatedAgreementHenselRecurrence

open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisK1.V7ExactCorrelatedAgreementLocalFactors
open AspisK1.V7ExactCorrelatedAgreementFunctionField
open AspisK1.V7ExactCorrelatedAgreementPowerSeriesLift
open AspisK1.V7ExactCorrelatedAgreementHenselCombinatorics
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The literal coefficient recurrence for the fixed V7 branch lift.  The
multiplier is the derivative of the selected global irreducible branch at
the selected local irreducible root; it is not a derivative of the original
interpolant and not a specialization-dependent factor. -/
theorem exactV7_fixedBranch_coefficient_recurrence
    (globalFactor : TrivariatePolynomial QM31Exact)
    (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (root : PowerSeries (LocalBranchField localFactor))
    (rootEquation :
      (liftedGlobalFactor globalFactor x₀ localFactor).IsRoot root)
    (rootConstant : PowerSeries.constantCoeff root =
      AdjoinRoot.root (localFactorOverRational localFactor))
    (order : Nat) (orderPositive : 0 < order) :
    ((((specializeEvaluationPoint x₀ globalFactor).derivative).map
        (algebraMap (Polynomial QM31Exact)
          (ChallengeRationalField QM31Exact))).map
      (AdjoinRoot.of (localFactorOverRational localFactor))).eval
        (AdjoinRoot.root (localFactorOverRational localFactor)) *
      PowerSeries.coeff order root =
        -nonlinearEvaluationCoefficient
          (liftedGlobalFactor globalFactor x₀ localFactor) root order := by
  have recurrence := derivative_mul_coeff_eq_neg_nonlinear_of_isRoot
    (liftedGlobalFactor globalFactor x₀ localFactor) root rootEquation order
      orderPositive
  rw [rootConstant,
    constantCoeff_liftedGlobalFactor_derivative_eval_C] at recurrence
  exact recurrence

#print axioms exactV7_fixedBranch_coefficient_recurrence

end

end AspisK1.V7ExactCorrelatedAgreementHenselRecurrence
