import AspisFormal.K1.V7ExactCorrelatedAgreementInitialCurveBranch

/-!
# Exact initial V7 fixed-curve extraction
-/

set_option autoImplicit false
set_option maxRecDepth 262144

namespace AspisK1.V7ExactCorrelatedAgreementTerminal

open Polynomial
open AspisK1.V7ExactCorrelatedAgreement
open AspisK1.V7ExactCorrelatedAgreementInterpolation
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementLocalFactors
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisK1.V7ExactCorrelatedAgreementFunctionField
open AspisK1.V7ExactCorrelatedAgreementPowerSeriesLift
open AspisK1.V7ExactCorrelatedAgreementRegularHensel
open AspisK1.V7ExactCorrelatedAgreementFactorBudgets
open AspisK1.V7ExactCorrelatedAgreementConcreteBranch
open AspisK1.V7ExactCorrelatedAgreementOuterSelection
open AspisK1.V7Tag73ExactGRSConversion
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV6Width29CorrelatedAgreement
open AspisV6PublishedTheoremInterfaces
open AspisV5ComponentCQM31TowerExact

noncomputable section

private theorem exists_four_elim
    {A B C D : Type*} {P : A → B → C → D → Prop} {Q : Prop}
    (existsWitness : ∃ a b c d, P a b c d)
    (finish : ∀ a b c d, P a b c d → Q) : Q := by
  obtain ⟨a, b, c, d, property⟩ := existsWitness
  exact finish a b c d property

set_option maxRecDepth 1048576 in
set_option maxHeartbeats 300000 in
set_option linter.constructorNameAsVariable false in
/-- Extract a released-message curve from one fixed exact symbolic
interpolant and an explicitly supplied set of valid challenges. -/
theorem exists_exactV7Initial_curve_of_interpolant
    (lanes : Fin 29 → InitialWord QM31Exact)
    (strategy : Width29ProximateStrategy QM31Exact (Fin 1048576)
      (InitialMessage QM31Exact))
    (coefficients :
      CurveMonomialIndex 1024 28 initialCurveXBound initialCurveYRows
        initialCurveZBound → QM31Exact)
    (coefficientsNeZero : coefficients ≠ 0)
    (kernel : curveInterpolationMap exactInitialGRSConversion.points
      (exactInitialNormalizedLanes lanes) coefficients = 0)
    (challenges : Finset QM31Exact)
    (validOn : ∀ gamma ∈ challenges,
      Width29ValidResponse exactInitialEncoder 38229 lanes strategy gamma)
    (outerMany :
      initialCurveZBound + 224 * initialCurveYRows * initialCurveZBound +
          58 * (1024 + 1) * initialCurveYRows ^ 2 * initialCurveZBound +
            (28 * 1048576 + 1) * initialCurveYRows < challenges.card) :
    ∃ (components : Fin 29 → InitialMessage QM31Exact)
        (selected : Finset QM31Exact),
      selected ⊆ challenges ∧
      28 * Fintype.card (Fin 1048576) < selected.card ∧
      ∀ gamma ∈ selected,
        Width29CandidateOnCurve exactInitialEncoder strategy components
          gamma := by
  apply exists_four_elim
    (exists_exactV7Initial_weighted_fixed_branch lanes strategy coefficients
      coefficientsNeZero kernel challenges validOn outerMany)
  intro globalFactor x₀ localFactor selected specification
  obtain ⟨componentMessages, selectedLarge, onCurve⟩ :=
    exists_exactV7Initial_components_of_selected_branch lanes strategy
      challenges validOn globalFactor x₀ localFactor selected
      specification.2.1 specification.2.2.1 specification.2.2.2.1
      specification.2.2.2.2.1 specification.2.2.2.2.2.1
      specification.2.2.2.2.2.2.1 specification.2.2.2.2.2.2.2
  exact ⟨componentMessages, selected,
    specification.2.2.2.2.2.2.1, selectedLarge, onCurve⟩

set_option maxRecDepth 1048576 in
set_option maxHeartbeats 300000 in
/-- The mathematical width-29 extraction step over any explicitly supplied
finite set of valid challenges.  Its conclusion already consists of released
V7 messages, which keeps the concrete `goodChallenges` predicate out of the
branch/Hensel proof term. -/
theorem exists_exactV7Initial_curve_of_valid_challenges
    (lanes : Fin 29 → InitialWord QM31Exact)
    (strategy : Width29ProximateStrategy QM31Exact (Fin 1048576)
      (InitialMessage QM31Exact))
    (challenges : Finset QM31Exact)
    (validOn : ∀ gamma ∈ challenges,
      Width29ValidResponse exactInitialEncoder 38229 lanes strategy gamma)
    (outerMany :
      initialCurveZBound + 224 * initialCurveYRows * initialCurveZBound +
          58 * (1024 + 1) * initialCurveYRows ^ 2 * initialCurveZBound +
            (28 * 1048576 + 1) * initialCurveYRows < challenges.card) :
    ∃ (components : Fin 29 → InitialMessage QM31Exact)
        (selected : Finset QM31Exact),
      selected ⊆ challenges ∧
      28 * Fintype.card (Fin 1048576) < selected.card ∧
      ∀ gamma ∈ selected,
        Width29CandidateOnCurve exactInitialEncoder strategy components
          gamma := by
  obtain ⟨coefficients, coefficientsNeZero, kernel⟩ :=
    exists_exactInitialCurveInterpolation lanes
  exact exists_exactV7Initial_curve_of_interpolant lanes strategy coefficients
    coefficientsNeZero kernel challenges validOn outerMany

end

end AspisK1.V7ExactCorrelatedAgreementTerminal
