import AspisFormal.K1.V7Tag73CausalOneFoldProbability
import AspisFormal.K1.V7Tag73CausalRestoredK15Probability
import AspisFormal.K1.V7Tag73ExactOneFoldEncoderBinding
import AspisFormal.K1.V7ExactCorrelatedAgreementInitial
import AspisFormal.K1.V7ExactCorrelatedAgreementTerminal

/-!
# Exact internal curve-probability specializations for Tag-73

The generic causal K1.3/K1.5 probability modules deliberately accept published
curve-decodability predicates.  V7 now proves both concrete predicates inside
Lean.  This module installs those exact theorems and leaves only the literal
counterfactual/source-coordinate providers to the operational composition.

No published coding theorem is a parameter of the declarations below.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73ExactInternalCurveProbability

open MeasureTheory
open AspisK1.V7ExactCorrelatedAgreementTerminal
open AspisK1.V7Tag73CausalOneFoldProbability
open AspisK1.V7Tag73CausalRestoredFamily
open AspisK1.V7Tag73CausalRestoredK15Probability
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73RestoredPointCompatibleK14
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCQM31TowerExact
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV6OneFoldCandidateExtraction
open AspisV6PublishedTheoremInterfaces

noncomputable section

/-- Exact pre-alpha context for one causal one-fold experiment.  The encoder
and inverse-table equalities are concrete source/public-parameter facts; the
degree-three correlated-agreement theorem is not stored in this structure. -/
structure ExactCausalOneFoldSamplerContext where
  schedule : OneFoldSchedule M31Exact QM31Exact
  encoders : CodeEncoders QM31Exact
  initialEncoderExact : encoders.initial = exactInitialEncoder
  finalEncoderExact : encoders.final = exactFinalEncoder
  inverseTablesExact : ExactOneFoldInverseTables schedule
  base : IdealTranscript QM31Exact
  strategy : ProximateStrategy QM31Exact (Fin 262144)
    (FinalCoefficients QM31Exact)

/-- Forget the exact source equalities after using them to construct the
generic algebraic binding and install the kernel-proved V7 degree-three
correlated-agreement theorem. -/
noncomputable def ExactCausalOneFoldSamplerContext.toGeneric
    (context : ExactCausalOneFoldSamplerContext) :
    CausalOneFoldSamplerContext M31Exact where
  schedule := context.schedule
  encoders := context.encoders
  binding := exactOneFoldAlgebraBinding context.schedule context.encoders
    context.initialEncoderExact context.finalEncoderExact
    context.inverseTablesExact
  base := context.base
  strategy := context.strategy
  published := by
    change PublishedOneFoldCurveDecodability exactFinalLinear
    exact exactV7FinalPublishedOneFoldCurveDecodability

/-- Exact causal one-fold probability.  Only the pre-answer context family is
supplied; the concrete coding theorem is discharged internally. -/
theorem exact_causal_oneFold_duplex_alpha_probability_le
    (context : Tag73CompleteOrdinarySamplerSkeleton →
      ExactCausalOneFoldSamplerContext) :
    (PMF.uniformOfFintype SuccessfulTag73DuplexOrdinaryAttempt).toOuterMeasure
        (duplexOrdinaryDependentEvent
          (causalOneFoldSamplerTarget fun skeleton =>
            (context skeleton).toGeneric)) ≤
      (foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  exact causal_oneFold_duplex_alpha_probability_le fun skeleton =>
    (context skeleton).toGeneric

/-- Exact restoration-aware K1.5 residual probability.  The concrete
width-29 theorem is kernel-proved, so no published theorem value remains in
the operational theorem signature. -/
theorem exact_causal_restored_k15_residual_duplex_gamma_probability_le
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : RestoredK15PreGammaProvider decoder words) :
    (PMF.uniformOfFintype SuccessfulTag73DuplexNonzeroAttempts).toOuterMeasure
        (causalRestoredK15ResidualDuplexGammaEvent provider) ≤
      (initialBatchChallengeCap : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal) := by
  exact causal_restored_k15_residual_duplex_gamma_probability_le
    exactV7InitialPublishedWidth29CurveDecodability provider

/-- Exact ungated K1.5 constrained-gamma probability for contexts in which
the absence of a restored point-compatible K1.4 certificate is already
established. -/
theorem exact_causal_restored_k15_duplex_gamma_probability_le
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : RestoredK15PreGammaProvider decoder words)
    (noRestored : ∀ skeleton,
      ¬ HasAcceptedRestoredPointCompatibleK14 decoder words
        (provider.point skeleton) (provider.claims skeleton)
        (restoredSelectedChainFamilyOfK13Provider
          (provider.selected skeleton))) :
    (PMF.uniformOfFintype SuccessfulTag73DuplexNonzeroAttempts).toOuterMeasure
        (causalRestoredK15DuplexGammaEvent provider) ≤
      (initialBatchChallengeCap : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal) := by
  exact causal_restored_k15_duplex_gamma_probability_le
    exactV7InitialPublishedWidth29CurveDecodability provider noRestored

end

#print axioms ExactCausalOneFoldSamplerContext.toGeneric
#print axioms exact_causal_oneFold_duplex_alpha_probability_le
#print axioms
  exact_causal_restored_k15_residual_duplex_gamma_probability_le
#print axioms exact_causal_restored_k15_duplex_gamma_probability_le

end AspisK1.V7Tag73ExactInternalCurveProbability
