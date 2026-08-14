import AspisFormal.V5FriConcreteEncoderApplicability

/-!
# Exact minimum distance of a realized Reed--Solomon code

`V5FriConcreteEncoderApplicability` proves both halves of the usual
Reed--Solomon distance calculation: distinct degree-at-most-`d` polynomials
agree at no more than `d` distinct evaluation points, and an explicit pair of
represented polynomials attains that overlap.  This file packages those two
facts as one exact-distance statement for each V5 output code.

Thus the maximum overlap of distinct codewords is exactly `d`, and the minimum
Hamming-distance numerator is exactly `wordSize - d`.
-/

namespace AspisV5FriExactRSDistance

open Polynomial
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriInitialListBound
open AspisV5FriConcreteEncoderApplicability

variable {K Message : Type*} {wordSize degreeCap : Nat}
  [Field K] [DecidableEq K]

/-- Exact overlap form of the Reed--Solomon minimum-distance statement.

The first field is the root-count upper bound for every pair of distinct
messages.  The second field witnesses two concrete messages attaining that
bound. -/
structure ExactPolynomialEvaluationDistance
    (encoder : Message -> Fin wordSize -> K) (degreeCap : Nat) : Prop where
  overlap_le : ∀ left right, left ≠ right ->
    (agreementSet (encoder left) (encoder right)).card ≤ degreeCap
  overlap_attained : ∃ left right, left ≠ right ∧
    (agreementSet (encoder left) (encoder right)).card = degreeCap

/-- A complete evaluation realization on distinct points has exact maximum
overlap `degreeCap`.  In particular its minimum Hamming-distance numerator is
`wordSize - degreeCap`.

The attaining pair is supplied by the explicit root-polynomial construction in
`V5FriConcreteEncoderApplicability`. -/
theorem exactPolynomialEvaluationDistance
    (encoder : Message -> Fin wordSize -> K)
    (realization : PolynomialEvaluationRealization encoder degreeCap)
    (hdegree : degreeCap < wordSize) :
    ExactPolynomialEvaluationDistance encoder degreeCap := by
  constructor
  · intro left right hne
    exact agreementSet_card_le_of_polynomialEvaluation
      encoder degreeCap realization left right hne
  · exact exists_messages_with_exact_agreement
      encoder degreeCap realization hdegree

/-! ## The four V5 output codes -/

/-- Exact distance statements for the four Reed--Solomon codes selected after
the four V5 folds.  This record states both the universal overlap bound and an
attaining pair for each code. -/
structure V5OutputExactDistances {F : Type*} [Field F] [Algebra F K]
    (schedule : FixedSchedule F K) (points : EvaluationPoints F) : Prop where
  round0 : ExactPolynomialEvaluationDistance (encoder1 schedule points) 255
  round1 : ExactPolynomialEvaluationDistance (encoder2 schedule points) 63
  round2 : ExactPolynomialEvaluationDistance (encoder3 schedule points) 15
  round3 : ExactPolynomialEvaluationDistance (encoder4 schedule) 3

/-- Once the concrete evaluation identities and final-domain distinctness are
supplied, all four output codes have exact, not merely lower-bounded, minimum
distance.  The distance complements are consequently
`255/131072`, `63/32768`, `15/8192`, and `3/2048`. -/
theorem exactV5OutputDistances {F : Type*} [Field F] [Algebra F K]
    [NeZero (2 : K)]
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (identities : ConcreteLineEvaluationIdentities schedule points)
    (hfinalDistinct : FinalDomainDistinct schedule) :
    V5OutputExactDistances schedule points := by
  exact ⟨
    exactPolynomialEvaluationDistance (encoder1 schedule points)
      (encoder1PolynomialRealization schedule points identities.layer1) (by norm_num),
    exactPolynomialEvaluationDistance (encoder2 schedule points)
      (encoder2PolynomialRealization schedule points identities.layer2) (by norm_num),
    exactPolynomialEvaluationDistance (encoder3 schedule points)
      (encoder3PolynomialRealization schedule points identities.layer3) (by norm_num),
    exactPolynomialEvaluationDistance (encoder4 schedule)
      (encoder4PolynomialRealization schedule hfinalDistinct) (by norm_num)
  ⟩

/-! ## Audit -/

#print axioms exactPolynomialEvaluationDistance
#print axioms exactV5OutputDistances

end AspisV5FriExactRSDistance
