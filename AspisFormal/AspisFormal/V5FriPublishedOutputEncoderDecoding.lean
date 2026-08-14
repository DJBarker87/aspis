import AspisFormal.V5FriCurveDecodabilityTransport
import AspisFormal.V5FriConcreteEncoderApplicability
import AspisFormal.V5FriPublishedThresholds

/-!
# Applying the published RS curve theorem to the four V5 fold outputs

The four codes selected after the V5 fold challenges are the concrete
`encoder1`, `encoder2`, `encoder3`, and `encoder4` definitions.  This file does
not assume curve decodability for any of them.

The initial `encoder0` circle word is a different obligation: its decoder-list
size is handled by the circle-distance and Johnson-list modules.  It is not the
selected output code of any of these four challenge reductions.

Instead, it states one external theorem interface for an ordinary
bounded-degree polynomial-evaluation code.  The interface records the exact
Johnson-interval, integer agreement-floor, and multiplicity hypotheses of the
published theorem.  Existing polynomial realizations identify each V5 output
encoder, bijectively and pointwise, with one such ordinary code.  The generic
basis-change theorem then transports the published result to the V5 message
bases.

The only code-facing inputs below are the exact natural-basis evaluation
identities for the three recursive line encoders and distinctness of the final
evaluation points.  They are polynomial identities, not decoding or soundness
assumptions.  No `DegreeThreeCurveDecodable` statement about a V5 encoder is a
premise of the final theorem.
-/

namespace AspisV5FriPublishedOutputEncoderDecoding

open Polynomial
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriCurveDecodabilityTransport
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV5FriListCap
open AspisV5FriPublishedThresholds

variable {F K Message : Type*}
  [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K]

/-! ## The single published-theorem boundary -/

/-- The ordinary Reed--Solomon encoder on a supplied list of distinct points.
Its messages are exactly the polynomials of degree at most `degreeCap`. -/
def ordinaryPolynomialEvaluation {wordSize : Nat} (degreeCap : Nat)
    (nodes : Fin wordSize -> K) :
    DegreeBoundedPolynomial K degreeCap -> Fin wordSize -> K :=
  fun polynomial x => polynomial.1.eval (nodes x)

/-- External interface mirroring the published degree-three curve-decoding
theorem for ordinary polynomial-evaluation codes.

The hypotheses expose, rather than hide, every numerical applicability check:
the minimum-distance complement `1 - delta` is
`degreeCap / wordSize`; the exact release agreement is `1 - theta`; the integer
agreement threshold is the floor of `(1-theta) * wordSize`; `theta` lies in the
stated Johnson interval; and the selected Guruswami--Sudan multiplicity is the
published one.  The conclusion is the real-threshold form used by the transport
layer.  (`degreeCap / wordSize` is not the dimension rate: the message space has
dimension `degreeCap + 1`.)

This is deliberately universal over ordinary evaluation nodes.  Supplying
four unrelated curve-decoding statements for the V5 encoders would be a much
stronger and less inspectable assumption. -/
def PublishedOrdinaryPolynomialCurveDecoding : Prop :=
  ∀ (degreeCap wordSize agreementThreshold selectedMultiplicity : Nat)
      (nodes : Fin wordSize -> K) (rate theta : Real),
    0 < wordSize ->
    degreeCap < wordSize ->
    Function.Injective nodes ->
    rate = (degreeCap : Real) / wordSize ->
    1 - theta = requiredAgreement ->
    0 < rate ->
    rate < 1 ->
    (agreementThreshold : Real) ≤ (1 - theta) * wordSize ->
    (1 - theta) * wordSize < (agreementThreshold : Real) + 1 ->
    (1 - rate) / 2 ≤ theta ->
    theta < 1 - Real.sqrt rate ->
    AspisV5FriListCap.multiplicity rate = selectedMultiplicity ->
    RealThresholdDegreeThreeCurveDecodable
      (ordinaryPolynomialEvaluation degreeCap nodes)
      agreementThreshold
      (challengeThreshold selectedMultiplicity rate wordSize)
      (concurrencyThreshold selectedMultiplicity rate wordSize)

/-! ## Generic transport from an exact polynomial realization -/

/-- A complete pointwise polynomial realization turns the one ordinary-RS
theorem into curve decodability for the concrete encoder.  The equivalence is
constructed from the realization's proved injectivity and completeness; it is
not assumed. -/
theorem degreeThreeCurveDecodable_of_published_realization
    {wordSize degreeCap agreementThreshold selectedMultiplicity : Nat}
    (encoder : Message -> Fin wordSize -> K)
    (realization : PolynomialEvaluationRealization encoder degreeCap)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (rate theta : Real)
    (hwordSize : 0 < wordSize)
    (hdegree : degreeCap < wordSize)
    (hrate : rate = (degreeCap : Real) / wordSize)
    (htheta : 1 - theta = requiredAgreement)
    (hratePos : 0 < rate) (hrateLtOne : rate < 1)
    (hfloorLower : (agreementThreshold : Real) ≤
      (1 - theta) * wordSize)
    (hfloorUpper : (1 - theta) * wordSize <
      (agreementThreshold : Real) + 1)
    (hintervalLower : (1 - rate) / 2 ≤ theta)
    (hintervalUpper : theta < 1 - Real.sqrt rate)
    (hmultiplicity : AspisV5FriListCap.multiplicity rate =
      selectedMultiplicity) :
    DegreeThreeCurveDecodable encoder agreementThreshold
      ⌊challengeThreshold selectedMultiplicity rate wordSize⌋₊ := by
  let messageEquiv : Message ≃ DegreeBoundedPolynomial K degreeCap :=
    Equiv.ofBijective realization.toBoundedPolynomial
      realization.bijective_toBoundedPolynomial
  have hencoder : ∀ message,
      encoder message = ordinaryPolynomialEvaluation degreeCap
        realization.points (messageEquiv message) := by
    intro message
    funext x
    simpa [ordinaryPolynomialEvaluation, messageEquiv,
      PolynomialEvaluationRealization.toBoundedPolynomial] using
        realization.encoder_eq_eval message x
  have hreal := hpublished degreeCap wordSize agreementThreshold
    selectedMultiplicity realization.points rate theta hwordSize hdegree
    realization.points_injective hrate htheta hratePos hrateLtOne hfloorLower
    hfloorUpper hintervalLower hintervalUpper hmultiplicity
  have hinteger : DegreeThreeCurveDecodable
      (ordinaryPolynomialEvaluation degreeCap realization.points)
      agreementThreshold
      ⌊challengeThreshold selectedMultiplicity rate wordSize⌋₊ :=
    degreeThreeCurveDecodable_floor
      (ordinaryPolynomialEvaluation degreeCap realization.points)
      agreementThreshold
      (challengeThreshold selectedMultiplicity rate wordSize)
      (concurrencyThreshold selectedMultiplicity rate wordSize)
      (challengeThreshold_nonneg selectedMultiplicity rate wordSize hratePos)
      (by
        simpa using
          (concurrencyThreshold_ge_three_symbols selectedMultiplicity rate
            wordSize hratePos.le))
      hreal
  exact degreeThreeCurveDecodable_of_equiv encoder
    (ordinaryPolynomialEvaluation degreeCap realization.points)
    messageEquiv hencoder agreementThreshold
    ⌊challengeThreshold selectedMultiplicity rate wordSize⌋₊ hinteger

/-! ## Exact V5 threshold facts -/

/-- The last output code uses the same agreement fraction as the preceding
three rounds; its integer floor is `95`. -/
theorem final_output_agreement_floor :
    (95 : Real) ≤ requiredAgreement * 2048 ∧
      requiredAgreement * 2048 < 96 := by
  have hsquare : Real.sqrt (1 / 512 : Real) ^ 2 = 1 / 512 :=
    Real.sq_sqrt (by norm_num)
  have hnonneg : 0 ≤ Real.sqrt (1 / 512 : Real) := Real.sqrt_nonneg _
  unfold requiredAgreement
  constructor <;> nlinarith

/-- The exact integer agreement floors for the four codes selected by the
four V5 fold challenges. -/
theorem output_agreement_floors :
    (6082 : Real) ≤ requiredAgreement * 131072 ∧
      requiredAgreement * 131072 < 6083 ∧
    (1520 : Real) ≤ requiredAgreement * 32768 ∧
      requiredAgreement * 32768 < 1521 ∧
    (380 : Real) ≤ requiredAgreement * 8192 ∧
      requiredAgreement * 8192 < 381 ∧
    (95 : Real) ≤ requiredAgreement * 2048 ∧
      requiredAgreement * 2048 < 96 := by
  rcases deployed_agreement_floors with
    ⟨_initialLower, _initialUpper, h0Lower, h0Upper,
      h1Lower, h1Upper, h2Lower, h2Upper⟩
  rcases final_output_agreement_floor with ⟨h3Lower, h3Upper⟩
  simpa only [requiredAgreement] using
    And.intro h0Lower (And.intro h0Upper
      (And.intro h1Lower (And.intro h1Upper
        (And.intro h2Lower (And.intro h2Upper
          (And.intro h3Lower h3Upper))))))

/-! ## The four exact V5 output encoders -/

/-- Curve-decoding statements obtained for the exact four output encoders.
The natural-number challenge caps are the floors of the published real
thresholds, not hand-chosen bounds. -/
structure V5OutputEncoderCurveDecoding
    (schedule : FixedSchedule F K) (points : EvaluationPoints F) : Prop where
  round0 : DegreeThreeCurveDecodable
    (encoder1 schedule points) 6082
    ⌊challengeThreshold 10 round0Rate 131072⌋₊
  round1 : DegreeThreeCurveDecodable
    (encoder2 schedule points) 1520
    ⌊challengeThreshold 9 round1Rate 32768⌋₊
  round2 : DegreeThreeCurveDecodable
    (encoder3 schedule points) 380
    ⌊challengeThreshold 6 round2Rate 8192⌋₊
  round3 : DegreeThreeCurveDecodable
    (encoder4 schedule) 95
    ⌊challengeThreshold 3 round3Rate 2048⌋₊

/-- The published ordinary polynomial-evaluation theorem applies to all four
concrete V5 fold-output encoders.

No field of `hpublished` mentions a V5 encoder.  `identities` and
`hfinalDistinct` are the exact code/domain equations needed to identify the
maintained encoders with ordinary evaluation codes. -/
theorem published_curve_decoding_applies_to_v5_outputs
    [NeZero (2 : K)]
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (identities : ConcreteLineEvaluationIdentities schedule points)
    (hfinalDistinct : FinalDomainDistinct schedule)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)) :
    V5OutputEncoderCurveDecoding schedule points := by
  rcases output_agreement_floors with
    ⟨hfloor0Lower, hfloor0Upper, hfloor1Lower, hfloor1Upper,
      hfloor2Lower, hfloor2Upper, hfloor3Lower, hfloor3Upper⟩
  rcases all_rounds_in_published_johnson_interval with
    ⟨hinterval0Lower, hinterval0Upper,
      hinterval1Lower, hinterval1Upper,
      hinterval2Lower, hinterval2Upper,
      hinterval3Lower, hinterval3Upper⟩
  rcases output_multiplicities with
    ⟨hmultiplicity0, hmultiplicity1, hmultiplicity2, hmultiplicity3⟩
  constructor
  · apply degreeThreeCurveDecodable_of_published_realization
      (encoder1 schedule points)
      (encoder1PolynomialRealization schedule points identities.layer1)
      hpublished round0Rate (proximity round0Rate)
    · norm_num
    · norm_num
    · rfl
    · unfold proximity
      ring
    · norm_num [round0Rate]
    · norm_num [round0Rate]
    · simpa [proximity] using hfloor0Lower
    · convert hfloor0Upper using 1 <;> norm_num [proximity]
    · exact hinterval0Lower
    · exact hinterval0Upper
    · exact hmultiplicity0
  · apply degreeThreeCurveDecodable_of_published_realization
      (encoder2 schedule points)
      (encoder2PolynomialRealization schedule points identities.layer2)
      hpublished round1Rate (proximity round1Rate)
    · norm_num
    · norm_num
    · rfl
    · unfold proximity
      ring
    · norm_num [round1Rate]
    · norm_num [round1Rate]
    · simpa [proximity] using hfloor1Lower
    · convert hfloor1Upper using 1 <;> norm_num [proximity]
    · exact hinterval1Lower
    · exact hinterval1Upper
    · exact hmultiplicity1
  · apply degreeThreeCurveDecodable_of_published_realization
      (encoder3 schedule points)
      (encoder3PolynomialRealization schedule points identities.layer3)
      hpublished round2Rate (proximity round2Rate)
    · norm_num
    · norm_num
    · rfl
    · unfold proximity
      ring
    · norm_num [round2Rate]
    · norm_num [round2Rate]
    · simpa [proximity] using hfloor2Lower
    · convert hfloor2Upper using 1 <;> norm_num [proximity]
    · exact hinterval2Lower
    · exact hinterval2Upper
    · exact hmultiplicity2
  · apply degreeThreeCurveDecodable_of_published_realization
      (encoder4 schedule)
      (encoder4PolynomialRealization schedule hfinalDistinct)
      hpublished round3Rate (proximity round3Rate)
    · norm_num
    · norm_num
    · rfl
    · unfold proximity
      ring
    · norm_num [round3Rate]
    · norm_num [round3Rate]
    · simpa [proximity] using hfloor3Lower
    · convert hfloor3Upper using 1 <;> norm_num [proximity]
    · exact hinterval3Lower
    · exact hinterval3Upper
    · exact hmultiplicity3

/-! ## Audit -/

#print axioms degreeThreeCurveDecodable_of_published_realization
#print axioms final_output_agreement_floor
#print axioms output_agreement_floors
#print axioms published_curve_decoding_applies_to_v5_outputs

end AspisV5FriPublishedOutputEncoderDecoding
