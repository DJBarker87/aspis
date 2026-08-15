import AspisFormal.V5FriReleasedLineGeometry
import AspisFormal.V5FriListCap
import AspisFormal.V5ComponentCQM31TowerExact
import AspisFormal.V5WorkNormalizedApplicabilityRepair
import AspisFormal.V5Width19CorrelatedAgreement

set_option maxRecDepth 40000
set_option maxHeartbeats 200000

/-!
# Exact side conditions for the released width-19 circle batching step

This file audits the initial V5 batching step against Appendix A.2,
Corollary 1 of the 24 March 2026 revision of S-two.  It proves the local facts
that can be checked from this repository:

* the batching field is the exact deployed quartic extension of M31;
* the initial domain has `2^19 = 524288` points;
* the maintained initial code is a QM31-linear subspace whose words are
  evaluations of `p0(x) + y*p1(x)` with both degrees below `512`;
* the containing circle-code parameter is `N = 1024`, hence the distance
  complement is `1/512` and the stated proximity is in the Johnson interval;
* the release uses nineteen lanes, so the scalar-power curve has degree
  eighteen;
* the agreement floor, Guruswami--Sudan multiplicity, list bound, and
  Corollary-1 challenge threshold are the exact released values; and
* restricting the paper's full-field challenge set to the deployed nonzero
  sampler changes only the denominator from `|QM31|` to `|QM31|-1`.

The paper's correlated-agreement result is deliberately represented by the
named proposition `PublishedAppendixA2Width19CurveDecodability`; it is not
asserted as a Lean theorem.  That proposition is definitionally the exact
`Width19CurveDecodable` interface already consumed by the batching reduction,
not a parallel soundness predicate.

The production verifier does not run the initial FFT.  For false-acceptance
soundness the nineteen committed lanes may be arbitrary received words, as the
published theorem permits; the verifier's fold checks target the maintained
code.  `RustInitialEncoderEquality` is therefore a completeness and
reproducibility boundary for the honest prover, not a premise of this CAT
soundness step.  This module supplies exact applicability data and a
nonzero-challenge restriction lemma, not an end-to-end deployed soundness
claim.
-/

namespace AspisV5Width19S2ApplicabilityAudit

open Polynomial
open AspisSoundnessLedger
open AspisCircleGroupOrder
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriExactLineDomains
open AspisV5FriInitialCircleEncoderIdentity
open AspisV5FriReleasedLineGeometry
open AspisV5FriListCap
open AspisV5ComponentCQM31Representation
open AspisV5ComponentCQM31TowerExact
open AspisV5ComponentCRejectionSampler
open AspisV5WorkNormalizedApplicabilityRepair
open AspisV5Width19CorrelatedAgreement
open AspisV5Width19LaneBatchBinding

/-! ## Exact released parameters -/

abbrev BaseField := M31Exact
abbrev ChallengeField := QM31Exact
abbrev InitialDomain := Fin 524288

theorem challenge_field_two_ne_zero : (2 : ChallengeField) ≠ 0 := by
  intro h
  have hm :
      algebraMap BaseField ChallengeField (2 : BaseField) =
        algebraMap BaseField ChallengeField 0 := by
    simpa only [map_ofNat, map_zero] using h
  have hbase : (2 : BaseField) = 0 :=
    (FaithfulSMul.algebraMap_injective BaseField ChallengeField) hm
  exact (by decide : (2 : BaseField) ≠ 0) hbase

local instance challengeFieldTwoNeZero : NeZero (2 : ChallengeField) :=
  ⟨challenge_field_two_ne_zero⟩

def initialCircleOrder : Nat := 1024
def initialDomainSize : Nat := 524288
def releasedBatchWidth : Nat := 19
def releasedCurveDegree : Nat := releasedBatchWidth - 1

noncomputable def distanceComplement : ℝ := 1 / 512
noncomputable def relativeDistance : ℝ := 1 - distanceComplement
noncomputable def releasedAgreement : ℝ :=
  (21 / 20) * Real.sqrt distanceComplement
noncomputable def releasedProximity : ℝ := 1 - releasedAgreement

/-- The exact finite parameters appearing in the width-19 application. -/
theorem exact_released_dimensions :
    initialCircleOrder = 1024 ∧
      initialDomainSize = 2 ^ 19 ∧
      releasedBatchWidth = 19 ∧
      releasedCurveDegree = 18 ∧
      initialCircleOrder * 512 = initialDomainSize := by
  norm_num [initialCircleOrder, initialDomainSize, releasedBatchWidth,
    releasedCurveDegree]

/-- The containing circle code has distance complement `N/|D| = 1/512`. -/
theorem exact_distance_complement :
    (initialCircleOrder : ℝ) / initialDomainSize = distanceComplement := by
  norm_num [initialCircleOrder, initialDomainSize, distanceComplement]

/-- The released proximity lies in the Johnson interval required by the
published circle correlated-agreement corollary. -/
theorem released_proximity_in_johnson_interval :
    relativeDistance / 2 ≤ releasedProximity ∧
      releasedProximity < 1 - Real.sqrt (1 - relativeDistance) := by
  have hsquare : Real.sqrt (1 / 512 : ℝ) ^ 2 = 1 / 512 :=
    Real.sq_sqrt (by norm_num)
  have hpositive : 0 < Real.sqrt (1 / 512 : ℝ) :=
    Real.sqrt_pos.2 (by norm_num)
  unfold relativeDistance releasedProximity releasedAgreement distanceComplement
  constructor <;> nlinarith

/-- Equation (74) chooses multiplicity ten for the initial code. -/
theorem exact_initial_multiplicity :
    AspisV5FriListCap.multiplicity circleRate = 10 :=
  deployed_multiplicities.1

/-- At the initial code, equation (73) is exactly
`(21/2) / sqrt(1/512)`, and it is below the public cap 240. -/
theorem exact_initial_gs_list_expression :
    listBound circleRate = (21 / 2) / Real.sqrt (1 / 512) ∧
      listBound circleRate < 240 := by
  constructor
  · rw [listBound, exact_initial_multiplicity]
    norm_num [circleRate]
  · exact all_committed_list_bounds_lt_240.1

/-- The exact integer floor used by the released decoder at 524288 symbols. -/
theorem exact_initial_agreement_floor :
    (24328 : ℝ) ≤ releasedAgreement * initialDomainSize ∧
      releasedAgreement * initialDomainSize < 24329 := by
  constructor
  · simpa [releasedAgreement, distanceComplement, initialDomainSize] using
      deployed_agreement_floors.1
  · simpa [releasedAgreement, distanceComplement, initialDomainSize] using
      deployed_agreement_floors.2.1

/-! ## The exact deployed challenge field -/

/-- The literal quadratic-over-quadratic QM31 tower has `(2^31-1)^4`
elements. -/
theorem exact_challenge_field_card :
    Fintype.card ChallengeField = (2 ^ 31 - 1) ^ 4 := by
  calc
    Fintype.card ChallengeField = Fintype.card QM31Limbs :=
      Fintype.card_congr qm31ExactLimbEquiv.symm
    _ = DeployedPrime ^ 4 := qm31Limbs_card
    _ = (2 ^ 31 - 1) ^ 4 := by
      norm_num [DeployedPrime, m31Modulus, rawCandidateCount]

/-- The real-valued field constant in the soundness ledger is the cardinality
of the exact deployed challenge field. -/
theorem exact_challenge_field_card_real :
    (Fintype.card ChallengeField : ℝ) = FIELD := by
  rw [exact_challenge_field_card]
  norm_num [FIELD]

/-- Removing zero leaves exactly `|QM31|-1` possible deployed batching
challenges. -/
theorem exact_nonzero_challenge_count :
    Fintype.card {z : ChallengeField // z ≠ 0} =
      (2 ^ 31 - 1) ^ 4 - 1 := by
  calc
    Fintype.card {z : ChallengeField // z ≠ 0} =
        Fintype.card ChallengeField -
          Fintype.card {z : ChallengeField // z = 0} :=
      Fintype.card_subtype_compl (fun z : ChallengeField => z = 0)
    _ = (2 ^ 31 - 1) ^ 4 - 1 := by
      rw [exact_challenge_field_card, Fintype.card_subtype_eq]

/-! ## The exact QM31-linear strict circle-code subspace -/

/-- The maintained released initial encoder, viewed as its QM31-linear range. -/
noncomputable def releasedInitialCode
    (schedule : FixedSchedule BaseField ChallengeField) :
    Submodule ChallengeField (Word0 ChallengeField) :=
  LinearMap.range (encoder0 schedule releasedEvaluationPoints)

/-- A word has the strict order-1024 circle-polynomial form used by the
released code: `p0(x)+y*p1(x)` with both univariate degrees below 512, on the
exact stored `G'_19` order. -/
def IsReleasedStrictCircleWord (word : Word0 ChallengeField) : Prop :=
  ∃ p0 p1 : ChallengeField[X],
    p0.natDegree < 512 ∧
      p1.natDegree < 512 ∧
      ∀ k : Fin (2 ^ 19),
        word k =
          p0.eval
              (algebraMap BaseField ChallengeField
                (X (storedInitialCirclePoint k))) +
            algebraMap BaseField ChallengeField
                (circleYCoordinate (storedInitialCirclePoint k)) *
              p1.eval
                (algebraMap BaseField ChallengeField
                  (X (storedInitialCirclePoint k)))

/-- Every word in the maintained QM31-linear range has the strict circle-code
form on the exact released domain. -/
theorem released_initial_code_is_strict_circle_subspace
    (schedule : FixedSchedule BaseField ChallengeField)
    (hfinal : FinalXMatchesReleasedDomain schedule)
    (word : Word0 ChallengeField)
    (hword : word ∈ releasedInitialCode schedule) :
    IsReleasedStrictCircleWord word := by
  rcases hword with ⟨coefficients, rfl⟩
  let identities := releasedLineEvaluationIdentities schedule hfinal
  have hencoder1 : ∀ (message : Coeff1 ChallengeField) (i : Fin 131072),
      encoder1 schedule releasedEvaluationPoints message i =
        (naturalCoefficientPolynomial message).eval
          (algebraMap BaseField ChallengeField (storedFirstLineX i)) := by
    intro message i
    have h := identities.layer1.encoder_eq_eval message i
    change encoder1 schedule releasedEvaluationPoints message i =
      (naturalCoefficientPolynomial message).eval
        (algebraMap BaseField ChallengeField (storedLine17X i)) at h
    simpa only [storedFirstLineX, storedLine17X, storedLine17Point, line17X]
      using h
  refine ⟨initialP0 coefficients, initialP1 coefficients,
    initialP0_degree_lt coefficients, initialP1_degree_lt coefficients, ?_⟩
  intro k
  exact encoder0_eq_stored_circle_eval schedule releasedEvaluationPoints
    (by intro i; rfl) (by intro i; rfl) hencoder1 coefficients k

/-- Pairwise agreement of distinct released initial codewords is at most
`1024`; equivalently the maintained code has relative distance at least
`1-1024/524288 = 511/512`. -/
theorem exact_released_initial_code_distance
    (schedule : FixedSchedule BaseField ChallengeField)
    (hfinal : FinalXMatchesReleasedDomain schedule) :
    InitialEncoderDistance
      (concreteCodeEncoders schedule releasedEvaluationPoints) :=
  releasedInitialEncoderDistance schedule hfinal

/-! ## The mixed M31/QM31 lanes live in one QM31 word space

Corollary 1 allows the input functions `f_j` to be arbitrary `K^D` words.  It
requires the *candidate code* `C'`, not the tuple of received words, to be an
`F`-linear subspace.  Thus the sixteen M31 lanes only need their canonical
coordinatewise embedding into QM31; the three QM31 lanes already have the
required codomain.
-/

structure ReleasedMixedLanes where
  c1 : Fin 16 → Word0 BaseField
  c2 : Fin 3 → Word0 ChallengeField

def embedBaseWord (word : Word0 BaseField) : Word0 ChallengeField :=
  fun i => algebraMap BaseField ChallengeField (word i)

def ReleasedMixedLanes.lane
    (lanes : ReleasedMixedLanes) (j : Fin 19) : Word0 ChallengeField :=
  if h : j.val < 16 then
    embedBaseWord (lanes.c1 ⟨j.val, h⟩)
  else
    lanes.c2 ⟨j.val - 16, by omega⟩

/-- The exact nineteen-term scalar-powers combination used in the initial
batch.  Its largest exponent is eighteen. -/
noncomputable def powersBatch
    (lanes : ReleasedMixedLanes) (gamma : ChallengeField) :
    Word0 ChallengeField :=
  fun i => ∑ j : Fin 19, gamma ^ j.val * lanes.lane j i

theorem powers_batch_uses_exact_exponents
    (lanes : ReleasedMixedLanes) (gamma : ChallengeField)
    (i : InitialDomain) :
    powersBatch lanes gamma i =
      ∑ j : Fin 19, gamma ^ j.val * lanes.lane j i ∧
      (Finset.univ.image (fun j : Fin 19 => j.val)) = Finset.range 19 := by
  constructor
  · rfl
  · ext n
    simp [Finset.mem_image]
    constructor
    · rintro ⟨j, -, rfl⟩
      exact j.isLt
    · intro hn
      exact ⟨⟨n, by simpa using hn⟩, by simp⟩

/-- The mixed-field lane adapter feeds exactly the curve used by the existing
width-19 correlated-agreement reduction. -/
theorem powers_batch_eq_width19_curve_value
    (lanes : ReleasedMixedLanes) (gamma : ChallengeField) :
    powersBatch lanes gamma =
      fun i => width19CurveValue lanes.lane gamma i := by
  funext i
  unfold powersBatch width19CurveValue width19Batch
  apply Finset.sum_congr rfl
  intro lane _hlane
  ring

/-- The polynomial used by the existing reduction has degree at most the
released value eighteen. -/
theorem actual_width19_curve_degree_le (values : Fin 19 → ChallengeField) :
    (monomialPolynomial values).natDegree ≤ releasedCurveDegree := by
  simpa [releasedCurveDegree, releasedBatchWidth] using
    width19Polynomial_natDegree_le values

/-! ## The exact interface consumed by the width-19 reduction -/

/-- The exact challenge-count threshold displayed by Appendix A.2 after
substituting `M=18`, `|D|=524288`, `1-delta=1/512`, and the released GS list
expression. -/
noncomputable def appendixA2Width19Threshold : ℝ :=
  ((21 / 2) / Real.sqrt (1 / 512)) *
    ((2 * ((21 / 2) / Real.sqrt (1 / 512)) ^ 4 / 3) * (1 / 512) + 1) *
    18 * 524288

/-- The displayed threshold is nonnegative, so its natural-number cap is its
floor. -/
theorem appendixA2_width19_threshold_nonneg :
    0 ≤ appendixA2Width19Threshold := by
  unfold appendixA2Width19Threshold
  have hsqrt : 0 < Real.sqrt (1 / 512 : ℝ) :=
    Real.sqrt_pos.2 (by norm_num)
  positivity

noncomputable def appendixA2Width19ChallengeCap : Nat :=
  ⌊appendixA2Width19Threshold⌋₊

theorem appendixA2_width19_cap_le_threshold :
    (appendixA2Width19ChallengeCap : ℝ) ≤ appendixA2Width19Threshold := by
  exact Nat.floor_le appendixA2_width19_threshold_nonneg

/-- The concrete encoder consumed by the existing width-19 batching
reduction. -/
def releasedEncoder
    (schedule : FixedSchedule BaseField ChallengeField) :
    Coeff0 ChallengeField → InitialDomain → ChallengeField :=
  fun coefficients => encoder0 schedule releasedEvaluationPoints coefficients

/-- Exact arithmetic relation between the fibre threshold used by the V5
query/fold analysis and the symbol threshold used by initial CAT.  Each initial
fibre contributes four symbols to `supportedAgreement0`. -/
theorem exact_initial_cat_threshold_and_four_symbol_expansion :
    agreementCap1 = 6082 ∧
      agreementCap0 = 24328 ∧
      agreementCap0 = 4 * agreementCap1 ∧
      ∀ fibres : Nat, agreementCap1 < fibres → agreementCap0 < 4 * fibres := by
  norm_num [agreementCap0, agreementCap1]

/-- The exact published-theorem input for this release.  It is deliberately
definitionally the existing `Width19CurveDecodable` predicate, with domain
`Fin 524288`, agreement-card floor `24328`, scalar-power degree `18`, and the
floor of the displayed Appendix-A.2 threshold.  This module does not prove
the cited literature result. -/
def PublishedAppendixA2Width19CurveDecodability
    (schedule : FixedSchedule BaseField ChallengeField) : Prop :=
  FinalXMatchesReleasedDomain schedule ∧
    Width19CurveDecodable (releasedEncoder schedule) agreementCap0
      appendixA2Width19ChallengeCap

/-- No parallel event is hidden behind the literature premise: it supplies
the exact predicate consumed by `width19_bad_response_challenges_card_le`. -/
theorem published_appendixA2_supplies_exact_width19_curve_decodable
    (schedule : FixedSchedule BaseField ChallengeField)
    (published : PublishedAppendixA2Width19CurveDecodability schedule) :
    Width19CurveDecodable (releasedEncoder schedule) 24328
      appendixA2Width19ChallengeCap := by
  simpa [PublishedAppendixA2Width19CurveDecodability, agreementCap0] using
    published.2

/-! ### Full-field paper statement versus the deployed nonzero sampler -/

/-- Full-field version of the valid-response challenge set.  It differs from
the deployed set only by allowing zero. -/
noncomputable def width19AllFieldGoodChallenges
    {Message : Type*}
    (encoder : Message → InitialDomain → ChallengeField)
    (agreementThreshold : Nat)
    (lanes : Fin 19 → InitialDomain → ChallengeField)
    (strategy : Width19ProximateStrategy ChallengeField InitialDomain Message) :
    Finset ChallengeField := by
  classical
  exact Finset.univ.filter
    (Width19ValidResponse encoder agreementThreshold lanes strategy)

/-- Exact restriction identity: the deployed good-challenge set is the
paper's full-field set with zero erased. -/
theorem width19_good_challenges_are_full_field_set_without_zero
    {Message : Type*}
    (encoder : Message → InitialDomain → ChallengeField)
    (agreementThreshold : Nat)
    (lanes : Fin 19 → InitialDomain → ChallengeField)
    (strategy : Width19ProximateStrategy ChallengeField InitialDomain Message) :
    width19GoodChallenges encoder agreementThreshold lanes strategy =
      (width19AllFieldGoodChallenges encoder agreementThreshold lanes
        strategy).erase 0 := by
  classical
  ext gamma
  simp [width19GoodChallenges, width19AllFieldGoodChallenges, and_assoc,
    and_left_comm, and_comm]

/-- In particular, every good deployed nonzero challenge is a good challenge
for the paper's all-field statement.  This is the set-theoretic reason the
published implication restricts to `F*`; probability must then divide by
`|F|-1`. -/
theorem nonzero_width19_good_challenges_subset_all_field
    {Message : Type*}
    (encoder : Message → InitialDomain → ChallengeField)
    (agreementThreshold : Nat)
    (lanes : Fin 19 → InitialDomain → ChallengeField)
    (strategy : Width19ProximateStrategy ChallengeField InitialDomain Message) :
    width19GoodChallenges encoder agreementThreshold lanes strategy ⊆
      width19AllFieldGoodChallenges encoder agreementThreshold lanes strategy := by
  rw [width19_good_challenges_are_full_field_set_without_zero]
  exact Finset.erase_subset _ _

/-- Direct use of the exact published input in the already-proved bad-response
counting theorem. -/
theorem released_width19_bad_response_count_le_exact_cap
    (schedule : FixedSchedule BaseField ChallengeField)
    (published : PublishedAppendixA2Width19CurveDecodability schedule)
    (lanes : Fin 19 → InitialDomain → ChallengeField)
    (strategy : Width19ProximateStrategy ChallengeField InitialDomain
      (Coeff0 ChallengeField)) :
    (width19GoodChallenges (releasedEncoder schedule) 24328 lanes
      (width19BadStrategy (releasedEncoder schedule) 24328 lanes strategy)).card ≤
        appendixA2Width19ChallengeCap := by
  exact width19_bad_response_challenges_card_le
    (releasedEncoder schedule) 24328 appendixA2Width19ChallengeCap
    (published_appendixA2_supplies_exact_width19_curve_decodable
      schedule published) lanes strategy

/-- Probability of the exact bad-response set under the deployed uniform
nonzero challenge sampler. -/
noncomputable def releasedWidth19BadResponseProbability
    (schedule : FixedSchedule BaseField ChallengeField)
    (lanes : Fin 19 → InitialDomain → ChallengeField)
    (strategy : Width19ProximateStrategy ChallengeField InitialDomain
      (Coeff0 ChallengeField)) : ℚ :=
  (width19GoodChallenges (releasedEncoder schedule) 24328 lanes
      (width19BadStrategy (releasedEncoder schedule) 24328 lanes strategy)).card /
    (((2 ^ 31 - 1) ^ 4 - 1 : Nat) : ℚ)

/-- Exact `|QM31|-1` denominator for the conditional CAT probability bound. -/
theorem released_width19_bad_response_probability_uses_exact_fstar_denominator
    (schedule : FixedSchedule BaseField ChallengeField)
    (published : PublishedAppendixA2Width19CurveDecodability schedule)
    (lanes : Fin 19 → InitialDomain → ChallengeField)
    (strategy : Width19ProximateStrategy ChallengeField InitialDomain
      (Coeff0 ChallengeField)) :
    releasedWidth19BadResponseProbability schedule lanes strategy ≤
      (appendixA2Width19ChallengeCap : ℚ) /
        (((2 ^ 31 - 1) ^ 4 - 1 : Nat) : ℚ) := by
  have hdenNat : 0 < (2 ^ 31 - 1) ^ 4 - 1 := by norm_num
  have hden : (0 : ℚ) < (((2 ^ 31 - 1) ^ 4 - 1 : Nat) : ℚ) := by
    exact_mod_cast hdenNat
  rw [releasedWidth19BadResponseProbability,
    div_le_div_iff_of_pos_right hden]
  exact_mod_cast released_width19_bad_response_count_le_exact_cap
    schedule published lanes strategy

/-! ## Conditional arithmetic for the 100-bit release target -/

/-- The threshold divided by the exact nonzero challenge count and the
released 37-bit work factor is definitionally the corrected batching term. -/
theorem appendixA2_threshold_fraction_eq_repaired_batch_term :
    appendixA2Width19Threshold / (FIELD - 1) / 2 ^ 37 =
      powersBatchArithmeticFStar 18 := by
  unfold appendixA2Width19Threshold powersBatchArithmeticFStar
  ring

/-- Conditional numerical budget for this one batching event.  It is below
`2^-107`, hence leaves seven bits of margin inside the project's 100-bit
overall target.  Applying the `2^37` factor to execution still requires the
separate grinding-output and transcript-correspondence premises named in
`V5WorkNormalizedApplicabilityRepair`. -/
theorem conditional_width19_batch_term_meets_100_bit_budget :
    appendixA2Width19Threshold / (FIELD - 1) / 2 ^ 37 ≤ 1 / 2 ^ 100 := by
  rw [appendixA2_threshold_fraction_eq_repaired_batch_term]
  exact width19_fstar_powers_batch_arithmetic_bound.trans (by norm_num)

/-- The actual natural-number cap consumed by `Width19CurveDecodable` also
meets the 100-bit batching budget. -/
theorem conditional_exact_width19_cap_meets_100_bit_budget :
    (appendixA2Width19ChallengeCap : ℝ) / (FIELD - 1) / 2 ^ 37 ≤
      1 / 2 ^ 100 := by
  calc
    (appendixA2Width19ChallengeCap : ℝ) / (FIELD - 1) / 2 ^ 37 ≤
        appendixA2Width19Threshold / (FIELD - 1) / 2 ^ 37 := by
      gcongr
      exact appendixA2_width19_cap_le_threshold
    _ ≤ 1 / 2 ^ 100 := conditional_width19_batch_term_meets_100_bit_budget

/-! ## Audit -/

#print axioms exact_released_dimensions
#print axioms released_proximity_in_johnson_interval
#print axioms exact_initial_gs_list_expression
#print axioms exact_initial_agreement_floor
#print axioms exact_challenge_field_card
#print axioms released_initial_code_is_strict_circle_subspace
#print axioms powers_batch_uses_exact_exponents
#print axioms exact_initial_cat_threshold_and_four_symbol_expansion
#print axioms published_appendixA2_supplies_exact_width19_curve_decodable
#print axioms width19_good_challenges_are_full_field_set_without_zero
#print axioms released_width19_bad_response_count_le_exact_cap
#print axioms released_width19_bad_response_probability_uses_exact_fstar_denominator
#print axioms conditional_width19_batch_term_meets_100_bit_budget
#print axioms conditional_exact_width19_cap_meets_100_bit_budget

end AspisV5Width19S2ApplicabilityAudit
