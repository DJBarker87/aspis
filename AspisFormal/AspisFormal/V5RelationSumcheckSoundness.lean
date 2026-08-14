import Mathlib
import AspisFormal.V5ComponentCRelationRowLinearity

/-!
# Degree-six relation-sumcheck algebra used by Tag 67

Tag 67 reads seven extension-field coefficients in each of four relation
rounds.  For coefficients `c₀, …, c₆`, the verifier checks the arity-four
boundary

`4 * (c₀ + c₄) = incomingClaim`

and then carries the Horner evaluation at the new challenge `alpha` into the
next round.  This file proves the finite-field algebra behind that check.

For one round, compare the seven coefficients accepted by the verifier with
the coefficients of an honest degree-at-most-six polynomial.  If the incoming
claim is wrong relative to the honest polynomial, the accepted boundary makes
the two coefficient vectors different.  Their polynomial difference is
therefore nonzero and can evaluate to zero at at most six field elements.  The
exact mass of that event under a uniform challenge is its finite-set cardinal
divided by the field cardinality, hence at most `6 / |K|`.

The final section counts the corresponding repair event over four rounds in
the actual order.  A round's coefficients may depend on all earlier
challenges, but not on its own challenge or a later one.  At each prefix the
bad set is present only when the claimed polynomial passes the boundary and
the incoming claim is wrong for the honest polynomial.  The union of those
four prefix-indexed sets has mass at most `24 / |K|`.

Before each boundary, Tag 67 also applies two sequential OOD-value mixes.  For
one fixed candidate, the second value may depend on the first mix but not the
second; false data cancel for at most `2 / |K|` of the ordered mix pairs.  A
four-round scalar recurrence proves that a zero terminal discrepancy after an
introduced error must contain either such a mix cancellation or an alpha
repair.  Separately, an explicit adaptive count over all twelve field
challenges shows that the union of the modeled mix and alpha sets has mass at
most `4 * (2 + 6) / |K| = 32 / |K|` for one fixed candidate.  Turning the
recurrence into membership in that union requires the scalar-to-polynomial
discrepancy equations; a conditional lemma states that step, but the deployed
equations are not proved here.

## Deliberate boundary

This is a finite-field theorem about the custom relation sumcheck.  It does not
prove that the deployed Tag-67 callback supplies the modeled coefficients and
claims, that Fiat--Shamir challenges are uniform, or that the committed FRI
oracles encode the honest polynomial.  In particular, it does not establish
the two scalar-to-polynomial discrepancy equations needed to place every
scalar alpha repair in the counted alpha set.  Those implementation,
random-oracle, PCS/FRI, and extraction links remain separate obligations.
-/

namespace AspisV5RelationSumcheckSoundness

open Polynomial

variable {K : Type*}

/-- The seven coefficients serialized for one Tag-67 relation round. -/
abbrev RelationCoefficients (K : Type*) := Fin 7 → K

/-- The degree-at-most-six polynomial represented by the seven serialized
coefficients. -/
noncomputable def relationPolynomial [Semiring K]
    (coefficients : RelationCoefficients K) : K[X] :=
  ∑ degree : Fin 7, C (coefficients degree) * X ^ degree.val

/-- Evaluation of `relationPolynomial` is the same seven-term power sum used
by the maintained relation-row model (and by the optimized Horner evaluator). -/
@[simp]
theorem eval_relationPolynomial [Semiring K]
    (coefficients : RelationCoefficients K) (alpha : K) :
    (relationPolynomial coefficients).eval alpha =
      ∑ degree : Fin 7, coefficients degree * alpha ^ degree.val := by
  simp [relationPolynomial, Polynomial.eval_finsetSum]

/-- Reading a coefficient back from the represented polynomial recovers the
corresponding serialized field element. -/
@[simp]
theorem coeff_relationPolynomial [Semiring K]
    (coefficients : RelationCoefficients K) (degree : Fin 7) :
    (relationPolynomial coefficients).coeff degree.val = coefficients degree := by
  classical
  unfold relationPolynomial
  rw [← lcoeff_apply, map_sum]
  calc
    (∑ other : Fin 7,
        (C (coefficients other) * X ^ other.val).coeff degree.val) =
        (C (coefficients degree) * X ^ degree.val).coeff degree.val := by
      apply Fintype.sum_eq_single degree
      intro other hne
      simp [coeff_C_mul, Fin.ext_iff] at hne ⊢
      omega
    _ = coefficients degree := by simp [coeff_C_mul]

/-- Every represented relation polynomial has degree at most six, including
the zero and lower-degree cases. -/
theorem natDegree_relationPolynomial_le_six [Semiring K]
    (coefficients : RelationCoefficients K) :
    (relationPolynomial coefficients).natDegree ≤ 6 := by
  classical
  unfold relationPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro degree _
  exact (Polynomial.natDegree_C_mul_X_pow_le _ degree.val).trans (by omega)

/-- Equality of represented polynomials forces equality of all seven
coefficient vectors. -/
theorem relationPolynomial_injective [Semiring K]
    [Nontrivial K] : Function.Injective (relationPolynomial (K := K)) := by
  intro left right hpolynomial
  funext degree
  have hcoeff := congrArg (fun p : K[X] => p.coeff degree.val) hpolynomial
  simpa using hcoeff

/-- The exact arity-four root-of-unity boundary used by
`aspis_core::sumcheck::boundary_sum` and the Tag-67 verifier. -/
def relationBoundary [Ring K] (coefficients : RelationCoefficients K) : K :=
  4 * (coefficients 0 + coefficients 4)

/-- The boundary above is definitionally the maintained Component-C
`boundaryLinear` read-off. -/
theorem relationBoundary_eq_componentC_boundary [Field K]
    (coefficients : RelationCoefficients K) :
    relationBoundary coefficients =
      AspisV5ComponentCRelationRowLinearity.boundaryLinear coefficients := by
  rfl

/-- A polynomial accepted against an incoming claim that is wrong for the
honest polynomial cannot equal that honest polynomial. -/
theorem accepted_wrong_boundary_coefficients_ne [Ring K]
    (claimed honest : RelationCoefficients K) (incomingClaim : K)
    (haccepted : relationBoundary claimed = incomingClaim)
    (hwrong : incomingClaim ≠ relationBoundary honest) :
    claimed ≠ honest := by
  intro hequal
  apply hwrong
  rw [← haccepted, hequal]

/-- Under the same boundary hypotheses, the claimed-minus-honest polynomial
is nonzero. -/
theorem accepted_wrong_boundary_difference_ne_zero [Field K]
    (claimed honest : RelationCoefficients K) (incomingClaim : K)
    (haccepted : relationBoundary claimed = incomingClaim)
    (hwrong : incomingClaim ≠ relationBoundary honest) :
    relationPolynomial claimed - relationPolynomial honest ≠ 0 := by
  intro hdifference
  have hpolynomial : relationPolynomial claimed = relationPolynomial honest :=
    sub_eq_zero.mp hdifference
  exact accepted_wrong_boundary_coefficients_ne claimed honest incomingClaim
    haccepted hwrong (relationPolynomial_injective hpolynomial)

/-- The difference of two represented relation polynomials still has degree at
most six. -/
theorem natDegree_relationPolynomial_sub_le_six [Field K]
    (claimed honest : RelationCoefficients K) :
    (relationPolynomial claimed - relationPolynomial honest).natDegree ≤ 6 := by
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le (natDegree_relationPolynomial_le_six claimed)
      (natDegree_relationPolynomial_le_six honest))

section FiniteField

variable [Field K] [Fintype K] [DecidableEq K]

/-- Challenges at which the accepted polynomial and the honest polynomial
carry the same next-round claim. -/
noncomputable def roundCollisionSet
    (claimed honest : RelationCoefficients K) : Finset K :=
  Finset.univ.filter fun alpha =>
    (relationPolynomial claimed).eval alpha =
      (relationPolynomial honest).eval alpha

/-- A wrong incoming claim that passes the Tag-67 boundary can be hidden at the
next Horner evaluation for at most six field challenges. -/
theorem roundCollisionSet_card_le_six
    (claimed honest : RelationCoefficients K) (incomingClaim : K)
    (haccepted : relationBoundary claimed = incomingClaim)
    (hwrong : incomingClaim ≠ relationBoundary honest) :
    (roundCollisionSet claimed honest).card ≤ 6 := by
  let difference := relationPolynomial claimed - relationPolynomial honest
  have hdifference : difference ≠ 0 :=
    accepted_wrong_boundary_difference_ne_zero claimed honest incomingClaim
      haccepted hwrong
  have hsubset : (roundCollisionSet claimed honest).val ⊆ difference.roots := by
    intro alpha halpha
    have heval : (relationPolynomial claimed).eval alpha =
        (relationPolynomial honest).eval alpha := by
      simpa [roundCollisionSet] using halpha
    rw [Polynomial.mem_roots hdifference]
    simp only [Polynomial.IsRoot, difference, Polynomial.eval_sub, sub_eq_zero]
    exact heval
  exact (Polynomial.card_le_degree_of_subset_roots hsubset).trans
    (natDegree_relationPolynomial_sub_le_six claimed honest)

/-- Exact rational mass of the one-round collision event for a uniform field
challenge.  The definition keeps the actual collision-set cardinal rather than
replacing it by six. -/
noncomputable def uniformRoundCollisionProbability
    (claimed honest : RelationCoefficients K) : ℚ :=
  (roundCollisionSet claimed honest).card / Fintype.card K

/-- The exact uniform collision mass is at most `6 / |K|`. -/
theorem uniformRoundCollisionProbability_le
    (claimed honest : RelationCoefficients K) (incomingClaim : K)
    (haccepted : relationBoundary claimed = incomingClaim)
    (hwrong : incomingClaim ≠ relationBoundary honest) :
    uniformRoundCollisionProbability claimed honest ≤
      (6 : ℚ) / Fintype.card K := by
  have hcardNat : 0 < Fintype.card K := Fintype.card_pos_iff.mpr ⟨0⟩
  have hcard : (0 : ℚ) < Fintype.card K := by exact_mod_cast hcardNat
  rw [uniformRoundCollisionProbability, div_le_div_iff_of_pos_right hcard]
  exact_mod_cast roundCollisionSet_card_le_six claimed honest incomingClaim
    haccepted hwrong

/-! ## Four relation rounds in transcript order

The data for a round are functions of its transcript prefix.  Thus round two,
for example, may adapt to `alpha₀` and `alpha₁`, but its seven claimed
coefficients are fixed before `alpha₂` is drawn.  This is the exact ordering
needed to apply the preceding root count separately at every prefix.
-/

/-- Claimed and honest coefficient vectors, and the incoming claim, all fixed
by a round's transcript prefix. -/
structure RoundData (K Prefix : Type*) where
  claimed : Prefix → RelationCoefficients K
  honest : Prefix → RelationCoefficients K
  incomingClaim : Prefix → K

/-- At one prefix, the claimed polynomial passes the deployed boundary while
that same incoming claim is wrong for the honest polynomial. -/
def RoundData.AcceptsWrongBoundaryAt
    {Prefix : Type*} (data : RoundData K Prefix)
    (transcriptPrefix : Prefix) : Prop :=
  relationBoundary (data.claimed transcriptPrefix) =
      data.incomingClaim transcriptPrefix ∧
    data.incomingClaim transcriptPrefix ≠
      relationBoundary (data.honest transcriptPrefix)

/-- One ordered four-round schedule.  Prefixes grow only to the left, matching
the actual order `alpha₀`, `alpha₁`, `alpha₂`, `alpha₃`. -/
structure FourRoundData (K : Type*) where
  round0 : RoundData K Unit
  round1 : RoundData K K
  round2 : RoundData K (K × K)
  round3 : RoundData K ((K × K) × K)

/-- Add one challenge to every prefix, retaining precisely the challenges in
the supplied bad set for that prefix. -/
noncomputable def extendByBadChallenge
    {Prefix Choice : Type*}
    [Fintype Prefix] [DecidableEq Prefix] [DecidableEq Choice]
    (bad : Prefix → Finset Choice) : Finset (Prefix × Choice) :=
  Finset.univ.biUnion fun transcriptPrefix =>
    (bad transcriptPrefix).image fun choice => (transcriptPrefix, choice)

omit [Field K] [Fintype K] [DecidableEq K] in
@[simp]
theorem mem_extendByBadChallenge
    {Prefix Choice : Type*}
    [Fintype Prefix] [DecidableEq Prefix] [DecidableEq Choice]
    (bad : Prefix → Finset Choice) (transcriptPrefix : Prefix) (choice : Choice) :
    (transcriptPrefix, choice) ∈ extendByBadChallenge bad ↔
      choice ∈ bad transcriptPrefix := by
  classical
  simp [extendByBadChallenge]

omit [Field K] [Fintype K] [DecidableEq K] in
/-- Fibre counting for one ordered challenge.  This is the finite counting
step that permits adaptive dependence on the earlier prefix. -/
theorem extendByBadChallenge_card_le
    {Prefix Choice : Type*}
    [Fintype Prefix] [DecidableEq Prefix] [DecidableEq Choice]
    (bad : Prefix → Finset Choice) (bound : ℕ)
    (hbad : ∀ transcriptPrefix, (bad transcriptPrefix).card ≤ bound) :
    (extendByBadChallenge bad).card ≤ Fintype.card Prefix * bound := by
  classical
  calc
    (extendByBadChallenge bad).card ≤
        ∑ transcriptPrefix : Prefix,
          ((bad transcriptPrefix).image fun alpha =>
            (transcriptPrefix, alpha)).card := by
      exact Finset.card_biUnion_le
    _ = ∑ transcriptPrefix : Prefix, (bad transcriptPrefix).card := by
      apply Fintype.sum_congr
      intro transcriptPrefix
      exact Finset.card_image_of_injective _ (Prod.mk_right_injective transcriptPrefix)
    _ ≤ ∑ _transcriptPrefix : Prefix, bound := by
      exact Finset.sum_le_sum fun transcriptPrefix _ => hbad transcriptPrefix
    _ = Fintype.card Prefix * bound := by simp

/-! ## The two OOD mixes before each boundary

Each deployed round updates its running claim in the order

`D → D + m₀ * error₀ → D + m₀ * error₀ + m₁ * error₁(m₀)`.

The first error is fixed before `m₀`.  The second may depend on `m₀` but
is fixed before `m₁`.  For a fixed candidate with `D ≠ 0`, cancellation
occupies at most `2 * |K|` of the `|K|²` pairs: normally there is at most one
`m₁` for each `m₀`; there can additionally be one exceptional `m₀` for
which the discrepancy already vanished and every `m₁` works.

This is intentionally a fixed-candidate theorem.  Applying it to the deployed
FRI list (whose accepted list size is bounded separately) requires a
list-to-evaluation/extraction reduction not proved here.
-/

/-- Roots of one affine equation `constant + challenge * coefficient = 0`. -/
def linearCancellationSet (constant coefficient : K) : Finset K :=
  Finset.univ.filter fun challenge =>
    constant + challenge * coefficient = 0

/-- A nonzero coefficient gives at most one cancelling challenge. -/
theorem linearCancellationSet_card_le_one
    (constant coefficient : K) (hcoefficient : coefficient ≠ 0) :
    (linearCancellationSet constant coefficient).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro left right hleft hright
  have hleft' : constant + left * coefficient = 0 := by
    simpa [linearCancellationSet] using hleft
  have hright' : constant + right * coefficient = 0 := by
    simpa [linearCancellationSet] using hright
  apply mul_right_cancel₀ hcoefficient
  calc
    left * coefficient = (constant + left * coefficient) - constant := by ring
    _ = (constant + right * coefficient) - constant := by rw [hleft', hright']
    _ = right * coefficient := by ring

/-- Values of the first mix that already cancel a nonzero incoming
discrepancy. -/
def firstMixCancellationSet (incomingError firstValueError : K) : Finset K :=
  linearCancellationSet incomingError firstValueError

/-- If the first value error vanishes, a nonzero incoming discrepancy cannot
cancel; otherwise the affine equation has at most one root. -/
theorem firstMixCancellationSet_card_le_one
    (incomingError firstValueError : K) (hincoming : incomingError ≠ 0) :
    (firstMixCancellationSet incomingError firstValueError).card ≤ 1 := by
  by_cases hfirst : firstValueError = 0
  · subst firstValueError
    simp [firstMixCancellationSet, linearCancellationSet, hincoming]
  · exact linearCancellationSet_card_le_one incomingError firstValueError hfirst

/-- Pairs handled by the ordinary case where the second value error is
nonzero, hence at most one `m₁` cancels for each fixed `m₀`. -/
noncomputable def regularSecondMixCancellationSet
    (incomingError firstValueError : K) (secondValueError : K → K) :
    Finset (K × K) :=
  extendByBadChallenge fun firstMix =>
    if secondValueError firstMix = 0 then ∅
    else linearCancellationSet
      (incomingError + firstMix * firstValueError)
      (secondValueError firstMix)

/-- The ordinary second-mix case has at most `|K|` pairs. -/
theorem regularSecondMixCancellationSet_card_le
    (incomingError firstValueError : K) (secondValueError : K → K) :
    (regularSecondMixCancellationSet incomingError firstValueError
      secondValueError).card ≤ Fintype.card K := by
  have hcard :
      (regularSecondMixCancellationSet incomingError firstValueError
        secondValueError).card ≤ Fintype.card K * 1 := by
    apply extendByBadChallenge_card_le
    intro firstMix
    by_cases hsecond : secondValueError firstMix ≠ 0
    · simpa [hsecond] using
        linearCancellationSet_card_le_one
          (incomingError + firstMix * firstValueError)
          (secondValueError firstMix) hsecond
    · have hzero : secondValueError firstMix = 0 := not_ne_iff.mp hsecond
      simp [hzero]
  simpa using hcard

/-! ### False OOD data introduced at either stage -/

/-- A first-stage affine cancellation has at most one root whenever the
incoming and first-value discrepancies are not both zero. -/
theorem firstMixCancellationSet_card_le_one_of_nontrivial
    (incomingError firstValueError : K)
    (hnontrivial : incomingError ≠ 0 ∨ firstValueError ≠ 0) :
    (firstMixCancellationSet incomingError firstValueError).card ≤ 1 := by
  rcases hnontrivial with hincoming | hfirst
  · exact firstMixCancellationSet_card_le_one
      incomingError firstValueError hincoming
  · exact linearCancellationSet_card_le_one
      incomingError firstValueError hfirst

/-- First-mix roots retained only when the incoming/first-value discrepancy
pair is nontrivial. -/
noncomputable def falseFirstMixCancellationSet
    (incomingError firstValueError : K) : Finset K := by
  classical
  exact if incomingError ≠ 0 ∨ firstValueError ≠ 0 then
    firstMixCancellationSet incomingError firstValueError
  else ∅

theorem falseFirstMixCancellationSet_card_le_one
    (incomingError firstValueError : K) :
    (falseFirstMixCancellationSet incomingError firstValueError).card ≤ 1 := by
  by_cases hnontrivial : incomingError ≠ 0 ∨ firstValueError ≠ 0
  · simpa [falseFirstMixCancellationSet, hnontrivial] using
      firstMixCancellationSet_card_le_one_of_nontrivial
        incomingError firstValueError hnontrivial
  · simp [falseFirstMixCancellationSet, hnontrivial]

/-- Exact event that some staged discrepancy is nonzero but the two sequential
mixes leave a zero discrepancy. -/
def falseSequentialTwoMixCancellationSet
    (incomingError firstValueError : K) (secondValueError : K → K) :
    Finset (K × K) :=
  Finset.univ.filter fun mixes =>
    (incomingError + mixes.1 * firstValueError +
      mixes.2 * secondValueError mixes.1 = 0) ∧
    (incomingError ≠ 0 ∨ firstValueError ≠ 0 ∨
      secondValueError mixes.1 ≠ 0)

noncomputable def falseExceptionalFirstMixEvent
    (incomingError firstValueError : K) : Finset (K × K) :=
  falseFirstMixCancellationSet incomingError firstValueError ×ˢ
    (Finset.univ : Finset K)

/-- For one fixed candidate, false data introduced before either mix can
cancel for at most `2 * |K|` ordered mix pairs.  The second value error may
depend on the first mix. -/
theorem falseSequentialTwoMixCancellationSet_card_le
    (incomingError firstValueError : K) (secondValueError : K → K) :
    (falseSequentialTwoMixCancellationSet incomingError firstValueError
      secondValueError).card ≤ 2 * Fintype.card K := by
  classical
  let regular := regularSecondMixCancellationSet incomingError firstValueError
    secondValueError
  let exceptional := falseExceptionalFirstMixEvent incomingError firstValueError
  have hsubset :
      falseSequentialTwoMixCancellationSet incomingError firstValueError
          secondValueError ⊆ regular ∪ exceptional := by
    intro mixes hmixes
    have hdata :
        (incomingError + mixes.1 * firstValueError +
          mixes.2 * secondValueError mixes.1 = 0) ∧
        (incomingError ≠ 0 ∨ firstValueError ≠ 0 ∨
          secondValueError mixes.1 ≠ 0) := by
      simpa [falseSequentialTwoMixCancellationSet] using hmixes
    by_cases hsecond : secondValueError mixes.1 ≠ 0
    · apply Finset.mem_union_left
      change mixes ∈ regularSecondMixCancellationSet incomingError
        firstValueError secondValueError
      unfold regularSecondMixCancellationSet
      rw [mem_extendByBadChallenge]
      simpa [hsecond, linearCancellationSet] using hdata.1
    · apply Finset.mem_union_right
      have hsecondZero : secondValueError mixes.1 = 0 := not_ne_iff.mp hsecond
      have hfirst : incomingError + mixes.1 * firstValueError = 0 := by
        simpa [hsecondZero] using hdata.1
      have hnontrivial : incomingError ≠ 0 ∨ firstValueError ≠ 0 := by
        rcases hdata.2 with hincoming | hfirstValue | hsecondValue
        · exact Or.inl hincoming
        · exact Or.inr hfirstValue
        · exact False.elim (hsecond hsecondValue)
      change mixes ∈ falseExceptionalFirstMixEvent incomingError firstValueError
      simp [falseExceptionalFirstMixEvent, falseFirstMixCancellationSet,
        hnontrivial, firstMixCancellationSet, linearCancellationSet, hfirst]
  have hregular : regular.card ≤ Fintype.card K := by
    exact regularSecondMixCancellationSet_card_le incomingError firstValueError
      secondValueError
  have hfirst := falseFirstMixCancellationSet_card_le_one
    incomingError firstValueError
  have hexceptional : exceptional.card ≤ Fintype.card K := by
    dsimp [exceptional, falseExceptionalFirstMixEvent]
    rw [Finset.card_product, Finset.card_univ]
    exact (Nat.mul_le_mul_right _ hfirst).trans_eq (one_mul _)
  calc
    (falseSequentialTwoMixCancellationSet incomingError firstValueError
        secondValueError).card ≤ (regular ∪ exceptional).card :=
      Finset.card_le_card hsubset
    _ ≤ regular.card + exceptional.card := Finset.card_union_le _ _
    _ ≤ Fintype.card K + Fintype.card K := Nat.add_le_add hregular hexceptional
    _ = 2 * Fintype.card K := by omega

noncomputable def uniformFalseSequentialTwoMixCancellationProbability
    (incomingError firstValueError : K) (secondValueError : K → K) : ℚ :=
  (falseSequentialTwoMixCancellationSet incomingError firstValueError
    secondValueError).card / Fintype.card K ^ 2

/-- Exact uniform fixed-candidate false-and-cancel mass is at most `2 / |K|`.
No FRI list factor or Fiat--Shamir reduction is included. -/
theorem uniformFalseSequentialTwoMixCancellationProbability_le
    (incomingError firstValueError : K) (secondValueError : K → K) :
    uniformFalseSequentialTwoMixCancellationProbability incomingError
        firstValueError secondValueError ≤
      (2 : ℚ) / Fintype.card K := by
  let fieldCard := Fintype.card K
  have hcardNat : 0 < fieldCard := Fintype.card_pos_iff.mpr ⟨0⟩
  have hcard : (0 : ℚ) < fieldCard := by exact_mod_cast hcardNat
  have hevent := falseSequentialTwoMixCancellationSet_card_le
    incomingError firstValueError secondValueError
  unfold uniformFalseSequentialTwoMixCancellationProbability
  change ((falseSequentialTwoMixCancellationSet incomingError firstValueError
      secondValueError).card : ℚ) / (fieldCard : ℚ) ^ 2 ≤
    2 / (fieldCard : ℚ)
  rw [div_le_iff₀ (pow_pos hcard 2)]
  have heventQ :
      ((falseSequentialTwoMixCancellationSet incomingError firstValueError
        secondValueError).card : ℚ) ≤ 2 * (fieldCard : ℚ) := by
    exact_mod_cast hevent
  calc
    ((falseSequentialTwoMixCancellationSet incomingError firstValueError
        secondValueError).card : ℚ) ≤ 2 * (fieldCard : ℚ) := heventQ
    _ = (2 / (fieldCard : ℚ)) * (fieldCard : ℚ) ^ 2 := by
      field_simp

/-! ## Deterministic four-round discrepancy recurrence

This scalar recurrence isolates the logical step behind a fixed-candidate
union.  A nonzero discrepancy either disappears during the two OOD mixes or
survives to the alpha evaluation.  If it survives and the next carried
discrepancy is zero, alpha repaired it.  Otherwise it remains active in the
next round.  Therefore a zero terminal discrepancy after any initial or newly
introduced error forces one of those two repair events in some round.

Connecting these scalar errors to the Tag-67 FRI list, accepted openings, and
the actual callback remains outside this theorem.
-/

/-- Four-round scalar trace.  The second OOD error may depend on the first mix,
matching the deployed order `value₀, mix₀, value₁, mix₁`. -/
structure FourRoundDiscrepancyTrace (K : Type*) where
  before : Fin 5 → K
  firstValueError : Fin 4 → K
  secondValueError : Fin 4 → K → K
  firstMix : Fin 4 → K
  secondMix : Fin 4 → K

/-- Discrepancy immediately after both OOD mixes in one round. -/
def FourRoundDiscrepancyTrace.afterMix
    (trace : FourRoundDiscrepancyTrace K) (round : Fin 4) : K :=
  trace.before round.castSucc +
    trace.firstMix round * trace.firstValueError round +
    trace.secondMix round * trace.secondValueError round (trace.firstMix round)

/-- Some false scalar data are active during this round. -/
def FourRoundDiscrepancyTrace.NontrivialRound
    (trace : FourRoundDiscrepancyTrace K) (round : Fin 4) : Prop :=
  trace.before round.castSucc ≠ 0 ∨
    trace.firstValueError round ≠ 0 ∨
    trace.secondValueError round (trace.firstMix round) ≠ 0

/-- False data become zero during the two sequential mixes. -/
def FourRoundDiscrepancyTrace.MixCancellation
    (trace : FourRoundDiscrepancyTrace K) (round : Fin 4) : Prop :=
  trace.NontrivialRound round ∧ trace.afterMix round = 0

/-- A nonzero post-mix discrepancy becomes zero at the alpha carry.  The
equation connecting `before round.succ` to the two polynomial evaluations is
an explicit model/implementation premise outside this scalar definition. -/
def FourRoundDiscrepancyTrace.AlphaRepair
    (trace : FourRoundDiscrepancyTrace K) (round : Fin 4) : Prop :=
  trace.afterMix round ≠ 0 ∧ trace.before round.succ = 0

/-- A false input exists initially or is introduced by one of the OOD values. -/
def FourRoundDiscrepancyTrace.HasInitialOrIntroducedError
    (trace : FourRoundDiscrepancyTrace K) : Prop :=
  trace.before 0 ≠ 0 ∨
    ∃ round : Fin 4,
      trace.firstValueError round ≠ 0 ∨
        trace.secondValueError round (trace.firstMix round) ≠ 0

/-- The scalar mix-cancellation event is exactly membership in the fixed-
candidate finite set proved above. -/
theorem FourRoundDiscrepancyTrace.mixCancellation_iff_mem
    (trace : FourRoundDiscrepancyTrace K) (round : Fin 4) :
    trace.MixCancellation round ↔
      (trace.firstMix round, trace.secondMix round) ∈
        falseSequentialTwoMixCancellationSet
          (trace.before round.castSucc)
          (trace.firstValueError round)
          (trace.secondValueError round) := by
  simp [FourRoundDiscrepancyTrace.MixCancellation,
    FourRoundDiscrepancyTrace.NontrivialRound,
    FourRoundDiscrepancyTrace.afterMix,
    falseSequentialTwoMixCancellationSet, and_comm]

omit [Fintype K] [DecidableEq K] in
/-- Any initial/introduced error makes at least one round nontrivial. -/
theorem FourRoundDiscrepancyTrace.exists_nontrivialRound
    (trace : FourRoundDiscrepancyTrace K)
    (hfalse : trace.HasInitialOrIntroducedError) :
    ∃ round : Fin 4, trace.NontrivialRound round := by
  rcases hfalse with hinitial | ⟨round, hintroduced⟩
  · refine ⟨0, Or.inl ?_⟩
    simpa using hinitial
  · refine ⟨round, Or.inr hintroduced⟩

omit [Fintype K] [DecidableEq K] in
/-- With a zero terminal discrepancy, every initial/introduced error forces a
mix cancellation or an alpha repair in one of the four rounds.  This is a
deterministic statement; no probability, random-oracle, FRI-list, or deployed
callback claim is hidden in it. -/
theorem FourRoundDiscrepancyTrace.terminal_zero_has_repair
    (trace : FourRoundDiscrepancyTrace K)
    (hterminal : trace.before 4 = 0)
    (hfalse : trace.HasInitialOrIntroducedError) :
    ∃ round : Fin 4,
      trace.MixCancellation round ∨ trace.AlphaRepair round := by
  have hround3 (hactive : trace.NontrivialRound (3 : Fin 4)) :
      ∃ round : Fin 4,
        trace.MixCancellation round ∨ trace.AlphaRepair round := by
    by_cases hmixed : trace.afterMix (3 : Fin 4) = 0
    · exact ⟨3, Or.inl ⟨hactive, hmixed⟩⟩
    · refine ⟨3, Or.inr ⟨hmixed, ?_⟩⟩
      simpa using hterminal
  have hround2 (hactive : trace.NontrivialRound (2 : Fin 4)) :
      ∃ round : Fin 4,
        trace.MixCancellation round ∨ trace.AlphaRepair round := by
    by_cases hmixed : trace.afterMix (2 : Fin 4) = 0
    · exact ⟨2, Or.inl ⟨hactive, hmixed⟩⟩
    · by_cases hnext : trace.before (2 : Fin 4).succ = 0
      · exact ⟨2, Or.inr ⟨hmixed, hnext⟩⟩
      · apply hround3
        exact Or.inl (by simpa using hnext)
  have hround1 (hactive : trace.NontrivialRound (1 : Fin 4)) :
      ∃ round : Fin 4,
        trace.MixCancellation round ∨ trace.AlphaRepair round := by
    by_cases hmixed : trace.afterMix (1 : Fin 4) = 0
    · exact ⟨1, Or.inl ⟨hactive, hmixed⟩⟩
    · by_cases hnext : trace.before (1 : Fin 4).succ = 0
      · exact ⟨1, Or.inr ⟨hmixed, hnext⟩⟩
      · apply hround2
        exact Or.inl (by simpa using hnext)
  have hround0 (hactive : trace.NontrivialRound (0 : Fin 4)) :
      ∃ round : Fin 4,
        trace.MixCancellation round ∨ trace.AlphaRepair round := by
    by_cases hmixed : trace.afterMix (0 : Fin 4) = 0
    · exact ⟨0, Or.inl ⟨hactive, hmixed⟩⟩
    · by_cases hnext : trace.before (0 : Fin 4).succ = 0
      · exact ⟨0, Or.inr ⟨hmixed, hnext⟩⟩
      · apply hround1
        exact Or.inl (by simpa using hnext)
  obtain ⟨round, hactive⟩ := trace.exists_nontrivialRound hfalse
  fin_cases round
  · exact hround0 hactive
  · exact hround1 hactive
  · exact hround2 hactive
  · exact hround3 hactive

omit [DecidableEq K] in
/-- Fixed-candidate finite-field arithmetic only: four rounds of a
`2 / |K|` two-mix event plus a `6 / |K|` alpha event sum to `32 / |K|`.
This equality is not installed in the deployed soundness ledger because the
FRI-list, Fiat--Shamir, and callback inclusion are still unproved. -/
theorem fixedCandidate_four_round_mix_plus_alpha_arithmetic :
    4 * ((2 : ℚ) / Fintype.card K + (6 : ℚ) / Fintype.card K) =
      (32 : ℚ) / Fintype.card K := by
  have hcardNat : 0 < Fintype.card K := Fintype.card_pos_iff.mpr ⟨0⟩
  have hcard : (Fintype.card K : ℚ) ≠ 0 := by exact_mod_cast hcardNat.ne'
  field_simp
  norm_num

/-- Four uniformly sampled challenges, grouped by their sequential prefixes. -/
abbrev FourChallenges (K : Type*) := ((K × K) × K) × K

/-- At one prefix, retain the alpha collisions only when the claimed
polynomial is accepted at the boundary and the incoming claim is wrong for the
honest polynomial.  Otherwise this prefix contributes no bad challenges. -/
noncomputable def RoundData.wrongIncomingCollisionSet
    {Prefix : Type*} (data : RoundData K Prefix)
    (transcriptPrefix : Prefix) : Finset K :=
  by
    classical
    exact if data.AcceptsWrongBoundaryAt transcriptPrefix then
      roundCollisionSet (data.claimed transcriptPrefix)
        (data.honest transcriptPrefix)
    else ∅

/-- Every prefix-indexed wrong-incoming repair set has at most six elements,
without requiring the incoming claim to be wrong at unrelated prefixes. -/
theorem RoundData.wrongIncomingCollisionSet_card_le_six
    {Prefix : Type*} (data : RoundData K Prefix)
    (transcriptPrefix : Prefix) :
    (data.wrongIncomingCollisionSet transcriptPrefix).card ≤ 6 := by
  by_cases hwrong : data.AcceptsWrongBoundaryAt transcriptPrefix
  · simp only [RoundData.wrongIncomingCollisionSet, hwrong, if_pos]
    exact roundCollisionSet_card_le_six
      (data.claimed transcriptPrefix) (data.honest transcriptPrefix)
      (data.incomingClaim transcriptPrefix) hwrong.1 hwrong.2
  · simp [RoundData.wrongIncomingCollisionSet, hwrong]

/-- If an accepted wrong incoming claim is repaired by equality at alpha, that
alpha belongs to the prefix-indexed bad set. -/
theorem RoundData.mem_wrongIncomingCollisionSet
    {Prefix : Type*} (data : RoundData K Prefix)
    (transcriptPrefix : Prefix) (alpha : K)
    (haccepted : relationBoundary (data.claimed transcriptPrefix) =
      data.incomingClaim transcriptPrefix)
    (hwrong : data.incomingClaim transcriptPrefix ≠
      relationBoundary (data.honest transcriptPrefix))
    (hevaluation : (relationPolynomial (data.claimed transcriptPrefix)).eval alpha =
      (relationPolynomial (data.honest transcriptPrefix)).eval alpha) :
    alpha ∈ data.wrongIncomingCollisionSet transcriptPrefix := by
  have hp : data.AcceptsWrongBoundaryAt transcriptPrefix :=
    ⟨haccepted, hwrong⟩
  have hcollision : alpha ∈
      roundCollisionSet (data.claimed transcriptPrefix)
        (data.honest transcriptPrefix) := by
    simp only [roundCollisionSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hevaluation
  simpa only [RoundData.wrongIncomingCollisionSet, hp, if_pos] using hcollision

/-- Conditional scalar-to-polynomial bridge for one alpha repair.  If the
post-mix scalar is exactly the incoming-minus-honest-boundary discrepancy and
the next scalar is exactly the claimed-minus-honest evaluation discrepancy,
then a nonzero-to-zero alpha repair belongs to the prefix-local degree-six
collision set.  Proving these two equations for the deployed FRI candidate is
still external. -/
theorem RoundData.mem_wrongIncomingCollisionSet_of_discrepancy_equations
    {Prefix : Type*} (data : RoundData K Prefix)
    (transcriptPrefix : Prefix) (alpha mixedError nextError : K)
    (haccepted : relationBoundary (data.claimed transcriptPrefix) =
      data.incomingClaim transcriptPrefix)
    (hboundaryError : mixedError = data.incomingClaim transcriptPrefix -
      relationBoundary (data.honest transcriptPrefix))
    (hevaluationError : nextError =
      (relationPolynomial (data.claimed transcriptPrefix)).eval alpha -
        (relationPolynomial (data.honest transcriptPrefix)).eval alpha)
    (hrepair : mixedError ≠ 0 ∧ nextError = 0) :
    alpha ∈ data.wrongIncomingCollisionSet transcriptPrefix := by
  have hwrong : data.incomingClaim transcriptPrefix ≠
      relationBoundary (data.honest transcriptPrefix) := by
    intro hequal
    apply hrepair.1
    rw [hboundaryError, hequal, sub_self]
  have hevaluation :
      (relationPolynomial (data.claimed transcriptPrefix)).eval alpha =
        (relationPolynomial (data.honest transcriptPrefix)).eval alpha := by
    apply sub_eq_zero.mp
    rw [← hevaluationError, hrepair.2]
  exact data.mem_wrongIncomingCollisionSet transcriptPrefix alpha
    haccepted hwrong hevaluation

noncomputable def round0CollisionChallenges (data : FourRoundData K) : Finset K :=
  data.round0.wrongIncomingCollisionSet ()

noncomputable def round1CollisionPrefixes (data : FourRoundData K) : Finset (K × K) :=
  extendByBadChallenge fun alpha0 =>
    data.round1.wrongIncomingCollisionSet alpha0

noncomputable def round2CollisionPrefixes (data : FourRoundData K) :
    Finset ((K × K) × K) :=
  extendByBadChallenge fun transcriptPrefix =>
    data.round2.wrongIncomingCollisionSet transcriptPrefix

noncomputable def round3CollisionChallenges (data : FourRoundData K) :
    Finset (FourChallenges K) :=
  extendByBadChallenge fun transcriptPrefix =>
    data.round3.wrongIncomingCollisionSet transcriptPrefix

/-- Lift each round's wrong-incoming collision prefixes through arbitrary later
challenges.  This union counts the four prefix-indexed repair events; showing
that an alpha repair from the scalar recurrence is equality of the claimed and
honest polynomial evaluations in this finite set, and then connecting that
model to Tag 67 and the FRI list, remain separate obligations. -/
noncomputable def fourRoundCollisionEvent (data : FourRoundData K) :
    Finset (FourChallenges K) :=
  let event0 :=
    (((round0CollisionChallenges data ×ˢ (Finset.univ : Finset K)) ×ˢ
        (Finset.univ : Finset K)) ×ˢ (Finset.univ : Finset K))
  let event1 :=
    ((round1CollisionPrefixes data ×ˢ (Finset.univ : Finset K)) ×ˢ
      (Finset.univ : Finset K))
  let event2 :=
    round2CollisionPrefixes data ×ˢ (Finset.univ : Finset K)
  let event3 := round3CollisionChallenges data
  ((event0 ∪ event1) ∪ event2) ∪ event3

/-- Four prefix-indexed wrong-claim repairs occupy at most
`24 * |K|³` of the `|K|⁴` challenge tuples.  Each round contributes at
most `6 * |K|³`; prior challenges select that round's polynomial and later
challenges are unrestricted. -/
theorem fourRoundCollisionEvent_card_le
    (data : FourRoundData K) :
    (fourRoundCollisionEvent data).card ≤
      24 * Fintype.card K ^ 3 := by
  classical
  let fieldCard := Fintype.card K
  have h0 : (round0CollisionChallenges data).card ≤ 6 := by
    exact data.round0.wrongIncomingCollisionSet_card_le_six ()
  have h1 : (round1CollisionPrefixes data).card ≤ fieldCard * 6 := by
    apply extendByBadChallenge_card_le
    intro alpha0
    exact data.round1.wrongIncomingCollisionSet_card_le_six alpha0
  have h2 : (round2CollisionPrefixes data).card ≤ fieldCard ^ 2 * 6 := by
    have hprefix : Fintype.card (K × K) = fieldCard ^ 2 := by
      simp [fieldCard, pow_two]
    rw [← hprefix]
    apply extendByBadChallenge_card_le
    intro transcriptPrefix
    exact data.round2.wrongIncomingCollisionSet_card_le_six transcriptPrefix
  have h3 : (round3CollisionChallenges data).card ≤ fieldCard ^ 3 * 6 := by
    have hprefix : Fintype.card ((K × K) × K) = fieldCard ^ 3 := by
      simp [fieldCard, pow_succ]
    rw [← hprefix]
    apply extendByBadChallenge_card_le
    intro transcriptPrefix
    exact data.round3.wrongIncomingCollisionSet_card_le_six transcriptPrefix
  let event0 : Finset (FourChallenges K) :=
    (((round0CollisionChallenges data ×ˢ (Finset.univ : Finset K)) ×ˢ
        (Finset.univ : Finset K)) ×ˢ (Finset.univ : Finset K))
  let event1 : Finset (FourChallenges K) :=
    ((round1CollisionPrefixes data ×ˢ (Finset.univ : Finset K)) ×ˢ
      (Finset.univ : Finset K))
  let event2 : Finset (FourChallenges K) :=
    round2CollisionPrefixes data ×ˢ (Finset.univ : Finset K)
  let event3 : Finset (FourChallenges K) := round3CollisionChallenges data
  have hevent0 : event0.card ≤ 6 * fieldCard ^ 3 := by
    dsimp [event0]
    simp only [Finset.card_product, Finset.card_univ]
    calc
      (round0CollisionChallenges data).card * fieldCard * fieldCard * fieldCard =
          (round0CollisionChallenges data).card * fieldCard ^ 3 := by ring
      _ ≤ 6 * fieldCard ^ 3 := Nat.mul_le_mul_right _ h0
  have hevent1 : event1.card ≤ 6 * fieldCard ^ 3 := by
    dsimp [event1]
    simp only [Finset.card_product, Finset.card_univ]
    calc
      (round1CollisionPrefixes data).card * fieldCard * fieldCard ≤
          (fieldCard * 6) * fieldCard * fieldCard := by
            exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)
      _ = 6 * fieldCard ^ 3 := by ring
  have hevent2 : event2.card ≤ 6 * fieldCard ^ 3 := by
    dsimp [event2]
    simp only [Finset.card_product, Finset.card_univ]
    calc
      (round2CollisionPrefixes data).card * fieldCard ≤
          (fieldCard ^ 2 * 6) * fieldCard := Nat.mul_le_mul_right _ h2
      _ = 6 * fieldCard ^ 3 := by ring
  have hevent3 : event3.card ≤ 6 * fieldCard ^ 3 := by
    dsimp [event3]
    exact h3.trans_eq (by ring)
  change (((event0 ∪ event1) ∪ event2) ∪ event3).card ≤ _
  have h01 := Finset.card_union_le event0 event1
  have h012 := Finset.card_union_le (event0 ∪ event1) event2
  have h0123 := Finset.card_union_le ((event0 ∪ event1) ∪ event2) event3
  dsimp [fieldCard] at hevent0 hevent1 hevent2 hevent3 ⊢
  omega

/-- Exact rational mass of the modeled four-round event under four independent
uniform field challenges. -/
noncomputable def uniformFourRoundCollisionProbability
    (data : FourRoundData K) : ℚ :=
  (fourRoundCollisionEvent data).card / Fintype.card K ^ 4

/-- The four prefix-indexed repair events have uniform union mass at most
`24 / |K|`.  This is not by itself a deployed relation/FRI soundness theorem. -/
theorem uniformFourRoundCollisionProbability_le
    (data : FourRoundData K) :
    uniformFourRoundCollisionProbability data ≤
      (24 : ℚ) / Fintype.card K := by
  let fieldCard := Fintype.card K
  have hcardNat : 0 < fieldCard := Fintype.card_pos_iff.mpr ⟨0⟩
  have hcard : (0 : ℚ) < fieldCard := by exact_mod_cast hcardNat
  have hevent := fourRoundCollisionEvent_card_le data
  unfold uniformFourRoundCollisionProbability
  change ((fourRoundCollisionEvent data).card : ℚ) / (fieldCard : ℚ) ^ 4 ≤
    24 / (fieldCard : ℚ)
  rw [div_le_iff₀ (pow_pos hcard 4)]
  have heventQ : ((fourRoundCollisionEvent data).card : ℚ) ≤
      24 * (fieldCard : ℚ) ^ 3 := by
    exact_mod_cast hevent
  calc
    ((fourRoundCollisionEvent data).card : ℚ) ≤
        24 * (fieldCard : ℚ) ^ 3 := heventQ
    _ = (24 / (fieldCard : ℚ)) * (fieldCard : ℚ) ^ 4 := by
      field_simp

/-! ## Fixed-candidate count over all twelve relation challenges

One relation round samples two OOD mixes and then alpha.  Across four rounds
there are twelve field challenges.  The structures below enforce the
interactive dependency order:

* all round data may depend on completed earlier rounds;
* the second OOD-value error may additionally depend on the current first mix;
* the claimed/honest relation polynomials may depend on both current mixes;
* none of those objects depends on the current alpha or any later challenge.

The exact fixed-candidate mix set contributes at most `2 * |K|` pairs and its
alpha lift contributes at most `2 * |K|²` triples.  The prefix-local
degree-six set contributes at most `6 * |K|²` triples.  Thus one round has at
most `8 * |K|²` repair triples, and the four-round adaptive union has at most
`32 * |K|¹¹` of the `|K|¹²` full challenge tuples.

This still does not union over a FRI candidate list or prove that deployed
Tag-67 false acceptance is contained in this fixed-candidate event.
-/

/-- Two ordered OOD mixes followed by alpha. -/
abbrev RelationRoundChallenges (K : Type*) := (K × K) × K

/-- Algebraic data for one fixed candidate at every earlier-round prefix. -/
structure AdaptiveFixedCandidateRound (K Prefix : Type*) where
  incomingError : Prefix → K
  firstValueError : Prefix → K
  secondValueError : Prefix → K → K
  relation : RoundData K (Prefix × (K × K))

/-- Exact false-and-cancel mix pairs for a fixed earlier-round prefix. -/
def AdaptiveFixedCandidateRound.mixRepairPairs
    {Prefix : Type*} (data : AdaptiveFixedCandidateRound K Prefix)
    (transcriptPrefix : Prefix) : Finset (K × K) :=
  falseSequentialTwoMixCancellationSet
    (data.incomingError transcriptPrefix)
    (data.firstValueError transcriptPrefix)
    (data.secondValueError transcriptPrefix)

/-- Alpha repair triples, with relation polynomials selected after both mixes
but before alpha. -/
noncomputable def AdaptiveFixedCandidateRound.alphaRepairTriples
    {Prefix : Type*} (data : AdaptiveFixedCandidateRound K Prefix)
    (transcriptPrefix : Prefix) : Finset (RelationRoundChallenges K) :=
  extendByBadChallenge fun mixes : K × K =>
    data.relation.wrongIncomingCollisionSet (transcriptPrefix, mixes)

/-- Union of mix-cancellation and alpha-repair triples in one round. -/
noncomputable def AdaptiveFixedCandidateRound.repairTriples
    {Prefix : Type*} (data : AdaptiveFixedCandidateRound K Prefix)
    (transcriptPrefix : Prefix) : Finset (RelationRoundChallenges K) :=
  (data.mixRepairPairs transcriptPrefix ×ˢ (Finset.univ : Finset K)) ∪
    data.alphaRepairTriples transcriptPrefix

/-- One fixed-candidate round has at most `8 * |K|²` repair triples. -/
theorem AdaptiveFixedCandidateRound.repairTriples_card_le
    {Prefix : Type*} (data : AdaptiveFixedCandidateRound K Prefix)
    (transcriptPrefix : Prefix) :
    (data.repairTriples transcriptPrefix).card ≤
      8 * Fintype.card K ^ 2 := by
  let fieldCard := Fintype.card K
  have hmix : (data.mixRepairPairs transcriptPrefix).card ≤ 2 * fieldCard := by
    exact falseSequentialTwoMixCancellationSet_card_le
      (data.incomingError transcriptPrefix)
      (data.firstValueError transcriptPrefix)
      (data.secondValueError transcriptPrefix)
  have hmixLift :
      (data.mixRepairPairs transcriptPrefix ×ˢ
        (Finset.univ : Finset K)).card ≤ 2 * fieldCard ^ 2 := by
    rw [Finset.card_product, Finset.card_univ]
    calc
      (data.mixRepairPairs transcriptPrefix).card * fieldCard ≤
          (2 * fieldCard) * fieldCard := Nat.mul_le_mul_right _ hmix
      _ = 2 * fieldCard ^ 2 := by ring
  have halpha : (data.alphaRepairTriples transcriptPrefix).card ≤
      fieldCard ^ 2 * 6 := by
    have hpairs : Fintype.card (K × K) = fieldCard ^ 2 := by
      simp [fieldCard, pow_two]
    rw [← hpairs]
    apply extendByBadChallenge_card_le
    intro mixes
    exact data.relation.wrongIncomingCollisionSet_card_le_six
      (transcriptPrefix, mixes)
  unfold AdaptiveFixedCandidateRound.repairTriples
  have hunion := Finset.card_union_le
    (data.mixRepairPairs transcriptPrefix ×ˢ (Finset.univ : Finset K))
    (data.alphaRepairTriples transcriptPrefix)
  dsimp [fieldCard] at hmixLift halpha ⊢
  omega

/-- Four sequential relation rounds.  Each field may depend on all completed
round challenge triples and no future triple. -/
structure AdaptiveFixedCandidateFourRounds (K : Type*) where
  round0 : AdaptiveFixedCandidateRound K Unit
  round1 : AdaptiveFixedCandidateRound K (RelationRoundChallenges K)
  round2 : AdaptiveFixedCandidateRound K
    (RelationRoundChallenges K × RelationRoundChallenges K)
  round3 : AdaptiveFixedCandidateRound K
    ((RelationRoundChallenges K × RelationRoundChallenges K) ×
      RelationRoundChallenges K)

/-- All twelve challenges, grouped into their four sequential round triples. -/
abbrev TwelveRelationChallenges (K : Type*) :=
  ((RelationRoundChallenges K × RelationRoundChallenges K) ×
    RelationRoundChallenges K) × RelationRoundChallenges K

noncomputable def round0RepairBlocks
    (data : AdaptiveFixedCandidateFourRounds K) :
    Finset (RelationRoundChallenges K) :=
  data.round0.repairTriples ()

noncomputable def round1RepairPrefixes
    (data : AdaptiveFixedCandidateFourRounds K) :
    Finset (RelationRoundChallenges K × RelationRoundChallenges K) :=
  extendByBadChallenge fun round0 => data.round1.repairTriples round0

noncomputable def round2RepairPrefixes
    (data : AdaptiveFixedCandidateFourRounds K) :
    Finset ((RelationRoundChallenges K × RelationRoundChallenges K) ×
      RelationRoundChallenges K) :=
  extendByBadChallenge fun earlier => data.round2.repairTriples earlier

noncomputable def round3RepairChallenges
    (data : AdaptiveFixedCandidateFourRounds K) :
    Finset (TwelveRelationChallenges K) :=
  extendByBadChallenge fun earlier => data.round3.repairTriples earlier

/-- Lift every round's repair prefixes through arbitrary later round triples. -/
noncomputable def adaptiveFixedCandidateRepairEvent
    (data : AdaptiveFixedCandidateFourRounds K) :
    Finset (TwelveRelationChallenges K) := by
  classical
  let event0 :=
    (((round0RepairBlocks data ×ˢ
        (Finset.univ : Finset (RelationRoundChallenges K))) ×ˢ
      (Finset.univ : Finset (RelationRoundChallenges K))) ×ˢ
      (Finset.univ : Finset (RelationRoundChallenges K)))
  let event1 :=
    ((round1RepairPrefixes data ×ˢ
      (Finset.univ : Finset (RelationRoundChallenges K))) ×ˢ
      (Finset.univ : Finset (RelationRoundChallenges K)))
  let event2 := round2RepairPrefixes data ×ˢ
    (Finset.univ : Finset (RelationRoundChallenges K))
  let event3 := round3RepairChallenges data
  exact ((event0 ∪ event1) ∪ event2) ∪ event3

/-- Adaptive fixed-candidate count over all twelve challenges:
`|bad| ≤ 32 * |K|¹¹`. -/
theorem adaptiveFixedCandidateRepairEvent_card_le
    (data : AdaptiveFixedCandidateFourRounds K) :
    (adaptiveFixedCandidateRepairEvent data).card ≤
      32 * Fintype.card K ^ 11 := by
  classical
  let fieldCard := Fintype.card K
  let blockCard := Fintype.card (RelationRoundChallenges K)
  have hblock : blockCard = fieldCard ^ 3 := by
    simp [blockCard, fieldCard]
    ring
  have h0 : (round0RepairBlocks data).card ≤ 8 * fieldCard ^ 2 :=
    data.round0.repairTriples_card_le ()
  have h1 : (round1RepairPrefixes data).card ≤
      blockCard * (8 * fieldCard ^ 2) := by
    apply extendByBadChallenge_card_le
    intro round0
    exact data.round1.repairTriples_card_le round0
  have h2 : (round2RepairPrefixes data).card ≤
      blockCard ^ 2 * (8 * fieldCard ^ 2) := by
    have hprefix : Fintype.card
        (RelationRoundChallenges K × RelationRoundChallenges K) =
        blockCard ^ 2 := by simp [blockCard, pow_two]
    rw [← hprefix]
    apply extendByBadChallenge_card_le
    intro earlier
    exact data.round2.repairTriples_card_le earlier
  have h3 : (round3RepairChallenges data).card ≤
      blockCard ^ 3 * (8 * fieldCard ^ 2) := by
    have hprefix : Fintype.card
        ((RelationRoundChallenges K × RelationRoundChallenges K) ×
          RelationRoundChallenges K) = blockCard ^ 3 := by
      simp [blockCard, pow_succ]
    rw [← hprefix]
    apply extendByBadChallenge_card_le
    intro earlier
    exact data.round3.repairTriples_card_le earlier
  let event0 : Finset (TwelveRelationChallenges K) :=
    (((round0RepairBlocks data ×ˢ
        (Finset.univ : Finset (RelationRoundChallenges K))) ×ˢ
      (Finset.univ : Finset (RelationRoundChallenges K))) ×ˢ
      (Finset.univ : Finset (RelationRoundChallenges K)))
  let event1 : Finset (TwelveRelationChallenges K) :=
    ((round1RepairPrefixes data ×ˢ
      (Finset.univ : Finset (RelationRoundChallenges K))) ×ˢ
      (Finset.univ : Finset (RelationRoundChallenges K)))
  let event2 : Finset (TwelveRelationChallenges K) :=
    round2RepairPrefixes data ×ˢ
      (Finset.univ : Finset (RelationRoundChallenges K))
  let event3 : Finset (TwelveRelationChallenges K) := round3RepairChallenges data
  have hevent0 : event0.card ≤ 8 * fieldCard ^ 11 := by
    dsimp [event0]
    simp only [Finset.card_product, Finset.card_univ]
    calc
      (round0RepairBlocks data).card * blockCard * blockCard * blockCard ≤
          (8 * fieldCard ^ 2) * blockCard * blockCard * blockCard := by
            exact Nat.mul_le_mul_right _
              (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h0))
      _ = 8 * fieldCard ^ 11 := by rw [hblock]; ring
  have hevent1 : event1.card ≤ 8 * fieldCard ^ 11 := by
    dsimp [event1]
    simp only [Finset.card_product, Finset.card_univ]
    calc
      (round1RepairPrefixes data).card * blockCard * blockCard ≤
          (blockCard * (8 * fieldCard ^ 2)) * blockCard * blockCard := by
            exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)
      _ = 8 * fieldCard ^ 11 := by rw [hblock]; ring
  have hevent2 : event2.card ≤ 8 * fieldCard ^ 11 := by
    dsimp [event2]
    simp only [Finset.card_product, Finset.card_univ]
    calc
      (round2RepairPrefixes data).card * blockCard ≤
          (blockCard ^ 2 * (8 * fieldCard ^ 2)) * blockCard :=
        Nat.mul_le_mul_right _ h2
      _ = 8 * fieldCard ^ 11 := by rw [hblock]; ring
  have hevent3 : event3.card ≤ 8 * fieldCard ^ 11 := by
    dsimp [event3]
    calc
      (round3RepairChallenges data).card ≤
          blockCard ^ 3 * (8 * fieldCard ^ 2) := h3
      _ = 8 * fieldCard ^ 11 := by rw [hblock]; ring
  unfold adaptiveFixedCandidateRepairEvent
  change (((event0 ∪ event1) ∪ event2) ∪ event3).card ≤ _
  have h01 := Finset.card_union_le event0 event1
  have h012 := Finset.card_union_le (event0 ∪ event1) event2
  have h0123 := Finset.card_union_le ((event0 ∪ event1) ∪ event2) event3
  dsimp [fieldCard] at hevent0 hevent1 hevent2 hevent3 ⊢
  omega

/-- Exact uniform mass of the fixed-candidate event in its twelve-challenge
sample space. -/
noncomputable def uniformAdaptiveFixedCandidateRepairProbability
    (data : AdaptiveFixedCandidateFourRounds K) : ℚ :=
  (adaptiveFixedCandidateRepairEvent data).card /
    Fintype.card (TwelveRelationChallenges K)

/-- The adaptive twelve-challenge fixed-candidate event has mass at most
`32 / |K|`.  No FRI-list or deployed inclusion is asserted. -/
theorem uniformAdaptiveFixedCandidateRepairProbability_le
    (data : AdaptiveFixedCandidateFourRounds K) :
    uniformAdaptiveFixedCandidateRepairProbability data ≤
      (32 : ℚ) / Fintype.card K := by
  let fieldCard := Fintype.card K
  have hcardNat : 0 < fieldCard := Fintype.card_pos_iff.mpr ⟨0⟩
  have hcard : (0 : ℚ) < fieldCard := by exact_mod_cast hcardNat
  have hfull : Fintype.card (TwelveRelationChallenges K) = fieldCard ^ 12 := by
    simp [TwelveRelationChallenges, RelationRoundChallenges, fieldCard]
    ring
  have hevent := adaptiveFixedCandidateRepairEvent_card_le data
  unfold uniformAdaptiveFixedCandidateRepairProbability
  rw [hfull]
  change ((adaptiveFixedCandidateRepairEvent data).card : ℚ) /
      (fieldCard : ℚ) ^ 12 ≤ 32 / (fieldCard : ℚ)
  rw [div_le_iff₀ (pow_pos hcard 12)]
  have heventQ : ((adaptiveFixedCandidateRepairEvent data).card : ℚ) ≤
      32 * (fieldCard : ℚ) ^ 11 := by
    exact_mod_cast hevent
  calc
    ((adaptiveFixedCandidateRepairEvent data).card : ℚ) ≤
        32 * (fieldCard : ℚ) ^ 11 := heventQ
    _ = (32 / (fieldCard : ℚ)) * (fieldCard : ℚ) ^ 12 := by
      field_simp

end FiniteField

#print axioms relationPolynomial_injective
#print axioms accepted_wrong_boundary_difference_ne_zero
#print axioms roundCollisionSet_card_le_six
#print axioms uniformRoundCollisionProbability_le
#print axioms falseSequentialTwoMixCancellationSet_card_le
#print axioms uniformFalseSequentialTwoMixCancellationProbability_le
#print axioms FourRoundDiscrepancyTrace.mixCancellation_iff_mem
#print axioms FourRoundDiscrepancyTrace.terminal_zero_has_repair
#print axioms fixedCandidate_four_round_mix_plus_alpha_arithmetic
#print axioms RoundData.wrongIncomingCollisionSet_card_le_six
#print axioms RoundData.mem_wrongIncomingCollisionSet
#print axioms RoundData.mem_wrongIncomingCollisionSet_of_discrepancy_equations
#print axioms fourRoundCollisionEvent_card_le
#print axioms uniformFourRoundCollisionProbability_le
#print axioms AdaptiveFixedCandidateRound.repairTriples_card_le
#print axioms adaptiveFixedCandidateRepairEvent_card_le
#print axioms uniformAdaptiveFixedCandidateRepairProbability_le

end AspisV5RelationSumcheckSoundness
