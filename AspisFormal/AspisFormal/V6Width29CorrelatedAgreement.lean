import AspisFormal.V5FriConcreteEncoderApplicability

/-!
# Width-29 correlated batching for V6

V6 batches 26 M31 C1 columns and three QM31 C2 columns with scalar powers of
one nonzero challenge.  This file proves the finite root-counting step for
that exact width.  A response strategy may choose a different close codeword
for every challenge; the conclusion therefore does not multiply the bound by
a decoder-list size.

The one external input is the published degree-28 curve-decoding statement,
spelled out as `Width29CurveDecodable`.
-/

namespace AspisV6Width29CorrelatedAgreement

open Polynomial
open AspisV5FriConcreteEncoderApplicability

variable {K Domain Message : Type*}
  [Field K] [Fintype K] [DecidableEq K]
  [Fintype Domain] [DecidableEq Domain]

def width29Batch (values : Fin 29 → K) (gamma : K) : K :=
  ∑ lane, values lane * gamma ^ lane.val

@[simp] theorem eval_monomialPolynomial_width29
    (values : Fin 29 → K) (gamma : K) :
    (monomialPolynomial values).eval gamma = width29Batch values gamma := by
  simp [monomialPolynomial, width29Batch, Polynomial.eval_finsetSum]

theorem width29Polynomial_ne_zero
    (values : Fin 29 → K) (hvalues : values ≠ 0) :
    monomialPolynomial values ≠ 0 := by
  intro hzero
  apply hvalues
  apply monomialPolynomial_injective
  simpa [monomialPolynomial] using hzero

theorem width29Polynomial_natDegree_le (values : Fin 29 → K) :
    (monomialPolynomial values).natDegree ≤ 28 := by
  simpa using
    (monomialPolynomial_natDegree_le (K := K) (n := 29) (by decide) values)

def width29NonzeroCollisionSet (values : Fin 29 → K) : Finset K :=
  (Finset.univ.erase 0).filter fun gamma => width29Batch values gamma = 0

theorem width29_nonzero_collision_card_le
    (values : Fin 29 → K) (hvalues : values ≠ 0) :
    (width29NonzeroCollisionSet values).card ≤ 28 := by
  let polynomial := monomialPolynomial values
  have hpolynomial : polynomial ≠ 0 := width29Polynomial_ne_zero values hvalues
  have hsubset : (width29NonzeroCollisionSet values).val ⊆ polynomial.roots := by
    intro gamma hgamma
    have hmem : gamma ∈ width29NonzeroCollisionSet values := hgamma
    have hbatch : width29Batch values gamma = 0 :=
      (Finset.mem_filter.mp hmem).2
    rw [Polynomial.mem_roots hpolynomial]
    simpa [Polynomial.IsRoot, polynomial] using hbatch
  exact (Polynomial.card_le_degree_of_subset_roots hsubset).trans
    (width29Polynomial_natDegree_le values)

def width29CurveValue
    (lanes : Fin 29 → Domain → K) (gamma : K) (x : Domain) : K :=
  width29Batch (fun lane => lanes lane x) gamma

structure Width29ProximateStrategy
    (K Domain Message : Type*) where
  candidate : K → Message
  support : K → Finset Domain

def Width29ValidResponse
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 29 → Domain → K)
    (strategy : Width29ProximateStrategy K Domain Message)
    (gamma : K) : Prop :=
  agreementThreshold < (strategy.support gamma).card ∧
    ∀ x ∈ strategy.support gamma,
      width29CurveValue lanes gamma x =
        encoder (strategy.candidate gamma) x

noncomputable def width29GoodChallenges
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 29 → Domain → K)
    (strategy : Width29ProximateStrategy K Domain Message) : Finset K := by
  classical
  exact (Finset.univ.erase 0).filter
    (Width29ValidResponse encoder agreementThreshold lanes strategy)

@[simp] theorem mem_width29GoodChallenges_iff
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 29 → Domain → K)
    (strategy : Width29ProximateStrategy K Domain Message)
    (gamma : K) :
    gamma ∈ width29GoodChallenges encoder agreementThreshold lanes strategy ↔
      gamma ≠ 0 ∧
        Width29ValidResponse encoder agreementThreshold lanes strategy gamma := by
  classical
  simp [width29GoodChallenges]

noncomputable def width29JointAgreementSet
    (encoder : Message → Domain → K)
    (lanes : Fin 29 → Domain → K)
    (components : Fin 29 → Message) : Finset Domain := by
  classical
  exact Finset.univ.filter fun x =>
    ∀ lane, lanes lane x = encoder (components lane) x

def Width29CandidateOnCurve
    (encoder : Message → Domain → K)
    (strategy : Width29ProximateStrategy K Domain Message)
    (components : Fin 29 → Message) (gamma : K) : Prop :=
  encoder (strategy.candidate gamma) =
    fun x => width29CurveValue
      (fun lane => encoder (components lane)) gamma x

def HasMatchingWidth29Decomposition
    (encoder : Message → Domain → K)
    (lanes : Fin 29 → Domain → K)
    (strategy : Width29ProximateStrategy K Domain Message)
    (gamma : K) : Prop :=
  ∃ components : Fin 29 → Message,
    strategy.support gamma ⊆
      width29JointAgreementSet encoder lanes components ∧
    Width29CandidateOnCurve encoder strategy components gamma

def Width29BadResponse
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 29 → Domain → K)
    (strategy : Width29ProximateStrategy K Domain Message)
    (gamma : K) : Prop :=
  Width29ValidResponse encoder agreementThreshold lanes strategy gamma ∧
    ¬ HasMatchingWidth29Decomposition encoder lanes strategy gamma

/-- Exact degree-28 curve-decoding statement needed from the cited theorem. -/
def Width29CurveDecodable
    (encoder : Message → Domain → K)
    (agreementThreshold challengeThreshold : Nat) : Prop :=
  ∀ (lanes : Fin 29 → Domain → K)
      (strategy : Width29ProximateStrategy K Domain Message),
    challengeThreshold <
        (width29GoodChallenges encoder agreementThreshold lanes strategy).card →
      ∃ (components : Fin 29 → Message) (selected : Finset K),
        selected ⊆
          width29GoodChallenges encoder agreementThreshold lanes strategy ∧
        28 * Fintype.card Domain < selected.card ∧
        ∀ gamma ∈ selected,
          Width29CandidateOnCurve encoder strategy components gamma

def width29CoordinateDiscrepancy
    (encoder : Message → Domain → K)
    (lanes : Fin 29 → Domain → K)
    (components : Fin 29 → Message) (x : Domain) : Fin 29 → K :=
  fun lane => lanes lane x - encoder (components lane) x

theorem width29CoordinateDiscrepancy_ne_zero_of_not_joint
    (encoder : Message → Domain → K)
    (lanes : Fin 29 → Domain → K)
    (components : Fin 29 → Message) (x : Domain)
    (hx : x ∉ width29JointAgreementSet encoder lanes components) :
    width29CoordinateDiscrepancy encoder lanes components x ≠ 0 := by
  classical
  intro hzero
  apply hx
  simp only [width29JointAgreementSet, Finset.mem_filter,
    Finset.mem_univ, true_and]
  intro lane
  have hlane := congrFun hzero lane
  simpa [width29CoordinateDiscrepancy] using sub_eq_zero.mp hlane

theorem width29CurveValue_sub_curveValue
    (encoder : Message → Domain → K)
    (lanes : Fin 29 → Domain → K)
    (components : Fin 29 → Message) (gamma : K) (x : Domain) :
    width29CurveValue lanes gamma x -
        width29CurveValue (fun lane => encoder (components lane)) gamma x =
      width29Batch
        (width29CoordinateDiscrepancy encoder lanes components x) gamma := by
  simp only [width29CurveValue, width29Batch,
    width29CoordinateDiscrepancy]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro lane _
  ring

noncomputable def width29ResolvingChallenges
    (encoder : Message → Domain → K)
    (lanes : Fin 29 → Domain → K)
    (components : Fin 29 → Message) : Finset K := by
  classical
  exact (Finset.univ.filter fun x =>
      x ∉ width29JointAgreementSet encoder lanes components).biUnion fun x =>
    width29NonzeroCollisionSet
      (width29CoordinateDiscrepancy encoder lanes components x)

theorem width29ResolvingChallenges_card_le
    (encoder : Message → Domain → K)
    (lanes : Fin 29 → Domain → K)
    (components : Fin 29 → Message) :
    (width29ResolvingChallenges encoder lanes components).card ≤
      28 * Fintype.card Domain := by
  classical
  let outside := Finset.univ.filter fun x =>
    x ∉ width29JointAgreementSet encoder lanes components
  have hroot : ∀ x ∈ outside,
      (width29NonzeroCollisionSet
        (width29CoordinateDiscrepancy encoder lanes components x)).card ≤ 28 := by
    intro x hx
    have hxnot : x ∉ width29JointAgreementSet encoder lanes components := by
      simpa [outside] using hx
    exact width29_nonzero_collision_card_le _
      (width29CoordinateDiscrepancy_ne_zero_of_not_joint
        encoder lanes components x hxnot)
  calc
    (width29ResolvingChallenges encoder lanes components).card =
        (outside.biUnion fun x =>
          width29NonzeroCollisionSet
            (width29CoordinateDiscrepancy encoder lanes components x)).card := by
          rfl
    _ ≤ outside.card * 28 :=
      Finset.card_biUnion_le_card_mul outside _ 28 hroot
    _ ≤ Fintype.card Domain * 28 := by
      gcongr
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = 28 * Fintype.card Domain := by omega

theorem exists_selected_not_width29Resolving
    (encoder : Message → Domain → K)
    (lanes : Fin 29 → Domain → K)
    (components : Fin 29 → Message) (selected : Finset K)
    (hlarge : 28 * Fintype.card Domain < selected.card) :
    ∃ gamma ∈ selected,
      gamma ∉ width29ResolvingChallenges encoder lanes components := by
  classical
  by_contra hnone
  push Not at hnone
  have hsubset : selected ⊆
      width29ResolvingChallenges encoder lanes components := by
    intro gamma hgamma
    exact hnone gamma hgamma
  have hle := (Finset.card_le_card hsubset).trans
    (width29ResolvingChallenges_card_le encoder lanes components)
  omega

theorem width29Support_subset_jointAgreement
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 29 → Domain → K)
    (strategy : Width29ProximateStrategy K Domain Message)
    (components : Fin 29 → Message) (gamma : K)
    (hgamma : gamma ≠ 0)
    (hvalid : Width29ValidResponse
      encoder agreementThreshold lanes strategy gamma)
    (honcurve : Width29CandidateOnCurve
      encoder strategy components gamma)
    (hresolve : gamma ∉
      width29ResolvingChallenges encoder lanes components) :
    strategy.support gamma ⊆
      width29JointAgreementSet encoder lanes components := by
  classical
  intro x hx
  have hagree := hvalid.2 x hx
  have hcurve := congrFun honcurve x
  by_contra hnotjoint
  have hdelta : width29Batch
      (width29CoordinateDiscrepancy encoder lanes components x) gamma = 0 := by
    rw [← width29CurveValue_sub_curveValue
      encoder lanes components gamma x]
    rw [hagree, hcurve]
    exact sub_self _
  apply hresolve
  simp only [width29ResolvingChallenges, Finset.mem_biUnion]
  refine ⟨x, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hnotjoint
  · simp [width29NonzeroCollisionSet, hgamma, hdelta]

noncomputable def width29BadStrategy
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 29 → Domain → K)
    (strategy : Width29ProximateStrategy K Domain Message) :
    Width29ProximateStrategy K Domain Message := by
  classical
  exact {
    candidate := strategy.candidate
    support := fun gamma =>
      if Width29BadResponse encoder agreementThreshold lanes strategy gamma
      then strategy.support gamma
      else ∅
  }

theorem mem_width29BadStrategy_good_iff
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 29 → Domain → K)
    (strategy : Width29ProximateStrategy K Domain Message)
    (gamma : K) :
    gamma ∈ width29GoodChallenges encoder agreementThreshold lanes
        (width29BadStrategy encoder agreementThreshold lanes strategy) ↔
      gamma ≠ 0 ∧
        Width29BadResponse encoder agreementThreshold lanes strategy gamma := by
  classical
  rw [mem_width29GoodChallenges_iff]
  constructor
  · intro h
    by_cases hbad :
        Width29BadResponse encoder agreementThreshold lanes strategy gamma
    · exact ⟨h.1, hbad⟩
    · have hempty :
          (width29BadStrategy encoder agreementThreshold lanes strategy).support
              gamma = ∅ := by
        simp [width29BadStrategy, hbad]
      have himpossible : agreementThreshold < 0 := by
        simpa only [hempty, Finset.card_empty] using h.2.1
      exact (Nat.not_lt_zero _ himpossible).elim
  · rintro ⟨hgamma, hbad⟩
    refine ⟨hgamma, ?_⟩
    have hsupport :
        (width29BadStrategy encoder agreementThreshold lanes strategy).support
            gamma = strategy.support gamma := by
      simp [width29BadStrategy, hbad]
    constructor
    · rw [hsupport]
      exact hbad.1.1
    · intro x hx
      rw [hsupport] at hx
      exact hbad.1.2 x hx

/-- The degree-28 curve-decoding threshold bounds all selected bad responses,
even though the strategy may return a different candidate for every gamma. -/
theorem width29_bad_response_challenges_card_le
    (encoder : Message → Domain → K)
    (agreementThreshold challengeThreshold : Nat)
    (hcurve : Width29CurveDecodable
      encoder agreementThreshold challengeThreshold)
    (lanes : Fin 29 → Domain → K)
    (strategy : Width29ProximateStrategy K Domain Message) :
    (width29GoodChallenges encoder agreementThreshold lanes
      (width29BadStrategy encoder agreementThreshold lanes strategy)).card ≤
        challengeThreshold := by
  classical
  by_contra hnot
  have hmany : challengeThreshold <
      (width29GoodChallenges encoder agreementThreshold lanes
        (width29BadStrategy encoder agreementThreshold lanes strategy)).card :=
    Nat.lt_of_not_ge hnot
  obtain ⟨components, selected, hselected, hlarge, honcurve⟩ :=
    hcurve lanes
      (width29BadStrategy encoder agreementThreshold lanes strategy) hmany
  obtain ⟨gamma, hgammaSelected, hgammaResolve⟩ :=
    exists_selected_not_width29Resolving
      encoder lanes components selected hlarge
  have hgood := hselected hgammaSelected
  have hbad :=
    (mem_width29BadStrategy_good_iff encoder agreementThreshold lanes
      strategy gamma).mp hgood
  have hvalidMasked :=
    (mem_width29GoodChallenges_iff encoder agreementThreshold lanes
      (width29BadStrategy encoder agreementThreshold lanes strategy)
      gamma).mp hgood
  have hsubsetMasked := width29Support_subset_jointAgreement
    encoder agreementThreshold lanes
      (width29BadStrategy encoder agreementThreshold lanes strategy)
      components gamma hvalidMasked.1 hvalidMasked.2
      (honcurve gamma hgammaSelected) hgammaResolve
  have hsupport : strategy.support gamma ⊆
      width29JointAgreementSet encoder lanes components := by
    simpa [width29BadStrategy, hbad.2] using hsubsetMasked
  have honcurveOriginal : Width29CandidateOnCurve
      encoder strategy components gamma := by
    simpa [Width29CandidateOnCurve, width29BadStrategy] using
      honcurve gamma hgammaSelected
  exact hbad.2.2 ⟨components, hsupport, honcurveOriginal⟩

#print axioms width29_nonzero_collision_card_le
#print axioms width29ResolvingChallenges_card_le
#print axioms width29Support_subset_jointAgreement
#print axioms width29_bad_response_challenges_card_le

end AspisV6Width29CorrelatedAgreement
