import Mathlib

/-!
# A direct Johnson list bound for the initial V5 FRI word

This file proves the elementary double-counting part of the Johnson bound.
It is independent of the FRI round-reduction argument.

For a family of agreement sets, let `m(x)` be the number of candidates that
agree with the received word at coordinate `x`.  Cauchy--Schwarz lower-bounds
`sum m(x)^2`.  Distinct codewords can overlap on at most `d` coordinates, so
counting ordered candidate pairs upper-bounds the same second moment by

`sum m(x) + d * L * (L - 1)`.

At the V5 initial dimensions, `N = 524288`, agreement at least `24329`, and
pairwise overlap at most `1024` imply `L <= 222`, which is stronger than the
release cap `240`.
-/

namespace AspisV5FriJohnsonListBound

open scoped BigOperators

variable {Coordinate Candidate : Type*}
  [Fintype Coordinate] [DecidableEq Coordinate]
  [Fintype Candidate] [DecidableEq Candidate]

/-- Real-valued incidence bit for one candidate and coordinate. -/
def incidence (agreement : Candidate -> Finset Coordinate)
    (c : Candidate) (x : Coordinate) : Real :=
  if x ∈ agreement c then 1 else 0

/-- Number of candidates agreeing at one coordinate, represented in `Real`. -/
def multiplicity (agreement : Candidate -> Finset Coordinate)
    (x : Coordinate) : Real :=
  ∑ c : Candidate, incidence agreement c x

@[simp] theorem sum_incidence
    (agreement : Candidate -> Finset Coordinate) (c : Candidate) :
    (∑ x : Coordinate, incidence agreement c x) = (agreement c).card := by
  classical
  simp [incidence]

theorem sum_multiplicity_eq_sum_card
    (agreement : Candidate -> Finset Coordinate) :
    (∑ x : Coordinate, multiplicity agreement x) =
      ∑ c : Candidate, ((agreement c).card : Real) := by
  classical
  simp only [multiplicity]
  rw [Finset.sum_comm]
  simp

@[simp] theorem sum_incidence_mul_incidence
    (agreement : Candidate -> Finset Coordinate) (c d : Candidate) :
    (∑ x : Coordinate, incidence agreement c x * incidence agreement d x) =
      (((agreement c) ∩ (agreement d)).card : Real) := by
  classical
  simp [incidence, Finset.inter_comm]

/-- Expanding the square of each coordinate multiplicity counts ordered
candidate pairs on their agreement-set intersections. -/
theorem sum_multiplicity_sq_eq_pair_intersections
    (agreement : Candidate -> Finset Coordinate) :
    (∑ x : Coordinate, multiplicity agreement x ^ 2) =
      ∑ c : Candidate, ∑ d : Candidate,
        (((agreement c) ∩ (agreement d)).card : Real) := by
  classical
  calc
    (∑ x : Coordinate, multiplicity agreement x ^ 2) =
        ∑ x : Coordinate, ∑ c : Candidate, ∑ d : Candidate,
          incidence agreement c x * incidence agreement d x := by
            congr with x
            simp [multiplicity, pow_two, Finset.sum_mul, Finset.mul_sum,
              mul_comm]
    _ = ∑ c : Candidate, ∑ x : Coordinate, ∑ d : Candidate,
          incidence agreement c x * incidence agreement d x := by
            rw [Finset.sum_comm]
    _ = ∑ c : Candidate, ∑ d : Candidate, ∑ x : Coordinate,
          incidence agreement c x * incidence agreement d x := by
            congr with c
            rw [Finset.sum_comm]
    _ = ∑ c : Candidate, ∑ d : Candidate,
          (((agreement c) ∩ (agreement d)).card : Real) := by
            congr with c
            congr with d
            exact sum_incidence_mul_incidence agreement c d

/-- The second moment is at most its diagonal part plus the contribution of
ordered distinct pairs. -/
theorem sum_multiplicity_sq_le
    (agreement : Candidate -> Finset Coordinate) (d : Nat)
    (hoverlap : ∀ c e : Candidate, c ≠ e ->
      ((agreement c) ∩ (agreement e)).card ≤ d) :
    (∑ x : Coordinate, multiplicity agreement x ^ 2) ≤
      (∑ x : Coordinate, multiplicity agreement x) +
        d * Fintype.card Candidate * (Fintype.card Candidate - 1) := by
  classical
  rw [sum_multiplicity_sq_eq_pair_intersections,
    sum_multiplicity_eq_sum_card]
  -- Split each inner sum into the diagonal candidate and all other candidates.
  have hinner : ∀ c : Candidate,
      (∑ e : Candidate, (((agreement c) ∩ (agreement e)).card : Real)) ≤
        (agreement c).card + d * (Fintype.card Candidate - 1) := by
    intro c
    calc
      (∑ e : Candidate, (((agreement c) ∩ (agreement e)).card : Real)) =
          ((agreement c).card : Real) +
            ∑ e ∈ Finset.univ.erase c,
              (((agreement c) ∩ (agreement e)).card : Real) := by
                rw [← Finset.sum_erase_add _ _ (Finset.mem_univ c)]
                simp
      _ ≤ ((agreement c).card : Real) +
          ∑ _e ∈ Finset.univ.erase c, (d : Real) := by
            gcongr with e he
            exact_mod_cast hoverlap c e (Finset.ne_of_mem_erase he).symm
      _ = ((agreement c).card : Real) +
          d * (Fintype.card Candidate - 1) := by
        letI : Nonempty Candidate := ⟨c⟩
        have hcardpos : 0 < Fintype.card Candidate := Fintype.card_pos
        simp [Finset.card_erase_of_mem, Nat.cast_sub hcardpos]
        ring
  calc
    (∑ c : Candidate, ∑ e : Candidate,
        (((agreement c) ∩ (agreement e)).card : Real)) ≤
        ∑ c : Candidate,
          ((agreement c).card + d * (Fintype.card Candidate - 1) : Real) := by
            gcongr with c
            exact hinner c
    _ = (∑ c : Candidate, ((agreement c).card : Real)) +
          d * Fintype.card Candidate * (Fintype.card Candidate - 1) := by
            simp [Finset.sum_add_distrib]
            ring

/-- Generic second-moment Johnson inequality. -/
theorem johnson_second_moment
    (agreement : Candidate -> Finset Coordinate) (a d : Nat)
    (hlarge : ∀ c : Candidate, a ≤ (agreement c).card)
    (hoverlap : ∀ c e : Candidate, c ≠ e ->
      ((agreement c) ∩ (agreement e)).card ≤ d) :
    let L : Real := Fintype.card Candidate
    let N : Real := Fintype.card Coordinate
    let S : Real := ∑ x : Coordinate, multiplicity agreement x
    L * a ≤ S ∧
      S ^ 2 ≤ N * (S + d * L * (L - 1)) := by
  classical
  dsimp
  constructor
  · rw [sum_multiplicity_eq_sum_card]
    calc
      (Fintype.card Candidate : Real) * a =
          ∑ _c : Candidate, (a : Real) := by simp
      _ ≤ ∑ c : Candidate, ((agreement c).card : Real) := by
        gcongr with c
        exact_mod_cast hlarge c
  · calc
      (∑ x : Coordinate, multiplicity agreement x) ^ 2 ≤
          (Fintype.card Coordinate : Real) *
            ∑ x : Coordinate, multiplicity agreement x ^ 2 := by
              simpa using sq_sum_le_card_mul_sum_sq
                (s := Finset.univ) (f := multiplicity agreement)
      _ ≤ (Fintype.card Coordinate : Real) *
          ((∑ x : Coordinate, multiplicity agreement x) +
            d * Fintype.card Candidate * (Fintype.card Candidate - 1)) := by
              gcongr
              exact sum_multiplicity_sq_le agreement d hoverlap

/-- Arithmetic form of the Johnson argument.  `boundPlusOne` is the first
forbidden list size.  The final strict inequality is precisely the positive
denominator check in the usual Johnson fraction. -/
theorem list_card_lt_of_johnson_parameters
    (agreement : Candidate -> Finset Coordinate)
    (wordSize agreementFloor overlapCap boundPlusOne : Nat)
    (hcoord : Fintype.card Coordinate = wordSize)
    (hlarge : ∀ c : Candidate, agreementFloor ≤ (agreement c).card)
    (hoverlap : ∀ c e : Candidate, c ≠ e ->
      ((agreement c) ∩ (agreement e)).card ≤ overlapCap)
    (hfloorOverlap : overlapCap ≤ agreementFloor)
    (hhalf : (wordSize : Real) / 2 ≤
      (boundPlusOne : Real) * agreementFloor)
    (hpositive : 0 <
      (((agreementFloor : Real) ^ 2 - wordSize * overlapCap) *
          boundPlusOne -
        wordSize * ((agreementFloor : Real) - overlapCap))) :
    Fintype.card Candidate < boundPlusOne := by
  classical
  obtain ⟨hlower, hsecond⟩ := johnson_second_moment
    agreement agreementFloor overlapCap hlarge hoverlap
  rw [hcoord] at hsecond
  by_contra hnot
  have hLnat : boundPlusOne ≤ Fintype.card Candidate := Nat.le_of_not_gt hnot
  have hL : (boundPlusOne : Real) ≤ Fintype.card Candidate := by
    exact_mod_cast hLnat
  have hA : (0 : Real) ≤ agreementFloor := by positivity
  have hN : (0 : Real) ≤ wordSize := by positivity
  have hDleA : (overlapCap : Real) ≤ agreementFloor := by
    exact_mod_cast hfloorOverlap
  have hAhalf : (wordSize : Real) / 2 ≤
      (Fintype.card Candidate : Real) * agreementFloor :=
    hhalf.trans (mul_le_mul_of_nonneg_right hL hA)
  have hproduct : 0 ≤
      ((∑ x : Coordinate, multiplicity agreement x) -
          (Fintype.card Candidate : Real) * agreementFloor) *
        ((∑ x : Coordinate, multiplicity agreement x) +
          (Fintype.card Candidate : Real) * agreementFloor - wordSize) :=
    mul_nonneg (sub_nonneg.mpr hlower) (by linarith)
  have hmonotone :
      ((Fintype.card Candidate : Real) * agreementFloor) ^ 2 -
          wordSize * ((Fintype.card Candidate : Real) * agreementFloor) ≤
        (∑ x : Coordinate, multiplicity agreement x) ^ 2 -
          wordSize * (∑ x : Coordinate, multiplicity agreement x) := by
    nlinarith [hproduct]
  have hbound :
      ((Fintype.card Candidate : Real) * agreementFloor) ^ 2 -
          wordSize * ((Fintype.card Candidate : Real) * agreementFloor) ≤
        wordSize * overlapCap * (Fintype.card Candidate : Real) *
          ((Fintype.card Candidate : Real) - 1) := by
    calc
      _ ≤ (∑ x : Coordinate, multiplicity agreement x) ^ 2 -
          wordSize * (∑ x : Coordinate, multiplicity agreement x) := hmonotone
      _ ≤ wordSize * overlapCap * (Fintype.card Candidate : Real) *
          ((Fintype.card Candidate : Real) - 1) := by
            norm_num at hsecond ⊢
            nlinarith [hsecond]
  have hcoef : 0 <
      (agreementFloor : Real) ^ 2 - wordSize * overlapCap := by
    by_contra hnotcoef
    have hcoef' :
        (agreementFloor : Real) ^ 2 - wordSize * overlapCap ≤ 0 :=
      le_of_not_gt hnotcoef
    nlinarith [hpositive, mul_nonneg hN (sub_nonneg.mpr hDleA)]
  have hfactor : 0 <
      ((agreementFloor : Real) ^ 2 - wordSize * overlapCap) *
          Fintype.card Candidate -
        wordSize * ((agreementFloor : Real) - overlapCap) := by
    nlinarith
  have hLpositive : (0 : Real) < Fintype.card Candidate := by
    have hboundPos : 0 < boundPlusOne := by
      by_contra hz
      have : boundPlusOne = 0 := Nat.eq_zero_of_not_pos hz
      subst boundPlusOne
      norm_num at hpositive
      nlinarith [mul_nonneg hN (sub_nonneg.mpr hDleA)]
    exact lt_of_lt_of_le (by exact_mod_cast hboundPos) hL
  have hstrict : 0 <
      (Fintype.card Candidate : Real) *
        ((((agreementFloor : Real) ^ 2 - wordSize * overlapCap) *
            Fintype.card Candidate) -
          wordSize * ((agreementFloor : Real) - overlapCap)) :=
    mul_pos hLpositive hfactor
  nlinarith [hbound, hstrict]

/-- The concrete initial V5 dimensions give a list of at most 222 codewords.
The coding-theory premise is kept explicit: distinct initial circle-code words
agree in at most `1024` coordinates, the distance complement recorded for the
release code. -/
theorem v5_initial_list_card_le_222
    (hcoord : Fintype.card Coordinate = 524288)
    (agreement : Candidate -> Finset Coordinate)
    (hlarge : ∀ c : Candidate, 24329 ≤ (agreement c).card)
    (hoverlap : ∀ c e : Candidate, c ≠ e ->
      ((agreement c) ∩ (agreement e)).card ≤ 1024) :
    Fintype.card Candidate ≤ 222 := by
  classical
  obtain ⟨hlower, hsecond⟩ :=
    johnson_second_moment agreement 24329 1024 hlarge hoverlap
  rw [hcoord] at hsecond
  by_contra hnot
  have hLnat : 223 ≤ Fintype.card Candidate := by omega
  have hL : (223 : Real) ≤ Fintype.card Candidate := by exact_mod_cast hLnat
  have hnonneg : (0 : Real) ≤ Fintype.card Candidate := by positivity
  have hAhalf : (524288 : Real) / 2 ≤
      (Fintype.card Candidate : Real) * 24329 := by
    calc
      (524288 : Real) / 2 ≤ 223 * 24329 := by norm_num
      _ ≤ (Fintype.card Candidate : Real) * 24329 := by nlinarith
  have hSlarge : (524288 : Real) / 2 ≤
      ∑ x : Coordinate, multiplicity agreement x := hAhalf.trans hlower
  have hproduct : 0 ≤
      ((∑ x : Coordinate, multiplicity agreement x) -
          (Fintype.card Candidate : Real) * 24329) *
        ((∑ x : Coordinate, multiplicity agreement x) +
          (Fintype.card Candidate : Real) * 24329 - 524288) :=
    mul_nonneg (sub_nonneg.mpr hlower) (by linarith)
  have hmonotone :
      ((Fintype.card Candidate : Real) * 24329) ^ 2 -
          524288 * ((Fintype.card Candidate : Real) * 24329) ≤
        (∑ x : Coordinate, multiplicity agreement x) ^ 2 -
          524288 * (∑ x : Coordinate, multiplicity agreement x) := by
    nlinarith [hproduct]
  have hbound :
      ((Fintype.card Candidate : Real) * 24329) ^ 2 -
          524288 * ((Fintype.card Candidate : Real) * 24329) ≤
        524288 * 1024 * (Fintype.card Candidate : Real) *
          ((Fintype.card Candidate : Real) - 1) := by
    calc
      ((Fintype.card Candidate : Real) * 24329) ^ 2 -
          524288 * ((Fintype.card Candidate : Real) * 24329) ≤
          (∑ x : Coordinate, multiplicity agreement x) ^ 2 -
            524288 * (∑ x : Coordinate, multiplicity agreement x) := hmonotone
      _ ≤ 524288 * 1024 * (Fintype.card Candidate : Real) *
          ((Fintype.card Candidate : Real) - 1) := by
            norm_num at hsecond ⊢
            nlinarith [hsecond]
  have hfactor : 0 <
      (55029329 : Real) * Fintype.card Candidate - 12218531840 := by
    nlinarith
  have hpositive : 0 <
      (Fintype.card Candidate : Real) *
        ((55029329 : Real) * Fintype.card Candidate - 12218531840) :=
    mul_pos (by nlinarith) hfactor
  nlinarith [hbound, hpositive]

theorem v5_initial_list_card_le_240
    (hcoord : Fintype.card Coordinate = 524288)
    (agreement : Candidate -> Finset Coordinate)
    (hlarge : ∀ c : Candidate, 24329 ≤ (agreement c).card)
    (hoverlap : ∀ c e : Candidate, c ≠ e ->
      ((agreement c) ∩ (agreement e)).card ≤ 1024) :
    Fintype.card Candidate ≤ 240 :=
  (v5_initial_list_card_le_222 hcoord agreement hlarge hoverlap).trans (by omega)

/-- First committed line layer: `N=131072`, agreement at least `6083`, and
distinct-codeword overlap at most `255` give list size at most `213`. -/
theorem v5_layer1_list_card_le_213
    (hcoord : Fintype.card Coordinate = 131072)
    (agreement : Candidate -> Finset Coordinate)
    (hlarge : ∀ c : Candidate, 6083 ≤ (agreement c).card)
    (hoverlap : ∀ c e : Candidate, c ≠ e ->
      ((agreement c) ∩ (agreement e)).card ≤ 255) :
    Fintype.card Candidate ≤ 213 := by
  have hlt := list_card_lt_of_johnson_parameters agreement
    131072 6083 255 214 hcoord hlarge hoverlap (by norm_num)
    (by norm_num) (by norm_num)
  omega

/-- Second committed line layer: direct Johnson list size at most `191`. -/
theorem v5_layer2_list_card_le_191
    (hcoord : Fintype.card Coordinate = 32768)
    (agreement : Candidate -> Finset Coordinate)
    (hlarge : ∀ c : Candidate, 1521 ≤ (agreement c).card)
    (hoverlap : ∀ c e : Candidate, c ≠ e ->
      ((agreement c) ∩ (agreement e)).card ≤ 63) :
    Fintype.card Candidate ≤ 191 := by
  have hlt := list_card_lt_of_johnson_parameters agreement
    32768 1521 63 192 hcoord hlarge hoverlap (by norm_num)
    (by norm_num) (by norm_num)
  omega

/-- Third committed line layer: direct Johnson list size at most `134`. -/
theorem v5_layer3_list_card_le_134
    (hcoord : Fintype.card Coordinate = 8192)
    (agreement : Candidate -> Finset Coordinate)
    (hlarge : ∀ c : Candidate, 381 ≤ (agreement c).card)
    (hoverlap : ∀ c e : Candidate, c ≠ e ->
      ((agreement c) ∩ (agreement e)).card ≤ 15) :
    Fintype.card Candidate ≤ 134 := by
  have hlt := list_card_lt_of_johnson_parameters agreement
    8192 381 15 135 hcoord hlarge hoverlap (by norm_num)
    (by norm_num) (by norm_num)
  omega

theorem v5_all_layer_list_caps_le_240
    (initial : Nat) (layer1 : Nat) (layer2 : Nat) (layer3 : Nat)
    (h0 : initial ≤ 222) (h1 : layer1 ≤ 213)
    (h2 : layer2 ≤ 191) (h3 : layer3 ≤ 134) :
    initial ≤ 240 ∧ layer1 ≤ 240 ∧ layer2 ≤ 240 ∧ layer3 ≤ 240 := by
  omega

#print axioms johnson_second_moment
#print axioms list_card_lt_of_johnson_parameters
#print axioms v5_initial_list_card_le_222
#print axioms v5_initial_list_card_le_240
#print axioms v5_layer1_list_card_le_213
#print axioms v5_layer2_list_card_le_191
#print axioms v5_layer3_list_card_le_134

end AspisV5FriJohnsonListBound
