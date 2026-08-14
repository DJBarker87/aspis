import AspisFormal.CircleGroupCardinality
import AspisFormal.V5FriConcreteEncoderCommutation
import AspisFormal.V5FriInitialListBound

set_option maxRecDepth 20000
set_option maxHeartbeats 500000

/-!
# Distance of the initial M31 circle code

This file proves the root-counting step specific to the initial circle code.
A circle polynomial

`p₀(x) + y * p₁(x)`, with `deg p₀, deg p₁ < 512`,

becomes an ordinary polynomial of degree at most `1024` after the
stereographic substitution `t = y / (1 + x)`.  Consequently two distinct
messages can agree on at most `1024` distinct circle points, provided the
coefficient-to-numerator map is injective and the encoder really evaluates
that expression.

The deployed half-odd M31 coset is also defined here.  Its `2^19` points are
proved pairwise distinct and proved to avoid `x = -1`, using the already
kernel-checked order of the deployed generator.  Thus its stereographic
parameters are pairwise distinct; this geometric part carries no interface
hypothesis.
-/

namespace AspisV5FriCircleEncoderDistance

open Polynomial
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriInitialListBound

/-! ## The exact deployed circle domain -/

/-- Exponent of the `i`-th point in the full half-odd `2^19` circle coset.
The verifier groups these points into `2^17` radix-four fibres. -/
def initialCircleExponent (i : Nat) : Int :=
  (2 : Int) ^ 11 * (2 * i + 1)

/-- The exact full initial circle domain, before the first radix-four fold. -/
def initialCirclePoint (i : Fin (2 ^ 19)) : AspisCircleGroupOrder.C :=
  AspisCircleGroupOrder.g ^ initialCircleExponent i

/-- The half-odd exponents give pairwise distinct points modulo the exact
order `2^31` of `g`. -/
theorem initialCirclePoint_injective : Function.Injective initialCirclePoint := by
  intro i j hij
  have hm := (AspisCircleGroupOrder.g_zpow_eq_iff (initialCircleExponent i)
    (initialCircleExponent j)).mp hij
  apply Fin.ext
  unfold initialCircleExponent Int.ModEq at hm
  have hi := i.isLt
  have hj := j.isLt
  norm_num at hi hj
  omega

/-- The half-turn has x-coordinate `-1`. -/
lemma halfTurn_x_eq_neg_one :
    AspisCircleGroupOrder.X
      (AspisCircleGroupOrder.g ^ ((2 : Int) ^ 30)) = -1 := by
  rw [show (2 : Int) ^ 30 = ((2 ^ 30 : Nat) : Int) by norm_num, zpow_natCast]
  rw [← AspisCircleGroupOrder.sq_iterate 30 AspisCircleGroupOrder.g]
  decide

/-- No deployed initial-domain point is the west pole `(-1,0)`. -/
theorem initialCirclePoint_x_ne_neg_one (i : Fin (2 ^ 19)) :
    AspisCircleGroupOrder.X (initialCirclePoint i) ≠ -1 := by
  intro hx
  have hsame :
      AspisCircleGroupOrder.X
          (AspisCircleGroupOrder.g ^ initialCircleExponent i) =
        AspisCircleGroupOrder.X
          (AspisCircleGroupOrder.g ^ ((2 : Int) ^ 30)) := by
    simpa only [initialCirclePoint, halfTurn_x_eq_neg_one] using hx
  have hm := (AspisCircleGroupOrder.sameXCoord_exp
    (initialCircleExponent i) ((2 : Int) ^ 30)).mp hsame
  unfold initialCircleExponent Int.ModEq at hm
  have hi := i.isLt
  norm_num at hi
  rcases hm with hm | hm <;> omega

/-- Stereographic parameter of an initial-domain point. -/
def initialStereo (i : Fin (2 ^ 19)) : ZMod AspisCircleGroupOrder.P :=
  (initialCirclePoint i).1.2 /
    (1 + AspisCircleGroupOrder.X (initialCirclePoint i))

/-- The exact initial-domain stereographic parameters are pairwise distinct. -/
theorem initialStereo_injective : Function.Injective initialStereo := by
  intro i j hij
  apply initialCirclePoint_injective
  apply AspisCircleGroupOrder.stereo_injective
  have hi : (initialCirclePoint i).1.1 ≠ -1 :=
    initialCirclePoint_x_ne_neg_one i
  have hj : (initialCirclePoint j).1.1 ≠ -1 :=
    initialCirclePoint_x_ne_neg_one j
  unfold AspisCircleGroupOrder.stereo
  rw [if_neg hi, if_neg hj, Option.some.injEq]
  simpa only [initialStereo, AspisCircleGroupOrder.X] using hij

/-! ## Stereographic numerator -/

variable {K : Type*} [Field K]

/-- The same linear-fractional lift before replacing its variable by `t²`. -/
noncomputable def fractionalLift (d : Nat) (p : K[X]) : K[X] :=
  ∑ i ∈ Finset.range (d + 1),
    Polynomial.C (p.coeff i) * (1 - X) ^ i * (1 + X) ^ (d - i)

/-- Homogenize a univariate polynomial after the substitution
`x = (1-t^2)/(1+t^2)`, clearing `d` powers of the denominator.  Defining
this as an expansion keeps concrete release degrees such as `512` opaque to
the elaborator instead of constructing a 513-term expression. -/
noncomputable def mobiusLift (d : Nat) (p : K[X]) : K[X] :=
  Polynomial.expand K 2 (fractionalLift d p)

/-- `mobiusLift` is the even expansion of `fractionalLift`. -/
theorem mobiusLift_eq_expand (d : Nat) (p : K[X]) :
    mobiusLift d p = Polynomial.expand K 2 (fractionalLift d p) := rfl

theorem fractionalLift_natDegree_le (d : Nat) (p : K[X]) :
    (fractionalLift d p).natDegree ≤ d := by
  classical
  unfold fractionalLift
  apply (Polynomial.natDegree_sum_le _ _).trans
  apply Finset.sup_le
  intro i hi
  simp only [Finset.mem_range] at hi
  change (Polynomial.C (p.coeff i) * (1 - X) ^ i *
    (1 + X) ^ (d - i)).natDegree ≤ d
  have hC : (Polynomial.C (p.coeff i)).natDegree ≤ 0 := by
    rw [Polynomial.natDegree_C]
  have hminus : ((1 : K[X]) - X).natDegree ≤ 1 := by
    exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
  have hplus : ((1 : K[X]) + X).natDegree ≤ 1 := by
    exact (Polynomial.natDegree_add_le _ _).trans (by simp)
  have hminusPow : (((1 : K[X]) - X) ^ i).natDegree ≤ i := by
    calc
      (((1 : K[X]) - X) ^ i).natDegree
          ≤ i * ((1 : K[X]) - X).natDegree :=
            Polynomial.natDegree_pow_le
      _ ≤ i * 1 := Nat.mul_le_mul_left i hminus
      _ = i := Nat.mul_one _
  have hplusPow : (((1 : K[X]) + X) ^ (d - i)).natDegree ≤ d - i := by
    calc
      (((1 : K[X]) + X) ^ (d - i)).natDegree
          ≤ (d - i) * ((1 : K[X]) + X).natDegree :=
            Polynomial.natDegree_pow_le
      _ ≤ (d - i) * 1 := Nat.mul_le_mul_left (d - i) hplus
      _ = d - i := Nat.mul_one _
  calc
    (Polynomial.C (p.coeff i) * (((1 : K[X]) - X) ^ i) *
        (((1 : K[X]) + X) ^ (d - i))).natDegree
        ≤ (Polynomial.C (p.coeff i)).natDegree +
            (((1 : K[X]) - X) ^ i).natDegree +
            (((1 : K[X]) + X) ^ (d - i)).natDegree := by
          exact (Polynomial.natDegree_mul_le.trans
            (Nat.add_le_add_right Polynomial.natDegree_mul_le _))
    _ ≤ 0 + i + (d - i) := by
          exact Nat.add_le_add (Nat.add_le_add hC hminusPow) hplusPow
    _ ≤ d := by omega

theorem mobiusLift_natDegree_le (d : Nat) (p : K[X]) :
    (mobiusLift d p).natDegree ≤ 2 * d := by
  rw [mobiusLift, Polynomial.natDegree_expand]
  have h := fractionalLift_natDegree_le d p
  omega

/-- Numerator obtained by clearing `512` powers of `1+t^2` in
`p₀(x) + y*p₁(x)`. -/
noncomputable def circleNumerator (p0 p1 : K[X]) : K[X] :=
  mobiusLift 512 p0 + (Polynomial.C 2 * X) * mobiusLift 511 p1

/-- The cleared numerator has degree at most `1024`. -/
theorem circleNumerator_natDegree_le (p0 p1 : K[X]) :
    (circleNumerator p0 p1).natDegree ≤ 1024 := by
  have hleft : (mobiusLift 512 p0).natDegree ≤ 1024 := by
    simpa using mobiusLift_natDegree_le 512 p0
  have hfactor : (Polynomial.C (2 : K) * X).natDegree ≤ 1 := by
    exact Polynomial.natDegree_mul_le.trans (by simp)
  have hright : ((Polynomial.C (2 : K) * X) * mobiusLift 511 p1).natDegree ≤
      1023 := by
    exact Polynomial.natDegree_mul_le.trans
      ((Nat.add_le_add hfactor (mobiusLift_natDegree_le 511 p1)).trans_eq
        (by norm_num))
  unfold circleNumerator
  exact (Polynomial.natDegree_add_le _ _).trans
    (max_le hleft (hright.trans (by norm_num)))

theorem coeff_expand_two_even (p : K[X]) (n : Nat) :
    (Polynomial.expand K 2 p).coeff (2 * n) = p.coeff n := by
  exact Polynomial.coeff_expand_mul' (by norm_num) p n

theorem coeff_expand_two_odd (p : K[X]) (n : Nat) :
    (Polynomial.expand K 2 p).coeff (2 * n + 1) = 0 := by
  rw [Polynomial.coeff_expand (p := 2) (by norm_num), if_neg (by omega)]

theorem coeff_scaledX_expand_two_even (p : K[X]) (n : Nat) :
    ((Polynomial.C 2 * X) * Polynomial.expand K 2 p).coeff (2 * n) = 0 := by
  rw [mul_assoc, Polynomial.coeff_C_mul]
  cases n with
  | zero => simp
  | succ n =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
        Polynomial.coeff_X_mul, coeff_expand_two_odd]
      simp

theorem coeff_scaledX_expand_two_odd (p : K[X]) (n : Nat) :
    ((Polynomial.C 2 * X) * Polynomial.expand K 2 p).coeff (2 * n + 1) =
      2 * p.coeff n := by
  rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul,
    coeff_expand_two_even]

/-- Even powers identify the first polynomial and odd powers identify the
second.  This is the injectivity of the parity-separated circle numerator. -/
theorem evenOddExpanded_injective [NeZero (2 : K)] :
    Function.Injective (fun pair : K[X] × K[X] =>
      Polynomial.expand K 2 pair.1 +
        (Polynomial.C 2 * X) * Polynomial.expand K 2 pair.2) := by
  rintro ⟨p0, p1⟩ ⟨q0, q1⟩ heq
  apply Prod.ext
  · ext n
    have hcoeff := congrArg (fun p : K[X] => p.coeff (2 * n)) heq
    simpa only [Polynomial.coeff_add, coeff_expand_two_even,
      coeff_scaledX_expand_two_even, add_zero] using hcoeff
  · ext n
    have hcoeff := congrArg (fun p : K[X] => p.coeff (2 * n + 1)) heq
    simp only [Polynomial.coeff_add, coeff_expand_two_odd,
      coeff_scaledX_expand_two_odd, zero_add] at hcoeff
    exact mul_left_cancel₀ (NeZero.ne (2 : K)) hcoeff

/-- Any finite extension field containing M31 has far more than the 513
points needed for the lift-injectivity argument. -/
theorem m31_extension_card_gt_513
    [Fintype K] [Algebra (ZMod AspisCircleGroupOrder.P) K] :
    513 < Fintype.card K := by
  have hcard := Fintype.card_le_of_injective
    (algebraMap (ZMod AspisCircleGroupOrder.P) K)
    (FaithfulSMul.algebraMap_injective (ZMod AspisCircleGroupOrder.P) K)
  rw [ZMod.card] at hcard
  norm_num [AspisCircleGroupOrder.P] at hcard ⊢
  omega

/-- Evaluation formula for the unsquared linear-fractional lift. -/
theorem fractionalLift_eval (d : Nat) (p : K[X]) (u : K) :
    (fractionalLift d p).eval u =
      ∑ i ∈ Finset.range (d + 1),
        p.coeff i * (1 - u) ^ i * (1 + u) ^ (d - i) := by
  classical
  rw [fractionalLift, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  simp

/-- Pointwise evaluation formula for the homogeneous lift. -/
theorem mobiusLift_eval (d : Nat) (p : K[X]) (t : K) :
    (mobiusLift d p).eval t =
      ∑ i ∈ Finset.range (d + 1),
        p.coeff i * (1 - t ^ 2) ^ i * (1 + t ^ 2) ^ (d - i) := by
  rw [mobiusLift, Polynomial.expand_eval, fractionalLift_eval]

/-- The homogeneous lift is exactly denominator-cleared evaluation at the
stereographic x-coordinate. -/
theorem mobiusLift_eval_div (d : Nat) (p : K[X])
    (hp : p.natDegree ≤ d) (a b : K) (hb : b ≠ 0) :
    (∑ i ∈ Finset.range (d + 1),
        p.coeff i * a ^ i * b ^ (d - i)) =
      p.eval (a / b) * b ^ d := by
  classical
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_iff.mpr hp), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hid : i ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [div_pow, ← pow_sub_mul_pow b hid]
  field_simp [hb]

/-- Compact denominator-cleared evaluation identity.  Keeping the finite sum
behind this symbolic lemma avoids expanding 512 summands at the concrete
release degree. -/
theorem mobiusLift_eval_ratio (d : Nat) (p : K[X])
    (hp : p.natDegree ≤ d) (t : K) (hden : 1 + t ^ 2 ≠ 0) :
    (mobiusLift d p).eval t =
      p.eval ((1 - t ^ 2) / (1 + t ^ 2)) * (1 + t ^ 2) ^ d := by
  rw [mobiusLift_eval]
  exact mobiusLift_eval_div d p hp (1 - t ^ 2) (1 + t ^ 2) hden

/-- The fractional-linear map `u = (1-x)/(1+x)` is an involution away from
`-1`. -/
theorem fractional_involution (x : K) (hx : x ≠ -1) [NeZero (2 : K)] :
    let u := (1 - x) / (1 + x)
    1 + u ≠ 0 ∧ (1 - u) / (1 + u) = x := by
  dsimp
  have hxden : (1 : K) + x ≠ 0 := by
    intro h
    apply hx
    linear_combination h
  have htwo : (2 : K) ≠ 0 := NeZero.ne _
  have hplus : 1 + (1 - x) / (1 + x) = 2 / (1 + x) := by
    field_simp [hxden]
    ring
  constructor
  · rw [hplus]
    exact div_ne_zero htwo hxden
  · rw [hplus]
    field_simp [hxden, htwo]
    ring

/-- The unsquared lift is injective on polynomials of degree at most `d` as
soon as the field has more than `d+1` elements. -/
theorem fractionalLift_eq_of_eq
    [Fintype K] [DecidableEq K] [NeZero (2 : K)]
    (d : Nat) (hcard : d + 1 < Fintype.card K)
    (p q : K[X]) (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d)
    (heq : fractionalLift d p = fractionalLift d q) : p = q := by
  classical
  let sample := (Finset.univ : Finset K).erase (-1)
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq' p q sample
  · intro x hx
    have hxneg : x ≠ -1 := by
      simpa only [sample, Finset.mem_erase, Finset.mem_univ, and_true] using hx
    obtain ⟨huden, hu⟩ := fractional_involution x hxneg
    have heval := congrArg
      (fun polynomial : K[X] => polynomial.eval ((1 - x) / (1 + x))) heq
    rw [fractionalLift_eval, fractionalLift_eval,
      mobiusLift_eval_div d p hp
        (1 - ((1 - x) / (1 + x))) (1 + ((1 - x) / (1 + x))) huden,
      mobiusLift_eval_div d q hq
        (1 - ((1 - x) / (1 + x))) (1 + ((1 - x) / (1 + x))) huden,
      hu] at heval
    exact mul_right_cancel₀ (pow_ne_zero d huden) heval
  · have hcardSample : sample.card = Fintype.card K - 1 := by
      simp [sample]
    rw [hcardSample]
    have hmax : max p.natDegree q.natDegree ≤ d := max_le hp hq
    omega

/-- The map `(p₀,p₁) ↦ circleNumerator p₀ p₁` is injective for the released
degree range.  Thus numerator nonzeroness is proved from coefficient
nonzeroness rather than assumed as a distance fact. -/
theorem circleNumerator_pair_eq
    [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K]
    (p0 p1 q0 q1 : K[X])
    (hp0 : p0.natDegree < 512) (hp1 : p1.natDegree < 512)
    (hq0 : q0.natDegree < 512) (hq1 : q1.natDegree < 512)
    (heq : circleNumerator p0 p1 = circleNumerator q0 q1) :
    p0 = q0 ∧ p1 = q1 := by
  have htwo : (2 : K) ≠ 0 := by
    intro hzero
    apply AspisCircleGroupOrder.two_ne_zero_ZModP
    apply FaithfulSMul.algebraMap_injective (ZMod AspisCircleGroupOrder.P) K
    simpa only [map_ofNat, map_zero] using hzero
  letI : NeZero (2 : K) := ⟨htwo⟩
  have hleft :
      circleNumerator p0 p1 =
        Polynomial.expand K 2 (fractionalLift 512 p0) +
          (Polynomial.C 2 * X) *
            Polynomial.expand K 2 (fractionalLift 511 p1) := by
    rw [circleNumerator, mobiusLift_eq_expand, mobiusLift_eq_expand]
  have hright :
      circleNumerator q0 q1 =
        Polynomial.expand K 2 (fractionalLift 512 q0) +
          (Polynomial.C 2 * X) *
            Polynomial.expand K 2 (fractionalLift 511 q1) := by
    rw [circleNumerator, mobiusLift_eq_expand, mobiusLift_eq_expand]
  have hrewritten :
      Polynomial.expand K 2 (fractionalLift 512 p0) +
          (Polynomial.C 2 * X) *
            Polynomial.expand K 2 (fractionalLift 511 p1) =
        Polynomial.expand K 2 (fractionalLift 512 q0) +
          (Polynomial.C 2 * X) *
            Polynomial.expand K 2 (fractionalLift 511 q1) :=
    hleft.symm.trans (heq.trans hright)
  have hlift0 : fractionalLift 512 p0 = fractionalLift 512 q0 := by
    ext n
    have hcoeff := congrArg (fun p : K[X] => p.coeff (2 * n)) hrewritten
    simpa only [Polynomial.coeff_add, coeff_expand_two_even,
      coeff_scaledX_expand_two_even, add_zero] using hcoeff
  have hlift1 : fractionalLift 511 p1 = fractionalLift 511 q1 := by
    ext n
    have hcoeff := congrArg (fun p : K[X] => p.coeff (2 * n + 1)) hrewritten
    simp only [Polynomial.coeff_add, coeff_expand_two_odd,
      coeff_scaledX_expand_two_odd, zero_add] at hcoeff
    exact mul_left_cancel₀ htwo hcoeff
  constructor
  · exact fractionalLift_eq_of_eq (K := K) 512
      (m31_extension_card_gt_513 (K := K)) p0 q0
      (Nat.le_of_lt hp0) (Nat.le_of_lt hq0) hlift0
  · have hcard : 512 < Fintype.card K := by
      have h := m31_extension_card_gt_513 (K := K)
      omega
    exact fractionalLift_eq_of_eq (K := K) 511 hcard p1 q1
      (by omega) (by omega) hlift1

/-- Stereographic substitution for one point of `x²+y²=1`. -/
theorem stereo_identities (x y : K) (hon : x ^ 2 + y ^ 2 = 1)
    (hx : x ≠ -1) [NeZero (2 : K)] :
    let t := y / (1 + x)
    (1 + t ^ 2 ≠ 0) ∧
      (1 - t ^ 2) / (1 + t ^ 2) = x ∧
      2 * t / (1 + t ^ 2) = y := by
  dsimp
  have hden : (1 : K) + x ≠ 0 := by
    intro h
    apply hx
    linear_combination h
  have htwo : (2 : K) ≠ 0 := NeZero.ne _
  have hplus : 1 + (y / (1 + x)) ^ 2 = 2 / (1 + x) := by
    field_simp [hden]
    linear_combination hon
  have hplus_ne : 1 + (y / (1 + x)) ^ 2 ≠ 0 := by
    rw [hplus]
    exact div_ne_zero htwo hden
  refine ⟨hplus_ne, ?_, ?_⟩
  · rw [hplus]
    field_simp [hden, htwo]
    linear_combination -hon
  · rw [hplus]
    field_simp [hden, htwo]

/-- Clearing the stereographic denominator turns
`p₀(x) + y*p₁(x)` into the ordinary polynomial `circleNumerator p₀ p₁`. -/
theorem circleNumerator_eval_stereo (p0 p1 : K[X])
    (hp0 : p0.natDegree < 512) (hp1 : p1.natDegree < 512)
    (x y : K) (hon : x ^ 2 + y ^ 2 = 1) (hx : x ≠ -1)
    [NeZero (2 : K)] :
    let t := y / (1 + x)
    (circleNumerator p0 p1).eval t =
      (1 + t ^ 2) ^ 512 * (p0.eval x + y * p1.eval x) := by
  let t : K := y / (1 + x)
  let b : K := 1 + t ^ 2
  change (circleNumerator p0 p1).eval t =
    b ^ 512 * (p0.eval x + y * p1.eval x)
  obtain ⟨hdenRaw, hxparamRaw, hyparamRaw⟩ := stereo_identities x y hon hx
  have hden : b ≠ 0 := by
    simpa only [b, t] using hdenRaw
  have hxparam : (1 - t ^ 2) / b = x := by
    simpa only [b, t] using hxparamRaw
  have hyparam : 2 * t / b = y := by
    simpa only [b, t] using hyparamRaw
  rw [circleNumerator, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [mobiusLift_eval_ratio 512 p0 (Nat.le_of_lt hp0)
      t hden,
    mobiusLift_eval_ratio 511 p1 (by omega)
      t hden,
    hxparam]
  have hytimes : 2 * t = y * b := (div_eq_iff hden).mp hyparam
  rw [hytimes, show b ^ 512 = b ^ 511 * b by rw [pow_succ]]
  change p0.eval x * (b ^ 511 * b) +
      y * b * (p1.eval x * b ^ 511) =
    b ^ 511 * b * (p0.eval x + y * p1.eval x)
  conv_rhs => rw [mul_add]
  congr 1 <;> ac_rfl

/-! ## Generic distance theorem for an exact circle realization -/

variable {Message : Type*} {wordSize : Nat}
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

private theorem algebraMap_div_one_add (a b : ZMod AspisCircleGroupOrder.P) :
    algebraMap (ZMod AspisCircleGroupOrder.P) K (a / (1 + b)) =
      algebraMap (ZMod AspisCircleGroupOrder.P) K a /
        (1 + algebraMap (ZMod AspisCircleGroupOrder.P) K b) := by
  calc
    _ = algebraMap (ZMod AspisCircleGroupOrder.P) K a /
        algebraMap (ZMod AspisCircleGroupOrder.P) K (1 + b) :=
      map_div₀
        (algebraMap (ZMod AspisCircleGroupOrder.P) K :
          ZMod AspisCircleGroupOrder.P →+* K) a (1 + b)
    _ = _ := by rw [map_add, map_one]

/-- Exact data connecting an encoder to its cleared stereographic
numerator.  The numerator is defined above from `p₀,p₁`; injectivity is a
coefficient-map fact, not a distance assumption. -/
structure CirclePolynomialRealization
    (encoder : Message → Fin wordSize → K) where
  point : Fin wordSize → AspisCircleGroupOrder.C
  point_injective : Function.Injective point
  avoids_west_pole : ∀ i, AspisCircleGroupOrder.X (point i) ≠ -1
  p0 : Message → K[X]
  p1 : Message → K[X]
  p0_degree_lt : ∀ message, (p0 message).natDegree < 512
  p1_degree_lt : ∀ message, (p1 message).natDegree < 512
  coefficient_pair_injective :
    Function.Injective (fun message => (p0 message, p1 message))
  encoder_eq_circle_eval : ∀ message i,
    encoder message i =
      (p0 message).eval
          (algebraMap (ZMod AspisCircleGroupOrder.P) K
            (AspisCircleGroupOrder.X (point i))) +
        algebraMap (ZMod AspisCircleGroupOrder.P) K (point i).1.2 *
          (p1 message).eval
            (algebraMap (ZMod AspisCircleGroupOrder.P) K
              (AspisCircleGroupOrder.X (point i)))

/-- The evaluation field in `CirclePolynomialRealization` implies the exact
cleared-numerator identity; it is not an additional premise. -/
theorem CirclePolynomialRealization.encoder_numerator_eval
    {encoder : Message → Fin wordSize → K}
    (r : CirclePolynomialRealization encoder) (message : Message)
    (i : Fin wordSize) :
    (circleNumerator (r.p0 message) (r.p1 message)).eval
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          ((r.point i).1.2 /
            (1 + AspisCircleGroupOrder.X (r.point i)))) =
      (1 + (algebraMap (ZMod AspisCircleGroupOrder.P) K
          ((r.point i).1.2 /
            (1 + AspisCircleGroupOrder.X (r.point i)))) ^ 2) ^ 512 *
        encoder message i := by
  have htwo : (2 : K) ≠ 0 := by
    intro hzero
    apply AspisCircleGroupOrder.two_ne_zero_ZModP
    apply FaithfulSMul.algebraMap_injective (ZMod AspisCircleGroupOrder.P) K
    simpa only [map_ofNat, map_zero] using hzero
  letI : NeZero (2 : K) := ⟨htwo⟩
  have hon := congrArg (algebraMap (ZMod AspisCircleGroupOrder.P) K)
    (r.point i).2
  have honK :
      (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (AspisCircleGroupOrder.X (r.point i))) ^ 2 +
        (algebraMap (ZMod AspisCircleGroupOrder.P) K (r.point i).1.2) ^ 2 = 1 := by
    simpa only [AspisCircleGroupOrder.OnCircle, AspisCircleGroupOrder.X,
      map_add, map_pow, map_one] using hon
  have hxK :
      algebraMap (ZMod AspisCircleGroupOrder.P) K
          (AspisCircleGroupOrder.X (r.point i)) ≠ -1 := by
    intro h
    apply r.avoids_west_pole i
    apply FaithfulSMul.algebraMap_injective (ZMod AspisCircleGroupOrder.P) K
    simpa only [map_neg, map_one] using h
  have h := circleNumerator_eval_stereo (r.p0 message) (r.p1 message)
    (r.p0_degree_lt message) (r.p1_degree_lt message)
    (algebraMap (ZMod AspisCircleGroupOrder.P) K
      (AspisCircleGroupOrder.X (r.point i)))
    (algebraMap (ZMod AspisCircleGroupOrder.P) K (r.point i).1.2)
    honK hxK
  dsimp only at h
  rw [← r.encoder_eq_circle_eval message i] at h
  have hchart :
      algebraMap (ZMod AspisCircleGroupOrder.P) K
          ((r.point i).1.2 /
            (1 + AspisCircleGroupOrder.X (r.point i))) =
        algebraMap (ZMod AspisCircleGroupOrder.P) K (r.point i).1.2 /
          (1 + algebraMap (ZMod AspisCircleGroupOrder.P) K
            (AspisCircleGroupOrder.X (r.point i))) := by
    exact algebraMap_div_one_add _ _
  rw [hchart]
  simpa only [AspisCircleGroupOrder.X] using h

/-- Numerator injectivity follows from coefficient-pair injectivity and the
proved algebra of the stereographic transform. -/
theorem CirclePolynomialRealization.numerator_injective
    [Fintype K] [DecidableEq K]
    {encoder : Message → Fin wordSize → K}
    (r : CirclePolynomialRealization encoder) :
    Function.Injective
      (fun message => circleNumerator (r.p0 message) (r.p1 message)) := by
  intro left right heq
  apply r.coefficient_pair_injective
  apply Prod.ext
  · exact (circleNumerator_pair_eq _ _ _ _
      (r.p0_degree_lt left) (r.p1_degree_lt left)
      (r.p0_degree_lt right) (r.p1_degree_lt right) heq).1
  · exact (circleNumerator_pair_eq _ _ _ _
      (r.p0_degree_lt left) (r.p1_degree_lt left)
      (r.p0_degree_lt right) (r.p1_degree_lt right) heq).2

/-- Stereographic parameters remain distinct after embedding into `K`. -/
theorem CirclePolynomialRealization.parameter_injective
    {encoder : Message → Fin wordSize → K}
    (r : CirclePolynomialRealization encoder) :
    Function.Injective (fun i =>
      algebraMap (ZMod AspisCircleGroupOrder.P) K
        ((r.point i).1.2 / (1 + AspisCircleGroupOrder.X (r.point i)))) := by
  intro i j hij
  have hbase :
      (r.point i).1.2 / (1 + AspisCircleGroupOrder.X (r.point i)) =
        (r.point j).1.2 / (1 + AspisCircleGroupOrder.X (r.point j)) := by
    exact (FaithfulSMul.algebraMap_injective
      (ZMod AspisCircleGroupOrder.P) K) hij
  apply r.point_injective
  apply AspisCircleGroupOrder.stereo_injective
  have hi : (r.point i).1.1 ≠ -1 := r.avoids_west_pole i
  have hj : (r.point j).1.1 ≠ -1 := r.avoids_west_pole j
  unfold AspisCircleGroupOrder.stereo
  rw [if_neg hi, if_neg hj, Option.some.injEq]
  simpa only [AspisCircleGroupOrder.X] using hbase

/-- Distinct messages in a realized degree-`<512` circle code agree in at
most `1024` coordinates.  This is the concrete circle root bound used by the
initial V5 list-size proof. -/
theorem agreementSet_card_le_1024
    [Fintype K] [DecidableEq K]
    (encoder : Message → Fin wordSize → K)
    (r : CirclePolynomialRealization encoder)
    (left right : Message) (hne : left ≠ right) :
    (agreementSet (encoder left) (encoder right)).card ≤ 1024 := by
  classical
  let difference := circleNumerator (r.p0 left) (r.p1 left) -
    circleNumerator (r.p0 right) (r.p1 right)
  have hdifference : difference ≠ 0 := by
    intro hzero
    apply hne
    apply r.numerator_injective
    exact sub_eq_zero.mp hzero
  have hdegree : difference.natDegree ≤ 1024 := by
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le (circleNumerator_natDegree_le _ _)
        (circleNumerator_natDegree_le _ _))
  let parameters : Fin wordSize → K := fun i =>
    algebraMap (ZMod AspisCircleGroupOrder.P) K
      ((r.point i).1.2 / (1 + AspisCircleGroupOrder.X (r.point i)))
  let rootsHit := (agreementSet (encoder left) (encoder right)).image parameters
  have hsubset : rootsHit.val ⊆ difference.roots := by
    intro parameter hparameter
    change parameter ∈ Finset.image parameters
      (agreementSet (encoder left) (encoder right)) at hparameter
    obtain ⟨i, hiagree, hparameterEq⟩ := Finset.mem_image.mp hparameter
    rw [Polynomial.mem_roots hdifference]
    simp only [Polynomial.IsRoot, difference, Polynomial.eval_sub, sub_eq_zero]
    rw [← hparameterEq]
    rw [r.encoder_numerator_eval, r.encoder_numerator_eval]
    congr 1
    simpa [agreementSet] using hiagree
  calc
    (agreementSet (encoder left) (encoder right)).card = rootsHit.card := by
      exact (Finset.card_image_of_injective _ r.parameter_injective).symm
    _ ≤ difference.natDegree := Polynomial.card_le_degree_of_subset_roots hsubset
    _ ≤ 1024 := hdegree

/-! ## Exact-domain constructor -/

/-- Specialize the generic realization to the exact deployed half-odd coset.
Only the coefficient/evaluation facts remain to be supplied. -/
noncomputable def exactInitialCosetRealization
    (encoder : Message → Fin (2 ^ 19) → K)
    (p0 p1 : Message → K[X])
    (hp0 : ∀ message, (p0 message).natDegree < 512)
    (hp1 : ∀ message, (p1 message).natDegree < 512)
    (hinjective : Function.Injective (fun message => (p0 message, p1 message)))
    (heval : ∀ message i,
      encoder message i =
        (p0 message).eval
            (algebraMap (ZMod AspisCircleGroupOrder.P) K
              (AspisCircleGroupOrder.X (initialCirclePoint i))) +
          algebraMap (ZMod AspisCircleGroupOrder.P) K
              (initialCirclePoint i).1.2 *
            (p1 message).eval
              (algebraMap (ZMod AspisCircleGroupOrder.P) K
                (AspisCircleGroupOrder.X (initialCirclePoint i)))) :
    CirclePolynomialRealization encoder where
  point := initialCirclePoint
  point_injective := initialCirclePoint_injective
  avoids_west_pole := initialCirclePoint_x_ne_neg_one
  p0 := p0
  p1 := p1
  p0_degree_lt := hp0
  p1_degree_lt := hp1
  coefficient_pair_injective := hinjective
  encoder_eq_circle_eval := heval

/-- The exact half-odd coset constructor immediately yields the released
`1024` overlap bound. -/
theorem exactInitialCoset_agreement_card_le_1024
    [Fintype K] [DecidableEq K]
    (encoder : Message → Fin (2 ^ 19) → K)
    (p0 p1 : Message → K[X])
    (hp0 : ∀ message, (p0 message).natDegree < 512)
    (hp1 : ∀ message, (p1 message).natDegree < 512)
    (hinjective : Function.Injective (fun message => (p0 message, p1 message)))
    (heval : ∀ message i,
      encoder message i =
        (p0 message).eval
            (algebraMap (ZMod AspisCircleGroupOrder.P) K
              (AspisCircleGroupOrder.X (initialCirclePoint i))) +
          algebraMap (ZMod AspisCircleGroupOrder.P) K
              (initialCirclePoint i).1.2 *
            (p1 message).eval
              (algebraMap (ZMod AspisCircleGroupOrder.P) K
                (AspisCircleGroupOrder.X (initialCirclePoint i))))
    (left right : Message) (hne : left ≠ right) :
    (agreementSet (encoder left) (encoder right)).card ≤ 1024 :=
  agreementSet_card_le_1024 encoder
    (exactInitialCosetRealization encoder p0 p1 hp0 hp1 hinjective heval)
    left right hne

/-! ## The maintained explicit `encoder0` -/

open AspisV5FriCoherentCandidateExtraction
open AspisV5FriConcreteEncoderCommutation
open AspisV5ComponentCConcreteFoldLinearity

/-- For the maintained explicit initial encoder, the distance theorem now
needs only its ordinary circle-polynomial evaluation identity and injective
coefficient conversion.  It does not assume a distance or decoding claim. -/
theorem concrete_encoder0_agreement_card_le_1024
    [Fintype K] [DecidableEq K]
    (schedule : FixedSchedule (ZMod AspisCircleGroupOrder.P) K)
    (points : EvaluationPoints (ZMod AspisCircleGroupOrder.P))
    (p0 p1 : Coeff0 K → K[X])
    (hp0 : ∀ message, (p0 message).natDegree < 512)
    (hp1 : ∀ message, (p1 message).natDegree < 512)
    (hinjective : Function.Injective (fun message => (p0 message, p1 message)))
    (heval : ∀ message i,
      encoder0 schedule points message i =
        (p0 message).eval
            (algebraMap (ZMod AspisCircleGroupOrder.P) K
              (AspisCircleGroupOrder.X (initialCirclePoint i))) +
          algebraMap (ZMod AspisCircleGroupOrder.P) K
              (initialCirclePoint i).1.2 *
            (p1 message).eval
              (algebraMap (ZMod AspisCircleGroupOrder.P) K
                (AspisCircleGroupOrder.X (initialCirclePoint i))))
    (left right : Coeff0 K) (hne : left ≠ right) :
    (agreementSet (encoder0 schedule points left)
      (encoder0 schedule points right)).card ≤ 1024 :=
  exactInitialCoset_agreement_card_le_1024
    (fun message => encoder0 schedule points message)
    p0 p1 hp0 hp1 hinjective heval left right hne

/-- The same result packaged in the interface consumed by the initial list
bound.  Its premises are exact evaluation/coefficient facts, not distance. -/
theorem concrete_initialEncoderDistance
    [Fintype K] [DecidableEq K]
    (schedule : FixedSchedule (ZMod AspisCircleGroupOrder.P) K)
    (points : EvaluationPoints (ZMod AspisCircleGroupOrder.P))
    (p0 p1 : Coeff0 K → K[X])
    (hp0 : ∀ message, (p0 message).natDegree < 512)
    (hp1 : ∀ message, (p1 message).natDegree < 512)
    (hinjective : Function.Injective (fun message => (p0 message, p1 message)))
    (heval : ∀ message i,
      encoder0 schedule points message i =
        (p0 message).eval
            (algebraMap (ZMod AspisCircleGroupOrder.P) K
              (AspisCircleGroupOrder.X (initialCirclePoint i))) +
          algebraMap (ZMod AspisCircleGroupOrder.P) K
              (initialCirclePoint i).1.2 *
            (p1 message).eval
              (algebraMap (ZMod AspisCircleGroupOrder.P) K
                (AspisCircleGroupOrder.X (initialCirclePoint i)))) :
    InitialEncoderDistance (concreteCodeEncoders schedule points) := by
  intro left right hne
  exact concrete_encoder0_agreement_card_le_1024 schedule points p0 p1
    hp0 hp1 hinjective heval left right hne

/-! ## Axiom audit -/

#print axioms initialCirclePoint_injective
#print axioms initialCirclePoint_x_ne_neg_one
#print axioms initialStereo_injective
#print axioms circleNumerator_natDegree_le
#print axioms circleNumerator_pair_eq
#print axioms agreementSet_card_le_1024
#print axioms concrete_initialEncoderDistance

end AspisV5FriCircleEncoderDistance
