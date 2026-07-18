import Mathlib
import AspisFormal.CircleGroupOrder
import AspisFormal.CircleFibreRoots

set_option maxRecDepth 20000

/-!
# Discrete availability facts for the rate-1/512 circle schedule

The component-A determinant experiment uses 96 independently chosen rows.  The
spend wire does not release that schedule: it samples 18 distinct arity-four
fibre indices from a universe of `2^17` fibres, and hence authenticates 72
distinct layer-zero codeword positions.  This file records that distinction
and proves the other local algebraic fact needed by the aligned-reserve model:
the three line-twiddle factors expected for message row 896 are nonzero over
the deployed group constants.

The results here deliberately stop short of a hiding theorem for the complete
released view.  In particular, 72 distinct positions do not supply the
96-row square schedule used by the diagnostic determinant.  A production
proof instead needs a rectangular full-row-rank theorem for the actual 72-row
evaluation map, followed by one joint rank argument for every other released
mask functional.
-/

namespace AspisCircleDiscreteAvailability

/-! ## Wire geometry -/

def queryCount : ℕ := 18
def fibreSlots : ℕ := 4
def maskWidth : ℕ := 96
def fibreCount : ℕ := 2 ^ 17

theorem opened_position_count : queryCount * fibreSlots = 72 := by
  norm_num [queryCount, fibreSlots]

theorem opened_positions_lt_maskWidth : queryCount * fibreSlots < maskWidth := by
  norm_num [queryCount, fibreSlots, maskWidth]

theorem queries_fit_fibre_universe : queryCount ≤ fibreCount := by
  norm_num [queryCount, fibreCount]

/-- The layer-zero codeword position belonging to fibre `q` and slot `s`. -/
def fibrePosition (q s : ℕ) : ℕ := fibreSlots * q + s

/-- Disjoint arity-four fibres really do give distinct codeword positions.
This is the exact combinatorial consequence of sampling fibre indices without
replacement; it says nothing yet about linear independence of their leakage
rows. -/
theorem fibrePosition_injective
    {q₁ q₂ s₁ s₂ : ℕ}
    (hs₁ : s₁ < fibreSlots) (hs₂ : s₂ < fibreSlots)
    (h : fibrePosition q₁ s₁ = fibrePosition q₂ s₂) :
    q₁ = q₂ ∧ s₁ = s₂ := by
  norm_num [fibrePosition, fibreSlots] at h hs₁ hs₂ ⊢
  constructor <;> omega

/-- Expand one schedule of fibre indices into its authenticated layer-zero
codeword positions. -/
def expandedPosition {q : ℕ} (queries : Fin q → Fin fibreCount)
    (entry : Fin q × Fin fibreSlots) : Fin (fibreSlots * fibreCount) :=
  ⟨fibrePosition (queries entry.1) entry.2, by
    have hq := (queries entry.1).isLt
    have hs := entry.2.isLt
    simp only [fibrePosition, fibreSlots, fibreCount] at hq hs ⊢
    omega⟩

/-- Without replacement is exactly injectivity of `queries`.  It implies the
expanded four-slot codeword positions are distinct because the fibres are
disjoint. -/
theorem expandedPosition_injective {q : ℕ} (queries : Fin q → Fin fibreCount)
    (hqueries : Function.Injective queries) :
    Function.Injective (expandedPosition queries) := by
  intro a b hab
  have hval : fibrePosition (queries a.1) a.2 = fibrePosition (queries b.1) b.2 :=
    congrArg Fin.val hab
  have hp := fibrePosition_injective a.2.isLt b.2.isLt hval
  apply Prod.ext
  · exact hqueries (Fin.ext hp.1)
  · exact Fin.ext hp.2

/-- The concrete q18 schedule therefore authenticates 72 distinct positions,
provided its fibre sampler returned without replacement. -/
theorem spend_opened_positions_injective
    (queries : Fin queryCount → Fin fibreCount)
    (hqueries : Function.Injective queries) :
    Function.Injective (expandedPosition queries) :=
  expandedPosition_injective queries hqueries

/-- There cannot be an injective 96-row schedule whose rows are drawn only
from the 72 positions opened by one spend proof.  Thus the existing square
determinant diagnostic is not itself a model of the wire schedule. -/
theorem no_square_schedule_from_opened_positions :
    ¬ ∃ f : Fin maskWidth → Fin (queryCount * fibreSlots), Function.Injective f := by
  rintro ⟨f, hf⟩
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hcard
  norm_num [maskWidth, queryCount, fibreSlots] at hcard

/-! ## The rectangular four-slot fibre minor -/

open Matrix

/-- Two independent sign bits enumerate the four circle points in one fibre. -/
abbrev FibreSign := Fin 2 × Fin 2

/-- The order-two Hadamard transform. -/
def hadamard2 (K : Type*) [Field K] : Matrix (Fin 2) (Fin 2) K :=
  !![1, 1; 1, -1]

/-- The four-character transform on the two sign bits. -/
def hadamard4 (K : Type*) [Field K] : Matrix FibreSign FibreSign K :=
  Matrix.kronecker (hadamard2 K) (hadamard2 K)

/-- Apply one of the two sign choices to a coordinate. -/
def signedCoordinate {K : Type*} [Field K] (sign : Fin 2) (z : K) : K :=
  if sign = 0 then z else -z

lemma hadamard2_mul_pow {K : Type*} [Field K] (sign character : Fin 2) (z : K) :
    hadamard2 K sign character * z ^ (character : ℕ) =
      signedCoordinate sign z ^ (character : ℕ) := by
  fin_cases sign <;> fin_cases character <;> simp [hadamard2, signedCoordinate]

lemma hadamard2_det {K : Type*} [Field K] : (hadamard2 K).det = -2 := by
  simp [hadamard2, Matrix.det_fin_two]
  ring

lemma hadamard4_det_ne_zero {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) :
    (hadamard4 K).det ≠ 0 := by
  simp only [hadamard4, Matrix.kronecker]
  rw [Matrix.det_kronecker, hadamard2_det]
  simp only [Fintype.card_fin]
  exact mul_ne_zero (pow_ne_zero 2 (neg_ne_zero.mpr h2))
    (pow_ne_zero 2 (neg_ne_zero.mpr h2))

/-- Character-dependent nonzero factor in one four-slot fibre.  The two
character bits select `1`, `x`, `y`, or `x*y`. -/
def fibreScale {K : Type*} [Field K] {n : ℕ}
    (x y : Fin n → K) (character : FibreSign) (i : Fin n) : K :=
  x i ^ (character.1 : ℕ) * y i ^ (character.2 : ℕ)

lemma fibreScale_ne_zero {K : Type*} [Field K] {n : ℕ}
    (x y : Fin n → K) (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (character : FibreSign) (i : Fin n) : fibreScale x y character i ≠ 0 := by
  exact mul_ne_zero (pow_ne_zero _ (hx i)) (pow_ne_zero _ (hy i))

lemma hadamard4_mul_fibreScale {K : Type*} [Field K] {n : ℕ}
    (x y : Fin n → K) (i : Fin n) (sign character : FibreSign) :
    hadamard4 K sign character * fibreScale x y character i =
      signedCoordinate sign.1 (x i) ^ (character.1 : ℕ) *
        signedCoordinate sign.2 (y i) ^ (character.2 : ℕ) := by
  rw [hadamard4]
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, fibreScale]
  calc
    (hadamard2 K sign.1 character.1 * hadamard2 K sign.2 character.2) *
        (x i ^ (character.1 : ℕ) * y i ^ (character.2 : ℕ)) =
      (hadamard2 K sign.1 character.1 * x i ^ (character.1 : ℕ)) *
        (hadamard2 K sign.2 character.2 * y i ^ (character.2 : ℕ)) := by ring
    _ = _ := by rw [hadamard2_mul_pow, hadamard2_mul_pow]

lemma signedCoordinate_even_pow {K : Type*} [Field K]
    (sign : Fin 2) (z : K) (degree : ℕ) :
    signedCoordinate sign z ^ (2 * degree) = (z ^ 2) ^ degree := by
  calc
    signedCoordinate sign z ^ (2 * degree) =
        (signedCoordinate sign z ^ 2) ^ degree := by rw [pow_mul]
    _ = (z ^ 2) ^ degree := by
      congr 1
      fin_cases sign <;> simp [signedCoordinate]

/-- One character block after the four-slot Hadamard transform: a nonzero
row diagonal times a Vandermonde in the distinct fibre nodes `x²`. -/
noncomputable def fibreCharacterBlock {K : Type*} [Field K] {n : ℕ}
    (x y : Fin n → K) (character : FibreSign) : Matrix (Fin n) (Fin n) K :=
  Matrix.diagonal (fibreScale x y character) *
    Matrix.vandermonde (fun i ↦ x i ^ 2)

theorem fibreCharacterBlock_det_ne_zero {K : Type*} [Field K] {n : ℕ}
    (x y : Fin n → K) (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (hnode : Function.Injective (fun i ↦ x i ^ 2)) (character : FibreSign) :
    (fibreCharacterBlock x y character).det ≠ 0 := by
  rw [fibreCharacterBlock, Matrix.det_mul, Matrix.det_diagonal]
  exact mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ fibreScale_ne_zero x y hx hy character i))
    ((Matrix.det_vandermonde_ne_zero_iff).mpr hnode)

/-- A square `4n × 4n` minor of the block-form circle evaluation map.  Its
columns are, for every degree `d<n`, the four functions
`x^(2d)`, `x^(2d+1)`, `y*x^(2d)`, and `y*x^(2d+1)`.

It is written in its exact factorised form: a four-character transform in
each fibre, followed by four Vandermonde blocks. -/
noncomputable def fibreEvaluationMinor {K : Type*} [Field K] {n : ℕ}
    (x y : Fin n → K) : Matrix (Fin n × FibreSign) (Fin n × FibreSign) K :=
  Matrix.kronecker (1 : Matrix (Fin n) (Fin n) K) (hadamard4 K) *
    Matrix.blockDiagonal (fibreCharacterBlock x y)

theorem fibreEvaluationMinor_apply {K : Type*} [Field K] {n : ℕ}
    (x y : Fin n → K) (i degree : Fin n) (sign character : FibreSign) :
    fibreEvaluationMinor x y (i, sign) (degree, character) =
      hadamard4 K sign character * fibreScale x y character i *
        (x i ^ 2) ^ (degree : ℕ) := by
  classical
  simp [fibreEvaluationMinor, Matrix.mul_apply, fibreCharacterBlock,
    Matrix.blockDiagonal_apply, Matrix.vandermonde_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.diagonal_apply]
  rw [Fintype.sum_prod_type]
  simp
  ring

/-- Entrywise binding to the ordinary block-form circle basis on a complete
four-point sign fibre.  Character bit 0 selects the parity of the x exponent;
character bit 1 selects the y block. -/
theorem fibreEvaluationMinor_is_block_eval {K : Type*} [Field K] {n : ℕ}
    (x y : Fin n → K) (i degree : Fin n) (sign character : FibreSign) :
    fibreEvaluationMinor x y (i, sign) (degree, character) =
      signedCoordinate sign.1 (x i) ^ (2 * (degree : ℕ) + (character.1 : ℕ)) *
        signedCoordinate sign.2 (y i) ^ (character.2 : ℕ) := by
  rw [fibreEvaluationMinor_apply, hadamard4_mul_fibreScale]
  rw [← signedCoordinate_even_pow sign.1 (x i) degree]
  rw [pow_add]
  ring

theorem fibreEvaluationMinor_det_ne_zero {K : Type*} [Field K] {n : ℕ}
    (x y : Fin n → K) (h2 : (2 : K) ≠ 0)
    (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (hnode : Function.Injective (fun i ↦ x i ^ 2)) :
    (fibreEvaluationMinor x y).det ≠ 0 := by
  rw [fibreEvaluationMinor, Matrix.det_mul]
  apply mul_ne_zero
  · simp only [Matrix.kronecker]
    rw [Matrix.det_kronecker]
    simp only [Matrix.det_one, one_pow, one_mul, Fintype.card_fin]
    exact pow_ne_zero n (hadamard4_det_ne_zero h2)
  · rw [Matrix.det_blockDiagonal]
    exact Finset.prod_ne_zero_iff.mpr
      (fun character _ ↦ fibreCharacterBlock_det_ne_zero x y hx hy hnode character)

/-! ### Discharging the minor hypotheses on deployed fibre representatives -/

open AspisCircleGroupOrder

/-- The quarter-turn `g^(2^29)` has x-coordinate zero.  This concrete check is
29 repeated squarings in the Lean kernel, using the already verified deployed
generator. -/
lemma quarterTurn_x_zero : X (g ^ (2 ^ 29 : ℤ)) = 0 := by
  rw [show (2 ^ 29 : ℤ) = ((2 ^ 29 : ℕ) : ℤ) by norm_num, zpow_natCast]
  rw [← sq_iterate 29 g]
  decide

/-- Exponent of the standard representative of deployed fibre `j`. -/
def representativeExp (j : ℕ) : ℤ :=
  (2 : ℤ) ^ 11 + (2 : ℤ) ^ 13 * j

def representativeX (j : ℕ) : ZMod P := X (g ^ representativeExp j)
def representativeY (j : ℕ) : ZMod P := (g ^ representativeExp j).1.2

/-- Doubling a circle point sends its x-coordinate to `2x²-1`. -/
lemma X_sq (z : C) : X (z ^ 2) = 2 * (X z) ^ 2 - 1 := by
  rw [pow_two]
  unfold X
  rw [mul_re]
  have hz := z.2
  simp only [OnCircle] at hz
  calc
    z.1.1 * z.1.1 - z.1.2 * z.1.2 =
        2 * z.1.1 ^ 2 - (z.1.1 ^ 2 + z.1.2 ^ 2) := by ring
    _ = 2 * z.1.1 ^ 2 - 1 := by rw [hz]

lemma representative_sq (j : ℕ) :
    (g ^ representativeExp j) ^ 2 =
      g ^ AspisCircleFibreRoots.fiberRootExp j := by
  calc
    (g ^ representativeExp j) ^ 2 = (g ^ representativeExp j) ^ (2 : ℤ) := by
      rw [zpow_two, pow_two]
    _ = g ^ (representativeExp j * 2) := (zpow_mul g (representativeExp j) 2).symm
    _ = g ^ AspisCircleFibreRoots.fiberRootExp j := by
      congr 1
      norm_num [representativeExp, AspisCircleFibreRoots.fiberRootExp]
      ring

theorem representative_x_ne_zero (j : ℕ) : representativeX j ≠ 0 := by
  intro hz
  have hx : X (g ^ representativeExp j) = X (g ^ (2 ^ 29 : ℤ)) := by
    rw [representativeX] at hz
    rw [hz, quarterTurn_x_zero]
  have hm := (sameXCoord_exp (representativeExp j) (2 ^ 29 : ℤ)).mp hx
  norm_num [representativeExp, Int.ModEq] at hm
  rcases hm with hm | hm <;> omega

theorem representative_y_ne_zero (j : ℕ) : representativeY j ≠ 0 := by
  intro hy
  have hon := (g ^ representativeExp j).2
  simp only [OnCircle] at hon
  have hx2 : representativeX j ^ 2 = 1 := by
    unfold representativeX X
    unfold representativeY at hy
    rw [hy] at hon
    simpa using hon
  have hx2' : X (g ^ representativeExp j) ^ 2 = 1 := by
    simpa only [representativeX] using hx2
  have hdouble :
      X (g ^ AspisCircleFibreRoots.fiberRootExp j) = X (g ^ (0 : ℤ)) := by
    rw [← representative_sq, X_sq, hx2']
    norm_num [X]
  have hm := (sameXCoord_exp (AspisCircleFibreRoots.fiberRootExp j) 0).mp hdouble
  unfold AspisCircleFibreRoots.SameXCoord AspisCircleFibreRoots.fiberRootExp
    Int.ModEq at hm
  rcases hm with hm | hm <;> omega

theorem representative_x_sq_injective_on_queries
    (queries : Fin queryCount → Fin fibreCount)
    (hqueries : Function.Injective queries) :
    Function.Injective (fun i ↦ representativeX (queries i) ^ 2) := by
  intro i j hij
  simp only [representativeX] at hij
  have hdouble :
      X (g ^ AspisCircleFibreRoots.fiberRootExp (queries i)) =
        X (g ^ AspisCircleFibreRoots.fiberRootExp (queries j)) := by
    rw [← representative_sq, ← representative_sq, X_sq, X_sq, hij]
  have hm := (sameXCoord_exp
    (AspisCircleFibreRoots.fiberRootExp (queries i))
    (AspisCircleFibreRoots.fiberRootExp (queries j))).mp hdouble
  have hq : (queries i : ℕ) = queries j :=
    AspisCircleFibreRoots.fiber_roots_distinct (queries i) (queries j)
      (by exact (queries i).isLt)
      (by exact (queries j).isLt) hm
  exact hqueries (Fin.ext hq)

/-- The q18 full-fibre schedule has an explicit nonsingular 72-column minor.
It uses x degrees only through 35, so it lies inside each 48-column block of
the v5 mask. -/
theorem spend_fibre_minor_det_ne_zero
    (queries : Fin queryCount → Fin fibreCount)
    (hqueries : Function.Injective queries) :
    (fibreEvaluationMinor
      (fun i ↦ representativeX (queries i))
      (fun i ↦ representativeY (queries i))).det ≠ 0 := by
  apply fibreEvaluationMinor_det_ne_zero
  · exact AspisCircleFibreRoots.two_ne_zero_P
  · exact fun i ↦ representative_x_ne_zero (queries i)
  · exact fun i ↦ representative_y_ne_zero (queries i)
  · exact representative_x_sq_injective_on_queries queries hqueries

theorem spend_minor_degree_lt_48 (degree : Fin queryCount) (parity : Fin 2) :
    2 * (degree : ℕ) + (parity : ℕ) < 48 := by
  have hd := degree.isLt
  have hp := parity.isLt
  norm_num [queryCount] at hd
  omega

/-! ## Nonvanishing of the aligned row-896 factor -/

open AspisCircleGroupOrder

/-- Exponent of entry `index` in line-twiddle layer `layer` for the log-19
encoder.  The encoder starts from the half-odds coset
`g^(2^11) · ⟨g^(2^13)⟩`; every line layer doubles both exponents.  Bit
reversal only permutes `index`, so nonvanishing can be proved for every index
in the layer. -/
def lineTwiddleExp (layer index : ℕ) : ℤ :=
  (2 : ℤ) ^ (11 + layer) + (2 : ℤ) ^ (13 + layer) * index

private theorem lineTwiddle6_ne_zero (index : ℕ) :
    X (g ^ lineTwiddleExp 6 index) ≠ 0 := by
  intro hz
  have hx : X (g ^ lineTwiddleExp 6 index) = X (g ^ (2 ^ 29 : ℤ)) := by
    rw [hz, quarterTurn_x_zero]
  have hm := (sameXCoord_exp (lineTwiddleExp 6 index) (2 ^ 29 : ℤ)).mp hx
  norm_num [lineTwiddleExp, Int.ModEq] at hm
  rcases hm with hm | hm <;> omega

private theorem lineTwiddle7_ne_zero (index : ℕ) :
    X (g ^ lineTwiddleExp 7 index) ≠ 0 := by
  intro hz
  have hx : X (g ^ lineTwiddleExp 7 index) = X (g ^ (2 ^ 29 : ℤ)) := by
    rw [hz, quarterTurn_x_zero]
  have hm := (sameXCoord_exp (lineTwiddleExp 7 index) (2 ^ 29 : ℤ)).mp hx
  norm_num [lineTwiddleExp, Int.ModEq] at hm
  rcases hm with hm | hm <;> omega

private theorem lineTwiddle8_ne_zero (index : ℕ) :
    X (g ^ lineTwiddleExp 8 index) ≠ 0 := by
  intro hz
  have hx : X (g ^ lineTwiddleExp 8 index) = X (g ^ (2 ^ 29 : ℤ)) := by
    rw [hz, quarterTurn_x_zero]
  have hm := (sameXCoord_exp (lineTwiddleExp 8 index) (2 ^ 29 : ℤ)).mp hx
  norm_num [lineTwiddleExp, Int.ModEq] at hm
  rcases hm with hm | hm <;> omega

/-- Abstract sign chosen by one FFT output bit. -/
def signed (negative : Bool) (x : ZMod P) : ZMod P :=
  if negative then -x else x

lemma signed_ne_zero {negative : Bool} {x : ZMod P} (hx : x ≠ 0) :
    signed negative x ≠ 0 := by
  cases negative <;> simp [signed, hx]

/-- The three-factor shape expected from binary row 896
(`896 = 2^7 + 2^8 + 2^9`).  The three indices range over the corresponding
log-19 line-twiddle layers; signs account for the output bits.  Identifying
these abstract indices and signs with the Rust encoder remains a separate
source-correspondence obligation. -/
def row896Factor
    (i₆ : Fin (2 ^ 11)) (i₇ : Fin (2 ^ 10)) (i₈ : Fin (2 ^ 9))
    (s₆ s₇ s₈ : Bool) : ZMod P :=
  signed s₆ (X (g ^ lineTwiddleExp 6 i₆)) *
    signed s₇ (X (g ^ lineTwiddleExp 7 i₇)) *
      signed s₈ (X (g ^ lineTwiddleExp 8 i₈))

/-- Every product in the modelled row-896 factor family is nonzero.  A later
Rust-to-Lean binding must still prove that the real encoder's bit reversal,
layer indices and output signs instantiate this family at each codeword
position. -/
theorem row896Factor_ne_zero
    (i₆ : Fin (2 ^ 11)) (i₇ : Fin (2 ^ 10)) (i₈ : Fin (2 ^ 9))
    (s₆ s₇ s₈ : Bool) : row896Factor i₆ i₇ i₈ s₆ s₇ s₈ ≠ 0 := by
  unfold row896Factor
  exact mul_ne_zero
    (mul_ne_zero
      (signed_ne_zero (lineTwiddle6_ne_zero i₆))
      (signed_ne_zero (lineTwiddle7_ne_zero i₇)))
    (signed_ne_zero (lineTwiddle8_ne_zero i₈))

#print axioms fibrePosition_injective
#print axioms spend_opened_positions_injective
#print axioms no_square_schedule_from_opened_positions
#print axioms fibreEvaluationMinor_is_block_eval
#print axioms fibreEvaluationMinor_det_ne_zero
#print axioms spend_fibre_minor_det_ne_zero
#print axioms quarterTurn_x_zero
#print axioms row896Factor_ne_zero

end AspisCircleDiscreteAvailability
