import AspisFormal.V5FriConcreteEncoderApplicability
import AspisFormal.SoundnessLedger

/-!
# Exact batching of the V5 constraint lanes

The production state-only evaluator combines one copy lane, sixteen semantic
lanes, and four Poseidon lanes with powers of the transcript challenge
`theta`.  The Rust loops visit each array in reverse while updating
`composition = theta * composition + lane`.  Consequently the final powers
are, in order,

* Poseidon lanes `0..3` at powers `0..3`;
* semantic lanes `0..15` at powers `4..19`; and
* the copy lane at power `20`.

This file proves that exact ordering, proves that a nonzero fixed lane vector
can vanish for at most twenty field challenges, and states the transcript
ordering condition needed to use that root count.  It does not claim that the
production transcript samples an ideal uniform field element; that remains a
separate hash/Fiat--Shamir assumption.
-/

namespace AspisV5ConstraintLaneBatching

open Polynomial
open AspisV5FriConcreteEncoderApplicability

variable {K : Type*} [Field K]

abbrev ConstraintLane := Fin 21

/-- The exact final coefficient vector produced by the two reverse Horner
loops in `atomic_state_only_composition_parts_compiled_v3`. -/
def constraintLaneVector
    (poseidon : Fin 4 → K) (semantic : Fin 16 → K) (copy : K) :
    ConstraintLane → K := fun lane =>
  if hposeidon : lane.val < 4 then
    poseidon ⟨lane.val, hposeidon⟩
  else if hsemantic : lane.val < 20 then
    semantic ⟨lane.val - 4, by omega⟩
  else
    copy

@[simp]
theorem constraintLaneVector_poseidon
    (poseidon : Fin 4 → K) (semantic : Fin 16 → K) (copy : K)
    (lane : Fin 4) :
    constraintLaneVector poseidon semantic copy
        ⟨lane.val, lane.isLt.trans (by decide : 4 < 21)⟩ = poseidon lane := by
  simp [constraintLaneVector, lane.isLt]

@[simp]
theorem constraintLaneVector_semantic
    (poseidon : Fin 4 → K) (semantic : Fin 16 → K) (copy : K)
    (lane : Fin 16) :
    constraintLaneVector poseidon semantic copy
        ⟨lane.val + 4, by omega⟩ = semantic lane := by
  simp [constraintLaneVector]

@[simp]
theorem constraintLaneVector_copy
    (poseidon : Fin 4 → K) (semantic : Fin 16 → K) (copy : K) :
    constraintLaneVector poseidon semantic copy (20 : ConstraintLane) = copy := by
  simp [constraintLaneVector]

/-- Scalar-power batch of all twenty-one production constraint lanes. -/
def width21Batch (values : ConstraintLane → K) (theta : K) : K :=
  ∑ lane : ConstraintLane, values lane * theta ^ lane.val

@[simp]
theorem eval_monomialPolynomial_width21
    (values : ConstraintLane → K) (theta : K) :
    (monomialPolynomial values).eval theta = width21Batch values theta := by
  simp [monomialPolynomial, width21Batch, Polynomial.eval_finsetSum]

/-- Literal mathematical spelling of a Rust reverse-iterator Horner loop. -/
def reverseHorner (lanes : List K) (theta accumulator : K) : K :=
  lanes.foldr (fun lane current => theta * current + lane) accumulator

/-- The two source loops: semantic lanes are folded into the copy lane first,
then Poseidon lanes are folded around that result. -/
def sourceConstraintComposition
    (poseidon : Fin 4 → K) (semantic : Fin 16 → K)
    (copy theta : K) : K :=
  reverseHorner (List.ofFn poseidon) theta
    (reverseHorner (List.ofFn semantic) theta copy)

/-- The source-shaped two-loop computation is exactly the width-21
scalar-power batch with the deployed lane order. -/
theorem sourceConstraintComposition_eq_width21Batch
    (poseidon : Fin 4 → K) (semantic : Fin 16 → K)
    (copy theta : K) :
    sourceConstraintComposition poseidon semantic copy theta =
      width21Batch (constraintLaneVector poseidon semantic copy) theta := by
  simp [sourceConstraintComposition, reverseHorner, width21Batch,
    constraintLaneVector, Fin.sum_univ_succ]
  ring

/-- The exact source computation is zero iff its width-21 polynomial
evaluates to zero. -/
theorem sourceConstraintComposition_eq_zero_iff_polynomial_eval_eq_zero
    (poseidon : Fin 4 → K) (semantic : Fin 16 → K)
    (copy theta : K) :
    sourceConstraintComposition poseidon semantic copy theta = 0 ↔
      (monomialPolynomial
        (constraintLaneVector poseidon semantic copy)).eval theta = 0 := by
  rw [sourceConstraintComposition_eq_width21Batch,
    eval_monomialPolynomial_width21]

/-- A nonzero twenty-one-lane discrepancy gives a nonzero polynomial. -/
theorem width21Polynomial_ne_zero
    (values : ConstraintLane → K) (hvalues : values ≠ 0) :
    monomialPolynomial values ≠ 0 := by
  intro hzero
  apply hvalues
  apply monomialPolynomial_injective
  simpa [monomialPolynomial] using hzero

/-- The constraint-lane batching polynomial has degree at most twenty. -/
theorem width21Polynomial_natDegree_le (values : ConstraintLane → K) :
    (monomialPolynomial values).natDegree ≤ 20 := by
  simpa using
    (monomialPolynomial_natDegree_le (K := K) (n := 21) (by decide) values)

/-- If the batching polynomial is identically zero, every source lane is
zero.  This is the deterministic implication used outside the collision
event. -/
theorem all_source_lanes_zero_of_polynomial_eq_zero
    (poseidon : Fin 4 → K) (semantic : Fin 16 → K) (copy : K)
    (hzero : monomialPolynomial
      (constraintLaneVector poseidon semantic copy) = 0) :
    (∀ lane, poseidon lane = 0) ∧
      (∀ lane, semantic lane = 0) ∧ copy = 0 := by
  have hvector : constraintLaneVector poseidon semantic copy = 0 := by
    apply monomialPolynomial_injective
    simpa [monomialPolynomial] using hzero
  constructor
  · intro lane
    have := congrFun hvector
      ⟨lane.val, lane.isLt.trans (by decide : 4 < 21)⟩
    simpa using this
  constructor
  · intro lane
    have := congrFun hvector ⟨lane.val + 4, by omega⟩
    simpa using this
  · have := congrFun hvector (20 : ConstraintLane)
    simpa using this

section FiniteField

variable [Fintype K] [DecidableEq K]

/-- All field challenges that hide a fixed nonzero lane discrepancy. -/
def width21CollisionSet (values : ConstraintLane → K) : Finset K :=
  Finset.univ.filter fun theta => width21Batch values theta = 0

/-- At most twenty field challenges hide a fixed nonzero constraint-lane
vector. -/
theorem width21_collision_card_le_twenty
    (values : ConstraintLane → K) (hvalues : values ≠ 0) :
    (width21CollisionSet values).card ≤ 20 := by
  let polynomial := monomialPolynomial values
  have hpolynomial : polynomial ≠ 0 := width21Polynomial_ne_zero values hvalues
  have hsubset : (width21CollisionSet values).val ⊆ polynomial.roots := by
    intro theta htheta
    have hbatch : width21Batch values theta = 0 := by
      exact (Finset.mem_filter.mp htheta).2
    rw [Polynomial.mem_roots hpolynomial]
    simpa [Polynomial.IsRoot, polynomial] using hbatch
  exact (Polynomial.card_le_degree_of_subset_roots hsubset).trans
    (width21Polynomial_natDegree_le values)

def uniformWidth21CollisionProbability (values : ConstraintLane → K) : Rat :=
  (width21CollisionSet values).card / Fintype.card K

/-- Under a uniform full-field challenge, the fixed-vector collision
probability is at most `20 / |K|`. -/
theorem uniform_width21_collision_probability_le
    (values : ConstraintLane → K) (hvalues : values ≠ 0) :
    uniformWidth21CollisionProbability values ≤
      (20 : Rat) / Fintype.card K := by
  have hcardNat : 0 < Fintype.card K := Fintype.card_pos_iff.mpr ⟨0⟩
  have hcard : (0 : Rat) < Fintype.card K := by exact_mod_cast hcardNat
  rw [uniformWidth21CollisionProbability,
    div_le_div_iff_of_pos_right hcard]
  exact_mod_cast width21_collision_card_le_twenty values hvalues

/-! ## Transcript-ordering condition -/

def FixedBeforeTheta {Prefix : Type*}
    (values : Prefix → K → ConstraintLane → K) : Prop :=
  ∀ transcriptPrefix thetaOne thetaTwo,
    values transcriptPrefix thetaOne = values transcriptPrefix thetaTwo

def adaptiveWidth21CollisionSet {Prefix : Type*}
    (values : Prefix → K → ConstraintLane → K)
    (transcriptPrefix : Prefix) : Finset K :=
  Finset.univ.filter fun theta =>
    width21Batch (values transcriptPrefix theta) theta = 0

theorem adaptiveWidth21CollisionSet_eq
    {Prefix : Type*}
    (values : Prefix → K → ConstraintLane → K)
    (fixed : FixedBeforeTheta values)
    (transcriptPrefix : Prefix) (thetaZero : K) :
    adaptiveWidth21CollisionSet values transcriptPrefix =
      width21CollisionSet (values transcriptPrefix thetaZero) := by
  ext theta
  simp only [adaptiveWidth21CollisionSet, width21CollisionSet,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [fixed transcriptPrefix theta thetaZero]

theorem adaptive_width21_collision_card_le_twenty
    {Prefix : Type*}
    (values : Prefix → K → ConstraintLane → K)
    (fixed : FixedBeforeTheta values)
    (transcriptPrefix : Prefix) (thetaZero : K)
    (nonzero : values transcriptPrefix thetaZero ≠ 0) :
    (adaptiveWidth21CollisionSet values transcriptPrefix).card ≤ 20 := by
  rw [adaptiveWidth21CollisionSet_eq values fixed transcriptPrefix thetaZero]
  exact width21_collision_card_le_twenty _ nonzero

end FiniteField

/-- For deployed QM31 cardinality, the exact 21-lane term is within the
existing conservative `2^-119` ledger allocation. -/
theorem qm31_width21_collision_le_two_pow_neg_119 :
    (20 : Real) / AspisSoundnessLedger.FIELD ≤ 1 / 2 ^ 119 := by
  unfold AspisSoundnessLedger.FIELD
  norm_num

#print axioms sourceConstraintComposition_eq_width21Batch
#print axioms all_source_lanes_zero_of_polynomial_eq_zero
#print axioms width21_collision_card_le_twenty
#print axioms uniform_width21_collision_probability_le
#print axioms adaptive_width21_collision_card_le_twenty
#print axioms qm31_width21_collision_le_two_pow_neg_119

end AspisV5ConstraintLaneBatching
