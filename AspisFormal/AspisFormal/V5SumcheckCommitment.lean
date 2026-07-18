import Mathlib
import AspisFormal.SumcheckMasking

/-!
# The v5 sumcheck-mask terminal commitment

This file isolates the algebra needed to authenticate component B without
confusing a degree-27 round polynomial with the multilinear extension of its
Boolean endpoint table.

There are ten rounds.  Round `i` has 27 freely sampled tail coefficients.
The omitted constant coefficient is minus one half of their sum, so the
resulting degree-27 polynomial has zero endpoint sum.  If `s_i` is the
incoming mask claim, the next claim is

```
  s_(i+1) = s_i / 2 + sum_k c_(i,k) * (z_i^(k+1) - 1/2).
```

The main theorem proves that the terminal is the advertised public linear
functional of the initial claim and all 270 tail coefficients.  This is the
functional which a future v5 PCS relation must authenticate.  No commitment,
Fiat--Shamir, Rust serialisation, or hiding conclusion is inferred here.

The final section records only the elementary dimension fact behind a padded
coefficient commitment.  A nonzero functional on 1,024 field coordinates has
a 1,023-dimensional kernel, abstractly equivalent to 271 state coordinates
and 752 pad coordinates.  This does not prove that the pad coordinates hide
the deployed query, OOD, fold, or terminal schedule.  That schedule-dependent
surjectivity statement remains an explicit open obligation.  An explicit Rust
encoding into this kernel, a PCS/verifier relation binding that encoding, the
rank of the resulting released-view map, and its compute-unit cost are also
outside this module and must be established separately.
-/

open scoped BigOperators

namespace AspisV5SumcheckCommitment

def roundCount : ℕ := 10
def tailCount : ℕ := 27
def stateCoordinateCount : ℕ := 1 + roundCount * tailCount
def ambientCoordinateCount : ℕ := 1024
def kernelCoordinateCount : ℕ := ambientCoordinateCount - 1
def padCoordinateCount : ℕ := kernelCoordinateCount - stateCoordinateCount

theorem concrete_coordinate_counts :
    stateCoordinateCount = 271 ∧ kernelCoordinateCount = 1023 ∧
      padCoordinateCount = 752 ∧
      stateCoordinateCount + padCoordinateCount = kernelCoordinateCount := by
  norm_num [stateCoordinateCount, kernelCoordinateCount, padCoordinateCount,
    roundCount, tailCount, ambientCoordinateCount]

section Terminal

variable {K : Type*} [Field K]

/-- The field element used for division by two. -/
def half : K := (2 : K)⁻¹

/-- Evaluation of the zero-endpoint-sum polynomial represented by its 27
nonconstant coefficients.  Coefficient `k` multiplies `X^(k+1)`; its share of
the derived constant coefficient is `-c_k / 2`. -/
def tailEvaluation (tail : Fin tailCount → K) (x : K) : K :=
  ∑ k, tail k * (x ^ ((k : ℕ) + 1) - half)

/-- One chained mask round. -/
def maskStep (state : K) (tail : Fin tailCount → K) (x : K) : K :=
  half * state + tailEvaluation tail x

/-- The recurrence is exactly evaluation of the round carrier plus the
zero-boundary polynomial from `SumcheckMasking`; this is the algebraic seam to
the existing component-B primitive. -/
theorem maskStep_eq_maskRoundCoeff_eval (h2 : (2 : K) ≠ 0)
    (state : K) (tail : Fin tailCount → K) (x : K) :
    maskStep state tail x =
      AspisSumcheckMasking.coeffEval
        (AspisSumcheckMasking.maskRoundCoeff state
          (AspisSumcheckMasking.zeroBoundaryFromTail h2 tail)) x := by
  simp only [maskStep, tailEvaluation, half,
    AspisSumcheckMasking.coeffEval, AspisSumcheckMasking.maskRoundCoeff,
    AspisSumcheckMasking.roundCarrier,
    AspisSumcheckMasking.zeroBoundaryFromTail, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ, Fin.val_succ]
  simp only [if_true, Fin.succ_ne_zero, if_false, Fin.val_zero, pow_zero,
    mul_one]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  simp only [div_eq_mul_inv]
  ring_nf
  congr 1
  apply Finset.sum_congr rfl
  intro coefficient _
  ring

/-- Iteration of the affine recurrence over an already evaluated list of
round contributions. -/
def chainContributions (initial : K) (contributions : List K) : K :=
  contributions.foldl (fun state contribution ↦ half * state + contribution) initial

/-- Closed weighted sum of a list of round contributions.  The head is
multiplied by one half once for every later round. -/
def weightedContributions : List K → K
  | [] => 0
  | contribution :: remaining =>
      half ^ remaining.length * contribution + weightedContributions remaining

/-- Coordinate form of `weightedContributions` for a list of arbitrary
length. -/
theorem weightedContributions_eq_sum_get (contributions : List K) :
    weightedContributions contributions =
      ∑ index : Fin contributions.length,
        half ^ (contributions.length - 1 - (index : ℕ)) * contributions.get index := by
  induction contributions with
  | nil => simp [weightedContributions]
  | cons contribution remaining ih =>
      rw [weightedContributions]
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Nat.add_sub_cancel, List.get_cons_zero,
        Fin.val_succ]
      rw [ih]
      congr 1
      apply Finset.sum_congr rfl
      intro index _
      congr 2
      omega

/-- `weightedContributions` applied to a fixed-size coordinate vector. -/
theorem weightedContributions_ofFn_eq_sum :
    ∀ {n : ℕ} (coordinates : Fin n → K),
      weightedContributions (List.ofFn coordinates) =
        ∑ index : Fin n,
          half ^ (n - 1 - (index : ℕ)) * coordinates index
  | 0, coordinates => by
      simp [weightedContributions]
  | n + 1, coordinates => by
      rw [List.ofFn_succ, weightedContributions, Fin.sum_univ_succ]
      simp only [List.length_ofFn, weightedContributions_ofFn_eq_sum,
        Fin.val_zero, Fin.val_succ, Nat.add_sub_cancel]
      congr 1
      apply Finset.sum_congr rfl
      intro index _
      congr 2
      omega

theorem chainContributions_eq_closed (initial : K) (contributions : List K) :
    chainContributions initial contributions =
      half ^ contributions.length * initial + weightedContributions contributions := by
  induction contributions generalizing initial with
  | nil => simp [chainContributions, weightedContributions]
  | cons contribution remaining ih =>
      rw [chainContributions, List.foldl_cons]
      change chainContributions (half * initial + contribution) remaining = _
      rw [ih]
      simp only [List.length_cons, weightedContributions]
      rw [pow_succ]
      ring

/-- The ten evaluated zero-boundary round contributions in transcript order. -/
def tenContributions
    (tails : Fin roundCount → Fin tailCount → K)
    (point : Fin roundCount → K) : List K :=
  List.ofFn (fun round ↦ tailEvaluation (tails round) (point round))

/-- Literal algebraic ten-round component-B recurrence. -/
def tenRoundTerminal (initial : K)
    (tails : Fin roundCount → Fin tailCount → K)
    (point : Fin roundCount → K) : K :=
  chainContributions initial (tenContributions tails point)

/-- Closed terminal functional.  Round `i` is halved once for each of the
`9-i` later rounds.  This definition is deliberately written as a coordinate
sum: it is the candidate dense covector that a future PCS relation would have
to bind. -/
def terminalCovector (point : Fin roundCount → K) (initial : K)
    (tails : Fin roundCount → Fin tailCount → K) : K :=
  half ^ roundCount * initial +
    ∑ round : Fin roundCount,
      half ^ (roundCount - 1 - (round : ℕ)) *
        ∑ coefficient : Fin tailCount,
          tails round coefficient *
            (point round ^ ((coefficient : ℕ) + 1) - half)

private theorem weightedContributions_tenContributions
    (tails : Fin roundCount → Fin tailCount → K)
    (point : Fin roundCount → K) :
    weightedContributions (tenContributions tails point) =
      ∑ round : Fin roundCount,
        half ^ (roundCount - 1 - (round : ℕ)) *
          tailEvaluation (tails round) (point round) := by
  exact weightedContributions_ofFn_eq_sum
    (fun round ↦ tailEvaluation (tails round) (point round))

/-- The exact terminal-covector identity for ten degree-27 chained masks. -/
theorem tenRoundTerminal_eq_terminalCovector (initial : K)
    (tails : Fin roundCount → Fin tailCount → K)
    (point : Fin roundCount → K) :
    tenRoundTerminal initial tails point = terminalCovector point initial tails := by
  rw [tenRoundTerminal, chainContributions_eq_closed]
  rw [weightedContributions_tenContributions]
  simp only [tenContributions, List.length_ofFn]
  rfl

/-- Expanded application form: the terminal is linear in the initial state
and all 270 stored tail coefficients, with no Boolean-table premise. -/
theorem tenRoundTerminal_eq_coordinate_sum (initial : K)
    (tails : Fin roundCount → Fin tailCount → K)
    (point : Fin roundCount → K) :
    tenRoundTerminal initial tails point =
      half ^ 10 * initial +
        ∑ round : Fin 10,
          half ^ (9 - (round : ℕ)) *
            ∑ coefficient : Fin 27,
              tails round coefficient *
                (point round ^ ((coefficient : ℕ) + 1) - half) := by
  change tenRoundTerminal initial tails point = terminalCovector point initial tails
  exact tenRoundTerminal_eq_terminalCovector initial tails point

/-- The polynomial represented by one tail really has zero endpoint sum when
two is nonzero. -/
theorem tailEvaluation_zero_add_one (h2 : (2 : K) ≠ 0)
    (tail : Fin tailCount → K) :
    tailEvaluation tail 0 + tailEvaluation tail 1 = 0 := by
  simp only [tailEvaluation]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro coefficient _
  have hhalf : (2 : K) * half = 1 := by
    simp [half, h2]
  simp only [zero_pow (Nat.succ_ne_zero _), one_pow]
  calc
    tail coefficient * (0 - half) + tail coefficient * (1 - half) =
        tail coefficient * (1 - (2 : K) * half) := by ring
    _ = 0 := by rw [hhalf]; simp

end Terminal

section KernelCoordinates

variable (K : Type*) [Field K]

/-- A nonzero public linear functional leaves exactly 1,023 degrees of freedom
inside a 1,024-coordinate message. -/
theorem nonzeroFunctional_kernel_finrank
    (inactive : (Fin ambientCoordinateCount → K) →ₗ[K] K)
    (hinactive : inactive ≠ 0) :
    Module.finrank K (LinearMap.ker inactive) = kernelCoordinateCount := by
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero hinactive
  norm_num [ambientCoordinateCount, kernelCoordinateCount] at h ⊢
  omega

/-- Abstract state-plus-pad coordinates for the kernel of a nonzero inactive
functional.  This is a dimension statement, not a deployed encoding table. -/
noncomputable def statePadEquiv
    (inactive : (Fin ambientCoordinateCount → K) →ₗ[K] K)
    (hinactive : inactive ≠ 0) :
    ((Fin stateCoordinateCount → K) × (Fin padCoordinateCount → K)) ≃ₗ[K]
      LinearMap.ker inactive :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [nonzeroFunctional_kernel_finrank K inactive hinactive]
    norm_num [stateCoordinateCount, padCoordinateCount, roundCount, tailCount,
      kernelCoordinateCount, ambientCoordinateCount])

/-- Every vector satisfying the inactive relation has unique 271-coordinate
state and 752-coordinate pad coordinates. -/
theorem existsUnique_state_pad_coordinates
    (inactive : (Fin ambientCoordinateCount → K) →ₗ[K] K)
    (hinactive : inactive ≠ 0) (message : LinearMap.ker inactive) :
    ∃! coordinates :
        (Fin stateCoordinateCount → K) × (Fin padCoordinateCount → K),
      statePadEquiv K inactive hinactive coordinates = message := by
  exact (statePadEquiv K inactive hinactive).bijective.existsUnique message

/-- State and pad coordinates are independent under the abstract kernel
equivalence: equality of a pure-state and pure-pad vector forces both to be
zero. -/
theorem state_pad_intersection_trivial
    (inactive : (Fin ambientCoordinateCount → K) →ₗ[K] K)
    (hinactive : inactive ≠ 0)
    (state : Fin stateCoordinateCount → K)
    (pad : Fin padCoordinateCount → K)
    (h : statePadEquiv K inactive hinactive (state, 0) =
      statePadEquiv K inactive hinactive (0, pad)) :
    state = 0 ∧ pad = 0 := by
  have hp : (state, 0) = (0, pad) :=
    (statePadEquiv K inactive hinactive).injective h
  exact ⟨congrArg Prod.fst hp, (congrArg Prod.snd hp).symm⟩

end KernelCoordinates

end AspisV5SumcheckCommitment

#print axioms AspisV5SumcheckCommitment.tenRoundTerminal_eq_terminalCovector
#print axioms AspisV5SumcheckCommitment.tenRoundTerminal_eq_coordinate_sum
#print axioms AspisV5SumcheckCommitment.maskStep_eq_maskRoundCoeff_eval
#print axioms AspisV5SumcheckCommitment.tailEvaluation_zero_add_one
#print axioms AspisV5SumcheckCommitment.concrete_coordinate_counts
#print axioms AspisV5SumcheckCommitment.nonzeroFunctional_kernel_finrank
#print axioms AspisV5SumcheckCommitment.existsUnique_state_pad_coordinates
#print axioms AspisV5SumcheckCommitment.state_pad_intersection_trivial
