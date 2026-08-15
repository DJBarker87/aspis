import AspisFormal.V5FunctionalBatching
import AspisFormal.V5RelationStressSourceBridge

/-!
# Nonzero batching-challenge control and probability

The production verifier draws the scalar used to combine four claims with
`challenge_nonzero_qm31`. This file separates three facts:

1. the bounded wrapper rejects zero and can only succeed with a nonzero value;
2. a uniform successful value is uniform over the nonzero field elements, so
   the cubic collision denominator is `|K| - 1`;
3. the maintained relation formula uses that value as
   `1, kappa, kappa^2, kappa^3`.

The first and third facts are deterministic. The second still requires the
cryptographic statement that the deployed hash transcript supplies uniform,
unpredictable field samples. No theorem below derives that statement from
SHA-256.
-/

namespace AspisV5NonzeroKappaSourceBridge

open AspisV5FunctionalBatching
open AspisV5RelationStressSourceBridge

variable {K S E : Type*}

/-- Result plus the transcript state left by a lower-level field draw. -/
abbrev StatefulDraw (K S E : Type*) := Except E K × S

/-- Source-shaped bounded rejection of zero. A lower-level error is returned
immediately; three zero values return `retryExhausted` after the third state
transition. -/
def boundedNonzero [Zero K] [DecidableEq K]
    (draw : S → StatefulDraw K S E) (retryExhausted : E) :
    Nat → S → StatefulDraw K S E
  | 0, state => (.error retryExhausted, state)
  | attempts + 1, state =>
      match draw state with
      | (.error error, nextState) => (.error error, nextState)
      | (.ok value, nextState) =>
          if value = 0 then
            boundedNonzero draw retryExhausted attempts nextState
          else
            (.ok value, nextState)

@[simp]
theorem boundedNonzero_zero [Zero K] [DecidableEq K]
    (draw : S → StatefulDraw K S E) (retryExhausted : E) (state : S) :
    boundedNonzero draw retryExhausted 0 state =
      (.error retryExhausted, state) := by
  rfl

theorem boundedNonzero_inner_error [Zero K] [DecidableEq K]
    (draw : S → StatefulDraw K S E) (retryExhausted error : E)
    (attempts : Nat) (state nextState : S)
    (hdraw : draw state = (.error error, nextState)) :
    boundedNonzero draw retryExhausted (attempts + 1) state =
      (.error error, nextState) := by
  simp [boundedNonzero, hdraw]

theorem boundedNonzero_rejects_zero [Zero K] [DecidableEq K]
    (draw : S → StatefulDraw K S E) (retryExhausted : E)
    (attempts : Nat) (state nextState : S)
    (hdraw : draw state = (.ok 0, nextState)) :
    boundedNonzero draw retryExhausted (attempts + 1) state =
      boundedNonzero draw retryExhausted attempts nextState := by
  simp [boundedNonzero, hdraw]

theorem boundedNonzero_returns_nonzero [Zero K] [DecidableEq K]
    (draw : S → StatefulDraw K S E) (retryExhausted : E)
    (attempts : Nat) (state finalState : S) (value : K)
    (hrun : boundedNonzero draw retryExhausted attempts state =
      (.ok value, finalState)) :
    value ≠ 0 := by
  induction attempts generalizing state with
  | zero => simp [boundedNonzero] at hrun
  | succ attempts ih =>
      cases hdraw : draw state with
      | mk result nextState =>
          cases result with
          | error error => simp [boundedNonzero, hdraw] at hrun
          | ok sampled =>
              by_cases hzero : sampled = 0
              · exact ih nextState (by simpa [boundedNonzero, hdraw, hzero] using hrun)
              · have hpair : sampled = value ∧ nextState = finalState := by
                  simpa [boundedNonzero, hdraw, hzero] using hrun
                simpa [← hpair.1] using hzero

/-- The production retry count is three: three zero values consume exactly
three lower-level states and then return the wrapper's exhaustion error. -/
theorem boundedNonzero_three_zeros
    [Zero K] [DecidableEq K]
    (draw : S → StatefulDraw K S E) (retryExhausted : E)
    (state0 state1 state2 state3 : S)
    (h0 : draw state0 = (.ok 0, state1))
    (h1 : draw state1 = (.ok 0, state2))
    (h2 : draw state2 = (.ok 0, state3)) :
    boundedNonzero draw retryExhausted 3 state0 =
      (.error retryExhausted, state3) := by
  simp [boundedNonzero, h0, h1, h2]

/-! ## The correct collision denominator -/

section FiniteField

variable [Field K] [Fintype K] [DecidableEq K]

/-- Roots of the four-claim batching polynomial among nonzero challenges. -/
def nonzeroCollisionSet (delta : Fin 4 → K) : Finset K :=
  (Finset.univ.erase 0).filter fun kappa =>
    batchedDiscrepancy delta kappa = 0

theorem nonzeroCollisionSet_subset_collisionSet (delta : Fin 4 → K) :
    nonzeroCollisionSet delta ⊆ collisionSet delta := by
  intro kappa hkappa
  simp only [nonzeroCollisionSet, Finset.mem_filter,
    Finset.mem_erase] at hkappa
  simp [collisionSet, hkappa.2]

/-- Removing zero cannot increase the cubic root count. -/
theorem nonzero_collision_card_le_three
    (delta : Fin 4 → K) (hdelta : delta ≠ 0) :
    (nonzeroCollisionSet delta).card ≤ 3 := by
  exact (Finset.card_le_card (nonzeroCollisionSet_subset_collisionSet delta)).trans
    (collision_card_le_three delta hdelta)

/-- Collision probability when the successful challenge is uniform over
`K` without zero. -/
def uniformNonzeroCollisionProbability (delta : Fin 4 → K) : ℚ :=
  (nonzeroCollisionSet delta).card /
    ((Fintype.card K - 1 : ℕ) : ℚ)

/-- A fixed nonzero four-claim discrepancy collides with probability at most
`3 / (|K| - 1)` under a uniform nonzero challenge. -/
theorem uniformNonzeroCollisionProbability_le
    (delta : Fin 4 → K) (hdelta : delta ≠ 0)
    (hcard : 1 < Fintype.card K) :
    uniformNonzeroCollisionProbability delta ≤
      (3 : ℚ) / ((Fintype.card K - 1 : ℕ) : ℚ) := by
  have hdenNat : 0 < Fintype.card K - 1 := Nat.sub_pos_iff_lt.mpr hcard
  have hden : (0 : ℚ) < ((Fintype.card K - 1 : ℕ) : ℚ) := by
    exact_mod_cast hdenNat
  rw [uniformNonzeroCollisionProbability, div_le_div_iff_of_pos_right hden]
  exact_mod_cast nonzero_collision_card_le_three delta hdelta

/-- Explicit assumption needed to turn the counting theorem into a deployed
probability statement. It is not proved by known-answer vectors or by the
deterministic rejection-loop theorem. -/
def SuccessfulKappaIsUniform (mass : K → ℚ) : Prop :=
  ∀ kappa, kappa ≠ 0 →
    mass kappa = 1 / ((Fintype.card K - 1 : ℕ) : ℚ)

def nonzeroCollisionMass (mass : K → ℚ) (delta : Fin 4 → K) : ℚ :=
  ∑ kappa ∈ nonzeroCollisionSet delta, mass kappa

theorem nonzeroCollisionMass_eq_uniformProbability
    (mass : K → ℚ) (delta : Fin 4 → K)
    (huniform : SuccessfulKappaIsUniform mass) :
    nonzeroCollisionMass mass delta =
      uniformNonzeroCollisionProbability delta := by
  classical
  unfold nonzeroCollisionMass uniformNonzeroCollisionProbability
  calc
    (∑ kappa ∈ nonzeroCollisionSet delta, mass kappa) =
        ∑ kappa ∈ nonzeroCollisionSet delta,
          1 / ((Fintype.card K - 1 : ℕ) : ℚ) := by
      apply Finset.sum_congr rfl
      intro kappa hkappa
      apply huniform
      have hkappa' : kappa ≠ 0 ∧ batchedDiscrepancy delta kappa = 0 := by
        simpa [nonzeroCollisionSet] using hkappa
      exact hkappa'.1
    _ = (nonzeroCollisionSet delta).card /
        ((Fintype.card K - 1 : ℕ) : ℚ) := by
      simp [div_eq_mul_inv]

theorem nonzeroCollisionMass_le
    (mass : K → ℚ) (delta : Fin 4 → K)
    (huniform : SuccessfulKappaIsUniform mass)
    (hdelta : delta ≠ 0) (hcard : 1 < Fintype.card K) :
    nonzeroCollisionMass mass delta ≤
      (3 : ℚ) / ((Fintype.card K - 1 : ℕ) : ℚ) := by
  rw [nonzeroCollisionMass_eq_uniformProbability mass delta huniform]
  exact uniformNonzeroCollisionProbability_le delta hdelta hcard

end FiniteField

/-- The corrected concrete term for QM31 remains below `2^-122`. -/
theorem qm31_four_functional_nonzero_collision :
    (3 : ℝ) / (AspisSoundnessLedger.FIELD - 1) ≤ 1 / 2 ^ 122 := by
  unfold AspisSoundnessLedger.FIELD
  norm_num

/-! ## The sampled value used by relation batching -/

/-- The maintained relation formula consumes the successful nonzero value as
the four claim multipliers `1, kappa, kappa^2, kappa^3`. -/
theorem successful_value_is_relation_batching_scalar
    [Field K] [DecidableEq K]
    (draw : S → StatefulDraw K S E) (retryExhausted : E)
    (state finalState : S) (kappa inactive gamma : K)
    (claims : Fin 76 → K)
    (hrun : boundedNonzero draw retryExhausted 3 state =
      (.ok kappa, finalState)) :
    kappa ≠ 0 ∧
      sourceCallerInitialClaim inactive kappa gamma claims =
        inactive + sourcePreparedPointClaim gamma claims sourcePoint0 +
          kappa * sourcePreparedPointClaim gamma claims sourcePoint1 +
          kappa ^ 2 * sourcePreparedPointClaim gamma claims sourcePoint2 +
          kappa ^ 3 * sourcePreparedPointClaim gamma claims sourcePoint3 := by
  exact ⟨boundedNonzero_returns_nonzero draw retryExhausted 3 state
      finalState kappa hrun,
    sourceCallerInitialClaim_explicit inactive kappa gamma claims⟩

/-- Remaining source-level call-path statement. The source audit shows this
equality at the assignments and calls; a universal extraction proof for the
large verifier caller must still supply it. -/
def ExactProductionKappaCallPath (sampledKappa relationKappa : K) : Prop :=
  relationKappa = sampledKappa

theorem relation_formula_uses_sampled_kappa
    [Field K]
    (sampledKappa relationKappa inactive gamma : K)
    (claims : Fin 76 → K)
    (hpath : ExactProductionKappaCallPath sampledKappa relationKappa) :
    sourceCallerInitialClaim inactive relationKappa gamma claims =
      inactive + sourcePreparedPointClaim gamma claims sourcePoint0 +
        sampledKappa * sourcePreparedPointClaim gamma claims sourcePoint1 +
        sampledKappa ^ 2 * sourcePreparedPointClaim gamma claims sourcePoint2 +
        sampledKappa ^ 3 * sourcePreparedPointClaim gamma claims sourcePoint3 := by
  rw [hpath]
  exact sourceCallerInitialClaim_explicit inactive sampledKappa gamma claims

#print axioms boundedNonzero_returns_nonzero
#print axioms boundedNonzero_three_zeros
#print axioms nonzero_collision_card_le_three
#print axioms uniformNonzeroCollisionProbability_le
#print axioms nonzeroCollisionMass_le
#print axioms qm31_four_functional_nonzero_collision
#print axioms successful_value_is_relation_batching_scalar
#print axioms relation_formula_uses_sampled_kappa

end AspisV5NonzeroKappaSourceBridge
