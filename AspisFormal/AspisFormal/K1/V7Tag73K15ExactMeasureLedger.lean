import AspisFormal.K1.V7FiniteFieldCausalTargetProbability
import AspisFormal.V5ComponentCQM31TowerExact

/-!
# Exact measure ledger for the fixed-family Tag-73 K1.5 event

The algebraic K1.5 development classifies every non-K1.4 failure into eight
causal categories.  Earlier files prove their exact root caps, but express the
final `396430 / |QM31|` total as an ideal rational subtotal.  This module gives
the corresponding measure theorem needed by the exact compiler experiment.

Each category remains a separate event.  A production/source bridge must
prove the eight component inequalities below from the literal sampler regions
and transcript order.  Once it does, no further probability premise is needed:
the finite union is bounded by `396430 / (|QM31| - 1)`.  The common nonzero
denominator is conservative for ordinary samplers and exact for the final
nonzero kappa sampler.  No grinding/work normalization appears.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73K15ExactMeasureLedger

open scoped ENNReal BigOperators
open MeasureTheory
open AspisV5ComponentCQM31TowerExact

/-- The eight causal categories produced by `FixedFamilyK15Failure`. -/
inductive FixedK15Category where
  | semantic
  | copyLambda
  | copyChi
  | muZero
  | inactiveChi
  | oodMix
  | relationAlpha
  | kappaPointRow
  deriving DecidableEq, Fintype

/-- Exact root numerator charged to each causal category. -/
def fixedK15CategoryCap : FixedK15Category → Nat
  | .semantic => 30500
  | .copyLambda => 292800
  | .copyChi => 73100
  | .muZero => 1
  | .inactiveChi => 1
  | .oodMix => 2
  | .relationAlpha => 24
  | .kappaPointRow => 2

theorem fixedK15CategoryCap_sum_eq :
    ∑ category, fixedK15CategoryCap category = 396430 := by
  decide

/-- One exact compiler experiment's eight source-classified K1.5 events. -/
structure FixedK15Events (Coins : Type) where
  event : FixedK15Category → Set Coins

/-- The complete fixed-family K1.5 event is the finite union of all eight
source-classified events. -/
def FixedK15Events.failure {Coins : Type} (events : FixedK15Events Coins) :
    Set Coins :=
  ⋃ category, events.event category

/-- The precise component obligations left to the production sampler/source
bridge.  Every inequality uses the same conservative nonzero-field
denominator, so ordinary and nonzero challenges can be composed without an
independence assumption. -/
structure FixedK15EventBounds
    {Coins : Type} (law : PMF Coins) (events : FixedK15Events Coins) : Prop where
  category : ∀ kind,
    law.toOuterMeasure (events.event kind) ≤
      (fixedK15CategoryCap kind : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal)

/-- An ordinary uniform QM31 bound safely weakens to the common nonzero-field
denominator used by the composed ledger. -/
theorem ordinary_bound_le_common_nonzero_bound (cap : Nat) :
    (cap : ENNReal) / ((P ^ 4 : Nat) : ENNReal) ≤
      (cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) := by
  apply ENNReal.div_le_div_left
  exact_mod_cast Nat.sub_le (P ^ 4) 1

/-- Build the complete ledger from the seven ordinary-sampler component
bounds and the exact nonzero-kappa component bound. -/
theorem fixedK15EventBounds_of_ordinary_and_kappa
    {Coins : Type} (law : PMF Coins) (events : FixedK15Events Coins)
    (ordinary : ∀ kind, kind ≠ .kappaPointRow →
      law.toOuterMeasure (events.event kind) ≤
        (fixedK15CategoryCap kind : ENNReal) /
          ((P ^ 4 : Nat) : ENNReal))
    (kappa : law.toOuterMeasure (events.event .kappaPointRow) ≤
      (2 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal)) :
    FixedK15EventBounds law events := by
  refine ⟨fun kind => ?_⟩
  by_cases isKappa : kind = .kappaPointRow
  · subst kind
    exact kappa
  · exact (ordinary kind isKappa).trans
      (ordinary_bound_le_common_nonzero_bound
        (fixedK15CategoryCap kind))

/-- Exact finite-union measure theorem for the corrected K1.5 numerator. -/
theorem fixed_k15_failure_probability_le
    {Coins : Type} (law : PMF Coins) (events : FixedK15Events Coins)
    (bounds : FixedK15EventBounds law events) :
    law.toOuterMeasure events.failure ≤
      (396430 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) := by
  calc
    law.toOuterMeasure events.failure ≤
        ∑ category,
          law.toOuterMeasure (events.event category) := by
      exact measure_iUnion_fintype_le law.toOuterMeasure events.event
    _ ≤ ∑ category,
        (fixedK15CategoryCap category : ENNReal) /
          ((P ^ 4 - 1 : Nat) : ENNReal) := by
      exact Finset.sum_le_sum fun category _ => bounds.category category
    _ = (396430 : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal) := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Nat.cast_sum]
      rw [fixedK15CategoryCap_sum_eq]
      norm_num

/-- Any concrete false-extraction event covered by the eight classified
events inherits the same exact raw K1.5 bound. -/
theorem covered_fixed_k15_failure_probability_le
    {Coins : Type} (law : PMF Coins) (events : FixedK15Events Coins)
    (attack : Set Coins) (covered : attack ⊆ events.failure)
    (bounds : FixedK15EventBounds law events) :
    law.toOuterMeasure attack ≤
      (396430 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) := by
  exact (law.toOuterMeasure.mono covered).trans
    (fixed_k15_failure_probability_le law events bounds)

/-- The exact measure ledger agrees with the already audited arithmetic and
is below `2^-105` before any work normalization. -/
theorem fixed_k15_failure_probability_le_two_pow_neg_105 :
    (396430 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) ≤
      (1 : ENNReal) / 2 ^ 105 := by
  rw [ENNReal.div_le_iff (by norm_num [P]) (by norm_num)]
  rw [ENNReal.div_eq_inv_mul, mul_one]
  rw [← ENNReal.div_eq_inv_mul]
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num))
    (Or.inl (by norm_num))).2
  norm_num [P]

#print axioms fixedK15CategoryCap_sum_eq
#print axioms ordinary_bound_le_common_nonzero_bound
#print axioms fixedK15EventBounds_of_ordinary_and_kappa
#print axioms fixed_k15_failure_probability_le
#print axioms covered_fixed_k15_failure_probability_le
#print axioms fixed_k15_failure_probability_le_two_pow_neg_105

end AspisK1.V7Tag73K15ExactMeasureLedger
