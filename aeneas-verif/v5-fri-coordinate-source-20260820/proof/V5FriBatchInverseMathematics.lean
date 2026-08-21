import Mathlib

set_option autoImplicit false

/-!
# Montgomery batch-inverse error propagation

The production coordinate helper performs one inversion of the product of all
denominators and reconstructs every individual inverse with a prefix/suffix
pass.  It then checks one denominator/output product.  The theorem below
formalizes why that one check validates the complete batch: any error in the
single injected inversion is a common multiplicative factor on every output.

The generated-loop proof supplies `prefixTimesEntryTimesSuffix` and
`outputValue` from the actual translated Rust states.  They are algorithm
invariants, not assumptions about a desired FRI table.
-/

namespace AspisV5FriBatchInverseMathematics

variable {K : Type*} [Field K]

/-- Semantic trace of the two Montgomery passes.  `backend` is the one value
returned by the injected inversion backend for `total`; it is deliberately
not assumed correct. -/
structure MontgomeryBatchTrace (n : Nat) where
  denominator : Fin n → K
  prefixProduct : Fin n → K
  suffixProduct : Fin n → K
  outputValueAt : Fin n → K
  total : K
  backend : K
  prefixTimesEntryTimesSuffix : ∀ i,
    prefixProduct i * denominator i * suffixProduct i = total
  outputValue : ∀ i,
    outputValueAt i = prefixProduct i * backend * suffixProduct i

/-- Every denominator/output product carries exactly the same backend-error
factor, irrespective of its position in the batch. -/
theorem every_product_eq_common_factor {n : Nat}
    (trace : MontgomeryBatchTrace (K := K) n) (i : Fin n) :
    trace.denominator i * trace.outputValueAt i = trace.total * trace.backend := by
  rw [trace.outputValue]
  rw [← trace.prefixTimesEntryTimesSuffix i]
  ring

/-- The production check of the first nonempty entry therefore proves every
returned value is an inverse of its corresponding denominator. -/
theorem first_product_check_validates_complete_batch {n : Nat}
    (trace : MontgomeryBatchTrace (K := K) (n + 1))
    (hfirst : trace.denominator 0 * trace.outputValueAt 0 = 1) :
    ∀ i, trace.denominator i * trace.outputValueAt i = 1 := by
  intro i
  rw [every_product_eq_common_factor trace i]
  rw [← every_product_eq_common_factor trace 0]
  exact hfirst

/-- In a field, the same check gives the exact mathematical inverse for every
nonzero denominator. -/
theorem first_product_check_yields_exact_inverses {n : Nat}
    (trace : MontgomeryBatchTrace (K := K) (n + 1))
    (hfirst : trace.denominator 0 * trace.outputValueAt 0 = 1) :
    ∀ i, trace.outputValueAt i = (trace.denominator i)⁻¹ := by
  intro i
  have hproduct := first_product_check_validates_complete_batch trace hfirst i
  have hnonzero : trace.denominator i ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hproduct
    exact zero_ne_one hproduct
  apply mul_left_cancel₀ hnonzero
  rw [hproduct, mul_inv_cancel₀ hnonzero]

#print axioms first_product_check_validates_complete_batch
#print axioms first_product_check_yields_exact_inverses

end AspisV5FriBatchInverseMathematics
