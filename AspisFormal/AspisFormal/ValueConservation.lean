import Mathlib
/-
  Value conservation over M31 (no field wraparound), kernel-checked.

  M31 prime p = 2^31 - 1 = 2147483647.
  The spend circuit range-checks v (input value), v' (output value), and f (fee)
  to be < 2^30 = 1073741824.  Because 2*(2^30 - 1) = 2^31 - 2 = p - 1 < p, an
  input+output balance that holds MODULO p is forced to hold over the INTEGERS:
  no wraparound can manufacture value.

  This is a security-relevant claim of the construction.  Nothing below is
  trusted because "an AI said so": the Lean kernel checks the proof term.
-/

theorem value_conservation_no_wraparound
    (v v' f : Nat)
    (hv  : v  < 1073741824)   -- v  < 2^30
    (hv' : v' < 1073741824)   -- v' < 2^30
    (hf  : f  < 1073741824)   -- f  < 2^30
    (hcong : (v' + f) % 2147483647 = v % 2147483647)  -- balance holds mod p
    : v' + f = v := by
  omega

-- A second form: the balance equation as the circuit states it, v = v' + f mod p,
-- likewise forces the integer identity, so total committed value cannot increase.
theorem no_inflation
    (v v' f : Nat)
    (hv  : v  < 1073741824)
    (hv' : v' < 1073741824)
    (hf  : f  < 1073741824)
    (hcong : v % 2147483647 = (v' + f) % 2147483647)
    : v = v' + f := by
  omega

#print axioms value_conservation_no_wraparound
