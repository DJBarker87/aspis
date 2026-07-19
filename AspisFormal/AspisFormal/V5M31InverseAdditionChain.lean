import AspisFormal.V5CuArithmeticEquivalences
import AspisFormal.V5ComponentCQM31RustFormulaSeam

/-!
# v5 Component C: value-level M31 inverse addition chain

`V5CuArithmeticEquivalences` proves the *exponent* schedule of the retained
`M31::inv` addition chain: each temporary carries the intended `2^k - 1`
exponent and the final one is `P - 2`.  That file works with natural-number
exponents only; it does not evaluate the chain in the field.

This leaf closes the remaining gap by transcribing the same chain at the
**value** level over `M31Exact = ZMod (2^31-1)` and proving that the actual
repeated-squaring / multiplication graph computes the field inverse.

The transcription mirrors `aspis-core/src/field.rs::M31::inv` line for line:

```
assert!(self.0 != 0, "inverse of zero");   -- production PANIC at zero
let t2  = self.mul(self).mul(self);         -- x*x*x
let t4  = square_n(t2, 2).mul(t2);
let t8  = square_n(t4, 4).mul(t4);
let t16 = square_n(t8, 8).mul(t8);
let t24 = square_n(t16, 8).mul(t8);
let t28 = square_n(t24, 4).mul(t4);
let t29 = t28.mul(t28).mul(self);
let t30 = t29.mul(t29);
t30.mul(t30).mul(self)
```

with `square_n(value, count)` the `count`-fold repeated squaring.

The exponent bookkeeping is *reused* from `m31InverseAdditionChain`; it is not
re-derived here.  What is new is the field-level content: repeated squaring is
`x ↦ x^(2^count)`, the multiplication graph realizes exponent addition, the
result is `x^(P-2)`, and, for every nonzero `x`, that equals a genuine
multiplicative inverse (Fermat, `P` prime).

The production Rust function is partial: it panics at zero.  The total adapter
`chainTryInv` records that domain exactly (`none` precisely at zero) and agrees,
after transport through `m31ResidueEquiv`, with the mathematical adapter
`exactM31SourceOps.tryInv` used by the deployment seam.  The residual code/model
obligation is unchanged in kind: an Aeneas extraction must show the generated
Rust `inv` value graph equals `additionChain` on the nonzero domain.
-/

namespace AspisV5M31InverseAdditionChain

open AspisV5CuArithmeticEquivalences
open AspisV5ComponentCQM31TowerExact
open AspisV5ComponentCQM31RustFormulaSeam
open AspisV5ComponentCRejectionSampler

/-! ## Repeated squaring -/

/-- Value-level `square_n`: square `x` exactly `count` times.  Mirrors the Rust
`for _ in 0..count { value = value.mul(value) }` loop. -/
def squareN (x : M31Exact) (count : ℕ) : M31Exact :=
  (fun v => v * v)^[count] x

/-- One more squaring squares the running value. -/
theorem squareN_succ (x : M31Exact) (count : ℕ) :
    squareN x (count + 1) = squareN x count * squareN x count := by
  simp only [squareN, Function.iterate_succ_apply']

/-- **Theorem 1.**  Repeated squaring `count` times sends `x` to `x^(2^count)`,
universally in `x` and `count`. -/
theorem squareN_eq_pow (x : M31Exact) (count : ℕ) :
    squareN x count = x ^ (2 ^ count) := by
  induction count with
  | zero => simp [squareN, Function.iterate_zero_apply]
  | succ n ih =>
      rw [squareN_succ, ih, ← pow_add, ← two_mul, pow_succ']

/-- Repeated squaring of a pure power collapses to a single power: this is the
form consumed by the temporary-exponent bookkeeping below. -/
theorem squareN_pow (x : M31Exact) (e count : ℕ) :
    squareN (x ^ e) count = x ^ (e * 2 ^ count) := by
  rw [squareN_eq_pow, ← pow_mul]

/-! ## The value-level addition chain

Each temporary is a named definition realizing exactly one line of the Rust
source, so `additionChain` is manifestly the composed chain. -/

def acT2 (x : M31Exact) : M31Exact := x * x * x
def acT4 (x : M31Exact) : M31Exact := squareN (acT2 x) 2 * acT2 x
def acT8 (x : M31Exact) : M31Exact := squareN (acT4 x) 4 * acT4 x
def acT16 (x : M31Exact) : M31Exact := squareN (acT8 x) 8 * acT8 x
def acT24 (x : M31Exact) : M31Exact := squareN (acT16 x) 8 * acT8 x
def acT28 (x : M31Exact) : M31Exact := squareN (acT24 x) 4 * acT4 x
def acT29 (x : M31Exact) : M31Exact := acT28 x * acT28 x * x
def acT30 (x : M31Exact) : M31Exact := acT29 x * acT29 x

/-- The value-level `M31::inv` addition chain over `M31Exact`. -/
def additionChain (x : M31Exact) : M31Exact := acT30 x * acT30 x * x

/-- Fidelity anchor: the named-temporary spelling is definitionally the literal
Rust `let` block. -/
theorem additionChain_matches_rust_schedule (x : M31Exact) :
    additionChain x =
      (let t2 := x * x * x
       let t4 := squareN t2 2 * t2
       let t8 := squareN t4 4 * t4
       let t16 := squareN t8 8 * t8
       let t24 := squareN t16 8 * t8
       let t28 := squareN t24 4 * t4
       let t29 := t28 * t28 * x
       let t30 := t29 * t29
       t30 * t30 * x) := by
  rfl

/-! ## Recorded-exponent recurrence

These project the *existing* `m31InverseAdditionChain` definition; the recorded
exponent of each temporary is its predecessor(s) combined by the same
square/multiply steps.  They hold definitionally — the schedule itself is not
re-derived. -/

theorem exp_t2 : m31InverseAdditionChain.t2 = 1 + 1 + 1 := rfl
theorem exp_t4 :
    m31InverseAdditionChain.t4 =
      squareNExponent m31InverseAdditionChain.t2 2 + m31InverseAdditionChain.t2 := rfl
theorem exp_t8 :
    m31InverseAdditionChain.t8 =
      squareNExponent m31InverseAdditionChain.t4 4 + m31InverseAdditionChain.t4 := rfl
theorem exp_t16 :
    m31InverseAdditionChain.t16 =
      squareNExponent m31InverseAdditionChain.t8 8 + m31InverseAdditionChain.t8 := rfl
theorem exp_t24 :
    m31InverseAdditionChain.t24 =
      squareNExponent m31InverseAdditionChain.t16 8 + m31InverseAdditionChain.t8 := rfl
theorem exp_t28 :
    m31InverseAdditionChain.t28 =
      squareNExponent m31InverseAdditionChain.t24 4 + m31InverseAdditionChain.t4 := rfl
theorem exp_t29 :
    m31InverseAdditionChain.t29 =
      m31InverseAdditionChain.t28 + m31InverseAdditionChain.t28 + 1 := rfl
theorem exp_t30 :
    m31InverseAdditionChain.t30 =
      m31InverseAdditionChain.t29 + m31InverseAdditionChain.t29 := rfl
theorem exp_result :
    m31InverseAdditionChain.result =
      m31InverseAdditionChain.t30 + m31InverseAdditionChain.t30 + 1 := rfl

/-! ## Theorem 2: every temporary carries its recorded exponent -/

theorem acT2_eq (x : M31Exact) : acT2 x = x ^ m31InverseAdditionChain.t2 := by
  rw [acT2, exp_t2]
  simp only [pow_add, pow_one]

theorem acT4_eq (x : M31Exact) : acT4 x = x ^ m31InverseAdditionChain.t4 := by
  rw [acT4, acT2_eq, squareN_pow, ← pow_add, exp_t4]
  simp only [squareNExponent]

theorem acT8_eq (x : M31Exact) : acT8 x = x ^ m31InverseAdditionChain.t8 := by
  rw [acT8, acT4_eq, squareN_pow, ← pow_add, exp_t8]
  simp only [squareNExponent]

theorem acT16_eq (x : M31Exact) : acT16 x = x ^ m31InverseAdditionChain.t16 := by
  rw [acT16, acT8_eq, squareN_pow, ← pow_add, exp_t16]
  simp only [squareNExponent]

theorem acT24_eq (x : M31Exact) : acT24 x = x ^ m31InverseAdditionChain.t24 := by
  rw [acT24, acT16_eq, acT8_eq, squareN_pow, ← pow_add, exp_t24]
  simp only [squareNExponent]

theorem acT28_eq (x : M31Exact) : acT28 x = x ^ m31InverseAdditionChain.t28 := by
  rw [acT28, acT24_eq, acT4_eq, squareN_pow, ← pow_add, exp_t28]
  simp only [squareNExponent]

theorem acT29_eq (x : M31Exact) : acT29 x = x ^ m31InverseAdditionChain.t29 := by
  rw [acT29, acT28_eq, ← pow_add, ← pow_succ, exp_t29]

theorem acT30_eq (x : M31Exact) : acT30 x = x ^ m31InverseAdditionChain.t30 := by
  rw [acT30, acT29_eq, ← pow_add, exp_t30]

/-- The final value carries the recorded result exponent. -/
theorem additionChain_eq_pow_result (x : M31Exact) :
    additionChain x = x ^ m31InverseAdditionChain.result := by
  rw [additionChain, acT30_eq, ← pow_add, ← pow_succ, exp_result]

/-! ## Theorem 3: the final value is `x^(P-2)` -/

theorem additionChain_eq_pow_P_sub_two (x : M31Exact) :
    additionChain x = x ^ (P - 2) := by
  rw [additionChain_eq_pow_result, m31_inverse_addition_chain_exponent_eq,
    show m31Prime - 2 = P - 2 from by norm_num [m31Prime, P]]

/-! ## Theorem 4: the nonzero inverse equation (Fermat) -/

/-- Fermat's inverse exponent in `ZMod P`, `P` prime.  Holds for every `x`
(including `0`, where both sides are `0`); the *genuine* two-sided inverse
below is what needs `x ≠ 0`. -/
theorem pow_P_sub_two_eq_inv (x : M31Exact) : x ^ (P - 2) = x⁻¹ := by
  by_cases hx : x = 0
  · subst hx
    rw [zero_pow (show P - 2 ≠ 0 by norm_num [P]), inv_zero]
  · rw [inv_eq_one_div, eq_div_iff hx, ← pow_succ,
      show (P - 2) + 1 = P - 1 by norm_num [P]]
    exact ZMod.pow_card_sub_one_eq_one hx

/-- The addition chain evaluates to the field inverse operation of `ZMod P`. -/
theorem additionChain_eq_field_inv (x : M31Exact) : additionChain x = x⁻¹ := by
  rw [additionChain_eq_pow_P_sub_two, pow_P_sub_two_eq_inv]

/-- For nonzero `x`, the chain is a genuine left multiplicative inverse.  The
hypothesis `x ≠ 0` is load-bearing: `mul_inv_cancel₀` requires it. -/
theorem additionChain_mul_self (x : M31Exact) (hx : x ≠ 0) :
    x * additionChain x = 1 := by
  rw [additionChain_eq_field_inv]
  exact mul_inv_cancel₀ hx

/-- **Strongest theorem (nonzero-`x` inverse equation).**  For every nonzero
`x : M31Exact`, the value-level addition chain equals `x⁻¹`, and that `x⁻¹` is a
genuine two-sided multiplicative inverse.  The equality to `x⁻¹` holds for all
`x`; the two cancellation conjuncts are exactly where `x ≠ 0` is required. -/
theorem additionChain_inv_of_ne_zero (x : M31Exact) (hx : x ≠ 0) :
    additionChain x = x⁻¹ ∧
      x * additionChain x = 1 ∧ additionChain x * x = 1 := by
  refine ⟨additionChain_eq_field_inv x, ?_, ?_⟩
  · rw [additionChain_eq_field_inv]; exact mul_inv_cancel₀ hx
  · rw [additionChain_eq_field_inv]; exact inv_mul_cancel₀ hx

/-! ## Teeth -/

/-- Tooth: the addition chain itself evaluates to `0` at `x = 0`.  So "the
arithmetic returned zero" CANNOT substitute for the Rust domain check —
`additionChain 0 = 0`, which is not an inverse of `0`. -/
theorem additionChain_zero : additionChain (0 : M31Exact) = 0 := by
  rw [additionChain_eq_pow_P_sub_two, zero_pow (show P - 2 ≠ 0 by norm_num [P])]

/-- Tooth: the nonzero hypothesis is load-bearing for the genuine inverse.
Without `x ≠ 0` the cancellation equation is false at `0`: `additionChain 0 = 0`
gives `0 * 0 = 0 ≠ 1`. -/
theorem additionChain_mul_self_fails_at_zero :
    ¬ ((0 : M31Exact) * additionChain 0 = 1) := by
  rw [additionChain_zero, mul_zero]
  exact zero_ne_one

/-! ## Totalized adapter and the code/model seam

The production Rust `M31::inv` is partial (it panics at zero).  The adapter
below is total and records that domain: `none` precisely at zero, `some` of the
addition chain elsewhere. -/

/-- Honest totalized adapter for the panicking Rust `M31::inv`. -/
def chainTryInv (x : M31Exact) : Option M31Exact :=
  if x = 0 then none else some (additionChain x)

/-- Tooth: the adapter returns `none` at zero. -/
theorem chainTryInv_zero : chainTryInv (0 : M31Exact) = none := by
  simp [chainTryInv]

/-- The adapter returns `none` at *exactly* the zero input — the total encoding
of the production `assert!(self.0 != 0)` panic domain. -/
theorem chainTryInv_none_iff (x : M31Exact) : chainTryInv x = none ↔ x = 0 := by
  unfold chainTryInv
  by_cases h : x = 0
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; simp [h]

/-- On the nonzero domain the adapter is `some` of the addition chain. -/
theorem chainTryInv_some_of_ne_zero (x : M31Exact) (hx : x ≠ 0) :
    chainTryInv x = some (additionChain x) := by
  rw [chainTryInv, if_neg hx]

/-- **Adapter correspondence.**  Transported through the canonical residue
equivalence, `chainTryInv` is exactly the mathematical adapter used by
`exactM31SourceOps.tryInv` (the totalization of Rust `M31::inv` already consumed
by the deployment seam). -/
theorem chainTryInv_eq_exact_tryInv (a : M31Value) :
    chainTryInv (m31ResidueEquiv a) =
      (exactM31SourceOps.tryInv a).map m31ResidueEquiv := by
  rw [exactM31_tryInv_map]
  unfold chainTryInv
  by_cases h : m31ResidueEquiv a = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, additionChain_eq_field_inv]

/-! ## Axiom audit -/

#print axioms squareN_eq_pow
#print axioms squareN_pow
#print axioms additionChain_matches_rust_schedule
#print axioms acT2_eq
#print axioms acT4_eq
#print axioms acT8_eq
#print axioms acT16_eq
#print axioms acT24_eq
#print axioms acT28_eq
#print axioms acT29_eq
#print axioms acT30_eq
#print axioms additionChain_eq_pow_result
#print axioms additionChain_eq_pow_P_sub_two
#print axioms pow_P_sub_two_eq_inv
#print axioms additionChain_eq_field_inv
#print axioms additionChain_mul_self
#print axioms additionChain_inv_of_ne_zero
#print axioms additionChain_zero
#print axioms additionChain_mul_self_fails_at_zero
#print axioms chainTryInv_zero
#print axioms chainTryInv_none_iff
#print axioms chainTryInv_some_of_ne_zero
#print axioms chainTryInv_eq_exact_tryInv

end AspisV5M31InverseAdditionChain
