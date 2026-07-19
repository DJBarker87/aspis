import AspisFormal.V5ComponentCQM31RustFormulaSeam

/-!
# v5 Component C: raw two-fold Mersenne reducer and the M31 multiplication seam

This leaf models the executable `reduce_u64` reducer used by `M31::mul` in
`aspis-core/src/field.rs` and proves, for arbitrary bounded inputs, that it
canonicalises correctly and that the packaged multiplication agrees with the
exact field operation `exactM31SourceOps.mul` already consumed by the CM31/QM31
formula proofs.

The reducer graph confirmed against the source is

```
fn reduce_u64(x: u64) -> u32 {
    let x = (x & P as u64) + (x >> 31);   // fold 1
    let x = (x & P as u64) + (x >> 31);   // fold 2
    let x = x as u32;                      // truncation
    if x >= P { x - P } else { x }         // one conditional subtraction
}
```

with `P = 2^31 - 1`, and `M31::mul(a, b) = M31(reduce_u64(a as u64 * b as u64))`.

The model stays at the natural-number level.  The two Rust bit operations are
kept literal — `x &&& P` and `x >>> 31` — and reduced to `Nat` division/modulo
by `2^31` through two identities proved structurally (not by testing numerals):

* `mask_low_eq_mod` : `x &&& (2^k - 1) = x % 2^k`, from the bitwise
  characterisations of `&&&`, `2^k - 1` and `% 2^k` (general in `k`);
* `shift_high_eq_div` : `x >>> k = x / 2^k`.

`fold31` is the resulting div/mod fold `x % 2^31 + x / 2^31`; it is not defined
as `x % P`, so canonicality is a theorem, not an assumption.  The `as u32`
truncation is modelled as `% 2^32` and proved to be the identity on the
post-fold value, so nothing is lost at the cast.

Nothing here claims that Lean reads Rust.  The residual code/model equality — the
extracted `reduce_u64` graph equalling `rawReduceU64` on every `u64` — is the
named boundary `RustReduceU64Matches`; the two transfer lemmas show that any
function meeting it inherits the canonicality and residue guarantees proved
below.
-/

namespace AspisV5M31RawMulReduction

open AspisV5ComponentCQM31RustFormulaSeam
open AspisV5ComponentCQM31TowerExact
open AspisV5ComponentCRejectionSampler

/-! ## Literal reducer graph -/

/-- One Mersenne fold in literal Rust bit-operation form: mask off the low 31
bits with `P = 2^31 - 1` and add the high part shifted down by 31. -/
def foldBits (x : Nat) : Nat := (x &&& P) + (x >>> 31)

/-- The same fold expressed by `Nat` division/modulo by `2^31`. -/
def fold31 (x : Nat) : Nat := x % 2 ^ 31 + x / 2 ^ 31

/-- The Rust `as u32` narrowing of a `Nat`, i.e. reduction modulo `2^32`
(`rawWordCount`). -/
def truncU32 (x : Nat) : Nat := x % 2 ^ 32

/-- One conditional subtraction of `P` (`if x >= P then x - P else x`). -/
def condSubP (x : Nat) : Nat := if P ≤ x then x - P else x

/-- The literal `reduce_u64` graph: two bit-folds, an `as u32` truncation, then
one conditional subtraction. -/
def rawReduceU64 (x : Nat) : Nat := condSubP (truncU32 (foldBits (foldBits x)))

/-- `M31::mul` on stored words: reduce the full `u64` product. -/
def rawM31Mul (x y : Nat) : Nat := rawReduceU64 (x * y)

/-! ## The two bitwise identities, proved structurally

Both are general in the bit width and are established from the bitwise
characterisations that ground `&&&`, `2^k - 1` and `% 2^k` in `Nat`
division/modulo.  No specific numeral is tested. -/

/-- Masking off the low `k` bits (AND with `2^k - 1`) is reduction modulo `2^k`.
Proved by `Nat.eq_of_testBit_eq`: bit `i` of each side is `testBit x i`
restricted to `i < k`. -/
theorem mask_low_eq_mod (x k : Nat) : x &&& (2 ^ k - 1) = x % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow,
    Bool.and_comm]

/-- Shifting right by `k` is integer division by `2^k`. -/
theorem shift_high_eq_div (x k : Nat) : x >>> k = x / 2 ^ k :=
  Nat.shiftRight_eq_div_pow x k

/-- The literal bit-fold equals the div/mod fold.  Here the low-bit mask is the
Mersenne constant `P = 2^31 - 1`, so `mask_low_eq_mod` applies at `k = 31`. -/
theorem foldBits_eq_fold31 (x : Nat) : foldBits x = fold31 x := by
  unfold foldBits fold31
  rw [show P = 2 ^ 31 - 1 from by norm_num [P], mask_low_eq_mod, shift_high_eq_div]

/-! ## Width fits after each fold (task item 1)

Exact bounds used, for every `x < 2^64`:
* after fold 1, `foldBits x < 2^33 + 2^31 = 10737418240` (about 34 bits — it
  stays in `u64`, and is genuinely wider than `u32`, see the load-bearing tooth);
* after fold 2, `foldBits (foldBits x) ≤ 2147483651 = P + 4 < 2^32`, so the
  `as u32` narrowing is exact. -/

/-- Fold 1 keeps any `u64` below `2^33 + 2^31`. -/
theorem first_fold_lt (x : Nat) (hx : x < 2 ^ 64) : foldBits x < 10737418240 := by
  rw [foldBits_eq_fold31]
  unfold fold31
  have hdm := Nat.div_add_mod x (2 ^ 31)
  have hmod : x % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt x (by norm_num)
  have hdiv : x / 2 ^ 31 < 2 ^ 33 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ 31)]; omega
  have e31 : (2 : Nat) ^ 31 = 2147483648 := by norm_num
  have e33 : (2 : Nat) ^ 33 = 8589934592 := by norm_num
  omega

/-- A single fold of anything below `2^33 + 2^31` lands at or below `P + 4`. -/
theorem fold31_second_le (n : Nat) (hn : n < 10737418240) : fold31 n ≤ 2147483651 := by
  unfold fold31
  have hdm := Nat.div_add_mod n (2 ^ 31)
  have hmod : n % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt n (by norm_num)
  have e31 : (2 : Nat) ^ 31 = 2147483648 := by norm_num
  omega

/-- After two folds the value is at most `P + 4 = 2147483651`. -/
theorem second_fold_le (x : Nat) (hx : x < 2 ^ 64) :
    foldBits (foldBits x) ≤ 2147483651 := by
  rw [foldBits_eq_fold31, foldBits_eq_fold31]
  exact fold31_second_le (fold31 x) (by rw [← foldBits_eq_fold31]; exact first_fold_lt x hx)

/-- After two folds the value is below `2^32`, so the `as u32` cast is exact. -/
theorem second_fold_lt_two_pow32 (x : Nat) (hx : x < 2 ^ 64) :
    foldBits (foldBits x) < 2 ^ 32 := by
  have h := second_fold_le x hx
  have e : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  omega

/-- The `as u32` narrowing of the twice-folded value is the identity. -/
theorem second_fold_cast_exact (x : Nat) (hx : x < 2 ^ 64) :
    truncU32 (foldBits (foldBits x)) = foldBits (foldBits x) :=
  Nat.mod_eq_of_lt (second_fold_lt_two_pow32 x hx)

/-! ## One conditional subtraction suffices (task item 2) -/

/-- After two folds the value is below `2 * P`, so a single subtraction of `P`
canonicalises it. -/
theorem second_fold_lt_two_mul_P (x : Nat) (hx : x < 2 ^ 64) :
    foldBits (foldBits x) < 2 * P := by
  have h := second_fold_le x hx
  have hP : P = 2147483647 := rfl
  omega

/-! ## Canonical output (task item 3) -/

/-- `rawReduceU64 x` is canonical for every `u64` input.  The two folds bring
`x` below `2^32` (cast exact) and below `2 * P`, so the single conditional
subtraction lands strictly below `P`. -/
theorem rawReduceU64_canonical (x : Nat) (hx : x < 2 ^ 64) : rawReduceU64 x < P := by
  unfold rawReduceU64 condSubP
  rw [second_fold_cast_exact x hx]
  have hb := second_fold_le x hx
  have hP : P = 2147483647 := rfl
  split <;> omega

/-! ## Residue preservation (task item 4) -/

/-- `2^31` is `1` in the field, because `2^31 = P + 1`. -/
theorem cast_two_pow31 : ((2 ^ 31 : Nat) : M31Exact) = 1 := by
  rw [show (2 ^ 31 : Nat) = P + 1 from by norm_num [P], Nat.cast_add, Nat.cast_one,
    ZMod.natCast_self, zero_add]

/-- One fold preserves the residue class modulo `P`: writing
`n = 2^31 * (n / 2^31) + n % 2^31` and using `2^31 = 1` in the field collapses
the high part onto the low part. -/
theorem fold31_residue (n : Nat) : ((fold31 n : Nat) : M31Exact) = (n : M31Exact) := by
  have hsplit := Nat.div_add_mod n (2 ^ 31)
  unfold fold31
  rw [Nat.cast_add]
  conv_rhs => rw [← hsplit]
  rw [Nat.cast_add, Nat.cast_mul, cast_two_pow31]
  ring

/-- The whole reducer preserves the residue class: the `as u32` cast is exact,
each fold preserves residues, and subtracting `P` in the high branch is a
no-op modulo `P`. -/
theorem rawReduceU64_residue (x : Nat) (hx : x < 2 ^ 64) :
    ((rawReduceU64 x : Nat) : M31Exact) = (x : M31Exact) := by
  unfold rawReduceU64 condSubP
  rw [second_fold_cast_exact x hx, foldBits_eq_fold31, foldBits_eq_fold31]
  have hcond : ((if P ≤ fold31 (fold31 x) then fold31 (fold31 x) - P
      else fold31 (fold31 x) : Nat) : M31Exact) = ((fold31 (fold31 x) : Nat) : M31Exact) := by
    split
    · rename_i h; rw [Nat.cast_sub h, ZMod.natCast_self, sub_zero]
    · rfl
  rw [hcond, fold31_residue, fold31_residue]

/-- Consequently, on `u64` inputs the reducer is exactly the remainder modulo
`P`: canonical output plus preserved residue pins the value uniquely. -/
theorem rawReduceU64_eq_mod (z : Nat) (hz : z < 2 ^ 64) : rawReduceU64 z = z % P := by
  have hcanon : rawReduceU64 z < P := rawReduceU64_canonical z hz
  have hres := rawReduceU64_residue z hz
  rw [ZMod.natCast_eq_natCast_iff] at hres
  have hmodeq : rawReduceU64 z % P = z % P := hres
  rw [Nat.mod_eq_of_lt hcanon] at hmodeq
  exact hmodeq

/-! ## Multiplication seam (task items 5–8) -/

/-- Two canonical M31 factors multiply without overflowing `u64`
(`(P-1)^2 < 2^64`), which is exactly the precondition of the reducer above. -/
theorem canonicalMul_lt_two_pow64 {x y : Nat}
    (hx : CanonicalRawM31 x) (hy : CanonicalRawM31 y) : x * y < 2 ^ 64 := by
  unfold CanonicalRawM31 at hx hy
  have h : x * y ≤ (P - 1) * (P - 1) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : (P - 1) * (P - 1) < 2 ^ 64 := by norm_num [P]
  omega

/-- The raw product reducer output is canonical for canonical inputs. -/
theorem rawM31Mul_canonical {x y : Nat}
    (hx : CanonicalRawM31 x) (hy : CanonicalRawM31 y) : CanonicalRawM31 (rawM31Mul x y) :=
  rawReduceU64_canonical _ (canonicalMul_lt_two_pow64 hx hy)

/-- The `ZMod P` image of the raw product equals the product of the input
residues. -/
theorem rawM31Mul_residue {x y : Nat}
    (hx : CanonicalRawM31 x) (hy : CanonicalRawM31 y) :
    ((rawM31Mul x y : Nat) : M31Exact) = (x : M31Exact) * (y : M31Exact) := by
  unfold rawM31Mul
  rw [rawReduceU64_residue _ (canonicalMul_lt_two_pow64 hx hy), Nat.cast_mul]

/-- The canonical M31 modulus equals `P` (`2^31 - 1 = 2147483647`). -/
theorem m31Modulus_eq_P : m31Modulus = P := by
  norm_num [m31Modulus, rawCandidateCount, P]

/-- Package the raw product as the existing canonical `Fin P` M31 type. -/
def rawM31MulValue (a b : M31Value) : M31Value :=
  ⟨rawM31Mul (a : Nat) (b : Nat), by
    have ha : CanonicalRawM31 (a : Nat) := by
      show (a : Nat) < P; rw [← m31Modulus_eq_P]; exact a.isLt
    have hb : CanonicalRawM31 (b : Nat) := by
      show (b : Nat) < P; rw [← m31Modulus_eq_P]; exact b.isLt
    have h : rawM31Mul (a : Nat) (b : Nat) < P := rawM31Mul_canonical ha hb
    have hm : m31Modulus = P := m31Modulus_eq_P
    omega⟩

/-- At the canonical `Fin P` representation the packaged raw product is the
inherited `Fin` multiplication `(a.val * b.val) % m31Modulus`. -/
theorem rawM31MulValue_eq_fin_mul (a b : M31Value) : rawM31MulValue a b = a * b := by
  apply Fin.ext
  rw [Fin.val_mul]
  show rawM31Mul (a : Nat) (b : Nat) = (a : Nat) * (b : Nat) % m31Modulus
  have ha : CanonicalRawM31 (a : Nat) := by
    show (a : Nat) < P; rw [← m31Modulus_eq_P]; exact a.isLt
  have hb : CanonicalRawM31 (b : Nat) := by
    show (b : Nat) < P; rw [← m31Modulus_eq_P]; exact b.isLt
  unfold rawM31Mul
  rw [rawReduceU64_eq_mod _ (canonicalMul_lt_two_pow64 ha hb)]
  rfl

/-- Strongest correspondence: the packaged two-fold-reducer multiplication on
canonical M31 values is exactly the exact-field multiplication already used by
the CM31/QM31 formula proofs. -/
theorem rawM31MulValue_eq_exactM31_mul (a b : M31Value) :
    rawM31MulValue a b = exactM31SourceOps.mul a b := by
  rw [rawM31MulValue_eq_fin_mul]
  apply m31ResidueEquiv.injective
  simp [exactM31SourceOps]

/-! ## Residual code/model boundary

`rawReduceU64` is the natural-number model; the residual an extraction such as
Aeneas must still supply is that the extracted `reduce_u64` graph equals it on
every `u64`.  The transfer lemmas show that any function meeting this boundary
inherits canonicality and residue preservation, so the boundary is the only
open obligation. -/

/-- Named code/model equality: the Rust `reduce_u64` agrees with `rawReduceU64`
on every `u64` input. -/
def RustReduceU64Matches (rustReduce : Nat → Nat) : Prop :=
  ∀ x, x < 2 ^ 64 → rustReduce x = rawReduceU64 x

/-- The model satisfies its own boundary, so the obligation is not vacuous. -/
theorem rustReduceU64Matches_nonvacuous : RustReduceU64Matches rawReduceU64 :=
  fun _ _ => rfl

/-- Any Rust reducer meeting the boundary produces canonical output. -/
theorem rustReduce_canonical_of_matches {rustReduce : Nat → Nat}
    (h : RustReduceU64Matches rustReduce) (x : Nat) (hx : x < 2 ^ 64) :
    rustReduce x < P := by
  rw [h x hx]; exact rawReduceU64_canonical x hx

/-- Any Rust reducer meeting the boundary preserves the residue class. -/
theorem rustReduce_residue_of_matches {rustReduce : Nat → Nat}
    (h : RustReduceU64Matches rustReduce) (x : Nat) (hx : x < 2 ^ 64) :
    ((rustReduce x : Nat) : M31Exact) = (x : M31Exact) := by
  rw [h x hx]; exact rawReduceU64_residue x hx

/-! ## Teeth -/

/-- Maximal `u64` input.  The universal canonicality and residue theorems apply
at `x = 2^64 - 1`, with no special-casing. -/
theorem tooth_max_u64_general :
    rawReduceU64 (2 ^ 64 - 1) < P ∧
    ((rawReduceU64 (2 ^ 64 - 1) : Nat) : M31Exact) = ((2 ^ 64 - 1 : Nat) : M31Exact) :=
  ⟨rawReduceU64_canonical _ (by norm_num), rawReduceU64_residue _ (by norm_num)⟩

/-- Concrete check (a consequence of `rawReduceU64_eq_mod`, not a substitute for
it): `2^64 - 1` reduces to `3`, since `2^64 ≡ 4 (mod P)`. -/
theorem tooth_max_u64_value : rawReduceU64 (2 ^ 64 - 1) = 3 := by
  rw [rawReduceU64_eq_mod _ (by norm_num)]; norm_num [P]

/-- Multiplication specialised to the maximal canonical factor `P - 1`.  The
universal canonicality and residue theorems apply. -/
theorem tooth_maxsq_general :
    CanonicalRawM31 (rawM31Mul (P - 1) (P - 1)) ∧
    ((rawM31Mul (P - 1) (P - 1) : Nat) : M31Exact)
      = ((P - 1 : Nat) : M31Exact) * ((P - 1 : Nat) : M31Exact) :=
  ⟨rawM31Mul_canonical (by norm_num [CanonicalRawM31, P]) (by norm_num [CanonicalRawM31, P]),
   rawM31Mul_residue (by norm_num [CanonicalRawM31, P]) (by norm_num [CanonicalRawM31, P])⟩

/-- Concrete check: `(P-1)^2 ≡ 1 (mod P)`, since `P - 1 ≡ -1`. -/
theorem tooth_maxsq_value : rawM31Mul (P - 1) (P - 1) = 1 := by
  unfold rawM31Mul
  rw [rawReduceU64_eq_mod _ (canonicalMul_lt_two_pow64
    (by norm_num [CanonicalRawM31, P]) (by norm_num [CanonicalRawM31, P]))]
  norm_num [P]

/-- The second fold is load-bearing.  At `x = 2^64 - 1` a single fold leaves
`10737418238`, which is both `≥ 2^32` (so the `as u32` cast would corrupt it)
and `≥ 2 * P` (so one conditional subtraction cannot canonicalise it): the
universal `x < 2^64` guarantees fail with only one fold. -/
theorem tooth_second_fold_load_bearing :
    foldBits (2 ^ 64 - 1) = 10737418238 ∧
    2 ^ 32 ≤ foldBits (2 ^ 64 - 1) ∧
    2 * P ≤ foldBits (2 ^ 64 - 1) := by
  have h : foldBits (2 ^ 64 - 1) = 10737418238 := by
    rw [foldBits_eq_fold31]; norm_num [fold31]
  refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> norm_num [P]

/-! ## Axiom audit -/

#print axioms mask_low_eq_mod
#print axioms shift_high_eq_div
#print axioms foldBits_eq_fold31
#print axioms first_fold_lt
#print axioms second_fold_lt_two_pow32
#print axioms second_fold_cast_exact
#print axioms second_fold_lt_two_mul_P
#print axioms rawReduceU64_canonical
#print axioms rawReduceU64_residue
#print axioms rawReduceU64_eq_mod
#print axioms canonicalMul_lt_two_pow64
#print axioms rawM31Mul_canonical
#print axioms rawM31Mul_residue
#print axioms rawM31MulValue_eq_fin_mul
#print axioms rawM31MulValue_eq_exactM31_mul
#print axioms rustReduceU64Matches_nonvacuous
#print axioms rustReduce_canonical_of_matches
#print axioms rustReduce_residue_of_matches
#print axioms tooth_max_u64_general
#print axioms tooth_max_u64_value
#print axioms tooth_maxsq_general
#print axioms tooth_maxsq_value
#print axioms tooth_second_fold_load_bearing

end AspisV5M31RawMulReduction
