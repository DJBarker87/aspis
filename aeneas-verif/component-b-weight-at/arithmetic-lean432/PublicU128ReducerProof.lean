import AspisCorePublicReducers
import M31ReduceU64Proof

/-!
# Source-authentic public `M31::reduce_u128`

The proof follows the generated four Mersenne folds, the generated narrowing
to `u32`, and the final conditional subtraction.  In particular, it does not
replace the deployed body with an abstract modular reduction.
-/

open Aeneas Aeneas.Std Result

namespace AspisAeneasPublicU128Reducer

open AspisCorePublicReducers
open AspisAeneasM31ReduceU64

abbrev CanonicalRawM31 := AspisAeneasM31ReduceU64.CanonicalRawM31
abbrev M31Exact := AspisAeneasM31ReduceU64.M31Exact
abbrev u128Cardinality : Nat := 2 ^ 128

def rawM31ReduceU128 (x : Nat) : Nat :=
  let folded :=
    mersenneFold31 (mersenneFold31 (mersenneFold31 (mersenneFold31 x)))
  if m31Modulus ≤ folded then folded - m31Modulus else folded

/-- The deliberately incorrect three-fold variant models narrowing at the
same point after omitting the fourth production fold. -/
def rawM31ReduceU128ThreeFolds (x : Nat) : Nat :=
  let folded := mersenneFold31 (mersenneFold31 (mersenneFold31 x))
  let narrowed := folded % (2 ^ 32)
  if m31Modulus ≤ narrowed then narrowed - m31Modulus else narrowed

@[simp] private theorem extracted_public_P_val : field.P.val = m31Modulus := by
  unfold field.P
  rfl

private theorem u128_size_eq : UScalar.size .U128 = u128Cardinality := by
  rw [UScalar.size_def, UScalarTy.U128_numBits_eq]

private theorem shift31_u128_val (x : Std.U128) :
    (Std.U128.wrapping_shr x 31#i32).val = x.val / 2 ^ 31 := by
  rw [show (31#i32 : Std.I32) = 31#i32 from rfl]
  change (Std.U128.wrapping_shr x ((31#i32 : Std.I32) : Std.U32)).bv.toNat =
    x.bv.toNat / 2 ^ 31
  rw [reducerShiftCount31_exact, Std.U128.wrapping_shr_bv_eq,
    BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  norm_num

private theorem masked31_u128_val (x : Std.U128) :
    (x &&& UScalar.cast .U128 field.P).val = x.val % 2 ^ 31 := by
  rw [UScalar.val_and, U32.cast_U128_val_eq, extracted_public_P_val,
    m31Modulus_eq_two31_sub_one, Nat.and_two_pow_sub_one_eq_mod]

private theorem fold_lt_two98 {x : Nat} (hx : x < 2 ^ 128) :
    mersenneFold31 x < 2 ^ 98 := by
  have hmod : x % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by positivity)
  have hdiv : x / 2 ^ 31 < 2 ^ 97 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    norm_num [← pow_add] at hx ⊢
    exact hx
  unfold mersenneFold31
  norm_num at hmod hdiv ⊢
  omega

private theorem second_fold_lt_two68 {x : Nat} (hx : x < 2 ^ 128) :
    mersenneFold31 (mersenneFold31 x) < 2 ^ 68 := by
  have hfirst := fold_lt_two98 hx
  have hmod : mersenneFold31 x % 2 ^ 31 < 2 ^ 31 :=
    Nat.mod_lt _ (by positivity)
  have hdiv : mersenneFold31 x / 2 ^ 31 < 2 ^ 67 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    norm_num [← pow_add] at hfirst ⊢
    exact hfirst
  unfold mersenneFold31
  norm_num at hmod hdiv ⊢
  omega

private theorem third_fold_lt_two38 {x : Nat} (hx : x < 2 ^ 128) :
    mersenneFold31 (mersenneFold31 (mersenneFold31 x)) < 2 ^ 38 := by
  have hsecond := second_fold_lt_two68 hx
  have hmod :
      mersenneFold31 (mersenneFold31 x) % 2 ^ 31 < 2 ^ 31 :=
    Nat.mod_lt _ (by positivity)
  have hdiv :
      mersenneFold31 (mersenneFold31 x) / 2 ^ 31 < 2 ^ 37 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    norm_num [← pow_add] at hsecond ⊢
    exact hsecond
  unfold mersenneFold31
  norm_num at hmod hdiv ⊢
  omega

theorem fourth_fold_lt_modulus_add_129
    {x : Nat} (hx : x < 2 ^ 128) :
    mersenneFold31
        (mersenneFold31 (mersenneFold31 (mersenneFold31 x))) <
      m31Modulus + 129 := by
  have hthird := third_fold_lt_two38 hx
  have hmod :
      mersenneFold31 (mersenneFold31 (mersenneFold31 x)) % 2 ^ 31 <
        2 ^ 31 := Nat.mod_lt _ (by positivity)
  have hdiv :
      mersenneFold31 (mersenneFold31 (mersenneFold31 x)) / 2 ^ 31 <
        2 ^ 7 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    norm_num [← pow_add] at hthird ⊢
    exact hthird
  unfold mersenneFold31
  norm_num [m31Modulus] at hmod hdiv ⊢
  omega

private theorem fourth_fold_lt_u32 {x : Nat} (hx : x < 2 ^ 128) :
    mersenneFold31
        (mersenneFold31 (mersenneFold31 (mersenneFold31 x))) < 2 ^ 32 := by
  have h := fourth_fold_lt_modulus_add_129 hx
  norm_num [m31Modulus] at h ⊢
  omega

theorem rawM31ReduceU128_canonical {x : Nat} (hx : x < 2 ^ 128) :
    CanonicalRawM31 (rawM31ReduceU128 x) := by
  let folded :=
    mersenneFold31 (mersenneFold31 (mersenneFold31 (mersenneFold31 x)))
  have hbound : folded < m31Modulus + 129 :=
    fourth_fold_lt_modulus_add_129 hx
  by_cases hhigh : m31Modulus ≤ folded
  · rw [rawM31ReduceU128, if_pos hhigh]
    unfold CanonicalRawM31
    have hdiff : folded - m31Modulus < 129 := by omega
    exact lt_trans hdiff (by norm_num [m31Modulus])
  · have hlow : folded < m31Modulus := Nat.lt_of_not_ge hhigh
    rw [rawM31ReduceU128, if_neg hhigh]
    exact hlow

theorem residue_rawM31ReduceU128 (x : Nat) :
    ((rawM31ReduceU128 x : Nat) : M31Exact) = (x : M31Exact) := by
  let folded :=
    mersenneFold31 (mersenneFold31 (mersenneFold31 (mersenneFold31 x)))
  by_cases hhigh : m31Modulus ≤ folded
  · rw [rawM31ReduceU128, if_pos hhigh, Nat.cast_sub hhigh,
      ZMod.natCast_self, sub_zero, residue_mersenneFold31,
      residue_mersenneFold31, residue_mersenneFold31,
      residue_mersenneFold31]
  · rw [rawM31ReduceU128, if_neg hhigh, residue_mersenneFold31,
      residue_mersenneFold31, residue_mersenneFold31,
      residue_mersenneFold31]

def extractedFold31U128 (x : Std.U128) : Std.U128 :=
  Std.U128.wrapping_add
    (x &&& UScalar.cast .U128 field.P)
    (Std.U128.wrapping_shr x 31#i32)

def extractedReduceU128Out (x : Std.U128) : Std.U32 :=
  let folded := extractedFold31U128
    (extractedFold31U128 (extractedFold31U128 (extractedFold31U128 x)))
  let narrowed := UScalar.cast .U32 folded
  if narrowed >= field.P then Std.U32.wrapping_sub narrowed field.P
  else narrowed

private theorem extractedFold31U128_val (x : Std.U128) :
    (extractedFold31U128 x).val = mersenneFold31 x.val := by
  rw [extractedFold31U128, Std.U128.wrapping_add_val_eq, u128_size_eq,
    masked31_u128_val, shift31_u128_val]
  apply Nat.mod_eq_of_lt
  have hx : x.val < 2 ^ 128 := by
    simpa [UScalarTy.U128_numBits_eq] using x.hmax
  have hfold := fold_lt_two98 hx
  norm_num [u128Cardinality] at hfold ⊢
  omega

private theorem extractedFourFoldsU128_val (x : Std.U128) :
    (extractedFold31U128
      (extractedFold31U128 (extractedFold31U128 (extractedFold31U128 x)))).val =
      mersenneFold31
        (mersenneFold31 (mersenneFold31 (mersenneFold31 x.val))) := by
  rw [extractedFold31U128_val, extractedFold31U128_val,
    extractedFold31U128_val, extractedFold31U128_val]

private theorem narrowedFourFoldsU128_val (x : Std.U128) :
    (UScalar.cast .U32
      (extractedFold31U128
        (extractedFold31U128
          (extractedFold31U128 (extractedFold31U128 x))))).val =
      mersenneFold31
        (mersenneFold31 (mersenneFold31 (mersenneFold31 x.val))) := by
  rw [UScalar.cast_val_eq, extractedFourFoldsU128_val,
    UScalarTy.U32_numBits_eq]
  have hx : x.val < 2 ^ 128 := by
    simpa [UScalarTy.U128_numBits_eq] using x.hmax
  rw [Nat.mod_eq_of_lt (fourth_fold_lt_u32 hx)]

private theorem wrapping_sub_public_P_val
    (narrowed : Std.U32) (hhigh : m31Modulus ≤ narrowed.val) :
    (Std.U32.wrapping_sub narrowed field.P).val =
      narrowed.val - m31Modulus := by
  change (UScalar.overflowing_sub narrowed field.P).fst.val =
    narrowed.val - m31Modulus
  have hnot : ¬narrowed.val < field.P.val := by
    rw [extracted_public_P_val]
    omega
  have hspec := UScalar.overflowing_sub_eq narrowed field.P
  simp only [hnot, ↓reduceIte] at hspec
  simpa [extracted_public_P_val] using hspec.1

private theorem extractedReduceU128Out_val (x : Std.U128) :
    (extractedReduceU128Out x).val = rawM31ReduceU128 x.val := by
  let folded :=
    mersenneFold31 (mersenneFold31 (mersenneFold31 (mersenneFold31 x.val)))
  let narrowed := UScalar.cast .U32
    (extractedFold31U128
      (extractedFold31U128 (extractedFold31U128 (extractedFold31U128 x))))
  have hnarrow : narrowed.val = folded := narrowedFourFoldsU128_val x
  change
    (if narrowed >= field.P then Std.U32.wrapping_sub narrowed field.P
      else narrowed).val = rawM31ReduceU128 x.val
  by_cases hhigh : m31Modulus ≤ folded
  · have hscalar : narrowed >= field.P := by
      change field.P.val ≤ narrowed.val
      rw [extracted_public_P_val, hnarrow]
      exact hhigh
    rw [if_pos hscalar, rawM31ReduceU128, if_pos hhigh,
      wrapping_sub_public_P_val narrowed (by simpa [hnarrow] using hhigh),
      hnarrow]
  · have hscalar : ¬narrowed >= field.P := by
      intro h
      apply hhigh
      change field.P.val ≤ narrowed.val at h
      rw [extracted_public_P_val, hnarrow] at h
      exact h
    rw [if_neg hscalar, rawM31ReduceU128, if_neg hhigh, hnarrow]

private theorem extracted_reduce_u128_eq_out (x : Std.U128) :
    field.M31.reduce_u128 x = ok (extractedReduceU128Out x) := by
  unfold field.M31.reduce_u128 extractedReduceU128Out extractedFold31U128
  simp only [Std.lift, bind_tc_ok]
  split <;> rfl

/-- The generated public `M31::reduce_u128` succeeds for every Rust `u128`,
returns a canonical limb, follows the exact four-fold raw formula, and denotes
the input residue in M31. -/
theorem extracted_public_m31_reduce_u128_corresponds (value : Std.U128) :
    ∃ out : field.M31,
      field.M31.reduce_u128 value = ok out ∧
      out.val = rawM31ReduceU128 value.val ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) = (value.val : M31Exact) := by
  let out := extractedReduceU128Out value
  have hvalue : value.val < 2 ^ 128 := by
    simpa [UScalarTy.U128_numBits_eq] using value.hmax
  have hout : out.val = rawM31ReduceU128 value.val :=
    extractedReduceU128Out_val value
  refine ⟨out, extracted_reduce_u128_eq_out value, hout, ?_, ?_⟩
  · rw [hout]
    exact rawM31ReduceU128_canonical hvalue
  · rw [hout]
    exact residue_rawM31ReduceU128 value.val

/-- At the maximum declared `u128` input, narrowing after only three folds
returns `P-1`, whereas the deployed fourth fold returns 15, the correct M31
residue.  Thus all four production folds are necessary for the full domain. -/
theorem all_four_mersenne_folds_are_necessary_at_u128_max :
    rawM31ReduceU128ThreeFolds (2 ^ 128 - 1) = m31Modulus - 1 ∧
    rawM31ReduceU128 (2 ^ 128 - 1) = 15 ∧
    rawM31ReduceU128ThreeFolds (2 ^ 128 - 1) ≠
      rawM31ReduceU128 (2 ^ 128 - 1) ∧
    ((rawM31ReduceU128ThreeFolds (2 ^ 128 - 1) : Nat) : M31Exact) ≠
      ((2 ^ 128 - 1 : Nat) : M31Exact) := by
  have hthree :
      rawM31ReduceU128ThreeFolds (2 ^ 128 - 1) = m31Modulus - 1 := by
    norm_num [rawM31ReduceU128ThreeFolds, mersenneFold31, m31Modulus]
  have hfour : rawM31ReduceU128 (2 ^ 128 - 1) = 15 := by
    norm_num [rawM31ReduceU128, mersenneFold31, m31Modulus]
  refine ⟨hthree, hfour, ?_, ?_⟩
  · rw [hthree, hfour]
    norm_num [m31Modulus]
  · rw [← residue_rawM31ReduceU128 (2 ^ 128 - 1), hthree, hfour]
    decide

#print axioms fourth_fold_lt_modulus_add_129
#print axioms rawM31ReduceU128_canonical
#print axioms residue_rawM31ReduceU128
#print axioms extracted_public_m31_reduce_u128_corresponds
#print axioms all_four_mersenne_folds_are_necessary_at_u128_max

end AspisAeneasPublicU128Reducer
