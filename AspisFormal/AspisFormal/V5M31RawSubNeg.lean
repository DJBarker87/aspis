import AspisFormal.V5ComponentCQM31RustFormulaSeam

/-!
# Raw M31 subtraction / negation: natural-number ↔ field correspondence

This leaf sits directly below the abstract base-field seam in
`V5ComponentCQM31RustFormulaSeam`.  That file proves the CM31/QM31 formula
tower on top of the *abstract* base operations `exactM31SourceOps.sub` and
`exactM31SourceOps.neg`, and it already carries the raw-word graph for
`M31::add` (`rawM31Add`).  It never modelled the raw-word graphs for the two
remaining scalar primitives.  This file supplies them.

The literal production graphs (`crates/aspis-core/src/field.rs`) are:

```
fn sub(self, rhs) { let s = self.0 + P - rhs.0; if s >= P { s - P } else { s } }
fn neg(self)      { if self.0 == 0 { 0 } else { P - self.0 } }
```

`rawM31Sub`/`rawM31Neg` below are the exact natural-number transcriptions,
with both subtraction branches kept explicit (`rawM31Sub_high_branch`,
`rawM31Sub_low_branch`) so an Aeneas wrapper can reuse the side conditions.

Every main theorem quantifies over *arbitrary* canonical inputs
(`CanonicalRawM31 x := x < P`); the concrete `tooth_*` lemmas are teeth, not
substitutes for the universal statements.  The strongest results are
`rawM31SubValue_eq_exactM31_sub` and `rawM31NegValue_eq_exactM31_neg`: the
packaged raw graph on canonical residues *is* the abstract field operation
that the whole formula tower already consumes.

Residual for a future Aeneas extraction: it must still discharge that the
Lean image of the generated Rust `M31::sub` / `M31::neg` equals these two Nat
graphs (`rawM31Sub` / `rawM31Neg`).  Everything downstream of that equality is
proved here.  As with `rawM31Add`, this is a named compatibility boundary
between two separately kernel-checked artifacts (Aeneas is pinned to Lean
4.31, this corpus to 4.32), not yet a single imported theorem chain.
-/

namespace AspisV5M31RawSubNeg

open AspisV5ComponentCQM31TowerExact
open AspisV5ComponentCRejectionSampler
open AspisV5ComponentCQM31RustFormulaSeam

/-! ## The literal Rust natural-number graphs -/

/-- The natural-number graph of Rust's `M31::sub`: bias by `P`, then one
conditional subtraction.  `s` mirrors the Rust `let s = self.0 + P - rhs.0`. -/
def rawM31Sub (x y : Nat) : Nat :=
  let s := x + P - y
  if P ≤ s then s - P else s

/-- The natural-number graph of Rust's `M31::neg`: a zero test guarding
`P - x`.  The `x == 0` branch is load-bearing (see the teeth). -/
def rawM31Neg (x : Nat) : Nat :=
  if x = 0 then 0 else P - x

/-! ## (1)–(2) The u32 edges that precede the conditional subtraction -/

/-- The biased sum `self.0 + P` computed before the checked `- rhs.0` fits in a
Rust `u32`.  This closes the potential add-overflow edge for the extraction. -/
theorem canonicalRawM31_sub_add_lt_u32 {x y : Nat}
    (hx : CanonicalRawM31 x) (_hy : CanonicalRawM31 y) :
    x + P < 2 ^ 32 := by
  norm_num [CanonicalRawM31, P] at hx ⊢
  omega

/-- The checked natural subtraction `self.0 + P - rhs.0` cannot underflow: any
canonical `y` is bounded by the biased `x + P`. -/
theorem canonicalRawM31_sub_no_underflow {x y : Nat}
    (_hx : CanonicalRawM31 x) (hy : CanonicalRawM31 y) :
    x + P ≥ y := by
  unfold CanonicalRawM31 at hy
  omega

/-! ## Explicit subtraction branches (for the Aeneas wrapper) -/

/-- High branch (`s ≥ P`): the second checked subtraction fires, does not
underflow, and lands below `P`. -/
theorem rawM31Sub_high_branch {x y : Nat}
    (hx : CanonicalRawM31 x) (_hy : CanonicalRawM31 y) (hhigh : P ≤ x + P - y) :
    rawM31Sub x y = x + P - y - P ∧ P ≤ x + P - y ∧ x + P - y - P < P := by
  refine ⟨by simp [rawM31Sub, hhigh], hhigh, ?_⟩
  unfold CanonicalRawM31 at hx
  omega

/-- Low branch (`s < P`): the comparison itself supplies the output bound and
no second subtraction is performed. -/
theorem rawM31Sub_low_branch {x y : Nat} (hlow : x + P - y < P) :
    rawM31Sub x y = x + P - y ∧ x + P - y < P := by
  have hnot : ¬ P ≤ x + P - y := by omega
  exact ⟨by simp [rawM31Sub, hnot], hlow⟩

/-! ## (3) Canonicality of the raw subtraction -/

/-- One conditional subtraction produces a canonical M31 representative. -/
theorem rawM31Sub_canonical {x y : Nat}
    (hx : CanonicalRawM31 x) (_hy : CanonicalRawM31 y) :
    CanonicalRawM31 (rawM31Sub x y) := by
  unfold CanonicalRawM31 at hx ⊢
  simp only [rawM31Sub]
  split <;> omega

/-! ## (4) The raw subtraction commutes with reduction into `ZMod P` -/

/-- The literal Rust subtraction graph reduces to `x - y` in the exact
`ZMod (2^31-1)` model.  Both comparison branches are covered explicitly. -/
theorem residue_rawM31Sub {x y : Nat}
    (hx : CanonicalRawM31 x) (hy : CanonicalRawM31 y) :
    ((rawM31Sub x y : Nat) : M31Exact) = (x : M31Exact) - (y : M31Exact) := by
  have hx' : x < P := hx
  have hy' : y < P := hy
  by_cases hhigh : P ≤ x + P - y
  · rw [(rawM31Sub_high_branch hx hy hhigh).1]
    have hyx : y ≤ x := by omega
    have hid : x + P - y - P = x - y := by omega
    rw [hid, Nat.cast_sub hyx]
  · have hlow : x + P - y < P := by omega
    rw [(rawM31Sub_low_branch hlow).1]
    have hle : y ≤ x + P := by omega
    rw [Nat.cast_sub hle, Nat.cast_add, ZMod.natCast_self, add_zero]

/-! ## (5) The packaged raw subtraction is the abstract field subtraction -/

/-- The one-subtraction graph is the ordinary remainder of the biased sum,
because the canonical bounds keep `(P - y) + x` strictly below `2*P`.  The
argument order matches `Fin.val_sub`. -/
theorem rawM31Sub_eq_mod {x y : Nat}
    (hx : CanonicalRawM31 x) (hy : CanonicalRawM31 y) :
    rawM31Sub x y = (P - y + x) % P := by
  unfold CanonicalRawM31 at hx hy
  have hcomm : P - y + x = x + P - y := by omega
  by_cases hhigh : P ≤ x + P - y
  · rw [rawM31Sub, if_pos hhigh, hcomm, Nat.mod_eq_sub_mod hhigh,
      Nat.mod_eq_of_lt (show x + P - y - P < P by omega)]
  · have hlow : x + P - y < P := Nat.lt_of_not_ge hhigh
    rw [rawM31Sub, if_neg hhigh, hcomm, Nat.mod_eq_of_lt hlow]

/-- Package the raw output as the existing canonical-residue type. -/
def rawM31SubValue (a b : M31Value) : M31Value :=
  ⟨rawM31Sub a b, by
    have h := rawM31Sub_canonical
      (x := (a : Nat)) (y := (b : Nat))
      (by simp [CanonicalRawM31, P, m31Modulus, rawCandidateCount])
      (by simp [CanonicalRawM31, P, m31Modulus, rawCandidateCount])
    simpa [CanonicalRawM31, P, m31Modulus, rawCandidateCount] using h⟩

/-- At the canonical `Fin P` representation, the raw graph is the inherited
`Fin` subtraction. -/
theorem rawM31SubValue_eq_fin_sub (a b : M31Value) :
    rawM31SubValue a b = a - b := by
  apply Fin.ext
  rw [Fin.val_sub]
  exact rawM31Sub_eq_mod
    (by simp [CanonicalRawM31, P, m31Modulus, rawCandidateCount])
    (by simp [CanonicalRawM31, P, m31Modulus, rawCandidateCount])

/-- Consequently the packaged raw subtraction is exactly the abstract
`exactM31SourceOps.sub` already consumed by every CM31/QM31 formula proof. -/
theorem rawM31SubValue_eq_exactM31_sub (a b : M31Value) :
    rawM31SubValue a b = exactM31SourceOps.sub a b := by
  rw [rawM31SubValue_eq_fin_sub]
  apply m31ResidueEquiv.injective
  simp [exactM31SourceOps, map_sub]

/-! ## (6) Canonicality of the raw negation -/

/-- The zero-guarded negation produces a canonical M31 representative. -/
theorem rawM31Neg_canonical {x : Nat} (hx : CanonicalRawM31 x) :
    CanonicalRawM31 (rawM31Neg x) := by
  unfold CanonicalRawM31 at hx ⊢
  unfold rawM31Neg
  split <;> omega

/-! ## (7) The raw negation commutes with reduction into `ZMod P` -/

/-- The literal Rust negation graph reduces to `-x` in the exact model. -/
theorem residue_rawM31Neg {x : Nat} (hx : CanonicalRawM31 x) :
    ((rawM31Neg x : Nat) : M31Exact) = -(x : M31Exact) := by
  have hx' : x < P := hx
  by_cases hz : x = 0
  · subst hz
    simp [rawM31Neg]
  · rw [rawM31Neg, if_neg hz]
    have hle : x ≤ P := le_of_lt hx'
    rw [Nat.cast_sub hle, ZMod.natCast_self, zero_sub]

/-! ## (8) The packaged raw negation is the abstract field negation -/

/-- The zero-guarded graph is the ordinary remainder `(P - x) % P`; the zero
case makes `P % P = 0` and the nonzero case leaves `P - x` untouched.  The form
matches `Fin.val_neg'`. -/
theorem rawM31Neg_eq_mod {x : Nat} (hx : CanonicalRawM31 x) :
    rawM31Neg x = (P - x) % P := by
  have hx' : x < P := hx
  by_cases hz : x = 0
  · subst hz
    simp [rawM31Neg]
  · rw [rawM31Neg, if_neg hz, Nat.mod_eq_of_lt (by omega)]

/-- Package the raw negation output as the existing canonical-residue type. -/
def rawM31NegValue (a : M31Value) : M31Value :=
  ⟨rawM31Neg a, by
    have h := rawM31Neg_canonical (x := (a : Nat))
      (by simp [CanonicalRawM31, P, m31Modulus, rawCandidateCount])
    simpa [CanonicalRawM31, P, m31Modulus, rawCandidateCount] using h⟩

/-- At the canonical `Fin P` representation, the raw graph is the inherited
`Fin` negation. -/
theorem rawM31NegValue_eq_fin_neg (a : M31Value) :
    rawM31NegValue a = -a := by
  apply Fin.ext
  rw [Fin.val_neg']
  exact rawM31Neg_eq_mod
    (by simp [CanonicalRawM31, P, m31Modulus, rawCandidateCount])

/-- Consequently the packaged raw negation is exactly the abstract
`exactM31SourceOps.neg` already consumed by every CM31/QM31 formula proof. -/
theorem rawM31NegValue_eq_exactM31_neg (a : M31Value) :
    rawM31NegValue a = exactM31SourceOps.neg a := by
  rw [rawM31NegValue_eq_fin_neg]
  apply m31ResidueEquiv.injective
  simp [exactM31SourceOps, map_neg]

/-! ## Teeth (concrete, proven — NOT substitutes for the universal theorems) -/

/-- Tooth: at the boundary `0 - 1`, the biased sum stays in the low branch. -/
theorem tooth_rawM31Sub_zero_one : rawM31Sub 0 1 = P - 1 := by decide

/-- Tooth: the zero case of negation returns `0`, not `P`. -/
theorem tooth_rawM31Neg_zero : rawM31Neg 0 = 0 := by decide

/-- Tooth: the nonzero case of negation returns `P - x`. -/
theorem tooth_rawM31Neg_one : rawM31Neg 1 = P - 1 := by decide

/-- The tempting but WRONG unconditional negation graph `P - x`, dropping the
`x == 0` guard. -/
def rawM31NegUnconditional (x : Nat) : Nat := P - x

/-- Tooth: the unconditional graph is NONcanonical at `x = 0` (it returns `P`,
i.e. `¬ CanonicalRawM31 (P - 0)`), so the `if x == 0` branch is load-bearing. -/
theorem tooth_unconditional_neg_noncanonical :
    ¬ CanonicalRawM31 (rawM31NegUnconditional 0) := by
  unfold CanonicalRawM31 rawM31NegUnconditional
  omega

/-- Tooth companion: side by side, the guarded graph canonicalises `0` while
the unconditional one escapes to `P ≠ 0`. -/
theorem tooth_zero_guard_is_loadbearing :
    rawM31Neg 0 = 0 ∧ rawM31NegUnconditional 0 = P ∧ (0 : Nat) ≠ P := by
  refine ⟨by decide, rfl, by decide⟩

/-! ## Axiom audit -/

#print axioms canonicalRawM31_sub_add_lt_u32
#print axioms canonicalRawM31_sub_no_underflow
#print axioms rawM31Sub_high_branch
#print axioms rawM31Sub_low_branch
#print axioms rawM31Sub_canonical
#print axioms residue_rawM31Sub
#print axioms rawM31Sub_eq_mod
#print axioms rawM31SubValue_eq_fin_sub
#print axioms rawM31SubValue_eq_exactM31_sub
#print axioms rawM31Neg_canonical
#print axioms residue_rawM31Neg
#print axioms rawM31Neg_eq_mod
#print axioms rawM31NegValue_eq_fin_neg
#print axioms rawM31NegValue_eq_exactM31_neg
#print axioms tooth_rawM31Sub_zero_one
#print axioms tooth_rawM31Neg_zero
#print axioms tooth_rawM31Neg_one
#print axioms tooth_unconditional_neg_noncanonical
#print axioms tooth_zero_guard_is_loadbearing

end AspisV5M31RawSubNeg
