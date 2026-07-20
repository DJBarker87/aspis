import AspisCoreTowerEmbeddings
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-!
# Source-authentic CM31/QM31 tower embeddings

The three Rust calls in this file are the Aeneas definitions generated from
the frozen production source.  The exact target is the established nested
tower `M31 = ZMod (2^31-1)`, `CM31 = M31[i]/(i²+1)`, and
`QM31 = CM31[u]/(u²-(2+i))`.
-/

open Aeneas Aeneas.Std Result

namespace AspisAeneasTowerEmbeddings

open AspisCoreTowerEmbeddings

abbrev m31Modulus : Nat := 2147483647
abbrev M31Exact := ZMod m31Modulus
abbrev CM31Exact := QuadraticAlgebra M31Exact (-1) 0

def qm31R : CM31Exact := ⟨2, 1⟩

abbrev QM31Exact := QuadraticAlgebra CM31Exact qm31R 0

def CanonicalRawM31 (x : Nat) : Prop := x < m31Modulus

def CanonicalCM31 (x : field.CM31) : Prop :=
  CanonicalRawM31 x.a.val ∧ CanonicalRawM31 x.b.val

def CanonicalQM31 (x : field.QM31) : Prop :=
  CanonicalCM31 x.c0 ∧ CanonicalCM31 x.c1

def cm31ToExact (x : field.CM31) : CM31Exact :=
  ⟨(x.a.val : M31Exact), (x.b.val : M31Exact)⟩

def qm31ToExact (x : field.QM31) : QM31Exact :=
  ⟨cm31ToExact x.c0, cm31ToExact x.c1⟩

/-- The actual generated `CM31::new` call preserves both canonical limbs in
their source order and denotes their literal exact CM31 pair. -/
theorem extracted_cm31_new_corresponds
    (a b : field.M31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    ∃ out : field.CM31,
      field.CM31.new a b = ok out ∧
      CanonicalCM31 out ∧
      cm31ToExact out = ⟨(a.val : M31Exact), (b.val : M31Exact)⟩ := by
  exact ⟨⟨a, b⟩, rfl, ⟨ha, hb⟩, rfl⟩

/-- The actual generated `CM31::from_m31` call succeeds for every canonical
base limb, preserves canonicality, and is the exact base-field embedding with
zero imaginary coordinate. -/
theorem extracted_cm31_from_m31_corresponds
    (a : field.M31) (ha : CanonicalRawM31 a.val) :
    ∃ out : field.CM31,
      field.CM31.from_m31 a = ok out ∧
      CanonicalCM31 out ∧
      cm31ToExact out =
        algebraMap M31Exact CM31Exact (a.val : M31Exact) := by
  let out : field.CM31 := ⟨a, 0#u32⟩
  refine ⟨out, ?_, ?_, ?_⟩
  · unfold field.CM31.from_m31 field.M31.ZERO
    rfl
  · exact ⟨ha, by norm_num [CanonicalRawM31, m31Modulus, out]⟩
  · rfl

/-- The actual generated `QM31::from_cm31` call succeeds for every canonical
CM31 input, preserves all four canonical limbs, and is the exact coefficient
embedding with zero `u` coordinate. -/
theorem extracted_qm31_from_cm31_corresponds
    (c0 : field.CM31) (hc0 : CanonicalCM31 c0) :
    ∃ out : field.QM31,
      field.QM31.from_cm31 c0 = ok out ∧
      CanonicalQM31 out ∧
      qm31ToExact out =
        algebraMap CM31Exact QM31Exact (cm31ToExact c0) := by
  let zeroCM : field.CM31 := ⟨0#u32, 0#u32⟩
  let out : field.QM31 := ⟨c0, zeroCM⟩
  refine ⟨out, ?_, ?_, ?_⟩
  · unfold field.QM31.from_cm31 field.CM31.ZERO
    rfl
  · refine ⟨hc0, ?_⟩
    norm_num [CanonicalCM31, CanonicalRawM31, m31Modulus, out, zeroCM]
  · rfl

/-! ## Concrete negative teeth -/

/-- Swapping the two source limbs changes the exact value. -/
theorem swapped_cm31_new_coordinates_tooth :
    ∃ out : field.CM31,
      field.CM31.new 1#u32 2#u32 = ok out ∧
      cm31ToExact out = (⟨1, 2⟩ : CM31Exact) ∧
      cm31ToExact out ≠ (⟨2, 1⟩ : CM31Exact) := by
  refine ⟨⟨1#u32, 2#u32⟩, rfl, rfl, ?_⟩
  intro h
  have hre := congrArg QuadraticAlgebra.re h
  norm_num [cm31ToExact] at hre
  exact (by decide : (1 : M31Exact) ≠ 2) hre

/-- `from_m31` cannot introduce a nonzero imaginary coordinate. -/
theorem nonzero_imaginary_from_m31_tooth :
    ∃ out : field.CM31,
      field.CM31.from_m31 3#u32 = ok out ∧
      cm31ToExact out = (⟨3, 0⟩ : CM31Exact) ∧
      cm31ToExact out ≠ (⟨3, 1⟩ : CM31Exact) := by
  refine ⟨⟨3#u32, 0#u32⟩, ?_, rfl, ?_⟩
  · unfold field.CM31.from_m31 field.M31.ZERO
    rfl
  · intro h
    have him := congrArg QuadraticAlgebra.im h
    norm_num [cm31ToExact] at him
    exact (by decide : (0 : M31Exact) ≠ 1) him

/-- `from_cm31` cannot introduce a nonzero outer `u` coordinate. -/
theorem nonzero_u_coordinate_from_cm31_tooth :
    ∃ out : field.QM31,
      field.QM31.from_cm31 ⟨3#u32, 4#u32⟩ = ok out ∧
      qm31ToExact out =
        (⟨(⟨3, 4⟩ : CM31Exact), 0⟩ : QM31Exact) ∧
      qm31ToExact out ≠
        (⟨(⟨3, 4⟩ : CM31Exact), 1⟩ : QM31Exact) := by
  refine ⟨⟨⟨3#u32, 4#u32⟩, ⟨0#u32, 0#u32⟩⟩, ?_, rfl, ?_⟩
  · unfold field.QM31.from_cm31 field.CM31.ZERO
    rfl
  · intro h
    have him := congrArg QuadraticAlgebra.im h
    norm_num [qm31ToExact, cm31ToExact] at him
    have hre := congrArg QuadraticAlgebra.re him
    norm_num at hre
    exact (by decide : (0 : M31Exact) ≠ 1) hre

/-- Concrete witnesses show that every canonical input domain used by the
three capstones is inhabited. -/
theorem canonical_embedding_domains_nonempty :
    (∃ a b : field.M31,
      CanonicalRawM31 a.val ∧ CanonicalRawM31 b.val) ∧
    (∃ c : field.CM31, CanonicalCM31 c) := by
  constructor
  · exact ⟨0#u32, 0#u32,
      by norm_num [CanonicalRawM31, m31Modulus]⟩
  · exact ⟨⟨0#u32, 0#u32⟩,
      by norm_num [CanonicalCM31, CanonicalRawM31, m31Modulus]⟩

#print axioms extracted_cm31_new_corresponds
#print axioms extracted_cm31_from_m31_corresponds
#print axioms extracted_qm31_from_cm31_corresponds
#print axioms swapped_cm31_new_coordinates_tooth
#print axioms nonzero_imaginary_from_m31_tooth
#print axioms nonzero_u_coordinate_from_cm31_tooth
#print axioms canonical_embedding_domains_nonempty

end AspisAeneasTowerEmbeddings
