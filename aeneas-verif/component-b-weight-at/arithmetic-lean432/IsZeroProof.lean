import AspisCoreIsZero
import QM31MulProof

/-!
# Source-authentic `is_zero` correspondence

These proofs use the three generated Aeneas calls from the authenticated
`field.rs` extraction.  The only handwritten data conversion maps the
extraction's nominal Rust structures into the same exact M31/CM31/QM31 tower
used by the multiplication proof.
-/

open Aeneas Aeneas.Std Result

namespace AspisAeneasIsZero

open AspisCoreIsZero

abbrev M31Exact := AspisAeneasQM31Mul.M31Exact
abbrev CM31Exact := AspisAeneasQM31Mul.CM31Exact
abbrev QM31Exact := AspisAeneasQM31Mul.QM31Exact
abbrev m31Modulus : Nat := 2147483647

def CanonicalRawM31 (x : Nat) : Prop := x < m31Modulus

def CanonicalCM31 (x : field.CM31) : Prop :=
  CanonicalRawM31 x.a.val ∧ CanonicalRawM31 x.b.val

def CanonicalQM31 (x : field.QM31) : Prop :=
  CanonicalCM31 x.c0 ∧ CanonicalCM31 x.c1

def cm31ToExact (x : field.CM31) : CM31Exact :=
  ⟨(x.a.val : M31Exact), (x.b.val : M31Exact)⟩

def qm31ToExact (x : field.QM31) : QM31Exact :=
  ⟨cm31ToExact x.c0, cm31ToExact x.c1⟩

private theorem canonicalNatCastEqZero (n : Nat) (h : CanonicalRawM31 n) :
    ((n : M31Exact) = 0 ↔ n = 0) := by
  rw [ZMod.natCast_eq_zero_iff]
  change n < AspisAeneasCM31Exact.m31Modulus at h
  constructor
  · intro hd
    calc
      n = n % AspisAeneasCM31Exact.m31Modulus :=
        (Nat.mod_eq_of_lt h).symm
      _ = 0 := Nat.mod_eq_zero_of_dvd hd
  · intro hn
    subst n
    exact dvd_zero _

private theorem cm31ExactEqZero (x : field.CM31) (hx : CanonicalCM31 x) :
    (cm31ToExact x = 0 ↔ x.a.val = 0 ∧ x.b.val = 0) := by
  rw [QuadraticAlgebra.ext_iff]
  simp only [cm31ToExact, QuadraticAlgebra.re_zero,
    QuadraticAlgebra.im_zero]
  rw [canonicalNatCastEqZero x.a.val hx.1,
    canonicalNatCastEqZero x.b.val hx.2]

private theorem qm31ExactEqZero (x : field.QM31) (hx : CanonicalQM31 x) :
    (qm31ToExact x = 0 ↔
      x.c0.a.val = 0 ∧ x.c0.b.val = 0 ∧
      x.c1.a.val = 0 ∧ x.c1.b.val = 0) := by
  rw [QuadraticAlgebra.ext_iff]
  simp only [qm31ToExact, QuadraticAlgebra.re_zero,
    QuadraticAlgebra.im_zero]
  rw [QuadraticAlgebra.ext_iff, QuadraticAlgebra.ext_iff]
  simp only [cm31ToExact, QuadraticAlgebra.re_zero,
    QuadraticAlgebra.im_zero]
  rw [canonicalNatCastEqZero x.c0.a.val hx.1.1,
    canonicalNatCastEqZero x.c0.b.val hx.1.2,
    canonicalNatCastEqZero x.c1.a.val hx.2.1,
    canonicalNatCastEqZero x.c1.b.val hx.2.2]
  tauto

private theorem u32EqZeroIff (x : Std.U32) :
    x = 0#u32 ↔ x.val = 0 := by
  constructor
  · intro h
    subst x
    rfl
  · intro h
    apply UScalar.eq_of_val_eq
    simpa using h

private theorem m31IsZeroSucceeds (x : field.M31) :
    ∃ b : Bool, field.M31.is_zero x = ok b := by
  exact ⟨x = 0#u32, rfl⟩

private theorem cm31IsZeroSucceeds (x : field.CM31) :
    ∃ b : Bool, field.CM31.is_zero x = ok b := by
  rcases m31IsZeroSucceeds x.a with ⟨ba, hba⟩
  rcases m31IsZeroSucceeds x.b with ⟨bb, hbb⟩
  cases ba <;> simp [field.CM31.is_zero, hba, hbb]

private theorem qm31IsZeroSucceeds (x : field.QM31) :
    ∃ b : Bool, field.QM31.is_zero x = ok b := by
  rcases cm31IsZeroSucceeds x.c0 with ⟨b0, hb0⟩
  rcases cm31IsZeroSucceeds x.c1 with ⟨b1, hb1⟩
  cases b0 <;> simp [field.QM31.is_zero, hb0, hb1]

/-! ## Raw generated-call characterizations -/

theorem extracted_m31_is_zero_raw (x : field.M31) :
    field.M31.is_zero x = ok true ↔ x.val = 0 := by
  simp [field.M31.is_zero, u32EqZeroIff]

theorem extracted_cm31_is_zero_raw (x : field.CM31) :
    field.CM31.is_zero x = ok true ↔
      x.a.val = 0 ∧ x.b.val = 0 := by
  by_cases ha : x.a.val = 0 <;> by_cases hb : x.b.val = 0 <;>
    simp [field.CM31.is_zero, field.M31.is_zero,
      ha, hb, u32EqZeroIff]

theorem extracted_qm31_is_zero_raw (x : field.QM31) :
    field.QM31.is_zero x = ok true ↔
      x.c0.a.val = 0 ∧ x.c0.b.val = 0 ∧
      x.c1.a.val = 0 ∧ x.c1.b.val = 0 := by
  by_cases h00 : x.c0.a.val = 0 <;>
    by_cases h01 : x.c0.b.val = 0 <;>
    by_cases h10 : x.c1.a.val = 0 <;>
    by_cases h11 : x.c1.b.val = 0 <;>
    simp [field.QM31.is_zero, field.CM31.is_zero,
      field.M31.is_zero, h00, h01, h10, h11, u32EqZeroIff]

/-! ## Exact-field capstones -/

/-- For every canonical M31 limb, the actual generated call succeeds and its
Boolean is true exactly when the represented field value is zero. -/
theorem extracted_m31_is_zero_corresponds
    (x : field.M31) (hx : CanonicalRawM31 x.val) :
    ∃ b : Bool,
      field.M31.is_zero x = ok b ∧
      (b = true ↔ (x.val : M31Exact) = 0) := by
  have hiff : field.M31.is_zero x = ok true ↔
      (x.val : M31Exact) = 0 :=
    (extracted_m31_is_zero_raw x).trans
      (canonicalNatCastEqZero x.val hx).symm
  obtain ⟨b, hb⟩ := m31IsZeroSucceeds x
  refine ⟨b, hb, ?_⟩
  have hbeq : b = true ↔ field.M31.is_zero x = ok true := by
    rw [hb]
    simp
  exact hbeq.trans hiff

/-- For every canonical CM31 pair, the actual generated short-circuit call
succeeds and reports zero exactly in the exact quadratic field. -/
theorem extracted_cm31_is_zero_corresponds
    (x : field.CM31) (hx : CanonicalCM31 x) :
    ∃ b : Bool,
      field.CM31.is_zero x = ok b ∧
      (b = true ↔ cm31ToExact x = 0) := by
  have hiff : field.CM31.is_zero x = ok true ↔
      cm31ToExact x = 0 :=
    (extracted_cm31_is_zero_raw x).trans (cm31ExactEqZero x hx).symm
  obtain ⟨b, hb⟩ := cm31IsZeroSucceeds x
  refine ⟨b, hb, ?_⟩
  have hbeq : b = true ↔ field.CM31.is_zero x = ok true := by
    rw [hb]
    simp
  exact hbeq.trans hiff

/-- For every canonical QM31 value, the actual generated nested
short-circuit call succeeds and reports zero exactly in the shared nested
tower. -/
theorem extracted_qm31_is_zero_corresponds
    (x : field.QM31) (hx : CanonicalQM31 x) :
    ∃ b : Bool,
      field.QM31.is_zero x = ok b ∧
      (b = true ↔ qm31ToExact x = 0) := by
  have hiff : field.QM31.is_zero x = ok true ↔
      qm31ToExact x = 0 :=
    (extracted_qm31_is_zero_raw x).trans (qm31ExactEqZero x hx).symm
  obtain ⟨b, hb⟩ := qm31IsZeroSucceeds x
  refine ⟨b, hb, ?_⟩
  have hbeq : b = true ↔ field.QM31.is_zero x = ok true := by
    rw [hb]
    simp
  exact hbeq.trans hiff

/-! ## Concrete teeth and non-vacuity -/

/-- Zero is accepted at every tower level, while placing one in any limb is
rejected.  The individual CM31 and QM31 coordinates exercise both arms of the
generated short-circuit conjunctions. -/
theorem extracted_is_zero_positive_negative_teeth :
    field.M31.is_zero 0#u32 = ok true ∧
    field.M31.is_zero 1#u32 = ok false ∧
    field.CM31.is_zero ⟨0#u32, 0#u32⟩ = ok true ∧
    field.CM31.is_zero ⟨1#u32, 0#u32⟩ = ok false ∧
    field.CM31.is_zero ⟨0#u32, 1#u32⟩ = ok false ∧
    field.QM31.is_zero ⟨⟨0#u32, 0#u32⟩, ⟨0#u32, 0#u32⟩⟩ = ok true ∧
    field.QM31.is_zero ⟨⟨1#u32, 0#u32⟩, ⟨0#u32, 0#u32⟩⟩ = ok false ∧
    field.QM31.is_zero ⟨⟨0#u32, 1#u32⟩, ⟨0#u32, 0#u32⟩⟩ = ok false ∧
    field.QM31.is_zero ⟨⟨0#u32, 0#u32⟩, ⟨1#u32, 0#u32⟩⟩ = ok false ∧
    field.QM31.is_zero ⟨⟨0#u32, 0#u32⟩, ⟨0#u32, 1#u32⟩⟩ = ok false := by
  norm_num [field.QM31.is_zero, field.CM31.is_zero, field.M31.is_zero]

theorem canonical_is_zero_domains_nonempty :
    (∃ x : field.M31, CanonicalRawM31 x.val) ∧
    (∃ x : field.CM31, CanonicalCM31 x) ∧
    (∃ x : field.QM31, CanonicalQM31 x) := by
  constructor
  · exact ⟨0#u32, by norm_num [CanonicalRawM31, m31Modulus]⟩
  constructor
  · exact ⟨⟨0#u32, 0#u32⟩,
      by norm_num [CanonicalCM31, CanonicalRawM31, m31Modulus]⟩
  · exact ⟨⟨⟨0#u32, 0#u32⟩, ⟨0#u32, 0#u32⟩⟩,
      by norm_num [CanonicalQM31, CanonicalCM31,
        CanonicalRawM31, m31Modulus]⟩

#print axioms extracted_m31_is_zero_raw
#print axioms extracted_cm31_is_zero_raw
#print axioms extracted_qm31_is_zero_raw
#print axioms extracted_m31_is_zero_corresponds
#print axioms extracted_cm31_is_zero_corresponds
#print axioms extracted_qm31_is_zero_corresponds
#print axioms extracted_is_zero_positive_negative_teeth
#print axioms canonical_is_zero_domains_nonempty

end AspisAeneasIsZero
