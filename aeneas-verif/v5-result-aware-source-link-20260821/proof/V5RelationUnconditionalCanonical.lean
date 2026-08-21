import V5RelationGeneratedFieldProjection

/-!
# Representation bounds for generated field multiplication

Multiplication in the production M31 implementation always finishes with the
checked `reduce_u64` routine.  Its output is therefore canonical even when a
caller supplies an arbitrary raw `u32` representation.  This weaker fact is
enough to prove that successful terminal dot products return canonical field
representatives without first assigning mathematical meaning to every stored
weight.
-/

namespace AspisV5RelationUnconditionalCanonical

open Aeneas Aeneas.Std Result

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev RawM31 := V5RelationFullGenerated.aspis_core.field.M31
abbrev RawCM31 := V5RelationFullGenerated.aspis_core.field.CM31
abbrev RawQM31 := V5RelationFullGenerated.aspis_core.field.QM31

abbrev CanonicalM31 := AspisAeneasCM31Multiplicative.CanonicalRawM31
abbrev CanonicalCM31 :=
  AspisV5RelationGeneratedFieldProjection.CanonicalCM31
abbrev CanonicalQM31 :=
  AspisV5RelationGeneratedFieldProjection.CanonicalQM31

private theorem generated_P_eq_reference :
    V5RelationFullGenerated.aspis_core.field.P =
      aspis_core.field.P := by
  apply UScalar.eq_of_val_eq
  unfold V5RelationFullGenerated.aspis_core.field.P
    aspis_core.field.P
  rfl

private theorem generated_P_eq_cm_reference :
    V5RelationFullGenerated.aspis_core.field.P =
      AspisCoreCM31Multiplicative.field.P := by
  apply UScalar.eq_of_val_eq
  unfold V5RelationFullGenerated.aspis_core.field.P
    AspisCoreCM31Multiplicative.field.P
  rfl

private theorem generated_reduce_u64_eq_reference (x : Std.U64) :
    V5RelationFullGenerated.aspis_core.field.reduce_u64 x =
      aspis_core.field.reduce_u64 x := by
  unfold V5RelationFullGenerated.aspis_core.field.reduce_u64
    aspis_core.field.reduce_u64
  rw [generated_P_eq_reference]

private theorem generated_m31_add_eq_reference (x y : RawM31) :
    V5RelationFullGenerated.aspis_core.field.M31.add x y =
      AspisCoreCM31Multiplicative.field.M31.add x y := by
  unfold V5RelationFullGenerated.aspis_core.field.M31.add
    AspisCoreCM31Multiplicative.field.M31.add
  rw [generated_P_eq_cm_reference]

private theorem generated_m31_sub_eq_reference (x y : RawM31) :
    V5RelationFullGenerated.aspis_core.field.M31.sub x y =
      AspisCoreCM31Multiplicative.field.M31.sub x y := by
  unfold V5RelationFullGenerated.aspis_core.field.M31.sub
    AspisCoreCM31Multiplicative.field.M31.sub
  rw [generated_P_eq_cm_reference]

/-- A successful generated base-field multiplication is canonical for all raw
`u32` inputs; the statement intentionally makes no exact-value claim. -/
theorem generated_m31_mul_success_canonical_any
    (x y out : RawM31)
    (run : V5RelationFullGenerated.aspis_core.field.M31.mul x y = .ok out) :
    CanonicalM31 out.val := by
  let product :=
    Std.U64.wrapping_mul (UScalar.cast .U64 x) (UScalar.cast .U64 y)
  obtain ⟨expected, referenceRun, _, expectedCanonical, _⟩ :=
    AspisAeneasM31ReduceU64.extracted_reduce_u64_corresponds product
  have generatedRun :
      V5RelationFullGenerated.aspis_core.field.reduce_u64 product =
        .ok expected := by
    rw [generated_reduce_u64_eq_reference]
    exact referenceRun
  unfold V5RelationFullGenerated.aspis_core.field.M31.mul at run
  simp only [Aeneas.Std.lift, bind_tc_ok] at run
  dsimp [product] at generatedRun
  rw [generatedRun] at run
  simp only [Aeneas.Std.lift, bind_tc_ok, Result.ok.injEq] at run
  subst out
  exact expectedCanonical

private theorem generated_m31_mul_exists_canonical_any (x y : RawM31) :
    ∃ out, V5RelationFullGenerated.aspis_core.field.M31.mul x y = .ok out ∧
      CanonicalM31 out.val := by
  let product :=
    Std.U64.wrapping_mul (UScalar.cast .U64 x) (UScalar.cast .U64 y)
  obtain ⟨out, referenceRun, _, canonical, _⟩ :=
    AspisAeneasM31ReduceU64.extracted_reduce_u64_corresponds product
  refine ⟨out, ?_, canonical⟩
  unfold V5RelationFullGenerated.aspis_core.field.M31.mul
  simp only [Aeneas.Std.lift, bind_tc_ok]
  dsimp [product] at referenceRun ⊢
  rw [generated_reduce_u64_eq_reference]
  rw [referenceRun]
  rfl

private theorem generated_m31_add_exists (x y : RawM31) :
    ∃ out, V5RelationFullGenerated.aspis_core.field.M31.add x y = .ok out := by
  unfold V5RelationFullGenerated.aspis_core.field.M31.add
  simp only [Aeneas.Std.lift, bind_tc_ok]
  split
  · exact ⟨Std.U32.wrapping_sub (Std.U32.wrapping_add x y)
      V5RelationFullGenerated.aspis_core.field.P, rfl⟩
  · exact ⟨Std.U32.wrapping_add x y, rfl⟩

private theorem generated_m31_sub_exists (x y : RawM31) :
    ∃ out, V5RelationFullGenerated.aspis_core.field.M31.sub x y = .ok out := by
  unfold V5RelationFullGenerated.aspis_core.field.M31.sub
  simp only [Aeneas.Std.lift, bind_tc_ok]
  split
  · exact ⟨Std.U32.wrapping_sub
      (Std.U32.wrapping_sub
        (Std.U32.wrapping_add x
          V5RelationFullGenerated.aspis_core.field.P) y)
      V5RelationFullGenerated.aspis_core.field.P, rfl⟩
  · exact ⟨Std.U32.wrapping_sub
      (Std.U32.wrapping_add x
        V5RelationFullGenerated.aspis_core.field.P) y, rfl⟩

private theorem generated_m31_add_success_canonical
    (x y out : RawM31) (hx : CanonicalM31 x.val)
    (hy : CanonicalM31 y.val)
    (run : V5RelationFullGenerated.aspis_core.field.M31.add x y = .ok out) :
    CanonicalM31 out.val := by
  obtain ⟨expected, referenceRun, expectedCanonical, _⟩ :=
    AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds x y hx hy
  have generatedRun :
      V5RelationFullGenerated.aspis_core.field.M31.add x y = .ok expected := by
    rw [generated_m31_add_eq_reference]
    exact referenceRun
  rw [generatedRun] at run
  cases run
  exact expectedCanonical

private theorem generated_m31_add_exists_canonical
    (x y : RawM31) (hx : CanonicalM31 x.val)
    (hy : CanonicalM31 y.val) :
    ∃ out, V5RelationFullGenerated.aspis_core.field.M31.add x y = .ok out ∧
      CanonicalM31 out.val := by
  obtain ⟨out, referenceRun, canonical, _⟩ :=
    AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds x y hx hy
  exact ⟨out, generated_m31_add_eq_reference x y ▸ referenceRun,
    canonical⟩

private theorem generated_m31_sub_success_canonical
    (x y out : RawM31) (hx : CanonicalM31 x.val)
    (hy : CanonicalM31 y.val)
    (run : V5RelationFullGenerated.aspis_core.field.M31.sub x y = .ok out) :
    CanonicalM31 out.val := by
  obtain ⟨expected, referenceRun, expectedCanonical, _⟩ :=
    AspisAeneasCM31Multiplicative.extracted_m31_sub_corresponds x y hx hy
  have generatedRun :
      V5RelationFullGenerated.aspis_core.field.M31.sub x y = .ok expected := by
    rw [generated_m31_sub_eq_reference]
    exact referenceRun
  rw [generatedRun] at run
  cases run
  exact expectedCanonical

private theorem generated_m31_sub_exists_canonical
    (x y : RawM31) (hx : CanonicalM31 x.val)
    (hy : CanonicalM31 y.val) :
    ∃ out, V5RelationFullGenerated.aspis_core.field.M31.sub x y = .ok out ∧
      CanonicalM31 out.val := by
  obtain ⟨out, referenceRun, canonical, _⟩ :=
    AspisAeneasCM31Multiplicative.extracted_m31_sub_corresponds x y hx hy
  exact ⟨out, generated_m31_sub_eq_reference x y ▸ referenceRun,
    canonical⟩

private theorem generated_cm31_add_exists (x y : RawCM31) :
    ∃ out, V5RelationFullGenerated.aspis_core.field.CM31.add x y = .ok out := by
  obtain ⟨a, ha⟩ := generated_m31_add_exists x.a y.a
  obtain ⟨b, hb⟩ := generated_m31_add_exists x.b y.b
  exact ⟨{ a := a, b := b }, by
    simp [V5RelationFullGenerated.aspis_core.field.CM31.add, ha, hb]⟩

private theorem generated_cm31_add_exists_canonical
    (x y : RawCM31) (hx : CanonicalCM31 x) (hy : CanonicalCM31 y) :
    ∃ out, V5RelationFullGenerated.aspis_core.field.CM31.add x y = .ok out ∧
      CanonicalCM31 out := by
  obtain ⟨a, ha, hca⟩ :=
    generated_m31_add_exists_canonical x.a y.a hx.1 hy.1
  obtain ⟨b, hb, hcb⟩ :=
    generated_m31_add_exists_canonical x.b y.b hx.2 hy.2
  exact ⟨{ a := a, b := b }, by
    simp [V5RelationFullGenerated.aspis_core.field.CM31.add, ha, hb],
    ⟨hca, hcb⟩⟩

private theorem generated_cm31_sub_exists_canonical
    (x y : RawCM31) (hx : CanonicalCM31 x) (hy : CanonicalCM31 y) :
    ∃ out, V5RelationFullGenerated.aspis_core.field.CM31.sub x y = .ok out ∧
      CanonicalCM31 out := by
  obtain ⟨a, ha, hca⟩ :=
    generated_m31_sub_exists_canonical x.a y.a hx.1 hy.1
  obtain ⟨b, hb, hcb⟩ :=
    generated_m31_sub_exists_canonical x.b y.b hx.2 hy.2
  exact ⟨{ a := a, b := b }, by
    simp [V5RelationFullGenerated.aspis_core.field.CM31.sub, ha, hb],
    ⟨hca, hcb⟩⟩

/-- CM31 multiplication is output-canonical for arbitrary raw inputs because
all three base-field products are reduced before the final add/sub chain. -/
theorem generated_cm31_mul_exists_canonical_any (x y : RawCM31) :
    ∃ out, V5RelationFullGenerated.aspis_core.field.CM31.mul x y = .ok out ∧
      CanonicalCM31 out := by
  obtain ⟨m0, hm0, hcm0⟩ :=
    generated_m31_mul_exists_canonical_any x.a y.a
  obtain ⟨m1, hm1, hcm1⟩ :=
    generated_m31_mul_exists_canonical_any x.b y.b
  obtain ⟨xsum, hxsum⟩ := generated_m31_add_exists x.a x.b
  obtain ⟨ysum, hysum⟩ := generated_m31_add_exists y.a y.b
  obtain ⟨m2, hm2, hcm2⟩ :=
    generated_m31_mul_exists_canonical_any xsum ysum
  obtain ⟨real, hreal, hcreal⟩ :=
    generated_m31_sub_exists_canonical m0 m1 hcm0 hcm1
  obtain ⟨cross0, hcross0, hccross0⟩ :=
    generated_m31_sub_exists_canonical m2 m0 hcm2 hcm0
  obtain ⟨imag, himag, hcimag⟩ :=
    generated_m31_sub_exists_canonical cross0 m1 hccross0 hcm1
  exact ⟨{ a := real, b := imag }, by
    simp [V5RelationFullGenerated.aspis_core.field.CM31.mul, hm0, hm1,
      hxsum, hysum, hm2, hreal, hcross0, himag], ⟨hcreal, hcimag⟩⟩

private theorem generated_mul_by_r_exists_canonical
    (x : RawCM31) (hx : CanonicalCM31 x) :
    ∃ out, V5RelationFullGenerated.aspis_core.field.mul_by_r x = .ok out ∧
      CanonicalCM31 out := by
  obtain ⟨twoA, htwoA, hctwoA⟩ :=
    generated_m31_add_exists_canonical x.a x.a hx.1 hx.1
  obtain ⟨real, hreal, hcreal⟩ :=
    generated_m31_sub_exists_canonical twoA x.b hctwoA hx.2
  obtain ⟨twoB, htwoB, hctwoB⟩ :=
    generated_m31_add_exists_canonical x.b x.b hx.2 hx.2
  obtain ⟨imag, himag, hcimag⟩ :=
    generated_m31_add_exists_canonical x.a twoB hx.1 hctwoB
  exact ⟨{ a := real, b := imag }, by
    simp [V5RelationFullGenerated.aspis_core.field.mul_by_r,
      V5RelationFullGenerated.aspis_core.field.M31.double,
      htwoA, hreal, htwoB, himag], ⟨hcreal, hcimag⟩⟩

/-- A generated QM31 multiplication always returns a canonical four-limb
representative, independently of the raw representatives supplied to it. -/
theorem generated_qm31_mul_exists_canonical_any (x y : RawQM31) :
    ∃ out, V5RelationFullGenerated.aspis_core.field.QM31.mul x y = .ok out ∧
      CanonicalQM31 out := by
  obtain ⟨m0, hm0, hcm0⟩ :=
    generated_cm31_mul_exists_canonical_any x.c0 y.c0
  obtain ⟨m1, hm1, hcm1⟩ :=
    generated_cm31_mul_exists_canonical_any x.c1 y.c1
  obtain ⟨xsum, hxsum⟩ := generated_cm31_add_exists x.c0 x.c1
  obtain ⟨ysum, hysum⟩ := generated_cm31_add_exists y.c0 y.c1
  obtain ⟨m2, hm2, hcm2⟩ :=
    generated_cm31_mul_exists_canonical_any xsum ysum
  obtain ⟨rotated, hrotated, hcrotated⟩ :=
    generated_mul_by_r_exists_canonical m1 hcm1
  obtain ⟨real, hreal, hcreal⟩ :=
    generated_cm31_add_exists_canonical m0 rotated hcm0 hcrotated
  obtain ⟨cross0, hcross0, hccross0⟩ :=
    generated_cm31_sub_exists_canonical m2 m0 hcm2 hcm0
  obtain ⟨imag, himag, hcimag⟩ :=
    generated_cm31_sub_exists_canonical cross0 m1 hccross0 hcm1
  exact ⟨{ c0 := real, c1 := imag }, by
    simp [V5RelationFullGenerated.aspis_core.field.QM31.mul, hm0, hm1,
      hxsum, hysum, hm2, hrotated, hreal, hcross0, himag],
    ⟨hcreal, hcimag⟩⟩

theorem generated_qm31_mul_success_canonical_any
    (x y out : RawQM31)
    (run : V5RelationFullGenerated.aspis_core.field.QM31.mul x y = .ok out) :
    CanonicalQM31 out := by
  obtain ⟨expected, expectedRun, expectedCanonical⟩ :=
    generated_qm31_mul_exists_canonical_any x y
  rw [expectedRun] at run
  cases run
  exact expectedCanonical

theorem generated_qm31_add_success_canonical
    (x y out : RawQM31) (hx : CanonicalQM31 x) (hy : CanonicalQM31 y)
    (run : V5RelationFullGenerated.aspis_core.field.QM31.add x y = .ok out) :
    CanonicalQM31 out :=
  (AspisV5RelationGeneratedFieldProjection.generated_qm31_add_run_corresponds
    x y out hx hy run).1

private theorem generated_cm31_square_exists_canonical_any (x : RawCM31) :
    ∃ out, V5RelationFullGenerated.aspis_core.field.CM31.square x = .ok out ∧
      CanonicalCM31 out := by
  obtain ⟨sum, hsum⟩ := generated_m31_add_exists x.a x.b
  obtain ⟨difference, hdifference⟩ := generated_m31_sub_exists x.a x.b
  obtain ⟨real, hreal, hcreal⟩ :=
    generated_m31_mul_exists_canonical_any sum difference
  obtain ⟨product, hproduct, hcproduct⟩ :=
    generated_m31_mul_exists_canonical_any x.a x.b
  obtain ⟨imag, himag, hcimag⟩ :=
    generated_m31_add_exists_canonical product product hcproduct hcproduct
  exact ⟨{ a := real, b := imag }, by
    simp [V5RelationFullGenerated.aspis_core.field.CM31.square,
      V5RelationFullGenerated.aspis_core.field.M31.double, hsum,
      hdifference, hreal, hproduct, himag], ⟨hcreal, hcimag⟩⟩

theorem generated_qm31_square_exists_canonical_any (x : RawQM31) :
    ∃ out, V5RelationFullGenerated.aspis_core.field.QM31.square x = .ok out ∧
      CanonicalQM31 out := by
  obtain ⟨c0Square, hc0Square, hcc0Square⟩ :=
    generated_cm31_square_exists_canonical_any x.c0
  obtain ⟨c1Square, hc1Square, hcc1Square⟩ :=
    generated_cm31_square_exists_canonical_any x.c1
  obtain ⟨rotated, hrotated, hcrotated⟩ :=
    generated_mul_by_r_exists_canonical c1Square hcc1Square
  obtain ⟨real, hreal, hcreal⟩ :=
    generated_cm31_add_exists_canonical c0Square rotated hcc0Square hcrotated
  obtain ⟨cross, hcross, hccross⟩ :=
    generated_cm31_mul_exists_canonical_any x.c0 x.c1
  obtain ⟨imag, himag, hcimag⟩ :=
    generated_cm31_add_exists_canonical cross cross hccross hccross
  exact ⟨{ c0 := real, c1 := imag }, by
    simp [V5RelationFullGenerated.aspis_core.field.QM31.square,
      V5RelationFullGenerated.aspis_core.field.CM31.double, hc0Square,
      hc1Square, hrotated, hreal, hcross, himag], ⟨hcreal, hcimag⟩⟩

theorem generated_qm31_square_success_canonical_any
    (x out : RawQM31)
    (run : V5RelationFullGenerated.aspis_core.field.QM31.square x = .ok out) :
    CanonicalQM31 out := by
  obtain ⟨expected, expectedRun, expectedCanonical⟩ :=
    generated_qm31_square_exists_canonical_any x
  rw [expectedRun] at run
  cases run
  exact expectedCanonical

private theorem linked_P_eq_generated :
    V5RelationLinkedGenerated.aspis_core.field.P =
      V5RelationFullGenerated.aspis_core.field.P := by
  apply UScalar.eq_of_val_eq
  unfold V5RelationLinkedGenerated.aspis_core.field.P
    V5RelationFullGenerated.aspis_core.field.P
  rfl

private theorem linked_reduce_u64_eq_generated (x : Std.U64) :
    V5RelationLinkedGenerated.aspis_core.field.reduce_u64 x =
      V5RelationFullGenerated.aspis_core.field.reduce_u64 x := by
  unfold V5RelationLinkedGenerated.aspis_core.field.reduce_u64
    V5RelationFullGenerated.aspis_core.field.reduce_u64
  rw [linked_P_eq_generated]

private theorem linked_m31_add_eq_generated (x y : RawM31) :
    V5RelationLinkedGenerated.aspis_core.field.M31.add x y =
      V5RelationFullGenerated.aspis_core.field.M31.add x y := by
  unfold V5RelationLinkedGenerated.aspis_core.field.M31.add
    V5RelationFullGenerated.aspis_core.field.M31.add
  rw [linked_P_eq_generated]

private theorem linked_m31_sub_eq_generated (x y : RawM31) :
    V5RelationLinkedGenerated.aspis_core.field.M31.sub x y =
      V5RelationFullGenerated.aspis_core.field.M31.sub x y := by
  unfold V5RelationLinkedGenerated.aspis_core.field.M31.sub
    V5RelationFullGenerated.aspis_core.field.M31.sub
  rw [linked_P_eq_generated]

private theorem linked_m31_mul_eq_generated (x y : RawM31) :
    V5RelationLinkedGenerated.aspis_core.field.M31.mul x y =
      V5RelationFullGenerated.aspis_core.field.M31.mul x y := by
  unfold V5RelationLinkedGenerated.aspis_core.field.M31.mul
    V5RelationFullGenerated.aspis_core.field.M31.mul
  simp only [Aeneas.Std.lift, bind_tc_ok]
  rw [linked_reduce_u64_eq_generated]

private theorem linked_cm31_add_eq_generated (x y : RawCM31) :
    V5RelationLinkedGenerated.aspis_core.field.CM31.add x y =
      V5RelationFullGenerated.aspis_core.field.CM31.add x y := by
  simp [V5RelationLinkedGenerated.aspis_core.field.CM31.add,
    V5RelationFullGenerated.aspis_core.field.CM31.add,
    linked_m31_add_eq_generated]

private theorem linked_cm31_sub_eq_generated (x y : RawCM31) :
    V5RelationLinkedGenerated.aspis_core.field.CM31.sub x y =
      V5RelationFullGenerated.aspis_core.field.CM31.sub x y := by
  simp [V5RelationLinkedGenerated.aspis_core.field.CM31.sub,
    V5RelationFullGenerated.aspis_core.field.CM31.sub,
    linked_m31_sub_eq_generated]

private theorem linked_cm31_mul_eq_generated (x y : RawCM31) :
    V5RelationLinkedGenerated.aspis_core.field.CM31.mul x y =
      V5RelationFullGenerated.aspis_core.field.CM31.mul x y := by
  simp [V5RelationLinkedGenerated.aspis_core.field.CM31.mul,
    V5RelationFullGenerated.aspis_core.field.CM31.mul,
    linked_m31_add_eq_generated, linked_m31_sub_eq_generated,
    linked_m31_mul_eq_generated]

private theorem linked_cm31_square_eq_generated (x : RawCM31) :
    V5RelationLinkedGenerated.aspis_core.field.CM31.square x =
      V5RelationFullGenerated.aspis_core.field.CM31.square x := by
  simp [V5RelationLinkedGenerated.aspis_core.field.CM31.square,
    V5RelationFullGenerated.aspis_core.field.CM31.square,
    V5RelationLinkedGenerated.aspis_core.field.M31.double,
    V5RelationFullGenerated.aspis_core.field.M31.double,
    linked_m31_add_eq_generated, linked_m31_sub_eq_generated,
    linked_m31_mul_eq_generated]

private theorem linked_mul_by_r_eq_generated (x : RawCM31) :
    V5RelationLinkedGenerated.aspis_core.field.mul_by_r x =
      V5RelationFullGenerated.aspis_core.field.mul_by_r x := by
  simp [V5RelationLinkedGenerated.aspis_core.field.mul_by_r,
    V5RelationFullGenerated.aspis_core.field.mul_by_r,
    V5RelationLinkedGenerated.aspis_core.field.M31.double,
    V5RelationFullGenerated.aspis_core.field.M31.double,
    linked_m31_add_eq_generated, linked_m31_sub_eq_generated]

private theorem linked_qm31_mul_eq_generated (x y : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.field.QM31.mul x y =
      V5RelationFullGenerated.aspis_core.field.QM31.mul x y := by
  simp [V5RelationLinkedGenerated.aspis_core.field.QM31.mul,
    V5RelationFullGenerated.aspis_core.field.QM31.mul,
    linked_cm31_add_eq_generated, linked_cm31_sub_eq_generated,
    linked_cm31_mul_eq_generated, linked_mul_by_r_eq_generated]

private theorem linked_qm31_add_eq_generated (x y : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.field.QM31.add x y =
      V5RelationFullGenerated.aspis_core.field.QM31.add x y := by
  simp [V5RelationLinkedGenerated.aspis_core.field.QM31.add,
    V5RelationFullGenerated.aspis_core.field.QM31.add,
    linked_cm31_add_eq_generated]

private theorem linked_qm31_square_eq_generated (x : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.field.QM31.square x =
      V5RelationFullGenerated.aspis_core.field.QM31.square x := by
  simp [V5RelationLinkedGenerated.aspis_core.field.QM31.square,
    V5RelationFullGenerated.aspis_core.field.QM31.square,
    V5RelationLinkedGenerated.aspis_core.field.CM31.double,
    V5RelationFullGenerated.aspis_core.field.CM31.double,
    linked_cm31_add_eq_generated, linked_cm31_mul_eq_generated,
    linked_cm31_square_eq_generated, linked_mul_by_r_eq_generated]

/-- Success-directed output bounds for the linked extraction used by the
actual `WeightAccumulator.dot` call. -/
theorem linked_qm31_mul_exists_canonical_any (x y : RawQM31) :
    ∃ out, V5RelationLinkedGenerated.aspis_core.field.QM31.mul x y = .ok out ∧
      CanonicalQM31 out := by
  obtain ⟨out, run, canonical⟩ :=
    generated_qm31_mul_exists_canonical_any x y
  exact ⟨out, linked_qm31_mul_eq_generated x y ▸ run, canonical⟩

theorem linked_qm31_square_exists_canonical_any (x : RawQM31) :
    ∃ out, V5RelationLinkedGenerated.aspis_core.field.QM31.square x = .ok out ∧
      CanonicalQM31 out := by
  obtain ⟨out, run, canonical⟩ :=
    generated_qm31_square_exists_canonical_any x
  exact ⟨out, linked_qm31_square_eq_generated x ▸ run, canonical⟩

theorem linked_qm31_add_exists_canonical
    (x y : RawQM31) (hx : CanonicalQM31 x) (hy : CanonicalQM31 y) :
    ∃ out, V5RelationLinkedGenerated.aspis_core.field.QM31.add x y = .ok out ∧
      CanonicalQM31 out := by
  obtain ⟨out, run, canonical, _⟩ :=
    AspisV5RelationGeneratedFieldProjection.generated_qm31_add_corresponds
      x y hx hy
  exact ⟨out, linked_qm31_add_eq_generated x y ▸ run, canonical⟩

theorem linked_qm31_sub_exists_canonical
    (x y : RawQM31) (hx : CanonicalQM31 x) (hy : CanonicalQM31 y) :
    ∃ out, V5RelationLinkedGenerated.aspis_core.field.QM31.sub x y = .ok out ∧
      CanonicalQM31 out := by
  obtain ⟨c0, hc0, hcc0⟩ :=
    generated_cm31_sub_exists_canonical x.c0 y.c0 hx.1 hy.1
  obtain ⟨c1, hc1, hcc1⟩ :=
    generated_cm31_sub_exists_canonical x.c1 y.c1 hx.2 hy.2
  exact ⟨{ c0 := c0, c1 := c1 }, by
    simp [V5RelationLinkedGenerated.aspis_core.field.QM31.sub,
      linked_cm31_sub_eq_generated, hc0, hc1], ⟨hcc0, hcc1⟩⟩

theorem linked_qm31_mul_success_canonical_any
    (x y out : RawQM31)
    (run : V5RelationLinkedGenerated.aspis_core.field.QM31.mul x y = .ok out) :
    CanonicalQM31 out := by
  rw [linked_qm31_mul_eq_generated] at run
  exact generated_qm31_mul_success_canonical_any x y out run

theorem linked_qm31_square_success_canonical_any
    (x out : RawQM31)
    (run : V5RelationLinkedGenerated.aspis_core.field.QM31.square x = .ok out) :
    CanonicalQM31 out := by
  rw [linked_qm31_square_eq_generated] at run
  exact generated_qm31_square_success_canonical_any x out run

theorem linked_qm31_add_success_canonical
    (x y out : RawQM31) (hx : CanonicalQM31 x) (hy : CanonicalQM31 y)
    (run : V5RelationLinkedGenerated.aspis_core.field.QM31.add x y = .ok out) :
    CanonicalQM31 out := by
  rw [linked_qm31_add_eq_generated] at run
  exact generated_qm31_add_success_canonical x y out hx hy run

theorem linked_qm31_sub_success_canonical
    (x y out : RawQM31) (hx : CanonicalQM31 x) (hy : CanonicalQM31 y)
    (run : V5RelationLinkedGenerated.aspis_core.field.QM31.sub x y = .ok out) :
    CanonicalQM31 out := by
  obtain ⟨expected, expectedRun, expectedCanonical⟩ :=
    linked_qm31_sub_exists_canonical x y hx hy
  rw [expectedRun] at run
  cases run
  exact expectedCanonical

theorem generated_qm31_zero_canonical :
    CanonicalQM31 V5RelationFullGenerated.aspis_core.field.QM31.ZERO := by
  norm_num [V5RelationFullGenerated.aspis_core.field.QM31.ZERO,
    CanonicalQM31,
    AspisV5RelationGeneratedFieldProjection.CanonicalQM31,
    AspisV5RelationGeneratedFieldProjection.CanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus]

#print axioms generated_m31_mul_success_canonical_any
#print axioms generated_qm31_mul_success_canonical_any
#print axioms generated_qm31_square_success_canonical_any
#print axioms linked_qm31_mul_success_canonical_any
#print axioms linked_qm31_square_success_canonical_any

end AspisV5RelationUnconditionalCanonical
