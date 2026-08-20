import RelationLinked.Funs
import ComponentBEvaluatorFieldBridge
import AspisFormal.V5ComponentCQM31TowerExact

/-!
# Exact field projection for the generated V5 relation verifier

The complete relation-driver extraction owns fresh generated CM31/QM31 record
types.  This file transports those records to the already checked production
field extraction and then into the maintained exact QM31 tower.  The transport
is structural: the four `u32` limbs remain in `(c0.a,c0.b,c1.a,c1.b)` order.

This removes scalar `add`, `mul`, and optimized `square` from the remaining
relation-verifier boundary.  Canonicality is explicit because the Rust field
operations are specified only on canonical M31 representatives.
-/

namespace AspisV5RelationLinkedFieldProjection

open Aeneas Aeneas.Std Result

abbrev NewM31 := V5RelationLinkedGenerated.aspis_core.field.M31
abbrev NewCM31 := V5RelationLinkedGenerated.aspis_core.field.CM31
abbrev NewQM31 := V5RelationLinkedGenerated.aspis_core.field.QM31

abbrev OldCM31 := ComponentBGenerated.aspis_core.field.CM31
abbrev OldQM31 := ComponentBGenerated.aspis_core.field.QM31

def toOldCM31 (x : NewCM31) : OldCM31 := ⟨x.a, x.b⟩
def fromOldCM31 (x : OldCM31) : NewCM31 := ⟨x.a, x.b⟩

def toOldQM31 (x : NewQM31) : OldQM31 :=
  ⟨toOldCM31 x.c0, toOldCM31 x.c1⟩

def fromOldQM31 (x : OldQM31) : NewQM31 :=
  ⟨fromOldCM31 x.c0, fromOldCM31 x.c1⟩

@[simp] theorem toOldCM31_fromOldCM31 (x : OldCM31) :
    toOldCM31 (fromOldCM31 x) = x := by cases x <;> rfl

@[simp] theorem fromOldCM31_toOldCM31 (x : NewCM31) :
    fromOldCM31 (toOldCM31 x) = x := by cases x <;> rfl

@[simp] theorem toOldQM31_fromOldQM31 (x : OldQM31) :
    toOldQM31 (fromOldQM31 x) = x := by cases x <;> rfl

@[simp] theorem fromOldQM31_toOldQM31 (x : NewQM31) :
    fromOldQM31 (toOldQM31 x) = x := by cases x <;> rfl

def CanonicalCM31 (x : NewCM31) : Prop :=
  AspisAeneasCM31Multiplicative.CanonicalRawM31 x.a.val ∧
    AspisAeneasCM31Multiplicative.CanonicalRawM31 x.b.val

def CanonicalQM31 (x : NewQM31) : Prop :=
  CanonicalCM31 x.c0 ∧ CanonicalCM31 x.c1

def toExact (x : NewQM31) : ComponentBRealEvaluatorProof.ExactQM31 :=
  ⟨⟨x.c0.a.val, x.c0.b.val⟩, ⟨x.c1.a.val, x.c1.b.val⟩⟩

/-- The coordinate interpretation in the maintained V5 tower.  The old field
proof and the maintained tower use the same modulus, `i² = -1`, non-residue
`2+i`, and limb order; this spelling makes that release-facing target explicit.
-/
def toMaintainedExact (x : NewQM31) :
    AspisV5ComponentCQM31TowerExact.QM31Exact :=
  ⟨⟨x.c0.a.val, x.c0.b.val⟩, ⟨x.c1.a.val, x.c1.b.val⟩⟩

theorem canonical_toOld (x : NewQM31) :
    CanonicalQM31 x ↔
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 (toOldQM31 x) := by
  rfl

theorem toExact_eq_old (x : NewQM31) :
    toExact x = ComponentBRealEvaluatorProof.generatedQm31ToExact (toOldQM31 x) := by
  rfl

private theorem P_eq_old :
    V5RelationLinkedGenerated.aspis_core.field.P =
      ComponentBGenerated.aspis_core.field.P := by
  apply UScalar.eq_of_val_eq
  unfold V5RelationLinkedGenerated.aspis_core.field.P
    ComponentBGenerated.aspis_core.field.P
  rfl

private theorem reduce_u64_eq_old (x : Std.U64) :
    V5RelationLinkedGenerated.aspis_core.field.reduce_u64 x =
      ComponentBGenerated.aspis_core.field.reduce_u64 x := by
  unfold V5RelationLinkedGenerated.aspis_core.field.reduce_u64
    ComponentBGenerated.aspis_core.field.reduce_u64
  rw [P_eq_old]

private theorem m31_add_eq_old (a b : NewM31) :
    V5RelationLinkedGenerated.aspis_core.field.M31.add a b =
      ComponentBGenerated.aspis_core.field.M31.add a b := by
  unfold V5RelationLinkedGenerated.aspis_core.field.M31.add
    ComponentBGenerated.aspis_core.field.M31.add
  rw [P_eq_old]

private theorem m31_sub_eq_old (a b : NewM31) :
    V5RelationLinkedGenerated.aspis_core.field.M31.sub a b =
      ComponentBGenerated.aspis_core.field.M31.sub a b := by
  unfold V5RelationLinkedGenerated.aspis_core.field.M31.sub
    ComponentBGenerated.aspis_core.field.M31.sub
  rw [P_eq_old]

private theorem m31_mul_eq_old (a b : NewM31) :
    V5RelationLinkedGenerated.aspis_core.field.M31.mul a b =
      ComponentBGenerated.aspis_core.field.M31.mul a b := by
  unfold V5RelationLinkedGenerated.aspis_core.field.M31.mul
    ComponentBGenerated.aspis_core.field.M31.mul
  simp only [Aeneas.Std.lift, bind_tc_ok]
  rw [reduce_u64_eq_old]

private theorem P_eq_multiplicative :
    V5RelationLinkedGenerated.aspis_core.field.P =
      AspisCoreCM31Multiplicative.field.P := by
  apply UScalar.eq_of_val_eq
  unfold V5RelationLinkedGenerated.aspis_core.field.P
    AspisCoreCM31Multiplicative.field.P
  rfl

private theorem reduce_u64_eq_multiplicative (x : Std.U64) :
    V5RelationLinkedGenerated.aspis_core.field.reduce_u64 x =
      AspisCoreCM31Multiplicative.field.reduce_u64 x := by
  unfold V5RelationLinkedGenerated.aspis_core.field.reduce_u64
    AspisCoreCM31Multiplicative.field.reduce_u64
  rw [P_eq_multiplicative]

private theorem m31_mul_eq_multiplicative (a b : NewM31) :
    V5RelationLinkedGenerated.aspis_core.field.M31.mul a b =
      AspisCoreCM31Multiplicative.field.M31.mul a b := by
  unfold V5RelationLinkedGenerated.aspis_core.field.M31.mul
    AspisCoreCM31Multiplicative.field.M31.mul
  simp only [Aeneas.Std.lift, bind_tc_ok]
  rw [reduce_u64_eq_multiplicative]

private theorem m31_mul_corresponds
    (a b : NewM31)
    (ha : AspisAeneasCM31Multiplicative.CanonicalRawM31 a.val)
    (hb : AspisAeneasCM31Multiplicative.CanonicalRawM31 b.val) :
    ∃ out : NewM31,
      V5RelationLinkedGenerated.aspis_core.field.M31.mul a b = ok out ∧
      AspisAeneasCM31Multiplicative.CanonicalRawM31 out.val ∧
      ((out.val : Nat) : ComponentBRealEvaluatorProof.ExactM31) =
        (a.val : ComponentBRealEvaluatorProof.ExactM31) *
          (b.val : ComponentBRealEvaluatorProof.ExactM31) := by
  obtain ⟨out, oldRun, canonical, exact⟩ :=
    AspisAeneasCM31Multiplicative.extracted_m31_mul_corresponds a b ha hb
  refine ⟨out, ?_, canonical, exact⟩
  rw [m31_mul_eq_multiplicative]
  exact oldRun

private theorem cm31_add_transport (x y : NewCM31) :
    V5RelationLinkedGenerated.aspis_core.field.CM31.add x y =
      (do
        let out ← ComponentBGenerated.aspis_core.field.CM31.add
          (toOldCM31 x) (toOldCM31 y)
        ok (fromOldCM31 out)) := by
  simp [V5RelationLinkedGenerated.aspis_core.field.CM31.add,
    ComponentBGenerated.aspis_core.field.CM31.add,
    m31_add_eq_old, toOldCM31, fromOldCM31]

private theorem cm31_sub_transport (x y : NewCM31) :
    V5RelationLinkedGenerated.aspis_core.field.CM31.sub x y =
      (do
        let out ← ComponentBGenerated.aspis_core.field.CM31.sub
          (toOldCM31 x) (toOldCM31 y)
        ok (fromOldCM31 out)) := by
  simp [V5RelationLinkedGenerated.aspis_core.field.CM31.sub,
    ComponentBGenerated.aspis_core.field.CM31.sub,
    m31_sub_eq_old, toOldCM31, fromOldCM31]

private theorem cm31_mul_transport (x y : NewCM31) :
    V5RelationLinkedGenerated.aspis_core.field.CM31.mul x y =
      (do
        let out ← ComponentBGenerated.aspis_core.field.CM31.mul
          (toOldCM31 x) (toOldCM31 y)
        ok (fromOldCM31 out)) := by
  simp [V5RelationLinkedGenerated.aspis_core.field.CM31.mul,
    ComponentBGenerated.aspis_core.field.CM31.mul,
    m31_add_eq_old, m31_sub_eq_old, m31_mul_eq_old,
    toOldCM31, fromOldCM31]

private theorem cm31_square_transport (x : NewCM31) :
    V5RelationLinkedGenerated.aspis_core.field.CM31.square x =
      (do
        let out ← ComponentBGenerated.aspis_core.field.CM31.square
          (toOldCM31 x)
        ok (fromOldCM31 out)) := by
  simp [V5RelationLinkedGenerated.aspis_core.field.CM31.square,
    ComponentBGenerated.aspis_core.field.CM31.square,
    V5RelationLinkedGenerated.aspis_core.field.M31.double,
    ComponentBGenerated.aspis_core.field.M31.double,
    m31_add_eq_old, m31_sub_eq_old, m31_mul_eq_old,
    toOldCM31, fromOldCM31]

private theorem cm31_double_transport (x : NewCM31) :
    V5RelationLinkedGenerated.aspis_core.field.CM31.double x =
      (do
        let out ← ComponentBGenerated.aspis_core.field.CM31.double
          (toOldCM31 x)
        ok (fromOldCM31 out)) := by
  simp [V5RelationLinkedGenerated.aspis_core.field.CM31.double,
    ComponentBGenerated.aspis_core.field.CM31.double,
    cm31_add_transport]

private theorem mul_by_r_transport (x : NewCM31) :
    V5RelationLinkedGenerated.aspis_core.field.mul_by_r x =
      (do
        let out ← ComponentBGenerated.aspis_core.field.mul_by_r
          (toOldCM31 x)
        ok (fromOldCM31 out)) := by
  simp [V5RelationLinkedGenerated.aspis_core.field.mul_by_r,
    ComponentBGenerated.aspis_core.field.mul_by_r,
    V5RelationLinkedGenerated.aspis_core.field.M31.double,
    ComponentBGenerated.aspis_core.field.M31.double,
    m31_add_eq_old, m31_sub_eq_old, toOldCM31, fromOldCM31]

theorem qm31_add_transport (x y : NewQM31) :
    V5RelationLinkedGenerated.aspis_core.field.QM31.add x y =
      (do
        let out ← ComponentBGenerated.aspis_core.field.QM31.add
          (toOldQM31 x) (toOldQM31 y)
        ok (fromOldQM31 out)) := by
  simp [V5RelationLinkedGenerated.aspis_core.field.QM31.add,
    ComponentBGenerated.aspis_core.field.QM31.add,
    cm31_add_transport, toOldQM31, fromOldQM31]

theorem qm31_mul_transport (x y : NewQM31) :
    V5RelationLinkedGenerated.aspis_core.field.QM31.mul x y =
      (do
        let out ← ComponentBGenerated.aspis_core.field.QM31.mul
          (toOldQM31 x) (toOldQM31 y)
        ok (fromOldQM31 out)) := by
  simp [V5RelationLinkedGenerated.aspis_core.field.QM31.mul,
    ComponentBGenerated.aspis_core.field.QM31.mul,
    cm31_add_transport, cm31_sub_transport, cm31_mul_transport,
    mul_by_r_transport, toOldQM31, fromOldQM31]

theorem qm31_square_transport (x : NewQM31) :
    V5RelationLinkedGenerated.aspis_core.field.QM31.square x =
      (do
        let out ← ComponentBGenerated.aspis_core.field.QM31.square
          (toOldQM31 x)
        ok (fromOldQM31 out)) := by
  simp [V5RelationLinkedGenerated.aspis_core.field.QM31.square,
    ComponentBGenerated.aspis_core.field.QM31.square,
    ComponentBGenerated.aspis_core.field.CM31.double,
    cm31_add_transport, cm31_mul_transport, cm31_square_transport,
    cm31_double_transport, mul_by_r_transport, toOldQM31, fromOldQM31]

theorem generated_qm31_add_corresponds
    (x y : NewQM31) (hx : CanonicalQM31 x) (hy : CanonicalQM31 y) :
    ∃ out : NewQM31,
      V5RelationLinkedGenerated.aspis_core.field.QM31.add x y = ok out ∧
      CanonicalQM31 out ∧
      toExact out = toExact x + toExact y := by
  obtain ⟨oldOut, oldRun, oldCanonical, oldExact⟩ :=
    ComponentBRealEvaluatorProof.generated_qm31_add_corresponds
      (toOldQM31 x) (toOldQM31 y)
      ((canonical_toOld x).mp hx) ((canonical_toOld y).mp hy)
  refine ⟨fromOldQM31 oldOut, ?_, ?_, ?_⟩
  · rw [qm31_add_transport, oldRun]
    simp
  · exact (canonical_toOld _).mpr (by simpa using oldCanonical)
  · rw [toExact_eq_old, toExact_eq_old, toExact_eq_old]
    simpa using oldExact

theorem generated_qm31_mul_corresponds
    (x y : NewQM31) (hx : CanonicalQM31 x) (hy : CanonicalQM31 y) :
    ∃ out : NewQM31,
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul x y = ok out ∧
      CanonicalQM31 out ∧
      toExact out = toExact x * toExact y := by
  obtain ⟨oldOut, oldRun, oldCanonical, oldExact⟩ :=
    ComponentBRealEvaluatorProof.generated_qm31_mul_corresponds
      (toOldQM31 x) (toOldQM31 y)
      ((canonical_toOld x).mp hx) ((canonical_toOld y).mp hy)
  refine ⟨fromOldQM31 oldOut, ?_, ?_, ?_⟩
  · rw [qm31_mul_transport, oldRun]
    simp
  · exact (canonical_toOld _).mpr (by simpa using oldCanonical)
  · rw [toExact_eq_old, toExact_eq_old, toExact_eq_old]
    simpa using oldExact

theorem generated_qm31_square_corresponds
    (x : NewQM31) (hx : CanonicalQM31 x) :
    ∃ out : NewQM31,
      V5RelationLinkedGenerated.aspis_core.field.QM31.square x = ok out ∧
      CanonicalQM31 out ∧
      toExact out = toExact x ^ 2 := by
  obtain ⟨oldOut, oldRun, oldCanonical, oldExact⟩ :=
    ComponentBRealEvaluatorProof.generated_qm31_square_corresponds
      (toOldQM31 x) ((canonical_toOld x).mp hx)
  refine ⟨fromOldQM31 oldOut, ?_, ?_, ?_⟩
  · rw [qm31_square_transport, oldRun]
    simp
  · exact (canonical_toOld _).mpr (by simpa using oldCanonical)
  · rw [toExact_eq_old, toExact_eq_old]
    simpa using oldExact

/-- The specialized Rust multiplication by one M31 word also denotes
ordinary multiplication by the base-field embedding of that word. -/
theorem generated_qm31_mul_m31_corresponds
    (x : NewQM31) (rhs : NewM31) (hx : CanonicalQM31 x)
    (hrhs : AspisAeneasCM31Multiplicative.CanonicalRawM31 rhs.val) :
    ∃ out : NewQM31,
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul_m31 x rhs = ok out ∧
      CanonicalQM31 out ∧
      toExact out = toExact x * (rhs.val : ComponentBRealEvaluatorProof.ExactQM31) := by
  obtain ⟨o00, h00, c00, e00⟩ :=
    m31_mul_corresponds x.c0.a rhs hx.1.1 hrhs
  obtain ⟨o01, h01, c01, e01⟩ :=
    m31_mul_corresponds x.c0.b rhs hx.1.2 hrhs
  obtain ⟨o10, h10, c10, e10⟩ :=
    m31_mul_corresponds x.c1.a rhs hx.2.1 hrhs
  obtain ⟨o11, h11, c11, e11⟩ :=
    m31_mul_corresponds x.c1.b rhs hx.2.2 hrhs
  let out : NewQM31 := ⟨⟨o00, o01⟩, ⟨o10, o11⟩⟩
  refine ⟨out, ?_, ⟨⟨c00, c01⟩, ⟨c10, c11⟩⟩, ?_⟩
  · simp [V5RelationLinkedGenerated.aspis_core.field.QM31.mul_m31,
      V5RelationLinkedGenerated.aspis_core.field.CM31.mul_m31,
      h00, h01, h10, h11, out]
  · apply QuadraticAlgebra.ext
    · apply QuadraticAlgebra.ext
      · simpa [toExact] using e00
      · simpa [toExact] using e01
    · apply QuadraticAlgebra.ext
      · simpa [toExact] using e10
      · simpa [toExact] using e11

/-- Success-directed forms used when projecting an arbitrary accepted Rust
execution.  Determinism identifies the result returned by Rust with the
canonical exact result supplied by the operation theorem above. -/
theorem generated_qm31_add_run_corresponds
    (x y out : NewQM31) (hx : CanonicalQM31 x) (hy : CanonicalQM31 y)
    (run : V5RelationLinkedGenerated.aspis_core.field.QM31.add x y = ok out) :
    CanonicalQM31 out ∧ toExact out = toExact x + toExact y := by
  obtain ⟨expected, expectedRun, expectedCanonical, expectedExact⟩ :=
    generated_qm31_add_corresponds x y hx hy
  rw [run] at expectedRun
  cases expectedRun
  exact ⟨expectedCanonical, expectedExact⟩

theorem generated_qm31_mul_run_corresponds
    (x y out : NewQM31) (hx : CanonicalQM31 x) (hy : CanonicalQM31 y)
    (run : V5RelationLinkedGenerated.aspis_core.field.QM31.mul x y = ok out) :
    CanonicalQM31 out ∧ toExact out = toExact x * toExact y := by
  obtain ⟨expected, expectedRun, expectedCanonical, expectedExact⟩ :=
    generated_qm31_mul_corresponds x y hx hy
  rw [run] at expectedRun
  cases expectedRun
  exact ⟨expectedCanonical, expectedExact⟩

theorem generated_qm31_square_run_corresponds
    (x out : NewQM31) (hx : CanonicalQM31 x)
    (run : V5RelationLinkedGenerated.aspis_core.field.QM31.square x = ok out) :
    CanonicalQM31 out ∧ toExact out = toExact x ^ 2 := by
  obtain ⟨expected, expectedRun, expectedCanonical, expectedExact⟩ :=
    generated_qm31_square_corresponds x hx
  rw [run] at expectedRun
  cases expectedRun
  exact ⟨expectedCanonical, expectedExact⟩

theorem generated_qm31_mul_m31_run_corresponds
    (x out : NewQM31) (rhs : NewM31) (hx : CanonicalQM31 x)
    (hrhs : AspisAeneasCM31Multiplicative.CanonicalRawM31 rhs.val)
    (run : V5RelationLinkedGenerated.aspis_core.field.QM31.mul_m31 x rhs = ok out) :
    CanonicalQM31 out ∧
      toExact out = toExact x * (rhs.val : ComponentBRealEvaluatorProof.ExactQM31) := by
  obtain ⟨expected, expectedRun, expectedCanonical, expectedExact⟩ :=
    generated_qm31_mul_m31_corresponds x rhs hx hrhs
  rw [run] at expectedRun
  cases expectedRun
  exact ⟨expectedCanonical, expectedExact⟩

#print axioms generated_qm31_add_corresponds
#print axioms generated_qm31_mul_corresponds
#print axioms generated_qm31_square_corresponds
#print axioms generated_qm31_mul_m31_corresponds
#print axioms generated_qm31_add_run_corresponds
#print axioms generated_qm31_mul_run_corresponds
#print axioms generated_qm31_square_run_corresponds
#print axioms generated_qm31_mul_m31_run_corresponds

end AspisV5RelationLinkedFieldProjection
