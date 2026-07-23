import RuntimeFoldPrimitiveInstantiation
import QM31SquareScalarsProof

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeSquareInstantiation

open aspis_prover
open ComponentCRuntimeFoldPrimitiveInstantiation

private abbrev SqCM31 := AspisLane5QM31SquareScalars.field.CM31
private abbrev SqQM31 := AspisLane5QM31SquareScalars.field.QM31

private def toSqCM (x : RuntimeCM31) : SqCM31 := ⟨x.a, x.b⟩
private def fromSqCM (x : SqCM31) : RuntimeCM31 := ⟨x.a, x.b⟩
private def toSqQM (x : RuntimeQM31) : SqQM31 :=
  ⟨toSqCM x.c0, toSqCM x.c1⟩
private def fromSqQM (x : SqQM31) : RuntimeQM31 :=
  ⟨fromSqCM x.c0, fromSqCM x.c1⟩

@[simp] private theorem mapResult_ok {A B : Type} (f : A → B) (x : A) :
    mapResult f (ok x) = ok (f x) := rfl

@[simp] private theorem mapResult_bind {A B C : Type}
    (f : B → C) (r : Result A) (k : A → Result B) :
    mapResult f (do let x ← r; k x) =
      (do let x ← r; mapResult f (k x)) := by
  cases r <;> rfl

@[simp] private theorem bind_mapResult {A B C : Type}
    (f : A → B) (r : Result A) (k : B → Result C) :
    (do let x ← mapResult f r; k x) =
      (do let x ← r; k (f x)) := by
  cases r <;> rfl

private theorem sqPEq :
    aspis_prover.aspis_core.field.P = AspisLane5QM31SquareScalars.field.P := by
  apply UScalar.eq_of_val_eq
  unfold aspis_prover.aspis_core.field.P AspisLane5QM31SquareScalars.field.P
  rfl

private theorem sqReduceEq (x : Std.U64) :
    aspis_prover.aspis_core.field.reduce_u64 x =
      AspisLane5QM31SquareScalars.field.reduce_u64 x := by
  unfold aspis_prover.aspis_core.field.reduce_u64
    AspisLane5QM31SquareScalars.field.reduce_u64
  rw [sqPEq]

private theorem sqM31AddEq (x y : RuntimeM31) :
    aspis_prover.aspis_core.field.M31.add x y =
      AspisLane5QM31SquareScalars.field.M31.add x y := by
  unfold aspis_prover.aspis_core.field.M31.add
    AspisLane5QM31SquareScalars.field.M31.add
  rw [sqPEq]

private theorem sqM31SubEq (x y : RuntimeM31) :
    aspis_prover.aspis_core.field.M31.sub x y =
      AspisLane5QM31SquareScalars.field.M31.sub x y := by
  unfold aspis_prover.aspis_core.field.M31.sub
    AspisLane5QM31SquareScalars.field.M31.sub
  rw [sqPEq]

private theorem sqM31MulEq (x y : RuntimeM31) :
    aspis_prover.aspis_core.field.M31.mul x y =
      AspisLane5QM31SquareScalars.field.M31.mul x y := by
  unfold aspis_prover.aspis_core.field.M31.mul
    AspisLane5QM31SquareScalars.field.M31.mul
  simp only [Std.lift, bind_tc_ok]
  rw [sqReduceEq]

private theorem sqM31DoubleEq (x : RuntimeM31) :
    aspis_prover.aspis_core.field.M31.double x =
      AspisLane5QM31SquareScalars.field.M31.double x := by
  unfold aspis_prover.aspis_core.field.M31.double
    AspisLane5QM31SquareScalars.field.M31.double
  exact sqM31AddEq x x

private theorem sqCMAddBridge (x y : RuntimeCM31) :
    aspis_prover.aspis_core.field.CM31.add x y = mapResult fromSqCM
      (AspisLane5QM31SquareScalars.field.CM31.add (toSqCM x) (toSqCM y)) := by
  unfold aspis_prover.aspis_core.field.CM31.add
    AspisLane5QM31SquareScalars.field.CM31.add
  simp only [sqM31AddEq, mapResult_bind, mapResult_ok, toSqCM, fromSqCM]

private theorem sqCMMulBridge (x y : RuntimeCM31) :
    aspis_prover.aspis_core.field.CM31.mul x y = mapResult fromSqCM
      (AspisLane5QM31SquareScalars.field.CM31.mul (toSqCM x) (toSqCM y)) := by
  unfold aspis_prover.aspis_core.field.CM31.mul
    AspisLane5QM31SquareScalars.field.CM31.mul
  simp only [sqM31AddEq, sqM31SubEq, sqM31MulEq,
    mapResult_bind, mapResult_ok, toSqCM, fromSqCM]

private theorem sqCMDoubleBridge (x : RuntimeCM31) :
    aspis_prover.aspis_core.field.CM31.double x = mapResult fromSqCM
      (AspisLane5QM31SquareScalars.field.CM31.double (toSqCM x)) := by
  unfold aspis_prover.aspis_core.field.CM31.double
    AspisLane5QM31SquareScalars.field.CM31.double
  exact sqCMAddBridge x x

private theorem sqCMSquareBridge (x : RuntimeCM31) :
    aspis_prover.aspis_core.field.CM31.square x = mapResult fromSqCM
      (AspisLane5QM31SquareScalars.field.CM31.square (toSqCM x)) := by
  unfold aspis_prover.aspis_core.field.CM31.square
    AspisLane5QM31SquareScalars.field.CM31.square
  simp only [sqM31AddEq, sqM31SubEq, sqM31MulEq, sqM31DoubleEq,
    mapResult_bind, mapResult_ok, toSqCM, fromSqCM]

private theorem sqMulByRBridge (x : RuntimeCM31) :
    aspis_prover.aspis_core.field.mul_by_r x = mapResult fromSqCM
      (AspisLane5QM31SquareScalars.field.mul_by_r (toSqCM x)) := by
  unfold aspis_prover.aspis_core.field.mul_by_r
    AspisLane5QM31SquareScalars.field.mul_by_r
  simp only [sqM31AddEq, sqM31SubEq, sqM31DoubleEq,
    mapResult_bind, mapResult_ok, toSqCM, fromSqCM]

private theorem runtimeSquareBridge (x : RuntimeQM31) :
    aspis_prover.aspis_core.field.QM31.square x = mapResult fromSqQM
      (AspisLane5QM31SquareScalars.field.QM31.square (toSqQM x)) := by
  unfold aspis_prover.aspis_core.field.QM31.square
    AspisLane5QM31SquareScalars.field.QM31.square
  simp only [sqCMSquareBridge, sqMulByRBridge, sqCMAddBridge,
    sqCMMulBridge, sqCMDoubleBridge, bind_mapResult, mapResult_bind,
    mapResult_ok, toSqQM, fromSqQM, toSqCM, fromSqCM]

/-- The exact optimized QM31 square used by the generated fold entrypoints. -/
theorem runtime_qm31_square_corresponds
    (x : RuntimeQM31) (hx : runtimeCanonicalQM31 x) :
    ∃ out,
      aspis_prover.aspis_core.field.QM31.square x = ok out ∧
      runtimeCanonicalQM31 out ∧
      runtimeQM31View out = runtimeQM31View x ^ 2 := by
  have hxSq : AspisLane5QM31SquareScalarsProof.CanonicalQM31 (toSqQM x) := by
    simpa [toSqQM, toSqCM, runtimeCanonicalQM31, runtimeCanonicalCM31,
      runtimeCanonicalM31,
      AspisLane5QM31SquareScalarsProof.CanonicalQM31,
      AspisLane5QM31SquareScalarsProof.CanonicalCM31,
      AspisAeneasCM31Multiplicative.CanonicalRawM31] using hx
  rcases AspisLane5QM31SquareScalarsProof.extracted_qm31_square_corresponds
      (toSqQM x) hxSq with
    ⟨outSq, houtSq, hcanonicalSq, _hseven, hexactSq⟩
  refine ⟨fromSqQM outSq, ?_, ?_, ?_⟩
  · rw [runtimeSquareBridge, houtSq]
    rfl
  · simpa [fromSqQM, fromSqCM, runtimeCanonicalQM31,
      runtimeCanonicalCM31, runtimeCanonicalM31,
      AspisLane5QM31SquareScalarsProof.CanonicalQM31,
      AspisLane5QM31SquareScalarsProof.CanonicalCM31,
      AspisAeneasCM31Multiplicative.CanonicalRawM31] using hcanonicalSq
  · have houtView :
        runtimeQM31View (fromSqQM outSq) =
          AspisLane5QM31SquareScalarsProof.qm31ToExact outSq := by
      rfl
    have hxView :
        runtimeQM31View x =
          AspisLane5QM31SquareScalarsProof.qm31ToExact (toSqQM x) := by
      rfl
    rw [houtView, hxView, pow_two]
    exact hexactSq

#print axioms runtime_qm31_square_corresponds

end aspis_prover.ComponentCRuntimeSquareInstantiation
