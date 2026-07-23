import GoodMatricesCurrent.SourceExtractedTerminalFieldPreparedTypes
import GoodMatricesCurrent.SourceExtractedTerminalFieldAuthenticPowBridge

open Aeneas Aeneas.Std Result

namespace GoodMatricesCurrent.SourceExtractedTerminalField

theorem root_m31_add_eq_authentic_prepared (left right : Std.U32) :
    _root_.aspis_core.field.M31.add left right =
      AuthenticFieldPreparedMul.field.M31.add left right := by
  have hP : _root_.aspis_core.field.P =
      AuthenticFieldPreparedMul.field.P := by
    apply UScalar.eq_of_val_eq
    unfold _root_.aspis_core.field.P AuthenticFieldPreparedMul.field.P
    rfl
  unfold _root_.aspis_core.field.M31.add
    AuthenticFieldPreparedMul.field.M31.add
  rw [hP]

theorem root_m31_sub_eq_authentic_prepared (left right : Std.U32) :
    _root_.aspis_core.field.M31.sub left right =
      AuthenticFieldPreparedMul.field.M31.sub left right := by
  have hP : AspisCoreAdditive.field.P =
      AuthenticFieldPreparedMul.field.P := by
    apply UScalar.eq_of_val_eq
    unfold AspisCoreAdditive.field.P AuthenticFieldPreparedMul.field.P
    rfl
  unfold _root_.aspis_core.field.M31.sub
  unfold AspisCoreAdditive.field.M31.sub
    AuthenticFieldPreparedMul.field.M31.sub
  rw [hP]

theorem root_m31_mul_eq_authentic_prepared (left right : Std.U32) :
    _root_.aspis_core.field.M31.mul left right =
      AuthenticFieldPreparedMul.field.M31.mul left right := by
  have hP : AuthenticFieldPow.field.P =
      AuthenticFieldPreparedMul.field.P := by
    apply UScalar.eq_of_val_eq
    unfold AuthenticFieldPow.field.P AuthenticFieldPreparedMul.field.P
    rfl
  have hreduce (value : Std.U64) :
      AuthenticFieldPow.field.reduce_u64 value =
        AuthenticFieldPreparedMul.field.reduce_u64 value := by
    unfold AuthenticFieldPow.field.reduce_u64
      AuthenticFieldPreparedMul.field.reduce_u64
    rw [hP]
  unfold _root_.aspis_core.field.M31.mul
  unfold AuthenticFieldPow.field.M31.mul
    AuthenticFieldPreparedMul.field.M31.mul
  simp only [hreduce]

theorem authentic_pow_m31_add_eq_prepared (left right : Std.U32) :
    AuthenticFieldPow.field.M31.add left right =
      AuthenticFieldPreparedMul.field.M31.add left right :=
  (root_m31_add_eq_authentic_pow left right).symm.trans
    (root_m31_add_eq_authentic_prepared left right)

theorem authentic_pow_m31_sub_eq_prepared (left right : Std.U32) :
    AuthenticFieldPow.field.M31.sub left right =
      AuthenticFieldPreparedMul.field.M31.sub left right :=
  (root_m31_sub_eq_authentic_pow left right).symm.trans
    (root_m31_sub_eq_authentic_prepared left right)

theorem authentic_sub_m31_sub_eq_prepared (left right : Std.U32) :
    AspisCoreAdditive.field.M31.sub left right =
      AuthenticFieldPreparedMul.field.M31.sub left right := by
  calc
    AspisCoreAdditive.field.M31.sub left right =
        _root_.aspis_core.field.M31.sub left right := by rfl
    _ = AuthenticFieldPreparedMul.field.M31.sub left right :=
      root_m31_sub_eq_authentic_prepared left right

private theorem authentic_prepared_cm31_map_eta
    (result : Result AuthenticFieldPreparedMul.field.CM31) :
    (do
      let value ← result
      .ok ({ a := value.a, b := value.b } :
        AuthenticFieldPreparedMul.field.CM31)) = result := by
  cases result with
  | ok value => cases value; rfl
  | fail error => rfl
  | div => rfl

theorem authentic_prepared_cm31_add_eq_root_mapped (left right : RootCM31) :
    AuthenticFieldPreparedMul.field.CM31.add
        { a := left.a, b := left.b } { a := right.a, b := right.b } =
      (do
        let value ← _root_.aspis_core.field.CM31.add left right
        .ok ({ a := value.a, b := value.b } :
          AuthenticFieldPreparedMul.field.CM31)) := by
  unfold _root_.aspis_core.field.CM31.add
    AuthenticFieldPreparedMul.field.CM31.add
  simp [root_m31_add_eq_authentic_prepared,
    authentic_prepared_cm31_map_eta]

theorem authentic_prepared_cm31_sub_eq_root_mapped (left right : RootCM31) :
    AuthenticFieldPreparedMul.field.CM31.sub
        { a := left.a, b := left.b } { a := right.a, b := right.b } =
      (do
        let value ← _root_.aspis_core.field.CM31.sub left right
        .ok ({ a := value.a, b := value.b } :
          AuthenticFieldPreparedMul.field.CM31)) := by
  rw [_root_.aspis_core.field.CM31.sub_eq_authentic]
  unfold AspisCoreAdditive.field.CM31.sub
    AuthenticFieldPreparedMul.field.CM31.sub
  simp [authentic_sub_m31_sub_eq_prepared,
    authentic_prepared_cm31_map_eta]

theorem authentic_prepared_mul_by_r_eq_pow_mapped (value : RootCM31) :
    AuthenticFieldPreparedMul.field.mul_by_r
        { a := value.a, b := value.b } =
      (do
        let output ← AuthenticFieldPow.field.mul_by_r
          { a := value.a, b := value.b }
        .ok ({ a := output.a, b := output.b } :
          AuthenticFieldPreparedMul.field.CM31)) := by
  unfold AuthenticFieldPow.field.mul_by_r
    AuthenticFieldPreparedMul.field.mul_by_r
  unfold AuthenticFieldPow.field.M31.double
    AuthenticFieldPreparedMul.field.M31.double
  simp [authentic_pow_m31_add_eq_prepared,
    authentic_pow_m31_sub_eq_prepared,
    authentic_prepared_cm31_map_eta]

end GoodMatricesCurrent.SourceExtractedTerminalField
