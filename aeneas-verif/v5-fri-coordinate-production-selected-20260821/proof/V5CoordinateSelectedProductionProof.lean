import V5CoordinateProductionFull.FunsDriver
import V5FriArithmeticSemantics
import V5FriCoordinateReleasedPointConnection

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5CoordinateSelectedProductionProof

namespace Source
open V5CoordinateSelectedProductionSource
end Source

namespace Adapter
open V5FriCoordinateAdapter
end Adapter

theorem p_eq :
    V5CoordinateSelectedProductionSource.field.P =
      V5FriCoordinateAdapter.aspis_core.field.P := by
  unfold V5CoordinateSelectedProductionSource.field.P
    V5FriCoordinateAdapter.aspis_core.field.P
  apply UScalar.eq_of_val_eq
  rfl

theorem adapter_p_val_eq :
    V5FriCoordinateAdapter.aspis_core.field.P.val = 2147483647 := by
  unfold V5FriCoordinateAdapter.aspis_core.field.P
  rfl

theorem u32_size_eq : Std.U32.size = 4294967296 := by
  rw [Std.U32.size, Std.U32.numBits]
  norm_num

theorem uscalar_u32_size_eq : UScalar.size .U32 = 4294967296 := by
  rw [UScalar.size_UScalarTyU32, u32_size_eq]

theorem generic_wrapping_add_eq_u32_wrapping_add
    (left right : Std.U32) :
    UScalar.wrapping_add left right = Std.U32.wrapping_add left right := by
  apply UScalar.eq_of_val_eq
  simp only [UScalar.wrapping_add_val_eq, Std.U32.wrapping_add_val_eq]

theorem generic_wrapping_sub_eq_u32_wrapping_sub
    (left right : Std.U32) :
    UScalar.wrapping_sub left right = Std.U32.wrapping_sub left right := by
  apply UScalar.eq_of_val_eq
  simp only [UScalar.wrapping_sub_val_eq, Std.U32.wrapping_sub_val_eq]

theorem generic_wrapping_add_eq_u64_wrapping_add
    (left right : Std.U64) :
    UScalar.wrapping_add left right = Std.U64.wrapping_add left right := by
  apply UScalar.eq_of_val_eq
  simp only [UScalar.wrapping_add_val_eq, Std.U64.wrapping_add_val_eq]

theorem generic_wrapping_mul_eq_u64_wrapping_mul
    (left right : Std.U64) :
    UScalar.wrapping_mul left right = Std.U64.wrapping_mul left right := by
  apply UScalar.eq_of_val_eq
  simp only [UScalar.wrapping_mul_val_eq, Std.U64.wrapping_mul_val_eq]

theorem checked_u64_shr31_eq_wrapping (value : Std.U64) :
    value >>> 31#u32 =
      Aeneas.Std.Result.ok (Std.U64.wrapping_shr value 31#u32) := by
  obtain ⟨output, hrun, _hval, hbv⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (UScalar.ShiftRight_spec value 31#u32 (by norm_num))
  rw [hrun]
  congr 2
  apply UScalar.eq_of_val_eq
  change output.bv.toNat =
    (Std.U64.wrapping_shr value 31#u32).bv.toNat
  rw [hbv, Std.U64.wrapping_shr_bv_eq]
  norm_num

theorem checked_usize_shr_u32_eq_wrapping
    (value : Std.Usize) (shift : Std.U32)
    (hshift : shift.val < UScalarTy.Usize.numBits) :
    value >>> shift =
      Aeneas.Std.Result.ok (Std.Usize.wrapping_shr value shift) := by
  obtain ⟨output, hrun, _hval, hbv⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (UScalar.ShiftRight_spec value shift hshift)
  rw [hrun]
  congr 2
  apply UScalar.eq_of_val_eq
  change output.bv.toNat =
    (Std.Usize.wrapping_shr value shift).bv.toNat
  have hshiftPlatform : shift.val < System.Platform.numBits := by
    exact hshift
  rw [hbv, Std.Usize.wrapping_shr_bv_eq,
    Nat.mod_eq_of_lt hshiftPlatform]
  simp only [BitVec.ushiftRight_eq]

theorem checked_usize_shr_i32_eight_eq_wrapping (value : Std.Usize) :
    value >>> (8#i32 : Std.I32) =
      Aeneas.Std.Result.ok (Std.Usize.wrapping_shr value (8#i32 : Std.I32)) := by
  obtain ⟨output, hrun, _hval, hbv⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (UScalar.ShiftRight_IScalar_spec value (8#i32 : Std.I32)
        (by norm_num) (by
          norm_num
          rcases System.Platform.numBits_eq with hbits | hbits <;>
            omega))
  rw [hrun]
  congr 2
  apply UScalar.eq_of_val_eq
  change output.bv.toNat =
    (Std.Usize.wrapping_shr value (8#i32 : Std.I32)).bv.toNat
  rw [hbv]
  unfold Std.Usize.wrapping_shr UScalar.wrapping_shr
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    simp [hbits, ScalarShiftAmount.toNat, IScalar.toNat]

theorem u64_and_val_le_right (left right : Std.U64) :
    (left &&& right).val ≤ right.val := by
  simp only [HAnd.hAnd, instHAndUScalar, UScalar.and, UScalar.val,
    BitVec.toNat_and]
  exact Nat.and_le_right

theorem u64_wrapping_shr31_val_eq (value : Std.U64) :
    (Std.U64.wrapping_shr value 31#u32).val = value.val >>> 31 := by
  unfold Std.U64.wrapping_shr UScalar.wrapping_shr
  change (value.bv.ushiftRight (31 % 64)).toNat = value.val >>> 31
  norm_num

theorem u64_wrapping_shr31_val_le_one
    (value : Std.U64) (hvalue : value.val ≤ 4294967291) :
    (Std.U64.wrapping_shr value 31#u32).val ≤ 1 := by
  rw [u64_wrapping_shr31_val_eq, Nat.shiftRight_eq_div_pow]
  norm_num
  omega

theorem u64_size_eq : Std.U64.size = 18446744073709551616 := by
  rw [Std.U64.size, Std.U64.numBits]
  norm_num

theorem checked_add_eq_wrapping {ty : UScalarTy}
    (left right : UScalar ty)
    (hbound : left.val + right.val ≤ UScalar.max ty) :
    left + right = Aeneas.Std.Result.ok (UScalar.wrapping_add left right) := by
  obtain ⟨output, hrun, _hvalue, hbv⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (UScalar.add_bv_spec (x := left) (y := right) hbound)
  rw [hrun]
  congr 2
  apply UScalar.eq_of_val_eq
  change output.bv.toNat =
    (UScalar.wrapping_add left right).bv.toNat
  rw [hbv, UScalar.wrapping_add_bv_eq]

theorem checked_sub_eq_wrapping {ty : UScalarTy}
    (left right : UScalar ty) (hbound : right.val ≤ left.val) :
    left - right = Aeneas.Std.Result.ok (UScalar.wrapping_sub left right) := by
  obtain ⟨output, hrun, _hvalue, _hbound, hbv⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (UScalar.sub_bv_spec (x := left) (y := right) hbound)
  rw [hrun]
  congr 2
  apply UScalar.eq_of_val_eq
  change output.bv.toNat =
    (UScalar.wrapping_sub left right).bv.toNat
  rw [hbv, UScalar.wrapping_sub_bv_eq]

theorem checked_usize_bits_sub_seventeen_eq_wrapping :
    core.num.Usize.BITS - 17#u32 =
      Aeneas.Std.Result.ok
        (Std.U32.wrapping_sub core.num.Usize.BITS 17#u32) := by
  apply checked_sub_eq_wrapping
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    simp [core.num.Usize.BITS, hbits]

theorem checked_mul_eq_wrapping {ty : UScalarTy}
    (left right : UScalar ty)
    (hbound : left.val * right.val ≤ UScalar.max ty) :
    left * right = Aeneas.Std.Result.ok (UScalar.wrapping_mul left right) := by
  obtain ⟨output, hrun, _hvalue, hbv⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (UScalar.mul_bv_spec (x := left) (y := right) hbound)
  rw [hrun]
  congr 2
  apply UScalar.eq_of_val_eq
  change output.bv.toNat =
    (UScalar.wrapping_mul left right).bv.toNat
  rw [hbv, UScalar.wrapping_mul_bv_eq]

theorem source_add_eq_adapter_add
    (left right : Std.U32)
    (hleft : left.val < 2147483647)
    (hright : right.val < 2147483647) :
    V5CoordinateSelectedProductionSource.field.M31.add left right =
      V5FriCoordinateAdapter.aspis_core.field.M31.add left right := by
  unfold V5CoordinateSelectedProductionSource.field.M31.add
    V5FriCoordinateAdapter.aspis_core.field.M31.add
  rw [p_eq]
  rw [checked_add_eq_wrapping]
  · simp only [Std.lift, bind_tc_ok]
    by_cases hreduce :
        V5FriCoordinateAdapter.aspis_core.field.P.val ≤
          (left.val + right.val) % Std.U32.size
    · have hreduce' :
          Std.U32.wrapping_add left right ≥
            V5FriCoordinateAdapter.aspis_core.field.P := by
        apply (UScalar.le_equiv _ _).2
        simpa only [Std.U32.wrapping_add_val_eq,
          UScalar.size_UScalarTyU32] using hreduce
      simp [hreduce, hreduce']
      rw [checked_sub_eq_wrapping]
      · rw [generic_wrapping_add_eq_u32_wrapping_add,
          generic_wrapping_sub_eq_u32_wrapping_sub]
        simp
      · simpa only [UScalar.wrapping_add_val_eq,
            UScalar.size_UScalarTyU32] using hreduce
    · have hreduce' :
          ¬ Std.U32.wrapping_add left right ≥
            V5FriCoordinateAdapter.aspis_core.field.P := by
        intro h
        apply hreduce
        have hval := (UScalar.le_equiv _ _).1 h
        simpa only [Std.U32.wrapping_add_val_eq,
          UScalar.size_UScalarTyU32] using hval
      simp [hreduce, hreduce']
      exact generic_wrapping_add_eq_u32_wrapping_add left right
  · rw [UScalar.max_UScalarTy_U32_eq, Std.U32.max_eq]
    omega

theorem source_sub_eq_adapter_sub
    (left right : Std.U32)
    (hleft : left.val < 2147483647)
    (hright : right.val < 2147483647) :
    V5CoordinateSelectedProductionSource.field.M31.sub left right =
      V5FriCoordinateAdapter.aspis_core.field.M31.sub left right := by
  unfold V5CoordinateSelectedProductionSource.field.M31.sub
    V5FriCoordinateAdapter.aspis_core.field.M31.sub
  rw [p_eq]
  have hadd_lt_size :
      left.val + V5FriCoordinateAdapter.aspis_core.field.P.val <
        Std.U32.size := by
    rw [adapter_p_val_eq, u32_size_eq]
    omega
  rw [checked_add_eq_wrapping]
  · simp only [Std.lift, bind_tc_ok]
    rw [checked_sub_eq_wrapping]
    · simp only [bind_tc_ok]
      by_cases hreduce :
          V5FriCoordinateAdapter.aspis_core.field.P.val ≤
            ((left.val + V5FriCoordinateAdapter.aspis_core.field.P.val) +
              (Std.U32.size - right.val)) % Std.U32.size
      · have hreduce' :
            (Std.U32.wrapping_add left
                V5FriCoordinateAdapter.aspis_core.field.P).wrapping_sub right ≥
              V5FriCoordinateAdapter.aspis_core.field.P := by
          apply (UScalar.le_equiv _ _).2
          simp only [Std.U32.wrapping_add_val_eq,
            Std.U32.wrapping_sub_val_eq, UScalar.size_UScalarTyU32]
          rw [Nat.mod_eq_of_lt hadd_lt_size]
          exact hreduce
        simp [hreduce, hreduce']
        rw [checked_sub_eq_wrapping]
        · rw [generic_wrapping_add_eq_u32_wrapping_add,
            generic_wrapping_sub_eq_u32_wrapping_sub,
            generic_wrapping_sub_eq_u32_wrapping_sub]
          simp
        · simp only [UScalar.wrapping_add_val_eq,
              UScalar.wrapping_sub_val_eq, UScalar.size_UScalarTyU32]
          rw [Nat.mod_eq_of_lt hadd_lt_size]
          exact hreduce
      · have hreduce' :
            ¬ (Std.U32.wrapping_add left
                V5FriCoordinateAdapter.aspis_core.field.P).wrapping_sub right ≥
              V5FriCoordinateAdapter.aspis_core.field.P := by
          intro h
          apply hreduce
          have hval := (UScalar.le_equiv _ _).1 h
          simpa only [Std.U32.wrapping_add_val_eq,
              Std.U32.wrapping_sub_val_eq, UScalar.size_UScalarTyU32,
              Nat.mod_eq_of_lt hadd_lt_size] using hval
        simp [hreduce, hreduce']
        rw [generic_wrapping_add_eq_u32_wrapping_add,
          generic_wrapping_sub_eq_u32_wrapping_sub]
    · rw [UScalar.wrapping_add_val_eq]
      rw [adapter_p_val_eq, uscalar_u32_size_eq]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
  · rw [UScalar.max_UScalarTy_U32_eq, Std.U32.max_eq,
      adapter_p_val_eq]
    omega

theorem source_reduce_u64_eq_adapter_reduce_u64
    (value : Std.U64)
    (hvalue : value.val ≤ 4611686009837453316) :
    V5CoordinateSelectedProductionSource.field.reduce_u64 value =
      V5FriCoordinateAdapter.aspis_core.field.reduce_u64 value := by
  unfold V5CoordinateSelectedProductionSource.field.reduce_u64
    V5FriCoordinateAdapter.aspis_core.field.reduce_u64
  rw [p_eq]
  have hmask :
      (UScalar.cast .U64
        V5FriCoordinateAdapter.aspis_core.field.P).val = 2147483647 := by
    rw [Std.U32.cast_U64_val_eq, adapter_p_val_eq]
  have hhigh :
      (Std.U64.wrapping_shr value 31#u32).val ≤ 2147483644 := by
    rw [u64_wrapping_shr31_val_eq, Nat.shiftRight_eq_div_pow]
    norm_num
    omega
  have hand :
      (value &&& UScalar.cast .U64
        V5FriCoordinateAdapter.aspis_core.field.P).val ≤ 2147483647 := by
    calc
      _ ≤ (UScalar.cast .U64
          V5FriCoordinateAdapter.aspis_core.field.P).val :=
        u64_and_val_le_right _ _
      _ = 2147483647 := hmask
  have hfirst_sum :
      (value &&& UScalar.cast .U64
          V5FriCoordinateAdapter.aspis_core.field.P).val +
        (Std.U64.wrapping_shr value 31#u32).val ≤ 4294967291 := by
    omega
  have hfirst_sum_lt_size :
      (value &&& UScalar.cast .U64
          V5FriCoordinateAdapter.aspis_core.field.P).val +
        (Std.U64.wrapping_shr value 31#u32).val < Std.U64.size := by
    rw [u64_size_eq]
    omega
  have hx1 :
      (Std.U64.wrapping_add
        (value &&& UScalar.cast .U64
          V5FriCoordinateAdapter.aspis_core.field.P)
        (Std.U64.wrapping_shr value 31#u32)).val ≤ 4294967291 := by
    rw [Std.U64.wrapping_add_val_eq, UScalar.size_UScalarTyU64,
      Nat.mod_eq_of_lt hfirst_sum_lt_size]
    exact hfirst_sum
  have hx1high :
      (Std.U64.wrapping_shr
        (Std.U64.wrapping_add
          (value &&& UScalar.cast .U64
            V5FriCoordinateAdapter.aspis_core.field.P)
          (Std.U64.wrapping_shr value 31#u32)) 31#u32).val ≤ 1 := by
    exact u64_wrapping_shr31_val_le_one _ hx1
  have hx1and :
      (Std.U64.wrapping_add
          (value &&& UScalar.cast .U64
            V5FriCoordinateAdapter.aspis_core.field.P)
          (Std.U64.wrapping_shr value 31#u32) &&&
        UScalar.cast .U64
          V5FriCoordinateAdapter.aspis_core.field.P).val ≤ 2147483647 := by
    calc
      _ ≤ (UScalar.cast .U64
          V5FriCoordinateAdapter.aspis_core.field.P).val :=
        u64_and_val_le_right _ _
      _ = 2147483647 := hmask
  simp only [Std.lift, bind_tc_ok]
  rw [checked_u64_shr31_eq_wrapping]
  simp only [bind_tc_ok]
  rw [checked_add_eq_wrapping]
  · simp only [bind_tc_ok]
    rw [generic_wrapping_add_eq_u64_wrapping_add]
    rw [checked_u64_shr31_eq_wrapping]
    simp only [bind_tc_ok]
    rw [checked_add_eq_wrapping]
    · simp only [bind_tc_ok]
      rw [generic_wrapping_add_eq_u64_wrapping_add]
      by_cases hreduce :
          UScalar.cast .U32
              (Std.U64.wrapping_add
                (Std.U64.wrapping_add
                    (value &&& UScalar.cast .U64
                      V5FriCoordinateAdapter.aspis_core.field.P)
                    (Std.U64.wrapping_shr value 31#u32) &&&
                  UScalar.cast .U64
                    V5FriCoordinateAdapter.aspis_core.field.P)
                (Std.U64.wrapping_shr
                  (Std.U64.wrapping_add
                    (value &&& UScalar.cast .U64
                      V5FriCoordinateAdapter.aspis_core.field.P)
                    (Std.U64.wrapping_shr value 31#u32)) 31#u32)) ≥
            V5FriCoordinateAdapter.aspis_core.field.P
      · simp [hreduce]
        rw [checked_sub_eq_wrapping]
        · rw [generic_wrapping_sub_eq_u32_wrapping_sub]
        · exact (UScalar.le_equiv _ _).1 hreduce
      · simp [hreduce]
    · rw [UScalar.max_UScalarTy_U64_eq, Std.U64.max_eq]
      omega
  · rw [UScalar.max_UScalarTy_U64_eq, Std.U64.max_eq]
    omega

theorem source_mul_eq_adapter_mul
    (left right : Std.U32)
    (hleft : left.val < 2147483647)
    (hright : right.val < 2147483647) :
    V5CoordinateSelectedProductionSource.field.M31.mul left right =
      V5FriCoordinateAdapter.aspis_core.field.M31.mul left right := by
  have hproduct : left.val * right.val ≤ 4611686009837453316 := by
    nlinarith
  have hwrapped :
      (Std.U64.wrapping_mul (UScalar.cast .U64 left)
        (UScalar.cast .U64 right)).val = left.val * right.val := by
    rw [Std.U64.wrapping_mul_val_eq, UScalar.size_UScalarTyU64,
      Std.U32.cast_U64_val_eq, Std.U32.cast_U64_val_eq]
    rw [Nat.mod_eq_of_lt]
    rw [u64_size_eq]
    omega
  unfold V5CoordinateSelectedProductionSource.field.M31.mul
    V5FriCoordinateAdapter.aspis_core.field.M31.mul
  simp only [Std.lift, bind_tc_ok]
  rw [checked_mul_eq_wrapping]
  · simp only [bind_tc_ok]
    rw [generic_wrapping_mul_eq_u64_wrapping_mul]
    rw [source_reduce_u64_eq_adapter_reduce_u64]
    rw [hwrapped]
    exact hproduct
  · rw [Std.U32.cast_U64_val_eq, Std.U32.cast_U64_val_eq,
      UScalar.max_UScalarTy_U64_eq, Std.U64.max_eq]
    omega

theorem adapter_p_eq_fresh_p :
    V5FriCoordinateAdapter.aspis_core.field.P =
      V5FriArithmeticExact.field.P := by
  apply UScalar.eq_of_val_eq
  unfold V5FriCoordinateAdapter.aspis_core.field.P
    V5FriArithmeticExact.field.P
  rfl

theorem adapter_reduce_eq_fresh_reduce (value : Std.U64) :
    V5FriCoordinateAdapter.aspis_core.field.reduce_u64 value =
      V5FriArithmeticExact.field.reduce_u64 value := by
  unfold V5FriCoordinateAdapter.aspis_core.field.reduce_u64
    V5FriArithmeticExact.field.reduce_u64
  rw [adapter_p_eq_fresh_p]

theorem adapter_add_eq_fresh_add (left right : Std.U32) :
    V5FriCoordinateAdapter.aspis_core.field.M31.add left right =
      V5FriArithmeticExact.field.M31.add left right := by
  unfold V5FriCoordinateAdapter.aspis_core.field.M31.add
    V5FriArithmeticExact.field.M31.add
  rw [adapter_p_eq_fresh_p]

theorem adapter_sub_eq_fresh_sub (left right : Std.U32) :
    V5FriCoordinateAdapter.aspis_core.field.M31.sub left right =
      V5FriArithmeticExact.field.M31.sub left right := by
  unfold V5FriCoordinateAdapter.aspis_core.field.M31.sub
    V5FriArithmeticExact.field.M31.sub
  rw [adapter_p_eq_fresh_p]

theorem adapter_mul_eq_fresh_mul (left right : Std.U32) :
    V5FriCoordinateAdapter.aspis_core.field.M31.mul left right =
      V5FriArithmeticExact.field.M31.mul left right := by
  unfold V5FriCoordinateAdapter.aspis_core.field.M31.mul
    V5FriArithmeticExact.field.M31.mul
  simp only [Std.lift, bind_tc_ok]
  rw [adapter_reduce_eq_fresh_reduce]

theorem adapter_neg_eq_fresh_neg (value : Std.U32) :
    V5FriCoordinateAdapter.aspis_core.field.M31.neg value =
      V5FriArithmeticExact.field.M31.neg value := by
  unfold V5FriCoordinateAdapter.aspis_core.field.M31.neg
    V5FriArithmeticExact.field.M31.neg
  rw [adapter_p_eq_fresh_p]

abbrev CanonicalM31 (value : Std.U32) : Prop :=
  AspisV5FriArithmeticSemantics.canonicalM31 value

theorem canonical_m31_lt (value : Std.U32) (hvalue : CanonicalM31 value) :
    value.val < 2147483647 := by
  exact hvalue

abbrev SourcePoint :=
  V5CoordinateSelectedProductionSource.circle_fri.BaseCirclePoint

abbrev AdapterPoint :=
  V5FriCoordinateAdapter.aspis_core.circle_fri.BaseCirclePoint

private instance : Inhabited SourcePoint :=
  ⟨{ x := 0#u32, y := 0#u32 }⟩

private theorem getElemBang_eq_getElem {T : Type*} [Inhabited T]
    (values : List T) (index : Nat) (hindex : index < values.length) :
    values[index]! = values[index] := by
  apply List.getElem!_of_getElem?
  simp [hindex]

private theorem result_bind_ite {T U : Type} (condition : Prop)
    [Decidable condition] (yes no : Result T) (next : T → Result U) :
    (if condition then yes else no) >>= next =
      if condition then yes >>= next else no >>= next := by
  by_cases hcondition : condition <;> simp [hcondition]

def toAdapterPoint (point : SourcePoint) : AdapterPoint :=
  { x := point.x, y := point.y }

def mapSourcePointResult : Result SourcePoint → Result AdapterPoint
  | .ok point => .ok (toAdapterPoint point)
  | .fail error => .fail error
  | .div => .div

theorem source_point_add_eq_adapter_point_add
    (left right : SourcePoint)
    (hleft : CanonicalM31 left.x ∧ CanonicalM31 left.y)
    (hright : CanonicalM31 right.x ∧ CanonicalM31 right.y) :
    mapSourcePointResult
        (V5CoordinateSelectedProductionSource.circle_fri.BaseCirclePoint.add left right) =
      V5FriCoordinateAdapter.aspis_core.circle_fri.BaseCirclePoint.add
        (toAdapterPoint left) (toAdapterPoint right) := by
  obtain ⟨xx, hxxFresh, hxxCanonical, _hxxValue⟩ :=
    AspisV5FriArithmeticSemantics.m31_mul_corresponds
      left.x right.x hleft.1 hright.1
  have hxxAdapter :
      V5FriCoordinateAdapter.aspis_core.field.M31.mul left.x right.x =
        .ok xx := by
    rw [adapter_mul_eq_fresh_mul]
    exact hxxFresh
  have hxxSource :
      V5CoordinateSelectedProductionSource.field.M31.mul left.x right.x = .ok xx := by
    rw [source_mul_eq_adapter_mul left.x right.x
      (canonical_m31_lt left.x hleft.1)
      (canonical_m31_lt right.x hright.1)]
    exact hxxAdapter
  obtain ⟨yy, hyyFresh, hyyCanonical, _hyyValue⟩ :=
    AspisV5FriArithmeticSemantics.m31_mul_corresponds
      left.y right.y hleft.2 hright.2
  have hyyAdapter :
      V5FriCoordinateAdapter.aspis_core.field.M31.mul left.y right.y =
        .ok yy := by
    rw [adapter_mul_eq_fresh_mul]
    exact hyyFresh
  have hyySource :
      V5CoordinateSelectedProductionSource.field.M31.mul left.y right.y = .ok yy := by
    rw [source_mul_eq_adapter_mul left.y right.y
      (canonical_m31_lt left.y hleft.2)
      (canonical_m31_lt right.y hright.2)]
    exact hyyAdapter
  obtain ⟨x, hxFresh, hxCanonical, _hxValue⟩ :=
    AspisV5FriArithmeticSemantics.m31_sub_corresponds
      xx yy hxxCanonical hyyCanonical
  have hxAdapter :
      V5FriCoordinateAdapter.aspis_core.field.M31.sub xx yy = .ok x := by
    rw [adapter_sub_eq_fresh_sub]
    exact hxFresh
  have hxSource :
      V5CoordinateSelectedProductionSource.field.M31.sub xx yy = .ok x := by
    rw [source_sub_eq_adapter_sub xx yy
      (canonical_m31_lt xx hxxCanonical)
      (canonical_m31_lt yy hyyCanonical)]
    exact hxAdapter
  obtain ⟨xy, hxyFresh, hxyCanonical, _hxyValue⟩ :=
    AspisV5FriArithmeticSemantics.m31_mul_corresponds
      left.x right.y hleft.1 hright.2
  have hxyAdapter :
      V5FriCoordinateAdapter.aspis_core.field.M31.mul left.x right.y =
        .ok xy := by
    rw [adapter_mul_eq_fresh_mul]
    exact hxyFresh
  have hxySource :
      V5CoordinateSelectedProductionSource.field.M31.mul left.x right.y = .ok xy := by
    rw [source_mul_eq_adapter_mul left.x right.y
      (canonical_m31_lt left.x hleft.1)
      (canonical_m31_lt right.y hright.2)]
    exact hxyAdapter
  obtain ⟨yx, hyxFresh, hyxCanonical, _hyxValue⟩ :=
    AspisV5FriArithmeticSemantics.m31_mul_corresponds
      left.y right.x hleft.2 hright.1
  have hyxAdapter :
      V5FriCoordinateAdapter.aspis_core.field.M31.mul left.y right.x =
        .ok yx := by
    rw [adapter_mul_eq_fresh_mul]
    exact hyxFresh
  have hyxSource :
      V5CoordinateSelectedProductionSource.field.M31.mul left.y right.x = .ok yx := by
    rw [source_mul_eq_adapter_mul left.y right.x
      (canonical_m31_lt left.y hleft.2)
      (canonical_m31_lt right.x hright.1)]
    exact hyxAdapter
  obtain ⟨y, hyFresh, _hyCanonical, _hyValue⟩ :=
    AspisV5FriArithmeticSemantics.m31_add_corresponds
      xy yx hxyCanonical hyxCanonical
  have hyAdapter :
      V5FriCoordinateAdapter.aspis_core.field.M31.add xy yx = .ok y := by
    rw [adapter_add_eq_fresh_add]
    exact hyFresh
  have hySource :
      V5CoordinateSelectedProductionSource.field.M31.add xy yx = .ok y := by
    rw [source_add_eq_adapter_add xy yx
      (canonical_m31_lt xy hxyCanonical)
      (canonical_m31_lt yx hyxCanonical)]
    exact hyAdapter
  unfold V5CoordinateSelectedProductionSource.circle_fri.BaseCirclePoint.add
    V5FriCoordinateAdapter.aspis_core.circle_fri.BaseCirclePoint.add
  simp only [hxxSource, hyySource, hxSource, hxySource, hyxSource,
    hySource, hxxAdapter, hyyAdapter, hxAdapter, hxyAdapter, hyxAdapter,
    hyAdapter, bind_tc_ok, mapSourcePointResult, toAdapterPoint]


theorem high_table_eq :
    V5CoordinateSelectedProductionSource.circle_fri.RATE512_CIRCLE_HIGH9_WINDOW =
      V5FriCoordinateAdapter.aspis_core.circle_fri.RATE512_CIRCLE_HIGH9_WINDOW := by
  unfold V5CoordinateSelectedProductionSource.circle_fri.RATE512_CIRCLE_HIGH9_WINDOW
    V5FriCoordinateAdapter.aspis_core.circle_fri.RATE512_CIRCLE_HIGH9_WINDOW
  apply Subtype.ext
  rfl

set_option maxRecDepth 200000 in
set_option maxHeartbeats 50000000 in
theorem low_table_eq :
    V5CoordinateSelectedProductionSource.circle_fri.RATE512_CIRCLE_LOW8_WINDOW =
      V5FriCoordinateAdapter.aspis_core.circle_fri.RATE512_CIRCLE_LOW8_WINDOW := by
  unfold V5CoordinateSelectedProductionSource.circle_fri.RATE512_CIRCLE_LOW8_WINDOW
    V5FriCoordinateAdapter.aspis_core.circle_fri.RATE512_CIRCLE_LOW8_WINDOW
  apply Subtype.ext
  rfl

def sourceSelectedPointCallNormalized (fiber : Std.U32) :
    Result SourcePoint := do
  let lowArray ←
    Array.index_usize
      V5CoordinateSelectedProductionSource.circle_fri.RATE512_CIRCLE_LOW8_WINDOW
      (AspisV5FriCoordinatePointLoops.sourceLowIndex fiber)
  let lowX ← Array.index_usize lowArray 0#usize
  let lowY ← Array.index_usize lowArray 1#usize
  let low : SourcePoint := { x := lowX, y := lowY }
  if AspisV5FriCoordinatePointLoops.sourceHighIndex fiber != 0#usize then
    let highArray ←
      Array.index_usize
        V5CoordinateSelectedProductionSource.circle_fri.RATE512_CIRCLE_HIGH9_WINDOW
        (AspisV5FriCoordinatePointLoops.sourceHighIndex fiber)
    let highX ← Array.index_usize highArray 0#usize
    let highY ← Array.index_usize highArray 1#usize
    V5CoordinateSelectedProductionSource.circle_fri.BaseCirclePoint.add low
      { x := highX, y := highY }
  else
    ok low

def sourceSelectedPointCall (fiber : Std.U32) : Result SourcePoint := do
  let widened ← lift (UScalar.cast .Usize fiber)
  let reversed ← core.num.Usize.reverse_bits widened
  let shift ← core.num.Usize.BITS - 17#u32
  let natural ← reversed >>> shift
  let lowIndex ← lift (natural &&& 255#usize)
  let lowArray ←
    Array.index_usize
      V5CoordinateSelectedProductionSource.circle_fri.RATE512_CIRCLE_LOW8_WINDOW
      lowIndex
  let lowX ← Array.index_usize lowArray 0#usize
  let lowY ← Array.index_usize lowArray 1#usize
  let highIndex ← natural >>> (8#i32 : Std.I32)
  if highIndex != 0#usize then
    let highArray ←
      Array.index_usize
        V5CoordinateSelectedProductionSource.circle_fri.RATE512_CIRCLE_HIGH9_WINDOW
        highIndex
    let highX ← Array.index_usize highArray 0#usize
    let highY ← Array.index_usize highArray 1#usize
    V5CoordinateSelectedProductionSource.circle_fri.BaseCirclePoint.add
      { x := lowX, y := lowY } { x := highX, y := highY }
  else
    ok { x := lowX, y := lowY }

theorem selected_shift_lt :
    (Std.U32.wrapping_sub core.num.Usize.BITS 17#u32).val <
      UScalarTy.Usize.numBits := by
  rw [UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with hbits | hbits
  · simp [core.num.Usize.BITS, hbits, Std.U32.wrapping_sub,
      UScalar.wrapping_sub]
    change 15 < 32
    norm_num
  · simp [core.num.Usize.BITS, hbits, Std.U32.wrapping_sub,
      UScalar.wrapping_sub]
    change 47 < 64
    norm_num

theorem sourceSelectedPointCall_eq_normalized (fiber : Std.U32) :
    sourceSelectedPointCall fiber = sourceSelectedPointCallNormalized fiber := by
  unfold sourceSelectedPointCall sourceSelectedPointCallNormalized
  rw [checked_usize_bits_sub_seventeen_eq_wrapping]
  simp only [Std.lift, bind_tc_ok]
  simp only [core.num.Usize.reverse_bits, bind_tc_ok]
  rw [checked_usize_shr_u32_eq_wrapping _ _ selected_shift_lt]
  simp only [bind_tc_ok]
  simp_rw [checked_usize_shr_i32_eight_eq_wrapping]
  simp [AspisV5FriCoordinatePointLoops.sourceNatural,
    AspisV5FriCoordinatePointLoops.sourceLowIndex,
    AspisV5FriCoordinatePointLoops.sourceHighIndex,
    core.num.Usize.reverse_bits, Std.lift]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 80000000 in
theorem sourceSelectedPointCallNormalized_maps_adapter (fiber : Std.U32) :
    mapSourcePointResult (sourceSelectedPointCallNormalized fiber) =
      AspisV5FriCoordinatePointLoops.selectedPointCall fiber := by
  let lowIndex : Fin 256 :=
    ⟨(AspisV5FriCoordinatePointLoops.sourceLowIndex fiber).val,
      AspisV5FriCoordinatePointLoops.sourceLowIndex_lt fiber⟩
  obtain ⟨lowArray, hlowArrayRun, hlowArrayValue⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Array.index_usize_spec
        V5FriCoordinateAdapter.aspis_core.circle_fri.RATE512_CIRCLE_LOW8_WINDOW
        (AspisV5FriCoordinatePointLoops.sourceLowIndex fiber)
        (AspisV5FriCoordinatePointLoops.sourceLowIndex_lt fiber))
  obtain ⟨lowX, hlowXRun, hlowXValue⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Array.index_usize_spec lowArray 0#usize (by simp))
  obtain ⟨lowY, hlowYRun, hlowYValue⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Array.index_usize_spec lowArray 1#usize (by simp))
  let lowSource : SourcePoint := { x := lowX, y := lowY }
  let lowAdapter : AdapterPoint := { x := lowX, y := lowY }
  have hlowEq :
      lowAdapter = AspisV5FriCoordinatePointLoops.lowEntry lowIndex := by
    simp [lowAdapter, AspisV5FriCoordinatePointLoops.lowEntry, lowIndex,
      hlowArrayValue, hlowXValue, hlowYValue]
  have hlowCanonical :
      CanonicalM31 lowX ∧ CanonicalM31 lowY := by
    have h := AspisV5FriCoordinatePointLoops.lowEntry_canonical lowIndex
    rw [← hlowEq] at h
    exact h
  by_cases hhighZero :
      AspisV5FriCoordinatePointLoops.sourceHighIndex fiber = 0#usize
  · simp [sourceSelectedPointCallNormalized,
      AspisV5FriCoordinatePointLoops.selectedPointCall,
      low_table_eq, hlowArrayRun, hlowXRun, hlowYRun, hhighZero,
      lowSource, lowAdapter, mapSourcePointResult, toAdapterPoint]
  · let highIndex : Fin 512 :=
      ⟨(AspisV5FriCoordinatePointLoops.sourceHighIndex fiber).val,
        AspisV5FriCoordinatePointLoops.sourceHighIndex_lt fiber⟩
    obtain ⟨highArray, hhighArrayRun, hhighArrayValue⟩ :=
      Aeneas.Std.WP.spec_imp_exists
        (Array.index_usize_spec
          V5FriCoordinateAdapter.aspis_core.circle_fri.RATE512_CIRCLE_HIGH9_WINDOW
          (AspisV5FriCoordinatePointLoops.sourceHighIndex fiber)
          (AspisV5FriCoordinatePointLoops.sourceHighIndex_lt fiber))
    obtain ⟨highX, hhighXRun, hhighXValue⟩ :=
      Aeneas.Std.WP.spec_imp_exists
        (Array.index_usize_spec highArray 0#usize (by simp))
    obtain ⟨highY, hhighYRun, hhighYValue⟩ :=
      Aeneas.Std.WP.spec_imp_exists
        (Array.index_usize_spec highArray 1#usize (by simp))
    let highSource : SourcePoint := { x := highX, y := highY }
    let highAdapter : AdapterPoint := { x := highX, y := highY }
    have hhighEq :
        highAdapter = AspisV5FriCoordinatePointLoops.highEntry highIndex := by
      simp [highAdapter, AspisV5FriCoordinatePointLoops.highEntry, highIndex,
        hhighArrayValue, hhighXValue, hhighYValue]
    have hhighCanonical :
        CanonicalM31 highX ∧ CanonicalM31 highY := by
      have h := AspisV5FriCoordinatePointLoops.highEntry_canonical highIndex
      rw [← hhighEq] at h
      exact h
    have hadd := source_point_add_eq_adapter_point_add lowSource highSource
      hlowCanonical hhighCanonical
    simp only [lowSource, highSource, toAdapterPoint] at hadd
    simpa [sourceSelectedPointCallNormalized,
      AspisV5FriCoordinatePointLoops.selectedPointCall,
      low_table_eq, high_table_eq, hlowArrayRun, hlowXRun, hlowYRun,
      hhighZero, hhighArrayRun, hhighXRun, hhighYRun, lowSource,
      highSource, lowAdapter, highAdapter] using hadd

def SourceRepresents (point : SourcePoint)
    (expected : AspisCircleGroupOrder.C) : Prop :=
  AspisV5FriCoordinatePointLoops.Represents (toAdapterPoint point) expected

theorem sourceSelectedPointCall_exact (fiber : Std.U32) :
    ∃ output : SourcePoint,
      sourceSelectedPointCall fiber = .ok output ∧
      SourceRepresents output
        (AspisV5FriCoordinatePointLoops.selectedExpectedPoint fiber) := by
  obtain ⟨adapterOutput, hadapterRun, hadapterRepresents⟩ :=
    AspisV5FriCoordinatePointLoops.selectedPointCall_exact fiber
  have hmapped : mapSourcePointResult (sourceSelectedPointCall fiber) =
      .ok adapterOutput := by
    rw [sourceSelectedPointCall_eq_normalized,
      sourceSelectedPointCallNormalized_maps_adapter, hadapterRun]
  cases hsource : sourceSelectedPointCall fiber with
  | fail error => simp [hsource, mapSourcePointResult] at hmapped
  | div => simp [hsource, mapSourcePointResult] at hmapped
  | ok sourceOutput =>
      have houtput : toAdapterPoint sourceOutput = adapterOutput := by
        simpa [hsource, mapSourcePointResult] using hmapped
      refine ⟨sourceOutput, rfl, ?_⟩
      unfold SourceRepresents
      rw [houtput]
      exact hadapterRepresents

def SourceSelectedPointsPost (fibers : Slice Std.U32)
    (points : alloc.vec.Vec SourcePoint) : Prop :=
  points.val.length = fibers.val.length ∧
    ∀ (index : Nat) (hindex : index < fibers.val.length),
      SourceRepresents points.val[index]!
        (AspisV5FriCoordinatePointLoops.selectedExpectedPoint
          fibers.val[index]!)

private def SourceSelectedPointsInvariant (fibers : Slice Std.U32)
    (state : core.slice.iter.Iter Std.U32 × alloc.vec.Vec SourcePoint) : Prop :=
  state.1.slice = fibers ∧
    state.1.i ≤ fibers.val.length ∧
    state.2.val.length = state.1.i ∧
    ∀ (index : Nat) (hindex : index < state.1.i),
      SourceRepresents state.2.val[index]!
        (AspisV5FriCoordinatePointLoops.selectedExpectedPoint
          fibers.val[index]!)

private theorem source_selected_loop_body_active
    (fibers : Slice Std.U32) (index : Nat)
    (points : alloc.vec.Vec SourcePoint)
    (hactive : index < fibers.val.length)
    (hrange : (fibers[index]'hactive).val < 131072) :
    V5CoordinateSelectedProductionSource.circle_fri.selected_circle_fiber_points_shared_loop0.body
        131072#usize { slice := fibers, i := index } points =
      (do
        let point ← sourceSelectedPointCall (fibers[index]'hactive)
        let nextPoints ← alloc.vec.Vec.push points point
        ok (cont ({ slice := fibers, i := index + 1 }, nextPoints) :
          ControlFlow
            (core.slice.iter.Iter Std.U32 × alloc.vec.Vec SourcePoint)
            (core.result.Result (alloc.vec.Vec SourcePoint)
              V5CoordinateSelectedProductionSource.circle_fri.CircleFriError))) := by
  unfold
    V5CoordinateSelectedProductionSource.circle_fri.selected_circle_fiber_points_shared_loop0.body
    core.slice.iter.IteratorSliceIter.next
  simp only [Slice.len_val, hactive, dite_true, bind_tc_ok]
  have hnotOutOfRange :
      ¬ (UScalar.cast .Usize (fibers[index]'hactive) ≥ 131072#usize) := by
    have hcast :
        (UScalar.cast .Usize (fibers[index]'hactive)).val =
          (fibers[index]'hactive).val := by
      exact Std.U32.cast_Usize_val_eq (fibers[index]'hactive)
    intro hout
    have houtVal := (UScalar.le_equiv _ _).1 hout
    rw [hcast] at houtVal
    norm_num at houtVal
    omega
  simp only [Std.lift, bind_tc_ok]
  split
  · rename_i hout
    exact (hnotOutOfRange hout).elim
  · simp [sourceSelectedPointCall, Std.lift, bind_assoc, result_bind_ite]
    rfl

/-- The directly translated production loop returns one exact released
circle point for every in-range input fibre, preserving caller order. -/
theorem source_selected_points_loop_exact
    (fibers : Slice Std.U32) (points : alloc.vec.Vec SourcePoint)
    (hpoints : points.val = [])
    (hrange : ∀ index, index < fibers.val.length →
      fibers.val[index]!.val < 131072) :
    V5CoordinateSelectedProductionSource.circle_fri.selected_circle_fiber_points_shared_loop0
        { slice := fibers, i := 0 } 131072#usize points
      ⦃ output => match output with
        | .Ok output => SourceSelectedPointsPost fibers output
        | .Err _ => False ⦄ := by
  unfold
    V5CoordinateSelectedProductionSource.circle_fri.selected_circle_fiber_points_shared_loop0
  apply loop.spec_decr_nat
    (body := fun state =>
      V5CoordinateSelectedProductionSource.circle_fri.selected_circle_fiber_points_shared_loop0.body
        131072#usize state.1 state.2)
    (x := ({ slice := fibers, i := 0 }, points))
    (fun state => fibers.val.length - state.1.i)
    (SourceSelectedPointsInvariant fibers)
    (fun output => match output with
      | .Ok output => SourceSelectedPointsPost fibers output
      | .Err _ => False)
  · rintro ⟨iter, currentPoints⟩ hstate
    rcases iter with ⟨iterSlice, iterIndex⟩
    rcases hstate with
      ⟨hslice, hindexLe, hlength, hrepresents⟩
    simp only at hslice hindexLe hlength hrepresents
    by_cases hactive : iterIndex < fibers.val.length
    · obtain ⟨point, hpointRun, hpointRep⟩ :=
        sourceSelectedPointCall_exact (fibers[iterIndex]'hactive)
      have hcapacity : currentPoints.val.length < Std.Usize.max := by
        have hfibersMax := fibers.property
        omega
      obtain ⟨nextPoints, hpushRun, hnextPoints⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (alloc.vec.Vec.push_spec currentPoints point hcapacity)
      have hfiberBang :
          fibers.val[iterIndex]! = fibers[iterIndex]'hactive := by
        change fibers.val[iterIndex]! = fibers.val[iterIndex]
        exact getElemBang_eq_getElem _ _ hactive
      have hfiberRange : (fibers[iterIndex]'hactive).val < 131072 := by
        rw [← hfiberBang]
        exact hrange iterIndex hactive
      simp only [hslice]
      rw [source_selected_loop_body_active fibers iterIndex currentPoints
        hactive hfiberRange, hpointRun]
      simp only [bind_tc_ok]
      rw [hpushRun]
      simp only [bind_tc_ok, WP.spec_ok]
      change SourceSelectedPointsInvariant fibers
          ({ slice := fibers, i := iterIndex + 1 }, nextPoints) ∧
        fibers.val.length - (iterIndex + 1) <
          fibers.val.length - iterIndex
      refine ⟨?_, by omega⟩
      unfold SourceSelectedPointsInvariant
      simp only
      refine ⟨True.intro, by omega, ?_, ?_⟩
      · rw [hnextPoints, List.length_append, hlength]
        simp
      · intro ordinal hord
        by_cases hprior : ordinal < iterIndex
        · have hleft : ordinal < currentPoints.val.length := by
            simpa [hlength] using hprior
          have happendBang :
              (currentPoints.val ++ [point])[ordinal]! =
                currentPoints.val[ordinal]! := by
            rw [getElemBang_eq_getElem _ _
                (by simp only [List.length_append, List.length_singleton];
                    omega),
              getElemBang_eq_getElem _ _ hleft,
              List.getElem_append_left hleft]
          rw [hnextPoints, happendBang]
          exact hrepresents ordinal hprior
        · have hlast : ordinal = iterIndex := by omega
          subst ordinal
          have happendBang :
              (currentPoints.val ++ [point])[iterIndex]! = point := by
            rw [getElemBang_eq_getElem _ _ (by simp [hlength])]
            simp [hlength]
          rw [hnextPoints, happendBang]
          rw [hfiberBang]
          exact hpointRep
    · have hdone : iterIndex = fibers.val.length := by omega
      simp only [hslice]
      unfold
        V5CoordinateSelectedProductionSource.circle_fri.selected_circle_fiber_points_shared_loop0.body
        core.slice.iter.IteratorSliceIter.next
      simp only [Slice.len_val, hactive, dite_false, bind_tc_ok, WP.spec_ok]
      unfold SourceSelectedPointsPost
      rw [← hdone]
      exact ⟨hlength, hrepresents⟩
  · unfold SourceSelectedPointsInvariant
    simp [hpoints]

private theorem released_domain_log_minus_two :
    U32.checked_sub 19#u32 2#u32 = some 17#u32 := by
  decide

private theorem released_circle_order_minus_one :
    (31#u32 - 1#u32 : Result Std.U32) = .ok 30#u32 := by
  rw [checked_sub_eq_wrapping]
  · congr 2
  · norm_num

private theorem released_checked_fiber_count :
    core.num.Usize.checked_shl 1#usize 17#u32 =
      .ok (some 131072#usize) := by
  unfold core.num.Usize.checked_shl
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    simp [hbits]
  all_goals
    apply UScalar.eq_of_val_eq
    simp [UScalar.val, hbits]

/-- At the released domain size, the public directly translated Rust helper
returns exactly the released circle point for every input fibre, in input
order. -/
theorem source_selected_circle_fiber_points_shared_domain19_exact
    (fibers : Slice Std.U32)
    (hrange : ∀ index, index < fibers.val.length →
      fibers.val[index]!.val < 131072) :
    ∃ output,
      V5CoordinateSelectedProductionSource.circle_fri.selected_circle_fiber_points_shared
          19#u32 fibers = .ok (.Ok output) ∧
        SourceSelectedPointsPost fibers output := by
  let initial : alloc.vec.Vec SourcePoint :=
    alloc.vec.Vec.with_capacity SourcePoint (Slice.len fibers)
  have hinitial : initial.val = [] := by
    rfl
  obtain ⟨loopOutput, hloop, hpost⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (source_selected_points_loop_exact fibers initial hinitial hrange)
  cases loopOutput with
  | Err error => simp at hpost
  | Ok output =>
      refine ⟨output, ?_, hpost⟩
      unfold
        V5CoordinateSelectedProductionSource.circle_fri.selected_circle_fiber_points_shared
      simpa [initial, released_domain_log_minus_two,
        V5CoordinateSelectedProductionSource.params.CIRCLE_LOG_ORDER,
        released_circle_order_minus_one, released_checked_fiber_count,
        Std.lift, core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,
        SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter]
        using hloop

#print axioms sourceSelectedPointCall_exact
#print axioms source_selected_points_loop_exact
#print axioms source_selected_circle_fiber_points_shared_domain19_exact

end V5CoordinateSelectedProductionProof
