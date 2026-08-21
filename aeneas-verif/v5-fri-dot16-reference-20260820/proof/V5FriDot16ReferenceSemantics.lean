import V5Dot16Reference.Funs
import M31ReduceU64Proof
import AspisFormal.V5ComponentCQM31TowerExact
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 6000

/-!
# Exact semantics of the fixed-index V5 FRI dot product

Kani proves that the unchanged production helper has exactly the same result
as the loop-free Rust function translated in `V5Dot16Reference.Funs`.  This
file proves that every successful generated call decodes the 64 little-endian
M31 words and returns the four exact 16-term field dot products.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open scoped BigOperators

namespace AspisV5FriDot16ReferenceSemantics

namespace Ref
open V5FriDot16ReferenceGenerated

abbrev M31 := aspis_core.field.M31
abbrev CM31 := aspis_core.field.CM31
abbrev QM31 := aspis_core.field.QM31

end Ref

local instance refQM31Inhabited : Inhabited Ref.QM31 where
  default :=
    { c0 := { a := 0#u32, b := 0#u32 }
      c1 := { a := 0#u32, b := 0#u32 } }

abbrev ExactM31 := AspisAeneasM31ReduceU64.M31Exact
abbrev modulus : Nat := AspisAeneasM31ReduceU64.m31Modulus

def canonicalM31 (value : Ref.M31) : Prop := value.val < modulus

def qm31Limb (value : Ref.QM31) (limb : Nat) : Ref.M31 :=
  if limb = 0 then value.c0.a else
  if limb = 1 then value.c0.b else
  if limb = 2 then value.c1.a else value.c1.b

def qm31LimbView (value : Ref.QM31) (limb : Nat) : ExactM31 :=
  ((qm31Limb value limb).val : ExactM31)

def byteOffset (slot index : Nat) : Nat := (slot * 16 + index) * 4

def wordArrayAt
    (bytes : Array Std.U8 256#usize) (slot index : Nat) :
    Array Std.U8 4#usize :=
  let offset := byteOffset slot index
  Array.make 4#usize [
    bytes.val[offset]!, bytes.val[offset + 1]!,
    bytes.val[offset + 2]!, bytes.val[offset + 3]!]

def decodedWord
    (bytes : Array Std.U8 256#usize) (slot index : Nat) : Std.U32 :=
  core.num.U32.from_le_bytes (wordArrayAt bytes slot index)

def decodedWordNat
    (bytes : Array Std.U8 256#usize) (slot index : Nat) : Nat :=
  (decodedWord bytes slot index).val

def weightNat
    (weights : Array (Array Std.U32 4#usize) 16#usize)
    (index limb : Nat) : Nat :=
  weights.val[index]!.val[limb]!.val

def CanonicalWeights
    (weights : Array (Array Std.U32 4#usize) 16#usize) : Prop :=
  ∀ index, index < 16 → ∀ limb, limb < 4 →
    weightNat weights index limb < modulus

def CanonicalWords (bytes : Array Std.U8 256#usize) : Prop :=
  ∀ slot, slot < 4 → ∀ index, index < 16 →
    decodedWordNat bytes slot index < modulus

def exactBlock
    (weights : Array (Array Std.U32 4#usize) 16#usize)
    (bytes : Array Std.U8 256#usize)
    (slot start limb : Nat) : ExactM31 :=
  (weightNat weights start limb : ExactM31) *
      (decodedWordNat bytes slot start : ExactM31) +
    (weightNat weights (start + 1) limb : ExactM31) *
      (decodedWordNat bytes slot (start + 1) : ExactM31) +
    (weightNat weights (start + 2) limb : ExactM31) *
      (decodedWordNat bytes slot (start + 2) : ExactM31) +
    (weightNat weights (start + 3) limb : ExactM31) *
      (decodedWordNat bytes slot (start + 3) : ExactM31)

def exactDot
    (weights : Array (Array Std.U32 4#usize) 16#usize)
    (bytes : Array Std.U8 256#usize)
    (slot limb : Nat) : ExactM31 :=
  exactBlock weights bytes slot 0 limb +
    exactBlock weights bytes slot 4 limb +
    exactBlock weights bytes slot 8 limb +
    exactBlock weights bytes slot 12 limb

def conventionalDot
    (weights : Array (Array Std.U32 4#usize) 16#usize)
    (bytes : Array Std.U8 256#usize)
    (slot limb : Nat) : ExactM31 :=
  ∑ index ∈ Finset.range 16,
    (weightNat weights index limb : ExactM31) *
      (decodedWordNat bytes slot index : ExactM31)

theorem exactDot_eq_conventionalDot
    (weights : Array (Array Std.U32 4#usize) 16#usize)
    (bytes : Array Std.U8 256#usize) (slot limb : Nat) :
    exactDot weights bytes slot limb =
      conventionalDot weights bytes slot limb := by
  simp [exactDot, exactBlock, conventionalDot, Finset.sum_range_succ]
  ring

private theorem reference_P_eq_reducer :
    V5FriDot16ReferenceGenerated.aspis_core.field.P =
      aspis_core.field.P := by
  apply UScalar.eq_of_val_eq
  unfold V5FriDot16ReferenceGenerated.aspis_core.field.P
    aspis_core.field.P
  rfl

private theorem reference_reduce_call_eq_reducer (value : Std.U64) :
    V5FriDot16ReferenceGenerated.aspis_core.field.reduce_u64 value =
      aspis_core.field.reduce_u64 value := by
  unfold V5FriDot16ReferenceGenerated.aspis_core.field.reduce_u64
    aspis_core.field.reduce_u64
  rw [reference_P_eq_reducer]

theorem generated_reduce_u64_corresponds (value : Std.U64) :
    ∃ out : Ref.M31,
      V5FriDot16ReferenceGenerated.aspis_core.field.M31.reduce_u64 value =
        ok out ∧
      canonicalM31 out ∧
      ((out.val : Nat) : ExactM31) = (value.val : ExactM31) := by
  rcases AspisAeneasM31ReduceU64.extracted_reduce_u64_corresponds value with
    ⟨out, hrun, _hraw, hcanonical, hexact⟩
  refine ⟨out, ?_, hcanonical, hexact⟩
  unfold V5FriDot16ReferenceGenerated.aspis_core.field.M31.reduce_u64
  rw [reference_reduce_call_eq_reducer, hrun]
  simp only [bind_tc_ok]

private theorem list_get_eq_getElemBang
    {T : Type} [Inhabited T]
    (values : List T) (index : Nat) (hIndex : index < values.length) :
    values[index] = values[index]! := by
  symm
  apply List.getElem!_of_getElem?
  simp [hIndex]

theorem generated_array_index_run
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (hIndex : index.val < N.val) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, hRun, hValue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hIndex))
  have hArrayBound : index.val < values.val.length := by
    simpa [Array.length_eq] using hIndex
  have hElem := list_get_eq_getElemBang values.val index.val hArrayBound
  simpa [hValue, hElem] using hRun

private theorem usize_size_gt_256 : 256 < Std.Usize.size := by
  rcases Usize.size_scalarTac_eq with ⟨hsize, _⟩
  rcases Usize.cMax_bound_concrete with ⟨hmax, _⟩
  omega

private theorem usize_wrapping_mul_small
    (left right : Std.Usize) (hbound : left.val * right.val < 257) :
    (Std.Usize.wrapping_mul left right).val = left.val * right.val := by
  rw [Std.Usize.wrapping_mul_val_eq]
  apply Nat.mod_eq_of_lt
  rw [UScalar.size_UScalarTyUsize]
  have hsize : 257 ≤ Std.Usize.size := by
    exact Nat.succ_le_of_lt usize_size_gt_256
  omega

private theorem usize_wrapping_add_small
    (left right : Std.Usize) (hbound : left.val + right.val < 257) :
    (Std.Usize.wrapping_add left right).val = left.val + right.val := by
  rw [Std.Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  rw [UScalar.size_UScalarTyUsize]
  have hsize : 257 ≤ Std.Usize.size := by
    exact Nat.succ_le_of_lt usize_size_gt_256
  omega

theorem read_word_corresponds
    (bytes : Array Std.U8 256#usize) (slot index : Std.Usize)
    (hslot : slot.val < 4) (hindex : index.val < 16) :
    V5FriDot16ReferenceGenerated.read_word bytes slot index =
      ok (
        core.convert.num.FromU64U32.from
          (decodedWord bytes slot.val index.val &&&
            V5FriDot16ReferenceGenerated.aspis_core.field.P),
        core.convert.num.FromU32Bool.from
          (decodedWord bytes slot.val index.val >=
            V5FriDot16ReferenceGenerated.aspis_core.field.P)) := by
  let scaled := Std.Usize.wrapping_mul slot 16#usize
  let base := Std.Usize.wrapping_add scaled index
  let offset := Std.Usize.wrapping_mul base 4#usize
  let offset1 := Std.Usize.wrapping_add offset 1#usize
  let offset2 := Std.Usize.wrapping_add offset 2#usize
  let offset3 := Std.Usize.wrapping_add offset 3#usize
  have hscaled : scaled.val = slot.val * 16 := by
    unfold scaled
    rw [usize_wrapping_mul_small slot 16#usize (by norm_num; omega)]
    rfl
  have hbase : base.val = slot.val * 16 + index.val := by
    have hsmall : scaled.val + index.val < 257 := by
      rw [hscaled]
      omega
    unfold base
    rw [usize_wrapping_add_small scaled index hsmall, hscaled]
  have hoffset : offset.val = byteOffset slot.val index.val := by
    have hsmall : base.val * (4#usize).val < 257 := by
      norm_num
      rw [hbase]
      omega
    unfold offset byteOffset
    rw [usize_wrapping_mul_small base 4#usize hsmall, hbase]
    norm_num
  have hoffset1 : offset1.val = byteOffset slot.val index.val + 1 := by
    have hsmall : offset.val + (1#usize).val < 257 := by
      norm_num
      rw [hoffset]
      unfold byteOffset
      omega
    unfold offset1
    rw [usize_wrapping_add_small offset 1#usize hsmall, hoffset]
    norm_num
  have hoffset2 : offset2.val = byteOffset slot.val index.val + 2 := by
    have hsmall : offset.val + (2#usize).val < 257 := by
      norm_num
      rw [hoffset]
      unfold byteOffset
      omega
    unfold offset2
    rw [usize_wrapping_add_small offset 2#usize hsmall, hoffset]
    norm_num
  have hoffset3 : offset3.val = byteOffset slot.val index.val + 3 := by
    have hsmall : offset.val + (3#usize).val < 257 := by
      norm_num
      rw [hoffset]
      unfold byteOffset
      omega
    unfold offset3
    rw [usize_wrapping_add_small offset 3#usize hsmall, hoffset]
    norm_num
  have h0bound : offset.val < 256 := by
    rw [hoffset]
    unfold byteOffset
    omega
  have h1bound : offset1.val < 256 := by
    rw [hoffset1]
    unfold byteOffset
    omega
  have h2bound : offset2.val < 256 := by
    rw [hoffset2]
    unfold byteOffset
    omega
  have h3bound : offset3.val < 256 := by
    rw [hoffset3]
    unfold byteOffset
    omega
  have h0 := generated_array_index_run bytes offset (by simpa using h0bound)
  have h1 := generated_array_index_run bytes offset1 (by simpa using h1bound)
  have h2 := generated_array_index_run bytes offset2 (by simpa using h2bound)
  have h3 := generated_array_index_run bytes offset3 (by simpa using h3bound)
  unfold V5FriDot16ReferenceGenerated.read_word
  simp only [Std.lift, bind_tc_ok]
  change
    (do
      let b0 ← Array.index_usize bytes offset
      let b1 ← Array.index_usize bytes offset1
      let b2 ← Array.index_usize bytes offset2
      let b3 ← Array.index_usize bytes offset3
      ok
        (core.convert.num.FromU64U32.from
            (core.num.U32.from_le_bytes
                (Array.make 4#usize [b0, b1, b2, b3]) &&&
              V5FriDot16ReferenceGenerated.aspis_core.field.P),
          core.convert.num.FromU32Bool.from
            (core.num.U32.from_le_bytes
                (Array.make 4#usize [b0, b1, b2, b3]) >=
              V5FriDot16ReferenceGenerated.aspis_core.field.P))) = _
  rw [h0, h1, h2, h3]
  simp only [bind_tc_ok]
  congr 3 <;>
    simp [decodedWord, wordArrayAt, hoffset, hoffset1, hoffset2, hoffset3]

def liftU32 (value : Std.U32) : Std.U64 :=
  core.convert.num.FromU64U32.from value

@[simp] theorem liftU32_val (value : Std.U32) :
    (liftU32 value).val = value.val := by
  simp [liftU32, core.convert.num.FromU64U32.from_val_eq]

def sourceRaw4
    (weights : Array (Array Std.U32 4#usize) 16#usize)
    (start : Nat) (values : Array Std.U64 4#usize) (limb : Nat) : Std.U64 :=
  let product := fun index valueIndex =>
    Std.U64.wrapping_mul
      (liftU32 weights.val[index]!.val[limb]!)
      values.val[valueIndex]!
  Std.U64.wrapping_add
    (Std.U64.wrapping_add
      (Std.U64.wrapping_add (product start 0) (product (start + 1) 1))
      (product (start + 2) 2))
    (product (start + 3) 3)

def raw4Nat
    (weights : Array (Array Std.U32 4#usize) 16#usize)
    (start : Nat) (values : Array Std.U64 4#usize) (limb : Nat) : Nat :=
  weightNat weights start limb * values.val[0]!.val +
    weightNat weights (start + 1) limb * values.val[1]!.val +
    weightNat weights (start + 2) limb * values.val[2]!.val +
    weightNat weights (start + 3) limb * values.val[3]!.val

def CanonicalBlockValues (values : Array Std.U64 4#usize) : Prop :=
  ∀ index, index < 4 → values.val[index]!.val < modulus

private theorem u64_wrapping_mul_exact (left right : Std.U64)
    (hBound : left.val * right.val < 2 ^ 64) :
    (Std.U64.wrapping_mul left right).val = left.val * right.val := by
  rw [Std.U64.wrapping_mul_val_eq]
  apply Nat.mod_eq_of_lt
  simpa [UScalar.size, Std.U64.size, Std.U64.numBits] using hBound

private theorem u64_wrapping_add_exact (left right : Std.U64)
    (hBound : left.val + right.val < 2 ^ 64) :
    (Std.U64.wrapping_add left right).val = left.val + right.val := by
  rw [Std.U64.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  simpa [UScalar.size, Std.U64.size, Std.U64.numBits] using hBound

theorem raw4_runs
    (weights : Array (Array Std.U32 4#usize) 16#usize)
    (start : Std.Usize) (values : Array Std.U64 4#usize)
    (limb : Std.Usize)
    (hstart : start.val + 3 < 16) (hlimb : limb.val < 4) :
    V5FriDot16ReferenceGenerated.raw4 weights start values limb =
      ok (sourceRaw4 weights start.val values limb.val) := by
  let start1 := Std.Usize.wrapping_add start 1#usize
  let start2 := Std.Usize.wrapping_add start 2#usize
  let start3 := Std.Usize.wrapping_add start 3#usize
  have hs1small : start.val + (1#usize).val < 257 := by
    norm_num
    omega
  have hs2small : start.val + (2#usize).val < 257 := by
    norm_num
    omega
  have hs3small : start.val + (3#usize).val < 257 := by
    norm_num
    omega
  have hs1 : start1.val = start.val + 1 := by
    unfold start1
    rw [usize_wrapping_add_small start 1#usize hs1small]
    norm_num
  have hs2 : start2.val = start.val + 2 := by
    unfold start2
    rw [usize_wrapping_add_small start 2#usize hs2small]
    norm_num
  have hs3 : start3.val = start.val + 3 := by
    unfold start3
    rw [usize_wrapping_add_small start 3#usize hs3small]
    norm_num
  have hw0bound : start.val < 16 := by omega
  have hw1bound : start1.val < 16 := by rw [hs1]; omega
  have hw2bound : start2.val < 16 := by rw [hs2]; omega
  have hw3bound : start3.val < 16 := by rw [hs3]; omega
  have hw0 := generated_array_index_run weights start (by simpa using hw0bound)
  have hw1 := generated_array_index_run weights start1 (by simpa using hw1bound)
  have hw2 := generated_array_index_run weights start2 (by simpa using hw2bound)
  have hw3 := generated_array_index_run weights start3 (by simpa using hw3bound)
  let w0 := weights.val[start.val]!
  let w1 := weights.val[start1.val]!
  let w2 := weights.val[start2.val]!
  let w3 := weights.val[start3.val]!
  have hw1eq : w1 = weights.val[start.val + 1]! := by simp [w1, hs1]
  have hw2eq : w2 = weights.val[start.val + 2]! := by simp [w2, hs2]
  have hw3eq : w3 = weights.val[start.val + 3]! := by simp [w3, hs3]
  have hw0l := generated_array_index_run w0 limb (by simpa using hlimb)
  have hw1l := generated_array_index_run w1 limb (by simpa using hlimb)
  have hw2l := generated_array_index_run w2 limb (by simpa using hlimb)
  have hw3l := generated_array_index_run w3 limb (by simpa using hlimb)
  have hv0 := generated_array_index_run values 0#usize (by norm_num)
  have hv1 := generated_array_index_run values 1#usize (by norm_num)
  have hv2 := generated_array_index_run values 2#usize (by norm_num)
  have hv3 := generated_array_index_run values 3#usize (by norm_num)
  unfold V5FriDot16ReferenceGenerated.raw4
  simp only [Std.lift, bind_tc_ok]
  change
    (do
      let a ← Array.index_usize weights start
      let x0 ← Array.index_usize a limb
      let v0 ← Array.index_usize values 0#usize
      let p0 := Std.U64.wrapping_mul (liftU32 x0) v0
      let a1 ← Array.index_usize weights start1
      let x1 ← Array.index_usize a1 limb
      let v1 ← Array.index_usize values 1#usize
      let p1 := Std.U64.wrapping_mul (liftU32 x1) v1
      let a2 ← Array.index_usize weights start2
      let x2 ← Array.index_usize a2 limb
      let v2 ← Array.index_usize values 2#usize
      let p2 := Std.U64.wrapping_mul (liftU32 x2) v2
      let a3 ← Array.index_usize weights start3
      let x3 ← Array.index_usize a3 limb
      let v3 ← Array.index_usize values 3#usize
      let p3 := Std.U64.wrapping_mul (liftU32 x3) v3
      ok (Std.U64.wrapping_add
        (Std.U64.wrapping_add (Std.U64.wrapping_add p0 p1) p2) p3)) = _
  rw [hw0, hw1, hw2, hw3]
  simp only [bind_tc_ok]
  change
    (do
      let x0 ← Array.index_usize w0 limb
      let v0 ← Array.index_usize values 0#usize
      let p0 := Std.U64.wrapping_mul (liftU32 x0) v0
      let x1 ← Array.index_usize w1 limb
      let v1 ← Array.index_usize values 1#usize
      let p1 := Std.U64.wrapping_mul (liftU32 x1) v1
      let x2 ← Array.index_usize w2 limb
      let v2 ← Array.index_usize values 2#usize
      let p2 := Std.U64.wrapping_mul (liftU32 x2) v2
      let x3 ← Array.index_usize w3 limb
      let v3 ← Array.index_usize values 3#usize
      let p3 := Std.U64.wrapping_mul (liftU32 x3) v3
      ok (Std.U64.wrapping_add
        (Std.U64.wrapping_add (Std.U64.wrapping_add p0 p1) p2) p3)) = _
  rw [hw0l, hw1l, hw2l, hw3l, hv0, hv1, hv2, hv3]
  simp only [bind_tc_ok]
  congr 2
  simp [w0, hw1eq, hw2eq]
  rw [hw3eq]
  rfl

theorem sourceRaw4_val_exact
    (weights : Array (Array Std.U32 4#usize) 16#usize)
    (start : Nat) (values : Array Std.U64 4#usize) (limb : Nat)
    (hstart : start + 3 < 16) (hlimb : limb < 4)
    (hweights : CanonicalWeights weights)
    (hvalues : CanonicalBlockValues values) :
    (sourceRaw4 weights start values limb).val =
      raw4Nat weights start values limb := by
  have hw0 := hweights start (by omega) limb hlimb
  have hw1 := hweights (start + 1) (by omega) limb hlimb
  have hw2 := hweights (start + 2) (by omega) limb hlimb
  have hw3 := hweights (start + 3) hstart limb hlimb
  have hv0 := hvalues 0 (by omega)
  have hv1 := hvalues 1 (by omega)
  have hv2 := hvalues 2 (by omega)
  have hv3 := hvalues 3 (by omega)
  let p0 := Std.U64.wrapping_mul
    (liftU32 weights.val[start]!.val[limb]!) values.val[0]!
  let p1 := Std.U64.wrapping_mul
    (liftU32 weights.val[start + 1]!.val[limb]!) values.val[1]!
  let p2 := Std.U64.wrapping_mul
    (liftU32 weights.val[start + 2]!.val[limb]!) values.val[2]!
  let p3 := Std.U64.wrapping_mul
    (liftU32 weights.val[start + 3]!.val[limb]!) values.val[3]!
  have hp0 : p0.val = weightNat weights start limb * values.val[0]!.val := by
    unfold p0 weightNat
    rw [u64_wrapping_mul_exact]
    · simp
    · simp only [liftU32_val]
      calc
        weights.val[start]!.val[limb]!.val * values.val[0]!.val
            ≤ (modulus - 1) * (modulus - 1) :=
          Nat.mul_le_mul (Nat.le_pred_of_lt hw0) (Nat.le_pred_of_lt hv0)
        _ < 2 ^ 64 := by norm_num [modulus]
  have hp1 : p1.val = weightNat weights (start + 1) limb * values.val[1]!.val := by
    unfold p1 weightNat
    rw [u64_wrapping_mul_exact]
    · simp
    · simp only [liftU32_val]
      calc
        weights.val[start + 1]!.val[limb]!.val * values.val[1]!.val
            ≤ (modulus - 1) * (modulus - 1) :=
          Nat.mul_le_mul (Nat.le_pred_of_lt hw1) (Nat.le_pred_of_lt hv1)
        _ < 2 ^ 64 := by norm_num [modulus]
  have hp2 : p2.val = weightNat weights (start + 2) limb * values.val[2]!.val := by
    unfold p2 weightNat
    rw [u64_wrapping_mul_exact]
    · simp
    · simp only [liftU32_val]
      calc
        weights.val[start + 2]!.val[limb]!.val * values.val[2]!.val
            ≤ (modulus - 1) * (modulus - 1) :=
          Nat.mul_le_mul (Nat.le_pred_of_lt hw2) (Nat.le_pred_of_lt hv2)
        _ < 2 ^ 64 := by norm_num [modulus]
  have hp3 : p3.val = weightNat weights (start + 3) limb * values.val[3]!.val := by
    unfold p3 weightNat
    rw [u64_wrapping_mul_exact]
    · simp
    · simp only [liftU32_val]
      calc
        weights.val[start + 3]!.val[limb]!.val * values.val[3]!.val
            ≤ (modulus - 1) * (modulus - 1) :=
          Nat.mul_le_mul (Nat.le_pred_of_lt hw3) (Nat.le_pred_of_lt hv3)
        _ < 2 ^ 64 := by norm_num [modulus]
  let s01 := Std.U64.wrapping_add p0 p1
  let s012 := Std.U64.wrapping_add s01 p2
  have hs01 : s01.val = p0.val + p1.val := by
    unfold s01
    rw [u64_wrapping_add_exact]
    rw [hp0, hp1]
    have h0 : weightNat weights start limb ≤ modulus - 1 := Nat.le_pred_of_lt hw0
    have h1 : weightNat weights (start + 1) limb ≤ modulus - 1 :=
      Nat.le_pred_of_lt hw1
    have v0 : values.val[0]!.val ≤ modulus - 1 := Nat.le_pred_of_lt hv0
    have v1 : values.val[1]!.val ≤ modulus - 1 := Nat.le_pred_of_lt hv1
    nlinarith [show 2 * (modulus - 1) ^ 2 < 2 ^ 64 by norm_num [modulus]]
  have hs012 : s012.val = p0.val + p1.val + p2.val := by
    have hbound : s01.val + p2.val < 2 ^ 64 := by
      rw [hs01, hp0, hp1, hp2]
      have h0 : weightNat weights start limb ≤ modulus - 1 :=
        Nat.le_pred_of_lt hw0
      have h1 : weightNat weights (start + 1) limb ≤ modulus - 1 :=
        Nat.le_pred_of_lt hw1
      have h2 : weightNat weights (start + 2) limb ≤ modulus - 1 :=
        Nat.le_pred_of_lt hw2
      have v0 : values.val[0]!.val ≤ modulus - 1 := Nat.le_pred_of_lt hv0
      have v1 : values.val[1]!.val ≤ modulus - 1 := Nat.le_pred_of_lt hv1
      have v2 : values.val[2]!.val ≤ modulus - 1 := Nat.le_pred_of_lt hv2
      nlinarith [show 3 * (modulus - 1) ^ 2 < 2 ^ 64 by norm_num [modulus]]
    unfold s012
    rw [u64_wrapping_add_exact s01 p2 hbound, hs01]
  unfold sourceRaw4 raw4Nat
  change (Std.U64.wrapping_add s012 p3).val = _
  have h0 : weightNat weights start limb ≤ modulus - 1 := Nat.le_pred_of_lt hw0
  have h1 : weightNat weights (start + 1) limb ≤ modulus - 1 :=
    Nat.le_pred_of_lt hw1
  have h2 : weightNat weights (start + 2) limb ≤ modulus - 1 :=
    Nat.le_pred_of_lt hw2
  have h3 : weightNat weights (start + 3) limb ≤ modulus - 1 :=
    Nat.le_pred_of_lt hw3
  have v0 : values.val[0]!.val ≤ modulus - 1 := Nat.le_pred_of_lt hv0
  have v1 : values.val[1]!.val ≤ modulus - 1 := Nat.le_pred_of_lt hv1
  have v2 : values.val[2]!.val ≤ modulus - 1 := Nat.le_pred_of_lt hv2
  have v3 : values.val[3]!.val ≤ modulus - 1 := Nat.le_pred_of_lt hv3
  have hbound : s012.val + p3.val < 2 ^ 64 := by
    rw [hs012, hp0, hp1, hp2, hp3]
    nlinarith [show 4 * (modulus - 1) ^ 2 < 2 ^ 64 by norm_num [modulus]]
  rw [u64_wrapping_add_exact s012 p3 hbound, hs012, hp0, hp1, hp2, hp3]

theorem raw4_corresponds
    (weights : Array (Array Std.U32 4#usize) 16#usize)
    (start : Std.Usize) (values : Array Std.U64 4#usize)
    (limb : Std.Usize)
    (hstart : start.val + 3 < 16) (hlimb : limb.val < 4)
    (hweights : CanonicalWeights weights)
    (hvalues : CanonicalBlockValues values) :
    ∃ out : Std.U64,
      V5FriDot16ReferenceGenerated.raw4 weights start values limb = ok out ∧
      out.val = raw4Nat weights start.val values limb.val ∧
      ((out.val : Nat) : ExactM31) =
        (raw4Nat weights start.val values limb.val : ExactM31) := by
  refine ⟨sourceRaw4 weights start.val values limb.val,
    raw4_runs weights start values limb hstart hlimb, ?_, ?_⟩
  · exact sourceRaw4_val_exact weights start.val values limb.val hstart hlimb
      hweights hvalues
  · rw [sourceRaw4_val_exact weights start.val values limb.val hstart hlimb
      hweights hvalues]

def maskedWord
    (bytes : Array Std.U8 256#usize) (slot index : Nat) : Std.U64 :=
  liftU32 (decodedWord bytes slot index &&&
    V5FriDot16ReferenceGenerated.aspis_core.field.P)

def invalidWord
    (bytes : Array Std.U8 256#usize) (slot index : Nat) : Std.U32 :=
  core.convert.num.FromU32Bool.from
    (decodedWord bytes slot index >=
      V5FriDot16ReferenceGenerated.aspis_core.field.P)

def blockValues
    (bytes : Array Std.U8 256#usize) (slot start : Nat) :
    Array Std.U64 4#usize :=
  Array.make 4#usize [
    maskedWord bytes slot start,
    maskedWord bytes slot (start + 1),
    maskedWord bytes slot (start + 2),
    maskedWord bytes slot (start + 3)]

def blockInvalid
    (bytes : Array Std.U8 256#usize) (slot start : Nat) : Std.U32 :=
  (((invalidWord bytes slot start) |||
      (invalidWord bytes slot (start + 1))) |||
    (invalidWord bytes slot (start + 2))) |||
  (invalidWord bytes slot (start + 3))

def rawBlockArray
    (weights : Array (Array Std.U32 4#usize) 16#usize)
    (bytes : Array Std.U8 256#usize) (slot start : Nat) :
    Array Std.U64 4#usize :=
  let values := blockValues bytes slot start
  Array.make 4#usize [
    sourceRaw4 weights start values 0,
    sourceRaw4 weights start values 1,
    sourceRaw4 weights start values 2,
    sourceRaw4 weights start values 3]

theorem maskedWord_val_of_canonical
    (bytes : Array Std.U8 256#usize) (slot index : Nat)
    (hcanonical : decodedWordNat bytes slot index < modulus) :
    (maskedWord bytes slot index).val = decodedWordNat bytes slot index := by
  have hcanonical' : (decodedWord bytes slot index).val < 2147483647 := by
    simpa [decodedWordNat, modulus] using hcanonical
  unfold maskedWord liftU32 decodedWordNat
  simp only [core.convert.num.FromU64U32.from_val_eq]
  rw [UScalar.val_and]
  rw [reference_P_eq_reducer]
  unfold aspis_core.field.P
  change (decodedWord bytes slot index).val &&& 2147483647 =
    (decodedWord bytes slot index).val
  rw [show 2147483647 = 2 ^ 31 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]
  apply Nat.mod_eq_of_lt
  norm_num
  omega

theorem invalidWord_eq_zero_of_canonical
    (bytes : Array Std.U8 256#usize) (slot index : Nat)
    (hcanonical : decodedWordNat bytes slot index < modulus) :
    invalidWord bytes slot index = 0#u32 := by
  have hcanonical' : (decodedWord bytes slot index).val < 2147483647 := by
    simpa [decodedWordNat, modulus] using hcanonical
  unfold invalidWord
  rw [reference_P_eq_reducer]
  unfold aspis_core.field.P
  have hnot : ¬2147483647 ≤ (decodedWord bytes slot index).val :=
    Nat.not_le_of_lt hcanonical'
  simp [core.convert.num.FromU32Bool.from, hnot]

theorem blockValues_canonical
    (bytes : Array Std.U8 256#usize) (slot start : Nat)
    (hslot : slot < 4) (hstart : start + 3 < 16)
    (hwords : CanonicalWords bytes) :
    CanonicalBlockValues (blockValues bytes slot start) := by
  intro index hindex
  have hi : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl
  · change (maskedWord bytes slot start).val < modulus
    rw [maskedWord_val_of_canonical bytes slot start
      (hwords slot hslot start (by omega))]
    exact hwords slot hslot start (by omega)
  · change (maskedWord bytes slot (start + 1)).val < modulus
    rw [maskedWord_val_of_canonical bytes slot (start + 1)
      (hwords slot hslot (start + 1) (by omega))]
    exact hwords slot hslot (start + 1) (by omega)
  · change (maskedWord bytes slot (start + 2)).val < modulus
    rw [maskedWord_val_of_canonical bytes slot (start + 2)
      (hwords slot hslot (start + 2) (by omega))]
    exact hwords slot hslot (start + 2) (by omega)
  · change (maskedWord bytes slot (start + 3)).val < modulus
    rw [maskedWord_val_of_canonical bytes slot (start + 3)
      (hwords slot hslot (start + 3) hstart)]
    exact hwords slot hslot (start + 3) hstart

theorem blockInvalid_eq_zero
    (bytes : Array Std.U8 256#usize) (slot start : Nat)
    (hslot : slot < 4) (hstart : start + 3 < 16)
    (hwords : CanonicalWords bytes) :
    blockInvalid bytes slot start = 0#u32 := by
  have h0 := invalidWord_eq_zero_of_canonical bytes slot start
    (hwords slot hslot start (by omega))
  have h1 := invalidWord_eq_zero_of_canonical bytes slot (start + 1)
    (hwords slot hslot (start + 1) (by omega))
  have h2 := invalidWord_eq_zero_of_canonical bytes slot (start + 2)
    (hwords slot hslot (start + 2) (by omega))
  have h3 := invalidWord_eq_zero_of_canonical bytes slot (start + 3)
    (hwords slot hslot (start + 3) hstart)
  rw [show blockInvalid bytes slot start =
      (((invalidWord bytes slot start ||| invalidWord bytes slot (start + 1)) |||
        invalidWord bytes slot (start + 2)) |||
        invalidWord bytes slot (start + 3)) by rfl,
    h0, h1, h2, h3]
  rfl

theorem block4_runs
    (weights : Array (Array Std.U32 4#usize) 16#usize)
    (bytes : Array Std.U8 256#usize) (slot start : Std.Usize)
    (hslot : slot.val < 4) (hstart : start.val + 3 < 16) :
    V5FriDot16ReferenceGenerated.block4 weights bytes slot start =
      ok (rawBlockArray weights bytes slot.val start.val,
        blockInvalid bytes slot.val start.val) := by
  let start1 := Std.Usize.wrapping_add start 1#usize
  let start2 := Std.Usize.wrapping_add start 2#usize
  let start3 := Std.Usize.wrapping_add start 3#usize
  have hs1 : start1.val = start.val + 1 := by
    unfold start1
    rw [usize_wrapping_add_small start 1#usize (by norm_num; omega)]
    norm_num
  have hs2 : start2.val = start.val + 2 := by
    unfold start2
    rw [usize_wrapping_add_small start 2#usize (by norm_num; omega)]
    norm_num
  have hs3 : start3.val = start.val + 3 := by
    unfold start3
    rw [usize_wrapping_add_small start 3#usize (by norm_num; omega)]
    norm_num
  have hr0 := read_word_corresponds bytes slot start hslot (by omega)
  have hr1 := read_word_corresponds bytes slot start1 hslot (by rw [hs1]; omega)
  have hr2 := read_word_corresponds bytes slot start2 hslot (by rw [hs2]; omega)
  have hr3 := read_word_corresponds bytes slot start3 hslot (by rw [hs3]; omega)
  have hr0' : V5FriDot16ReferenceGenerated.read_word bytes slot start =
      ok (maskedWord bytes slot.val start.val,
        invalidWord bytes slot.val start.val) := by
    simpa [maskedWord, invalidWord, liftU32] using hr0
  have hr1' : V5FriDot16ReferenceGenerated.read_word bytes slot start1 =
      ok (maskedWord bytes slot.val (start.val + 1),
        invalidWord bytes slot.val (start.val + 1)) := by
    simpa [maskedWord, invalidWord, liftU32, hs1] using hr1
  have hr2' : V5FriDot16ReferenceGenerated.read_word bytes slot start2 =
      ok (maskedWord bytes slot.val (start.val + 2),
        invalidWord bytes slot.val (start.val + 2)) := by
    simpa [maskedWord, invalidWord, liftU32, hs2] using hr2
  have hr3' : V5FriDot16ReferenceGenerated.read_word bytes slot start3 =
      ok (maskedWord bytes slot.val (start.val + 3),
        invalidWord bytes slot.val (start.val + 3)) := by
    simpa [maskedWord, invalidWord, liftU32, hs3] using hr3
  let values := blockValues bytes slot.val start.val
  have hv : values = Array.make 4#usize [
      maskedWord bytes slot.val start.val,
      maskedWord bytes slot.val (start.val + 1),
      maskedWord bytes slot.val (start.val + 2),
      maskedWord bytes slot.val (start.val + 3)] := by rfl
  have hraw0 := raw4_runs weights start values 0#usize hstart (by norm_num)
  have hraw1 := raw4_runs weights start values 1#usize hstart (by norm_num)
  have hraw2 := raw4_runs weights start values 2#usize hstart (by norm_num)
  have hraw3 := raw4_runs weights start values 3#usize hstart (by norm_num)
  unfold V5FriDot16ReferenceGenerated.block4
  simp only [Std.lift, bind_tc_ok]
  rw [show Std.Usize.wrapping_add start 1#usize = start1 by rfl,
    show Std.Usize.wrapping_add start 2#usize = start2 by rfl,
    show Std.Usize.wrapping_add start 3#usize = start3 by rfl]
  rw [hr0', hr1', hr2', hr3']
  simp only [bind_tc_ok]
  rw [← hv, hraw0, hraw1, hraw2, hraw3]
  simp only [bind_tc_ok]
  rfl

theorem rawBlockArray_exact
    (weights : Array (Array Std.U32 4#usize) 16#usize)
    (bytes : Array Std.U8 256#usize) (slot start limb : Nat)
    (hslot : slot < 4) (hstart : start + 3 < 16) (hlimb : limb < 4)
    (hweights : CanonicalWeights weights) (hwords : CanonicalWords bytes) :
    (((rawBlockArray weights bytes slot start).val[limb]!.val : Nat) :
        ExactM31) = exactBlock weights bytes slot start limb := by
  let values := blockValues bytes slot start
  have hvalues := blockValues_canonical bytes slot start hslot hstart hwords
  have hsource := sourceRaw4_val_exact weights start values limb hstart hlimb
    hweights hvalues
  have hm0 := maskedWord_val_of_canonical bytes slot start
    (hwords slot hslot start (by omega))
  have hm1 := maskedWord_val_of_canonical bytes slot (start + 1)
    (hwords slot hslot (start + 1) (by omega))
  have hm2 := maskedWord_val_of_canonical bytes slot (start + 2)
    (hwords slot hslot (start + 2) (by omega))
  have hm3 := maskedWord_val_of_canonical bytes slot (start + 3)
    (hwords slot hslot (start + 3) hstart)
  have hv0 : values.val[0]!.val = decodedWordNat bytes slot start := by
    change (maskedWord bytes slot start).val = _
    exact hm0
  have hv1 : values.val[1]!.val = decodedWordNat bytes slot (start + 1) := by
    change (maskedWord bytes slot (start + 1)).val = _
    exact hm1
  have hv2 : values.val[2]!.val = decodedWordNat bytes slot (start + 2) := by
    change (maskedWord bytes slot (start + 2)).val = _
    exact hm2
  have hv3 : values.val[3]!.val = decodedWordNat bytes slot (start + 3) := by
    change (maskedWord bytes slot (start + 3)).val = _
    exact hm3
  have hi : limb = 0 ∨ limb = 1 ∨ limb = 2 ∨ limb = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl
  all_goals
    simp [rawBlockArray, Array.make]
    change (((sourceRaw4 weights start values _).val : Nat) : ExactM31) = _
    rw [hsource]
    unfold raw4Nat exactBlock
    rw [hv0, hv1, hv2, hv3]
    push_cast
    rfl

def reducedLimbSum
    (b0 b1 b2 b3 : Array Std.U64 4#usize) (limb : Nat) : ExactM31 :=
  ((b0.val[limb]!.val : Nat) : ExactM31) +
    ((b1.val[limb]!.val : Nat) : ExactM31) +
    ((b2.val[limb]!.val : Nat) : ExactM31) +
    ((b3.val[limb]!.val : Nat) : ExactM31)

theorem reduce4_corresponds
    (b0 b1 b2 b3 : Array Std.U64 4#usize) (limb : Std.Usize)
    (hlimb : limb.val < 4) :
    ∃ out : Ref.M31,
      V5FriDot16ReferenceGenerated.reduce4 b0 b1 b2 b3 limb = ok out ∧
      canonicalM31 out ∧
      ((out.val : Nat) : ExactM31) =
        reducedLimbSum b0 b1 b2 b3 limb.val := by
  let v0 := b0.val[limb.val]!
  let v1 := b1.val[limb.val]!
  let v2 := b2.val[limb.val]!
  let v3 := b3.val[limb.val]!
  have hb0 := generated_array_index_run b0 limb (by simpa using hlimb)
  have hb1 := generated_array_index_run b1 limb (by simpa using hlimb)
  have hb2 := generated_array_index_run b2 limb (by simpa using hlimb)
  have hb3 := generated_array_index_run b3 limb (by simpa using hlimb)
  rcases generated_reduce_u64_corresponds v0 with
    ⟨m0, hm0run, hm0canonical, hm0exact⟩
  rcases generated_reduce_u64_corresponds v1 with
    ⟨m1, hm1run, hm1canonical, hm1exact⟩
  rcases generated_reduce_u64_corresponds v2 with
    ⟨m2, hm2run, hm2canonical, hm2exact⟩
  rcases generated_reduce_u64_corresponds v3 with
    ⟨m3, hm3run, hm3canonical, hm3exact⟩
  let u0 := liftU32 m0
  let u1 := liftU32 m1
  let u2 := liftU32 m2
  let u3 := liftU32 m3
  let s01 := Std.U64.wrapping_add u0 u1
  let s012 := Std.U64.wrapping_add s01 u2
  let total := Std.U64.wrapping_add s012 u3
  have hu0 : u0.val = m0.val := by simp [u0]
  have hu1 : u1.val = m1.val := by simp [u1]
  have hu2 : u2.val = m2.val := by simp [u2]
  have hu3 : u3.val = m3.val := by simp [u3]
  have hs01 : s01.val = m0.val + m1.val := by
    unfold s01
    rw [u64_wrapping_add_exact]
    · simp [hu0, hu1]
    · rw [hu0, hu1]
      have h0 := Nat.le_pred_of_lt hm0canonical
      have h1 := Nat.le_pred_of_lt hm1canonical
      calc
        m0.val + m1.val ≤ 2 * modulus.pred := by omega
        _ < 2 ^ 64 := by norm_num [modulus]
  have hs012 : s012.val = m0.val + m1.val + m2.val := by
    unfold s012
    rw [u64_wrapping_add_exact]
    · rw [hs01, hu2]
    · rw [hs01, hu2]
      have h0 := Nat.le_pred_of_lt hm0canonical
      have h1 := Nat.le_pred_of_lt hm1canonical
      have h2 := Nat.le_pred_of_lt hm2canonical
      calc
        m0.val + m1.val + m2.val ≤ 3 * modulus.pred := by omega
        _ < 2 ^ 64 := by norm_num [modulus]
  have htotal : total.val = m0.val + m1.val + m2.val + m3.val := by
    unfold total
    rw [u64_wrapping_add_exact]
    · rw [hs012, hu3]
    · rw [hs012, hu3]
      have h0 := Nat.le_pred_of_lt hm0canonical
      have h1 := Nat.le_pred_of_lt hm1canonical
      have h2 := Nat.le_pred_of_lt hm2canonical
      have h3 := Nat.le_pred_of_lt hm3canonical
      calc
        m0.val + m1.val + m2.val + m3.val ≤
            4 * modulus.pred := by omega
        _ < 2 ^ 64 := by norm_num [modulus]
  rcases generated_reduce_u64_corresponds total with
    ⟨out, houtrun, houtcanonical, houtexact⟩
  refine ⟨out, ?_, houtcanonical, ?_⟩
  · unfold V5FriDot16ReferenceGenerated.reduce4
    simp only [Std.lift, bind_tc_ok]
    rw [hb0, hb1, hb2, hb3]
    simp only [bind_tc_ok]
    change
      (do
        let m0' ← V5FriDot16ReferenceGenerated.aspis_core.field.M31.reduce_u64 v0
        let m1' ← V5FriDot16ReferenceGenerated.aspis_core.field.M31.reduce_u64 v1
        let s01' := Std.U64.wrapping_add (liftU32 m0') (liftU32 m1')
        let m2' ← V5FriDot16ReferenceGenerated.aspis_core.field.M31.reduce_u64 v2
        let s012' := Std.U64.wrapping_add s01' (liftU32 m2')
        let m3' ← V5FriDot16ReferenceGenerated.aspis_core.field.M31.reduce_u64 v3
        let total' := Std.U64.wrapping_add s012' (liftU32 m3')
        V5FriDot16ReferenceGenerated.aspis_core.field.M31.reduce_u64 total') = _
    rw [hm0run, hm1run, hm2run, hm3run]
    simp only [bind_tc_ok]
    change V5FriDot16ReferenceGenerated.aspis_core.field.M31.reduce_u64 total = _
    exact houtrun
  · rw [houtexact, htotal]
    unfold reducedLimbSum
    push_cast
    rw [hm0exact, hm1exact, hm2exact, hm3exact]

theorem reducedRawBlocks_exact
    (weights : Array (Array Std.U32 4#usize) 16#usize)
    (bytes : Array Std.U8 256#usize) (slot limb : Nat)
    (hslot : slot < 4) (hlimb : limb < 4)
    (hweights : CanonicalWeights weights) (hwords : CanonicalWords bytes) :
    reducedLimbSum
        (rawBlockArray weights bytes slot 0)
        (rawBlockArray weights bytes slot 4)
        (rawBlockArray weights bytes slot 8)
        (rawBlockArray weights bytes slot 12) limb =
      exactDot weights bytes slot limb := by
  unfold reducedLimbSum exactDot
  rw [rawBlockArray_exact weights bytes slot 0 limb hslot (by omega) hlimb
      hweights hwords,
    rawBlockArray_exact weights bytes slot 4 limb hslot (by omega) hlimb
      hweights hwords,
    rawBlockArray_exact weights bytes slot 8 limb hslot (by omega) hlimb
      hweights hwords,
    rawBlockArray_exact weights bytes slot 12 limb hslot (by omega) hlimb
      hweights hwords]

theorem slot_dot_corresponds
    (weights : Array (Array Std.U32 4#usize) 16#usize)
    (bytes : Array Std.U8 256#usize) (slot : Std.Usize)
    (hslot : slot.val < 4)
    (hweights : CanonicalWeights weights) (hwords : CanonicalWords bytes) :
    ∃ out : Ref.QM31,
      V5FriDot16ReferenceGenerated.slot_dot weights bytes slot =
        ok (out, 0#u32) ∧
      ∀ limb, limb < 4 →
        canonicalM31 (qm31Limb out limb) ∧
        qm31LimbView out limb = exactDot weights bytes slot.val limb := by
  let b0 := rawBlockArray weights bytes slot.val (0#usize).val
  let b1 := rawBlockArray weights bytes slot.val (4#usize).val
  let b2 := rawBlockArray weights bytes slot.val (8#usize).val
  let b3 := rawBlockArray weights bytes slot.val (12#usize).val
  have hb0 := block4_runs weights bytes slot 0#usize hslot (by norm_num)
  have hb1 := block4_runs weights bytes slot 4#usize hslot (by norm_num)
  have hb2 := block4_runs weights bytes slot 8#usize hslot (by norm_num)
  have hb3 := block4_runs weights bytes slot 12#usize hslot (by norm_num)
  have he0 := blockInvalid_eq_zero bytes slot.val (0#usize).val hslot
    (by norm_num) hwords
  have he1 := blockInvalid_eq_zero bytes slot.val (4#usize).val hslot
    (by norm_num) hwords
  have he2 := blockInvalid_eq_zero bytes slot.val (8#usize).val hslot
    (by norm_num) hwords
  have he3 := blockInvalid_eq_zero bytes slot.val (12#usize).val hslot
    (by norm_num) hwords
  rcases reduce4_corresponds b0 b1 b2 b3 0#usize (by norm_num) with
    ⟨m0, hm0run, hm0canonical, hm0exact⟩
  rcases reduce4_corresponds b0 b1 b2 b3 1#usize (by norm_num) with
    ⟨m1, hm1run, hm1canonical, hm1exact⟩
  rcases reduce4_corresponds b0 b1 b2 b3 2#usize (by norm_num) with
    ⟨m2, hm2run, hm2canonical, hm2exact⟩
  rcases reduce4_corresponds b0 b1 b2 b3 3#usize (by norm_num) with
    ⟨m3, hm3run, hm3canonical, hm3exact⟩
  have hm0dot : ((m0.val : Nat) : ExactM31) =
      exactDot weights bytes slot.val 0 := by
    rw [hm0exact]
    exact reducedRawBlocks_exact weights bytes slot.val 0 hslot (by omega)
      hweights hwords
  have hm1dot : ((m1.val : Nat) : ExactM31) =
      exactDot weights bytes slot.val 1 := by
    rw [hm1exact]
    exact reducedRawBlocks_exact weights bytes slot.val 1 hslot (by omega)
      hweights hwords
  have hm2dot : ((m2.val : Nat) : ExactM31) =
      exactDot weights bytes slot.val 2 := by
    rw [hm2exact]
    exact reducedRawBlocks_exact weights bytes slot.val 2 hslot (by omega)
      hweights hwords
  have hm3dot : ((m3.val : Nat) : ExactM31) =
      exactDot weights bytes slot.val 3 := by
    rw [hm3exact]
    exact reducedRawBlocks_exact weights bytes slot.val 3 hslot (by omega)
      hweights hwords
  let c0 : Ref.CM31 := { a := m0, b := m1 }
  let c1 : Ref.CM31 := { a := m2, b := m3 }
  let out : Ref.QM31 := { c0, c1 }
  refine ⟨out, ?_, ?_⟩
  · unfold V5FriDot16ReferenceGenerated.slot_dot
    rw [hb0]
    simp only [bind_tc_ok]
    rw [hb1]
    simp only [bind_tc_ok]
    rw [hb2]
    simp only [bind_tc_ok]
    rw [hb3]
    simp only [bind_tc_ok]
    rw [hm0run]
    simp only [bind_tc_ok]
    rw [hm1run]
    simp only [bind_tc_ok,
      V5FriDot16ReferenceGenerated.aspis_core.field.CM31.new]
    rw [hm2run]
    simp only [bind_tc_ok]
    rw [hm3run]
    simp only [bind_tc_ok]
    rw [he0, he1, he2, he3]
    rfl
  · intro limb hlimb
    have hi : limb = 0 ∨ limb = 1 ∨ limb = 2 ∨ limb = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl
    · exact ⟨hm0canonical, hm0dot⟩
    · exact ⟨hm1canonical, hm1dot⟩
    · exact ⟨hm2canonical, hm2dot⟩
    · exact ⟨hm3canonical, hm3dot⟩

theorem indexed_dot16_corresponds
    (weights : Array (Array Std.U32 4#usize) 16#usize)
    (bytes : Array Std.U8 256#usize)
    (hweights : CanonicalWeights weights) (hwords : CanonicalWords bytes) :
    ∃ out : Array Ref.QM31 4#usize,
      V5FriDot16ReferenceGenerated.indexed_dot16 weights bytes =
        ok (some out) ∧
      ∀ slot, slot < 4 → ∀ limb, limb < 4 →
        canonicalM31 (qm31Limb out.val[slot]! limb) ∧
        qm31LimbView out.val[slot]! limb =
          conventionalDot weights bytes slot limb := by
  rcases slot_dot_corresponds weights bytes 0#usize (by norm_num)
      hweights hwords with ⟨v0, hv0run, hv0⟩
  rcases slot_dot_corresponds weights bytes 1#usize (by norm_num)
      hweights hwords with ⟨v1, hv1run, hv1⟩
  rcases slot_dot_corresponds weights bytes 2#usize (by norm_num)
      hweights hwords with ⟨v2, hv2run, hv2⟩
  rcases slot_dot_corresponds weights bytes 3#usize (by norm_num)
      hweights hwords with ⟨v3, hv3run, hv3⟩
  let out : Array Ref.QM31 4#usize := Array.make 4#usize [v0, v1, v2, v3]
  refine ⟨out, ?_, ?_⟩
  · unfold V5FriDot16ReferenceGenerated.indexed_dot16
    rw [hv0run]
    simp only [bind_tc_ok]
    rw [hv1run]
    simp only [bind_tc_ok]
    rw [hv2run]
    simp only [bind_tc_ok]
    rw [hv3run]
    simp only [bind_tc_ok]
    rfl
  · intro slot hslot limb hlimb
    have hs : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by omega
    rcases hs with rfl | rfl | rfl | rfl
    · change canonicalM31 (qm31Limb v0 limb) ∧
        qm31LimbView v0 limb = conventionalDot weights bytes 0 limb
      rcases hv0 limb hlimb with ⟨hcanonical, hexact⟩
      exact ⟨hcanonical, hexact.trans
        (exactDot_eq_conventionalDot weights bytes 0 limb)⟩
    · change canonicalM31 (qm31Limb v1 limb) ∧
        qm31LimbView v1 limb = conventionalDot weights bytes 1 limb
      rcases hv1 limb hlimb with ⟨hcanonical, hexact⟩
      exact ⟨hcanonical, hexact.trans
        (exactDot_eq_conventionalDot weights bytes 1 limb)⟩
    · change canonicalM31 (qm31Limb v2 limb) ∧
        qm31LimbView v2 limb = conventionalDot weights bytes 2 limb
      rcases hv2 limb hlimb with ⟨hcanonical, hexact⟩
      exact ⟨hcanonical, hexact.trans
        (exactDot_eq_conventionalDot weights bytes 2 limb)⟩
    · change canonicalM31 (qm31Limb v3 limb) ∧
        qm31LimbView v3 limb = conventionalDot weights bytes 3 limb
      rcases hv3 limb hlimb with ⟨hcanonical, hexact⟩
      exact ⟨hcanonical, hexact.trans
        (exactDot_eq_conventionalDot weights bytes 3 limb)⟩


end AspisV5FriDot16ReferenceSemantics

#print axioms AspisV5FriDot16ReferenceSemantics.generated_reduce_u64_corresponds
#print axioms AspisV5FriDot16ReferenceSemantics.read_word_corresponds
#print axioms AspisV5FriDot16ReferenceSemantics.raw4_corresponds
#print axioms AspisV5FriDot16ReferenceSemantics.block4_runs
#print axioms AspisV5FriDot16ReferenceSemantics.reduce4_corresponds
#print axioms AspisV5FriDot16ReferenceSemantics.slot_dot_corresponds
#print axioms AspisV5FriDot16ReferenceSemantics.indexed_dot16_corresponds
