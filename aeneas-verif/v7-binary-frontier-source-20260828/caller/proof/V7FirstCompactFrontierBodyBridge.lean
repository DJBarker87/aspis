import V7FirstCompact.Funs
import Mathlib.Data.Nat.Log

/-!
# Literal source bridge for one adjacent frontier contribution

This theorem follows the translated production loop body through both slice
indexes, the `u32` XOR, `leading_zeros`, checked subtraction, cast and checked
`usize` addition.  A successful body step therefore adds exactly
`floor(log2(left XOR right))`; the arithmetic hint is not an opaque source
premise.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open V7FirstCompactSource

set_option autoImplicit false

namespace V7FirstCompactFrontierBodyBridge

theorem u32_xor_val (left right : Std.U32) :
    (left ^^^ right).val = Nat.xor left.val right.val := by
  rfl

theorem source_frontier_body_adds_exact_log2
    (iterator next : core.slice.iter.Windows Std.U32)
    (pair : Slice Std.U32)
    (left right : Std.U32)
    (expanded output : Std.Usize)
    (nextExact :
      core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
          iterator = .ok (some pair, next))
    (pairZero : Slice.index_usize pair 0#usize = .ok left)
    (pairOne : Slice.index_usize pair 1#usize = .ok right)
    (xorNonzero : Nat.xor left.val right.val ≠ 0)
    (success :
      v6_onefold.binary_frontier_nodes_loop2.body iterator expanded =
        .ok (.cont (next, output))) :
    output.val = expanded.val + Nat.log2 (Nat.xor left.val right.val) := by
  have scalarXorNonzero : left ^^^ right ≠ 0#u32 := by
    intro equality
    have valueEquality := congrArg UScalar.val equality
    change (left ^^^ right).val = 0 at valueEquality
    rw [u32_xor_val] at valueEquality
    exact xorNonzero valueEquality
  have scalarXorTest : ((left ^^^ right) != 0#u32) = true := by
    simpa using scalarXorNonzero
  have xorBvNonzero : (left ^^^ right).bv ≠ 0 := by
    intro bvZero
    apply scalarXorNonzero
    apply U32.bv_eq_imp_eq
    simpa using bvZero
  have valueNe : left.val ≠ right.val := by
    intro valueEquality
    apply xorNonzero
    rw [valueEquality]
    simp
  have xorLt : Nat.xor left.val right.val < 2 ^ 32 := by
    apply Nat.xor_lt_two_pow
    · simpa using left.hBounds
    · simpa using right.hBounds
  have logLt : Nat.log2 (Nat.xor left.val right.val) < 32 :=
    (Nat.log2_lt xorNonzero).2 xorLt
  have leadingZerosLt :
      BitVec.leadingZeros (left ^^^ right).bv < 2 ^ 32 := by
    rw [BitVec.leadingZeros]
    simp only [xorBvNonzero, if_false]
    norm_num
    omega
  have leadingVal :
      (core.num.U32.leading_zeros (left ^^^ right)).val =
        31 - Nat.log2 (Nat.xor left.val right.val) := by
    rw [core.num.U32.leading_zeros]
    simp only [UScalar.val]
    change (BitVec.ofNat 32
      (BitVec.leadingZeros (left ^^^ right).bv)).toNat = _
    rw [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt leadingZerosLt]
    rw [BitVec.leadingZeros]
    simp only [xorBvNonzero, if_false]
    rw [show (left ^^^ right).bv.toNat = Nat.xor left.val right.val by
      exact u32_xor_val left right]
    simp only [UScalarTy.U32_numBits_eq, Nat.log2_eq_log_two]
    change 32 - Nat.log 2 (Nat.xor left.bv.toNat right.bv.toNat) - 1 =
      31 - Nat.log 2 (Nat.xor left.bv.toNat right.bv.toNat)
    omega
  unfold v6_onefold.binary_frontier_nodes_loop2.body at success
  rw [nextExact] at success
  simp only [bind_tc_ok] at success
  simp [pairZero, pairOne] at success
  simp only [bind_tc_ok, lift, scalarXorTest, massert] at success
  cases firstResult : (core.num.U32.BITS - 1#u32) with
  | fail error =>
      rw [firstResult] at success
      simp [valueNe] at success
  | div =>
      rw [firstResult] at success
      simp [valueNe] at success
  | ok initial =>
      have initialSpec := UScalar.sub_equiv core.num.U32.BITS 1#u32
      rw [firstResult] at initialSpec
      have initialVal : initial.val = 31 := by
        simpa using initialSpec.2.1.symm
      rw [firstResult] at success
      simp [valueNe] at success
      cases secondResult :
          (initial - core.num.U32.leading_zeros (left ^^^ right)) with
      | fail error =>
          rw [secondResult] at success
          simp [valueNe] at success
      | div =>
          rw [secondResult] at success
          simp [valueNe] at success
      | ok increment =>
          have incrementSpec := UScalar.sub_equiv initial
            (core.num.U32.leading_zeros (left ^^^ right))
          rw [secondResult] at incrementSpec
          have incrementVal :
              increment.val = Nat.log2 (Nat.xor left.val right.val) := by
            have exactDifference := incrementSpec.2.1
            rw [initialVal, leadingVal] at exactDifference
            omega
          rw [secondResult] at success
          simp [valueNe] at success
          cases thirdResult :
              (expanded + UScalar.cast .Usize increment) with
          | fail error =>
              rw [thirdResult] at success
              simp [valueNe] at success
          | div =>
              rw [thirdResult] at success
              simp [valueNe] at success
          | ok finalExpanded =>
              have finalSpec := UScalar.add_equiv expanded
                (UScalar.cast .Usize increment)
              rw [thirdResult] at finalSpec
              rw [thirdResult] at success
              simp [valueNe] at success
              have outputEquality : output = finalExpanded := by
                simpa using success.symm
              rw [outputEquality, finalSpec.2.1,
                U32.cast_Usize_val_eq, incrementVal]

theorem source_frontier_body_succeeds_exact_log2
    (iterator next : core.slice.iter.Windows Std.U32)
    (pair : Slice Std.U32)
    (left right : Std.U32)
    (expanded : Std.Usize)
    (nextExact :
      core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
          iterator = .ok (some pair, next))
    (pairZero : Slice.index_usize pair 0#usize = .ok left)
    (pairOne : Slice.index_usize pair 1#usize = .ok right)
    (xorNonzero : Nat.xor left.val right.val ≠ 0)
    (headroom :
      expanded.val + Nat.log2 (Nat.xor left.val right.val) ≤ Std.Usize.max) :
    ∃ output : Std.Usize,
      v6_onefold.binary_frontier_nodes_loop2.body iterator expanded =
        .ok (.cont (next, output)) ∧
      output.val = expanded.val + Nat.log2 (Nat.xor left.val right.val) := by
  have scalarXorNonzero : left ^^^ right ≠ 0#u32 := by
    intro equality
    have valueEquality := congrArg UScalar.val equality
    change (left ^^^ right).val = 0 at valueEquality
    rw [u32_xor_val] at valueEquality
    exact xorNonzero valueEquality
  have xorBvNonzero : (left ^^^ right).bv ≠ 0 := by
    intro bvZero
    apply scalarXorNonzero
    apply U32.bv_eq_imp_eq
    simpa using bvZero
  have xorLt : Nat.xor left.val right.val < 2 ^ 32 := by
    apply Nat.xor_lt_two_pow
    · simpa using left.hBounds
    · simpa using right.hBounds
  have logLt : Nat.log2 (Nat.xor left.val right.val) < 32 :=
    (Nat.log2_lt xorNonzero).2 xorLt
  have leadingZerosLt :
      BitVec.leadingZeros (left ^^^ right).bv < 2 ^ 32 := by
    rw [BitVec.leadingZeros]
    simp only [xorBvNonzero, if_false]
    norm_num
    omega
  have leadingVal :
      (core.num.U32.leading_zeros (left ^^^ right)).val =
        31 - Nat.log2 (Nat.xor left.val right.val) := by
    rw [core.num.U32.leading_zeros]
    simp only [UScalar.val]
    change (BitVec.ofNat 32
      (BitVec.leadingZeros (left ^^^ right).bv)).toNat = _
    rw [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt leadingZerosLt]
    rw [BitVec.leadingZeros]
    simp only [xorBvNonzero, if_false]
    rw [show (left ^^^ right).bv.toNat = Nat.xor left.val right.val by
      exact u32_xor_val left right]
    simp only [UScalarTy.U32_numBits_eq, Nat.log2_eq_log_two]
    change 32 - Nat.log 2 (Nat.xor left.bv.toNat right.bv.toNat) - 1 =
      31 - Nat.log 2 (Nat.xor left.bv.toNat right.bv.toNat)
    omega
  cases firstResult : (core.num.U32.BITS - 1#u32) with
  | fail error =>
      have firstFacts := UScalar.sub_equiv core.num.U32.BITS 1#u32
      rw [firstResult] at firstFacts
      norm_num at firstFacts
  | div =>
      have firstFacts := UScalar.sub_equiv core.num.U32.BITS 1#u32
      rw [firstResult] at firstFacts
      exact False.elim firstFacts
  | ok initial =>
      have firstFacts := UScalar.sub_equiv core.num.U32.BITS 1#u32
      rw [firstResult] at firstFacts
      have initialVal : initial.val = 31 := by
        simpa using firstFacts.2.1.symm
      cases secondResult :
          (initial - core.num.U32.leading_zeros (left ^^^ right)) with
      | fail error =>
          have secondFacts := UScalar.sub_equiv initial
            (core.num.U32.leading_zeros (left ^^^ right))
          rw [secondResult] at secondFacts
          rw [initialVal, leadingVal] at secondFacts
          omega
      | div =>
          have secondFacts := UScalar.sub_equiv initial
            (core.num.U32.leading_zeros (left ^^^ right))
          rw [secondResult] at secondFacts
          exact False.elim secondFacts
      | ok increment =>
          have secondFacts := UScalar.sub_equiv initial
            (core.num.U32.leading_zeros (left ^^^ right))
          rw [secondResult] at secondFacts
          have incrementVal :
              increment.val = Nat.log2 (Nat.xor left.val right.val) := by
            have exactDifference := secondFacts.2.1
            rw [initialVal, leadingVal] at exactDifference
            omega
          cases thirdResult :
              (expanded + UScalar.cast .Usize increment) with
          | fail error =>
              have thirdFacts := UScalar.add_equiv expanded
                (UScalar.cast .Usize increment)
              rw [thirdResult] at thirdFacts
              apply False.elim
              apply thirdFacts
              unfold UScalar.inBounds
              simp only [U32.cast_Usize_val_eq, incrementVal, Nat.zero_le,
                true_and]
              have maxSucc :
                  2 ^ UScalarTy.Usize.numBits = Std.Usize.max + 1 := by
                rcases System.Platform.numBits_eq with platformBits | platformBits <;>
                  norm_num [Std.Usize.max, Std.Usize.numBits, platformBits]
              rw [maxSucc]
              omega
          | div =>
              have thirdFacts := UScalar.add_equiv expanded
                (UScalar.cast .Usize increment)
              rw [thirdResult] at thirdFacts
              exact False.elim thirdFacts
          | ok output =>
              have thirdFacts := UScalar.add_equiv expanded
                (UScalar.cast .Usize increment)
              rw [thirdResult] at thirdFacts
              have outputVal :
                  output.val = expanded.val +
                    Nat.log2 (Nat.xor left.val right.val) := by
                rw [thirdFacts.2.1, U32.cast_Usize_val_eq, incrementVal]
              refine ⟨output, ?_, outputVal⟩
              unfold v6_onefold.binary_frontier_nodes_loop2.body
              rw [nextExact]
              simp only [bind_tc_ok]
              simp [pairZero, pairOne]
              have scalarXorTest : ((left ^^^ right) != 0#u32) = true := by
                simpa using scalarXorNonzero
              have xorValueNonzero : (left ^^^ right).val ≠ 0 := by
                rw [u32_xor_val]
                exact xorNonzero
              have valueDistinct : left.val ≠ right.val := by
                intro equality
                apply xorNonzero
                simp [equality]
              simp only [scalarXorTest, massert, bind_tc_ok]
              rw [firstResult]
              simp only [bind_tc_ok, lift]
              rw [secondResult]
              simp only [bind_tc_ok, lift]
              rw [thirdResult]
              simp [valueDistinct]

#print axioms source_frontier_body_adds_exact_log2
#print axioms source_frontier_body_succeeds_exact_log2

end V7FirstCompactFrontierBodyBridge
