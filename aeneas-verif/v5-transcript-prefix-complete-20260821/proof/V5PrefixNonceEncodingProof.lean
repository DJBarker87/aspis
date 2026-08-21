import Aeneas.Std
import AspisFormal.V5NonceWorkAuthentication

namespace AspisV5PrefixNonceEncodingProof

open Aeneas Aeneas.Std
open AspisFormal.V5ExactRuntimeWireRepair
open AspisV5NonceWorkAuthentication

abbrev ModelByte := AspisFormal.V5ExactRuntimeWireRepair.Byte

def generatedToByte (value : Std.U8) : ModelByte :=
  ⟨value.val, value.lt_succ_max⟩

def modelNonce (value : Nonce64) : Std.U64 :=
  Std.U64.ofNatCore value.val (by simpa using value.isLt)

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem generated_nonce_bytes_are_exact (value : Nonce64) :
    (core.num.U64.to_le_bytes (modelNonce value)).val.map generatedToByte =
      List.ofFn (nonceLEBytes value) := by
  change (((modelNonce value).bv.toLEBytes.map (@UScalar.mk .U8)).map
    generatedToByte) = List.ofFn (nonceLEBytes value)
  rw [BitVec.toLEBytes.eq_def]
  rw [if_pos (by norm_num : 64 > 0)]
  simp only [List.map_cons]
  rw [BitVec.toLEBytes.eq_def]
  rw [if_pos (by norm_num : 56 > 0)]
  simp only [List.map_cons]
  rw [BitVec.toLEBytes.eq_def]
  rw [if_pos (by norm_num : 48 > 0)]
  simp only [List.map_cons]
  rw [BitVec.toLEBytes.eq_def]
  rw [if_pos (by norm_num : 40 > 0)]
  simp only [List.map_cons]
  rw [BitVec.toLEBytes.eq_def]
  rw [if_pos (by norm_num : 32 > 0)]
  simp only [List.map_cons]
  rw [BitVec.toLEBytes.eq_def]
  rw [if_pos (by norm_num : 24 > 0)]
  simp only [List.map_cons]
  rw [BitVec.toLEBytes.eq_def]
  rw [if_pos (by norm_num : 16 > 0)]
  simp only [List.map_cons]
  rw [BitVec.toLEBytes.eq_def]
  rw [if_pos (by norm_num : 8 > 0)]
  simp only [List.map_cons]
  rw [BitVec.toLEBytes.eq_def]
  rw [if_neg (by norm_num : ¬ 0 > 0)]
  simp only [List.map_nil, List.ofFn_succ, List.ofFn_zero, List.cons.injEq,
    and_true]
  repeat' constructor
  all_goals apply Fin.ext
  all_goals
    simp only [generatedToByte, UScalar.val.eq_1, nonceLEBytes, nonceLEByte]
  all_goals change (BitVec.setWidth 8 _).toNat = _
  all_goals rw [BitVec.toNat_setWidth]
  all_goals try simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
  all_goals
    simp only [Nat.shiftRight_eq_div_pow, modelNonce, UScalar.bv_toNat]
  all_goals norm_num at *
  all_goals omega

#print axioms generated_nonce_bytes_are_exact

end AspisV5PrefixNonceEncodingProof
