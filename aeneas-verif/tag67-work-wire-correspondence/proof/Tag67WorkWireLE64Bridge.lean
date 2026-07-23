import Tag67WorkWireMaintainedCapstone

open Aeneas Aeneas.Std Result ControlFlow

namespace AspisTag67WorkWireMaintained

open AspisFormal.V5ExactRuntimeWireRepair
open AspisV5NonceWorkAuthentication
open aspis_verifier.v5_cu_probe

/-- The maintained nonce represented by one actual generated `U64` result. -/
def u64ToModelNonce (value : Std.U64) : Nonce64 :=
  ⟨value.val, by
    simpa [UScalar.size_UScalarTyU64, U64.size, U64.numBits] using value.hSize⟩

/-- The maintained view is constructed from the six generated decoded chunks;
it is not an unrelated universally quantified view. -/
def decodedWorkWireView
    (fold0 fold1 fold2 fold3 batch final : Std.U64) : WorkWireView where
  nonces
    | .batch => u64ToModelNonce batch
    | .fold round =>
        match round.val with
        | 0 => u64ToModelNonce fold0
        | 1 => u64ToModelNonce fold1
        | 2 => u64ToModelNonce fold2
        | _ => u64ToModelNonce fold3
    | .finalQuery => u64ToModelNonce final

def serializedRelationFinalSlice
    (shape : RuntimeShape) (wire : RuntimeExactWire shape)
    (hfit : runtimeRepairedProofBytes shape ≤ Std.Usize.max) : Slice Std.U8 :=
  ⟨List.ofFn (fun i : Fin 64 =>
      (serializedRuntimeSlice shape wire hfit).val[11048 + i.val]!), by
    simp
    have hmax : 64 ≤ Std.Usize.max := by
      cases System.Platform.numBits_eq <;>
        simp [Usize.max, Usize.numBits, *]
    exact hmax⟩

private theorem slice_index_run
    {T : Type} [Inhabited T] (values : Slice T)
    (index : Std.Usize) (hindex : index.val < values.length) :
    Slice.index_usize values index = ok values.val[index.val]! := by
  grind [Slice.index_usize]

private theorem usize_add_val_of_lt (left right : Std.Usize)
    (hsmall : left.val + right.val < UScalar.size .Usize) :
    (Std.Usize.wrapping_add left right).val = left.val + right.val := by
  rw [Std.Usize.wrapping_add_val_eq]
  exact Nat.mod_eq_of_lt hsmall

private theorem usize_succ_val_below_64 (offset : Std.Usize)
    (h : offset.val < 64) :
    (Std.Usize.wrapping_add offset 1#usize).val = offset.val + 1 := by
  apply usize_add_val_of_lt
  have hsize : 65 < UScalar.size .Usize := by
    rw [UScalar.size_def, UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with hbits | hbits <;>
      rw [hbits] <;> norm_num
  have hone : (1#usize : Std.Usize).val = 1 := by decide
  rw [hone]
  omega

private def zeroScanInvariant (relationFinal : Slice Std.U8)
    (offset : Std.Usize) : Prop :=
  40 ≤ offset.val ∧ offset.val ≤ 64 ∧
    ∀ index, 40 ≤ index → index < offset.val →
      relationFinal.val[index]! = 0#u8

private def zeroScanPost (relationFinal : Slice Std.U8) (accepted : Bool) : Prop :=
  accepted = true →
    ∀ index, 40 ≤ index → index < 64 →
      relationFinal.val[index]! = 0#u8

/-- An accepting execution of the actual generated zero-tail loop implies
that every byte it scanned (40 through 63 of relation-final) is zero. -/
theorem generated_read_zero
    (relationFinal : Slice Std.U8)
    (hlength : relationFinal.length = 64)
    (haccepted : v5_relation_final_zero_tail_is_valid relationFinal = ok true)
    (localByte : Fin 24) :
    relationFinal.val[40 + localByte.val]! = 0#u8 := by
  have hspec :
      v5_relation_final_zero_tail_is_valid_loop relationFinal 40#usize
        ⦃ accepted => zeroScanPost relationFinal accepted ⦄ := by
    simp only [v5_relation_final_zero_tail_is_valid_loop]
    apply loop.spec_decr_nat
      (fun offset : Std.Usize => 64 - offset.val)
      (zeroScanInvariant relationFinal)
      (zeroScanPost relationFinal)
    · intro offset hinvariant
      rcases hinvariant with ⟨hlower, hupper, hprefix⟩
      unfold v5_relation_final_zero_tail_is_valid_loop.body
      by_cases hactive : offset.val < 64
      · have hactiveScalar : offset < 64#usize := by simpa using hactive
        rw [if_pos hactiveScalar]
        have hindex : offset.val < relationFinal.length := by
          rw [hlength]
          exact hactive
        rw [slice_index_run relationFinal offset hindex]
        simp only [bind_tc_ok]
        by_cases hnonzero : relationFinal.val[offset.val]! != 0#u8
        · rw [if_pos hnonzero]
          simp [zeroScanPost]
        · rw [if_neg hnonzero]
          simp only [lift, bind_tc_ok]
          have hzero : relationFinal.val[offset.val]! = 0#u8 := by
            apply UScalar.eq_of_val_eq
            simpa using hnonzero
          have hnext := usize_succ_val_below_64 offset hactive
          refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
          · rw [hnext]
            omega
          · rw [hnext]
            omega
          · intro index hindexLower hindexUpper
            rw [hnext] at hindexUpper
            by_cases hbefore : index < offset.val
            · exact hprefix index hindexLower hbefore
            · have heq : index = offset.val := by omega
              simpa [heq] using hzero
          · rw [hnext]
            omega
      · have hdoneScalar : ¬ offset < 64#usize := by simpa using hactive
        rw [if_neg hdoneScalar]
        intro _ index hindexLower hindexUpper
        apply hprefix index hindexLower
        omega
    · refine ⟨by decide, by decide, ?_⟩
      intro index _ hindex
      exfalso
      norm_num at hindex
      omega
  have hloop :
      v5_relation_final_zero_tail_is_valid_loop relationFinal 40#usize = ok true := by
    simpa [v5_relation_final_zero_tail_is_valid, hlength] using haccepted
  rw [hloop] at hspec
  have hall : ∀ index, 40 ≤ index → index < 64 →
      relationFinal.val[index]! = 0#u8 := by
    simpa [Std.WP.spec, Std.WP.theta, Std.WP.wp_return,
      zeroScanPost] using hspec
  apply hall (40 + localByte.val)
  · omega
  · have := localByte.isLt
    omega

/-- The generated `from_le_bytes` result retains every one of its eight input
bytes.  This is the operational LE64 round-trip needed below. -/
theorem generated_u64_from_le_bytes_roundtrip
    (bytes : Array Std.U8 8#usize) :
    core.num.U64.to_le_bytes (core.num.U64.from_le_bytes bytes) = bytes := by
  apply Subtype.ext
  apply List.ext_getElem
  · simp [core.num.U64.to_le_bytes]
  · intro byteIndex hleft hright
    have hbyte : byteIndex < 8 := by simpa [Array.length_eq] using hright
    apply U8.bv_eq_imp_eq
    apply (BitVec.eq_iff _ _).2
    intro bitIndex hbit
    have hbit8 : bitIndex < 8 := by simpa using hbit
    have hdiv : (8 * byteIndex + bitIndex) / 8 = byteIndex := by omega
    have hmod : (8 * byteIndex + bitIndex) % 8 = bitIndex := by omega
    rw [List.Inhabited_getElem_eq_getElem! _ _ hleft,
      List.Inhabited_getElem_eq_getElem! _ _ hright]
    simp only [core.num.U64.to_le_bytes, core.num.U64.from_le_bytes]
    rw [List.getElem!_map_eq _ _ _ (by
      simp [BitVec.toLEBytes_length]
      exact hbyte)]
    simp only [BitVec.getElem!_eq_testBit_toNat]
    change Byte.testBit
        ((core.num.U64.from_le_bytes bytes).bv.toLEBytes[byteIndex]!) bitIndex =
      Byte.testBit bytes.val[byteIndex]!.bv bitIndex
    rw [BitVec.toLEBytes_getElem!_testBit _ _ _ hbit8]
    simp only [core.num.U64.from_le_bytes]
    rw [BitVec.getElem!_cast, BitVec.fromLEBytes_getElem!]
    rw [hdiv, hmod]
    rw [List.getElem!_map_eq _ _ _ hright]

private theorem model_le64_bitvec_bytes (nonce : Nonce64) :
    (List.ofFn fun i => modelByteToU8 (nonceLEBytes nonce i)).map U8.bv =
      (modelNonceToU64 nonce).bv.toLEBytes := by
  simp [modelNonceToU64, modelByteToU8, nonceLEBytes, nonceLEByte,
    BitVec.toLEBytes]
  repeat' apply And.intro
  all_goals
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow] <;> omega

theorem model_le64_roundtrip (nonce : Nonce64) :
    core.num.U64.from_le_bytes
        (Array.make 8#usize (List.ofFn fun i =>
          modelByteToU8 (nonceLEBytes nonce i))) =
      modelNonceToU64 nonce := by
  apply U64.bv_eq_imp_eq
  have hbytes := model_le64_bitvec_bytes nonce
  simp only [core.num.U64.from_le_bytes, Array.make]
  apply (BitVec.eq_iff _ _).2
  intro i hi
  simp only [BitVec.getElem!_cast, BitVec.fromLEBytes_getElem!]
  have hget := congrArg (fun bytes => bytes[i / 8]!) hbytes
  rw [hget]
  rw [BitVec.toLEBytes_getElem!_testBit _ _ _ (Nat.mod_lt _ (by norm_num))]
  congr 1
  omega

/-- Maintained `nonceLEByte(s)` is exactly generated `U64::to_le_bytes`. -/
theorem nonceLEBytes_matches_generated_u64 (value : Std.U64) :
    List.ofFn (fun i => modelByteToU8
      (nonceLEBytes (u64ToModelNonce value) i)) =
      (core.num.U64.to_le_bytes value).val := by
  have hmodel := model_le64_bitvec_bytes (u64ToModelNonce value)
  have hvalue : modelNonceToU64 (u64ToModelNonce value) = value := by
    apply U64.bv_eq_imp_eq
    apply BitVec.eq_of_toNat_eq
    simp [modelNonceToU64, u64ToModelNonce]
  rw [hvalue] at hmodel
  apply (List.map_injective_iff.mpr (fun _ _ h => U8.bv_eq_imp_eq _ _ h))
  simpa [core.num.U64.to_le_bytes] using hmodel

theorem bitVec_fromLEBytes_recovers_generated_u64 (value : Std.U64) :
    ∃ h : 8 *
        ((List.ofFn fun i => modelByteToU8
          (nonceLEBytes (u64ToModelNonce value) i)).map U8.bv).length = 64,
      (BitVec.fromLEBytes
        ((List.ofFn fun i => modelByteToU8
          (nonceLEBytes (u64ToModelNonce value) i)).map U8.bv)).cast h =
        value.bv := by
  have hvalue : modelNonceToU64 (u64ToModelNonce value) = value := by
    apply U64.bv_eq_imp_eq
    apply BitVec.eq_of_toNat_eq
    simp [modelNonceToU64, u64ToModelNonce]
  have hround := model_le64_roundtrip (u64ToModelNonce value)
  rw [hvalue] at hround
  have hbv := congrArg U64.bv hround
  refine ⟨by simp, ?_⟩
  simpa [core.num.U64.from_le_bytes, Array.make] using hbv

private theorem generated_u64_read_recovers_each_byte
    (data : Slice Std.U8) (offset : Std.Usize) (value : Std.U64)
    (hread : v5_work_wire_u64 data offset = ok value)
    (hbound : offset.val + 7 < data.length)
    (hsmall : offset.val + 7 < UScalar.size .Usize)
    (localByte : Fin 8) :
    data.val[offset.val + localByte.val]! =
      modelByteToU8 (nonceLEBytes (u64ToModelNonce value) localByte) := by
  have hadd1 : (Std.Usize.wrapping_add offset 1#usize).val = offset.val + 1 := by
    apply usize_add_val_of_lt
    have : (1#usize : Std.Usize).val = 1 := by decide
    rw [this]
    omega
  have hadd2 : (Std.Usize.wrapping_add offset 2#usize).val = offset.val + 2 := by
    apply usize_add_val_of_lt
    have : (2#usize : Std.Usize).val = 2 := by decide
    rw [this]
    omega
  have hadd3 : (Std.Usize.wrapping_add offset 3#usize).val = offset.val + 3 := by
    apply usize_add_val_of_lt
    have : (3#usize : Std.Usize).val = 3 := by decide
    rw [this]
    omega
  have hadd4 : (Std.Usize.wrapping_add offset 4#usize).val = offset.val + 4 := by
    apply usize_add_val_of_lt
    have : (4#usize : Std.Usize).val = 4 := by decide
    rw [this]
    omega
  have hadd5 : (Std.Usize.wrapping_add offset 5#usize).val = offset.val + 5 := by
    apply usize_add_val_of_lt
    have : (5#usize : Std.Usize).val = 5 := by decide
    rw [this]
    omega
  have hadd6 : (Std.Usize.wrapping_add offset 6#usize).val = offset.val + 6 := by
    apply usize_add_val_of_lt
    have : (6#usize : Std.Usize).val = 6 := by decide
    rw [this]
    omega
  have hadd7 : (Std.Usize.wrapping_add offset 7#usize).val = offset.val + 7 := by
    apply usize_add_val_of_lt
    have : (7#usize : Std.Usize).val = 7 := by decide
    rw [this]
    exact hsmall
  have h0 := slice_index_run data offset (by omega)
  have h1 := slice_index_run data (Std.Usize.wrapping_add offset 1#usize)
    (by rw [hadd1]; omega)
  have h2 := slice_index_run data (Std.Usize.wrapping_add offset 2#usize)
    (by rw [hadd2]; omega)
  have h3 := slice_index_run data (Std.Usize.wrapping_add offset 3#usize)
    (by rw [hadd3]; omega)
  have h4 := slice_index_run data (Std.Usize.wrapping_add offset 4#usize)
    (by rw [hadd4]; omega)
  have h5 := slice_index_run data (Std.Usize.wrapping_add offset 5#usize)
    (by rw [hadd5]; omega)
  have h6 := slice_index_run data (Std.Usize.wrapping_add offset 6#usize)
    (by rw [hadd6]; omega)
  have h7 := slice_index_run data (Std.Usize.wrapping_add offset 7#usize)
    (by rw [hadd7]; omega)
  let bytes : Array Std.U8 8#usize := Array.make 8#usize
    [data.val[offset.val]!, data.val[offset.val + 1]!,
     data.val[offset.val + 2]!, data.val[offset.val + 3]!,
     data.val[offset.val + 4]!, data.val[offset.val + 5]!,
     data.val[offset.val + 6]!, data.val[offset.val + 7]!]
  have hdecoded : core.num.U64.from_le_bytes bytes = value := by
    simpa [v5_work_wire_u64, lift, h0, h1, h2, h3, h4, h5, h6, h7,
      hadd1, hadd2, hadd3, hadd4, hadd5, hadd6, hadd7, bytes] using hread
  have hroundtrip := generated_u64_from_le_bytes_roundtrip bytes
  rw [hdecoded] at hroundtrip
  have hnonce := nonceLEBytes_matches_generated_u64 value
  have hlist : List.ofFn (fun i => modelByteToU8
      (nonceLEBytes (u64ToModelNonce value) i)) = bytes.val :=
    hnonce.trans (congrArg (fun a : Array Std.U8 8#usize => a.val) hroundtrip)
  change List.ofFn (fun i => modelByteToU8
      (nonceLEBytes (u64ToModelNonce value) i)) =
    [data.val[offset.val]!, data.val[offset.val + 1]!,
     data.val[offset.val + 2]!, data.val[offset.val + 3]!,
     data.val[offset.val + 4]!, data.val[offset.val + 5]!,
     data.val[offset.val + 6]!, data.val[offset.val + 7]!] at hlist
  have hget := congrArg (fun values => values[localByte.val]!) hlist
  fin_cases localByte <;> simpa [bytes, Array.make] using hget.symm

private theorem serialized_slice_byte_at
    (shape : RuntimeShape) (wire : RuntimeExactWire shape)
    (hfit : runtimeRepairedProofBytes shape ≤ Std.Usize.max)
    (index : Nat) (hindex : index < runtimeRepairedProofBytes shape) :
    (serializedRuntimeSlice shape wire hfit).val[index]! =
      modelByteToU8 (runtimeWireByteAt shape wire ⟨index, hindex⟩) := by
  have hwire : index < wire.val.length := by
    rw [wire.property]
    exact hindex
  simp [serializedRuntimeSlice, serializeRuntimeExact, serializeExact,
    runtimeWireByteAt, List.getElem!_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_eq_getElem hwire]

private theorem generated_magic_recovers_actual_bytes
    (shape : RuntimeShape) (wire : RuntimeExactWire shape)
    (hfit : runtimeRepairedProofBytes shape ≤ Std.Usize.max)
    (hmagic : v5_work_wire_magic_is_valid
      (serializedRuntimeSlice shape wire hfit) = ok true)
    (localByte : Fin 8) :
    runtimeWireByteAt shape wire (magicRuntimeOffset shape localByte) =
      av5CUP08 localByte := by
  let data := serializedRuntimeSlice shape wire hfit
  have hlength : data.length = runtimeRepairedProofBytes shape := by
    simp [data, serializedRuntimeSlice, serializeRuntimeExact, serializeExact,
      wire.property]
  have hlong : 8 ≤ data.length := by
    rw [hlength]
    simp only [runtimeRepairedProofBytes, repairedFixedBytes]
    omega
  have hlong' : 8 ≤ data.val.length := by exact hlong
  have h0 := slice_index_run data 0#usize (by
    change 0 < data.val.length; exact lt_of_lt_of_le (by norm_num) hlong')
  have h1 := slice_index_run data 1#usize (by
    change 1 < data.val.length; exact lt_of_lt_of_le (by norm_num) hlong')
  have h2 := slice_index_run data 2#usize (by
    change 2 < data.val.length; exact lt_of_lt_of_le (by norm_num) hlong')
  have h3 := slice_index_run data 3#usize (by
    change 3 < data.val.length; exact lt_of_lt_of_le (by norm_num) hlong')
  have h4 := slice_index_run data 4#usize (by
    change 4 < data.val.length; exact lt_of_lt_of_le (by norm_num) hlong')
  have h5 := slice_index_run data 5#usize (by
    change 5 < data.val.length; exact lt_of_lt_of_le (by norm_num) hlong')
  have h6 := slice_index_run data 6#usize (by
    change 6 < data.val.length; exact lt_of_lt_of_le (by norm_num) hlong')
  have h7 := slice_index_run data 7#usize (by
    change 7 < data.val.length; exact lt_of_lt_of_le (by norm_num) hlong')
  have hlenScalar : Slice.len data ≥ 8#usize := by
    simpa [Slice.len] using hlong
  have hmagic' := hmagic
  change v5_work_wire_magic_is_valid data = ok true at hmagic'
  unfold v5_work_wire_magic_is_valid at hmagic'
  rw [if_pos hlenScalar, h0] at hmagic'
  have ha0 : Array.index_usize V5_CU_PROBE_ACCOUNT_MAGIC 0#usize = ok 65#u8 := by
    simp [V5_CU_PROBE_ACCOUNT_MAGIC, Array.index_usize, Array.make]
  have ha1 : Array.index_usize V5_CU_PROBE_ACCOUNT_MAGIC 1#usize = ok 86#u8 := by
    simp [V5_CU_PROBE_ACCOUNT_MAGIC, Array.index_usize, Array.make]
  have ha2 : Array.index_usize V5_CU_PROBE_ACCOUNT_MAGIC 2#usize = ok 53#u8 := by
    simp [V5_CU_PROBE_ACCOUNT_MAGIC, Array.index_usize, Array.make]
  have ha3 : Array.index_usize V5_CU_PROBE_ACCOUNT_MAGIC 3#usize = ok 67#u8 := by
    simp [V5_CU_PROBE_ACCOUNT_MAGIC, Array.index_usize, Array.make]
  have ha4 : Array.index_usize V5_CU_PROBE_ACCOUNT_MAGIC 4#usize = ok 85#u8 := by
    simp [V5_CU_PROBE_ACCOUNT_MAGIC, Array.index_usize, Array.make]
  have ha5 : Array.index_usize V5_CU_PROBE_ACCOUNT_MAGIC 5#usize = ok 80#u8 := by
    simp [V5_CU_PROBE_ACCOUNT_MAGIC, Array.index_usize, Array.make]
  have ha6 : Array.index_usize V5_CU_PROBE_ACCOUNT_MAGIC 6#usize = ok 48#u8 := by
    simp [V5_CU_PROBE_ACCOUNT_MAGIC, Array.index_usize, Array.make]
  have ha7 : Array.index_usize V5_CU_PROBE_ACCOUNT_MAGIC 7#usize = ok 56#u8 := by
    simp [V5_CU_PROBE_ACCOUNT_MAGIC, Array.index_usize, Array.make]
  rw [ha0, h1, ha1, h2, ha2, h3, ha3, h4, ha4,
    h5, ha5, h6, ha6, h7, ha7] at hmagic'
  simp only [bind_tc_ok] at hmagic'
  have hv0 : (0#usize : Std.Usize).val = 0 := by decide
  have hv1 : (1#usize : Std.Usize).val = 1 := by decide
  have hv2 : (2#usize : Std.Usize).val = 2 := by decide
  have hv3 : (3#usize : Std.Usize).val = 3 := by decide
  have hv4 : (4#usize : Std.Usize).val = 4 := by decide
  have hv5 : (5#usize : Std.Usize).val = 5 := by decide
  have hv6 : (6#usize : Std.Usize).val = 6 := by decide
  have hv7 : (7#usize : Std.Usize).val = 7 := by decide
  simp only [hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7] at hmagic'
  have hd0 : data.val[0]! = 65#u8 := by
    by_contra hn
    rw [if_neg hn] at hmagic'
    simp at hmagic'
  rw [if_pos hd0] at hmagic'
  have hd1 : data.val[1]! = 86#u8 := by
    by_contra hn
    rw [if_neg hn] at hmagic'
    simp at hmagic'
  rw [if_pos hd1] at hmagic'
  have hd2 : data.val[2]! = 53#u8 := by
    by_contra hn
    rw [if_neg hn] at hmagic'
    simp at hmagic'
  rw [if_pos hd2] at hmagic'
  have hd3 : data.val[3]! = 67#u8 := by
    by_contra hn
    rw [if_neg hn] at hmagic'
    simp at hmagic'
  rw [if_pos hd3] at hmagic'
  have hd4 : data.val[4]! = 85#u8 := by
    by_contra hn
    rw [if_neg hn] at hmagic'
    simp at hmagic'
  rw [if_pos hd4] at hmagic'
  have hd5 : data.val[5]! = 80#u8 := by
    by_contra hn
    rw [if_neg hn] at hmagic'
    simp at hmagic'
  rw [if_pos hd5] at hmagic'
  have hd6 : data.val[6]! = 48#u8 := by
    by_contra hn
    rw [if_neg hn] at hmagic'
    simp at hmagic'
  rw [if_pos hd6] at hmagic'
  have hd7 : data.val[7]! = 56#u8 := by
    simpa using hmagic'
  have hbyte (index : Nat) (hindex : index < 8) :
      data.val[index]! = modelByteToU8 (runtimeWireByteAt shape wire
        ⟨index, by
          simp [runtimeRepairedProofBytes, repairedFixedBytes]
          omega⟩) := by
    exact serialized_slice_byte_at shape wire hfit index (by
      simp [runtimeRepairedProofBytes, repairedFixedBytes]
      omega)
  have hmapped := hbyte localByte.val localByte.isLt
  have hexpected : data.val[localByte.val]! =
      modelByteToU8 (av5CUP08 localByte) := by
    fin_cases localByte <;>
      simp [av5CUP08, hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7] <;>
      apply UScalar.eq_of_val_eq <;> rfl
  have heq := hmapped.symm.trans hexpected
  apply Fin.ext
  simpa [modelByteToU8, magicRuntimeOffset] using congrArg UScalar.val heq

private theorem generated_zero_tail_recovers_actual_byte
    (shape : RuntimeShape) (wire : RuntimeExactWire shape)
    (hfit : runtimeRepairedProofBytes shape ≤ Std.Usize.max)
    (hzero : v5_relation_final_zero_tail_is_valid
      (serializedRelationFinalSlice shape wire hfit) = ok true)
    (localByte : RemainingZeroByte) :
    runtimeWireByteAt shape wire
      (remainingZeroRuntimeOffset shape localByte) = 0 := by
  let relationFinal := serializedRelationFinalSlice shape wire hfit
  have hlength : relationFinal.length = 64 := by
    simp [relationFinal, serializedRelationFinalSlice]
  have hread := generated_read_zero relationFinal hlength hzero localByte
  have hglobal : 11048 + (40 + localByte.val) = 11088 + localByte.val := by omega
  have hbound : 11088 + localByte.val < runtimeRepairedProofBytes shape := by
    have := localByte.isLt
    simp [runtimeRepairedProofBytes, repairedFixedBytes]
    omega
  have hmapped := serialized_slice_byte_at shape wire hfit
    (11088 + localByte.val) hbound
  have hrelation : relationFinal.val[40 + localByte.val]! =
      (serializedRuntimeSlice shape wire hfit).val[11088 + localByte.val]! := by
    have hlt : 40 + localByte.val < 64 := by
      have := localByte.isLt
      omega
    have hget := List.getElem!_ofFn
      (fun i : Fin 64 =>
        (serializedRuntimeSlice shape wire hfit).val[11048 + i.val]!)
      (40 + localByte.val) hlt
    simpa only [relationFinal, serializedRelationFinalSlice, hglobal] using hget
  rw [hrelation, hmapped] at hread
  have hoffset :
      (⟨11088 + localByte.val, hbound⟩ :
        Fin (runtimeRepairedProofBytes shape)) =
      remainingZeroRuntimeOffset shape localByte := by
    apply Fin.ext
    rfl
  rw [hoffset] at hread
  apply Fin.ext
  simpa [modelByteToU8, remainingZeroRuntimeOffset] using
    congrArg UScalar.val hread

private theorem work_kind_offset_plus_seven_fits_usize (kind : WorkKind) :
    kind.offset + 7 < UScalar.size .Usize := by
  have hsize : 19136 < UScalar.size .Usize := by
    rw [UScalar.size_def, UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with h | h <;>
      rw [h] <;> norm_num
  have hsize' : 19136 < Std.Usize.size := by
    simpa only [UScalar.size_UScalarTyUsize] using hsize
  cases kind with
  | batch => simp only [WorkKind.offset]; omega
  | fold round =>
      have hround := round.isLt
      simp only [WorkKind.offset]
      omega
  | finalQuery => simp only [WorkKind.offset]; omega

private theorem generated_read_recovers_positioned_nonce
    (shape : RuntimeShape) (wire : RuntimeExactWire shape)
    (hfit : runtimeRepairedProofBytes shape ≤ Std.Usize.max)
    (kind : WorkKind) (offset : Std.Usize) (value : Std.U64)
    (hoffset : offset.val = kind.offset)
    (hread : v5_work_wire_u64 (serializedRuntimeSlice shape wire hfit) offset =
      ok value)
    (localByte : Fin 8) :
    runtimeWireByteAt shape wire
        (positionedNonceRuntimeOffset shape ⟨kind, localByte⟩) =
      nonceLEBytes (u64ToModelNonce value) localByte := by
  let data := serializedRuntimeSlice shape wire hfit
  have hlength : data.length = runtimeRepairedProofBytes shape := by
    simp [data, serializedRuntimeSlice, serializeRuntimeExact, serializeExact,
      wire.property]
  have hbound : offset.val + 7 < data.length := by
    rw [hlength, hoffset]
    have hfixed := positioned_nonce_byte_offset_lt_fixed_body
      (PositionedNonceByte.mk kind ⟨7, by decide⟩)
    simp only [positionedNonceByteOffset] at hfixed
    simp only [runtimeRepairedProofBytes]
    omega
  have hbyte := generated_u64_read_recovers_each_byte data offset value hread
    hbound (by rw [hoffset]; exact work_kind_offset_plus_seven_fits_usize kind)
    localByte
  have hindex : kind.offset + localByte.val < runtimeRepairedProofBytes shape :=
    (positionedNonceRuntimeOffset shape ⟨kind, localByte⟩).isLt
  have hmapped := serialized_slice_byte_at shape wire hfit
    (kind.offset + localByte.val) hindex
  have hposition : offset.val + localByte.val = kind.offset + localByte.val := by
    rw [hoffset]
  rw [hposition, hmapped] at hbyte
  apply Fin.ext
  simpa [modelByteToU8, positionedNonceRuntimeOffset,
    positionedNonceByteOffset] using congrArg UScalar.val hbyte

/-- Source-authentic closure of the work-wire projection seam.  The only
premises are successful executions of generated guards/reads on the actual
maintained serialized bytes.  The maintained view is existentially built from
those six returned `U64` chunks; there is no arbitrary-view or projection
premise. -/
theorem generated_acceptance_constructs_exact_work_wire_view
    (shape : RuntimeShape) (wire : RuntimeExactWire shape)
    (hfit : runtimeRepairedProofBytes shape ≤ Std.Usize.max)
    (fold0 fold1 fold2 fold3 batch final : Std.U64) (selected : Std.U8)
    (hmagic : v5_work_wire_magic_is_valid
      (serializedRuntimeSlice shape wire hfit) = ok true)
    (hfold0 : v5_work_wire_u64
      (serializedRuntimeSlice shape wire hfit) 11048#usize = ok fold0)
    (hfold1 : v5_work_wire_u64
      (serializedRuntimeSlice shape wire hfit) 11056#usize = ok fold1)
    (hfold2 : v5_work_wire_u64
      (serializedRuntimeSlice shape wire hfit) 11064#usize = ok fold2)
    (hfold3 : v5_work_wire_u64
      (serializedRuntimeSlice shape wire hfit) 11072#usize = ok fold3)
    (hbatch : v5_work_wire_u64
      (serializedRuntimeSlice shape wire hfit) 11080#usize = ok batch)
    (hfinal : v5_work_wire_u64
      (serializedRuntimeSlice shape wire hfit) 19127#usize = ok final)
    (hselector : Slice.index_usize
      (serializedRuntimeSlice shape wire hfit) 19135#usize = ok selected)
    (hzero : v5_relation_final_zero_tail_is_valid
      (serializedRelationFinalSlice shape wire hfit) = ok true) :
    ∃ view : WorkWireView,
      view = decodedWorkWireView fold0 fold1 fold2 fold3 batch final ∧
      projectWorkWire shape wire = canonicalWorkWire view ∧
      project_v5_work_wire (serializedRuntimeSlice shape wire hfit) = ok {
        fold_nonces := Array.make 4#usize [fold0, fold1, fold2, fold3]
        batch_nonce := batch
        final_nonce := final
        query_selector := selected
      } := by
  let view := decodedWorkWireView fold0 fold1 fold2 fold3 batch final
  refine ⟨view, rfl, ?_, ?_⟩
  · unfold projectWorkWire canonicalWorkWire
    congr 1
    · funext localByte
      exact generated_magic_recovers_actual_bytes shape wire hfit hmagic localByte
    · funext kind localByte
      cases kind with
      | batch =>
          simpa [projectWorkWire, canonicalWorkWire, view,
            decodedWorkWireView] using
            generated_read_recovers_positioned_nonce shape wire hfit .batch
              11080#usize batch (by decide) hbatch localByte
      | fold round =>
          fin_cases round
          · simpa [projectWorkWire, canonicalWorkWire, view,
              decodedWorkWireView] using
              generated_read_recovers_positioned_nonce shape wire hfit (.fold 0)
                11048#usize fold0 (by decide) hfold0 localByte
          · simpa [projectWorkWire, canonicalWorkWire, view,
              decodedWorkWireView] using
              generated_read_recovers_positioned_nonce shape wire hfit (.fold 1)
                11056#usize fold1 (by decide) hfold1 localByte
          · simpa [projectWorkWire, canonicalWorkWire, view,
              decodedWorkWireView] using
              generated_read_recovers_positioned_nonce shape wire hfit (.fold 2)
                11064#usize fold2 (by decide) hfold2 localByte
          · simpa [projectWorkWire, canonicalWorkWire, view,
              decodedWorkWireView] using
              generated_read_recovers_positioned_nonce shape wire hfit (.fold 3)
                11072#usize fold3 (by decide) hfold3 localByte
      | finalQuery =>
          simpa [projectWorkWire, canonicalWorkWire, view,
            decodedWorkWireView] using
            generated_read_recovers_positioned_nonce shape wire hfit .finalQuery
              19127#usize final (by decide) hfinal localByte
    · funext localByte
      exact generated_zero_tail_recovers_actual_byte shape wire hfit hzero localByte
  · have hadd8 : Std.Usize.wrapping_add 11048#usize 8#usize = 11056#usize := by
      apply UScalar.eq_of_val_eq
      cases System.Platform.numBits_eq <;>
        simp_all [Usize.size, Usize.numBits]
    have hadd16 : Std.Usize.wrapping_add 11048#usize 16#usize = 11064#usize := by
      apply UScalar.eq_of_val_eq
      cases System.Platform.numBits_eq <;>
        simp_all [Usize.size, Usize.numBits]
    have hadd24 : Std.Usize.wrapping_add 11048#usize 24#usize = 11072#usize := by
      apply UScalar.eq_of_val_eq
      cases System.Platform.numBits_eq <;>
        simp_all [Usize.size, Usize.numBits]
    simp [project_v5_work_wire,
      V5_CU_PROBE_RELATION_FINAL_OFFSET_EXACT,
      V5_CU_PROBE_BATCH_NONCE_OFFSET_EXACT,
      V5_CU_PROBE_FINAL_NONCE_OFFSET_EXACT,
      V5_CU_PROBE_QUERY_SELECTOR_OFFSET_EXACT,
      hadd8, hadd16, hadd24, hfold0, hfold1, hfold2, hfold3,
      hbatch, hfinal, hselector, lift, Array.make]

#print axioms generated_read_zero
#print axioms generated_u64_from_le_bytes_roundtrip
#print axioms nonceLEBytes_matches_generated_u64
#print axioms bitVec_fromLEBytes_recovers_generated_u64
#print axioms generated_acceptance_constructs_exact_work_wire_view

end AspisTag67WorkWireMaintained
