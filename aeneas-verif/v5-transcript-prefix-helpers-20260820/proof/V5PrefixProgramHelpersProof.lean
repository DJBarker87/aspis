import V5PrefixProgramHelpersGenerated.Funs

namespace V5PrefixProgramHelpersProof

open Aeneas Aeneas.Std Result ControlFlow Error
open V5PrefixProgramHelpersGenerated

abbrev Transcript :=
  V5PrefixProgramHelpersGenerated.aspis_core.transcript.Transcript

def roundZeroRecord (root salt : Array Std.U8 32#usize) :
    Array Std.U8 65#usize :=
  Array.make 65#usize (0#u8 :: root.val ++ salt.val) (by
    simp [root.property, salt.property])

def c2Record (root salt : Array Std.U8 32#usize) :
    Array Std.U8 64#usize :=
  Array.make 64#usize (root.val ++ salt.val) (by
    simp [root.property, salt.property])

/-- Exact bytes built by the unchanged round-root helper for the prefix's
layer-zero call. -/
theorem generated_round_zero_record_exact
    (root salt : Array Std.U8 32#usize) :
    V5PrefixProgramHelpersGenerated.v5_cu_probe.real_v5_round_root_record
        0#usize root salt = .ok (roundZeroRecord root salt) := by
  simp [V5PrefixProgramHelpersGenerated.v5_cu_probe.real_v5_round_root_record,
    roundZeroRecord, Array.update, Array.repeat,
    core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.index.SliceIndexRangeFromUsizeSlice,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice, Array.to_slice, Array.from_slice,
    Slice.len, Slice.length, Slice.drop, List.setSlice!, Array.make,
    UScalar.cast, lift,
    root.property, salt.property]
  simp_lists
  apply Subtype.ext
  simp only
  congr 1

/-- Exact concatenation built by the unchanged C2-root helper. -/
theorem generated_c2_record_exact
    (root salt : Array Std.U8 32#usize) :
    V5PrefixProgramHelpersGenerated.v5_cu_probe.real_v5_c2_root_record
        root salt = .ok (c2Record root salt) := by
  simp [V5PrefixProgramHelpersGenerated.v5_cu_probe.real_v5_c2_root_record,
    c2Record, Array.repeat, core.array.Array.index_mut,
    core.ops.index.IndexMutSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.index.SliceIndexRangeFromUsizeSlice,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice, Array.to_slice, Array.from_slice,
    Slice.len, Slice.length, Slice.drop, List.setSlice!, Array.make, lift,
    root.property, salt.property]
  simp_lists

/-- The extracted prefix root helper absorbs exactly label 12 and the
layer-byte/root/salt record. -/
theorem generated_absorb_round_zero_root_exact
    (transcript : Transcript) (root salt : Array Std.U8 32#usize) :
    V5PrefixProgramHelpersGenerated.v5_cu_probe.absorb_real_v5_round_root
        transcript 0#usize root salt =
      .ok { transcript with events := transcript.events ++
        [.absorb 12#u8 (0#u8 :: root.val ++ salt.val)] } := by
  simp [V5PrefixProgramHelpersGenerated.v5_cu_probe.absorb_real_v5_round_root,
    V5PrefixProgramHelpersGenerated.v5_cu_probe.real_v5_round_root_absorb_input,
    generated_round_zero_record_exact,
    V5PrefixProgramHelpersGenerated.aspis_core.transcript.label.M31_CIRCLE_ROUND_ROOT,
    V5PrefixProgramHelpersGenerated.aspis_core.transcript.Transcript.absorb,
    roundZeroRecord, Array.make, lift]

/-- The extracted C2 helper absorbs exactly label 13 and `root ++ salt`. -/
theorem generated_absorb_c2_root_exact
    (transcript : Transcript) (root salt : Array Std.U8 32#usize) :
    V5PrefixProgramHelpersGenerated.v5_cu_probe.absorb_real_v5_c2_root
        transcript root salt =
      .ok { transcript with events := transcript.events ++
        [.absorb 13#u8 (root.val ++ salt.val)] } := by
  simp [V5PrefixProgramHelpersGenerated.v5_cu_probe.absorb_real_v5_c2_root,
    V5PrefixProgramHelpersGenerated.v5_cu_probe.real_v5_c2_root_absorb_input,
    generated_c2_record_exact,
    V5PrefixProgramHelpersGenerated.aspis_core.transcript.label.M31_CIRCLE_C2_ROOT,
    V5PrefixProgramHelpersGenerated.aspis_core.transcript.Transcript.absorb,
    c2Record, Array.make, lift]

/-- A successful extracted batch-work helper checks exactly 37 bits before
absorbing label 28 and the nonce's exact little-endian bytes. -/
theorem generated_batch_work_success_exact
    (transcript : Transcript) (nonce : Std.U64)
    (hvalid : transcript.workValid nonce 37#u8 = true) :
    V5PrefixProgramHelpersGenerated.v5_cu_probe.check_and_absorb_real_v5_batch_nonce
        transcript nonce =
      .ok (.Ok (), { transcript with events := transcript.events ++
        [.absorb 28#u8 (core.num.U64.to_le_bytes nonce).val] }) := by
  simp [V5PrefixProgramHelpersGenerated.v5_cu_probe.check_and_absorb_real_v5_batch_nonce,
    V5PrefixProgramHelpersGenerated.v5_cu_probe.v5_batch_work_difficulty,
    V5PrefixProgramHelpersGenerated.v5_cu_probe.require_real_v5_work,
    V5PrefixProgramHelpersGenerated.v5_cu_probe.v5_real_work_is_valid,
    V5PrefixProgramHelpersGenerated.v5_cu_probe.absorb_real_v5_batch_nonce,
    V5PrefixProgramHelpersGenerated.v5_cu_probe.v5_batch_work_absorb_input,
    V5PrefixProgramHelpersGenerated.v5_cu_probe.v5_batch_work_record,
    V5PrefixProgramHelpersGenerated.aspis_core.transcript.label.M31_PAYMENT_BATCH_POW_NONCE,
    V5PrefixProgramHelpersGenerated.aspis_core.transcript.Transcript.grinding_ok,
    V5PrefixProgramHelpersGenerated.aspis_core.transcript.Transcript.absorb,
    core.result.Result.Insts.CoreOpsTry.branch, hvalid, lift]

#print axioms generated_round_zero_record_exact
#print axioms generated_c2_record_exact
#print axioms generated_absorb_round_zero_root_exact
#print axioms generated_absorb_c2_root_exact
#print axioms generated_batch_work_success_exact

end V5PrefixProgramHelpersProof
