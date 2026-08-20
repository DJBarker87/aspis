import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullHelperSoundness

/-! Exact record-chunk layout recovered from a successful unchanged helper. -/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5MerkleUnchangedFullRecordChunks

open V5MerkleUnchangedCompat
variable [HashContext]

open V5MerkleUnchangedFull
open AspisV5MerkleUnchangedFullParserBridge
open AspisV5MerkleUnchangedFullHelperSoundness

/-- Splitting a list whose length is an exact multiple produces exactly that
many full chunks, no remainder, and preserves every input element in order. -/
theorem toChunksExact_of_exact_length
    {alpha : Type*} (chunkSize count : Nat) (positive : 0 < chunkSize)
    (values : List alpha) (length_eq : values.length = count * chunkSize) :
    let output := List.toChunksExact chunkSize positive values
    output.1.length = count ∧
      output.2 = [] ∧
      (output.1.flatMap id) = values ∧
      ∀ chunk ∈ output.1, chunk.length = chunkSize := by
  induction count generalizing values with
  | zero =>
      have hempty : values = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst values
      simp [List.toChunksExact, positive]
  | succ count inductionHypothesis =>
      have hsize : chunkSize ≤ values.length := by
        rw [length_eq]
        simp [Nat.add_mul]
      have hnotSmall : ¬ values.length < chunkSize := by omega
      have hdropLength : (values.drop chunkSize).length = count * chunkSize := by
        simp [List.length_drop, length_eq, Nat.add_mul]
      have ih := inductionHypothesis (values.drop chunkSize) hdropLength
      unfold List.toChunksExact
      rw [dif_neg hnotSmall]
      change
        let output := List.toChunksExact chunkSize positive
          (values.drop chunkSize)
        (values.take chunkSize :: output.1).length = count + 1 ∧
          output.2 = [] ∧
          (values.take chunkSize :: output.1).flatMap id = values ∧
          ∀ chunk ∈ values.take chunkSize :: output.1,
            chunk.length = chunkSize
      dsimp only
      rcases ih with ⟨hcount, hremainder, hflatten, hchunks⟩
      refine ⟨by simp [hcount], hremainder, ?_, ?_⟩
      · simp only [List.flatMap_cons, id_eq]
        rw [hflatten]
        exact List.take_append_drop chunkSize values
      · intro chunk hchunk
        simp only [List.mem_cons] at hchunk
        rcases hchunk with rfl | hchunk
        · simp [List.length_take, hsize]
        · exact hchunks chunk hchunk

/-- Concrete list-level facts supplied by `chunks_exact` on a parser record
slice whose checked length is exactly `count * width`. -/
structure ExactRecordChunks
    (records : Slice Std.U8) (recordWidth : Std.Usize)
    (count : Nat) (iter : core.slice.iter.ChunksExact Std.U8) : Prop where
  count_eq : iter.chunks.length = count
  remainder_empty : iter.remainder.val = []
  flatten_eq : (iter.chunks.map fun chunk => chunk.val).flatten = records.val
  chunk_length : ∀ chunk ∈ iter.chunks,
    chunk.val.length = recordWidth.val

theorem chunks_exact_success_of_exact_length
    (records : Slice Std.U8) (recordWidth : Std.Usize)
    (count : Nat) (iter : core.slice.iter.ChunksExact Std.U8)
    (positive : 0 < recordWidth.val)
    (recordsLength : records.val.length = count * recordWidth.val)
    (run : core.slice.Slice.chunks_exact records recordWidth = .ok iter) :
    ExactRecordChunks records recordWidth count iter := by
  unfold core.slice.Slice.chunks_exact at run
  rw [dif_pos positive] at run
  let output := List.toChunksExact recordWidth.val positive records.val
  let sliceChunks : List (Slice Std.U8) := output.1.attach.map fun chunk =>
    (⟨chunk.1, by
      have := List.toChunksExact_chunk_length positive records.val chunk.1
        chunk.2
      scalar_tac⟩ : Slice Std.U8)
  have hiter : iter = {
      chunks := sliceChunks
      remainder := ⟨output.2, by
        have := List.toChunksExact_remainder_length positive records.val
        scalar_tac⟩ } := by
    exact Result.ok.inj run |>.symm
  have hexact := toChunksExact_of_exact_length recordWidth.val count positive
    records.val recordsLength
  change output.1.length = count ∧ output.2 = [] ∧
      output.1.flatMap id = records.val ∧
      ∀ chunk ∈ output.1, chunk.length = recordWidth.val at hexact
  rcases hexact with ⟨hcount, hremainder, hflatten, hlength⟩
  subst iter
  refine {
    count_eq := ?_
    remainder_empty := hremainder
    flatten_eq := ?_
    chunk_length := ?_ }
  · change (output.1.attach.map fun chunk =>
        (⟨chunk.1, by
          have := List.toChunksExact_chunk_length positive records.val
            chunk.1 chunk.2
          scalar_tac⟩ : Slice Std.U8)).length = count
    simpa only [List.length_map, List.length_attach] using hcount
  · have hsliceValues :
        (sliceChunks.map fun chunk => chunk.val) = output.1 := by
      simp [sliceChunks, List.map_map, Function.comp_def]
    change (sliceChunks.map (fun chunk : Slice Std.U8 =>
      chunk.val)).flatten = records.val
    rw [hsliceValues]
    simpa only [List.flatMap_id] using hflatten
  · intro chunk hchunk
    have hsliceValues :
        (sliceChunks.map fun item => item.val) = output.1 := by
      simp [sliceChunks, List.map_map, Function.comp_def]
    have hvalueMem : chunk.val ∈
        (sliceChunks.map fun item => item.val) :=
      List.mem_map_of_mem
        (f := fun item : Slice Std.U8 => item.val) hchunk
    rw [hsliceValues] at hvalueMem
    exact hlength chunk.val hvalueMem

/-- The parser length equation and the unchanged record-width/chunk calls
force the leaf iterator to contain exactly the parser's records, divided into
one `value || salt32` chunk per expected index. -/
theorem released_helper_record_chunks_exact
    {root : Array Std.U8 32#usize} {binaryDepth : Std.U32}
    {treeTag : Std.U8} {valueWidth : Std.Usize}
    {expectedIndices : Slice Std.U32} {proofBytes : Slice Std.U8}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {radixLevel : Std.Usize}
    {level next : alloc.vec.Vec (Array Std.U8 32#usize)}
    {opening : aspis_core.state_only_private_openings.StateOnlyPrivateOpening}
    {remainder : Slice Std.U8}
    {outputLevel outputNext : alloc.vec.Vec (Array Std.U8 32#usize)}
    (execution : GeneratedReleasedHelperExecution root binaryDepth treeTag
      valueWidth expectedIndices proofBytes topology radixLevel level next
      opening remainder outputLevel outputNext)
    (raw : ExactRawParserOutput proofBytes (Slice.len expectedIndices)
      valueWidth opening remainder)
    (expectedPositive : 0 < (Slice.len expectedIndices).val) :
    ExactRecordChunks opening.records execution.recordWidth
      (Slice.len expectedIndices).val execution.recordIter ∧
      execution.recordWidth.val = valueWidth.val + 32 := by
  rcases raw with ⟨frontierCount, count_eq, width_eq, count_offset,
    records_offset, records_eq, records_length, frontier_count_offset,
    frontier_offset, frontier_eq, frontier_length, end_offset, end_bound,
    remainder_eq⟩
  have hrecordWidth : execution.recordWidth =
      Std.Usize.wrapping_add opening.value_width
        aspis_core.state_only_private_merkle.STATE_ONLY_PRIVATE_LEAF_SALT_BYTES := by
    simpa [aspis_core.state_only_private_openings.StateOnlyPrivateOpening.record_width]
      using Result.ok.inj execution.record_width_run |>.symm
  have hwidthBound : valueWidth.val + 32 < UScalar.size .Usize := by
    have hrecordPrefix :
        (Slice.len expectedIndices).val * (valueWidth.val + 32) ≤
          proofBytes.val.length := by
      calc
        (Slice.len expectedIndices).val * (valueWidth.val + 32) =
            opening.records.val.length := records_length.symm
        _ ≤ proofBytes.val.length := by
          rw [records_eq, List.slice_length]
          omega
    have hproofBound : proofBytes.val.length ≤ Std.Usize.max :=
      proofBytes.property
    have hwidthLe : valueWidth.val + 32 ≤ Std.Usize.max :=
      (Nat.le_mul_of_pos_left (valueWidth.val + 32) expectedPositive).trans
        (hrecordPrefix.trans hproofBound)
    rcases System.Platform.numBits_eq with hbits | hbits <;>
      norm_num [UScalar.size, Usize.size, Usize.max, Usize.numBits, hbits]
        at hwidthLe ⊢ <;> omega
  have hrecordWidthVal : execution.recordWidth.val = valueWidth.val + 32 := by
    rw [hrecordWidth, width_eq]
    rw [Std.Usize.wrapping_add_val_eq]
    norm_num [aspis_core.state_only_private_merkle.STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]
    apply Nat.mod_eq_of_lt
    simpa only [UScalar.size_UScalarTyUsize] using hwidthBound
  have hpositive : 0 < execution.recordWidth.val := by omega
  refine ⟨chunks_exact_success_of_exact_length opening.records
    execution.recordWidth (Slice.len expectedIndices).val execution.recordIter
    hpositive ?_ execution.chunks_run, hrecordWidthVal⟩
  simpa [hrecordWidthVal] using records_length

#print axioms toChunksExact_of_exact_length
#print axioms chunks_exact_success_of_exact_length
#print axioms released_helper_record_chunks_exact

end AspisV5MerkleUnchangedFullRecordChunks
