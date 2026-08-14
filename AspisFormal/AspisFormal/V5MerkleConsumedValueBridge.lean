import AspisFormal.V5MerkleRustBridge
import AspisFormal.V5ComponentCQM31Representation

/-!
# Exact bytes returned by the V5 Merkle parser and read by FRI

`V5MerkleRustBridge` proves that the five parsed record streams authenticate
to the five public roots.  This file adds the part that a Merkle proof alone
does not provide: the zero-copy parser views, sorted index/ordinal lookup, and
the exact byte slices read by the four production FRI transitions.

The deterministic statements below prove that every modeled consumer byte is
the value prefix of an authenticated `value || salt32` record.  They also pin
the production byte layouts used by the M31 and QM31 decoders.

The final source boundary is intentionally narrow.  It asks extraction to show
that the real Rust parser's returned slices and the real FRI consumer reads are
the modeled observation.  Tests can exercise that equality at concrete inputs,
but are not treated as its universal proof.
-/

namespace AspisV5MerkleConsumedValueBridge

open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge

/-! ## Zero-copy parser output -/

/-- Byte offsets returned by `parse_private_opening_from_proof`.  They are
relative to the proof suffix supplied to that one helper call. -/
structure OpeningOffsets where
  count : Nat
  records : Nat
  frontierCount : Nat
  frontier : Nat
  endOffset : Nat
  deriving DecidableEq

/-- Mathematical view of the slices in Rust's `StateOnlyPrivateOpening`.
`record` and `value` below are defined from these flat arrays exactly as the
Rust methods are, rather than stored as independent fields. -/
structure ReturnedOpening where
  count : Nat
  valueWidth : Nat
  records : List Byte
  frontier : List Byte
  offsets : OpeningOffsets
  deriving DecidableEq

def ReturnedOpening.recordWidth (opening : ReturnedOpening) : Nat :=
  opening.valueWidth + 32

def ReturnedOpening.record (opening : ReturnedOpening) (ordinal : Nat) :
    Option (List Byte) :=
  if ordinal < opening.count then
    some ((opening.records.drop (ordinal * opening.recordWidth)).take
      opening.recordWidth)
  else none

def ReturnedOpening.value (opening : ReturnedOpening) (ordinal : Nat) :
    Option (List Byte) :=
  if ordinal < opening.count then
    some ((opening.records.drop (ordinal * opening.recordWidth)).take
      opening.valueWidth)
  else none

def ReturnedOpening.salt (opening : ReturnedOpening) (ordinal : Nat) :
    Option (List Byte) :=
  if ordinal < opening.count then
    some (((opening.records.drop (ordinal * opening.recordWidth)).drop
      opening.valueWidth).take 32)
  else none

/-- Flat digest representation returned as Rust's `frontier` slice. -/
def flattenDigests (frontier : List Digest32) : List Byte :=
  frontier.flatMap digestBytes

def openingOfTrace {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries) : ReturnedOpening :=
  let records := trace.records.flatten
  let frontier := flattenDigests trace.frontier
  { count := trace.records.length
    valueWidth := valueWidth tree
    records := records
    frontier := frontier
    offsets :=
      { count := 0
        records := 2
        frontierCount := 2 + records.length
        frontier := 2 + records.length + 4
        endOffset := 2 + records.length + 4 + frontier.length } }

@[simp] theorem openingOfTrace_count {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries) :
    (openingOfTrace trace).count = trace.records.length := rfl

@[simp] theorem openingOfTrace_valueWidth {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries) :
    (openingOfTrace trace).valueWidth = valueWidth tree := rfl

@[simp] theorem openingOfTrace_records {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries) :
    (openingOfTrace trace).records = trace.records.flatten := rfl

@[simp] theorem openingOfTrace_frontier {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries) :
    (openingOfTrace trace).frontier = flattenDigests trace.frontier := rfl

theorem openingOfTrace_offsets {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries) :
    (openingOfTrace trace).offsets =
      { count := 0
        records := 2
        frontierCount := 2 + trace.records.flatten.length
        frontier := 2 + trace.records.flatten.length + 4
        endOffset := 2 + trace.records.flatten.length + 4 +
          (flattenDigests trace.frontier).length } := rfl

theorem openingOfTrace_wire_exact {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries) :
    trace.wire =
      u16LE (openingOfTrace trace).count ++
        (openingOfTrace trace).records ++
          u32LE trace.frontier.length ++
            (openingOfTrace trace).frontier := by
  simpa [openingOfTrace, flattenDigests] using
    exactSection_wire_is_count_records_frontier trace

theorem flattenDigests_length (frontier : List Digest32) :
    (flattenDigests frontier).length = 32 * frontier.length := by
  simp [flattenDigests, digestBytes_length, mul_comm]

theorem openingOfTrace_endOffset_eq_wire_length {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries) :
    (openingOfTrace trace).offsets.endOffset = trace.wire.length := by
  rw [openingOfTrace_wire_exact]
  simp [openingOfTrace, u16LE_length, u32LE_length, flattenDigests]
  omega

/-! ## Fixed-width flat-record slicing -/

theorem take_drop_flatten_fixed_width {A : Type*}
    (records : List (List A)) (width ordinal : Nat)
    (hall : ∀ record ∈ records, record.length = width)
    (hordinal : ordinal < records.length) :
    ((records.flatten.drop (ordinal * width)).take width) = records[ordinal] := by
  have hlengths : records.map List.length = List.replicate records.length width := by
    apply List.eq_replicate_iff.mpr
    constructor
    · simp
    · intro value hvalue
      simp only [List.mem_map] at hvalue
      obtain ⟨record, hrecord, rfl⟩ := hvalue
      exact hall record hrecord
  have hprefix : ((records.map List.length).take ordinal).sum =
      ordinal * width := by
    rw [hlengths, List.take_replicate, List.sum_replicate]
    simp
    omega
  rw [← hprefix, List.drop_sum_flatten]
  have hdrop : records.drop ordinal = records[ordinal] :: records.drop (ordinal + 1) := by
    rw [List.drop_eq_getElem_cons hordinal]
  rw [hdrop, List.flatten_cons,
    List.take_append_of_le_length
      (hall records[ordinal] (List.getElem_mem hordinal) |>.symm.le)]
  rw [← hall records[ordinal] (List.getElem_mem hordinal), List.take_length]

theorem exactSection_records_uniform_length {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries)
    (record : List Byte) (hrecord : record ∈ trace.records) :
    record.length = valueWidth tree + 32 := by
  simp only [ExactSectionTrace.records, List.mem_map] at hrecord
  obtain ⟨index, hindex, rfl⟩ := hrecord
  apply trace.records_length index
  exact (Finset.mem_sort (.≤.)).mp hindex

def sectionOrdinal (tree : V5PrivateSection) (queries : Finset V5Query)
    (index : Nat) : Nat :=
  (orderedActiveIndices tree queries 0).idxOf index

theorem sectionIndex_mem_ordered (tree : V5PrivateSection)
    {queries : Finset V5Query} {query : V5Query} (hq : query ∈ queries) :
    sectionIndex tree query ∈ orderedActiveIndices tree queries 0 := by
  apply (Finset.mem_sort (.≤.)).mpr
  exact sectionIndex_mem_active tree hq

theorem sectionOrdinal_getElem?_eq (tree : V5PrivateSection)
    {queries : Finset V5Query} {index : Nat}
    (hindex : index ∈ activeIndices tree queries 0) :
    (orderedActiveIndices tree queries 0)[sectionOrdinal tree queries index]? =
      some index := by
  apply List.getElem?_idxOf
  exact (Finset.mem_sort (.≤.)).mpr hindex

theorem sectionOrdinal_lt_count (tree : V5PrivateSection)
    {queries : Finset V5Query} {index : Nat}
    (hindex : index ∈ activeIndices tree queries 0) :
    sectionOrdinal tree queries index <
      (orderedActiveIndices tree queries 0).length := by
  apply (List.idxOf_lt_length_iff).mpr
  exact (Finset.mem_sort (.≤.)).mpr hindex

def sectionValueAtIndex {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries) (index : Nat) :
    List Byte :=
  (trace.recordAt index).take (valueWidth tree)

theorem openingOfTrace_record_at_ordinal {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries)
    {index : Nat} (hindex : index ∈ activeIndices tree queries 0) :
    (openingOfTrace trace).record (sectionOrdinal tree queries index) =
      some (trace.recordAt index) := by
  have hord := sectionOrdinal_lt_count tree hindex
  have hget := sectionOrdinal_getElem?_eq tree hindex
  have hgetMap : trace.records[sectionOrdinal tree queries index]? =
      some (trace.recordAt index) := by
    rw [ExactSectionTrace.records, List.getElem?_map, hget]
    rfl
  have hbound : sectionOrdinal tree queries index < trace.records.length := by
    simpa [ExactSectionTrace.records] using hord
  have hgetElem : trace.records[sectionOrdinal tree queries index] =
      trace.recordAt index := by
    rw [List.getElem?_eq_getElem hbound] at hgetMap
    exact Option.some.inj hgetMap
  rw [ReturnedOpening.record, if_pos]
  · simp only [openingOfTrace_records, ReturnedOpening.recordWidth,
      openingOfTrace_valueWidth]
    rw [take_drop_flatten_fixed_width trace.records
      (valueWidth tree + 32) (sectionOrdinal tree queries index)
      (exactSection_records_uniform_length trace) hbound]
    exact congrArg some hgetElem
  · simpa [openingOfTrace_count, ExactSectionTrace.records] using hord

theorem openingOfTrace_value_at_ordinal {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries)
    {index : Nat} (hindex : index ∈ activeIndices tree queries 0) :
    (openingOfTrace trace).value (sectionOrdinal tree queries index) =
      some (sectionValueAtIndex trace index) := by
  have hord := sectionOrdinal_lt_count tree hindex
  have hget := sectionOrdinal_getElem?_eq tree hindex
  have hgetMap : trace.records[sectionOrdinal tree queries index]? =
      some (trace.recordAt index) := by
    rw [ExactSectionTrace.records, List.getElem?_map, hget]
    rfl
  have hbound : sectionOrdinal tree queries index < trace.records.length := by
    simpa [ExactSectionTrace.records] using hord
  have hgetElem : trace.records[sectionOrdinal tree queries index] =
      trace.recordAt index := by
    rw [List.getElem?_eq_getElem hbound] at hgetMap
    exact Option.some.inj hgetMap
  rw [ReturnedOpening.value, if_pos]
  · simp only [openingOfTrace_records, ReturnedOpening.recordWidth,
      openingOfTrace_valueWidth, sectionValueAtIndex]
    have hrecord := take_drop_flatten_fixed_width trace.records
      (valueWidth tree + 32) (sectionOrdinal tree queries index)
      (exactSection_records_uniform_length trace) hbound
    have hsliced :
        (trace.records.flatten.drop
          (sectionOrdinal tree queries index * (valueWidth tree + 32))).take
            (valueWidth tree + 32) = trace.recordAt index := by
      rw [hrecord, hgetElem]
    have htake := congrArg (List.take (valueWidth tree)) hsliced
    have hwidth : valueWidth tree ≤ valueWidth tree + 32 := by omega
    rw [List.take_take, Nat.min_eq_left hwidth] at htake
    exact congrArg some htake
  · simpa [openingOfTrace_count, ExactSectionTrace.records] using hord

theorem openingOfTrace_query_value_is_authenticated
    {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries)
    (query : V5Query) (hq : query ∈ queries) :
    (openingOfTrace trace).value
        (sectionOrdinal tree queries (sectionIndex tree query)) =
      some (openedValue (trace.acceptedLeaf query hq)) := by
  rw [openingOfTrace_value_at_ordinal trace
    (sectionIndex_mem_active tree hq)]
  rfl

/-! ## One-helper and five-section driver results -/

structure HelperOutput where
  opening : ReturnedOpening
  bytesConsumed : Nat
  remainder : List Byte
  deriving DecidableEq

def helperOutputOfTrace {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries)
    (remainder : List Byte) : HelperOutput where
  opening := openingOfTrace trace
  bytesConsumed := trace.wire.length
  remainder := remainder

theorem helperOutput_exact_consumption {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries)
    (remainder : List Byte) :
    (helperOutputOfTrace trace remainder).bytesConsumed =
        (helperOutputOfTrace trace remainder).opening.offsets.endOffset ∧
      (trace.wire ++ remainder).drop
          (helperOutputOfTrace trace remainder).bytesConsumed = remainder := by
  constructor
  · exact (openingOfTrace_endOffset_eq_wire_length trace).symm
  · simp [helperOutputOfTrace]

structure V5DriverOutput where
  c1 : ReturnedOpening
  c2 : ReturnedOpening
  line1 : ReturnedOpening
  line2 : ReturnedOpening
  line3 : ReturnedOpening
  layer0Indices : List Nat
  line1Indices : List Nat
  line2Indices : List Nat
  line3Indices : List Nat
  bytesConsumed : Nat
  remainder : List Byte
  deriving DecidableEq

def V5DriverOutput.opening (output : V5DriverOutput) :
    V5PrivateSection -> ReturnedOpening
  | .c1 => output.c1
  | .c2 => output.c2
  | .line1 => output.line1
  | .line2 => output.line2
  | .line3 => output.line3

def V5DriverOutput.indices (output : V5DriverOutput) :
    V5PrivateSection -> List Nat
  | .c1 | .c2 => output.layer0Indices
  | .line1 => output.line1Indices
  | .line2 => output.line2Indices
  | .line3 => output.line3Indices

def driverOutputOfRun {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) (remainder : List Byte) :
    V5DriverOutput where
  c1 := openingOfTrace (run.sections .c1)
  c2 := openingOfTrace (run.sections .c2)
  line1 := openingOfTrace (run.sections .line1)
  line2 := openingOfTrace (run.sections .line2)
  line3 := openingOfTrace (run.sections .line3)
  layer0Indices := orderedActiveIndices .c1 queries 0
  line1Indices := orderedActiveIndices .line1 queries 0
  line2Indices := orderedActiveIndices .line2 queries 0
  line3Indices := orderedActiveIndices .line3 queries 0
  bytesConsumed := run.proofBytes.length
  remainder := remainder

theorem c1_c2_ordered_indices_equal (queries : Finset V5Query) :
    orderedActiveIndices .c1 queries 0 =
      orderedActiveIndices .c2 queries 0 := by
  rfl

@[simp] theorem driverOutputOfRun_indices {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) (remainder : List Byte)
    (tree : V5PrivateSection) :
    (driverOutputOfRun run remainder).indices tree =
      orderedActiveIndices tree queries 0 := by
  cases tree <;> simp [driverOutputOfRun, V5DriverOutput.indices,
    c1_c2_ordered_indices_equal]

@[simp] theorem driverOutputOfRun_opening {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) (remainder : List Byte)
    (tree : V5PrivateSection) :
    (driverOutputOfRun run remainder).opening tree =
      openingOfTrace (run.sections tree) := by
  cases tree <;> rfl

theorem driverOutput_exact_bytes_consumed {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) (remainder : List Byte) :
    (driverOutputOfRun run remainder).bytesConsumed =
      (run.sections .c1).wire.length +
      (run.sections .c2).wire.length +
      (run.sections .line1).wire.length +
      (run.sections .line2).wire.length +
      (run.sections .line3).wire.length := by
  simp only [driverOutputOfRun]
  rw [run.proof_eq]
  simp only [List.length_append]

theorem driverOutput_exact_remainder {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) (remainder : List Byte) :
    (run.proofBytes ++ remainder).drop
        (driverOutputOfRun run remainder).bytesConsumed = remainder := by
  simp [driverOutputOfRun]

theorem driverOutput_value_at_index_is_authenticated
    {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) (remainder : List Byte)
    (tree : V5PrivateSection) {index : Nat}
    (hindex : index ∈ activeIndices tree queries 0) :
    ((driverOutputOfRun run remainder).opening tree).value
        (sectionOrdinal tree queries index) =
      some (sectionValueAtIndex (run.sections tree) index) := by
  rw [driverOutputOfRun_opening]
  exact openingOfTrace_value_at_ordinal (run.sections tree) hindex

theorem sectionValueAtIndex_length {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries)
    {index : Nat} (hindex : index ∈ activeIndices tree queries 0) :
    (sectionValueAtIndex trace index).length = valueWidth tree := by
  simp only [sectionValueAtIndex, List.length_take]
  rw [trace.records_length index hindex]
  simp

/-! ## Parent routing used by the FRI reader -/

theorem layer0_parent_mem_line1 {queries : Finset V5Query} {index : Nat}
    (hindex : index ∈ activeIndices .c1 queries 0) :
    index / 4 ∈ activeIndices .line1 queries 0 := by
  rcases Finset.mem_image.mp hindex with ⟨query, hquery, hqueryIndex⟩
  apply Finset.mem_image.mpr
  refine ⟨query, hquery, ?_⟩
  simpa [indexAtRadixLevel, sectionIndex] using
    congrArg (fun value : Nat => value / 4) hqueryIndex

theorem line1_parent_mem_line2 {queries : Finset V5Query} {index : Nat}
    (hindex : index ∈ activeIndices .line1 queries 0) :
    index / 4 ∈ activeIndices .line2 queries 0 := by
  rcases Finset.mem_image.mp hindex with ⟨query, hquery, hqueryIndex⟩
  apply Finset.mem_image.mpr
  refine ⟨query, hquery, ?_⟩
  simp only [indexAtRadixLevel, sectionIndex] at hqueryIndex ⊢
  rw [← hqueryIndex, Nat.div_div_eq_div_mul]

theorem line2_parent_mem_line3 {queries : Finset V5Query} {index : Nat}
    (hindex : index ∈ activeIndices .line2 queries 0) :
    index / 4 ∈ activeIndices .line3 queries 0 := by
  rcases Finset.mem_image.mp hindex with ⟨query, hquery, hqueryIndex⟩
  apply Finset.mem_image.mpr
  refine ⟨query, hquery, ?_⟩
  simp only [indexAtRadixLevel, sectionIndex] at hqueryIndex ⊢
  rw [← hqueryIndex, Nat.div_div_eq_div_mul]

/-! ## Exact byte decoders and production layouts -/

def fixedBytes? (width : Nat) (bytes : List Byte) :
    Option (Fin width -> Byte) :=
  if h : bytes.length = width then
    some fun index => bytes.get ⟨index, by omega⟩
  else none

def byteSlice (bytes : List Byte) (offset width : Nat) : List Byte :=
  (bytes.drop offset).take width

def decodeM31Bytes (bytes : List Byte) :=
  (fixedBytes? 4 bytes).bind
    AspisV5ComponentCQM31Representation.decodeM31LE

def decodeQM31Bytes (bytes : List Byte) :=
  (fixedBytes? 16 bytes).bind
    AspisV5ComponentCQM31Representation.decodeQM31LE

def decodeM31At (bytes : List Byte) (offset : Nat) :=
  decodeM31Bytes (byteSlice bytes offset 4)

def decodeQM31At (bytes : List Byte) (offset : Nat) :=
  decodeQM31Bytes (byteSlice bytes offset 16)

/-- C1's production kernel reads slot-major, then column-major within the
slot: `(slot * 16 + column) * 4`. -/
def decodeC1Entry (value : List Byte) (slot : Fin 4) (column : Fin 16) :=
  decodeM31At value (((slot : Nat) * 16 + (column : Nat)) * 4)

/-- C2 is helper-major with four slots per helper:
`(helper * 4 + slot) * 16`. -/
def decodeC2Entry (value : List Byte) (slot : Fin 4) (helper : Fin 3) :=
  decodeQM31At value (((helper : Nat) * 4 + (slot : Nat)) * 16)

/-- Each later leaf contains four consecutive QM31 values. -/
def decodeLaterSlot (value : List Byte) (slot : Fin 4) :=
  decodeQM31At value ((slot : Nat) * 16)

theorem decodeC1Entry_exact_offset (value : List Byte)
    (slot : Fin 4) (column : Fin 16) :
    decodeC1Entry value slot column =
      decodeM31Bytes (byteSlice value
        (((slot : Nat) * 16 + (column : Nat)) * 4) 4) := rfl

theorem decodeC2Entry_exact_offset (value : List Byte)
    (slot : Fin 4) (helper : Fin 3) :
    decodeC2Entry value slot helper =
      decodeQM31Bytes (byteSlice value
        (((helper : Nat) * 4 + (slot : Nat)) * 16) 16) := rfl

theorem decodeLaterSlot_exact_offset (value : List Byte) (slot : Fin 4) :
    decodeLaterSlot value slot =
      decodeQM31Bytes (byteSlice value ((slot : Nat) * 16) 16) := rfl

/-- Exact code/model edge for the two byte decoders used by the FRI readers.
It is deliberately decoder-only: encoding and field arithmetic are separate
obligations elsewhere in the development. -/
def ExactRustFriByteDecoderEquality
    (rustM31Decode : (Fin 4 -> Byte) ->
      Option AspisV5ComponentCRejectionSampler.M31Value)
    (rustQM31Decode : (Fin 16 -> Byte) ->
      Option AspisV5ComponentCRejectionSampler.QM31Limbs) : Prop :=
  rustM31Decode = AspisV5ComponentCQM31Representation.decodeM31LE ∧
    rustQM31Decode = AspisV5ComponentCQM31Representation.decodeQM31LE

theorem exactRustFriByteDecoders_bind_list_decoders
    (rustM31Decode : (Fin 4 -> Byte) ->
      Option AspisV5ComponentCRejectionSampler.M31Value)
    (rustQM31Decode : (Fin 16 -> Byte) ->
      Option AspisV5ComponentCRejectionSampler.QM31Limbs)
    (hdecode : ExactRustFriByteDecoderEquality rustM31Decode rustQM31Decode) :
    (∀ bytes, decodeM31Bytes bytes =
      (fixedBytes? 4 bytes).bind rustM31Decode) ∧
    (∀ bytes, decodeQM31Bytes bytes =
      (fixedBytes? 16 bytes).bind rustQM31Decode) := by
  constructor
  · intro bytes
    simp [decodeM31Bytes, hdecode.1]
  · intro bytes
    simp [decodeQM31Bytes, hdecode.2]

theorem exactRustFriByteDecoders_bind_all_fri_offsets
    (rustM31Decode : (Fin 4 -> Byte) ->
      Option AspisV5ComponentCRejectionSampler.M31Value)
    (rustQM31Decode : (Fin 16 -> Byte) ->
      Option AspisV5ComponentCRejectionSampler.QM31Limbs)
    (hdecode : ExactRustFriByteDecoderEquality rustM31Decode rustQM31Decode)
    (c1 c2 later : List Byte) :
    (∀ slot column, decodeC1Entry c1 slot column =
      (fixedBytes? 4 (byteSlice c1
        (((slot : Nat) * 16 + (column : Nat)) * 4) 4)).bind rustM31Decode) ∧
    (∀ slot helper, decodeC2Entry c2 slot helper =
      (fixedBytes? 16 (byteSlice c2
        (((helper : Nat) * 4 + (slot : Nat)) * 16) 16)).bind
          rustQM31Decode) ∧
    (∀ slot, decodeLaterSlot later slot =
      (fixedBytes? 16 (byteSlice later ((slot : Nat) * 16) 16)).bind
        rustQM31Decode) := by
  obtain ⟨hm31, hqm31⟩ := exactRustFriByteDecoders_bind_list_decoders
    rustM31Decode rustQM31Decode hdecode
  exact ⟨fun slot column => by
      rw [decodeC1Entry_exact_offset, hm31],
    fun slot helper => by
      rw [decodeC2Entry_exact_offset, hqm31],
    fun slot => by
      rw [decodeLaterSlot_exact_offset, hqm31]⟩

/-! ## The four FRI read schedules -/

structure LayerZeroRead where
  query : Nat
  ordinal : Nat
  c1Value : List Byte
  c2Value : List Byte
  parentIndex : Nat
  parentOrdinal : Nat
  parentValue : List Byte
  parentSlot : Fin 4
  deriving DecidableEq

def LayerZeroRead.c1Decoded (read : LayerZeroRead)
    (slot : Fin 4) (column : Fin 16) :=
  decodeC1Entry read.c1Value slot column

def LayerZeroRead.c2Decoded (read : LayerZeroRead)
    (slot : Fin 4) (helper : Fin 3) :=
  decodeC2Entry read.c2Value slot helper

def LayerZeroRead.expectedParent (read : LayerZeroRead) :=
  decodeLaterSlot read.parentValue read.parentSlot

structure LineTransitionRead where
  layer : Nat
  index : Nat
  ordinal : Nat
  incoming : List Byte
  parentIndex : Nat
  parentOrdinal : Nat
  outgoing : List Byte
  slot : Fin 4
  deriving DecidableEq

def LineTransitionRead.incomingValues (read : LineTransitionRead)
    (slot : Fin 4) :=
  decodeLaterSlot read.incoming slot

def LineTransitionRead.expectedParent (read : LineTransitionRead) :=
  decodeLaterSlot read.outgoing read.slot

structure TerminalRead where
  index : Nat
  ordinal : Nat
  incoming : List Byte
  deriving DecidableEq

def TerminalRead.incomingValues (read : TerminalRead) (slot : Fin 4) :=
  decodeLaterSlot read.incoming slot

structure FriReadSchedule where
  layer0ToLine1 : List LayerZeroRead
  line1ToLine2 : List LineTransitionRead
  line2ToLine3 : List LineTransitionRead
  line3ToFinal : List TerminalRead
  deriving DecidableEq

def layerZeroReadOfRun {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) (query : Nat) : LayerZeroRead where
  query := query
  ordinal := sectionOrdinal .c1 queries query
  c1Value := sectionValueAtIndex (run.sections .c1) query
  c2Value := sectionValueAtIndex (run.sections .c2) query
  parentIndex := query / 4
  parentOrdinal := sectionOrdinal .line1 queries (query / 4)
  parentValue := sectionValueAtIndex (run.sections .line1) (query / 4)
  parentSlot := ⟨query % 4, Nat.mod_lt _ (by decide)⟩

def line1ReadOfRun {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) (index : Nat) :
    LineTransitionRead where
  layer := 1
  index := index
  ordinal := sectionOrdinal .line1 queries index
  incoming := sectionValueAtIndex (run.sections .line1) index
  parentIndex := index / 4
  parentOrdinal := sectionOrdinal .line2 queries (index / 4)
  outgoing := sectionValueAtIndex (run.sections .line2) (index / 4)
  slot := ⟨index % 4, Nat.mod_lt _ (by decide)⟩

def line2ReadOfRun {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) (index : Nat) :
    LineTransitionRead where
  layer := 2
  index := index
  ordinal := sectionOrdinal .line2 queries index
  incoming := sectionValueAtIndex (run.sections .line2) index
  parentIndex := index / 4
  parentOrdinal := sectionOrdinal .line3 queries (index / 4)
  outgoing := sectionValueAtIndex (run.sections .line3) (index / 4)
  slot := ⟨index % 4, Nat.mod_lt _ (by decide)⟩

def terminalReadOfRun {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) (index : Nat) : TerminalRead where
  index := index
  ordinal := sectionOrdinal .line3 queries index
  incoming := sectionValueAtIndex (run.sections .line3) index

def friReadScheduleOfRun {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) : FriReadSchedule where
  layer0ToLine1 :=
    (orderedActiveIndices .c1 queries 0).map (layerZeroReadOfRun run)
  line1ToLine2 :=
    (orderedActiveIndices .line1 queries 0).map (line1ReadOfRun run)
  line2ToLine3 :=
    (orderedActiveIndices .line2 queries 0).map (line2ReadOfRun run)
  line3ToFinal :=
    (orderedActiveIndices .line3 queries 0).map (terminalReadOfRun run)

theorem activeIndices_c1_eq_c2 (queries : Finset V5Query) :
    activeIndices .c1 queries 0 = activeIndices .c2 queries 0 := by
  ext index
  simp [activeIndices, sectionIndex]

theorem sectionOrdinal_c1_eq_c2 (queries : Finset V5Query) (index : Nat) :
    sectionOrdinal .c1 queries index = sectionOrdinal .c2 queries index := by
  simp only [sectionOrdinal]
  rw [c1_c2_ordered_indices_equal]

theorem sectionValueAtIndex_is_authenticated
    {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries)
    {index : Nat} (hindex : index ∈ activeIndices tree queries 0) :
    ∃ query : V5Query, ∃ hquery : query ∈ queries,
      sectionIndex tree query = index ∧
        sectionValueAtIndex trace index =
          openedValue (trace.acceptedLeaf query hquery) := by
  rcases Finset.mem_image.mp hindex with ⟨query, hquery, hindexEq⟩
  refine ⟨query, hquery, hindexEq, ?_⟩
  subst index
  rfl

theorem layerZeroRead_exact_returned_values
    {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) (remainder : List Byte)
    {query : Nat} (hquery : query ∈ activeIndices .c1 queries 0) :
    let read := layerZeroReadOfRun run query
    let output := driverOutputOfRun run remainder
    output.layer0Indices[read.ordinal]? = some query ∧
      output.c1.value read.ordinal = some read.c1Value ∧
      output.c2.value read.ordinal = some read.c2Value ∧
      output.line1Indices[read.parentOrdinal]? = some read.parentIndex ∧
      output.line1.value read.parentOrdinal = some read.parentValue := by
  dsimp only [layerZeroReadOfRun]
  have hc2 : query ∈ activeIndices .c2 queries 0 := by
    simpa [activeIndices_c1_eq_c2] using hquery
  have hparent := layer0_parent_mem_line1 hquery
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact sectionOrdinal_getElem?_eq .c1 hquery
  · exact driverOutput_value_at_index_is_authenticated run remainder .c1 hquery
  · rw [sectionOrdinal_c1_eq_c2]
    exact driverOutput_value_at_index_is_authenticated run remainder .c2 hc2
  · exact sectionOrdinal_getElem?_eq .line1 hparent
  · exact driverOutput_value_at_index_is_authenticated run remainder .line1 hparent

theorem layerZeroRead_exact_widths {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries)
    {query : Nat} (hquery : query ∈ activeIndices .c1 queries 0) :
    let read := layerZeroReadOfRun run query
    read.c1Value.length = 256 ∧ read.c2Value.length = 192 ∧
      read.parentValue.length = 64 := by
  dsimp only [layerZeroReadOfRun]
  have hc2 : query ∈ activeIndices .c2 queries 0 := by
    simpa [activeIndices_c1_eq_c2] using hquery
  have hparent := layer0_parent_mem_line1 hquery
  simpa [valueWidth] using And.intro
    (sectionValueAtIndex_length (run.sections .c1) hquery)
    (And.intro (sectionValueAtIndex_length (run.sections .c2) hc2)
      (sectionValueAtIndex_length (run.sections .line1) hparent))

theorem line1Read_exact_returned_values
    {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) (remainder : List Byte)
    {index : Nat} (hindex : index ∈ activeIndices .line1 queries 0) :
    let read := line1ReadOfRun run index
    let output := driverOutputOfRun run remainder
    output.line1Indices[read.ordinal]? = some index ∧
      output.line1.value read.ordinal = some read.incoming ∧
      output.line2Indices[read.parentOrdinal]? = some read.parentIndex ∧
      output.line2.value read.parentOrdinal = some read.outgoing := by
  dsimp only [line1ReadOfRun]
  have hparent := line1_parent_mem_line2 hindex
  exact ⟨sectionOrdinal_getElem?_eq .line1 hindex,
    driverOutput_value_at_index_is_authenticated run remainder .line1 hindex,
    sectionOrdinal_getElem?_eq .line2 hparent,
    driverOutput_value_at_index_is_authenticated run remainder .line2 hparent⟩

theorem line2Read_exact_returned_values
    {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) (remainder : List Byte)
    {index : Nat} (hindex : index ∈ activeIndices .line2 queries 0) :
    let read := line2ReadOfRun run index
    let output := driverOutputOfRun run remainder
    output.line2Indices[read.ordinal]? = some index ∧
      output.line2.value read.ordinal = some read.incoming ∧
      output.line3Indices[read.parentOrdinal]? = some read.parentIndex ∧
      output.line3.value read.parentOrdinal = some read.outgoing := by
  dsimp only [line2ReadOfRun]
  have hparent := line2_parent_mem_line3 hindex
  exact ⟨sectionOrdinal_getElem?_eq .line2 hindex,
    driverOutput_value_at_index_is_authenticated run remainder .line2 hindex,
    sectionOrdinal_getElem?_eq .line3 hparent,
    driverOutput_value_at_index_is_authenticated run remainder .line3 hparent⟩

theorem terminalRead_exact_returned_value
    {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) (remainder : List Byte)
    {index : Nat} (hindex : index ∈ activeIndices .line3 queries 0) :
    let read := terminalReadOfRun run index
    let output := driverOutputOfRun run remainder
    output.line3Indices[read.ordinal]? = some index ∧
      output.line3.value read.ordinal = some read.incoming := by
  dsimp only [terminalReadOfRun]
  exact ⟨sectionOrdinal_getElem?_eq .line3 hindex,
    driverOutput_value_at_index_is_authenticated run remainder .line3 hindex⟩

theorem line1Read_exact_widths {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries)
    {index : Nat} (hindex : index ∈ activeIndices .line1 queries 0) :
    let read := line1ReadOfRun run index
    read.incoming.length = 64 ∧ read.outgoing.length = 64 := by
  dsimp only [line1ReadOfRun]
  have hparent := line1_parent_mem_line2 hindex
  simpa [valueWidth] using And.intro
    (sectionValueAtIndex_length (run.sections .line1) hindex)
    (sectionValueAtIndex_length (run.sections .line2) hparent)

theorem line2Read_exact_widths {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries)
    {index : Nat} (hindex : index ∈ activeIndices .line2 queries 0) :
    let read := line2ReadOfRun run index
    read.incoming.length = 64 ∧ read.outgoing.length = 64 := by
  dsimp only [line2ReadOfRun]
  have hparent := line2_parent_mem_line3 hindex
  simpa [valueWidth] using And.intro
    (sectionValueAtIndex_length (run.sections .line2) hindex)
    (sectionValueAtIndex_length (run.sections .line3) hparent)

theorem terminalRead_exact_width {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries)
    {index : Nat} (hindex : index ∈ activeIndices .line3 queries 0) :
    (terminalReadOfRun run index).incoming.length = 64 := by
  simpa [terminalReadOfRun, valueWidth] using
    sectionValueAtIndex_length (run.sections .line3) hindex

/-- Every entry in the first production loop is the exact returned C1/C2
value and returned line-1 parent value at the sorted ordinals. -/
theorem every_layer0_schedule_read_is_returned
    {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) (remainder : List Byte)
    (read : LayerZeroRead)
    (hread : read ∈ (friReadScheduleOfRun run).layer0ToLine1) :
    let output := driverOutputOfRun run remainder
    output.layer0Indices[read.ordinal]? = some read.query ∧
      output.c1.value read.ordinal = some read.c1Value ∧
      output.c2.value read.ordinal = some read.c2Value ∧
      output.line1Indices[read.parentOrdinal]? = some read.parentIndex ∧
      output.line1.value read.parentOrdinal = some read.parentValue := by
  simp only [friReadScheduleOfRun, List.mem_map] at hread
  obtain ⟨query, hqueryList, rfl⟩ := hread
  have hquery : query ∈ activeIndices .c1 queries 0 :=
    (Finset.mem_sort (.≤.)).mp hqueryList
  exact layerZeroRead_exact_returned_values run remainder hquery

theorem every_line1_schedule_read_is_returned
    {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) (remainder : List Byte)
    (read : LineTransitionRead)
    (hread : read ∈ (friReadScheduleOfRun run).line1ToLine2) :
    let output := driverOutputOfRun run remainder
    output.line1Indices[read.ordinal]? = some read.index ∧
      output.line1.value read.ordinal = some read.incoming ∧
      output.line2Indices[read.parentOrdinal]? = some read.parentIndex ∧
      output.line2.value read.parentOrdinal = some read.outgoing := by
  simp only [friReadScheduleOfRun, List.mem_map] at hread
  obtain ⟨index, hindexList, rfl⟩ := hread
  exact line1Read_exact_returned_values run remainder
    ((Finset.mem_sort (.≤.)).mp hindexList)

theorem every_line2_schedule_read_is_returned
    {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) (remainder : List Byte)
    (read : LineTransitionRead)
    (hread : read ∈ (friReadScheduleOfRun run).line2ToLine3) :
    let output := driverOutputOfRun run remainder
    output.line2Indices[read.ordinal]? = some read.index ∧
      output.line2.value read.ordinal = some read.incoming ∧
      output.line3Indices[read.parentOrdinal]? = some read.parentIndex ∧
      output.line3.value read.parentOrdinal = some read.outgoing := by
  simp only [friReadScheduleOfRun, List.mem_map] at hread
  obtain ⟨index, hindexList, rfl⟩ := hread
  exact line2Read_exact_returned_values run remainder
    ((Finset.mem_sort (.≤.)).mp hindexList)

theorem every_terminal_schedule_read_is_returned
    {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) (remainder : List Byte)
    (read : TerminalRead)
    (hread : read ∈ (friReadScheduleOfRun run).line3ToFinal) :
    let output := driverOutputOfRun run remainder
    output.line3Indices[read.ordinal]? = some read.index ∧
      output.line3.value read.ordinal = some read.incoming := by
  simp only [friReadScheduleOfRun, List.mem_map] at hread
  obtain ⟨index, hindexList, rfl⟩ := hread
  exact terminalRead_exact_returned_value run remainder
    ((Finset.mem_sort (.≤.)).mp hindexList)

/-- A byte string is authenticated at `index` when it is the value prefix of
one of the section records whose path reaches the public root. -/
def AuthenticatedSectionValue {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) (tree : V5PrivateSection)
    (index : Nat) (value : List Byte) : Prop :=
  ∃ query : V5Query, ∃ hquery : query ∈ queries,
    sectionIndex tree query = index ∧
      value = openedValue ((run.sections tree).acceptedLeaf query hquery)

theorem sectionValueAtIndex_is_AuthenticatedSectionValue
    {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) (tree : V5PrivateSection)
    {index : Nat} (hindex : index ∈ activeIndices tree queries 0) :
    AuthenticatedSectionValue run tree index
      (sectionValueAtIndex (run.sections tree) index) :=
  sectionValueAtIndex_is_authenticated (run.sections tree) hindex

theorem every_layer0_schedule_read_is_authenticated
    {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) (read : LayerZeroRead)
    (hread : read ∈ (friReadScheduleOfRun run).layer0ToLine1) :
    AuthenticatedSectionValue run .c1 read.query read.c1Value ∧
      AuthenticatedSectionValue run .c2 read.query read.c2Value ∧
      AuthenticatedSectionValue run .line1 read.parentIndex
        read.parentValue := by
  simp only [friReadScheduleOfRun, List.mem_map] at hread
  obtain ⟨query, hqueryList, rfl⟩ := hread
  have hquery : query ∈ activeIndices .c1 queries 0 :=
    (Finset.mem_sort (.≤.)).mp hqueryList
  have hc2 : query ∈ activeIndices .c2 queries 0 := by
    simpa [activeIndices_c1_eq_c2] using hquery
  have hparent := layer0_parent_mem_line1 hquery
  exact ⟨sectionValueAtIndex_is_AuthenticatedSectionValue run .c1 hquery,
    sectionValueAtIndex_is_AuthenticatedSectionValue run .c2 hc2,
    sectionValueAtIndex_is_AuthenticatedSectionValue run .line1 hparent⟩

theorem every_line1_schedule_read_is_authenticated
    {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) (read : LineTransitionRead)
    (hread : read ∈ (friReadScheduleOfRun run).line1ToLine2) :
    AuthenticatedSectionValue run .line1 read.index read.incoming ∧
      AuthenticatedSectionValue run .line2 read.parentIndex read.outgoing := by
  simp only [friReadScheduleOfRun, List.mem_map] at hread
  obtain ⟨index, hindexList, rfl⟩ := hread
  have hindex : index ∈ activeIndices .line1 queries 0 :=
    (Finset.mem_sort (.≤.)).mp hindexList
  exact ⟨sectionValueAtIndex_is_AuthenticatedSectionValue run .line1 hindex,
    sectionValueAtIndex_is_AuthenticatedSectionValue run .line2
      (line1_parent_mem_line2 hindex)⟩

theorem every_line2_schedule_read_is_authenticated
    {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) (read : LineTransitionRead)
    (hread : read ∈ (friReadScheduleOfRun run).line2ToLine3) :
    AuthenticatedSectionValue run .line2 read.index read.incoming ∧
      AuthenticatedSectionValue run .line3 read.parentIndex read.outgoing := by
  simp only [friReadScheduleOfRun, List.mem_map] at hread
  obtain ⟨index, hindexList, rfl⟩ := hread
  have hindex : index ∈ activeIndices .line2 queries 0 :=
    (Finset.mem_sort (.≤.)).mp hindexList
  exact ⟨sectionValueAtIndex_is_AuthenticatedSectionValue run .line2 hindex,
    sectionValueAtIndex_is_AuthenticatedSectionValue run .line3
      (line2_parent_mem_line3 hindex)⟩

theorem every_terminal_schedule_read_is_authenticated
    {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) (read : TerminalRead)
    (hread : read ∈ (friReadScheduleOfRun run).line3ToFinal) :
    AuthenticatedSectionValue run .line3 read.index read.incoming := by
  simp only [friReadScheduleOfRun, List.mem_map] at hread
  obtain ⟨index, hindexList, rfl⟩ := hread
  exact sectionValueAtIndex_is_AuthenticatedSectionValue run .line3
    ((Finset.mem_sort (.≤.)).mp hindexList)

theorem friReadSchedule_has_exact_four_production_loops
    {sha256 roots queries} (run : ExactV5Run sha256 roots queries) :
    (friReadScheduleOfRun run).layer0ToLine1 =
        (orderedActiveIndices .c1 queries 0).map (layerZeroReadOfRun run) ∧
      (friReadScheduleOfRun run).line1ToLine2 =
        (orderedActiveIndices .line1 queries 0).map (line1ReadOfRun run) ∧
      (friReadScheduleOfRun run).line2ToLine3 =
        (orderedActiveIndices .line2 queries 0).map (line2ReadOfRun run) ∧
      (friReadScheduleOfRun run).line3ToFinal =
        (orderedActiveIndices .line3 queries 0).map (terminalReadOfRun run) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Smallest remaining source equality -/

/-- Observable output of the real helper/driver plus the byte slices passed to
the four FRI checks.  An extraction adapter for Rust should populate this from
the actual returned `StateOnlyPrivateOpening` views and actual arguments to
`gamma_combine_v5_layer0_exact`,
`check_fixed_line_transition_prepared_polynomial_powers`, and
`check_fixed_terminal_transition_prepared_polynomial_refs`. -/
structure OpeningAndFriObservation where
  driver : V5DriverOutput
  friReads : FriReadSchedule
  deriving DecidableEq

def observationOfRun {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) : OpeningAndFriObservation where
  driver := driverOutputOfRun run []
  friReads := friReadScheduleOfRun run

def ExactOpeningAndFriObservation (sha256 : List Byte -> Digest32)
    (call : V5ProductionCall) (observation : OpeningAndFriObservation) : Prop :=
  ∃ run : ExactV5Run sha256 call.roots call.queries,
    run.proofBytes = call.proofBytes ∧ observation = observationOfRun run

theorem friReadSchedule_eq_of_driverOutput_eq
    {sha256 roots queries}
    (left right : ExactV5Run sha256 roots queries)
    (hdriver : driverOutputOfRun left [] = driverOutputOfRun right []) :
    friReadScheduleOfRun left = friReadScheduleOfRun right := by
  have hvalue (tree : V5PrivateSection) {index : Nat}
      (hindex : index ∈ activeIndices tree queries 0) :
      sectionValueAtIndex (left.sections tree) index =
        sectionValueAtIndex (right.sections tree) index := by
    have hleft :=
      driverOutput_value_at_index_is_authenticated left [] tree hindex
    have hright :=
      driverOutput_value_at_index_is_authenticated right [] tree hindex
    rw [hdriver] at hleft
    exact Option.some.inj (hleft.symm.trans hright)
  have hlayer0 :
      (orderedActiveIndices .c1 queries 0).map (layerZeroReadOfRun left) =
        (orderedActiveIndices .c1 queries 0).map (layerZeroReadOfRun right) := by
    apply List.map_congr_left
    intro index hindexList
    have hindex : index ∈ activeIndices .c1 queries 0 :=
      (Finset.mem_sort (.≤.)).mp hindexList
    have hc2 : index ∈ activeIndices .c2 queries 0 := by
      simpa [activeIndices_c1_eq_c2] using hindex
    have hparent := layer0_parent_mem_line1 hindex
    simp only [layerZeroReadOfRun]
    congr 1
    · exact hvalue .c1 hindex
    · exact hvalue .c2 hc2
    · exact hvalue .line1 hparent
  have hline1 :
      (orderedActiveIndices .line1 queries 0).map (line1ReadOfRun left) =
        (orderedActiveIndices .line1 queries 0).map (line1ReadOfRun right) := by
    apply List.map_congr_left
    intro index hindexList
    have hindex : index ∈ activeIndices .line1 queries 0 :=
      (Finset.mem_sort (.≤.)).mp hindexList
    have hparent := line1_parent_mem_line2 hindex
    simp only [line1ReadOfRun]
    congr 1
    · exact hvalue .line1 hindex
    · exact hvalue .line2 hparent
  have hline2 :
      (orderedActiveIndices .line2 queries 0).map (line2ReadOfRun left) =
        (orderedActiveIndices .line2 queries 0).map (line2ReadOfRun right) := by
    apply List.map_congr_left
    intro index hindexList
    have hindex : index ∈ activeIndices .line2 queries 0 :=
      (Finset.mem_sort (.≤.)).mp hindexList
    have hparent := line2_parent_mem_line3 hindex
    simp only [line2ReadOfRun]
    congr 1
    · exact hvalue .line2 hindex
    · exact hvalue .line3 hparent
  have hterminal :
      (orderedActiveIndices .line3 queries 0).map (terminalReadOfRun left) =
        (orderedActiveIndices .line3 queries 0).map (terminalReadOfRun right) := by
    apply List.map_congr_left
    intro index hindexList
    have hindex : index ∈ activeIndices .line3 queries 0 :=
      (Finset.mem_sort (.≤.)).mp hindexList
    simp only [terminalReadOfRun]
    congr 1
    exact hvalue .line3 hindex
  unfold friReadScheduleOfRun
  congr

/-- Source boundary for the parser/authentication half only.  A successful
production observation must expose the five returned openings, sorted index
lists, offsets, consumption count, and empty remainder of one exact modeled
run.  This says nothing yet about which values the later FRI loops read. -/
def ExactRustV5OpeningParserOutputEquality
    (sha256 : List Byte -> Digest32)
    (rustObservation : V5ProductionCall -> Option OpeningAndFriObservation) :
    Prop :=
  ∀ call observation, rustObservation call = some observation ->
    ∃ run : ExactV5Run sha256 call.roots call.queries,
      run.proofBytes = call.proofBytes ∧
        observation.driver = driverOutputOfRun run []

/-- Source boundary left for the actual four FRI loops after the returned
opening views are fixed.  It covers their monotone-index traversal, parent
index and slot calculation, and the exact record-value slices passed to each
check.  The separately extracted record/value accessor proof and byte-decoder
proof do not establish this loop-level dataflow equality. -/
def ExactRustV5FriLoopReadEquality
    (sha256 : List Byte -> Digest32)
    (rustObservation : V5ProductionCall -> Option OpeningAndFriObservation) :
    Prop :=
  ∀ call observation (run : ExactV5Run sha256 call.roots call.queries),
    rustObservation call = some observation ->
    run.proofBytes = call.proofBytes ->
    observation.driver = driverOutputOfRun run [] ->
    observation.friReads = friReadScheduleOfRun run

/-- The output/dataflow executable premise left by this module.
`rustObservation` returns
`some` only for a successful Rust execution which completed all four FRI
loops.  Unlike the earlier boolean helper premise, the observation includes
the returned records/frontier slices, offsets, sorted indices,
bytes-consumed/remainder result, and every byte slice actually handed to the
four FRI checks.

The separate `ExactRustFriByteDecoderEquality` above is the smaller
byte-decoder premise; this observation relation does not silently absorb it.

Only the security-relevant direction is required: every successful Rust
observation must equal a modeled observation.  The reverse would incorrectly
claim that Merkle-valid but algebraically invalid values pass FRI.  This
proposition is not assumed by any deterministic theorem above. -/
def ExactRustV5OpeningAndFriConsumerEquality
    (sha256 : List Byte -> Digest32)
    (rustObservation : V5ProductionCall -> Option OpeningAndFriObservation) :
    Prop :=
  ∀ call observation, rustObservation call = some observation ->
    ExactOpeningAndFriObservation sha256 call observation

theorem exactRustV5OpeningAndFriConsumerEquality_iff_split
    (sha256 : List Byte -> Digest32)
    (rustObservation : V5ProductionCall -> Option OpeningAndFriObservation) :
    ExactRustV5OpeningAndFriConsumerEquality sha256 rustObservation ↔
      ExactRustV5OpeningParserOutputEquality sha256 rustObservation ∧
        ExactRustV5FriLoopReadEquality sha256 rustObservation := by
  constructor
  · intro hsource
    constructor
    · intro call observation hrust
      obtain ⟨run, hbytes, hobservation⟩ := hsource call observation hrust
      exact ⟨run, hbytes, congrArg OpeningAndFriObservation.driver hobservation⟩
    · intro call observation run hrust hbytes hdriver
      obtain ⟨sourceRun, hsourceBytes, hobservation⟩ :=
        hsource call observation hrust
      have hdriverSource : observation.driver =
          driverOutputOfRun sourceRun [] :=
        congrArg OpeningAndFriObservation.driver hobservation
      have hschedules : friReadScheduleOfRun run =
          friReadScheduleOfRun sourceRun :=
        friReadSchedule_eq_of_driverOutput_eq run sourceRun
          (hdriver.symm.trans hdriverSource)
      calc
        observation.friReads = friReadScheduleOfRun sourceRun :=
          congrArg OpeningAndFriObservation.friReads hobservation
        _ = friReadScheduleOfRun run := hschedules.symm
  · intro hsource call observation hrust
    obtain ⟨run, hbytes, hdriver⟩ := hsource.1 call observation hrust
    have hreads := hsource.2 call observation run hrust hbytes hdriver
    refine ⟨run, hbytes, ?_⟩
    cases observation
    simp_all [observationOfRun]

theorem rustObservation_exposes_only_authenticated_fri_values
    (sha256 : List Byte -> Digest32)
    (rustObservation : V5ProductionCall -> Option OpeningAndFriObservation)
    (hsource : ExactRustV5OpeningAndFriConsumerEquality sha256 rustObservation)
    (call : V5ProductionCall) (observation : OpeningAndFriObservation)
    (hrust : rustObservation call = some observation) :
    ∃ run : ExactV5Run sha256 call.roots call.queries,
      run.proofBytes = call.proofBytes ∧
      observation.driver = driverOutputOfRun run [] ∧
      observation.friReads = friReadScheduleOfRun run ∧
      (∀ read, read ∈ observation.friReads.layer0ToLine1 ->
        observation.driver.c1.value read.ordinal = some read.c1Value ∧
        observation.driver.c2.value read.ordinal = some read.c2Value ∧
        observation.driver.line1.value read.parentOrdinal =
          some read.parentValue) ∧
      (∀ read, read ∈ observation.friReads.line1ToLine2 ->
        observation.driver.line1.value read.ordinal = some read.incoming ∧
        observation.driver.line2.value read.parentOrdinal =
          some read.outgoing) ∧
      (∀ read, read ∈ observation.friReads.line2ToLine3 ->
        observation.driver.line2.value read.ordinal = some read.incoming ∧
        observation.driver.line3.value read.parentOrdinal =
          some read.outgoing) ∧
      (∀ read, read ∈ observation.friReads.line3ToFinal ->
        observation.driver.line3.value read.ordinal = some read.incoming) ∧
      (∀ read, read ∈ observation.friReads.layer0ToLine1 ->
        AuthenticatedSectionValue run .c1 read.query read.c1Value ∧
          AuthenticatedSectionValue run .c2 read.query read.c2Value ∧
          AuthenticatedSectionValue run .line1 read.parentIndex
            read.parentValue) ∧
      (∀ read, read ∈ observation.friReads.line1ToLine2 ->
        AuthenticatedSectionValue run .line1 read.index read.incoming ∧
          AuthenticatedSectionValue run .line2 read.parentIndex
            read.outgoing) ∧
      (∀ read, read ∈ observation.friReads.line2ToLine3 ->
        AuthenticatedSectionValue run .line2 read.index read.incoming ∧
          AuthenticatedSectionValue run .line3 read.parentIndex
            read.outgoing) ∧
      (∀ read, read ∈ observation.friReads.line3ToFinal ->
        AuthenticatedSectionValue run .line3 read.index read.incoming) := by
  obtain ⟨run, hbytes, hobservation⟩ := hsource call observation hrust
  subst observation
  refine ⟨run, hbytes, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro read hread
    have h := every_layer0_schedule_read_is_returned run [] read hread
    exact ⟨h.2.1, h.2.2.1, h.2.2.2.2⟩
  · intro read hread
    have h := every_line1_schedule_read_is_returned run [] read hread
    exact ⟨h.2.1, h.2.2.2⟩
  · intro read hread
    have h := every_line2_schedule_read_is_returned run [] read hread
    exact ⟨h.2.1, h.2.2.2⟩
  · intro read hread
    exact (every_terminal_schedule_read_is_returned run [] read hread).2
  · exact every_layer0_schedule_read_is_authenticated run
  · exact every_line1_schedule_read_is_authenticated run
  · exact every_line2_schedule_read_is_authenticated run
  · exact every_terminal_schedule_read_is_authenticated run

/-! ## Audit -/

#print axioms openingOfTrace_endOffset_eq_wire_length
#print axioms openingOfTrace_value_at_ordinal
#print axioms openingOfTrace_query_value_is_authenticated
#print axioms driverOutput_exact_bytes_consumed
#print axioms driverOutput_value_at_index_is_authenticated
#print axioms exactRustFriByteDecoders_bind_all_fri_offsets
#print axioms sectionValueAtIndex_is_authenticated
#print axioms every_layer0_schedule_read_is_returned
#print axioms every_line1_schedule_read_is_returned
#print axioms every_line2_schedule_read_is_returned
#print axioms every_terminal_schedule_read_is_returned
#print axioms every_layer0_schedule_read_is_authenticated
#print axioms every_line1_schedule_read_is_authenticated
#print axioms every_line2_schedule_read_is_authenticated
#print axioms every_terminal_schedule_read_is_authenticated
#print axioms friReadSchedule_eq_of_driverOutput_eq
#print axioms exactRustV5OpeningAndFriConsumerEquality_iff_split
#print axioms rustObservation_exposes_only_authenticated_fri_values

end AspisV5MerkleConsumedValueBridge
