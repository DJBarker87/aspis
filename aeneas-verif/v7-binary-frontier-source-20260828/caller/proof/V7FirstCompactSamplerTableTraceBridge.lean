import V7FirstCompactSamplerK13PositionBridge
import AspisFormal.K1.V7Tag73DeterministicRefinement
import AspisFormal.K1.V7Tag73ReturnedPlanSemantics

/-!
# Translated q16 squeeze trace to the fixed Tag-73 oracle table

This module is the deterministic source/scheduler seam.  A table-aligned
translated trace records the two literal lookups made by every production
`squeeze_block`.  The main theorem proves that the semantic Tag-73 duplex over
that same fixed table returns byte-for-byte the translated source blocks and
ends in the translated source digest.

The only remaining caller obligation is operational: show that the production
hash callback used by the accepted translated run is backed by the exact
scheduler table at those recorded inputs.  No decoder, probability, or
cryptographic premise occurs here.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace V7FirstCompactSamplerTableTraceBridge

open V7FirstCompactSource
open V7FirstCompactSamplerNativeBlockBridge
open V7FirstCompactSqueezeSourceBridge
open V7FirstCompactSamplerOuterLoopBridge
open V7FirstCompactSamplerK13PositionBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ReturnedPlanSemantics
open AspisK1.V7FsAokExperiment

abbrev Transcript := transcript.Transcript

/-- Total semantic oracle induced by the accepted fixed table. Missing inputs
receive the standard zero default; the trace relation below proves every input
used by the accepted source path is present. -/
def fixedTableHashOracle (table : FixedOracleTable) : HashOracle where
  answer := fun input => (tableLookup table input).getD (zeroBytes 32)

theorem fixed_table_hash_oracle_answer_of_lookup
    (table : FixedOracleTable) (input : ByteString) (output : Digest256)
    (found : tableLookup table input = some output) :
    (fixedTableHashOracle table).answer input = output := by
  simp [fixedTableHashOracle, found]

/-- Exact mathematical digest represented by the translated transcript state. -/
def nativeTranscriptDigest (self : Transcript) : Digest256 :=
  nativeSourceDigest (sourceSqueezeBytes self.state)

/-- Exact operational scheduler/source coherence restricted to the finite
callback inputs actually exercised by the extracted trace.  Every constructor
records the output and advance lookup for one literal successful source
`squeeze_block`; requiring callback coverage globally would be impossible for
a total SHA callback and a finite table. -/
inductive HashCallbackRecordedInFixedTable (table : FixedOracleTable) :
    {initial : Transcript} → {blocks : List SourceSqueezeBlock} →
      {final : Transcript} →
      NativeExactSqueezeTrace initial blocks final → Prop
  | nil (self : Transcript) :
      HashCallbackRecordedInFixedTable table
        (NativeExactSqueezeTrace.nil self)
  | cons (self next final : Transcript) (block : SourceSqueezeBlock)
      (blocks : List SourceSqueezeBlock)
      (sourceRun :
        transcript.Transcript.squeeze_block self = .ok (block, next))
      (tail : NativeExactSqueezeTrace next blocks final)
      (outputLookup :
        tableLookup table
            (nativeHashInputBytes (taggedHashInput self 1#u8)) =
          some (nativeSourceDigest (sourceSqueezeBytes block)))
      (advanceLookup :
        tableLookup table
            (nativeHashInputBytes (taggedHashInput self 2#u8)) =
          some (nativeSourceDigest (sourceSqueezeBytes next.state)))
      (tailRecorded : HashCallbackRecordedInFixedTable table tail) :
      HashCallbackRecordedInFixedTable table
        (NativeExactSqueezeTrace.cons self next final block blocks sourceRun
          tail)

/-- Scheduler-facing form of finite source/table coherence.  It asks only that
the fixed table contain SHA-256 at the two exact inputs exercised by each
source squeeze.  The production callback equality is kept in the permitted
SHA-256 source boundary and discharged separately below. -/
inductive ShaTraceInputsRecordedInFixedTable (table : FixedOracleTable)
    (sha256 : ByteString → Digest256) :
    {initial : Transcript} → {blocks : List SourceSqueezeBlock} →
      {final : Transcript} →
      NativeExactSqueezeTrace initial blocks final → Prop
  | nil (self : Transcript) :
      ShaTraceInputsRecordedInFixedTable table sha256
        (NativeExactSqueezeTrace.nil self)
  | cons (self next final : Transcript) (block : SourceSqueezeBlock)
      (blocks : List SourceSqueezeBlock)
      (sourceRun :
        transcript.Transcript.squeeze_block self = .ok (block, next))
      (tail : NativeExactSqueezeTrace next blocks final)
      (outputLookup :
        tableLookup table
            (nativeHashInputBytes (taggedHashInput self 1#u8)) =
          some (sha256 (nativeHashInputBytes (taggedHashInput self 1#u8))))
      (advanceLookup :
        tableLookup table
            (nativeHashInputBytes (taggedHashInput self 2#u8)) =
          some (sha256 (nativeHashInputBytes (taggedHashInput self 2#u8))))
      (tailRecorded : ShaTraceInputsRecordedInFixedTable table sha256 tail) :
      ShaTraceInputsRecordedInFixedTable table sha256
        (NativeExactSqueezeTrace.cons self next final block blocks sourceRun
          tail)

/-- Exact chronological scheduler query-pair representation of a translated
q16 source trace.  Each source squeeze contributes its output query followed
by its advance query, with the permitted SHA-256 function fixing both answers.
This is the precise ordering consumed by `QueryPairsCoveredByTable`. -/
inductive NativeSqueezeTraceShaQueryPairs
    (sha256 : ByteString → Digest256) :
    {initial : Transcript} → {blocks : List SourceSqueezeBlock} →
      {final : Transcript} →
      NativeExactSqueezeTrace initial blocks final →
      List (ShaInput × ShaOutput) → Prop
  | nil (self : Transcript) :
      NativeSqueezeTraceShaQueryPairs sha256
        (NativeExactSqueezeTrace.nil self) []
  | cons (self next final : Transcript) (block : SourceSqueezeBlock)
      (blocks : List SourceSqueezeBlock)
      (sourceRun :
        transcript.Transcript.squeeze_block self = .ok (block, next))
      (tail : NativeExactSqueezeTrace next blocks final)
      (tailPairs : List (ShaInput × ShaOutput))
      (tailExact : NativeSqueezeTraceShaQueryPairs sha256 tail tailPairs) :
      NativeSqueezeTraceShaQueryPairs sha256
        (NativeExactSqueezeTrace.cons self next final block blocks sourceRun
          tail)
        ((nativeHashInputBytes (taggedHashInput self 1#u8),
            sha256 (nativeHashInputBytes (taggedHashInput self 1#u8))) ::
          (nativeHashInputBytes (taggedHashInput self 2#u8),
            sha256 (nativeHashInputBytes (taggedHashInput self 2#u8))) ::
          tailPairs)

/-- Exact chronological query pairs with the literal translated callback
outputs, rather than only their decoded q16 positions.  Retaining both the
output and advance digest is essential: decoder equality does not identify a
unique transcript. -/
inductive NativeSqueezeTraceQueryPairs :
    {initial : Transcript} → {blocks : List SourceSqueezeBlock} →
      {final : Transcript} →
      NativeExactSqueezeTrace initial blocks final →
      List (ShaInput × ShaOutput) → Prop
  | nil (self : Transcript) :
      NativeSqueezeTraceQueryPairs (NativeExactSqueezeTrace.nil self) []
  | cons (self next final : Transcript) (block : SourceSqueezeBlock)
      (blocks : List SourceSqueezeBlock)
      (sourceRun :
        transcript.Transcript.squeeze_block self = .ok (block, next))
      (tail : NativeExactSqueezeTrace next blocks final)
      (tailPairs : List (ShaInput × ShaOutput))
      (tailExact : NativeSqueezeTraceQueryPairs tail tailPairs) :
      NativeSqueezeTraceQueryPairs
        (NativeExactSqueezeTrace.cons self next final block blocks sourceRun
          tail)
        ((nativeHashInputBytes (taggedHashInput self 1#u8),
            nativeSourceDigest (sourceSqueezeBytes block)) ::
          (nativeHashInputBytes (taggedHashInput self 2#u8),
            nativeSourceDigest (sourceSqueezeBytes next.state)) ::
          tailPairs)

/-- Every finite translated source trace has a canonical literal ordered pair
sequence, even though the proof-valued trace cannot be eliminated directly
into data. -/
theorem native_squeeze_trace_has_exact_query_pairs
    {initial final : Transcript} {blocks : List SourceSqueezeBlock}
    (trace : NativeExactSqueezeTrace initial blocks final) :
    ∃ pairs : List (ShaInput × ShaOutput),
      NativeSqueezeTraceQueryPairs trace pairs := by
  induction trace with
  | nil self => exact ⟨[], NativeSqueezeTraceQueryPairs.nil self⟩
  | cons self next final block blocks sourceRun tail ih =>
      obtain ⟨tailPairs, tailExact⟩ := ih
      exact ⟨
        (nativeHashInputBytes (taggedHashInput self 1#u8),
            nativeSourceDigest (sourceSqueezeBytes block)) ::
          (nativeHashInputBytes (taggedHashInput self 2#u8),
            nativeSourceDigest (sourceSqueezeBytes next.state)) ::
          tailPairs,
        NativeSqueezeTraceQueryPairs.cons self next final block blocks
          sourceRun tail tailPairs tailExact⟩

/-- Final-table coverage of the literal source pair sequence constructs the
exact path-specific callback/table coherence predicate. -/
theorem hash_callback_recorded_of_exact_query_pairs
    {table : FixedOracleTable} {initial final : Transcript}
    {blocks : List SourceSqueezeBlock}
    {pairs : List (ShaInput × ShaOutput)}
    {trace : NativeExactSqueezeTrace initial blocks final}
    (ordered : NativeSqueezeTraceQueryPairs trace pairs)
    (covered : QueryPairsCoveredByTable table pairs) :
    HashCallbackRecordedInFixedTable table trace := by
  revert covered
  induction ordered with
  | nil self =>
      intro _
      exact HashCallbackRecordedInFixedTable.nil self
  | cons self next final block blocks sourceRun tail tailPairs tailExact ih =>
      intro covered
      have outputLookup := covered
        (nativeHashInputBytes (taggedHashInput self 1#u8),
          nativeSourceDigest (sourceSqueezeBytes block)) (by simp)
      have advanceLookup := covered
        (nativeHashInputBytes (taggedHashInput self 2#u8),
          nativeSourceDigest (sourceSqueezeBytes next.state)) (by simp)
      have tailCovered : QueryPairsCoveredByTable table tailPairs := by
        intro pair member
        exact covered pair (by simp [member])
      exact HashCallbackRecordedInFixedTable.cons self next final block blocks
        sourceRun tail outputLookup advanceLookup (ih tailCovered)

/-- Existing scheduler pair coverage discharges every lookup in the finite
source trace once the scheduler's chronological pair list is identified with
the literal source squeeze order. -/
theorem sha_trace_inputs_recorded_of_query_pairs
    {table : FixedOracleTable} {sha256 : ByteString → Digest256}
    {initial final : Transcript} {blocks : List SourceSqueezeBlock}
    {pairs : List (ShaInput × ShaOutput)}
    {trace : NativeExactSqueezeTrace initial blocks final}
    (ordered : NativeSqueezeTraceShaQueryPairs sha256 trace pairs)
    (covered : QueryPairsCoveredByTable table pairs) :
    ShaTraceInputsRecordedInFixedTable table sha256 trace := by
  revert covered
  induction ordered with
  | nil self =>
      intro _
      exact ShaTraceInputsRecordedInFixedTable.nil self
  | cons self next final block blocks sourceRun tail tailPairs tailExact ih =>
      intro covered
      have outputLookup := covered
        (nativeHashInputBytes (taggedHashInput self 1#u8),
          sha256 (nativeHashInputBytes (taggedHashInput self 1#u8))) (by simp)
      have advanceLookup := covered
        (nativeHashInputBytes (taggedHashInput self 2#u8),
          sha256 (nativeHashInputBytes (taggedHashInput self 2#u8))) (by simp)
      have tailCovered : QueryPairsCoveredByTable table tailPairs := by
        intro pair member
        exact covered pair (by simp [member])
      exact ShaTraceInputsRecordedInFixedTable.cons self next final block blocks
        sourceRun tail outputLookup advanceLookup (ih tailCovered)

/-- Literal production SHA semantics turns finite scheduler table coverage into
the exact source-output lookup facts used by the deterministic replay. -/
theorem hash_callback_recorded_of_sha_trace_inputs
    {table : FixedOracleTable} {sha256 : ByteString → Digest256}
    {initial final : Transcript} {blocks : List SourceSqueezeBlock}
    (trace : NativeExactSqueezeTrace initial blocks final)
    (shaSemantics : HashCallbackReturnsSha256 sha256 initial.hash)
    (recorded : ShaTraceInputsRecordedInFixedTable table sha256 trace) :
    HashCallbackRecordedInFixedTable table trace := by
  revert shaSemantics
  induction recorded with
  | nil self =>
      intro _
      exact HashCallbackRecordedInFixedTable.nil self
  | cons self next final block blocks sourceRun tail outputLookup
      advanceLookup tailRecorded ih =>
      intro shaSemantics
      have runs := successful_squeeze_exposes_hash_runs self next block sourceRun
      obtain ⟨output, outputRun, outputSha⟩ :=
        shaSemantics (taggedHashInput self 1#u8)
      obtain ⟨nextState, advanceRun, advanceSha⟩ :=
        shaSemantics (taggedHashInput self 2#u8)
      rw [runs.1] at outputRun
      rw [runs.2] at advanceRun
      have outputExact : output = block := by
        exact (Result.ok.inj outputRun).symm
      have advanceExact : nextState = next.state := by
        exact (Result.ok.inj advanceRun).symm
      subst output
      subst nextState
      have callbackExact := successful_squeeze_preserves_hash
        self next block sourceRun
      have tailSha : HashCallbackReturnsSha256 sha256 next.hash := by
        simpa only [callbackExact] using shaSemantics
      refine HashCallbackRecordedInFixedTable.cons self next final block blocks
        sourceRun tail ?_ ?_ (ih tailSha)
      · rw [outputSha]
        exact outputLookup
      · rw [advanceSha]
        exact advanceLookup

/-- A literal translated squeeze trace whose two hashes are present in the
same fixed oracle table used by the Tag-73 scheduler. -/
inductive NativeTableSqueezeTrace (table : FixedOracleTable) :
    Transcript → List SourceSqueezeBlock → Transcript → Prop
  | nil (self : Transcript) : NativeTableSqueezeTrace table self [] self
  | cons (self next final : Transcript) (block : SourceSqueezeBlock)
      (blocks : List SourceSqueezeBlock)
      (sourceRun :
        transcript.Transcript.squeeze_block self = .ok (block, next))
      (outputLookup :
        tableLookup table
            (bytes (nativeTranscriptDigest self) ++ [domSqueeze]) =
          some (nativeSourceDigest (sourceSqueezeBytes block)))
      (advanceLookup :
        tableLookup table
            (bytes (nativeTranscriptDigest self) ++ [domAdvance]) =
          some (nativeTranscriptDigest next))
      (tail : NativeTableSqueezeTrace table next blocks final) :
      NativeTableSqueezeTrace table self (block :: blocks) final

/-- Minimal effectful-runtime reflection for an already proved translated
source trace.  It contains only the two fixed-table lookup facts corresponding
to each literal successful callback pair. -/
inductive SourceSqueezeRuntimeReflection (table : FixedOracleTable) :
    {initial : Transcript} → {blocks : List SourceSqueezeBlock} →
      {final : Transcript} →
      NativeExactSqueezeTrace initial blocks final → Prop
  | nil (self : Transcript) :
      SourceSqueezeRuntimeReflection table (NativeExactSqueezeTrace.nil self)
  | cons (self next final : Transcript) (block : SourceSqueezeBlock)
      (blocks : List SourceSqueezeBlock)
      (sourceRun :
        transcript.Transcript.squeeze_block self = .ok (block, next))
      (tail : NativeExactSqueezeTrace next blocks final)
      (outputLookup :
        tableLookup table
            (bytes (nativeTranscriptDigest self) ++ [domSqueeze]) =
          some (nativeSourceDigest (sourceSqueezeBytes block)))
      (advanceLookup :
        tableLookup table
            (bytes (nativeTranscriptDigest self) ++ [domAdvance]) =
          some (nativeTranscriptDigest next))
      (tailReflected : SourceSqueezeRuntimeReflection table tail) :
      SourceSqueezeRuntimeReflection table
        (NativeExactSqueezeTrace.cons self next final block blocks sourceRun
          tail)

/-- Runtime reflection supplies exactly the lookup fields required to align
the translated source trace with the scheduler's fixed-table duplex. -/
theorem native_table_squeeze_trace_of_runtime_reflection
    {table : FixedOracleTable} {initial final : Transcript}
    {blocks : List SourceSqueezeBlock}
    {trace : NativeExactSqueezeTrace initial blocks final}
    (reflected : SourceSqueezeRuntimeReflection table trace) :
    NativeTableSqueezeTrace table initial blocks final := by
  induction reflected with
  | nil self => exact NativeTableSqueezeTrace.nil self
  | cons self next final block blocks sourceRun tail outputLookup
      advanceLookup tailReflected ih =>
      exact NativeTableSqueezeTrace.cons self next final block blocks sourceRun
        outputLookup advanceLookup ih

/-- One callback/table coherence proof automatically reflects every literal
successful pair in an already extracted source trace.  No per-block lookup
premises remain for callers to manufacture. -/
theorem source_squeeze_runtime_reflection_of_recorded_callback
    {table : FixedOracleTable} {initial final : Transcript}
    {blocks : List SourceSqueezeBlock}
    (trace : NativeExactSqueezeTrace initial blocks final)
    (recorded : HashCallbackRecordedInFixedTable table trace) :
    SourceSqueezeRuntimeReflection table trace := by
  induction recorded with
  | nil self => exact SourceSqueezeRuntimeReflection.nil self
  | cons self next final block blocks sourceRun tail outputLookup
      advanceLookup tailRecorded ih =>
      rw [native_hash_input_bytes_tagged] at outputLookup advanceLookup
      refine SourceSqueezeRuntimeReflection.cons self next final block blocks
        sourceRun tail ?_ ?_ ih
      · simpa [nativeTranscriptDigest, domSqueeze] using outputLookup
      · simpa [nativeTranscriptDigest, domAdvance] using advanceLookup

theorem native_table_squeeze_trace_of_recorded_callback
    {table : FixedOracleTable} {initial final : Transcript}
    {blocks : List SourceSqueezeBlock}
    (trace : NativeExactSqueezeTrace initial blocks final)
    (recorded : HashCallbackRecordedInFixedTable table trace) :
    NativeTableSqueezeTrace table initial blocks final :=
  native_table_squeeze_trace_of_runtime_reflection
    (source_squeeze_runtime_reflection_of_recorded_callback trace recorded)

/-- Forgetting table alignment recovers the exact translated source trace. -/
theorem native_table_squeeze_trace_to_source_trace
    {table : FixedOracleTable} {initial final : Transcript}
    {blocks : List SourceSqueezeBlock}
    (trace : NativeTableSqueezeTrace table initial blocks final) :
    NativeExactSqueezeTrace initial blocks final := by
  induction trace with
  | nil self => exact NativeExactSqueezeTrace.nil self
  | cons self next final block blocks sourceRun _ _ tail ih =>
      exact NativeExactSqueezeTrace.cons self next final block blocks
        sourceRun ih

/-- The translated and semantic q16 squeeze chains are byte exact once their
literal fixed-table lookups are identified. -/
theorem native_table_squeeze_trace_matches_semantic
    {table : FixedOracleTable} {initial final : Transcript}
    {blocks : List SourceSqueezeBlock}
    (trace : NativeTableSqueezeTrace table initial blocks final)
    (machine : MachineState)
    (aligned : machine.digest = nativeTranscriptDigest initial) :
    (squeezeBlocks (fixedTableHashOracle table) blocks.length machine).1 =
        sourceTraceDigests blocks ∧
      (squeezeBlocks (fixedTableHashOracle table) blocks.length machine).2.digest =
        nativeTranscriptDigest final := by
  induction trace generalizing machine with
  | nil self =>
      simp [squeezeBlocks, sourceTraceDigests, aligned]
  | cons self next final block blocks sourceRun outputLookup advanceLookup
      tail ih =>
      let after := (squeezeBlock (fixedTableHashOracle table) machine).2
      have outputExact :
          (squeezeBlock (fixedTableHashOracle table) machine).1 =
            nativeSourceDigest (sourceSqueezeBytes block) := by
        change (fixedTableHashOracle table).answer
            (bytes machine.digest ++ [domSqueeze]) = _
        rw [aligned]
        exact fixed_table_hash_oracle_answer_of_lookup table _ _ outputLookup
      have advanceExact :
          after.digest = nativeTranscriptDigest next := by
        change (fixedTableHashOracle table).answer
            (bytes machine.digest ++ [domAdvance]) = _
        rw [aligned]
        exact fixed_table_hash_oracle_answer_of_lookup table _ _ advanceLookup
      have rest := ih after advanceExact
      constructor
      · simp only [List.length_cons, squeezeBlocks]
        rw [outputExact, rest.1]
        rfl
      · simp only [List.length_cons, squeezeBlocks]
        exact rest.2

/-- Complete deterministic source/scheduler replay from the single callback
coherence predicate. -/
theorem native_source_trace_matches_semantic_of_recorded_callback
    {table : FixedOracleTable} {initial final : Transcript}
    {blocks : List SourceSqueezeBlock}
    (trace : NativeExactSqueezeTrace initial blocks final)
    (recorded : HashCallbackRecordedInFixedTable table trace)
    (machine : MachineState)
    (aligned : machine.digest = nativeTranscriptDigest initial) :
    (squeezeBlocks (fixedTableHashOracle table) blocks.length machine).1 =
        sourceTraceDigests blocks ∧
      (squeezeBlocks (fixedTableHashOracle table)
        blocks.length machine).2.digest = nativeTranscriptDigest final := by
  exact native_table_squeeze_trace_matches_semantic
    (native_table_squeeze_trace_of_recorded_callback trace recorded)
    machine aligned

/-- Release-facing deterministic replay from only the permitted production
SHA-256 callback boundary and finite scheduler-table coverage of the q16 trace.
No global callback/table agreement premise survives. -/
theorem native_source_trace_matches_semantic_of_sha256_coverage
    {table : FixedOracleTable} {sha256 : ByteString → Digest256}
    {initial final : Transcript} {blocks : List SourceSqueezeBlock}
    (trace : NativeExactSqueezeTrace initial blocks final)
    (shaSemantics : HashCallbackReturnsSha256 sha256 initial.hash)
    (recorded : ShaTraceInputsRecordedInFixedTable table sha256 trace)
    (machine : MachineState)
    (aligned : machine.digest = nativeTranscriptDigest initial) :
    (squeezeBlocks (fixedTableHashOracle table) blocks.length machine).1 =
        sourceTraceDigests blocks ∧
      (squeezeBlocks (fixedTableHashOracle table)
        blocks.length machine).2.digest = nativeTranscriptDigest final := by
  exact native_source_trace_matches_semantic_of_recorded_callback trace
    (hash_callback_recorded_of_sha_trace_inputs trace shaSemantics recorded)
    machine aligned

/-- Scheduler-facing release endpoint.  A literal ordered q16 query path and
the scheduler's already proved final-table coverage suffice, together with the
permitted production SHA callback boundary, for byte-exact semantic replay. -/
theorem native_source_trace_matches_semantic_of_query_pair_coverage
    {table : FixedOracleTable} {sha256 : ByteString → Digest256}
    {initial final : Transcript} {blocks : List SourceSqueezeBlock}
    {pairs : List (ShaInput × ShaOutput)}
    (trace : NativeExactSqueezeTrace initial blocks final)
    (ordered : NativeSqueezeTraceShaQueryPairs sha256 trace pairs)
    (covered : QueryPairsCoveredByTable table pairs)
    (shaSemantics : HashCallbackReturnsSha256 sha256 initial.hash)
    (machine : MachineState)
    (aligned : machine.digest = nativeTranscriptDigest initial) :
    (squeezeBlocks (fixedTableHashOracle table) blocks.length machine).1 =
        sourceTraceDigests blocks ∧
      (squeezeBlocks (fixedTableHashOracle table)
        blocks.length machine).2.digest = nativeTranscriptDigest final := by
  exact native_source_trace_matches_semantic_of_sha256_coverage trace
    shaSemantics
    (sha_trace_inputs_recorded_of_query_pairs ordered covered)
    machine aligned

/-- Strongest pair-level endpoint: literal source output/advance pairs covered
by the scheduler table imply byte-exact semantic replay.  No decoded-schedule
equality is used as a substitute for transcript equality. -/
theorem native_source_trace_matches_semantic_of_exact_pair_coverage
    {table : FixedOracleTable} {initial final : Transcript}
    {blocks : List SourceSqueezeBlock}
    {pairs : List (ShaInput × ShaOutput)}
    (trace : NativeExactSqueezeTrace initial blocks final)
    (ordered : NativeSqueezeTraceQueryPairs trace pairs)
    (covered : QueryPairsCoveredByTable table pairs)
    (machine : MachineState)
    (aligned : machine.digest = nativeTranscriptDigest initial) :
    (squeezeBlocks (fixedTableHashOracle table) blocks.length machine).1 =
        sourceTraceDigests blocks ∧
      (squeezeBlocks (fixedTableHashOracle table)
        blocks.length machine).2.digest = nativeTranscriptDigest final := by
  exact native_source_trace_matches_semantic_of_recorded_callback trace
    (hash_callback_recorded_of_exact_query_pairs ordered covered)
    machine aligned

#print axioms fixed_table_hash_oracle_answer_of_lookup
#print axioms native_squeeze_trace_has_exact_query_pairs
#print axioms hash_callback_recorded_of_exact_query_pairs
#print axioms sha_trace_inputs_recorded_of_query_pairs
#print axioms hash_callback_recorded_of_sha_trace_inputs
#print axioms native_table_squeeze_trace_of_runtime_reflection
#print axioms source_squeeze_runtime_reflection_of_recorded_callback
#print axioms native_table_squeeze_trace_of_recorded_callback
#print axioms native_table_squeeze_trace_to_source_trace
#print axioms native_table_squeeze_trace_matches_semantic
#print axioms native_source_trace_matches_semantic_of_recorded_callback
#print axioms native_source_trace_matches_semantic_of_sha256_coverage
#print axioms native_source_trace_matches_semantic_of_query_pair_coverage
#print axioms native_source_trace_matches_semantic_of_exact_pair_coverage

end V7FirstCompactSamplerTableTraceBridge
