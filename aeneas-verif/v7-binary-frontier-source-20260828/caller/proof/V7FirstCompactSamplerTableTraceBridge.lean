import V7FirstCompactSamplerK13PositionBridge
import AspisFormal.K1.V7Tag73DeterministicRefinement

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

/-- Exact operational scheduler/source coherence: every successful callback
run is present at the same concatenated input and output in the fixed ROM
table.  This is a runtime alignment property, not a cryptographic premise. -/
def HashCallbackRecordedInFixedTable
    (table : FixedOracleTable)
    (hash : Slice (Slice Std.U8) → Result SourceSqueezeBlock) : Prop :=
  ∀ input output, hash input = .ok output →
    tableLookup table (nativeHashInputBytes input) =
      some (nativeSourceDigest (sourceSqueezeBytes output))

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
    (recorded : HashCallbackRecordedInFixedTable table initial.hash) :
    SourceSqueezeRuntimeReflection table trace := by
  induction trace with
  | nil self => exact SourceSqueezeRuntimeReflection.nil self
  | cons self next final block blocks sourceRun tail ih =>
      have runs := successful_squeeze_exposes_hash_runs self next block sourceRun
      have outputLookup := recorded _ _ runs.1
      have advanceLookup := recorded _ _ runs.2
      rw [native_hash_input_bytes_tagged] at outputLookup advanceLookup
      have callbackExact := successful_squeeze_preserves_hash
        self next block sourceRun
      have tailRecorded :
          HashCallbackRecordedInFixedTable table next.hash := by
        simpa [callbackExact] using recorded
      refine SourceSqueezeRuntimeReflection.cons self next final block blocks
        sourceRun tail ?_ ?_ (ih tailRecorded)
      · simpa [nativeTranscriptDigest, domSqueeze] using outputLookup
      · simpa [nativeTranscriptDigest, domAdvance] using advanceLookup

theorem native_table_squeeze_trace_of_recorded_callback
    {table : FixedOracleTable} {initial final : Transcript}
    {blocks : List SourceSqueezeBlock}
    (trace : NativeExactSqueezeTrace initial blocks final)
    (recorded : HashCallbackRecordedInFixedTable table initial.hash) :
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
    (recorded : HashCallbackRecordedInFixedTable table initial.hash)
    (machine : MachineState)
    (aligned : machine.digest = nativeTranscriptDigest initial) :
    (squeezeBlocks (fixedTableHashOracle table) blocks.length machine).1 =
        sourceTraceDigests blocks ∧
      (squeezeBlocks (fixedTableHashOracle table)
        blocks.length machine).2.digest = nativeTranscriptDigest final := by
  exact native_table_squeeze_trace_matches_semantic
    (native_table_squeeze_trace_of_recorded_callback trace recorded)
    machine aligned

#print axioms fixed_table_hash_oracle_answer_of_lookup
#print axioms native_table_squeeze_trace_of_runtime_reflection
#print axioms source_squeeze_runtime_reflection_of_recorded_callback
#print axioms native_table_squeeze_trace_of_recorded_callback
#print axioms native_table_squeeze_trace_to_source_trace
#print axioms native_table_squeeze_trace_matches_semantic
#print axioms native_source_trace_matches_semantic_of_recorded_callback

end V7FirstCompactSamplerTableTraceBridge
