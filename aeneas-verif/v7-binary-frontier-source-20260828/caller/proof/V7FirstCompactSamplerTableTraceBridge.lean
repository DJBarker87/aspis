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

#print axioms fixed_table_hash_oracle_answer_of_lookup
#print axioms native_table_squeeze_trace_to_source_trace
#print axioms native_table_squeeze_trace_matches_semantic

end V7FirstCompactSamplerTableTraceBridge
