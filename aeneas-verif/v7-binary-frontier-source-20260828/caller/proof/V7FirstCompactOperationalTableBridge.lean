import V7FirstCompactCandidateSchedulerEntryBridge
import V7FixedTableOracleStateBridge

/-!
# q16 source candidate replay from the operational ROM table

This is the composition point between a literal translated q16 candidate and
the actual compiler oracle state.  It deliberately asks only for finite
membership of the candidate absorb and its source-trace pairs in that state;
freshness and role ownership are not assumed or inferred.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace V7FirstCompactOperationalTableBridge

open V7FirstCompactSource
open V7FirstCompactCandidateSchedulerEntryBridge
open V7FirstCompactCallerBridge
open V7FirstCompactSqueezeSourceBridge
open V7FirstCompactSamplerNativeBlockBridge
open V7FirstCompactSamplerOuterLoopBridge
open V7FirstCompactSamplerK13PositionBridge
open V7FirstCompactSamplerTableTraceBridge
open V7FixedTableOracleStateBridge
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73CoupledReplayAlignment
open AspisK1.V7Tag73DeterministicRefinement

noncomputable section

/-- The selected translated candidate and all literal sampler callbacks replay
under the fixed-table erasure of the actual ROM state whenever those exact
pairs are present in that state.  Cache hits are included: table membership,
not fresh exposure, is the required invariant here. -/
theorem raw_candidate_entry_and_trace_match_operational_table
    (state : OracleState)
    (inputTranscript : transcript.Transcript) (sourceCounter : Std.U8)
    (output : Option v7_onefold.V7CompactQuerySchedule)
    (raw : RawCandidateExecution inputTranscript sourceCounter output)
    (machine : MachineState) (counter : Fin 64)
    (counterExact : sourceCounter.val = counter.val)
    (baseAligned : machine.digest = nativeTranscriptDigest inputTranscript)
    {blocks : List SourceSqueezeBlock} {pairs : List (ShaInput × ShaOutput)}
    (trace : NativeExactSqueezeTrace raw.absorbed blocks raw.sampledTranscript)
    (ordered : NativeSqueezeTraceQueryPairs trace pairs)
    (candidateEntry : AspisK1.V7FsAokExperiment.TableEntry)
    (candidateFound : lookupEntry state
      (nativeHashInputBytes
        (candidateAbsorbHashInput inputTranscript sourceCounter)) =
      some candidateEntry)
    (candidateOutput : candidateEntry.output = nativeTranscriptDigest raw.absorbed)
    (squeezeCovered : ∀ pair ∈ pairs,
      ∃ entry : AspisK1.V7FsAokExperiment.TableEntry,
        lookupEntry state pair.1 = some entry ∧ entry.output = pair.2) :
    inputTranscript.hash
        (candidateAbsorbHashInput inputTranscript sourceCounter) =
      .ok raw.absorbed.state ∧
    (squeezeBlocks (fixedTableHashOracle (fixedTableOfOracleState state))
      blocks.length
      (absorb (fixedTableHashOracle (fixedTableOfOracleState state)) machine
        (.queryCandidate counter))).1 = sourceTraceDigests blocks ∧
    (squeezeBlocks (fixedTableHashOracle (fixedTableOfOracleState state))
      blocks.length
      (absorb (fixedTableHashOracle (fixedTableOfOracleState state)) machine
        (.queryCandidate counter))).2.digest =
      nativeTranscriptDigest raw.sampledTranscript := by
  have candidateCovered : tableLookup (fixedTableOfOracleState state)
      (nativeHashInputBytes
        (candidateAbsorbHashInput inputTranscript sourceCounter)) =
      some (nativeTranscriptDigest raw.absorbed) := by
    rw [← candidateOutput]
    exact fixed_table_of_oracle_state_lookup_of_lookupEntry state _
      candidateEntry candidateFound
  have traceCovered := operational_pair_coverage_implies_fixed_table_coverage
    state pairs squeezeCovered
  exact raw_candidate_entry_and_trace_match_semantic
    inputTranscript sourceCounter output raw machine counter counterExact
    baseAligned trace ordered candidateCovered traceCovered

#print axioms raw_candidate_entry_and_trace_match_operational_table

end

end V7FirstCompactOperationalTableBridge
