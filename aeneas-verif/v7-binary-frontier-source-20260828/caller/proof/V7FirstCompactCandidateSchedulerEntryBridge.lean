import V7FirstCompactSamplerTableTraceBridge

/-!
# Translated selected-candidate entry state to the Tag-73 scheduler

This module aligns the production candidate clone and one-byte counter absorb
with the semantic scheduler's selected q16 branch.  It is deliberately kept
downstream of the exact source-pair bridge and does not touch K1.5 replay.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace V7FirstCompactCandidateSchedulerEntryBridge

open V7FirstCompactSource
open V7FirstCompactCallerBridge
open V7FirstCompactSamplerNativeBlockBridge
open V7FirstCompactSqueezeSourceBridge
open V7FirstCompactSamplerTableTraceBridge
open AspisK1.V7Tag73TranscriptSchedule

abbrev Transcript := transcript.Transcript

/-- Literal 35-byte packed input used by the production short candidate
absorb: prior digest, absorb domain, candidate label, counter. -/
def candidateAbsorbBytes (self : Transcript) (counter : Std.U8) :
    Array Std.U8 35#usize :=
  ⟨self.state.val ++ [0#u8, 57#u8, counter], by
    simp [self.state.property]⟩

def candidateAbsorbHashInput (self : Transcript) (counter : Std.U8) :
    Slice (Slice Std.U8) :=
  ⟨[⟨(candidateAbsorbBytes self counter).val, by scalar_tac⟩], by
    scalar_tac⟩

def candidateCounterSlice (counter : Std.U8) : Slice Std.U8 :=
  ⟨[counter], by scalar_tac⟩

def exactCandidateAbsorbRun (self : Transcript) (counter : Std.U8) :
    Result Transcript := do
  let nextState ← self.hash (candidateAbsorbHashInput self counter)
  .ok { self with state := nextState }

theorem native_candidate_absorb_hash_input_bytes
    (self : Transcript) (counter : Std.U8) :
    nativeHashInputBytes (candidateAbsorbHashInput self counter) =
      bytes (nativeSourceDigest (sourceSqueezeBytes self.state)) ++
        [domAbsorb, queryCandidateLabel, UInt8.ofNat counter.val] := by
  rw [bytes_native_source_digest]
  simp [nativeHashInputBytes, candidateAbsorbHashInput, candidateAbsorbBytes,
    sourceSqueezeBytes, domAbsorb, queryCandidateLabel]

theorem source_candidate_clone_run_is_exact (self : Transcript) :
    transcript.Transcript.Insts.CoreCloneClone.clone self = .ok self := by
  unfold transcript.Transcript.Insts.CoreCloneClone.clone
  have stateSpec := core.array.CloneArray.clone_spec core.clone.CloneU8
    self.state (by
      intro value member
      rfl)
  obtain ⟨state, stateRun, stateExact⟩ :=
    Aeneas.Std.WP.spec_imp_exists stateSpec
  rw [stateRun]
  simp only [bind_tc_ok]
  subst state
  rfl

theorem raw_candidate_clone_exact
    (inputTranscript : Transcript) (counter : Std.U8)
    (output : Option v7_onefold.V7CompactQuerySchedule)
    (raw : RawCandidateExecution inputTranscript counter output) :
    raw.cloned = inputTranscript := by
  have cloneRun := raw.cloneRun
  rw [source_candidate_clone_run_is_exact] at cloneRun
  exact Result.ok.inj cloneRun.symm

theorem raw_candidate_clone_is_exact
    (inputTranscript : Transcript) (counter : Std.U8)
    (output : Option v7_onefold.V7CompactQuerySchedule)
    (raw : RawCandidateExecution inputTranscript counter output) :
    raw.cloned.state = inputTranscript.state ∧
      raw.cloned.hash = inputTranscript.hash := by
  have exactClone := raw_candidate_clone_exact inputTranscript counter output raw
  exact ⟨congrArg (fun value : Transcript => value.state) exactClone,
    congrArg (fun value : Transcript => value.hash) exactClone⟩

theorem raw_candidate_counter_data_exact
    (inputTranscript : Transcript) (counter : Std.U8)
    (output : Option v7_onefold.V7CompactQuerySchedule)
    (raw : RawCandidateExecution inputTranscript counter output) :
    raw.counterData.val = [counter] := by
  have run := raw.sliceRun
  simp [lift, Array.to_slice, Array.make] at run
  exact congrArg (fun value : Slice Std.U8 => value.val) run.symm

theorem raw_candidate_counter_slice_exact
    (inputTranscript : Transcript) (counter : Std.U8)
    (output : Option v7_onefold.V7CompactQuerySchedule)
    (raw : RawCandidateExecution inputTranscript counter output) :
    raw.counterData = candidateCounterSlice counter := by
  apply Subtype.ext
  exact raw_candidate_counter_data_exact inputTranscript counter output raw

#print axioms native_candidate_absorb_hash_input_bytes
#print axioms source_candidate_clone_run_is_exact
#print axioms raw_candidate_clone_exact
#print axioms raw_candidate_clone_is_exact
#print axioms raw_candidate_counter_data_exact
#print axioms raw_candidate_counter_slice_exact

end V7FirstCompactCandidateSchedulerEntryBridge
