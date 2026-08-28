import V7FirstCompactSamplerTableTraceBridge

/-!
# Translated selected-candidate entry state to the Tag-73 scheduler

This module aligns the production candidate clone and one-byte counter absorb
with the semantic scheduler's selected q16 branch.  It is deliberately kept
downstream of the exact source-pair bridge and does not touch K1.5 replay.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace V7FirstCompactCandidateSchedulerEntryBridge

open V7FirstCompactSource
open V7FirstCompactCallerBridge
open V7FirstCompactSamplerNativeBlockBridge
open V7FirstCompactSamplerK13PositionBridge
open V7FirstCompactSamplerOuterLoopBridge
open V7FirstCompactSqueezeSourceBridge
open V7FirstCompactSamplerTableTraceBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ReturnedPlanSemantics
open AspisK1.V7FsAokExperiment

abbrev Transcript := transcript.Transcript

private theorem usizeAddExact (x y z : Std.Usize)
    (hbound : x.val + y.val ≤ Std.Usize.max)
    (hval : z.val = x.val + y.val) :
    x + y = (ok z : Result Std.Usize) := by
  have hspec := Std.Usize.add_spec (x := x) (y := y) hbound
  obtain ⟨value, valueEquation, valueVal⟩ := WP.spec_imp_exists hspec
  have valueIsZ : value = z := by
    apply UScalar.eq_of_val_eq
    omega
  rw [valueEquation, valueIsZ]

private theorem usizeSubExact (x y z : Std.Usize)
    (hbound : y.val ≤ x.val)
    (hval : z.val = x.val - y.val) :
    x - y = (ok z : Result Std.Usize) := by
  have hspec := Std.Usize.sub_spec (x := x) (y := y) hbound
  obtain ⟨value, valueEquation, valueVal⟩ := WP.spec_imp_exists hspec
  have valueIsZ : value = z := by
    apply UScalar.eq_of_val_eq
    omega
  rw [valueEquation, valueIsZ]

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

private theorem candidatePackedPrefixExact
    (state : List Std.U8) (counter : Std.U8)
    (stateLength : state.length = 32) :
    List.slice 0 35
      (((List.replicate 192 0#u8).setSlice! 0 state).set 32 0#u8 |>.set 33 57#u8
        |>.setSlice! 34 [counter]) =
      state ++ [0#u8, 57#u8, counter] := by
  have baseExact :
      (List.replicate 192 0#u8).setSlice! 0 state =
        state ++ List.replicate 160 0#u8 := by
    simp [List.setSlice!, stateLength]
  rw [baseExact]
  apply List.ext_getElem
  · simp [List.setSlice!, stateLength]
  · intro index leftBound rightBound
    have indexBound : index < 35 := by
      simpa [stateLength] using rightBound
    interval_cases index <;>
      simp [List.setSlice!, stateLength]

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

theorem successful_source_candidate_absorb_exposes_hash_run
    (self next : Transcript) (counter : Std.U8)
    (run : transcript.Transcript.absorb self
      transcript.label.V7_QUERY_CANDIDATE (candidateCounterSlice counter) =
        .ok next) :
    self.hash (candidateAbsorbHashInput self counter) = .ok next.state ∧
      next.hash = self.hash := by
  have packedCapacity :
      192#usize - 34#usize = (.ok 158#usize : Result Std.Usize) := by
    apply usizeSubExact <;> scalar_tac
  have dataLength : Slice.len (candidateCounterSlice counter) = 1#usize := by
    apply UScalar.eq_of_val_eq
    rfl
  have oneLeCapacity : (1#usize : Std.Usize) ≤ 158#usize := by
    scalar_tac
  unfold transcript.Transcript.absorb at run
  rw [dataLength, transcript.Transcript.absorb.PACKED_ABSORB_BYTES,
    packedCapacity] at run
  simp only [bind_tc_ok] at run
  simp only [oneLeCapacity, ↓reduceIte] at run
  have counterEnd :
      34#usize + 1#usize = (.ok 35#usize : Result Std.Usize) := by
    apply usizeAddExact <;> scalar_tac
  rw [counterEnd] at run
  simp only [bind_tc_ok] at run
  generalize index0Run :
      core.array.Array.index_mut
        (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8))
        (Array.repeat 192#usize 0#u8) { «end» := 32#usize } =
      index0Result at run
  cases index0Result with
  | fail error => simp [index0Run] at run
  | div => simp [index0Run] at run
  | ok indexed0 =>
      rcases indexed0 with ⟨prefixSlice, back0⟩
      have index0Spec :=
        Array.index_mut_SliceIndexRangeToUsizeSlice
          (Array.repeat 192#usize 0#u8) { «end» := 32#usize }
          (by scalar_tac)
      rw [index0Run] at index0Spec
      simp only [WP.spec_ok] at index0Spec
      rcases index0Spec with ⟨prefixVal, prefixLength, back0Spec⟩
      change (do
        let copied0 ← core.slice.Slice.copy_from_slice core.marker.CopyU8
          prefixSlice (Array.to_slice self.state)
        let input2 ← Array.update (back0 copied0) 32#usize
          transcript.DOM_ABSORB
        let input3 ← Array.update input2 33#usize
          transcript.label.V7_QUERY_CANDIDATE
        let indexed1 ← core.array.Array.index_mut
          (core.ops.index.IndexMutSlice
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) input3
          { start := 34#usize, «end» := 35#usize }
        let copied1 ← core.slice.Slice.copy_from_slice core.marker.CopyU8
          indexed1.1 (candidateCounterSlice counter)
        let finalSlice ← core.array.Array.index
          (core.ops.index.IndexSlice
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8))
          (indexed1.2 copied1) { «end» := 35#usize }
        let nextState ← self.hash (Array.to_slice
          (Array.make 1#usize [finalSlice]))
        .ok { self with state := nextState }) = .ok next at run
      generalize copy0Run :
          core.slice.Slice.copy_from_slice core.marker.CopyU8 prefixSlice
            (Array.to_slice self.state) = copy0Result at run
      cases copy0Result with
      | fail error => simp only [Bind.bind, Aeneas.Std.bind] at run; cases run
      | div => simp only [Bind.bind, Aeneas.Std.bind] at run; cases run
      | ok copied0 =>
          have copy0Spec := core.slice.Slice.copy_from_slice.step_spec
            core.marker.CopyU8 prefixSlice (Array.to_slice self.state) (by
              simpa [Array.to_slice, Slice.length] using prefixLength)
          rw [copy0Run] at copy0Spec
          simp only [WP.spec_ok] at copy0Spec
          simp only [bind_tc_ok] at run
          generalize update32Run :
              Array.update (back0 copied0) 32#usize
                transcript.DOM_ABSORB = update32Result at run
          cases update32Result with
          | fail error => simp only [Bind.bind, Aeneas.Std.bind] at run; cases run
          | div => simp only [Bind.bind, Aeneas.Std.bind] at run; cases run
          | ok input2 =>
              have update32Spec := Array.update_spec (back0 copied0)
                32#usize transcript.DOM_ABSORB (by scalar_tac)
              rw [update32Run] at update32Spec
              simp only [WP.spec_ok] at update32Spec
              simp only [bind_tc_ok] at run
              generalize update33Run :
                  Array.update input2 33#usize
                    transcript.label.V7_QUERY_CANDIDATE = update33Result at run
              cases update33Result with
              | fail error => simp only [Bind.bind, Aeneas.Std.bind] at run; cases run
              | div => simp only [Bind.bind, Aeneas.Std.bind] at run; cases run
              | ok input3 =>
                  have update33Spec := Array.update_spec input2 33#usize
                    transcript.label.V7_QUERY_CANDIDATE (by scalar_tac)
                  rw [update33Run] at update33Spec
                  simp only [WP.spec_ok] at update33Spec
                  simp only [bind_tc_ok] at run
                  generalize index1Run :
                      core.array.Array.index_mut
                        (core.ops.index.IndexMutSlice
                          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8))
                        input3 { start := 34#usize, «end» := 35#usize } =
                      index1Result at run
                  cases index1Result with
                  | fail error => simp only [Bind.bind, Aeneas.Std.bind] at run; cases run
                  | div => simp only [Bind.bind, Aeneas.Std.bind] at run; cases run
                  | ok indexed1 =>
                      rcases indexed1 with ⟨counterTarget, back1⟩
                      have index1Spec :=
                        Array.index_mut_SliceIndexRangeUsizeSlice.step input3
                          { start := 34#usize, «end» := 35#usize }
                          (by scalar_tac) (by scalar_tac)
                      rw [index1Run] at index1Spec
                      simp only [WP.spec_ok] at index1Spec
                      rcases index1Spec with
                        ⟨counterTargetVal, counterTargetLength, back1Spec⟩
                      simp only [bind_tc_ok] at run
                      change (do
                        let copied1 ← core.slice.Slice.copy_from_slice
                          core.marker.CopyU8 counterTarget
                            (candidateCounterSlice counter)
                        let finalSlice ← core.array.Array.index
                          (core.ops.index.IndexSlice
                            (core.slice.index.SliceIndexRangeToUsizeSlice
                              Std.U8))
                          (back1 copied1) { «end» := 35#usize }
                        let nextState ← self.hash (Array.to_slice
                          (Array.make 1#usize [finalSlice]))
                        .ok { self with state := nextState }) = .ok next at run
                      generalize copy1Run :
                          core.slice.Slice.copy_from_slice core.marker.CopyU8
                            counterTarget (candidateCounterSlice counter) =
                          copy1Result at run
                      cases copy1Result with
                      | fail error => simp only [Bind.bind, Aeneas.Std.bind] at run; cases run
                      | div => simp only [Bind.bind, Aeneas.Std.bind] at run; cases run
                      | ok copied1 =>
                          have copy1Spec :=
                            core.slice.Slice.copy_from_slice.step_spec
                              core.marker.CopyU8 counterTarget
                                (candidateCounterSlice counter) (by
                                  simpa [candidateCounterSlice, Slice.length]
                                    using counterTargetLength)
                          rw [copy1Run] at copy1Spec
                          simp only [WP.spec_ok] at copy1Spec
                          simp only [bind_tc_ok] at run
                          generalize finalIndexRun :
                              core.array.Array.index
                                (core.ops.index.IndexSlice
                                  (core.slice.index.SliceIndexRangeToUsizeSlice
                                    Std.U8))
                                (back1 copied1) { «end» := 35#usize } =
                              finalIndexResult at run
                          cases finalIndexResult with
                          | fail error => simp only [Bind.bind, Aeneas.Std.bind] at run; cases run
                          | div => simp only [Bind.bind, Aeneas.Std.bind] at run; cases run
                          | ok finalSlice =>
                              rw [Array.index_SliceIndexRangeToUsizeSlice] at finalIndexRun
                              have finalIndexSpec :=
                                core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec
                                  { «end» := 35#usize }
                                  (Array.to_slice (back1 copied1))
                                  (by scalar_tac)
                              rw [finalIndexRun] at finalIndexSpec
                              simp only [WP.spec_ok] at finalIndexSpec
                              rcases finalIndexSpec with
                                ⟨finalSliceVal, finalSliceLength⟩
                              simp only [bind_tc_ok, lift,
                                Array.to_slice, Array.make] at run
                              generalize hashRun : self.hash ⟨[finalSlice], by
                                scalar_tac⟩ = hashResult at run
                              cases hashResult with
                              | fail error => simp only [Bind.bind, Aeneas.Std.bind] at run; cases run
                              | div => simp only [Bind.bind, Aeneas.Std.bind] at run; cases run
                              | ok nextState =>
                                  simp only [bind_tc_ok, Result.ok.injEq] at run
                                  subst next
                                  have finalSliceExact :
                                      finalSlice =
                                        ⟨(candidateAbsorbBytes self counter).val,
                                          by scalar_tac⟩ := by
                                    apply Subtype.ext
                                    change finalSlice.val =
                                      (candidateAbsorbBytes self counter).val
                                    change finalSlice.val =
                                      List.slice 0 35 (back1 copied1).val at finalSliceVal
                                    rw [finalSliceVal, back1Spec copied1,
                                      copy1Spec, update33Spec, update32Spec,
                                      Array.set_val_eq, Array.set_val_eq,
                                      back0Spec copied0, copy0Spec,
                                      Array.to_slice, Array.repeat_val,
                                      candidateCounterSlice,
                                      candidateAbsorbBytes,
                                      transcript.DOM_ABSORB,
                                      transcript.label.V7_QUERY_CANDIDATE]
                                    exact candidatePackedPrefixExact self.state.val
                                      counter self.state.property
                                  rw [finalSliceExact] at hashRun
                                  exact ⟨by
                                    simpa [candidateAbsorbHashInput] using hashRun,
                                    rfl⟩

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

/-- A literal successful production candidate execution exposes the exact
35-byte absorb callback pair used by the semantic q16 scheduler. -/
theorem raw_candidate_absorb_exposes_exact_hash_run
    (inputTranscript : Transcript) (counter : Std.U8)
    (output : Option v7_onefold.V7CompactQuerySchedule)
    (raw : RawCandidateExecution inputTranscript counter output) :
    inputTranscript.hash
        (candidateAbsorbHashInput inputTranscript counter) =
      .ok raw.absorbed.state ∧
    raw.absorbed.hash = inputTranscript.hash := by
  have absorbRun := raw.absorbRun
  rw [raw_candidate_clone_exact inputTranscript counter output raw,
    raw_candidate_counter_slice_exact inputTranscript counter output raw] at absorbRun
  exact successful_source_candidate_absorb_exposes_hash_run
    inputTranscript raw.absorbed counter absorbRun

/-- The literal candidate absorb input is the scheduler's candidate-input
grammar once the pre-candidate source digest is aligned with the scheduler
state. -/
theorem candidate_absorb_input_matches_source
    (inputTranscript : Transcript) (sourceCounter : Std.U8)
    (machine : MachineState) (counter : Fin 64)
    (counterExact : sourceCounter.val = counter.val)
    (aligned : machine.digest = nativeTranscriptDigest inputTranscript) :
    candidateAbsorbInput machine counter =
      nativeHashInputBytes
        (candidateAbsorbHashInput inputTranscript sourceCounter) := by
  rw [native_candidate_absorb_hash_input_bytes]
  simp [candidateAbsorbInput, aligned, nativeTranscriptDigest, counterExact]

/-- The candidate callback from a literal successful source run and the
scheduler's fixed-table absorb are the same one-query transition.  The table
coverage is path-specific: it names this exact source input and output only. -/
theorem raw_candidate_absorb_matches_semantic_table
    {table : FixedOracleTable}
    (inputTranscript : Transcript) (sourceCounter : Std.U8)
    (output : Option v7_onefold.V7CompactQuerySchedule)
    (raw : RawCandidateExecution inputTranscript sourceCounter output)
    (machine : MachineState) (counter : Fin 64)
    (counterExact : sourceCounter.val = counter.val)
    (aligned : machine.digest = nativeTranscriptDigest inputTranscript)
    (covered : tableLookup table
      (nativeHashInputBytes
        (candidateAbsorbHashInput inputTranscript sourceCounter)) =
        some (nativeTranscriptDigest raw.absorbed)) :
    inputTranscript.hash
        (candidateAbsorbHashInput inputTranscript sourceCounter) =
      .ok raw.absorbed.state ∧
    (absorb (fixedTableHashOracle table) machine
      (.queryCandidate counter)).digest =
      nativeTranscriptDigest raw.absorbed := by
  constructor
  · exact (raw_candidate_absorb_exposes_exact_hash_run
      inputTranscript sourceCounter output raw).1
  · change (fixedTableHashOracle table).answer
        (candidateAbsorbInput machine counter) =
      nativeTranscriptDigest raw.absorbed
    rw [candidate_absorb_input_matches_source inputTranscript sourceCounter
      machine counter counterExact aligned]
    exact fixed_table_hash_oracle_answer_of_lookup table _ _ covered

/-- Complete selected-candidate entry replay: the translated candidate absorb
and its subsequent literal source squeeze pairs replay under the same semantic
fixed table.  This is the q16 source/scheduler seam used before decoder and
frontier reasoning. -/
theorem raw_candidate_entry_and_trace_match_semantic
    {table : FixedOracleTable}
    (inputTranscript : Transcript) (sourceCounter : Std.U8)
    (output : Option v7_onefold.V7CompactQuerySchedule)
    (raw : RawCandidateExecution inputTranscript sourceCounter output)
    (machine : MachineState) (counter : Fin 64)
    (counterExact : sourceCounter.val = counter.val)
    (baseAligned : machine.digest = nativeTranscriptDigest inputTranscript)
    {blocks : List SourceSqueezeBlock} {pairs : List (ShaInput × ShaOutput)}
    (trace : NativeExactSqueezeTrace raw.absorbed blocks raw.sampledTranscript)
    (ordered : NativeSqueezeTraceQueryPairs trace pairs)
    (candidateCovered : tableLookup table
      (nativeHashInputBytes
        (candidateAbsorbHashInput inputTranscript sourceCounter)) =
        some (nativeTranscriptDigest raw.absorbed))
    (squeezeCovered : QueryPairsCoveredByTable table pairs) :
    inputTranscript.hash
        (candidateAbsorbHashInput inputTranscript sourceCounter) =
      .ok raw.absorbed.state ∧
    (squeezeBlocks (fixedTableHashOracle table) blocks.length
      (absorb (fixedTableHashOracle table) machine
        (.queryCandidate counter))).1 = sourceTraceDigests blocks ∧
    (squeezeBlocks (fixedTableHashOracle table) blocks.length
      (absorb (fixedTableHashOracle table) machine
        (.queryCandidate counter))).2.digest =
      nativeTranscriptDigest raw.sampledTranscript := by
  have entry := raw_candidate_absorb_matches_semantic_table (table := table)
    inputTranscript sourceCounter output raw machine counter counterExact
    baseAligned candidateCovered
  have replay := native_source_trace_matches_semantic_of_exact_pair_coverage
    trace ordered squeezeCovered
    (absorb (fixedTableHashOracle table) machine
      (.queryCandidate counter)) entry.2
  exact ⟨entry.1, replay.1, replay.2⟩

#print axioms native_candidate_absorb_hash_input_bytes
#print axioms source_candidate_clone_run_is_exact
#print axioms successful_source_candidate_absorb_exposes_hash_run
#print axioms raw_candidate_clone_exact
#print axioms raw_candidate_clone_is_exact
#print axioms raw_candidate_counter_data_exact
#print axioms raw_candidate_counter_slice_exact
#print axioms raw_candidate_absorb_exposes_exact_hash_run
#print axioms candidate_absorb_input_matches_source
#print axioms raw_candidate_absorb_matches_semantic_table
#print axioms raw_candidate_entry_and_trace_match_semantic

end V7FirstCompactCandidateSchedulerEntryBridge
