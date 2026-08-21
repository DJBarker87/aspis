import V5MerkleUnchangedGeneratedSectionBridge

/-!
# Exact composition of the unchanged five-section V5 Merkle driver

This file composes the exact generated outer-loop trace with the exact
per-section helper theorem.  It constructs the maintained `ExactV5Run`
directly; neither of the former proposition-valued Rust source-equality
boundaries is used.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5MerkleUnchangedFiveSectionComposition

open V5MerkleUnchangedFull
open V5MerkleUnchangedDriverProof
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5MerkleConsumedValueBridge
open AspisV5TopologyConstruction
open AspisV5MerkleUnchangedFullHelperBridge
open AspisV5MerkleUnchangedFullConstructorSemantics
open AspisV5MerkleUnchangedFullSectionTopologyAlignment
open AspisV5MerkleUnchangedFullSectionCallBridge
open AspisV5MerkleUnchangedGeneratedSectionBridge

abbrev GeneratedDigest := Array Std.U8 32#usize
abbrev GeneratedHash := Slice (Slice Std.U8) → GeneratedDigest
abbrev GeneratedOpening :=
  aspis_core.state_only_private_openings.StateOnlyPrivateOpening
abbrev GeneratedDigestVec := alloc.vec.Vec GeneratedDigest
abbrev ModelByte := AspisV5MerkleAuthenticationBinding.Byte

/-- The maintained five-root view determined by the exact five generated
section calls.  Each call's `root_eq` field separately proves that this is the
corresponding entry of the generated driver's root array. -/
def rootsOfFiveCallTrace
    {hash : GeneratedHash}
    {s0 s1 s2 s3 s4 : Slice Std.U32}
    {roots : Array GeneratedDigest 5#usize}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {level0 next0 : GeneratedDigestVec}
    {proofBytes : Slice Std.U8}
    {parsed0 : Array (Option GeneratedOpening) 5#usize}
    {finalRemainder : Slice Std.U8}
    {finalParsed : Array (Option GeneratedOpening) 5#usize}
    (trace : GeneratedFiveCallTrace hash s0 s1 s2 s3 s4 roots topology
      level0 next0 proofBytes parsed0 finalRemainder finalParsed) :
    V5PrivateRoots Digest32 where
  c1 := generatedArrayToDigest trace.call0.root
  c2 := generatedArrayToDigest trace.call1.root
  line1 := generatedArrayToDigest trace.call2.root
  line2 := generatedArrayToDigest trace.call3.root
  line3 := generatedArrayToDigest trace.call4.root

@[simp] theorem rootsOfFiveCallTrace_get_c1
    {hash : GeneratedHash} {s0 s1 s2 s3 s4 : Slice Std.U32}
    {roots : Array GeneratedDigest 5#usize}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {level0 next0 : GeneratedDigestVec} {proofBytes : Slice Std.U8}
    {parsed0 : Array (Option GeneratedOpening) 5#usize}
    {finalRemainder : Slice Std.U8}
    {finalParsed : Array (Option GeneratedOpening) 5#usize}
    (trace : GeneratedFiveCallTrace hash s0 s1 s2 s3 s4 roots topology
      level0 next0 proofBytes parsed0 finalRemainder finalParsed) :
    (rootsOfFiveCallTrace trace).get .c1 =
      generatedArrayToDigest trace.call0.root := rfl

@[simp] theorem rootsOfFiveCallTrace_get_c2
    {hash : GeneratedHash} {s0 s1 s2 s3 s4 : Slice Std.U32}
    {roots : Array GeneratedDigest 5#usize}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {level0 next0 : GeneratedDigestVec} {proofBytes : Slice Std.U8}
    {parsed0 : Array (Option GeneratedOpening) 5#usize}
    {finalRemainder : Slice Std.U8}
    {finalParsed : Array (Option GeneratedOpening) 5#usize}
    (trace : GeneratedFiveCallTrace hash s0 s1 s2 s3 s4 roots topology
      level0 next0 proofBytes parsed0 finalRemainder finalParsed) :
    (rootsOfFiveCallTrace trace).get .c2 =
      generatedArrayToDigest trace.call1.root := rfl

@[simp] theorem rootsOfFiveCallTrace_get_line1
    {hash : GeneratedHash} {s0 s1 s2 s3 s4 : Slice Std.U32}
    {roots : Array GeneratedDigest 5#usize}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {level0 next0 : GeneratedDigestVec} {proofBytes : Slice Std.U8}
    {parsed0 : Array (Option GeneratedOpening) 5#usize}
    {finalRemainder : Slice Std.U8}
    {finalParsed : Array (Option GeneratedOpening) 5#usize}
    (trace : GeneratedFiveCallTrace hash s0 s1 s2 s3 s4 roots topology
      level0 next0 proofBytes parsed0 finalRemainder finalParsed) :
    (rootsOfFiveCallTrace trace).get .line1 =
      generatedArrayToDigest trace.call2.root := rfl

@[simp] theorem rootsOfFiveCallTrace_get_line2
    {hash : GeneratedHash} {s0 s1 s2 s3 s4 : Slice Std.U32}
    {roots : Array GeneratedDigest 5#usize}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {level0 next0 : GeneratedDigestVec} {proofBytes : Slice Std.U8}
    {parsed0 : Array (Option GeneratedOpening) 5#usize}
    {finalRemainder : Slice Std.U8}
    {finalParsed : Array (Option GeneratedOpening) 5#usize}
    (trace : GeneratedFiveCallTrace hash s0 s1 s2 s3 s4 roots topology
      level0 next0 proofBytes parsed0 finalRemainder finalParsed) :
    (rootsOfFiveCallTrace trace).get .line2 =
      generatedArrayToDigest trace.call3.root := rfl

@[simp] theorem rootsOfFiveCallTrace_get_line3
    {hash : GeneratedHash} {s0 s1 s2 s3 s4 : Slice Std.U32}
    {roots : Array GeneratedDigest 5#usize}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {level0 next0 : GeneratedDigestVec} {proofBytes : Slice Std.U8}
    {parsed0 : Array (Option GeneratedOpening) 5#usize}
    {finalRemainder : Slice Std.U8}
    {finalParsed : Array (Option GeneratedOpening) 5#usize}
    (trace : GeneratedFiveCallTrace hash s0 s1 s2 s3 s4 roots topology
      level0 next0 proofBytes parsed0 finalRemainder finalParsed) :
    (rootsOfFiveCallTrace trace).get .line3 =
      generatedArrayToDigest trace.call4.root := rfl

/-- The exact five generated helper successes form one maintained
`ExactV5Run`.  The only executable semantic premise is `hhash`; the remaining
hypotheses are the explicit model view of the public query slices and the
already-proved constructor fields for their shared topology. -/
theorem generated_five_call_trace_yields_exact_run
    (sha256 : List ModelByte → Digest32)
    (queries : Finset V5Query) (queryCount : queries.card = 18)
    {hash : GeneratedHash}
    {s0 s1 s2 s3 s4 : Slice Std.U32}
    {roots : Array GeneratedDigest 5#usize}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {level0 next0 : GeneratedDigestVec}
    {proofBytes : Slice Std.U8}
    {parsed0 : Array (Option GeneratedOpening) 5#usize}
    {finalRemainder : Slice Std.U8}
    {finalParsed : Array (Option GeneratedOpening) 5#usize}
    (trace : GeneratedFiveCallTrace hash s0 s1 s2 s3 s4 roots topology
      level0 next0 proofBytes parsed0 finalRemainder finalParsed)
    (hhash : HashCallbackEqualsSha256 sha256 hash)
    (s0Model : s0.val.map (fun index => index.val) =
      orderedActiveIndices .c1 queries 0)
    (s1Model : s1.val.map (fun index => index.val) =
      orderedActiveIndices .c2 queries 0)
    (s2Model : s2.val.map (fun index => index.val) =
      orderedActiveIndices .line1 queries 0)
    (s3Model : s3.val.map (fun index => index.val) =
      orderedActiveIndices .line2 queries 0)
    (s4Model : s4.val.map (fun index => index.val) =
      orderedActiveIndices .line3 queries 0)
    (fields : FullExactConstructedTopologyFields queries topology)
    (hempty : finalRemainder.val = []) :
    ∃ run : ExactV5Run sha256 (rootsOfFiveCallTrace trace) queries,
      run.proofBytes = proofBytes.val.map generatedU8ToByte := by
  have p0 := generated_section_call_parameters .c1 queries trace.call0 rfl rfl
    s0Model
  have p1 := generated_section_call_parameters .c2 queries trace.call1 rfl rfl
    s1Model
  have p2 := generated_section_call_parameters .line1 queries trace.call2 rfl
    rfl s2Model
  have p3 := generated_section_call_parameters .line2 queries trace.call3 rfl
    rfl s3Model
  have p4 := generated_section_call_parameters .line3 queries trace.call4 rfl
    rfl s4Model
  obtain ⟨c1, hc1⟩ := generated_section_call_yields_exact_acceptance
    sha256 .c1 queries queryCount trace.call0 hhash p0 fields
  obtain ⟨c2, hc2⟩ := generated_section_call_yields_exact_acceptance
    sha256 .c2 queries queryCount trace.call1 hhash p1 fields
  obtain ⟨line1, hline1⟩ := generated_section_call_yields_exact_acceptance
    sha256 .line1 queries queryCount trace.call2 hhash p2 fields
  obtain ⟨line2, hline2⟩ := generated_section_call_yields_exact_acceptance
    sha256 .line2 queries queryCount trace.call3 hhash p3 fields
  obtain ⟨line3, hline3⟩ := generated_section_call_yields_exact_acceptance
    sha256 .line3 queries queryCount trace.call4 hhash p4 fields
  change proofBytes.val.map generatedU8ToByte =
    c1.wire ++ trace.remainder1.val.map generatedU8ToByte at hc1
  change trace.remainder1.val.map generatedU8ToByte =
    c2.wire ++ trace.remainder2.val.map generatedU8ToByte at hc2
  change trace.remainder2.val.map generatedU8ToByte =
    line1.wire ++ trace.remainder3.val.map generatedU8ToByte at hline1
  change trace.remainder3.val.map generatedU8ToByte =
    line2.wire ++ trace.remainder4.val.map generatedU8ToByte at hline2
  change trace.remainder4.val.map generatedU8ToByte =
    line3.wire ++ finalRemainder.val.map generatedU8ToByte at hline3
  let sections : ∀ tree,
      ExactSectionTrace sha256 tree ((rootsOfFiveCallTrace trace).get tree)
        queries := fun tree => match tree with
    | .c1 => c1
    | .c2 => c2
    | .line1 => line1
    | .line2 => line2
    | .line3 => line3
  let run : ExactV5Run sha256 (rootsOfFiveCallTrace trace) queries := {
    proofBytes := proofBytes.val.map generatedU8ToByte
    query_count := queryCount
    sections := sections
    proof_eq := by
      change proofBytes.val.map generatedU8ToByte =
        c1.wire ++ c2.wire ++ line1.wire ++ line2.wire ++ line3.wire
      rw [hc1, hc2, hline1, hline2, hline3, hempty]
      simp only [List.map_nil, List.append_nil, List.append_assoc]
  }
  exact ⟨run, rfl⟩

/-- The stronger five-section composition keeps the five concrete openings
returned by the unchanged source loop and identifies each with the matching
authenticated section in the constructed run. -/
theorem generated_five_call_trace_yields_exact_run_and_openings
    (sha256 : List ModelByte → Digest32)
    (queries : Finset V5Query) (queryCount : queries.card = 18)
    {hash : GeneratedHash}
    {s0 s1 s2 s3 s4 : Slice Std.U32}
    {roots : Array GeneratedDigest 5#usize}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {level0 next0 : GeneratedDigestVec}
    {proofBytes : Slice Std.U8}
    {parsed0 : Array (Option GeneratedOpening) 5#usize}
    {finalRemainder : Slice Std.U8}
    {finalParsed : Array (Option GeneratedOpening) 5#usize}
    (trace : GeneratedFiveCallTrace hash s0 s1 s2 s3 s4 roots topology
      level0 next0 proofBytes parsed0 finalRemainder finalParsed)
    (hhash : HashCallbackEqualsSha256 sha256 hash)
    (s0Model : s0.val.map (fun index => index.val) =
      orderedActiveIndices .c1 queries 0)
    (s1Model : s1.val.map (fun index => index.val) =
      orderedActiveIndices .c2 queries 0)
    (s2Model : s2.val.map (fun index => index.val) =
      orderedActiveIndices .line1 queries 0)
    (s3Model : s3.val.map (fun index => index.val) =
      orderedActiveIndices .line2 queries 0)
    (s4Model : s4.val.map (fun index => index.val) =
      orderedActiveIndices .line3 queries 0)
    (fields : FullExactConstructedTopologyFields queries topology)
    (hempty : finalRemainder.val = []) :
    ∃ run : ExactV5Run sha256 (rootsOfFiveCallTrace trace) queries,
      run.proofBytes = proofBytes.val.map generatedU8ToByte ∧
      generatedOpeningToReturned trace.call0.opening =
        openingOfTrace (run.sections .c1) ∧
      generatedOpeningToReturned trace.call1.opening =
        openingOfTrace (run.sections .c2) ∧
      generatedOpeningToReturned trace.call2.opening =
        openingOfTrace (run.sections .line1) ∧
      generatedOpeningToReturned trace.call3.opening =
        openingOfTrace (run.sections .line2) ∧
      generatedOpeningToReturned trace.call4.opening =
        openingOfTrace (run.sections .line3) := by
  have p0 := generated_section_call_parameters .c1 queries trace.call0 rfl rfl
    s0Model
  have p1 := generated_section_call_parameters .c2 queries trace.call1 rfl rfl
    s1Model
  have p2 := generated_section_call_parameters .line1 queries trace.call2 rfl
    rfl s2Model
  have p3 := generated_section_call_parameters .line2 queries trace.call3 rfl
    rfl s3Model
  have p4 := generated_section_call_parameters .line3 queries trace.call4 rfl
    rfl s4Model
  obtain ⟨c1, hc1, hc1Opening⟩ :=
    generated_section_call_yields_exact_returned_section sha256 .c1 queries
      queryCount trace.call0 hhash p0 fields
  obtain ⟨c2, hc2, hc2Opening⟩ :=
    generated_section_call_yields_exact_returned_section sha256 .c2 queries
      queryCount trace.call1 hhash p1 fields
  obtain ⟨line1, hline1, hline1Opening⟩ :=
    generated_section_call_yields_exact_returned_section sha256 .line1 queries
      queryCount trace.call2 hhash p2 fields
  obtain ⟨line2, hline2, hline2Opening⟩ :=
    generated_section_call_yields_exact_returned_section sha256 .line2 queries
      queryCount trace.call3 hhash p3 fields
  obtain ⟨line3, hline3, hline3Opening⟩ :=
    generated_section_call_yields_exact_returned_section sha256 .line3 queries
      queryCount trace.call4 hhash p4 fields
  let sections : ∀ tree,
      ExactSectionTrace sha256 tree ((rootsOfFiveCallTrace trace).get tree)
        queries := fun tree => match tree with
    | .c1 => c1
    | .c2 => c2
    | .line1 => line1
    | .line2 => line2
    | .line3 => line3
  let run : ExactV5Run sha256 (rootsOfFiveCallTrace trace) queries := {
    proofBytes := proofBytes.val.map generatedU8ToByte
    query_count := queryCount
    sections := sections
    proof_eq := by
      change proofBytes.val.map generatedU8ToByte =
        c1.wire ++ c2.wire ++ line1.wire ++ line2.wire ++ line3.wire
      rw [hc1, hc2, hline1, hline2, hline3, hempty]
      simp only [List.map_nil, List.append_nil, List.append_assoc]
  }
  refine ⟨run, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact hc1Opening
  · exact hc2Opening
  · exact hline1Opening
  · exact hline2Opening
  · exact hline3Opening

#print axioms rootsOfFiveCallTrace_get_c1
#print axioms generated_five_call_trace_yields_exact_run
#print axioms generated_five_call_trace_yields_exact_run_and_openings

end AspisV5MerkleUnchangedFiveSectionComposition
