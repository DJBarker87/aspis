import V5MerkleUnchangedFiveSectionComposition
import V5MerkleUnchangedQueryModelBridge

/-!
# Public unchanged V5 Merkle acceptance implies the maintained exact run

This is the end-to-end Merkle source bridge.  It starts at successful
execution of the exact Charon/Aeneas translation of
`verify_v5_private_openings`, recovers the five helper calls, proves their
query/topology views, and composes their exact section traces into
`ExactV5PrivateOpeningAcceptance`.

The two former proposition-valued source-equality hypotheses are not used.
The only executable semantic boundary is the explicit hash callback equation.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5MerkleUnchangedPublicAcceptanceBridge

open V5MerkleUnchangedFull
open V5MerkleUnchangedDriverProof
open V5MerkleQueryReuseProof
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5TopologyConstruction
open AspisV5MerkleUnchangedFullHelperBridge
open AspisV5MerkleUnchangedFullConstructorSemantics
open AspisV5MerkleUnchangedFiveSectionComposition
open AspisV5MerkleUnchangedQueryModelBridge

abbrev GeneratedDigest := Array Std.U8 32#usize
abbrev GeneratedHash := Slice (Slice Std.U8) → GeneratedDigest
abbrev ModelByte := AspisV5MerkleAuthenticationBinding.Byte

/-- The five maintained roots are exactly the five entries read by the
generated source driver. -/
def GeneratedRootsMatch (rootsArray : Array GeneratedDigest 5#usize)
    (roots : V5PrivateRoots Digest32) : Prop :=
  ∃ c1 c2 line1 line2 line3 : GeneratedDigest,
    Array.index_usize rootsArray 0#usize = .ok c1 ∧
    Array.index_usize rootsArray 1#usize = .ok c2 ∧
    Array.index_usize rootsArray 2#usize = .ok line1 ∧
    Array.index_usize rootsArray 3#usize = .ok line2 ∧
    Array.index_usize rootsArray 4#usize = .ok line3 ∧
    roots.c1 = generatedArrayToDigest c1 ∧
    roots.c2 = generatedArrayToDigest c2 ∧
    roots.line1 = generatedArrayToDigest line1 ∧
    roots.line2 = generatedArrayToDigest line2 ∧
    roots.line3 = generatedArrayToDigest line3

/-- Release-root and maintained-run evidence produced by one successful exact
generated execution. -/
def ExactGeneratedV5MerkleAcceptance
    (sha256 : List ModelByte → Digest32)
    (generatedRoots : private_openings.V5PrivateOpeningRoots)
    (queries : Finset V5Query) (proofBytes : Slice Std.U8) : Prop :=
  ∃ rootsArray : Array GeneratedDigest 5#usize,
    ∃ roots : V5PrivateRoots Digest32,
      generatedRoots.as_array = .ok rootsArray ∧
      GeneratedRootsMatch rootsArray roots ∧
      ExactV5PrivateOpeningAcceptance sha256 {
        roots := roots
        queries := queries
        proofBytes := proofBytes.val.map generatedU8ToByte }

private theorem usize_shift_one_by_17 :
    (1#usize <<< 17#i32 : Result Std.Usize) = .ok 131072#usize := by
  change UScalar.shiftLeft_IScalar 1#usize 17#i32 = .ok 131072#usize
  have h17 : (17#i32).val = 17 := by scalar_tac
  rcases System.Platform.numBits_eq with hbits | hbits
  all_goals
    simp [UScalar.shiftLeft_IScalar, UScalar.shiftLeft, h17, hbits]
    apply UScalar.eq_of_val_eq
    simp [UScalar.val, hbits]

private theorem released_layer0_leaves_value
    (leaves : Std.Usize)
    (run : private_openings.V5_PRIVATE_LAYER0_LEAVES = .ok leaves) :
    leaves.val = 131072 := by
  have exactRun : private_openings.V5_PRIVATE_LAYER0_LEAVES =
      (.ok 131072#usize : Result Std.Usize) := by
    unfold private_openings.V5_PRIVATE_LAYER0_LEAVES
    exact usize_shift_one_by_17
  have valueEq : (131072#usize : Std.Usize) = leaves :=
    Result.ok.inj (exactRun.symm.trans run)
  rw [← valueEq]
  rfl

private theorem released_depth0_value
    (depth : Std.U32)
    (run : Array.index_usize private_openings.V5_PRIVATE_DEPTHS 0#usize =
      .ok depth) :
    depth = 17#u32 := by
  have expected :
      Array.index_usize private_openings.V5_PRIVATE_DEPTHS 0#usize =
        (.ok 17#u32 : Result Std.U32) := by
    unfold private_openings.V5_PRIVATE_DEPTHS Array.index_usize
    rfl
  exact Result.ok.inj (run.symm.trans expected)

/-- Exact generated public acceptance yields the maintained five-section
acceptance, without either old Merkle source-equality premise.

The ordinary input-view hypotheses are supplied by the transcript layer:
there are 18 distinct model queries, every raw query is 17-bit, and sorting
the raw query slice gives the maintained query set. -/
theorem generated_public_acceptance_yields_exact_v5
    (sha256 : List ModelByte → Digest32)
    (modelQueries : Finset V5Query)
    (queryCount : modelQueries.card = 18)
    (hash : GeneratedHash)
    (roots : private_openings.V5PrivateOpeningRoots)
    (rawQueries : Slice Std.U32) (proofBytes : Slice Std.U8)
    (verified : private_openings.VerifiedV5PrivateOpenings)
    (hhash : HashCallbackEqualsSha256 sha256 hash)
    (queryModel :
      (expectedLayer0 rawQueries.val).map (fun index => index.val) =
        sharedLevelIndices modelQueries 0)
    (hverify : private_openings.verify_v5_private_openings
      hash roots rawQueries proofBytes = .ok (.Ok verified)) :
    ExactGeneratedV5MerkleAcceptance sha256 roots modelQueries proofBytes := by
  obtain ⟨remainder, remainderEmpty, sourceNonempty⟩ :=
    generated_verify_success_yields_call_trace hash roots rawQueries proofBytes
      verified hverify
  obtain ⟨source⟩ := sourceNonempty
  obtain ⟨calls⟩ := source.callTrace
  have nonempty : rawQueries.val ≠ [] :=
    query_model_implies_nonempty rawQueries.val modelQueries queryCount
      queryModel
  have inRange : ∀ query ∈ rawQueries.val, query.val < 131072 :=
    query_model_implies_17_bit_range rawQueries.val modelQueries queryModel
  have leavesValue :=
    released_layer0_leaves_value source.layer0Leaves source.layer0Leaves_eq
  have rangeForSource : ∀ query ∈ rawQueries.val,
      query < UScalar.cast .U32 source.layer0Leaves := by
    intro query member
    have bound := inRange query member
    scalar_tac
  obtain ⟨s0Model, s1Model, s2Model, s3Model, s4Model⟩ :=
    generated_query_slices_model_five_sections rawQueries source.layer0Leaves
      source.indices source.later0 source.later1 source.later2 modelQueries
      nonempty rangeForSource source.indices_eq source.later0_eq
      source.later1_eq source.later2_eq queryModel
  have topologyRun :
      aspis_core.merkle.Radix4BinaryCapTopology.new 17#u32
        (alloc.vec.Vec.deref source.indices.layer0) =
          .ok (some source.topology) := by
    have depthEq := released_depth0_value source.depth0 source.depth0_eq
    simpa [depthEq] using source.topology_eq
  have fields : FullExactConstructedTopologyFields modelQueries
      source.topology := by
    letI : V5MerkleUnchangedCompat.HashContext := { hash := hash }
    apply exact_new_17_success_has_topology_fields modelQueries queryCount
      (alloc.vec.Vec.deref source.indices.layer0) source.topology
    · change source.indices.layer0.val.map (fun index => index.val) =
        sharedLevelIndices modelQueries 0
      simpa [sharedLevelIndices] using s0Model
    · exact topologyRun
  have finalEmpty : source.finalRemainder.val = [] := by
    rw [source.returned_remainder_eq]
    exact remainderEmpty
  obtain ⟨run, runProof⟩ := generated_five_call_trace_yields_exact_run
    sha256 modelQueries queryCount calls hhash s0Model s1Model s2Model s3Model
      s4Model fields finalEmpty
  refine ⟨source.rootsArray, rootsOfFiveCallTrace calls, source.roots_eq,
    ?_, ⟨run, runProof⟩⟩
  exact ⟨calls.call0.root, calls.call1.root, calls.call2.root,
    calls.call3.root, calls.call4.root, calls.call0.root_eq,
    calls.call1.root_eq, calls.call2.root_eq, calls.call3.root_eq,
    calls.call4.root_eq, rfl, rfl, rfl, rfl, rfl⟩

/-- The exact maintained run immediately gives an authenticated five-tree
forest under the roots read by the generated source. -/
theorem generated_public_acceptance_yields_forest
    (sha256 : List ModelByte → Digest32)
    (modelQueries : Finset V5Query)
    (queryCount : modelQueries.card = 18)
    (hash : GeneratedHash)
    (roots : private_openings.V5PrivateOpeningRoots)
    (rawQueries : Slice Std.U32) (proofBytes : Slice Std.U8)
    (verified : private_openings.VerifiedV5PrivateOpenings)
    (hhash : HashCallbackEqualsSha256 sha256 hash)
    (queryModel :
      (expectedLayer0 rawQueries.val).map (fun index => index.val) =
        sharedLevelIndices modelQueries 0)
    (hverify : private_openings.verify_v5_private_openings
      hash roots rawQueries proofBytes = .ok (.Ok verified)) :
    ∃ rootsArray : Array GeneratedDigest 5#usize,
      ∃ modelRoots : V5PrivateRoots Digest32,
        roots.as_array = .ok rootsArray ∧
        GeneratedRootsMatch rootsArray modelRoots ∧
        Nonempty (AcceptedV5Forest (sha256MerkleHashing sha256) modelRoots
          modelQueries) := by
  obtain ⟨rootsArray, modelRoots, rootsEq, rootsMatch, run, _⟩ :=
    generated_public_acceptance_yields_exact_v5 sha256 modelQueries queryCount
      hash roots rawQueries proofBytes verified hhash queryModel hverify
  exact ⟨rootsArray, modelRoots, rootsEq, rootsMatch,
    exactV5Run_yieldsForest run⟩

#print axioms generated_public_acceptance_yields_exact_v5
#print axioms generated_public_acceptance_yields_forest

end AspisV5MerkleUnchangedPublicAcceptanceBridge
