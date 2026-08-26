import V7MerkleK12AcceptedBridge

open Aeneas Aeneas.Std Result

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-!
# Translated sparse-frontier traversal composition

This file discharges the source-control-flow side of
`PairedHashRounds`.  It is separate from `V7MerkleK12AcceptedBridge` so the
pure path-to-frozen-predicate adapter remains a stable focused target.
-/

namespace AspisV7MerkleK12TraversalBridge


abbrev GeneratedEntry := AspisV7MerkleK12SourceBridge.GeneratedEntry
abbrev GeneratedLevel := AspisV7MerkleK12SourceBridge.GeneratedLevel

/-! ## Edge-covering view of one translated inner loop

The next trace is the exact semantic shape obtained by inverting the three
successful inner-loop branches: a frontier sibling consumes one live entry;
an adjacent even/odd pair consumes two; termination consumes none.  Every
step retains the literal generated `Vec::push` equation and the exact paired
hash edge created by that production branch.
-/

inductive ExactInnerEdgeTrace (hash : AspisV7MerkleK12SourceBridge.GeneratedHash) :
    List GeneratedEntry → GeneratedLevel → GeneratedLevel → Type
  | done (scratch : GeneratedLevel) : ExactInnerEdgeTrace hash [] scratch scratch
  | frontier {child parent : GeneratedEntry} {rest : List GeneratedEntry}
      {scratch pushed final : GeneratedLevel}
      (edge : AspisV7MerkleK12AcceptedBridge.PairedHashEdge hash child parent)
      (pushRun : alloc.vec.Vec.push scratch parent = .ok pushed)
      (tail : ExactInnerEdgeTrace hash rest pushed final) :
      ExactInnerEdgeTrace hash (child :: rest) scratch final
  | paired {left right parent : GeneratedEntry} {rest : List GeneratedEntry}
      {scratch pushed final : GeneratedLevel}
      (leftEdge : AspisV7MerkleK12AcceptedBridge.PairedHashEdge hash left parent)
      (rightEdge : AspisV7MerkleK12AcceptedBridge.PairedHashEdge hash right parent)
      (pushRun : alloc.vec.Vec.push scratch parent = .ok pushed)
      (tail : ExactInnerEdgeTrace hash rest pushed final) :
      ExactInnerEdgeTrace hash (left :: right :: rest) scratch final

theorem vec_clear_success_values_empty
    (level cleared : GeneratedLevel)
    (run : alloc.vec.Vec.clear Global level = .ok cleared) :
    cleared.val = [] := by
  unfold alloc.vec.Vec.clear at run
  have exactValue := Result.ok.inj run
  rw [← exactValue]

theorem vec_push_success_values_append
    (level output : GeneratedLevel) (entry : GeneratedEntry)
    (run : alloc.vec.Vec.push level entry = .ok output) :
    output.val = level.val ++ [entry] := by
  unfold alloc.vec.Vec.push at run
  dsimp only at run
  split at run
  · injection run with outputExact
    subst output
    simp [List.concat_eq_append]
  · simp at run

theorem vec_extend_builtin_success_values_append
    (level output : GeneratedLevel) (entries : Slice GeneratedEntry)
    (run : alloc.vec.Vec.extend_from_slice (BuiltinClone GeneratedEntry)
      level entries = .ok output) :
    output.val = level.val ++ entries.val := by
  rcases level with ⟨levelValues, levelBound⟩
  rcases output with ⟨outputValues, outputBound⟩
  rcases entries with ⟨entryValues, entryBound⟩
  have cloneSpec := Slice.clone_spec
    (s := (⟨entryValues, entryBound⟩ : Slice GeneratedEntry))
    (clone := (BuiltinClone GeneratedEntry).clone)
    (by intro entry member; rfl)
  obtain ⟨cloned, cloneRun, clonedExact⟩ :=
    Aeneas.Std.WP.spec_imp_exists cloneSpec
  subst cloned
  have bound : levelValues.length + entryValues.length ≤ Std.Usize.max := by
    by_contra noRoom
    simp [alloc.vec.Vec.extend_from_slice, noRoom] at run
  let expected : GeneratedLevel :=
    ⟨levelValues ++ entryValues, by
      simpa [List.length_append] using bound⟩
  have boundExact :
      alloc.vec.Vec.length
          (⟨levelValues, levelBound⟩ : GeneratedLevel) +
        Slice.length (⟨entryValues, entryBound⟩ : Slice GeneratedEntry) ≤
          Std.Usize.max := by
    simpa using bound
  have canonical :
      alloc.vec.Vec.extend_from_slice (BuiltinClone GeneratedEntry)
        ⟨levelValues, levelBound⟩ ⟨entryValues, entryBound⟩ =
          .ok expected := by
    simp only [alloc.vec.Vec.extend_from_slice, dif_pos boundExact]
    split
    · rename_i clonedAgain cloneEquation
      have clonedAgainExact : clonedAgain =
          (⟨entryValues, entryBound⟩ : Slice GeneratedEntry) :=
        Result.ok.inj (cloneEquation.symm.trans cloneRun)
      subst clonedAgain
      rfl
    · rename_i error cloneEquation
      have impossibleEq :
          (Result.ok (⟨entryValues, entryBound⟩ : Slice GeneratedEntry) :
              Result (Slice GeneratedEntry)) = Result.fail error :=
        cloneRun.symm.trans cloneEquation
      exact False.elim
        (Result.noConfusion (P := False) rfl (heq_of_eq impossibleEq))
    · rename_i cloneEquation
      have impossibleEq :
          (Result.ok (⟨entryValues, entryBound⟩ : Slice GeneratedEntry) :
              Result (Slice GeneratedEntry)) = Result.div :=
        cloneRun.symm.trans cloneEquation
      exact False.elim
        (Result.noConfusion (P := False) rfl (heq_of_eq impossibleEq))
  have outputExact := Result.ok.inj (canonical.symm.trans run)
  exact (congrArg Subtype.val outputExact).symm

theorem ExactInnerEdgeTrace.preserves_scratch_members
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash} {remaining : List GeneratedEntry}
    {scratch final : GeneratedLevel}
    (trace : ExactInnerEdgeTrace hash remaining scratch final) :
    ∀ entry, entry ∈ scratch.val → entry ∈ final.val := by
  induction trace with
  | done => exact fun entry member => member
  | frontier edge pushRun tail inductionHypothesis =>
      intro entry member
      apply inductionHypothesis entry
      rw [vec_push_success_values_append _ _ _ pushRun]
      exact List.mem_append_left [_] member
  | paired leftEdge rightEdge pushRun tail inductionHypothesis =>
      intro entry member
      apply inductionHypothesis entry
      rw [vec_push_success_values_append _ _ _ pushRun]
      exact List.mem_append_left [_] member

structure EdgeDestination (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (child : GeneratedEntry) (final : GeneratedLevel) where
  parent : GeneratedEntry
  parentMember : parent ∈ final.val
  edge : AspisV7MerkleK12AcceptedBridge.PairedHashEdge hash child parent

/-- Propositional coverage theorem used to select a proof-relevant edge
destination without eliminating a membership proposition directly into
`Type`. -/
theorem ExactInnerEdgeTrace.nonemptyDestination
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash} {remaining : List GeneratedEntry}
    {scratch final : GeneratedLevel}
    (trace : ExactInnerEdgeTrace hash remaining scratch final)
    (child : GeneratedEntry) (member : child ∈ remaining) :
    Nonempty (EdgeDestination hash child final) := by
  induction trace generalizing child with
  | done => simp at member
  | @frontier head parent rest current pushed output edge pushRun tail ih =>
      simp only [List.mem_cons] at member
      rcases member with childExact | member
      · subst child
        have parentPushed : parent ∈ pushed.val := by
          rw [vec_push_success_values_append current pushed parent pushRun]
          exact List.mem_append_right current.val (by simp)
        exact ⟨{
          parent := parent
          parentMember := tail.preserves_scratch_members parent parentPushed
          edge := edge }⟩
      · exact ih child member
  | @paired left right parent rest current pushed output leftEdge rightEdge
      pushRun tail ih =>
      simp only [List.mem_cons] at member
      rcases member with childLeft | childRightOrRest
      · subst child
        have parentPushed : parent ∈ pushed.val := by
          rw [vec_push_success_values_append current pushed parent pushRun]
          exact List.mem_append_right current.val (by simp)
        exact ⟨{
          parent := parent
          parentMember := tail.preserves_scratch_members parent parentPushed
          edge := leftEdge }⟩
      · rcases childRightOrRest with childRight | member
        · subst child
          have parentPushed : parent ∈ pushed.val := by
            rw [vec_push_success_values_append current pushed parent pushRun]
            exact List.mem_append_right current.val (by simp)
          exact ⟨{
            parent := parent
            parentMember := tail.preserves_scratch_members parent parentPushed
            edge := rightEdge }⟩
        · exact ih child member

/-- Complete inner-trace coverage: every consumed live entry has an actual
parent in the returned level and the literal paired source hash edge that
created it.  The witness is selected from the propositional coverage theorem
above. -/
noncomputable def ExactInnerEdgeTrace.destinationOfMember
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash}
    {remaining : List GeneratedEntry} {scratch final : GeneratedLevel}
    (trace : ExactInnerEdgeTrace hash remaining scratch final)
    (child : GeneratedEntry) (member : child ∈ remaining) :
    EdgeDestination hash child final :=
  Classical.choice (trace.nonemptyDestination child member)

noncomputable def ExactInnerEdgeTrace.toPairedHashRound
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash} {level scratch final : GeneratedLevel}
    (trace : ExactInnerEdgeTrace hash level.val scratch final) :
    AspisV7MerkleK12AcceptedBridge.PairedHashRound hash level final where
  parentOf child member := (trace.destinationOfMember child member).parent
  parentMember child member :=
    (trace.destinationOfMember child member).parentMember
  edge child member := (trace.destinationOfMember child member).edge

/-! ## Exact outer edge trace

One constructor corresponds to one successful translated outer range step.
The inner trace starts from the scratch level returned by production's
`Vec::clear`; it constructs the next live level, which is passed literally to
the following constructor.
-/

inductive ExactOuterEdgeTrace (hash : AspisV7MerkleK12SourceBridge.GeneratedHash) :
    Nat → GeneratedLevel → GeneratedLevel → Type
  | done (level : GeneratedLevel) : ExactOuterEdgeTrace hash 0 level level
  | step {rounds : Nat} {level scratch next final : GeneratedLevel}
      (scratchEmpty : scratch.val = [])
      (inner : ExactInnerEdgeTrace hash level.val scratch next)
      (tail : ExactOuterEdgeTrace hash rounds next final) :
      ExactOuterEdgeTrace hash (rounds + 1) level final

noncomputable def ExactOuterEdgeTrace.toPairedHashRounds
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash} {rounds : Nat}
    {level final : GeneratedLevel}
    (trace : ExactOuterEdgeTrace hash rounds level final) :
    AspisV7MerkleK12AcceptedBridge.PairedHashRounds hash rounds level final := by
  induction trace with
  | done => exact .zero _
  | step scratchEmpty inner tail inductionHypothesis =>
      exact .step inner.toPairedHashRound inductionHypothesis

/-- The final length/index checks already extracted from production determine
the complete singleton list, not merely its zeroth projection. -/
theorem exact_traversal_final_level_values
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (c1Root c2Root : Array Std.U8 26#usize)
    (depth : Std.U32) (entries : Slice GeneratedEntry)
    (c1Nodes c2Nodes : Slice Std.U8)
    (initialLevel initialNext outputLevel outputNext : GeneratedLevel)
    (traversal : AspisV7MerkleK12SourceBridge.ExactAcceptedTwoTreeTraversal hash c1Root c2Root
      depth entries c1Nodes c2Nodes initialLevel initialNext outputLevel
      outputNext) :
    outputLevel.val = [(0#u32, c1Root, c2Root)] := by
  have lengthExact : outputLevel.val.length = 1 := by
    have scalarExact := congrArg UScalar.val
      traversal.finalRoot.finalSingleton
    simpa using scalarExact
  have indexExact := traversal.finalRoot.rootEntryEquation
  cases valuesEquation : outputLevel.val with
  | nil => simp [valuesEquation] at lengthExact
  | cons head tail =>
      cases tail with
      | nil =>
          have headExact : head = (0#u32, c1Root, c2Root) := by
            simpa [alloc.vec.Vec.index, alloc.vec.Vec.index_usize,
              Slice.index_usize, valuesEquation] using indexExact
          subst head
          rfl
      | cons next rest => simp [valuesEquation] at lengthExact

/-- The executable external `Vec::clear` used by the exact extraction leaves
the traversal scratch level literally empty. -/
theorem exact_traversal_cleared_level_values
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (c1Root c2Root : Array Std.U8 26#usize)
    (depth : Std.U32) (entries : Slice GeneratedEntry)
    (c1Nodes c2Nodes : Slice Std.U8)
    (initialLevel initialNext outputLevel outputNext : GeneratedLevel)
    (traversal : AspisV7MerkleK12SourceBridge.ExactAcceptedTwoTreeTraversal hash c1Root c2Root
      depth entries c1Nodes c2Nodes initialLevel initialNext outputLevel
      outputNext) :
    traversal.initialization.clearedLevel.val = [] :=
  vec_clear_success_values_empty initialLevel
    traversal.initialization.clearedLevel
    traversal.initialization.clearEquation

/-- Seeding is exactly `clear` followed by extending from the supplied source
entry slice, so the first live level contains precisely those entries in their
production order. -/
theorem exact_traversal_seeded_level_values
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (c1Root c2Root : Array Std.U8 26#usize)
    (depth : Std.U32) (entries : Slice GeneratedEntry)
    (c1Nodes c2Nodes : Slice Std.U8)
    (initialLevel initialNext outputLevel outputNext : GeneratedLevel)
    (traversal : AspisV7MerkleK12SourceBridge.ExactAcceptedTwoTreeTraversal hash c1Root c2Root
      depth entries c1Nodes c2Nodes initialLevel initialNext outputLevel
      outputNext) :
    traversal.initialization.seededLevel.val = entries.val := by
  have extended := vec_extend_builtin_success_values_append
    traversal.initialization.clearedLevel
    traversal.initialization.seededLevel entries
    traversal.initialization.seedEquation
  rw [exact_traversal_cleared_level_values hash c1Root c2Root depth entries
    c1Nodes c2Nodes initialLevel initialNext outputLevel outputNext traversal]
    at extended
  simpa using extended

/-- Source-facing composition once the direct outer body inversion has
produced `ExactOuterEdgeTrace`.  Depth 18 and count 16 occur in the types of
the edge trace and seed function.  Leaf tags and shared salt occur in each
`PairedSourceSeed`; paths and root equations are constructed here. -/
theorem exact_outer_edge_trace_implies_accepted_two_tree_openings
    (sha256 : List AspisPool.V7MerkleQueryGrammar.Byte →
      List AspisPool.V7MerkleQueryGrammar.Byte)
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (hashSemantics : AspisV7MerkleK12SourceBridge.HashCallbackEqualsSha256
      sha256 hash)
    (c1Root c2Root : Array Std.U8 26#usize)
    (entries : Slice GeneratedEntry) (c1Nodes c2Nodes : Slice Std.U8)
    (initialLevel initialNext outputLevel outputNext : GeneratedLevel)
    (traversal : AspisV7MerkleK12SourceBridge.ExactAcceptedTwoTreeTraversal
      hash c1Root c2Root 18#u32 entries c1Nodes c2Nodes initialLevel
      initialNext outputLevel outputNext)
    (seeds : AspisV7MerkleK12AcceptedBridge.PairedSourceSeedBatch hash)
    (callerEntriesExact : entries.val =
      List.ofFn (fun ordinal => (seeds ordinal).entry))
    (positionsInjective : Function.Injective
      (fun ordinal => (seeds ordinal).finitePosition))
    (sourceEdges : ExactOuterEdgeTrace hash
      AspisPool.V7MerkleQueryGrammar.treeDepth
      traversal.initialization.seededLevel outputLevel) :
    AspisPool.V7MerkleQueryExtractor.accepted_two_tree_openings
      (AspisV7MerkleK12AcceptedBridge.frozenTruncate sha256)
      (AspisV7MerkleK12AcceptedBridge.rootsOfGeneratedDigests c1Root c2Root)
      (AspisV7MerkleK12AcceptedBridge.proofOfSourceOpeningBatch
        (AspisV7MerkleK12AcceptedBridge.sourceOpeningBatchOfRounds seeds
          traversal.initialization.seededLevel outputLevel
          sourceEdges.toPairedHashRounds
          (by
            rw [exact_traversal_seeded_level_values hash c1Root c2Root
              18#u32 entries c1Nodes c2Nodes initialLevel initialNext
              outputLevel outputNext traversal]
            exact callerEntriesExact)
          (exact_traversal_final_level_values hash c1Root c2Root 18#u32
            entries c1Nodes c2Nodes initialLevel initialNext outputLevel
            outputNext traversal))) := by
  apply
    AspisV7MerkleK12AcceptedBridge.exact_source_hash_rounds_imply_accepted_two_tree_openings
      sha256 hash hashSemantics c1Root c2Root seeds
      traversal.initialization.seededLevel outputLevel
      sourceEdges.toPairedHashRounds
  exact positionsInjective

#print axioms vec_clear_success_values_empty
#print axioms vec_push_success_values_append
#print axioms vec_extend_builtin_success_values_append
#print axioms ExactInnerEdgeTrace.preserves_scratch_members
#print axioms ExactInnerEdgeTrace.destinationOfMember
#print axioms ExactInnerEdgeTrace.toPairedHashRound
#print axioms ExactOuterEdgeTrace.toPairedHashRounds
#print axioms exact_traversal_final_level_values
#print axioms exact_traversal_cleared_level_values
#print axioms exact_traversal_seeded_level_values
#print axioms exact_outer_edge_trace_implies_accepted_two_tree_openings

end AspisV7MerkleK12TraversalBridge
