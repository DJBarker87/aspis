import V7MerkleK12InnerTraceBridge

open Aeneas Aeneas.Std Result

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-!
# Nested exact trace of the translated outer traversal loop

Every `step` below is obtained from one literal `cont` equation of the
translated outer body.  It exposes the range advance, scratch clear, exact
inner-loop result, and the finite exact trace of that inner loop.
-/

namespace AspisV7MerkleK12OuterTraceBridge

/-- Exact public range effect of a successful translated U32 iterator step. -/
theorem range_next_u32_some_exact
    (iter next : core.ops.range.Range Std.U32) (ordinal : Std.U32)
    (run : core.iter.range.IteratorRange.next core.iter.range.StepU32 iter =
      .ok (some ordinal, next)) :
    iter.start.val < iter.end.val ∧ ordinal = iter.start ∧
      next.start.val = iter.start.val + 1 ∧ next.end = iter.end := by
  have active : iter.start.val < iter.end.val := by
    by_contra inactive
    have inactive' : iter.end.val ≤ iter.start.val := by omega
    have spec := core.iter.range.IteratorRange.next_U32_none_spec iter inactive'
    rw [run] at spec
    simp at spec
  have spec := core.iter.range.IteratorRange.next_U32_some_spec iter active
  rw [run] at spec
  refine ⟨active, ?_⟩
  simpa using spec

/-- A normal `none` from the same iterator is exactly range exhaustion. -/
theorem range_next_u32_none_implies_exhausted
    (iter next : core.ops.range.Range Std.U32)
    (run : core.iter.range.IteratorRange.next core.iter.range.StepU32 iter =
      .ok (none, next)) :
    iter.end.val ≤ iter.start.val := by
  by_contra notExhausted
  have active : iter.start.val < iter.end.val := by omega
  have spec := core.iter.range.IteratorRange.next_U32_some_spec iter active
  rw [run] at spec
  simp at spec

inductive ExactOuterNestedTrace
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (c1Nodes c2Nodes : Slice Std.U8) :
    Nat → AspisV7MerkleK12SourceBridge.OuterLoopState →
      AspisV7MerkleK12SourceBridge.OuterLoopOutput → Type
  | done {start : AspisV7MerkleK12SourceBridge.OuterLoopState}
      {result : AspisV7MerkleK12SourceBridge.OuterLoopOutput}
      (bodyRun : AspisV7MerkleK12SourceBridge.exactOuterBody
        hash c1Nodes c2Nodes start = .ok (.done result)) :
      ExactOuterNestedTrace hash c1Nodes c2Nodes 0 start result
  | step {rounds : Nat}
      {start next : AspisV7MerkleK12SourceBridge.OuterLoopState}
      {result : AspisV7MerkleK12SourceBridge.OuterLoopOutput}
      (ordinal : Std.U32)
      (cleared : AspisV7MerkleK12SourceBridge.GeneratedLevel)
      (rangeRun : core.iter.range.IteratorRange.next
        core.iter.range.StepU32 start.1 = .ok (some ordinal, next.1))
      (clearRun : alloc.vec.Vec.clear Global start.2.2.1 = .ok cleared)
      (innerRun :
        V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0
          hash c1Nodes c2Nodes start.2.1 cleared start.2.2.2 0#usize =
            .ok (next.2.1, next.2.2.2, none))
      (scratchAfterSwap : next.2.2.1 = start.2.1)
      (innerTrace : AspisV7MerkleK12SourceBridge.ExactLoopTrace
        (AspisV7MerkleK12SourceBridge.exactInnerBody hash c1Nodes c2Nodes
          start.2.1)
        (cleared, start.2.2.2, 0#usize)
        (next.2.1, next.2.2.2, none))
      (tail : ExactOuterNestedTrace hash c1Nodes c2Nodes rounds next result) :
      ExactOuterNestedTrace hash c1Nodes c2Nodes (rounds + 1) start result

/-- A translated outer body can normally finish with `pending = none` only
when the public range is exhausted.  An active range step either continues
after a successful inner traversal or returns a non-`none` rejection. -/
theorem exact_outer_body_done_none_is_exhausted
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (c1Nodes c2Nodes : Slice Std.U8)
    (start : AspisV7MerkleK12SourceBridge.OuterLoopState)
    (outputLevel outputNext : AspisV7MerkleK12SourceBridge.GeneratedLevel)
    (outputNodePos : Std.Usize)
    (run : AspisV7MerkleK12SourceBridge.exactOuterBody hash c1Nodes c2Nodes
      start = .ok (.done (outputLevel, outputNext, outputNodePos, none))) :
    start.1.end.val ≤ start.1.start.val ∧
      outputLevel = start.2.1 ∧ outputNext = start.2.2.1 ∧
      outputNodePos = start.2.2.2 := by
  unfold AspisV7MerkleK12SourceBridge.exactOuterBody at run
  unfold
    V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0.body
    at run
  generalize rangeEquation :
      core.iter.range.IteratorRange.next core.iter.range.StepU32 start.1 =
        rangeResult at run
  cases rangeResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok rangeOutput =>
      rcases rangeOutput with ⟨ordinal, nextIter⟩
      simp only [Aeneas.Std.bind_tc_ok] at run
      cases ordinal with
      | none =>
          have exhausted := range_next_u32_none_implies_exhausted start.1
            nextIter rangeEquation
          have outputFacts :
              start.2.1 = outputLevel ∧ start.2.2.1 = outputNext ∧
                start.2.2.2 = outputNodePos := by
            simpa using Result.ok.inj run
          exact ⟨exhausted,
            outputFacts.1.symm, outputFacts.2.1.symm,
            outputFacts.2.2.symm⟩
      | some ordinal =>
          generalize clearEquation :
              alloc.vec.Vec.clear Global start.2.2.1 = clearResult at run
          cases clearResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
          | div => simp [Bind.bind, Aeneas.Std.bind] at run
          | ok cleared =>
              simp only [Aeneas.Std.bind_tc_ok] at run
              generalize innerEquation :
                  V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0
                    hash c1Nodes c2Nodes start.2.1 cleared start.2.2.2
                    0#usize = innerResult at run
              cases innerResult with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
              | div => simp [Bind.bind, Aeneas.Std.bind] at run
              | ok innerOutput =>
                  rcases innerOutput with
                    ⟨innerNext, innerNodePos, pending⟩
                  simp only [Aeneas.Std.bind_tc_ok] at run
                  cases pending <;> simp at run

/-- The number of semantic outer steps is determined by the exact generated
range, rather than supplied by a traversal premise.  This result-index-generic
form avoids eliminating a fixed `pending = none` index through the trace. -/
theorem ExactOuterNestedTrace.rounds_eq_range_remaining_of_result_none
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (c1Nodes c2Nodes : Slice Std.U8)
    {rounds : Nat}
    {start : AspisV7MerkleK12SourceBridge.OuterLoopState}
    {result : AspisV7MerkleK12SourceBridge.OuterLoopOutput}
    (trace : ExactOuterNestedTrace hash c1Nodes c2Nodes rounds start result)
    (resultNone : result.2.2.2 = none) :
    rounds = start.1.end.val - start.1.start.val := by
  induction trace with
  | @done start result bodyRun =>
      rcases result with ⟨outputLevel, outputNext, outputNodePos, pending⟩
      cases pending with
      | some rejected => cases resultNone
      | none =>
          have exhausted := exact_outer_body_done_none_is_exhausted hash
            c1Nodes c2Nodes start outputLevel outputNext outputNodePos bodyRun
          have exhaustedRange := exhausted.1
          omega
  | step ordinal cleared rangeRun clearRun innerRun scratchAfterSwap
      innerTrace tail inductionHypothesis =>
      obtain ⟨active, ordinalExact, nextStartExact, nextEndExact⟩ :=
        range_next_u32_some_exact _ _ ordinal rangeRun
      rw [inductionHypothesis resultNone, nextEndExact, nextStartExact]
      omega

/-- Fixed-success-index wrapper used by the production traversal. -/
theorem ExactOuterNestedTrace.rounds_eq_range_remaining
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (c1Nodes c2Nodes : Slice Std.U8)
    {rounds : Nat}
    {start : AspisV7MerkleK12SourceBridge.OuterLoopState}
    {outputLevel outputNext : AspisV7MerkleK12SourceBridge.GeneratedLevel}
    {outputNodePos : Std.Usize}
    (trace : ExactOuterNestedTrace hash c1Nodes c2Nodes rounds start
      (outputLevel, outputNext, outputNodePos, none)) :
    rounds = start.1.end.val - start.1.start.val := by
  exact ExactOuterNestedTrace.rounds_eq_range_remaining_of_result_none hash
    c1Nodes c2Nodes trace rfl

theorem ExactOuterNestedTrace.rounds_eq_treeDepth_of_production_range
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (c1Nodes c2Nodes : Slice Std.U8)
    {rounds : Nat}
    {level next outputLevel outputNext :
      AspisV7MerkleK12SourceBridge.GeneratedLevel}
    {nodePos outputNodePos : Std.Usize}
    (trace : ExactOuterNestedTrace hash c1Nodes c2Nodes rounds
      ({ start := 0#u32, «end» := 18#u32 }, level, next, nodePos)
      (outputLevel, outputNext, outputNodePos, none)) :
    rounds = AspisPool.V7MerkleQueryGrammar.treeDepth := by
  rw [trace.rounds_eq_range_remaining]
  norm_num [AspisPool.V7MerkleQueryGrammar.treeDepth]

/-- Every nested translated outer step contains a complete inner edge trace;
therefore the full outer execution yields the exact paired-hash rounds used
by the constructive opening adapter.  As above, the generic result index
makes the induction independent of the final tuple's proof index. -/
theorem ExactOuterNestedTrace.yields_outer_edge_trace_of_result_none
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (c1Nodes c2Nodes : Slice Std.U8)
    {rounds : Nat}
    {start : AspisV7MerkleK12SourceBridge.OuterLoopState}
    {result : AspisV7MerkleK12SourceBridge.OuterLoopOutput}
    (trace : ExactOuterNestedTrace hash c1Nodes c2Nodes rounds start result)
    (resultNone : result.2.2.2 = none) :
    Nonempty (AspisV7MerkleK12TraversalBridge.ExactOuterEdgeTrace hash rounds
      start.2.1 result.1) := by
  induction trace with
  | @done start result bodyRun =>
      rcases result with ⟨outputLevel, outputNext, outputNodePos, pending⟩
      cases pending with
      | some rejected => cases resultNone
      | none =>
          have terminal := exact_outer_body_done_none_is_exhausted hash
            c1Nodes c2Nodes start outputLevel outputNext outputNodePos bodyRun
          have outputLevelExact := terminal.2.1
          rw [outputLevelExact]
          exact ⟨AspisV7MerkleK12TraversalBridge.ExactOuterEdgeTrace.done
            start.2.1⟩
  | step ordinal cleared rangeRun clearRun innerRun scratchAfterSwap
      innerTrace tail inductionHypothesis =>
      let innerEdges := Classical.choice
        (AspisV7MerkleK12InnerTraceBridge.exact_inner_control_flow_trace_yields_edge_trace
          hash c1Nodes c2Nodes _ cleared _ _ _ innerTrace)
      let outerTail := Classical.choice (inductionHypothesis resultNone)
      exact ⟨AspisV7MerkleK12TraversalBridge.ExactOuterEdgeTrace.step
        (AspisV7MerkleK12TraversalBridge.vec_clear_success_values_empty _ _
          clearRun)
        innerEdges outerTail⟩

/-- Fixed-success-index wrapper used by the production traversal. -/
theorem ExactOuterNestedTrace.yields_outer_edge_trace
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (c1Nodes c2Nodes : Slice Std.U8)
    {rounds : Nat}
    {start : AspisV7MerkleK12SourceBridge.OuterLoopState}
    {outputLevel outputNext : AspisV7MerkleK12SourceBridge.GeneratedLevel}
    {outputNodePos : Std.Usize}
    (trace : ExactOuterNestedTrace hash c1Nodes c2Nodes rounds start
      (outputLevel, outputNext, outputNodePos, none)) :
    Nonempty (AspisV7MerkleK12TraversalBridge.ExactOuterEdgeTrace hash rounds
      start.2.1 outputLevel) := by
  exact ExactOuterNestedTrace.yields_outer_edge_trace_of_result_none hash
    c1Nodes c2Nodes trace rfl

/-- Direct conversion of the generic finite outer control-flow trace into a
nested source trace containing each exact inner-loop trace. -/
theorem exact_outer_control_flow_trace_yields_nested_trace
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (c1Nodes c2Nodes : Slice Std.U8)
    {start : AspisV7MerkleK12SourceBridge.OuterLoopState}
    {result : AspisV7MerkleK12SourceBridge.OuterLoopOutput}
    (trace : AspisV7MerkleK12SourceBridge.ExactLoopTrace
      (AspisV7MerkleK12SourceBridge.exactOuterBody hash c1Nodes c2Nodes)
      start result) :
    Nonempty (Σ rounds,
      ExactOuterNestedTrace hash c1Nodes c2Nodes rounds start result) := by
  induction trace with
  | done bodyRun =>
      exact ⟨⟨0, ExactOuterNestedTrace.done bodyRun⟩⟩
  | @cont current next output bodyRun tail inductionHypothesis =>
      rcases current with ⟨iter, level, scratch, nodePos⟩
      unfold AspisV7MerkleK12SourceBridge.exactOuterBody at bodyRun
      unfold
        V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0.body
        at bodyRun
      generalize rangeEquation :
          core.iter.range.IteratorRange.next core.iter.range.StepU32 iter =
            rangeResult at bodyRun
      cases rangeResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
      | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
      | ok rangeOutput =>
          rcases rangeOutput with ⟨ordinalOption, nextIter⟩
          simp only [Aeneas.Std.bind_tc_ok] at bodyRun
          cases ordinalOption with
          | none => simp at bodyRun
          | some ordinal =>
              generalize clearEquation :
                  alloc.vec.Vec.clear Global scratch = clearResult at bodyRun
              cases clearResult with
              | fail error =>
                  simp [Bind.bind, Aeneas.Std.bind] at bodyRun
              | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
              | ok cleared =>
                  simp only [Aeneas.Std.bind_tc_ok] at bodyRun
                  generalize innerEquation :
                      V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0
                        hash c1Nodes c2Nodes level cleared nodePos 0#usize =
                          innerResult at bodyRun
                  cases innerResult with
                  | fail error =>
                      simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                  | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                  | ok innerOutput =>
                      rcases innerOutput with
                        ⟨innerNext, innerNodePos, pending⟩
                      simp only [Aeneas.Std.bind_tc_ok] at bodyRun
                      cases pending with
                      | some rejected => simp at bodyRun
                      | none =>
                          have nextExact :
                              next = (nextIter, innerNext, level,
                                innerNodePos) := by
                            simpa using (Result.ok.inj bodyRun).symm
                          subst next
                          let exactInnerTrace := Classical.choice
                            (AspisV7MerkleK12SourceBridge.inner_loop_success_yields_exact_control_flow_trace
                              hash c1Nodes c2Nodes level cleared innerNext
                              nodePos 0#usize innerNodePos none innerEquation)
                          let nestedTail := Classical.choice inductionHypothesis
                          rcases nestedTail with ⟨rounds, nestedTail⟩
                          exact ⟨⟨rounds + 1,
                            ExactOuterNestedTrace.step ordinal cleared
                              rangeEquation clearEquation innerEquation rfl
                              exactInnerTrace nestedTail⟩⟩

/-- Deterministic constructive projection of production's stored finite outer
control-flow trace into all 18 paired Merkle rounds. -/
noncomputable def outerEdgeTraceOfExactTraversal
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (c1Root c2Root : Array Std.U8 26#usize)
    (entries : Slice AspisV7MerkleK12SourceBridge.GeneratedEntry)
    (c1Nodes c2Nodes : Slice Std.U8)
    (initialLevel initialNext outputLevel outputNext :
      AspisV7MerkleK12SourceBridge.GeneratedLevel)
    (traversal : AspisV7MerkleK12SourceBridge.ExactAcceptedTwoTreeTraversal
      hash c1Root c2Root 18#u32 entries c1Nodes c2Nodes initialLevel
      initialNext outputLevel outputNext) :
    AspisV7MerkleK12TraversalBridge.ExactOuterEdgeTrace hash
      AspisPool.V7MerkleQueryGrammar.treeDepth
      traversal.initialization.seededLevel outputLevel := by
  have traceField := traversal.traversal.traversalControlFlowTrace
  unfold AspisV7MerkleK12SourceBridge.ExactTraversalControlFlowTrace
    at traceField
  let nestedSigma := Classical.choice
    (exact_outer_control_flow_trace_yields_nested_trace hash c1Nodes c2Nodes
      traceField)
  rcases nestedSigma with ⟨rounds, nested⟩
  have roundsExact := nested.rounds_eq_treeDepth_of_production_range
  subst rounds
  exact Classical.choice nested.yields_outer_edge_trace

/-- Source verifier traversal to the literal frozen accepted-opening
predicate, with no caller-supplied edge/path/root implication.  The complete
18-round paired edge trace is derived from the translated traversal field.
The remaining seed arguments are exactly the 16 translated caller leaf calls
and their public schedule facts, discharged by the caller bridge. -/
theorem exact_translated_traversal_implies_accepted_two_tree_openings
    (sha256 : List AspisPool.V7MerkleQueryGrammar.Byte →
      List AspisPool.V7MerkleQueryGrammar.Byte)
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (hashSemantics : AspisV7MerkleK12SourceBridge.HashCallbackEqualsSha256
      sha256 hash)
    (c1Root c2Root : Array Std.U8 26#usize)
    (entries : Slice AspisV7MerkleK12SourceBridge.GeneratedEntry)
    (c1Nodes c2Nodes : Slice Std.U8)
    (initialLevel initialNext outputLevel outputNext :
      AspisV7MerkleK12SourceBridge.GeneratedLevel)
    (traversal : AspisV7MerkleK12SourceBridge.ExactAcceptedTwoTreeTraversal
      hash c1Root c2Root 18#u32 entries c1Nodes c2Nodes initialLevel
      initialNext outputLevel outputNext)
    (seeds : AspisV7MerkleK12AcceptedBridge.PairedSourceSeedBatch hash)
    (callerEntriesExact : entries.val =
      List.ofFn (fun ordinal => (seeds ordinal).entry))
    (positionsInjective : Function.Injective
      (fun ordinal => (seeds ordinal).finitePosition)) :
    AspisPool.V7MerkleQueryExtractor.accepted_two_tree_openings
      (AspisV7MerkleK12AcceptedBridge.frozenTruncate sha256)
      (AspisV7MerkleK12AcceptedBridge.rootsOfGeneratedDigests c1Root c2Root)
      (AspisV7MerkleK12AcceptedBridge.proofOfSourceOpeningBatch
        (AspisV7MerkleK12AcceptedBridge.sourceOpeningBatchOfRounds seeds
          traversal.initialization.seededLevel outputLevel
          (outerEdgeTraceOfExactTraversal hash c1Root c2Root entries c1Nodes
            c2Nodes initialLevel initialNext outputLevel outputNext
            traversal).toPairedHashRounds
          (by
            rw [AspisV7MerkleK12TraversalBridge.exact_traversal_seeded_level_values
              hash c1Root c2Root 18#u32 entries c1Nodes c2Nodes initialLevel
              initialNext outputLevel outputNext traversal]
            exact callerEntriesExact)
          (AspisV7MerkleK12TraversalBridge.exact_traversal_final_level_values
            hash c1Root c2Root 18#u32 entries c1Nodes c2Nodes initialLevel
            initialNext outputLevel outputNext traversal))) := by
  exact
    AspisV7MerkleK12TraversalBridge.exact_outer_edge_trace_implies_accepted_two_tree_openings
      sha256 hash hashSemantics c1Root c2Root entries c1Nodes c2Nodes
      initialLevel initialNext outputLevel outputNext traversal seeds
      callerEntriesExact positionsInjective
      (outerEdgeTraceOfExactTraversal hash c1Root c2Root entries c1Nodes
        c2Nodes initialLevel initialNext outputLevel outputNext traversal)

noncomputable def exactTraversalOfVerifierSuccess
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (c1Root c2Root : Array Std.U8 26#usize)
    (entries : Slice AspisV7MerkleK12SourceBridge.GeneratedEntry)
    (c1Nodes c2Nodes : Slice Std.U8)
    (initialLevel initialNext outputLevel outputNext :
      AspisV7MerkleK12SourceBridge.GeneratedLevel)
    (run : V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes
      hash (c1Root, c2Root) 18#u32 entries (c1Nodes, c2Nodes) initialLevel
      initialNext = .ok (true, outputLevel, outputNext)) :
    AspisV7MerkleK12SourceBridge.ExactAcceptedTwoTreeTraversal hash c1Root
      c2Root 18#u32 entries c1Nodes c2Nodes initialLevel initialNext
      outputLevel outputNext :=
  Classical.choice
    (AspisV7MerkleK12SourceBridge.verify_two_subtrees_success_yields_exact_traversal
      hash c1Root c2Root 18#u32 entries c1Nodes c2Nodes initialLevel
      initialNext outputLevel outputNext run)

/-- The strongest verifier-local source theorem: literal success of the
translated production verifier implies the existing frozen accepted-opening
predicate for the 16 source leaf seeds.  The caller theorem supplies those
seeds from its own translated loop; no path/root/acceptance implication is a
premise here. -/
theorem translated_verifier_success_implies_accepted_two_tree_openings
    (sha256 : List AspisPool.V7MerkleQueryGrammar.Byte →
      List AspisPool.V7MerkleQueryGrammar.Byte)
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (hashSemantics : AspisV7MerkleK12SourceBridge.HashCallbackEqualsSha256
      sha256 hash)
    (c1Root c2Root : Array Std.U8 26#usize)
    (entries : Slice AspisV7MerkleK12SourceBridge.GeneratedEntry)
    (c1Nodes c2Nodes : Slice Std.U8)
    (initialLevel initialNext outputLevel outputNext :
      AspisV7MerkleK12SourceBridge.GeneratedLevel)
    (run : V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes
      hash (c1Root, c2Root) 18#u32 entries (c1Nodes, c2Nodes) initialLevel
      initialNext = .ok (true, outputLevel, outputNext))
    (seeds : AspisV7MerkleK12AcceptedBridge.PairedSourceSeedBatch hash)
    (callerEntriesExact : entries.val =
      List.ofFn (fun ordinal => (seeds ordinal).entry))
    (positionsInjective : Function.Injective
      (fun ordinal => (seeds ordinal).finitePosition)) :
    let traversal := exactTraversalOfVerifierSuccess hash c1Root c2Root
      entries c1Nodes c2Nodes initialLevel initialNext outputLevel outputNext
      run
    AspisPool.V7MerkleQueryExtractor.accepted_two_tree_openings
      (AspisV7MerkleK12AcceptedBridge.frozenTruncate sha256)
      (AspisV7MerkleK12AcceptedBridge.rootsOfGeneratedDigests c1Root c2Root)
      (AspisV7MerkleK12AcceptedBridge.proofOfSourceOpeningBatch
        (AspisV7MerkleK12AcceptedBridge.sourceOpeningBatchOfRounds seeds
          traversal.initialization.seededLevel outputLevel
          (outerEdgeTraceOfExactTraversal hash c1Root c2Root entries c1Nodes
            c2Nodes initialLevel initialNext outputLevel outputNext
            traversal).toPairedHashRounds
          (by
            rw [AspisV7MerkleK12TraversalBridge.exact_traversal_seeded_level_values
              hash c1Root c2Root 18#u32 entries c1Nodes c2Nodes initialLevel
              initialNext outputLevel outputNext traversal]
            exact callerEntriesExact)
          (AspisV7MerkleK12TraversalBridge.exact_traversal_final_level_values
            hash c1Root c2Root 18#u32 entries c1Nodes c2Nodes initialLevel
            initialNext outputLevel outputNext traversal))) := by
  dsimp only
  exact exact_translated_traversal_implies_accepted_two_tree_openings sha256
    hash hashSemantics c1Root c2Root entries c1Nodes c2Nodes initialLevel
    initialNext outputLevel outputNext
    (exactTraversalOfVerifierSuccess hash c1Root c2Root entries c1Nodes
      c2Nodes initialLevel initialNext outputLevel outputNext run)
    seeds callerEntriesExact positionsInjective

#print axioms range_next_u32_some_exact
#print axioms range_next_u32_none_implies_exhausted
#print axioms exact_outer_body_done_none_is_exhausted
#print axioms ExactOuterNestedTrace.rounds_eq_range_remaining_of_result_none
#print axioms ExactOuterNestedTrace.rounds_eq_range_remaining
#print axioms ExactOuterNestedTrace.rounds_eq_treeDepth_of_production_range
#print axioms ExactOuterNestedTrace.yields_outer_edge_trace_of_result_none
#print axioms ExactOuterNestedTrace.yields_outer_edge_trace
#print axioms exact_outer_control_flow_trace_yields_nested_trace
#print axioms outerEdgeTraceOfExactTraversal
#print axioms exact_translated_traversal_implies_accepted_two_tree_openings
#print axioms exactTraversalOfVerifierSuccess
#print axioms translated_verifier_success_implies_accepted_two_tree_openings

end AspisV7MerkleK12OuterTraceBridge
